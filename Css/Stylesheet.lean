/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Css.Condition

@[expose] public section

namespace Css

inductive KeyframeSelector where
  | «from»
  | to
  | at (p : Percentage)
  deriving DecidableEq, Repr

def KeyframeSelector.render : KeyframeSelector → String
  | .from => "from"
  | .to => "to"
  | .at p => p.value.render ++ "%"

structure Keyframe where
  selectors : List KeyframeSelector
  decls : List Declaration
  deriving Repr

/-- A keyframe block, as `frame [.from] [opacity 0]`. Of no selectors, it applies at no point, so
is left out. -/
def frame (selectors : List KeyframeSelector) (decls : List Declaration) : Keyframe :=
  ⟨selectors, decls⟩

inductive Rule where
  /-- A style rule. Of no selectors, it matches nothing, so is left out. -/
  | style (selectors : List Complex) (decls : List Declaration)
  /-- `@media`. Of no queries, it applies to `all`. -/
  | media (queries : List MediaQuery) (rules : List Rule)
  | supports (c : SupportsCondition) (rules : List Rule)
  /-- A layer block, named or anonymous. -/
  | layer (name : Option String) (rules : List Rule)
  /-- `@layer a, b;`, fixing the order of layers. Of no names, it is left out. -/
  | layerOrder (names : List String)
  | keyframes (name : String) (frames : List Keyframe)
  | fontFace (decls : List Declaration)
  /-- Inserted verbatim. The content is trusted as-is, and can unbalance the stylesheet or close
  an enclosing `<style>` element. -/
  | unsafeRaw (css : String)

def rule (selectors : List Complex) (decls : List Declaration) : Rule := .style selectors decls

def media (queries : List MediaQuery) (rules : List Rule) : Rule := .media queries rules

def supports (c : SupportsCondition) (rules : List Rule) : Rule := .supports c rules

def layer (name : String) (rules : List Rule) : Rule := .layer (some name) rules

def keyframes (name : String) (frames : List Keyframe) : Rule := .keyframes name frames

def fontFace (decls : List Declaration) : Rule := .fontFace decls

/-! ## Rendering -/

def joinWith (sep : String) : List String → String
  | [] => ""
  | [s] => s
  | s :: rest => s ++ sep ++ joinWith sep rest

def indent (depth : Nat) : String := String.ofList (List.replicate (2 * depth) ' ')

/-- `prelude { body }`, laid out on lines of its own when `pretty`. -/
def block (pretty : Bool) (depth : Nat) (prelude body : String) : String :=
  if pretty then (indent depth ++ prelude ++ " ") ++ "{" ++ ("\n" ++ body ++ indent depth) ++ "}" ++ "\n"
  else prelude ++ "{" ++ body ++ "}" ++ ""

def declsBody (pretty : Bool) (depth : Nat) (ds : List Declaration) : String :=
  if pretty then String.join (ds.map fun d => indent (depth + 1) ++ d.render true ++ ";\n")
  else joinWith ";" (ds.map (·.render))

def listSep (pretty : Bool) : String := if pretty then ", " else ","

def Keyframe.render (pretty : Bool) (depth : Nat) (k : Keyframe) : String :=
  if k.selectors.isEmpty then ""
  else block pretty depth (joinWith (listSep pretty) (k.selectors.map (·.render)))
    (declsBody pretty depth k.decls)

mutual

def Rule.renderAt (pretty : Bool) (depth : Nat) : Rule → String
  | .style sels ds =>
    if sels.isEmpty then ""
    else block pretty depth (joinWith (listSep pretty) (sels.map (·.render)))
      (declsBody pretty depth ds)
  | .media qs rs =>
    block pretty depth
      ("@media " ++ if qs.isEmpty then "all" else joinWith (listSep pretty) (qs.map (·.render)))
      (Rule.renderListAt pretty (depth + 1) rs)
  | .supports c rs =>
    block pretty depth ("@supports " ++ c.render) (Rule.renderListAt pretty (depth + 1) rs)
  | .layer none rs => block pretty depth "@layer" (Rule.renderListAt pretty (depth + 1) rs)
  | .layer (some n) rs =>
    block pretty depth ("@layer " ++ escapeIdent n) (Rule.renderListAt pretty (depth + 1) rs)
  | .layerOrder names =>
    if names.isEmpty then ""
    else if pretty then
      indent depth ++ "@layer " ++ joinWith ", " (names.map escapeIdent) ++ ";\n"
    else "@layer " ++ joinWith "," (names.map escapeIdent) ++ ";"
  | .keyframes n fs =>
    block pretty depth ("@keyframes " ++ escapeIdent n)
      (String.join (fs.map (Keyframe.render pretty (depth + 1))))
  | .fontFace ds => block pretty depth "@font-face" (declsBody pretty depth ds)
  | .unsafeRaw css => css

def Rule.renderListAt (pretty : Bool) (depth : Nat) : List Rule → String
  | [] => ""
  | r :: rs => Rule.renderAt pretty depth r ++ Rule.renderListAt pretty depth rs

end

/-- The rule, compact, or indented by two spaces a level when `pretty`. -/
def Rule.render (r : Rule) (pretty : Bool := false) : String := r.renderAt pretty 0

def declsHaveUnsafe (ds : List Declaration) : Bool := ds.any (·.hasUnsafe)

mutual

def Rule.hasUnsafe : Rule → Bool
  | .style _ ds | .fontFace ds => declsHaveUnsafe ds
  | .media qs rs => qs.any (·.hasUnsafe) || Rule.listHasUnsafe rs
  | .supports c rs => c.hasUnsafe || Rule.listHasUnsafe rs
  | .layer _ rs => Rule.listHasUnsafe rs
  | .layerOrder _ => false
  | .keyframes _ fs => fs.any fun f => declsHaveUnsafe f.decls
  | .unsafeRaw _ => true

def Rule.listHasUnsafe : List Rule → Bool
  | [] => false
  | r :: rs => r.hasUnsafe || Rule.listHasUnsafe rs

end

/-- An `@import` of another stylesheet, where the media queries match. -/
structure Import where
  url : String
  media : List MediaQuery := []
  deriving Repr

def Import.render (pretty : Bool) (i : Import) : String :=
  "@import " ++ Value.render [.function "url" [.string i.url]] ++
    (if i.media.isEmpty then "" else " " ++ joinWith (listSep pretty) (i.media.map (·.render))) ++
    (if pretty then ";\n" else ";")

structure Stylesheet where
  imports : List Import := []
  rules : List Rule

instance : Coe (List Rule) Stylesheet := ⟨({ rules := · })⟩

namespace Stylesheet

/-- The stylesheet, compact, or indented by two spaces a level when `pretty`. Imports come
first, where CSS requires them. -/
def render (s : Stylesheet) (pretty : Bool := false) : String :=
  String.join (s.imports.map (Import.render pretty)) ++ Rule.renderListAt pretty 0 s.rules

def hasUnsafe (s : Stylesheet) : Bool :=
  s.imports.any (·.media.any (·.hasUnsafe)) || Rule.listHasUnsafe s.rules

end Stylesheet

/-! ## Well-formedness -/

/-- The block depth after `cs`, starting from `d`, or `none` if a `}` closes no `{`. -/
def depthAfter : List Char → Nat → Option Nat
  | [], d => some d
  | c :: cs, d =>
    if c = '{' then depthAfter cs (d + 1)
    else if c = '}' then (match d with | 0 => none | d + 1 => depthAfter cs d)
    else depthAfter cs d

/-- What the stylesheet's renderer guarantees: every `}` closes a `{` before it and every `{` is
closed, so blocks nest, and there is no `<`, so the output can't close a `<style>` element. -/
def WellFormed (s : String) : Prop :=
  (∀ d, depthAfter s.toList d = some d) ∧ AllChars (· != '<') s

theorem depthAfter_append (a b : List Char) (d : Nat) :
    depthAfter (a ++ b) d = (depthAfter a d).bind (depthAfter b) := by
  induction a generalizing d with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.cons_append, depthAfter]
    split
    · exact ih _
    · split
      · cases d
        · rfl
        · exact ih _
      · exact ih _

theorem WellFormed.append {a b : String} (ha : WellFormed a) (hb : WellFormed b) :
    WellFormed (a ++ b) := by
  refine ⟨fun d => ?_, allChars_append.mpr ⟨ha.2, hb.2⟩⟩
  rw [String.toList_append, depthAfter_append, ha.1 d]
  exact hb.1 d

def isFlat (c : Char) : Bool := c != '{' && c != '}' && c != '<'

theorem isFlat_of_inert : ∀ c, isInert c = true → isFlat c = true := by
  intro c h
  simp only [isInert, isFlat, Bool.and_eq_true] at h ⊢
  exact ⟨⟨h.1.1.1.1, h.1.1.1.2⟩, h.1.2⟩

theorem WellFormed.of_flat {s : String} (h : AllChars isFlat s) : WellFormed s := by
  refine ⟨fun d => ?_, h.mono fun c hc => by simp only [isFlat, Bool.and_eq_true] at hc; exact hc.2⟩
  have : ∀ l : List Char, (∀ c ∈ l, isFlat c = true) → depthAfter l d = some d := by
    intro l hl
    induction l with
    | nil => rfl
    | cons c cs ih =>
      have hc := hl c (List.mem_cons_self ..)
      simp only [isFlat, Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
      simp only [depthAfter, hc.1.1, hc.1.2, ↓reduceIte]
      exact ih fun c h => hl c (List.mem_cons_of_mem _ h)
  exact this _ h

theorem WellFormed.braces {pre inner post : String} (hp : AllChars isFlat pre)
    (hi : WellFormed inner) (hq : AllChars isFlat post) :
    WellFormed (pre ++ "{" ++ inner ++ "}" ++ post) := by
  have hb : WellFormed ("{" ++ inner ++ "}") := by
    refine ⟨fun d => ?_, ?_⟩
    · simp only [String.toList_append, depthAfter_append]
      have : depthAfter "{".toList d = some (d + 1) := by
        simp [depthAfter]
      rw [this]
      simp only [Option.bind_some, hi.1 (d + 1)]
      simp [depthAfter]
    · simp only [allChars_append]; exact ⟨⟨by decide, hi.2⟩, by decide⟩
  have := ((WellFormed.of_flat hp).append hb).append (WellFormed.of_flat hq)
  simpa only [String.append_assoc] using this

theorem joinWith_allChars {p : Char → Bool} {sep : String} (hs : AllChars p sep) :
    (l : List String) → (∀ s ∈ l, AllChars p s) → AllChars p (joinWith sep l)
  | [], _ => fun _ h => by simp [joinWith] at h
  | [s], h => h s (List.mem_singleton_self s)
  | s :: t :: rest, h => by
    simp only [joinWith, allChars_append]
    exact ⟨⟨h s List.mem_cons_self, hs⟩,
      joinWith_allChars hs (t :: rest) fun x hx => h x (List.mem_cons_of_mem _ hx)⟩

private theorem indent_flat (d : Nat) : AllChars isFlat (indent d) :=
  allChars_ofList fun c hc => by
    simp only [List.mem_replicate] at hc
    rw [hc.2]; decide

private theorem ident_flat (s : String) : AllChars isFlat (escapeIdent s) :=
  ((escapeIdent_safe s).mono isInert_of_name).mono isFlat_of_inert

theorem Declaration.render_flat (d : Declaration) (pretty : Bool) (h : d.hasUnsafe = false) :
    AllChars isFlat (d.render pretty) := by
  simp only [Declaration.render, allChars_append]
  exact ⟨⟨⟨ident_flat _, by split <;> decide⟩, (d.value.render_inert h).mono isFlat_of_inert⟩,
    by repeat (first | decide | split)⟩

/-- Given no `Component.unsafeRaw`, a declaration can't end itself or the block it is in, so in
an inline `style` attribute every `;` is one `inlineStyle` put there. -/
theorem Declaration.render_inline (d : Declaration) (h : d.hasUnsafe = false) :
    AllChars (fun c => c != '{' && c != '}' && c != ';' && c != '<') d.render := by
  simp only [Declaration.render, allChars_append]
  have v := d.value.render_inert h
  refine ⟨⟨⟨((escapeIdent_safe _).mono isInert_of_name).mono ?_, by decide⟩, v.mono ?_⟩, by
    split <;> decide⟩ <;>
  · intro c hc
    simp only [isInert, Bool.and_eq_true] at hc
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨hc.1.1.1.1, hc.1.1.1.2⟩, hc.1.1.2⟩, hc.1.2⟩

private theorem declsBody_wf (pretty : Bool) (depth : Nat) (ds : List Declaration)
    (h : declsHaveUnsafe ds = false) : WellFormed (declsBody pretty depth ds) := by
  have hd : ∀ d ∈ ds, d.hasUnsafe = false := by
    simpa [declsHaveUnsafe] using h
  refine WellFormed.of_flat ?_
  unfold declsBody
  split
  · refine allChars_join fun s hs => ?_
    simp only [List.mem_map] at hs
    obtain ⟨d, hm, rfl⟩ := hs
    simp only [allChars_append]
    exact ⟨⟨indent_flat _, d.render_flat true (hd d hm)⟩, by decide⟩
  · refine joinWith_allChars (by decide) _ fun s hs => ?_
    simp only [List.mem_map] at hs
    obtain ⟨d, hm, rfl⟩ := hs
    exact d.render_flat false (hd d hm)

private theorem block_wf {pretty : Bool} {depth : Nat} {pre body : String}
    (hp : AllChars isFlat pre) (hb : WellFormed body) :
    WellFormed (block pretty depth pre body) := by
  unfold block
  split
  · refine WellFormed.braces ?_ ?_ (by decide)
    · simp only [allChars_append]; exact ⟨⟨indent_flat _, hp⟩, by decide⟩
    · exact (((WellFormed.of_flat (by decide)).append hb).append (WellFormed.of_flat (indent_flat _)))
  · exact WellFormed.braces hp hb (by decide)

private theorem selectors_flat (pretty : Bool) (sels : List Complex) :
    AllChars isFlat (joinWith (listSep pretty) (sels.map (·.render))) := by
  refine joinWith_allChars (by unfold listSep; split <;> decide) _ fun s hs => ?_
  simp only [List.mem_map] at hs
  obtain ⟨c, _, rfl⟩ := hs
  exact c.render_inert.mono isFlat_of_inert

private theorem queries_flat (pretty : Bool) (qs : List MediaQuery)
    (h : ∀ q ∈ qs, q.hasUnsafe = false) :
    AllChars isFlat (joinWith (listSep pretty) (qs.map (·.render))) := by
  refine joinWith_allChars (by unfold listSep; split <;> decide) _ fun s hs => ?_
  simp only [List.mem_map] at hs
  obtain ⟨q, hm, rfl⟩ := hs
  exact (q.render_inert (h q hm)).mono isFlat_of_inert

private theorem keyframe_wf (pretty : Bool) (depth : Nat) (k : Keyframe)
    (h : declsHaveUnsafe k.decls = false) : WellFormed (k.render pretty depth) := by
  unfold Keyframe.render
  split
  · exact WellFormed.of_flat (by decide)
  · refine block_wf (joinWith_allChars (by unfold listSep; split <;> decide) _ fun s hs => ?_)
      (declsBody_wf _ _ _ h)
    simp only [List.mem_map] at hs
    obtain ⟨sel, _, rfl⟩ := hs
    cases sel with
    | «from» | to => decide
    | «at» p =>
      simp only [KeyframeSelector.render, allChars_append]
      exact ⟨((Num.render_chars _).mono isInert_of_num).mono isFlat_of_inert, by decide⟩

mutual

theorem Rule.renderAt_wf (pretty : Bool) (depth : Nat) :
    (r : Rule) → r.hasUnsafe = false → WellFormed (r.renderAt pretty depth)
  | .style sels ds, h => by
    simp only [Rule.renderAt]
    split
    · exact WellFormed.of_flat (by decide)
    · exact block_wf (selectors_flat _ _) (declsBody_wf _ _ _ h)
  | .media qs rs, h => by
    simp only [Rule.hasUnsafe, Bool.or_eq_false_iff, List.any_eq_false, Bool.not_eq_true] at h
    simp only [Rule.renderAt]
    refine block_wf ?_ (Rule.renderListAt_wf pretty (depth + 1) rs h.2)
    simp only [allChars_append]
    refine ⟨by decide, ?_⟩
    split
    · decide
    · exact queries_flat _ _ h.1
  | .supports c rs, h => by
    simp only [Rule.hasUnsafe, Bool.or_eq_false_iff] at h
    simp only [Rule.renderAt]
    refine block_wf ?_ (Rule.renderListAt_wf pretty (depth + 1) rs h.2)
    simp only [allChars_append]
    exact ⟨by decide, (c.render_inert h.1).mono isFlat_of_inert⟩
  | .layer none rs, h => by
    simp only [Rule.renderAt]
    exact block_wf (by decide) (Rule.renderListAt_wf pretty (depth + 1) rs h)
  | .layer (some n) rs, h => by
    simp only [Rule.renderAt]
    refine block_wf ?_ (Rule.renderListAt_wf pretty (depth + 1) rs h)
    simp only [allChars_append]
    exact ⟨by decide, ident_flat n⟩
  | .layerOrder names, _ => by
    simp only [Rule.renderAt]
    have hn : ∀ sep, AllChars isFlat sep →
        AllChars isFlat (joinWith sep (names.map escapeIdent)) := fun sep hs =>
      joinWith_allChars hs _ fun s hs => by
        simp only [List.mem_map] at hs
        obtain ⟨n, _, rfl⟩ := hs
        exact ident_flat n
    refine WellFormed.of_flat ?_
    split
    · decide
    · split
      · simp only [allChars_append]
        exact ⟨⟨⟨indent_flat _, by decide⟩, hn _ (by decide)⟩, by decide⟩
      · simp only [allChars_append]
        exact ⟨⟨by decide, hn _ (by decide)⟩, by decide⟩
  | .keyframes n fs, h => by
    simp only [Rule.hasUnsafe, List.any_eq_false, Bool.not_eq_true] at h
    simp only [Rule.renderAt]
    refine block_wf ?_ ?_
    · simp only [allChars_append]
      exact ⟨by decide, ident_flat n⟩
    · have : ∀ l : List String, (∀ s ∈ l, WellFormed s) → WellFormed (String.join l) := by
        intro l hl
        induction l with
        | nil => exact WellFormed.of_flat fun _ h => by simp at h
        | cons s ss ih =>
          rw [String.join_cons]
          exact (hl s List.mem_cons_self).append (ih fun x hx => hl x (List.mem_cons_of_mem _ hx))
      refine this _ fun s hs => ?_
      simp only [List.mem_map] at hs
      obtain ⟨k, hm, rfl⟩ := hs
      exact keyframe_wf _ _ k (h k hm)
  | .fontFace ds, h => by
    simp only [Rule.renderAt]
    exact block_wf (by decide) (declsBody_wf _ _ _ h)

theorem Rule.renderListAt_wf (pretty : Bool) (depth : Nat) :
    (rs : List Rule) → Rule.listHasUnsafe rs = false → WellFormed (Rule.renderListAt pretty depth rs)
  | [], _ => WellFormed.of_flat fun _ h => by simp [Rule.renderListAt] at h
  | r :: rs, h => by
    simp only [Rule.listHasUnsafe, Bool.or_eq_false_iff] at h
    simp only [Rule.renderListAt]
    exact (Rule.renderAt_wf pretty depth r h.1).append (Rule.renderListAt_wf pretty depth rs h.2)

end

/-- Given no `unsafeRaw`, a rendered stylesheet, compact or pretty, is `WellFormed`: its blocks
nest, whatever strings it was built from, and it can't close the `<style>` element it is
embedded in. -/
theorem Stylesheet.render_wellFormed (s : Stylesheet) (pretty : Bool) (h : s.hasUnsafe = false) :
    WellFormed (s.render pretty) := by
  simp only [Stylesheet.hasUnsafe, Bool.or_eq_false_iff, List.any_eq_false, Bool.not_eq_true]
    at h
  simp only [Stylesheet.render]
  refine WellFormed.append (WellFormed.of_flat (allChars_join fun str hs => ?_))
    (Rule.renderListAt_wf pretty 0 s.rules h.2)
  simp only [List.mem_map] at hs
  obtain ⟨i, hm, rfl⟩ := hs
  have hq := h.1 i hm
  simp only [Import.render, allChars_append]
  refine ⟨⟨⟨by decide, (Value.render_inert _ rfl).mono isFlat_of_inert⟩, ?_⟩, by split <;> decide⟩
  split
  · decide
  · simp only [allChars_append]
    exact ⟨by decide, queries_flat _ _ fun q hq' => by simpa using hq q hq'⟩

end Css
