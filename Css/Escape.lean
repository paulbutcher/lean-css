/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

@[expose] public section

namespace Css

/-- Every character of `s` satisfies `p`. -/
def AllChars (p : Char → Bool) (s : String) : Prop := ∀ c ∈ s.toList, p c = true

instance {p : Char → Bool} {s : String} : Decidable (AllChars p s) :=
  inferInstanceAs (Decidable (∀ c ∈ s.toList, p c = true))

@[simp] theorem allChars_append {p : Char → Bool} {a b : String} :
    AllChars p (a ++ b) ↔ AllChars p a ∧ AllChars p b := by
  simp [AllChars, String.toList_append, or_imp, forall_and]

theorem AllChars.mono {p q : Char → Bool} {s : String} (h : ∀ c, p c = true → q c = true)
    (hs : AllChars p s) : AllChars q s :=
  fun c hc => h c (hs c hc)

theorem allChars_join {p : Char → Bool} {l : List String} (h : ∀ s ∈ l, AllChars p s) :
    AllChars p (String.join l) := by
  intro c hc
  simp only [String.toList_join, List.mem_flatMap] at hc
  obtain ⟨s, hs, hc⟩ := hc
  exact h s hs c hc

theorem allChars_ofList {p : Char → Bool} {l : List Char} (h : ∀ c ∈ l, p c = true) :
    AllChars p (String.ofList l) := by
  simpa [AllChars] using h

/-- A fact about every character follows from one about the ASCII range, which `decide` can
check, and one about the rest. -/
theorem forall_char_of_ascii {P : Char → Prop} (ascii : ∀ n : Fin 128, P (Char.ofNat n))
    (high : ∀ c : Char, 128 ≤ c.toNat → P c) (c : Char) : P c := by
  if h : c.toNat < 128 then simpa [Char.ofNat_toNat] using ascii ⟨c.toNat, h⟩
  else exact high c (by omega)

def isHexDigit (c : Char) : Bool := c.isDigit || ('a' ≤ c && c ≤ 'f')

def hexDigit (d : Fin 16) : Char :=
  match d.val with
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3' | 4 => '4' | 5 => '5' | 6 => '6' | 7 => '7'
  | 8 => '8' | 9 => '9' | 10 => 'a' | 11 => 'b' | 12 => 'c' | 13 => 'd' | 14 => 'e' | _ => 'f'

/-- Lowercase hexadecimal digits of `n`, most significant first. -/
def hexDigits (n : Nat) : List Char :=
  if h : n < 16 then [hexDigit ⟨n, h⟩]
  else hexDigits (n / 16) ++ [hexDigit ⟨n % 16, Nat.mod_lt _ (by decide)⟩]
termination_by n
decreasing_by omega

theorem hexDigits_hex (n : Nat) : ∀ c ∈ hexDigits n, isHexDigit c = true := by
  have hd : ∀ d, isHexDigit (hexDigit d) = true := by decide
  fun_induction hexDigits n with
  | case1 => simpa using hd _
  | case2 _ _ ih =>
    intro c hc
    simp only [List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · exact ih c hc
    · exact hd _

/-- CSS's `ident code point`, which `escapeIdent` and `escapeName` leave as they are. -/
def isNameChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '-' || 0x80 ≤ c.toNat

/-- Characters `escapeString` leaves as they are: printable ASCII and anything beyond, less those
that end a string or a block, start an escape, or could close a `<style>` element. -/
def isStringChar (c : Char) : Bool :=
  (0x20 ≤ c.toNat && c.toNat < 0x7f && c != '"' && c != '\\' && c != '{' && c != '}' &&
    c != ';' && c != '<' && c != '>' && c != '!') || 0x80 ≤ c.toNat

/-- The characters an escape is written with. -/
def isEscapeChar (c : Char) : Bool := c == '\\' || isHexDigit c || c == ' '

/-- A hex escape. The trailing space ends it, and is consumed with it, so what follows can be
anything, a hex digit included. -/
def hexEscape (c : Char) : String := "\\" ++ String.ofList (hexDigits c.toNat) ++ " "

def escapeWith (keep : Char → Bool) (l : List Char) : String :=
  String.join (l.map fun c => if keep c then String.singleton c else hexEscape c)

/-- A CSS name, as follows the `#` of a hash token: every character outside `isNameChar`
escaped. -/
def escapeName (s : String) : String := escapeWith isNameChar s.toList

/-- A CSS identifier, after CSSOM's "serialize an identifier": as `escapeName`, and also a
leading digit, a digit after a leading `-`, and a lone `-`, none of which can start one. -/
def escapeIdent (s : String) : String :=
  match s.toList with
  | ['-'] => "\\-"
  | '-' :: c :: rest => "-" ++ lead c ++ escapeWith isNameChar rest
  | c :: rest => lead c ++ escapeWith isNameChar rest
  | [] => ""
where
  lead (c : Char) : String := if c.isDigit then hexEscape c else escapeWith isNameChar [c]

/-- The unit of a dimension, which follows its number directly. As `escapeIdent`, and also a
leading `e` before a digit or `-`, which would otherwise be read as the number's exponent. -/
def escapeUnit (u : String) : String :=
  match u.toList with
  | c :: d :: rest =>
    if (c == 'e' || c == 'E') && (d.isDigit || d == '-') then
      hexEscape c ++ escapeWith isNameChar (d :: rest)
    else escapeIdent u
  | _ => escapeIdent u

/-- The contents of a double-quoted CSS string: every character outside `isStringChar`
escaped. -/
def escapeString (s : String) : String := escapeWith isStringChar s.toList

theorem hexEscape_chars (c : Char) : AllChars isEscapeChar (hexEscape c) := by
  simp only [hexEscape, allChars_append]
  refine ⟨⟨by decide, allChars_ofList fun c hc => ?_⟩, by decide⟩
  simp [isEscapeChar, hexDigits_hex _ c hc]

theorem escapeWith_chars (keep : Char → Bool) (l : List Char) :
    AllChars (fun c => keep c || isEscapeChar c) (escapeWith keep l) := by
  refine allChars_join fun s hs => ?_
  simp only [List.mem_map] at hs
  obtain ⟨c, _, rfl⟩ := hs
  split
  · intro c' hc'
    simp only [String.toList_singleton, List.mem_singleton] at hc'
    subst hc'
    simp [*]
  · exact (hexEscape_chars c).mono fun c h => by simp [h]

private theorem name_of_escape :
    ∀ c, isEscapeChar c = true → (isNameChar c || c == '\\' || c == ' ') = true :=
  forall_char_of_ascii (by decide) fun c h _ => by simp [isNameChar, h]

private theorem escapeWith_name (l : List Char) :
    AllChars (fun c => isNameChar c || c == '\\' || c == ' ') (escapeWith isNameChar l) :=
  (escapeWith_chars _ l).mono fun c h => by
    simp only [Bool.or_eq_true] at h
    rcases h with h | h
    · simp [h]
    · exact name_of_escape c h

private theorem hexEscape_name (c : Char) :
    AllChars (fun c => isNameChar c || c == '\\' || c == ' ') (hexEscape c) :=
  (hexEscape_chars c).mono name_of_escape

/-- `escapeIdent`'s output holds nothing but name characters and escapes, so whatever it is
given, it is one identifier and can't end the construct it stands in. -/
theorem escapeIdent_safe (s : String) :
    AllChars (fun c => isNameChar c || c == '\\' || c == ' ') (escapeIdent s) := by
  have lead : ∀ c, AllChars (fun c => isNameChar c || c == '\\' || c == ' ')
      (escapeIdent.lead c) := fun c => by
    unfold escapeIdent.lead
    split
    · exact hexEscape_name c
    · exact escapeWith_name _
  unfold escapeIdent
  split
  · decide
  · simp only [allChars_append]
    exact ⟨⟨by decide, lead _⟩, escapeWith_name _⟩
  · simp only [allChars_append]
    exact ⟨lead _, escapeWith_name _⟩
  · decide

/-- Whether `l` can start an identifier, as far as digits go: it doesn't start with a digit, or
with `-` then a digit. -/
def identStart : List Char → Bool
  | c :: rest => !c.isDigit && (c != '-' || rest.head?.all (!·.isDigit))
  | [] => true

private theorem hexEscape_toList (c : Char) : ∃ t, (hexEscape c).toList = '\\' :: t :=
  ⟨hexDigits c.toNat ++ [' '], by simp [hexEscape]⟩

/-- What `escapeIdent_safe` leaves out: the output starts as an identifier can, so it isn't read
as a number or a dimension instead. -/
theorem escapeIdent_start (s : String) : identStart (escapeIdent s).toList = true := by
  have lead : ∀ c, ∃ d t, (escapeIdent.lead c).toList = d :: t ∧
      d.isDigit = false ∧ (d = '\\' ∨ d = c) := by
    intro c
    unfold escapeIdent.lead
    split
    · obtain ⟨t, ht⟩ := hexEscape_toList c
      exact ⟨'\\', t, ht, by decide, .inl rfl⟩
    · rename_i hc
      simp only [escapeWith, List.map_cons, List.map_nil, String.join_cons, String.join_nil,
        String.append_empty]
      split
      · exact ⟨c, [], by simp, by simpa using hc, .inr rfl⟩
      · obtain ⟨t, ht⟩ := hexEscape_toList c
        exact ⟨'\\', t, ht, by decide, .inl rfl⟩
  unfold escapeIdent
  split
  next => decide
  next _ c rest _ =>
    obtain ⟨d, t, h, hd, -⟩ := lead c
    simp [identStart, String.toList_append, h, hd]
  next _ c rest h1 h2 _ =>
    obtain ⟨d, t, h, hd, hdc⟩ := lead c
    simp only [String.toList_append, h, List.cons_append, identStart, hd]
    simp only [Bool.not_false, Bool.true_and, Bool.or_eq_true, bne_iff_ne, ne_eq]
    left
    rintro rfl
    rcases hdc with hdc | rfl
    · exact absurd hdc (by decide)
    · cases rest with
      | nil => exact h1 rfl rfl
      | cons x xs => exact h2 x xs rfl rfl
  next => decide

theorem escapeName_safe (s : String) :
    AllChars (fun c => isNameChar c || c == '\\' || c == ' ') (escapeName s) :=
  escapeWith_name _

theorem escapeUnit_safe (s : String) :
    AllChars (fun c => isNameChar c || c == '\\' || c == ' ') (escapeUnit s) := by
  unfold escapeUnit
  split
  · split
    · simp only [allChars_append]
      exact ⟨hexEscape_name _, escapeWith_name _⟩
    · exact escapeIdent_safe s
  · exact escapeIdent_safe s

private theorem string_of_escape :
    ∀ c, isEscapeChar c = true → (isStringChar c || c == '\\') = true :=
  forall_char_of_ascii (by decide) fun c h _ => by simp [isStringChar, h]

/-- `escapeString`'s output holds no `"`, newline, or `\` but the one starting an escape, so
between a pair of `"` it is one string, and none of `{`, `}`, `;`, `<`, `>`, or `!`, so it can't
be mistaken for structure by anything that scans characters without tokenizing. -/
theorem escapeString_safe (s : String) :
    AllChars (fun c => isStringChar c || c == '\\') (escapeString s) :=
  (escapeWith_chars _ _).mono fun c h => by
    simp only [Bool.or_eq_true] at h
    rcases h with h | h
    · simp [h]
    · exact string_of_escape c h

end Css
