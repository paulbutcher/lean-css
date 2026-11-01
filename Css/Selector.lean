/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Css.Value

@[expose] public section

namespace Css

inductive Combinator where
  | descendant
  | child
  | nextSibling
  | subsequentSibling
  deriving DecidableEq, Repr

def Combinator.render : Combinator → String
  | .descendant => " "
  | .child => ">"
  | .nextSibling => "+"
  | .subsequentSibling => "~"

inductive AttrMatch where
  | present
  | equals (v : String)
  /-- `~=`: one of the attribute's whitespace-separated words. -/
  | includes (v : String)
  /-- `|=`: the attribute, or its prefix up to a `-`. -/
  | dashMatch (v : String)
  | prefix (v : String)
  | suffix (v : String)
  | substring (v : String)
  deriving DecidableEq, Repr

def AttrMatch.render : AttrMatch → String
  | .present => ""
  | .equals v => "=\"" ++ escapeString v ++ "\""
  | .includes v => "~=\"" ++ escapeString v ++ "\""
  | .dashMatch v => "|=\"" ++ escapeString v ++ "\""
  | .prefix v => "^=\"" ++ escapeString v ++ "\""
  | .suffix v => "$=\"" ++ escapeString v ++ "\""
  | .substring v => "*=\"" ++ escapeString v ++ "\""

css_keywords PseudoElement
  | before | after | firstLine | firstLetter | placeholder | selection | marker | backdrop
  | fileSelectorButton

css_keywords PseudoKeyword aliased PseudoClass
  | hover | active | focus | focusVisible | focusWithin | visited | link | anyLink | target
  | checked | indeterminate | disabled | enabled | required | optional | valid | invalid
  | userValid | userInvalid | inRange | outOfRange | readOnly | readWrite | placeholderShown
  | autofill | defaultValue | empty | root | scope | firstChild | lastChild | onlyChild
  | firstOfType | lastOfType | onlyOfType | popoverOpen | modal | fullscreen

mutual

inductive PseudoClass where
  | keyword (k : PseudoKeyword)
  /-- `:nth-child(an+b)` -/
  | nthChild (a b : Int)
  | nthLastChild (a b : Int)
  | nthOfType (a b : Int)
  | nthLastOfType (a b : Int)
  /-- `:not()`. Of no selectors, it matches everything, so is left out. -/
  | not (sels : List Complex)
  | is (sels : List Complex)
  | «where» (sels : List Complex)
  /-- `:has()`. Of no selectors, it matches nothing, so is written `:is()`. -/
  | has (rel : List Relative)

/-- A simple selector other than a type selector. -/
inductive Simple where
  | id (name : String)
  | class_ (name : String)
  | attr (name : String) (m : AttrMatch) (caseInsensitive : Bool)
  | pseudo (p : PseudoClass)

/-- An optional type selector, then simple selectors, then pseudo-elements. With none of these it
is `*`. -/
inductive Compound where
  | mk (type : Option String) (simples : List Simple) (elements : List PseudoElement)

inductive Complex where
  | single (c : Compound)
  | combine (left : Complex) (comb : Combinator) (right : Compound)

/-- A selector relative to the `:has()` subject, as `> img`. -/
inductive Relative where
  | mk (comb : Combinator) (sel : Complex)

end

instance : Coe PseudoKeyword PseudoClass := ⟨.keyword⟩

/-- The `an+b` of `:nth-child()`, written as tersely as the microsyntax allows. -/
def anPlusB (a b : Int) : String :=
  let n (k : Int) := Num.render (k : Num)
  if a = 0 then n b
  else
    (if a = 1 then "" else if a = -1 then "-" else n a) ++ "n" ++
      (if b > 0 then "+" ++ n b else if b < 0 then n b else "")

mutual

def PseudoClass.render : PseudoClass → String
  | .keyword k => ":" ++ escapeIdent (Keyword.keyword k)
  | .nthChild a b => ":nth-child(" ++ anPlusB a b ++ ")"
  | .nthLastChild a b => ":nth-last-child(" ++ anPlusB a b ++ ")"
  | .nthOfType a b => ":nth-of-type(" ++ anPlusB a b ++ ")"
  | .nthLastOfType a b => ":nth-last-of-type(" ++ anPlusB a b ++ ")"
  | .not sels => if sels.isEmpty then "" else ":not(" ++ Complex.renderList sels ++ ")"
  | .is sels => ":is(" ++ Complex.renderList sels ++ ")"
  | .where sels => ":where(" ++ Complex.renderList sels ++ ")"
  | .has rel => if rel.isEmpty then ":is()" else ":has(" ++ Relative.renderList rel ++ ")"

def Simple.render : Simple → String
  | .id n => "#" ++ escapeIdent n
  | .class_ n => "." ++ escapeIdent n
  | .attr n m ci => "[" ++ escapeIdent n ++ m.render ++ (if ci then " i" else "") ++ "]"
  | .pseudo p => p.render

def Simple.renderList : List Simple → String
  | [] => ""
  | s :: ss => s.render ++ Simple.renderList ss

def Compound.render : Compound → String
  | .mk type simples elements =>
    let body := (type.map escapeIdent).getD "" ++ Simple.renderList simples ++
      String.join (elements.map fun e => "::" ++ escapeIdent (Keyword.keyword e))
    if body.isEmpty then "*" else body

def Complex.render : Complex → String
  | .single c => c.render
  | .combine l k r => l.render ++ k.render ++ r.render

/-- A selector list, comma-separated. -/
def Complex.renderList : List Complex → String
  | [] => ""
  | s :: ss => s.render ++ Complex.renderTail ss

def Complex.renderTail : List Complex → String
  | [] => ""
  | s :: ss => "," ++ s.render ++ Complex.renderTail ss

def Relative.render : Relative → String
  | .mk .descendant s => s.render
  | .mk k s => k.render ++ s.render

def Relative.renderList : List Relative → String
  | [] => ""
  | r :: rs => r.render ++ Relative.renderTail rs

def Relative.renderTail : List Relative → String
  | [] => ""
  | r :: rs => "," ++ r.render ++ Relative.renderTail rs

end

/-! ## Building selectors -/

/-- Simple selectors, and pseudo-elements, without a type selector: what follows `tag "a"` in
`a.btn:hover::before`. Pseudo-elements render last, after the simple selectors, wherever they were
appended. -/
structure Subclass where
  simples : List Simple := []
  elements : List PseudoElement := []

instance : Append Subclass := ⟨fun a b => ⟨a.simples ++ b.simples, a.elements ++ b.elements⟩⟩

def Compound.ofSubclass (s : Subclass) : Compound := .mk none s.simples s.elements

instance : HAppend Compound Subclass Compound where
  hAppend | .mk t ss es, s => .mk t (ss ++ s.simples) (es ++ s.elements)

instance : Coe Compound Complex := ⟨.single⟩
instance : Coe Subclass Complex := ⟨fun s => .single (.ofSubclass s)⟩

/-- A type selector, as `tag "nav"` for `nav`. -/
def tag (name : String) : Compound := .mk (some name) [] []

/-- `*` -/
def universal : Compound := .mk none [] []

/-- A class selector, as `cls "btn"` for `.btn`. -/
def cls (name : String) : Subclass := { simples := [.class_ name] }

/-- An ID selector, as `id_ "main"` for `#main`. -/
def id_ (name : String) : Subclass := { simples := [.id name] }

def attr (name : String) (m : AttrMatch := .present) (caseInsensitive : Bool := false) : Subclass :=
  { simples := [.attr name m caseInsensitive] }

def pseudo (p : PseudoClass) : Subclass := { simples := [.pseudo p] }

def pseudoElement (e : PseudoElement) : Subclass := { elements := [e] }

namespace Complex

/-- `a` then `comb`, then all of `b`, so `b`'s leftmost compound is the one related to `a`. -/
def append (a : Complex) (comb : Combinator) : Complex → Complex
  | .single c => .combine a comb c
  | .combine l k r => .combine (append a comb l) k r

end Complex

def descendant (a b : Complex) : Complex := a.append .descendant b
def child (a b : Complex) : Complex := a.append .child b
def nextSibling (a b : Complex) : Complex := a.append .nextSibling b
def subsequentSibling (a b : Complex) : Complex := a.append .subsequentSibling b

instance : Coe Complex Relative := ⟨.mk .descendant⟩

namespace Relative

def child (s : Complex) : Relative := .mk .child s
def nextSibling (s : Complex) : Relative := .mk .nextSibling s
def subsequentSibling (s : Complex) : Relative := .mk .subsequentSibling s

end Relative

/-! ## Safety -/

theorem anPlusB_inert (a b : Int) : AllChars isInert (anPlusB a b) := by
  have n : ∀ k : Int, AllChars isInert (Num.render (k : Num)) := fun k =>
    (Num.render_chars _).mono isInert_of_num
  unfold anPlusB
  split
  · exact n b
  · simp only [allChars_append]
    refine ⟨⟨?_, by decide⟩, ?_⟩
    · split
      · decide
      · split
        · decide
        · exact n a
    · split
      · simp only [allChars_append]; exact ⟨by decide, n b⟩
      · split
        · exact n b
        · decide

theorem AttrMatch.render_inert (m : AttrMatch) : AllChars isInert m.render := by
  have str : ∀ (pre : String) v, AllChars isInert pre →
      AllChars isInert (pre ++ escapeString v ++ "\"") := fun pre v h => by
    simp only [allChars_append]
    exact ⟨⟨h, (escapeString_safe v).mono isInert_of_string⟩, by decide⟩
  cases m <;> first | decide | exact str _ _ (by decide)

private theorem ident_inert (s : String) : AllChars isInert (escapeIdent s) :=
  (escapeIdent_safe s).mono isInert_of_name

private theorem combinator_inert (k : Combinator) : AllChars isInert k.render := by
  cases k <;> decide

private theorem wrap_inert {pre : String} {s : String} (hp : AllChars isInert pre)
    (hs : AllChars isInert s) : AllChars isInert (pre ++ s ++ ")") := by
  simp only [allChars_append]
  exact ⟨⟨hp, hs⟩, by decide⟩

mutual

theorem PseudoClass.render_inert : (p : PseudoClass) → AllChars isInert p.render
  | .keyword k => by
    simp only [PseudoClass.render, allChars_append]; exact ⟨by decide, ident_inert _⟩
  | .nthChild a b | .nthLastChild a b | .nthOfType a b | .nthLastOfType a b =>
    wrap_inert (by decide) (anPlusB_inert a b)
  | .not sels => by
    simp only [PseudoClass.render]
    split
    · decide
    · exact wrap_inert (by decide) (Complex.renderList_inert sels)
  | .is sels | .where sels => wrap_inert (by decide) (Complex.renderList_inert sels)
  | .has rel => by
    simp only [PseudoClass.render]
    split
    · decide
    · exact wrap_inert (by decide) (Relative.renderList_inert rel)

theorem Simple.render_inert : (s : Simple) → AllChars isInert s.render
  | .id n | .class_ n => by
    simp only [Simple.render, allChars_append]; exact ⟨by decide, ident_inert n⟩
  | .attr n m ci => by
    simp only [Simple.render, allChars_append]
    exact ⟨⟨⟨⟨by decide, ident_inert n⟩, m.render_inert⟩, by split <;> decide⟩, by decide⟩
  | .pseudo p => p.render_inert

theorem Simple.renderList_inert : (l : List Simple) → AllChars isInert (Simple.renderList l)
  | [] => by decide
  | s :: ss => by
    simp only [Simple.renderList, allChars_append]
    exact ⟨s.render_inert, Simple.renderList_inert ss⟩

theorem Compound.render_inert : (c : Compound) → AllChars isInert c.render
  | .mk type simples elements => by
    simp only [Compound.render]
    split
    · decide
    · simp only [allChars_append]
      refine ⟨⟨?_, Simple.renderList_inert simples⟩, allChars_join fun s hs => ?_⟩
      · cases type
        · decide
        · exact ident_inert _
      · simp only [List.mem_map] at hs
        obtain ⟨e, _, rfl⟩ := hs
        simp only [allChars_append]
        exact ⟨by decide, ident_inert _⟩

theorem Complex.render_inert : (c : Complex) → AllChars isInert c.render
  | .single c => c.render_inert
  | .combine l k r => by
    simp only [Complex.render, allChars_append]
    exact ⟨⟨l.render_inert, combinator_inert k⟩, r.render_inert⟩

theorem Complex.renderList_inert : (l : List Complex) → AllChars isInert (Complex.renderList l)
  | [] => by decide
  | s :: ss => by
    simp only [Complex.renderList, allChars_append]
    exact ⟨s.render_inert, Complex.renderTail_inert ss⟩

theorem Complex.renderTail_inert : (l : List Complex) → AllChars isInert (Complex.renderTail l)
  | [] => by decide
  | s :: ss => by
    simp only [Complex.renderTail, allChars_append]
    exact ⟨⟨by decide, s.render_inert⟩, Complex.renderTail_inert ss⟩

theorem Relative.render_inert : (r : Relative) → AllChars isInert r.render
  | .mk .descendant s => s.render_inert
  | .mk .child s | .mk .nextSibling s | .mk .subsequentSibling s => by
    simp only [Relative.render, allChars_append]
    exact ⟨by decide, s.render_inert⟩

theorem Relative.renderList_inert : (l : List Relative) → AllChars isInert (Relative.renderList l)
  | [] => by decide
  | r :: rs => by
    simp only [Relative.renderList, allChars_append]
    exact ⟨r.render_inert, Relative.renderTail_inert rs⟩

theorem Relative.renderTail_inert : (l : List Relative) → AllChars isInert (Relative.renderTail l)
  | [] => by decide
  | r :: rs => by
    simp only [Relative.renderTail, allChars_append]
    exact ⟨⟨by decide, r.render_inert⟩, Relative.renderTail_inert rs⟩

end

end Css
