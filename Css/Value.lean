/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Css.Num
public import Css.Keywords

@[expose] public section

namespace Css

/-- One component of a property value, at about the level of a CSS token. Every typed value
renders through these, and strings are stored unescaped: `Component.render` is the only place
they are escaped. -/
inductive Component where
  | ident (name : String)
  | number (n : Num)
  | dimension (n : Num) (unit : String)
  | percentage (n : Num)
  | string (s : String)
  | hash (name : String)
  | function (name : String) (args : List Component)
  | parens (inner : List Component)
  | comma
  | slash
  | plus
  | minus
  | times
  /-- Inserted verbatim. The content is trusted as-is, and can end the declaration, the rule, or
  an enclosing `<style>` element. -/
  | unsafeRaw (css : String)
  deriving Repr

/-- A property value: components separated by spaces, but for none before a comma. -/
abbrev Value := List Component

namespace Component

mutual

def render : Component → String
  | .ident n => escapeIdent n
  | .number n => n.render
  | .dimension n u => n.render ++ escapeUnit u
  | .percentage n => n.render ++ "%"
  | .string s => "\"" ++ escapeString s ++ "\""
  | .hash n => "#" ++ escapeName n
  | .function f args => escapeIdent f ++ "(" ++ renderList args ++ ")"
  | .parens inner => "(" ++ renderList inner ++ ")"
  | .comma => ","
  | .slash => "/"
  | .plus => "+"
  | .minus => "-"
  | .times => "*"
  | .unsafeRaw css => css

def renderList : List Component → String
  | [] => ""
  | c :: cs => render c ++ renderTail cs

def renderTail : List Component → String
  | [] => ""
  | c :: cs => (if c matches .comma then "" else " ") ++ render c ++ renderTail cs

end

mutual

def hasVerbatim : Component → Bool
  | .function _ args | .parens args => hasVerbatimList args
  | .unsafeRaw _ => true
  | _ => false

def hasVerbatimList : List Component → Bool
  | [] => false
  | c :: cs => hasVerbatim c || hasVerbatimList cs

end

end Component

def Value.render (v : Value) : String := Component.renderList v

def Value.hasVerbatim (v : Value) : Bool := Component.hasVerbatimList v

/-- Characters which can't appear in a value, a selector, or a media query, because they would
end a declaration or a block, mark a declaration important, or close a `<style>` element. -/
def isInert (c : Char) : Bool := c != '{' && c != '}' && c != ';' && c != '<' && c != '!'

private theorem isInert_of_high (c : Char) (h : 128 ≤ c.toNat) : isInert c = true := by
  have ne : ∀ d : Char, d.toNat < 128 → c ≠ d := fun d hd he => by subst he; omega
  simp [isInert, ne '{' (by decide), ne '}' (by decide), ne ';' (by decide), ne '<' (by decide),
    ne '!' (by decide)]

theorem isInert_of_name :
    ∀ c, (isNameChar c || c == '\\' || c == ' ') = true → isInert c = true :=
  forall_char_of_ascii (by decide) fun c h _ => isInert_of_high c h

theorem isInert_of_string : ∀ c, (isStringChar c || c == '\\') = true → isInert c = true :=
  forall_char_of_ascii (by decide) fun c h _ => isInert_of_high c h

theorem isInert_of_num :
    ∀ c, (c.isDigit || c == '.' || c == '-') = true → isInert c = true :=
  forall_char_of_ascii (by decide) fun c h _ => isInert_of_high c h

namespace Component

mutual

theorem render_inert : (c : Component) → c.hasVerbatim = false → AllChars isInert c.render
  | .ident n, _ => (escapeIdent_safe n).mono isInert_of_name
  | .number n, _ => (Num.render_chars n).mono isInert_of_num
  | .dimension n u, _ => by
    simp only [render, allChars_append]
    exact ⟨(Num.render_chars n).mono isInert_of_num, (escapeUnit_safe u).mono isInert_of_name⟩
  | .percentage n, _ => by
    simp only [render, allChars_append]
    exact ⟨(Num.render_chars n).mono isInert_of_num, by decide⟩
  | .string s, _ => by
    simp only [render, allChars_append]
    exact ⟨⟨by decide, (escapeString_safe s).mono isInert_of_string⟩, by decide⟩
  | .hash n, _ => by
    simp only [render, allChars_append]
    exact ⟨by decide, (escapeName_safe n).mono isInert_of_name⟩
  | .function f args, h => by
    simp only [render, allChars_append]
    exact ⟨⟨⟨(escapeIdent_safe f).mono isInert_of_name, by decide⟩, renderList_inert args h⟩,
      by decide⟩
  | .parens inner, h => by
    simp only [render, allChars_append]
    exact ⟨⟨by decide, renderList_inert inner h⟩, by decide⟩
  | .comma, _ | .slash, _ | .plus, _ | .minus, _ | .times, _ => by decide

theorem renderList_inert :
    (l : List Component) → hasVerbatimList l = false → AllChars isInert (renderList l)
  | [], _ => by decide
  | c :: cs, h => by
    simp only [hasVerbatimList, Bool.or_eq_false_iff] at h
    simp only [renderList, allChars_append]
    exact ⟨render_inert c h.1, renderTail_inert cs h.2⟩

theorem renderTail_inert :
    (l : List Component) → hasVerbatimList l = false → AllChars isInert (renderTail l)
  | [], _ => by decide
  | c :: cs, h => by
    simp only [hasVerbatimList, Bool.or_eq_false_iff] at h
    simp only [renderTail, allChars_append]
    exact ⟨⟨by split <;> decide, render_inert c h.1⟩, renderTail_inert cs h.2⟩

end

end Component

/-- Given no `Component.unsafeRaw`, a rendered value holds none of `{`, `}`, `;`, `<`, or `!`:
whatever strings it was built from, it can't end its declaration or the rule it is in, mark
the declaration important, or close a `<style>` element. -/
theorem Value.render_inert (v : Value) (h : v.hasVerbatim = false) : AllChars isInert v.render :=
  Component.renderList_inert v h

/-- How a typed value is written as a property value. -/
class ToValue (α : Type) where
  toValue : α → Value

export ToValue (toValue)

instance [Keyword α] : ToValue α := ⟨fun k => [.ident (Keyword.keyword k)]⟩

instance : ToValue Value := ⟨id⟩

instance : ToValue Num := ⟨fun n => [.number n]⟩

instance : ToValue Int := ⟨fun n => [.number n]⟩

instance : ToValue Nat := ⟨fun n => [.number n]⟩

instance : ToValue String := ⟨fun s => [.string s]⟩

/-- Values separated by commas. -/
def commaSeparated {α : Type} [ToValue α] (xs : List α) : Value :=
  match xs with
  | [] => []
  | x :: rest => toValue x ++ rest.flatMap fun x => .comma :: toValue x

end Css
