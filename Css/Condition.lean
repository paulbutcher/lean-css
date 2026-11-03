/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Css.Properties
public import Css.Selector

@[expose] public section

namespace Css

/-- `inner` in parentheses, unless it is a leaf that brings its own. -/
def parenthesize (isLeaf : Bool) (inner : String) : String :=
  if isLeaf then inner else "(" ++ inner ++ ")"

/-! ## Media queries -/

css_keywords MediaType | all | screen | print

css_keywords ColorScheme | light | dark

css_keywords Orientation | portrait | landscape

css_keywords PointerAccuracy | none | coarse | fine

inductive MediaCondition where
  | minWidth (l : Length)
  | maxWidth (l : Length)
  | minHeight (l : Length)
  | maxHeight (l : Length)
  | prefersColorScheme (s : ColorScheme)
  /-- `(prefers-reduced-motion: reduce)` -/
  | prefersReducedMotion
  | orientation (o : Orientation)
  /-- `(hover: hover)`, or `(hover: none)` given `false`. -/
  | hover (canHover : Bool := true)
  | pointer (p : PointerAccuracy)
  /-- A feature with no typed counterpart here, as `(name: value)`. -/
  | feature (name : String) (value : Value)
  | and (a b : MediaCondition)
  | or (a b : MediaCondition)
  | not (a : MediaCondition)
  deriving Repr

namespace MediaCondition

def isLeaf : MediaCondition → Bool
  | .and .. | .or .. | .not .. => false
  | _ => true

def renderFeature (name : String) (v : Value) : String :=
  "(" ++ escapeIdent name ++ ":" ++ v.render ++ ")"

/-- The condition, parenthesized only where the grammar needs it to be. -/
def render : MediaCondition → String
  | .minWidth l => renderFeature "min-width" (toValue l)
  | .maxWidth l => renderFeature "max-width" (toValue l)
  | .minHeight l => renderFeature "min-height" (toValue l)
  | .maxHeight l => renderFeature "max-height" (toValue l)
  | .prefersColorScheme s => renderFeature "prefers-color-scheme" (toValue s)
  | .prefersReducedMotion => renderFeature "prefers-reduced-motion" [.ident "reduce"]
  | .orientation o => renderFeature "orientation" (toValue o)
  | .hover b => renderFeature "hover" [.ident (if b then "hover" else "none")]
  | .pointer p => renderFeature "pointer" (toValue p)
  | .feature n v => renderFeature n v
  | .and a b => parenthesize a.isLeaf a.render ++ " and " ++ parenthesize b.isLeaf b.render
  | .or a b => parenthesize a.isLeaf a.render ++ " or " ++ parenthesize b.isLeaf b.render
  | .not a => "not " ++ parenthesize a.isLeaf a.render

def hasVerbatim : MediaCondition → Bool
  | .feature _ v => v.hasVerbatim
  | .and a b | .or a b => a.hasVerbatim || b.hasVerbatim
  | .not a => a.hasVerbatim
  | _ => false

end MediaCondition

inductive MediaQuery where
  | condition (c : MediaCondition)
  | type (t : MediaType) (negated : Bool := false)
  /-- `screen and (...)`, or with `negated`, `not screen and (...)`. -/
  | typeAnd (t : MediaType) (c : MediaCondition) (negated : Bool := false)
  deriving Repr

instance : Coe MediaCondition MediaQuery := ⟨.condition⟩

namespace MediaQuery

export MediaCondition (minWidth maxWidth minHeight maxHeight prefersColorScheme
  prefersReducedMotion orientation hover pointer feature and or not)

def render : MediaQuery → String
  | .condition c => c.render
  | .type t n => (if n then "not " else "") ++ Keyword.keyword t
  | .typeAnd t c n =>
    (if n then "not " else "") ++ Keyword.keyword t ++ " and " ++
      parenthesize (!c matches .or ..) c.render

def hasVerbatim : MediaQuery → Bool
  | .condition c | .typeAnd _ c _ => c.hasVerbatim
  | .type .. => false

end MediaQuery

/-! ## `@supports` -/

inductive SupportsCondition where
  /-- Whether the declaration is supported; its importance is ignored. -/
  | decl (d : Declaration)
  | selector (s : Complex)
  | and (a b : SupportsCondition)
  | or (a b : SupportsCondition)
  | not (a : SupportsCondition)

namespace SupportsCondition

def isLeaf : SupportsCondition → Bool
  | .decl _ | .selector _ => true
  | _ => false

def render : SupportsCondition → String
  | .decl d => "(" ++ escapeIdent d.property ++ ":" ++ d.value.render ++ ")"
  | .selector s => "selector(" ++ s.render ++ ")"
  | .and a b => parenthesize a.isLeaf a.render ++ " and " ++ parenthesize b.isLeaf b.render
  | .or a b => parenthesize a.isLeaf a.render ++ " or " ++ parenthesize b.isLeaf b.render
  | .not a => "not " ++ parenthesize a.isLeaf a.render

def hasVerbatim : SupportsCondition → Bool
  | .decl d => d.hasVerbatim
  | .selector _ => false
  | .and a b | .or a b => a.hasVerbatim || b.hasVerbatim
  | .not a => a.hasVerbatim

end SupportsCondition

/-! ## Safety -/

private theorem ident_inert (s : String) : AllChars isInert (escapeIdent s) :=
  (escapeIdent_safe s).mono isInert_of_name

theorem parenthesize_inert {b : Bool} {s : String} (h : AllChars isInert s) :
    AllChars isInert (parenthesize b s) := by
  unfold parenthesize
  split
  · exact h
  · simp only [allChars_append]; exact ⟨⟨by decide, h⟩, by decide⟩

private theorem feat_inert (n : String) (v : Value) (h : v.hasVerbatim = false) :
    AllChars isInert (MediaCondition.renderFeature n v) := by
  simp only [MediaCondition.renderFeature, allChars_append]
  exact ⟨⟨⟨⟨by decide, ident_inert n⟩, by decide⟩, v.render_inert h⟩, by decide⟩

theorem MediaCondition.render_inert :
    (c : MediaCondition) → c.hasVerbatim = false → AllChars isInert c.render
  | .minWidth _, _ | .maxWidth _, _ | .minHeight _, _ | .maxHeight _, _
  | .prefersColorScheme _, _ | .prefersReducedMotion, _ | .orientation _, _ | .hover _, _
  | .pointer _, _ => feat_inert _ _ rfl
  | .feature _ v, h => feat_inert _ v h
  | .and a b, h | .or a b, h => by
    simp only [hasVerbatim, Bool.or_eq_false_iff] at h
    simp only [render, allChars_append]
    exact ⟨⟨parenthesize_inert (a.render_inert h.1), by decide⟩,
      parenthesize_inert (b.render_inert h.2)⟩
  | .not a, h => by
    simp only [render, allChars_append]
    exact ⟨by decide, parenthesize_inert (a.render_inert h)⟩

theorem MediaQuery.render_inert (q : MediaQuery) (h : q.hasVerbatim = false) :
    AllChars isInert q.render := by
  cases q with
  | condition c => exact c.render_inert h
  | type t n =>
    simp only [render, allChars_append]
    exact ⟨by split <;> decide, by cases t <;> decide⟩
  | typeAnd t c n =>
    simp only [render, allChars_append]
    exact ⟨⟨⟨by split <;> decide, by cases t <;> decide⟩, by decide⟩,
      parenthesize_inert (c.render_inert h)⟩

theorem SupportsCondition.render_inert :
    (c : SupportsCondition) → c.hasVerbatim = false → AllChars isInert c.render
  | .decl d, h => by
    simp only [render, allChars_append]
    exact ⟨⟨⟨⟨by decide, ident_inert _⟩, by decide⟩, d.value.render_inert h⟩, by decide⟩
  | .selector s, _ => by
    simp only [render, allChars_append]
    exact ⟨⟨by decide, s.render_inert⟩, by decide⟩
  | .and a b, h | .or a b, h => by
    simp only [hasVerbatim, Bool.or_eq_false_iff] at h
    simp only [render, allChars_append]
    exact ⟨⟨parenthesize_inert (a.render_inert h.1), by decide⟩,
      parenthesize_inert (b.render_inert h.2)⟩
  | .not a, h => by
    simp only [render, allChars_append]
    exact ⟨by decide, parenthesize_inert (a.render_inert h)⟩

end Css
