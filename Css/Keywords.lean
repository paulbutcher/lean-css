/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public meta import Lean.Elab.Command

@[expose] public section

namespace Css

/-- A type whose values each stand for one CSS keyword. -/
class Keyword (α : Type) where
  keyword : α → String

/-- `inlineBlock` becomes `inline-block`. -/
meta def kebab (s : String) : String :=
  s.foldl (fun acc c => if c.isUpper then (acc.push '-').push c.toLower else acc.push c) ""

open Lean in
/-- `css_keywords T | a | bC` declares an enumeration `T` whose constructors render as the CSS
keywords `a` and `b-c`. `css_keywords T aliased U V | ...` also exports each constructor into
namespaces `U` and `V`, so that, given a coercion from `T`, `.a` elaborates against either. -/
syntax (docComment)? "css_keywords " ident (" aliased " ident+)? (" | " ident)+ : command

open Lean in
macro_rules
  | `($[$doc?]? css_keywords $name $[aliased $aliases*]? $[| $ctors]*) => do
    let ctorDecls ← ctors.mapM fun c => `(Lean.Parser.Command.ctor| | $c:ident)
    let pats := ctors.map fun c => mkIdent (name.getId ++ c.getId)
    let strs := ctors.map fun c => Syntax.mkStrLit (kebab (c.getId.toString (escape := false)))
    let decl ← `($[$doc?]? inductive $name where $ctorDecls* deriving DecidableEq, Repr
      instance : Keyword $name where keyword $[| $pats => $strs]*)
    let exports ← (aliases.getD #[]).flatMapM fun a => do
      return #[← `(command| namespace $a), ← `(command| export $name ($ctors*)),
        ← `(command| end $a)]
    return mkNullNode (#[decl.raw] ++ exports.map (·.raw))

end Css
