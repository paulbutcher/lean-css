/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Css.Keywords
public import Css.Escape
public import Css.Num
public import Css.Value
public import Css.Types
public import Css.Properties
public import Css.Selector
public import Css.Condition
public import Css.Stylesheet

/-!
# `Css`: a typed CSS library

Builds CSS from Lean values. Typed values (`Css/Types.lean`) render through `Component`, the one
place strings are escaped, so the safety facts are proven once, there; `Stylesheet.render_wellFormed`
lifts them to a whole stylesheet.
-/
