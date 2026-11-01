/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Css
meta import Css

namespace CssTests

open Css

-- Identifiers: name characters pass through; what can't start one is escaped.
#guard escapeIdent "btn-primary_2" = "btn-primary_2"
#guard escapeIdent "--brand" = "--brand"
#guard escapeIdent "2col" = "\\32 col"
#guard escapeIdent "-2" = "-\\32 "
#guard escapeIdent "-" = "\\-"
#guard escapeIdent "a b.c" = "a\\20 b\\2e c"
#guard escapeIdent "naïve" = "naïve"

-- A unit starting like an exponent is escaped, so `1e3x` isn't read as the number 1000.
#guard escapeUnit "e3x" = "\\65 3x"
#guard escapeUnit "em" = "em"

-- A string can't be closed, or close a `<style>` element, from inside.
#guard escapeString "say \"hi\"\n</style>" = "say \\22 hi\\22 \\a \\3c /style\\3e "

-- `#` names may start with a digit.
#guard escapeName "1a" = "1a"

end CssTests
