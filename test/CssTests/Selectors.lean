/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Css
meta import Css

namespace CssTests

open Css

def sel (c : Complex) : String := c.render

#guard sel (tag "a" ++ cls "btn" ++ pseudo .hover) = "a.btn:hover"
#guard sel (cls "a" ++ id_ "b" ++ attr "href") = ".a#b[href]"
#guard sel (attr "lang" (.dashMatch "en") (caseInsensitive := true)) = "[lang|=\"en\" i]"

-- Pseudo-elements go last, wherever they were appended.
#guard sel (tag "p" ++ (pseudoElement .firstLine ++ cls "lead")) = "p.lead::first-line"

-- A compound of nothing is the universal selector.
#guard sel universal = "*"
#guard sel (Compound.ofSubclass {}) = "*"
#guard sel (pseudo (.not [])) = "*"

#guard sel (descendant (cls "nav") (tag "a")) = ".nav a"
#guard sel (child (tag "ul") (tag "li")) = "ul>li"
#guard sel (nextSibling (tag "h1") (tag "p")) = "h1+p"
#guard sel (subsequentSibling (tag "h1") (tag "p")) = "h1~p"
-- The right side's leftmost compound is the one related to the left side.
#guard sel (child (cls "a") (descendant (cls "b") (cls "c"))) = ".a>.b .c"

#guard sel (pseudo (.nthChild 2 1)) = ":nth-child(2n+1)"
#guard sel (pseudo (.nthChild 0 3)) = ":nth-child(3)"
#guard sel (pseudo (.nthLastOfType (-1) 3)) = ":nth-last-of-type(-n+3)"
#guard sel (pseudo (.nthOfType 1 (-2))) = ":nth-of-type(n-2)"

#guard sel (pseudo (.is [tag "h1", tag "h2"])) = ":is(h1,h2)"
#guard sel (pseudo (.where [])) = ":where()"
#guard sel (tag "a" ++ pseudo (.not [cls "x", attr "disabled"])) = "a:not(.x,[disabled])"
#guard sel (tag "li" ++ pseudo (.has [.nextSibling (tag "li"), cls "on"])) = "li:has(+li,.on)"
-- `:has()` of nothing matches nothing, which `:has()` itself can't say.
#guard sel (tag "li" ++ pseudo (.has [])) = "li:is()"

-- Names are escaped, so none can turn into other syntax.
#guard sel (cls "1st" ++ id_ "a b") = ".\\31 st#a\\20 b"
#guard sel (attr "x" (.equals "\"]{")) = "[x=\"\\22 ]\\7b \"]"

end CssTests
