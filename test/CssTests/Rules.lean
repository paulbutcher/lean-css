/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Css
meta import Css

namespace CssTests

open Css

def sheet : Stylesheet where
  imports := [{ url := "print.css", media := [.type .print] }]
  rules := [
    rule [tag "body", class_ "page"] [margin 0, color .black],
    media [.minWidth (px 600)] [rule [class_ "col"] [width (pct 50)]],
    keyframes "fade" [frame [.from] [opacity 0], frame [.at (pct 50), .to] [opacity 1]]
  ]

#guard sheet.render
  = "@import url(\"print.css\") print;" ++
    "body,.page{margin:0px;color:black}" ++
    "@media (min-width:600px){.col{width:50%}}" ++
    "@keyframes fade{from{opacity:0}50%,to{opacity:1}}"

#guard sheet.render (pretty := true) = "@import url(\"print.css\") print;
body, .page {
  margin: 0px;
  color: black;
}
@media (min-width:600px) {
  .col {
    width: 50%;
  }
}
@keyframes fade {
  from {
    opacity: 0;
  }
  50%, to {
    opacity: 1;
  }
}
"

-- Rules and keyframes of no selectors match nothing, so are left out.
#guard (rule [] [color .red]).render = ""
#guard (keyframes "k" [frame [] [opacity 1]]).rule.render = "@keyframes k{}"

-- A media rule of no queries applies to all media.
#guard (media [] [rule [tag "p"] []]).render = "@media all{p{}}"

-- `or` can't follow a media type without parentheses; `and` and `not` can.
#guard (MediaQuery.typeAnd .screen (.or (.hover) (.pointer .fine))).render
  = "screen and ((hover:hover) or (pointer:fine))"
#guard (MediaQuery.typeAnd .screen (.and (.hover) (.not (.maxWidth (px 300)))) (negated := true)).render
  = "not screen and (hover:hover) and (not (max-width:300px))"
#guard (MediaQuery.and (.or .prefersReducedMotion (.orientation .portrait)) (.hover false)).render
  = "((prefers-reduced-motion:reduce) or (orientation:portrait)) and (hover:none)"

-- `@supports` ignores importance, which isn't part of the test.
#guard (supports (.not (.decl (display .grid).important)) []).render = "@supports not (display:grid){}"
#guard (supports (.and (.selector (tag "a" ++ pseudo (.has []))) (.decl (gap 0))) []).render
  = "@supports selector(a:is()) and (gap:0px){}"

#guard (layer "base" [rule [tag "p"] [color .red]]).rule.render = "@layer base{p{color:red}}"
#guard (Rule.layer none []).render = "@layer{}"
#guard (Rule.layerOrder [.named "reset", .named "base"]).render = "@layer reset,base;"
-- A layer's handle names it in the order, and is no keyframes handle.
def base := layer "base" []
#guard (Rule.layerOrder [.named "reset", base]).render = "@layer reset,base;"
#guard_msgs (drop info) in
#check_failure animation [{ name := base, duration := ms 1 }]
#guard (Rule.layerOrder []).render = ""

#guard (fontFace [fontFamily "X", src [{ url := "x.woff2", format := some "woff2" }, { url := "x.ttf" }]]).render
  = "@font-face{font-family:\"X\";src:url(\"x.woff2\") format(\"woff2\"), url(\"x.ttf\")}"

-- The well-formedness theorem's hypothesis is decidable for a concrete stylesheet.
example : WellFormed (sheet.render true) := sheet.render_wellFormed true (by decide)

def named : Stylesheet := [
  rule [class_ "a" ++ id_ "top", tag "p" ++ pseudo (.not [class_ "b" ++ attr "href"])] [],
  media [] [supports (.selector (class_ "untested")) [rule [pseudo (.is [class_ "c"])] []]],
  layer "l" [rule [tag "li" ++ pseudo (.has [.child (class_ "a" ++ attr "data-x")])] []],
  rule [pseudo (.where [id_ "w"])] [],
]

-- Each name once, from any depth, but not from what `@supports` only tests.
example : named.classNames = ["a", "b", "c"] := by decide
example : named.ids = ["top", "w"] := by decide
example : named.attrNames = ["href", "data-x"] := by decide

-- `unsafeRaw` is the one way to produce something else.
#guard (Stylesheet.mk [] [.unsafeRaw "}</style>"]).hasVerbatim
#guard (Stylesheet.mk [] [rule [tag "p"] [declare "x" [Component.unsafeRaw "}"]]]).hasVerbatim

end CssTests
