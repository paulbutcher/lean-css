/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Css
meta import Css

namespace CssTests

open Css

def r (d : Declaration) : String := d.render

-- Numbers are exact and written without an exponent or trailing zeros.
#guard [(1.50 : Num), 1e3, 0.001, -2.5, -0.0, 10].map Num.render
  = ["1.5", "1000", "0.001", "-2.5", "0", "10"]

-- Arithmetic becomes `calc()`, with parentheses only where precedence needs them.
#guard r (width (px 100 - pct 10)) = "width:calc(100px - 10%)"
#guard r (width (calc_ ((px 100 - pct 10) / 2))) = "width:calc((100px - 10%) / 2)"
#guard r (width (calc_ (px 1 - (px 2 + px 3)))) = "width:calc(1px - (2px + 3px))"
#guard r (width (calc_ (px 1 + px 2 + px 3))) = "width:calc(1px + 2px + 3px)"
#guard r (width (calc_ (px 4 + em 2 * 3))) = "width:calc(4px + 2em * 3)"
#guard r (fontSize (clamp (rem 1) (vw 2 + rem 0.5) (rem 2)))
  = "font-size:clamp(1rem, 2vw + 0.5rem, 2rem)"
#guard r (width (.val (.min (pct 100) (px 600)))) = "width:min(100%, 600px)"

-- Coercions and literals reach the property's type.
#guard r (margin 0) = "margin:0px"
#guard r (margin (.two 0 .auto)) = "margin:0px auto"
#guard r (padding (.four (px 1) (px 2) (px 3) (pct 4))) = "padding:1px 2px 3px 4%"
#guard r (lineHeight 1.5) = "line-height:1.5"
#guard r (fontWeight 600) = "font-weight:600"
#guard r (fontSize .xxLarge) = "font-size:xx-large"
#guard r (zIndex (.val (-1))) = "z-index:-1"
#guard r (aspectRatio (.ratio 16 9)) = "aspect-ratio:16 / 9"

-- Colors.
#guard r (color .rebeccapurple) = "color:rebeccapurple"
#guard r (color (.hex 0xff)) = "color:#0000ff"
#guard r (color (.rgb 255 0 0)) = "color:rgb(255 0 0)"
#guard r (color (.rgb 255 0 0 0.5)) = "color:rgb(255 0 0 / 0.5)"
#guard r (color .currentColor) = "color:currentcolor"

-- Shorthands leave out parts at their initial values.
#guard r (border { style := .solid }) = "border:solid"
#guard r (border { width := px 1, style := .dashed, color := .red }) = "border:1px dashed red"
#guard r (boxShadow [{ x := px 1, y := px 2 }]) = "box-shadow:1px 2px"
#guard r (boxShadow [{ x := 0, y := 0, spread := px 2, color := .blue, inset := true }])
  = "box-shadow:inset 0px 0px 0px 2px blue"
#guard r (transition [{ duration := ms 150 }, { property := "color", duration := sec 1, delay := ms 50 }])
  = "transition:all 150ms, color 1s ease 50ms"
#guard r (animation [{ name := "fade", duration := ms 300, fillMode := .forwards }])
  = "animation:300ms forwards fade"

-- An empty list is `none`, where the property has it.
#guard r (boxShadow []) = "box-shadow:none"
#guard r (transform []) = "transform:none"
#guard r (backgroundImage []) = "background-image:none"
#guard r (gridTemplateColumns []) = "grid-template-columns:none"

#guard r (gridTemplateColumns [px 200, .minmax (px 100) (fr 1), .autoFit [fr 1]])
  = "grid-template-columns:200px minmax(100px, 1fr) repeat(auto-fit, 1fr)"
#guard r (gridRow (.range 2 (.span 3))) = "grid-row:2 / span 3"
#guard r (fontFamily ⟨"Fira Code", [.uiMonospace, .monospace]⟩)
  = "font-family:\"Fira Code\", ui-monospace, monospace"
#guard r (backgroundImage [.linearGradient (deg 180) [stop .white, stop .black (pct 80)], url "a.png"])
  = "background-image:linear-gradient(180deg, white, black 80%), url(\"a.png\")"

-- CSS-wide keywords, custom properties, and importance.
#guard r color.revertLayer = "color:revert-layer"
#guard r (custom "gap" (rem 2)) = "--gap:2rem"
#guard r (gap.var "gap" (some (rem 1))) = "gap:var(--gap, 1rem)"
#guard (display .grid).important.render true = "display: grid !important"

-- Untrusted strings stay inside the value.
#guard r (content "}</style><script>") = "content:\"\\7d \\3c /style\\3e \\3c script\\3e \""
#guard r (declare "x;y" (Component.ident "a}b" :: [])) = "x\\3b y:a\\7d b"

#guard inlineStyle [color .red, marginTop (em 1)] = "color:red;margin-top:1em"

end CssTests
