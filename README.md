# CSS

A Lean 4 library for building CSS. It represents stylesheets as typed Lean values, so a property given a value of the wrong kind (e.g. `color (px 4)`, or `display .bold`) or a selector put together out of order (e.g. a second type selector in one compound) is a type error rather than a silently dropped declaration, and every name and string is escaped automatically. `Stylesheet.render_wellFormed` proves that, as long as you don't reach for `unsafeRaw`, the CSS this library produces always nests its blocks properly and can never close the `<style>` element it is embedded in.

It is to CSS what [lean-html](https://github.com/paulbutcher/lean-html) is to HTML.

## Installation

Add it to your `lakefile.toml`:

```toml
[[require]]
name = "css"
git = "https://github.com/paulbutcher/lean-css"
```

## Usage

```lean
import Css

open Css

def site : Stylesheet := [
  rule [tag "body"] [margin 0, fontFamily ⟨"Inter", [.sansSerif]⟩, lineHeight 1.5],
  rule [cls "card", tag "article" ++ cls "card"] [
    padding (rem 1),
    borderRadius (px 8),
    border { width := px 1, style := .solid, color := .hex 0xdddddd },
  ],
  rule [tag "a" ++ pseudo .hover] [color .rebeccapurple, textDecoration .underline],
  rule [child (cls "nav") (tag "li" ++ pseudo (.nthChild 2 1))] [backgroundColor .whitesmoke],
  media [.minWidth (px 768)] [
    rule [cls "grid"] [display .grid, gridTemplateColumns [.repeat 3 [fr 1]], gap (rem 1)],
  ],
  keyframes "spin" [frame [.to] [transform [.rotate (turn 1)]]],
]

#eval IO.println (site.render (pretty := true))
```

`site.render` is the stylesheet as a compact `String`; `(pretty := true)` indents it instead.

- A property (`color`, `margin`, `display`, ...) is a `Property α`, applied to a value of type `α` to give a `Declaration`. Keywords are constructors, so `display .flex` and `color .red`, and literals and coercions reach the property's type: `margin 0`, `margin (.two (px 4) .auto)`, `lineHeight 1.5`, `fontWeight 600`.
- Every property takes the CSS-wide keywords, `color.inherit`, and a custom property, `color.var "brand" (some .black)`. `custom "brand" (Color.hex 0x336699)` declares one, and `d.important` marks a declaration `!important`.
- Lengths and the like are built with `px`, `em`, `rem`, `vw`, `pct`, `deg`, `ms`, and so on, from exact decimals, so `px 1.5` renders as `1.5px`. `+`, `-`, `*`, and `/` on them build `calc()`, with only the parentheses it needs; where a property takes something wider than `LengthPercentage`, such as `OrAuto LengthPercentage`, wrap the arithmetic in `calc_`. `clamp`, `.min`, and `.max` are there too.
- Shorthands such as `border`, `boxShadow`, `transition`, and `animation` take records, leaving out parts at their initial values. A list property given `[]` renders `none`.
- `declare name value` sets a property with no typed counterpart here, with a `Value` (a list of `Component`s) or any typed value; it is escaped like any other, so is as safe, but isn't checked.
- `inlineStyle decls` renders declarations for an HTML `style` attribute.

## Selectors

- `tag "a"` is a type selector, `universal` is `*`, and `cls`, `id_`, `attr`, `pseudo`, and `pseudoElement` are the rest of a compound selector, joined with `++`: `tag "a" ++ cls "btn" ++ pseudo .hover`. Only a type selector can start one, and only once. Pseudo-elements render last, after the pseudo-classes, wherever they were appended.
- `descendant`, `child`, `nextSibling`, and `subsequentSibling` combine selectors. `pseudo (.not [...])`, `.is`, `.where`, and `.has` take selector lists, `.has` relative ones such as `.child (tag "img")`.
- A rule takes a list of selectors, and where a list of selectors or keyframe selectors is empty, the output says what the empty list means: a rule or keyframe of no selectors is left out, `:not()` of none matches everything, so is left out too, and `:has()` of none matches nothing, so is written `:is()`.

## At-rules

- `media`, with typed queries such as `.minWidth (px 600)`, `.prefersColorScheme .dark`, and `.typeAnd .screen (...)`, combined with `.and`, `.or`, and `.not`, and parenthesized where the grammar requires. `.feature name value` covers the rest.
- `supports`, testing declarations and selectors; `layer`, `Rule.layerOrder`, `keyframes`, and `fontFace`, with the `src` and `fontDisplay` descriptors.
- A `Stylesheet` takes `imports`, rendered first, where CSS requires them.
- Not modelled: nesting, `@container`, `@page`, `@property`, `@scope`, and namespaces.

## `unsafeRaw`

`Component.unsafeRaw` and `Rule.unsafeRaw` insert CSS verbatim. They are trusted as-is, so can end a declaration or a rule early, or close the enclosing `<style>` element and inject markup, and they are exactly what `render_wellFormed`'s hypothesis rules out.

## Formal verification

- `Stylesheet.render_wellFormed`: given no `unsafeRaw`, the rendered stylesheet, compact or pretty, is `WellFormed`: every `}` closes an earlier `{` and every `{` is closed, and it contains no `<`. `decide` proves the hypothesis for a concrete stylesheet.
- `Value.render_inert`: no value, selector, or media query contains `{`, `}`, `;`, `<`, or `!`, whatever strings it was built from, so none can end its declaration or block or mark it important. `Declaration.render_inline` is the same for a declaration in a `style` attribute.
- `escapeIdent_safe`, `escapeIdent_start`, `escapeString_safe`, `escapeName_safe`, and `escapeUnit_safe` are the escaping facts these rest on.

## License

This library is released under the Apache 2.0 license. See the LICENSE file for the complete license text.
