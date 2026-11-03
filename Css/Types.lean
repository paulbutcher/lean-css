/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Css.Value

@[expose] public section

namespace Css

css_keywords Global | inherit | initial | unset | revert | revertLayer

/-! ## Dimensions -/

css_keywords LengthUnit
  | px | em | rem | ex | ch | cap | ic | lh | rlh | vw | vh | vi | vb | vmin | vmax | svw | svh
  | lvw | lvh | dvw | dvh | cqw | cqh | cqi | cqb | cqmin | cqmax | cm | mm | q | «in» | pt | pc

structure Length where
  value : Num
  unit : LengthUnit
  deriving DecidableEq, Repr

instance : OfNat Length 0 := ⟨⟨0, .px⟩⟩
instance : ToValue Length := ⟨fun l => [.dimension l.value (Keyword.keyword l.unit)]⟩

def px (n : Num) : Length := ⟨n, .px⟩
def em (n : Num) : Length := ⟨n, .em⟩
def rem (n : Num) : Length := ⟨n, .rem⟩
def ex (n : Num) : Length := ⟨n, .ex⟩
def ch (n : Num) : Length := ⟨n, .ch⟩
def lh (n : Num) : Length := ⟨n, .lh⟩
def vw (n : Num) : Length := ⟨n, .vw⟩
def vh (n : Num) : Length := ⟨n, .vh⟩
def vmin (n : Num) : Length := ⟨n, .vmin⟩
def vmax (n : Num) : Length := ⟨n, .vmax⟩
def svh (n : Num) : Length := ⟨n, .svh⟩
def dvh (n : Num) : Length := ⟨n, .dvh⟩
def cm (n : Num) : Length := ⟨n, .cm⟩
def mm (n : Num) : Length := ⟨n, .mm⟩
def pt (n : Num) : Length := ⟨n, .pt⟩

structure Percentage where
  value : Num
  deriving DecidableEq, Repr

instance : ToValue Percentage := ⟨fun p => [.percentage p.value]⟩

def pct (n : Num) : Percentage := ⟨n⟩

css_keywords AngleUnit | deg | grad | rad | turn

structure Angle where
  value : Num
  unit : AngleUnit
  deriving DecidableEq, Repr

instance : OfNat Angle 0 := ⟨⟨0, .deg⟩⟩
instance : ToValue Angle := ⟨fun a => [.dimension a.value (Keyword.keyword a.unit)]⟩

def deg (n : Num) : Angle := ⟨n, .deg⟩
def grad (n : Num) : Angle := ⟨n, .grad⟩
def rad (n : Num) : Angle := ⟨n, .rad⟩
def turn (n : Num) : Angle := ⟨n, .turn⟩

css_keywords TimeUnit | s | ms

structure Time where
  value : Num
  unit : TimeUnit
  deriving DecidableEq, Repr

instance : OfNat Time 0 := ⟨⟨0, .s⟩⟩
instance : ToValue Time := ⟨fun t => [.dimension t.value (Keyword.keyword t.unit)]⟩

def sec (n : Num) : Time := ⟨n, .s⟩
def ms (n : Num) : Time := ⟨n, .ms⟩

/-! ## `<length-percentage>` and math functions -/

/-- A length or percentage, or a math function of them. Arithmetic renders as `calc()`, which the
`+`, `-`, `*`, and `/` instances below build, with only the parentheses the expression needs. -/
inductive LengthPercentage where
  | length (l : Length)
  | percentage (p : Percentage)
  | add (a b : LengthPercentage)
  | sub (a b : LengthPercentage)
  | mul (a : LengthPercentage) (k : Num)
  | div (a : LengthPercentage) (k : Num)
  | min (a b : LengthPercentage)
  | max (a b : LengthPercentage)
  | clamp (lo val hi : LengthPercentage)
  deriving DecidableEq, Repr

namespace LengthPercentage

/-- The expression as it appears inside a math function. -/
def expr : LengthPercentage → Value
  | .length l => toValue l
  | .percentage p => toValue p
  | .add a b => a.expr ++ .plus :: b.expr
  | .sub a b => a.expr ++ .minus :: (if b matches .add .. | .sub .. then [.parens b.expr] else b.expr)
  | .mul a k => (if a matches .add .. | .sub .. then [.parens a.expr] else a.expr) ++ [.times, .number k]
  | .div a k => (if a matches .add .. | .sub .. then [.parens a.expr] else a.expr) ++ [.slash, .number k]
  | .min a b => [.function "min" (a.expr ++ .comma :: b.expr)]
  | .max a b => [.function "max" (a.expr ++ .comma :: b.expr)]
  | .clamp lo v hi => [.function "clamp" (lo.expr ++ .comma :: v.expr ++ .comma :: hi.expr)]

instance : ToValue LengthPercentage where
  toValue x := if x matches .add .. | .sub .. | .mul .. | .div .. then [.function "calc" x.expr]
    else x.expr

end LengthPercentage

/-- A type that `+`, `-`, `*`, and `/` combine into a `LengthPercentage`. -/
class ToLengthPercentage (α : Type) where
  toLengthPercentage : α → LengthPercentage

instance : ToLengthPercentage Length := ⟨.length⟩
instance : ToLengthPercentage Percentage := ⟨.percentage⟩
instance : ToLengthPercentage LengthPercentage := ⟨id⟩

instance : Coe Length LengthPercentage := ⟨.length⟩
instance : Coe Percentage LengthPercentage := ⟨.percentage⟩
instance : OfNat LengthPercentage 0 := ⟨.length 0⟩

open ToLengthPercentage in
instance [ToLengthPercentage α] [ToLengthPercentage β] : HAdd α β LengthPercentage :=
  ⟨fun a b => .add (toLengthPercentage a) (toLengthPercentage b)⟩

open ToLengthPercentage in
instance [ToLengthPercentage α] [ToLengthPercentage β] : HSub α β LengthPercentage :=
  ⟨fun a b => .sub (toLengthPercentage a) (toLengthPercentage b)⟩

/-- A type of number that scales a `LengthPercentage`, so that a literal factor can elaborate as
the `Nat` it defaults to. -/
class ToNum (α : Type) where
  toNum : α → Num

instance : ToNum Num := ⟨id⟩
instance : ToNum Nat := ⟨fun n => n⟩
instance : ToNum Int := ⟨fun n => n⟩

open ToLengthPercentage ToNum in
instance [ToLengthPercentage α] [ToNum β] : HMul α β LengthPercentage :=
  ⟨fun a k => .mul (toLengthPercentage a) (toNum k)⟩

open ToLengthPercentage ToNum in
instance [ToLengthPercentage α] [ToNum β] : HDiv α β LengthPercentage :=
  ⟨fun a k => .div (toLengthPercentage a) (toNum k)⟩

/-- Fixes the type arithmetic is elaborated at, which `+`, `-`, `*`, and `/` need where a property
expects something wider, such as `OrAuto LengthPercentage`. -/
def calc_ (x : LengthPercentage) : LengthPercentage := x

/-- `clamp(lo, val, hi)` -/
def clamp (lo val hi : LengthPercentage) : LengthPercentage := .clamp lo val hi

/-! ## Wrappers -/

/-- A value or `auto`. -/
inductive OrAuto (α : Type) where
  | auto
  | val (a : α)
  deriving DecidableEq, Repr

instance : Coe α (OrAuto α) := ⟨.val⟩
instance [OfNat α n] : OfNat (OrAuto α) n := ⟨.val (OfNat.ofNat n)⟩
instance [ToValue α] : ToValue (OrAuto α) := ⟨fun | .auto => [.ident "auto"] | .val a => toValue a⟩

/-- A value or `none`. -/
inductive OrNone (α : Type) where
  | none
  | val (a : α)
  deriving DecidableEq, Repr

instance : Coe α (OrNone α) := ⟨.val⟩
instance [OfNat α n] : OfNat (OrNone α) n := ⟨.val (OfNat.ofNat n)⟩
instance [ToValue α] : ToValue (OrNone α) := ⟨fun | .none => [.ident "none"] | .val a => toValue a⟩

/-- The one to four values of a box shorthand such as `margin`, in CSS's order. -/
inductive Sides (α : Type) where
  | all (a : α)
  | two (vertical horizontal : α)
  | three (top horizontal bottom : α)
  | four (top right bottom left : α)
  deriving DecidableEq, Repr

instance : Coe α (Sides α) := ⟨.all⟩
instance [OfNat α n] : OfNat (Sides α) n := ⟨.all (OfNat.ofNat n)⟩

instance [ToValue α] : ToValue (Sides α) where
  toValue
    | .all a => toValue a
    | .two v h => toValue v ++ toValue h
    | .three t h b => toValue t ++ toValue h ++ toValue b
    | .four t r b l => toValue t ++ toValue r ++ toValue b ++ toValue l

/-! ## Colors -/

css_keywords NamedColor aliased Color
  | aliceblue | antiquewhite | aqua | aquamarine | azure | beige | bisque | black | blanchedalmond
  | blue | blueviolet | brown | burlywood | cadetblue | chartreuse | chocolate | coral
  | cornflowerblue | cornsilk | crimson | cyan | darkblue | darkcyan | darkgoldenrod | darkgray
  | darkgreen | darkgrey | darkkhaki | darkmagenta | darkolivegreen | darkorange | darkorchid
  | darkred | darksalmon | darkseagreen | darkslateblue | darkslategray | darkslategrey
  | darkturquoise | darkviolet | deeppink | deepskyblue | dimgray | dimgrey | dodgerblue
  | firebrick | floralwhite | forestgreen | fuchsia | gainsboro | ghostwhite | gold | goldenrod
  | gray | green | greenyellow | grey | honeydew | hotpink | indianred | indigo | ivory | khaki
  | lavender | lavenderblush | lawngreen | lemonchiffon | lightblue | lightcoral | lightcyan
  | lightgoldenrodyellow | lightgray | lightgreen | lightgrey | lightpink | lightsalmon
  | lightseagreen | lightskyblue | lightslategray | lightslategrey | lightsteelblue | lightyellow
  | lime | limegreen | linen | magenta | maroon | mediumaquamarine | mediumblue | mediumorchid
  | mediumpurple | mediumseagreen | mediumslateblue | mediumspringgreen | mediumturquoise
  | mediumvioletred | midnightblue | mintcream | mistyrose | moccasin | navajowhite | navy
  | oldlace | olive | olivedrab | orange | orangered | orchid | palegoldenrod | palegreen
  | paleturquoise | palevioletred | papayawhip | peachpuff | peru | pink | plum | powderblue
  | purple | rebeccapurple | red | rosybrown | royalblue | saddlebrown | salmon | sandybrown
  | seagreen | seashell | sienna | silver | skyblue | slateblue | slategray | slategrey | snow
  | springgreen | steelblue | tan | teal | thistle | tomato | turquoise | violet | wheat | white
  | whitesmoke | yellow | yellowgreen

/-- A color. The named colors are written as constructors, `.red`, through their aliases in this
namespace. -/
inductive Color where
  | named (c : NamedColor)
  | currentColor
  | transparent
  /-- `#rrggbb` -/
  | hex (rgb : Nat) (h : rgb < 0x1000000 := by decide)
  | rgb (r g b : UInt8) (alpha : Num := 1)
  | hsl (hue : Angle) (saturation lightness : Percentage) (alpha : Num := 1)
  deriving DecidableEq, Repr

instance : Coe NamedColor Color := ⟨.named⟩

def Color.withAlpha (args : Value) (alpha : Num) : Value :=
  if alpha = 1 then args else args ++ [.slash, .number alpha]

instance : ToValue Color where
  toValue
    | .named c => toValue c
    | .currentColor => [.ident "currentcolor"]
    | .transparent => [.ident "transparent"]
    | .hex n _ =>
      let ds := hexDigits n
      [.hash (String.ofList (List.replicate (6 - ds.length) '0' ++ ds))]
    | .rgb r g b a => [.function "rgb" (Color.withAlpha [.number r.toNat, .number g.toNat, .number b.toNat] a)]
    | .hsl h s l a => [.function "hsl" (Color.withAlpha (toValue h ++ toValue s ++ toValue l) a)]

/-! ## Images -/

/-- A color stop of a gradient, at an optional position. -/
structure ColorStop where
  color : Color
  position : Option LengthPercentage := none
  deriving DecidableEq, Repr

def stop (color : Color) (position : Option LengthPercentage := none) : ColorStop :=
  ⟨color, position⟩

instance : ToValue ColorStop := ⟨fun s => toValue s.color ++ (s.position.map toValue).getD []⟩

inductive Image where
  | url (url : String)
  | linearGradient (angle : Angle) (stops : List ColorStop)
  | radialGradient (stops : List ColorStop)
  deriving DecidableEq, Repr

def url (url : String) : Image := .url url

instance : ToValue Image where
  toValue
    | .url u => [.function "url" [.string u]]
    | .linearGradient a stops => [.function "linear-gradient" (toValue a ++ .comma :: commaSeparated stops)]
    | .radialGradient stops => [.function "radial-gradient" (commaSeparated stops)]

/-- Layered images, as in `background-image`, where none at all is `none`. -/
instance : ToValue (List Image) := ⟨fun | [] => [.ident "none"] | is => commaSeparated is⟩

/-! ## Keyword properties -/

css_keywords Display
  | block | inline | inlineBlock | flex | inlineFlex | grid | inlineGrid | flowRoot | none
  | contents | table | tableRow | tableCell | tableCaption | listItem

css_keywords PositionKind | static | relative | absolute | fixed | sticky

css_keywords FlexDirection | row | rowReverse | column | columnReverse

css_keywords FlexWrap | nowrap | wrap | wrapReverse

css_keywords JustifyContent
  | normal | start | «end» | center | flexStart | flexEnd | left | right | spaceBetween
  | spaceAround | spaceEvenly | stretch

css_keywords AlignItems
  | normal | stretch | center | start | «end» | flexStart | flexEnd | selfStart | selfEnd
  | baseline

css_keywords AlignContent
  | normal | start | «end» | center | flexStart | flexEnd | spaceBetween | spaceAround
  | spaceEvenly | stretch | baseline

css_keywords AlignSelf
  | auto | normal | stretch | center | start | «end» | flexStart | flexEnd | selfStart | selfEnd
  | baseline

css_keywords JustifyItems | normal | stretch | center | start | «end» | left | right | baseline

css_keywords JustifySelf
  | auto | normal | stretch | center | start | «end» | left | right | baseline

css_keywords TextAlign | start | «end» | left | right | center | justify

css_keywords FontStyle | normal | italic | oblique

css_keywords TextDecorationLine | none | underline | overline | lineThrough

css_keywords TextTransform | none | capitalize | uppercase | lowercase

css_keywords WhiteSpace | normal | nowrap | pre | preWrap | preLine | breakSpaces

css_keywords WordBreak | normal | breakAll | keepAll

css_keywords OverflowWrap | normal | breakWord | anywhere

css_keywords TextOverflow | clip | ellipsis

css_keywords VerticalAlign | baseline | sub | super | textTop | textBottom | middle | top | bottom

css_keywords Overflow | visible | hidden | clip | scroll | auto

css_keywords Visibility | visible | hidden | collapse

css_keywords BoxSizing | contentBox | borderBox

css_keywords Cursor
  | auto | default | none | contextMenu | help | pointer | progress | wait | cell | crosshair
  | text | verticalText | alias | copy | move | noDrop | notAllowed | grab | grabbing | colResize
  | rowResize | nResize | eResize | sResize | wResize | ewResize | nsResize | zoomIn | zoomOut

css_keywords PointerEvents | auto | none

css_keywords UserSelect | auto | none | text | all

css_keywords ObjectFit | fill | contain | cover | none | scaleDown

css_keywords BorderStyle
  | none | hidden | dotted | dashed | solid | double | groove | ridge | inset | outset

css_keywords ListStyleType
  | none | disc | circle | square | decimal | decimalLeadingZero | lowerRoman | upperRoman
  | lowerAlpha | upperAlpha | lowerGreek

css_keywords FloatKind | none | left | right | inlineStart | inlineEnd

css_keywords Clear | none | left | right | both | inlineStart | inlineEnd

css_keywords BackgroundRepeat | «repeat» | noRepeat | repeatX | repeatY | space | round

css_keywords Resize | none | both | horizontal | vertical | block | inline

css_keywords ScrollBehavior | auto | smooth

css_keywords FontDisplay | auto | block | swap | fallback | optional

/-! ## Mixed values -/

css_keywords LineWidthKeyword aliased LineWidth | thin | medium | thick

inductive LineWidth where
  | keyword (k : LineWidthKeyword)
  | length (l : Length)
  deriving DecidableEq, Repr

instance : Coe LineWidthKeyword LineWidth := ⟨.keyword⟩
instance : Coe Length LineWidth := ⟨.length⟩
instance : OfNat LineWidth 0 := ⟨.length 0⟩
instance : ToValue LineWidth := ⟨fun | .keyword k => toValue k | .length l => toValue l⟩

css_keywords FontSizeKeyword aliased FontSize
  | xxSmall | xSmall | small | medium | large | xLarge | xxLarge | xxxLarge | smaller | larger

inductive FontSize where
  | keyword (k : FontSizeKeyword)
  | size (s : LengthPercentage)
  deriving DecidableEq, Repr

instance : Coe FontSizeKeyword FontSize := ⟨.keyword⟩
instance : Coe LengthPercentage FontSize := ⟨.size⟩
instance : ToValue FontSize := ⟨fun | .keyword k => toValue k | .size s => toValue s⟩

/-- `font-weight`. A numeric literal must be a multiple of 100, as `600`; `.weight` takes any
weight from 1 to 1000. -/
inductive FontWeight where
  | normal
  | bold
  | bolder
  | lighter
  | weight (n : Nat) (h : 1 ≤ n ∧ n ≤ 1000 := by decide)
  deriving DecidableEq, Repr

instance : OfNat FontWeight 100 := ⟨.weight 100⟩
instance : OfNat FontWeight 200 := ⟨.weight 200⟩
instance : OfNat FontWeight 300 := ⟨.weight 300⟩
instance : OfNat FontWeight 400 := ⟨.weight 400⟩
instance : OfNat FontWeight 500 := ⟨.weight 500⟩
instance : OfNat FontWeight 600 := ⟨.weight 600⟩
instance : OfNat FontWeight 700 := ⟨.weight 700⟩
instance : OfNat FontWeight 800 := ⟨.weight 800⟩
instance : OfNat FontWeight 900 := ⟨.weight 900⟩

instance : ToValue FontWeight where
  toValue
    | .normal => [.ident "normal"]
    | .bold => [.ident "bold"]
    | .bolder => [.ident "bolder"]
    | .lighter => [.ident "lighter"]
    | .weight n _ => [.number n]

inductive LineHeight where
  | normal
  | number (n : Num)
  | size (s : LengthPercentage)
  deriving DecidableEq, Repr

instance : OfNat LineHeight n := ⟨.number (OfNat.ofNat n)⟩
instance : OfScientific LineHeight := ⟨fun m s e => .number (OfScientific.ofScientific m s e)⟩
instance : Coe LengthPercentage LineHeight := ⟨.size⟩

instance : ToValue LineHeight where
  toValue
    | .normal => [.ident "normal"]
    | .number n => [.number n]
    | .size s => toValue s

css_keywords GenericFamily aliased FontFamily FontStack
  | serif | sansSerif | monospace | cursive | fantasy | systemUi | uiSerif | uiSansSerif
  | uiMonospace | uiRounded | math | emoji

inductive FontFamily where
  | generic (g : GenericFamily)
  | named (name : String)
  deriving DecidableEq, Repr

instance : Coe GenericFamily FontFamily := ⟨.generic⟩
instance : Coe String FontFamily := ⟨.named⟩
instance : ToValue FontFamily := ⟨fun | .generic g => toValue g | .named n => [.string n]⟩

/-- A font family with its fallbacks, of which `font-family` needs at least one. -/
structure FontStack where
  first : FontFamily
  fallbacks : List FontFamily := []
  deriving DecidableEq, Repr

instance : Coe FontFamily FontStack := ⟨(⟨·, []⟩)⟩
instance : ToValue FontStack := ⟨fun s => commaSeparated (s.first :: s.fallbacks)⟩

inductive BackgroundSize where
  | cover
  | contain
  | size (width : OrAuto LengthPercentage) (height : OrAuto LengthPercentage := .auto)
  deriving DecidableEq, Repr

instance : Coe LengthPercentage BackgroundSize := ⟨(.size · .auto)⟩

instance : ToValue BackgroundSize where
  toValue
    | .cover => [.ident "cover"]
    | .contain => [.ident "contain"]
    | .size w .auto => toValue w
    | .size w h => toValue w ++ toValue h

inductive AspectRatio where
  | auto
  | ratio (width : Num) (height : Num := 1)
  deriving DecidableEq, Repr

instance : OfNat AspectRatio n := ⟨.ratio (OfNat.ofNat n)⟩

instance : ToValue AspectRatio where
  toValue
    | .auto => [.ident "auto"]
    | .ratio w h => [.number w, .slash, .number h]

/-- `content`, for `::before` and `::after`. -/
inductive Content where
  | normal
  | none
  | text (s : String)
  | attr (name : String)
  deriving DecidableEq, Repr

instance : Coe String Content := ⟨.text⟩

instance : ToValue Content where
  toValue
    | .normal => [.ident "normal"]
    | .none => [.ident "none"]
    | .text s => [.string s]
    | .attr n => [.function "attr" [.ident n]]

/-! ## Borders and shadows -/

/-- The `border` shorthand. Omitted parts take their initial values, so are left out. -/
structure Border where
  width : LineWidth := .medium
  style : BorderStyle
  color : Color := .currentColor
  deriving DecidableEq, Repr

instance : ToValue Border where
  toValue b :=
    (if b.width = .medium then [] else toValue b.width) ++ toValue b.style ++
      (if b.color = .currentColor then [] else toValue b.color)

structure Shadow where
  x : Length
  y : Length
  blur : Length := 0
  spread : Length := 0
  color : Color := .currentColor
  inset : Bool := false
  deriving DecidableEq, Repr

instance : ToValue Shadow where
  toValue s :=
    (if s.inset then [.ident "inset"] else []) ++ toValue s.x ++ toValue s.y ++
      (if s.blur = 0 && s.spread = 0 then [] else toValue s.blur) ++
      (if s.spread = 0 then [] else toValue s.spread) ++
      (if s.color = .currentColor then [] else toValue s.color)

/-- Layered shadows, where none at all is `none`. -/
instance : ToValue (List Shadow) := ⟨fun | [] => [.ident "none"] | ss => commaSeparated ss⟩

/-! ## Transforms, transitions, and animations -/

inductive Transform where
  | translate (x : LengthPercentage) (y : LengthPercentage := 0)
  | translateX (x : LengthPercentage)
  | translateY (y : LengthPercentage)
  | scale (x : Num) (y : Option Num := none)
  | rotate (a : Angle)
  | skew (x : Angle) (y : Angle := 0)
  deriving DecidableEq, Repr

instance : ToValue Transform where
  toValue
    | .translate x y => [.function "translate" (toValue x ++ .comma :: toValue y)]
    | .translateX x => [.function "translateX" (toValue x)]
    | .translateY y => [.function "translateY" (toValue y)]
    | .scale x none => [.function "scale" [.number x]]
    | .scale x (some y) => [.function "scale" [.number x, .comma, .number y]]
    | .rotate a => [.function "rotate" (toValue a)]
    | .skew x y => [.function "skew" (toValue x ++ .comma :: toValue y)]

/-- A transform list, where none at all is `none`. -/
instance : ToValue (List Transform) := ⟨fun | [] => [.ident "none"] | ts => ts.flatMap toValue⟩

css_keywords EasingKeyword aliased Easing
  | ease | linear | easeIn | easeOut | easeInOut | stepStart | stepEnd

css_keywords StepPosition | jumpStart | jumpEnd | jumpNone | jumpBoth

inductive Easing where
  | keyword (k : EasingKeyword)
  | cubicBezier (x1 y1 x2 y2 : Num)
  | steps (n : Nat) (position : StepPosition := .jumpEnd)
  deriving DecidableEq, Repr

instance : Coe EasingKeyword Easing := ⟨.keyword⟩

instance : ToValue Easing where
  toValue
    | .keyword k => toValue k
    | .cubicBezier a b c d =>
      [.function "cubic-bezier" [.number a, .comma, .number b, .comma, .number c, .comma, .number d]]
    | .steps n p => [.function "steps" [.number n, .comma, .ident (Keyword.keyword p)]]

structure Transition where
  /-- The property transitioned, or `all`. -/
  property : String := "all"
  duration : Time
  easing : Easing := .ease
  delay : Time := 0
  deriving DecidableEq, Repr

instance : ToValue Transition where
  toValue t :=
    [.ident t.property] ++ toValue t.duration ++
      (if t.easing = .ease && t.delay = 0 then [] else toValue t.easing) ++
      (if t.delay = 0 then [] else toValue t.delay)

/-- Transitions, where none at all is `none`. -/
instance : ToValue (List Transition) := ⟨fun | [] => [.ident "none"] | ts => commaSeparated ts⟩

css_keywords AnimationDirection | normal | reverse | alternate | alternateReverse

css_keywords FillMode | none | forwards | backwards | both

inductive Iterations where
  | infinite
  | count (n : Num)
  deriving DecidableEq, Repr

instance : OfNat Iterations n := ⟨.count (OfNat.ofNat n)⟩
instance : ToValue Iterations := ⟨fun | .infinite => [.ident "infinite"] | .count n => [.number n]⟩

/-- An `@keyframes` rule's name, as `keyframes` returns it, or `.named` for one defined
elsewhere. -/
structure Keyframes where
  named ::
  name : String
  deriving DecidableEq, Repr

/-- One animation of the `animation` shorthand. -/
structure Animation where
  name : Keyframes
  duration : Time
  easing : Easing := .ease
  delay : Time := 0
  iterations : Iterations := 1
  direction : AnimationDirection := .normal
  fillMode : FillMode := .none
  deriving DecidableEq, Repr

instance : ToValue Animation where
  toValue a :=
    toValue a.duration ++ (if a.easing = .ease then [] else toValue a.easing) ++
      (if a.delay = 0 then [] else toValue a.delay) ++
      (if a.iterations = 1 then [] else toValue a.iterations) ++
      (if a.direction = .normal then [] else toValue a.direction) ++
      (if a.fillMode = .none then [] else toValue a.fillMode) ++ [.ident a.name.name]

/-- Animations, where none at all is `none`. -/
instance : ToValue (List Animation) := ⟨fun | [] => [.ident "none"] | as => commaSeparated as⟩

/-! ## Grid -/

/-- One track of a grid template. -/
inductive Track where
  | size (s : LengthPercentage)
  | fr (n : Num)
  | auto
  | minContent
  | maxContent
  | minmax (min max : Track)
  | fitContent (limit : LengthPercentage)
  | «repeat» (count : Nat) (tracks : List Track)
  | autoFill (tracks : List Track)
  | autoFit (tracks : List Track)
  deriving Repr

instance : Coe LengthPercentage Track := ⟨.size⟩

def fr (n : Num) : Track := .fr n

mutual

def Track.toValue : Track → Value
  | .size s => ToValue.toValue s
  | .fr n => [.dimension n "fr"]
  | .auto => [.ident "auto"]
  | .minContent => [.ident "min-content"]
  | .maxContent => [.ident "max-content"]
  | .minmax a b => [.function "minmax" (a.toValue ++ .comma :: b.toValue)]
  | .fitContent l => [.function "fit-content" (ToValue.toValue l)]
  | .repeat n ts => [.function "repeat" (.number n :: .comma :: Track.toValueList ts)]
  | .autoFill ts => [.function "repeat" (.ident "auto-fill" :: .comma :: Track.toValueList ts)]
  | .autoFit ts => [.function "repeat" (.ident "auto-fit" :: .comma :: Track.toValueList ts)]

def Track.toValueList : List Track → Value
  | [] => []
  | t :: ts => t.toValue ++ Track.toValueList ts

end

instance : ToValue Track := ⟨Track.toValue⟩

/-- A track list, where none at all is `none`. -/
instance : ToValue (List Track) := ⟨fun | [] => [.ident "none"] | ts => Track.toValueList ts⟩

inductive GridLine where
  | auto
  | line (n : Int)
  | span (n : Nat)
  deriving DecidableEq, Repr

instance : OfNat GridLine n := ⟨.line n⟩

instance : ToValue GridLine where
  toValue
    | .auto => [.ident "auto"]
    | .line n => [.number n]
    | .span n => [.ident "span", .number n]

/-- `grid-column` or `grid-row`: a start line, and an end line if given. -/
inductive GridPlacement where
  | line (l : GridLine)
  | range (start stop : GridLine)
  deriving DecidableEq, Repr

instance : Coe GridLine GridPlacement := ⟨.line⟩
instance : OfNat GridPlacement n := ⟨.line (.line n)⟩

instance : ToValue GridPlacement where
  toValue
    | .line l => toValue l
    | .range a b => toValue a ++ .slash :: toValue b

end Css
