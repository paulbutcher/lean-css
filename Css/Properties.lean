/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Css.Types

@[expose] public section

namespace Css

structure Declaration where
  property : String
  value : Value
  isImportant : Bool := false
  deriving Repr

namespace Declaration

def important (d : Declaration) : Declaration := { d with isImportant := true }

def hasUnsafe (d : Declaration) : Bool := d.value.hasUnsafe

def render (d : Declaration) (pretty : Bool := false) : String :=
  escapeIdent d.property ++ (if pretty then ": " else ":") ++ d.value.render ++
    (if d.isImportant then (if pretty then " !important" else "!important") else "")

end Declaration

/-- Declarations as an inline `style` attribute's value. -/
def inlineStyle (ds : List Declaration) : String :=
  ";".intercalate (ds.map (·.render))

/-- A property whose value has type `α`. Applying it to a value gives a declaration, so
`color .red` is one. -/
structure Property (α : Type) where
  name : String

instance [ToValue α] : CoeFun (Property α) (fun _ => α → Declaration) :=
  ⟨fun p v => { property := p.name, value := toValue v }⟩

namespace Property

/-- A CSS-wide keyword, valid for every property. -/
def global (p : Property α) (g : Global) : Declaration := { property := p.name, value := toValue g }

def inherit (p : Property α) : Declaration := p.global .inherit
def initial (p : Property α) : Declaration := p.global .initial
def unset (p : Property α) : Declaration := p.global .unset
def revert (p : Property α) : Declaration := p.global .revert
def revertLayer (p : Property α) : Declaration := p.global .revertLayer

/-- The value of custom property `--name`, as `var(--name)`, falling back to `fallback` where
that is unset. -/
def var [ToValue α] (p : Property α) (name : String) (fallback : Option α := none) : Declaration :=
  { property := p.name, value := [Css.var name ((fallback.map toValue).getD [])] }

end Property

/-- `--name: value` -/
def custom [ToValue α] (name : String) (value : α) : Declaration :=
  { property := "--" ++ name, value := toValue value }

/-- A declaration of a property with no typed counterpart here. Its name and value are escaped
like any other, so this is as safe as a typed declaration, but not checked. -/
def declare [ToValue α] (property : String) (value : α) : Declaration :=
  { property, value := toValue value }

/-! ## Color and background -/

def color : Property Color := ⟨"color"⟩
def opacity : Property Num := ⟨"opacity"⟩
def backgroundColor : Property Color := ⟨"background-color"⟩
def backgroundImage : Property (List Image) := ⟨"background-image"⟩
def backgroundRepeat : Property BackgroundRepeat := ⟨"background-repeat"⟩
def backgroundSize : Property BackgroundSize := ⟨"background-size"⟩

/-! ## Box model -/

def display : Property Display := ⟨"display"⟩
def boxSizing : Property BoxSizing := ⟨"box-sizing"⟩
def width : Property (OrAuto LengthPercentage) := ⟨"width"⟩
def height : Property (OrAuto LengthPercentage) := ⟨"height"⟩
def minWidth : Property (OrAuto LengthPercentage) := ⟨"min-width"⟩
def minHeight : Property (OrAuto LengthPercentage) := ⟨"min-height"⟩
def maxWidth : Property (OrNone LengthPercentage) := ⟨"max-width"⟩
def maxHeight : Property (OrNone LengthPercentage) := ⟨"max-height"⟩
def aspectRatio : Property AspectRatio := ⟨"aspect-ratio"⟩
def margin : Property (Sides (OrAuto LengthPercentage)) := ⟨"margin"⟩
def marginTop : Property (OrAuto LengthPercentage) := ⟨"margin-top"⟩
def marginRight : Property (OrAuto LengthPercentage) := ⟨"margin-right"⟩
def marginBottom : Property (OrAuto LengthPercentage) := ⟨"margin-bottom"⟩
def marginLeft : Property (OrAuto LengthPercentage) := ⟨"margin-left"⟩
def marginInline : Property (OrAuto LengthPercentage) := ⟨"margin-inline"⟩
def marginBlock : Property (OrAuto LengthPercentage) := ⟨"margin-block"⟩
def padding : Property (Sides LengthPercentage) := ⟨"padding"⟩
def paddingTop : Property LengthPercentage := ⟨"padding-top"⟩
def paddingRight : Property LengthPercentage := ⟨"padding-right"⟩
def paddingBottom : Property LengthPercentage := ⟨"padding-bottom"⟩
def paddingLeft : Property LengthPercentage := ⟨"padding-left"⟩
def paddingInline : Property LengthPercentage := ⟨"padding-inline"⟩
def paddingBlock : Property LengthPercentage := ⟨"padding-block"⟩
def overflow : Property Overflow := ⟨"overflow"⟩
def overflowX : Property Overflow := ⟨"overflow-x"⟩
def overflowY : Property Overflow := ⟨"overflow-y"⟩
def visibility : Property Visibility := ⟨"visibility"⟩

/-! ## Borders -/

def border : Property Border := ⟨"border"⟩
def borderTop : Property Border := ⟨"border-top"⟩
def borderRight : Property Border := ⟨"border-right"⟩
def borderBottom : Property Border := ⟨"border-bottom"⟩
def borderLeft : Property Border := ⟨"border-left"⟩
def borderWidth : Property (Sides LineWidth) := ⟨"border-width"⟩
def borderStyle : Property (Sides BorderStyle) := ⟨"border-style"⟩
def borderColor : Property (Sides Color) := ⟨"border-color"⟩
def borderRadius : Property (Sides LengthPercentage) := ⟨"border-radius"⟩
def outline : Property Border := ⟨"outline"⟩
def outlineOffset : Property Length := ⟨"outline-offset"⟩
def boxShadow : Property (List Shadow) := ⟨"box-shadow"⟩

/-! ## Positioning -/

def position : Property PositionKind := ⟨"position"⟩
def top : Property (OrAuto LengthPercentage) := ⟨"top"⟩
def right : Property (OrAuto LengthPercentage) := ⟨"right"⟩
def bottom : Property (OrAuto LengthPercentage) := ⟨"bottom"⟩
def left : Property (OrAuto LengthPercentage) := ⟨"left"⟩
def inset : Property (Sides (OrAuto LengthPercentage)) := ⟨"inset"⟩
def zIndex : Property (OrAuto Int) := ⟨"z-index"⟩
def float : Property FloatKind := ⟨"float"⟩
def clear : Property Clear := ⟨"clear"⟩

/-! ## Flexbox and grid -/

def flexDirection : Property FlexDirection := ⟨"flex-direction"⟩
def flexWrap : Property FlexWrap := ⟨"flex-wrap"⟩
def flexGrow : Property Num := ⟨"flex-grow"⟩
def flexShrink : Property Num := ⟨"flex-shrink"⟩
def flexBasis : Property (OrAuto LengthPercentage) := ⟨"flex-basis"⟩
def order : Property Int := ⟨"order"⟩
def justifyContent : Property JustifyContent := ⟨"justify-content"⟩
def justifyItems : Property JustifyItems := ⟨"justify-items"⟩
def justifySelf : Property JustifySelf := ⟨"justify-self"⟩
def alignItems : Property AlignItems := ⟨"align-items"⟩
def alignContent : Property AlignContent := ⟨"align-content"⟩
def alignSelf : Property AlignSelf := ⟨"align-self"⟩
def gap : Property LengthPercentage := ⟨"gap"⟩
def rowGap : Property LengthPercentage := ⟨"row-gap"⟩
def columnGap : Property LengthPercentage := ⟨"column-gap"⟩
def gridTemplateColumns : Property (List Track) := ⟨"grid-template-columns"⟩
def gridTemplateRows : Property (List Track) := ⟨"grid-template-rows"⟩
def gridColumn : Property GridPlacement := ⟨"grid-column"⟩
def gridRow : Property GridPlacement := ⟨"grid-row"⟩

/-! ## Text -/

def fontFamily : Property FontStack := ⟨"font-family"⟩
def fontSize : Property FontSize := ⟨"font-size"⟩
def fontWeight : Property FontWeight := ⟨"font-weight"⟩
def fontStyle : Property FontStyle := ⟨"font-style"⟩
def lineHeight : Property LineHeight := ⟨"line-height"⟩
def letterSpacing : Property Length := ⟨"letter-spacing"⟩
def textAlign : Property TextAlign := ⟨"text-align"⟩
def textDecoration : Property TextDecorationLine := ⟨"text-decoration"⟩
def textTransform : Property TextTransform := ⟨"text-transform"⟩
def textOverflow : Property TextOverflow := ⟨"text-overflow"⟩
def whiteSpace : Property WhiteSpace := ⟨"white-space"⟩
def wordBreak : Property WordBreak := ⟨"word-break"⟩
def overflowWrap : Property OverflowWrap := ⟨"overflow-wrap"⟩
def verticalAlign : Property VerticalAlign := ⟨"vertical-align"⟩
def listStyleType : Property ListStyleType := ⟨"list-style-type"⟩
def content : Property Content := ⟨"content"⟩

/-! ## Interaction and media -/

def cursor : Property Cursor := ⟨"cursor"⟩
def pointerEvents : Property PointerEvents := ⟨"pointer-events"⟩
def userSelect : Property UserSelect := ⟨"user-select"⟩
def resize : Property Resize := ⟨"resize"⟩
def scrollBehavior : Property ScrollBehavior := ⟨"scroll-behavior"⟩
def objectFit : Property ObjectFit := ⟨"object-fit"⟩

/-! ## Transforms and animation -/

def transform : Property (List Transform) := ⟨"transform"⟩
def transition : Property (List Transition) := ⟨"transition"⟩
def animation : Property (List Animation) := ⟨"animation"⟩

/-! ## `@font-face` descriptors -/

structure FontSource where
  url : String
  format : Option String := none
  deriving DecidableEq, Repr

instance : ToValue FontSource where
  toValue f :=
    .function "url" [.string f.url] :: (f.format.map fun s => [.function "format" [.string s]]).getD []

def src : Property (List FontSource) := ⟨"src"⟩
def fontDisplay : Property FontDisplay := ⟨"font-display"⟩

instance : ToValue (List FontSource) := ⟨commaSeparated⟩

end Css
