# Changelog

## [Unreleased]

* Breaking: `cls` is renamed `class_`, matching lean-html
* Breaking: `hasUnsafe` is renamed `hasVerbatim` throughout, matching lean-html
* Breaking: `Rule.listHasUnsafe` and `Track.listToValue` are renamed `Rule.hasVerbatimList` and `Track.toValueList`
* Breaking: `custom`, `Css.var`, and `Property.var`'s string name give way to a typed `CustomProp α` handle
* Breaking: `keyframes` and `layer` return handles, which `animation` and `Rule.layerOrder` take in place of names
* `class_`, `id_`, and `attr` accept any `ClassName`, `IdName`, or `AttrName` instance
* `Stylesheet.classNames`, `ids`, and `attrNames` list the names the selectors use

## [0.1.0] - 2026-11-01

Initial release.
