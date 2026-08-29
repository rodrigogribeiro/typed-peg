# Changelog

## 0.1.0.0 — 2026-08-28

### Added

- Initial release.
- Type-safe PEG parser combinators with compile-time left-recursion detection
  via type families (`PEG.Grammar`).
- FIRST-set and nullability information tracked at the type level (`PEG.Type`,
  `PEG.TyLevel`).
- Indentation-sensitive parsing primitives (`PEG.Indent`).
- Quasi-quoter `pegRules` for writing grammars in a concrete DSL (`PEG.QQ`).
- Simple semantics interpreter (`PEG.Semantics.Simple`).
