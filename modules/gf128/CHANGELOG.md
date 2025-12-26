# Changelog

## [0.1.0] - 2025-04-26

### Added
- Reference bitwise multiplication implementation (gf128_mul_base)
- Table-driven multiplication (gf128_mul_table)
- PCLMUL-based carry-less multiplication (gf128_mul_pclmul)
- Inversion and division routines (gf128_inv, gf128_div)
- Unit tests covering all operations and randomized property tests
- Benchmark harness for all multiplication methods
- Continuous integration configuration (GitHub Actions)
- Apache 2.0 LICENSE file
- CONTRIBUTING.md with code style and contribution guidelines
- CHANGELOG.md initial release notes for version 0.1.0

### Changed
- Updated API and documentation (docs/design.md, codex.md)

### Unreleased
- None