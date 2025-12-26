# Contributing to GF128 Library

Thank you for your interest in improving the GF128 finite-field library! By contributing, you agree to abide by the guidelines below.

## Code Style
- Language: C (C99 standard)
- Indentation: 4 spaces (no tabs)
- Brace style: K&R (opening brace on same line)
- Naming: use `gf128_` prefix for public API; static/internal functions may use `_` as needed
- Run formatting checks with `clang-format -i` or `make format` if available

## Git Workflow
1. Fork the repository and create a topic branch named `feature/your-change` or `fix/issue-number`.
2. Commit logically grouped changes with clear messages:
   - Use present tense, short summary (<50 characters).
   - Provide detailed description if needed in the body.
   - Reference issues with `Fixes #<issue>` when applicable.
3. Rebase on the latest `main` branch before opening a Pull Request.
4. Submit a Pull Request against the `main` branch and describe your changes.

## Testing & CI
- Ensure all unit tests pass: build with CMake and run `ctest`.
- Include new tests for any added feature or edge case.
- Benchmarks: update or add performance tests in `benchmarks/` if relevant.
- CI (GitHub Actions) will automatically run tests and lint checks on each PR.

## Documentation
- Update or add documentation in `docs/design.md` for new algorithms or API changes.
- Examples: modify `examples/example.c` to illustrate new features.
- Update `docs/roadmap.md` and `CHANGELOG.md` with user-facing notes.
- Update `codex.md` with updated AI-context instructions for future LLM-based development.

## License
By contributing, you agree that your contributions will be licensed under the Apache License 2.0.