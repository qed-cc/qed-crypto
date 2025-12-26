# Code Coverage Guide for Gate Computer

This guide explains how to measure code coverage for Gate Computer, helping to convert F810 from FALSE to TRUE.

## Quick Start

```bash
# Build with coverage enabled
./scripts/build_coverage.sh

# Generate coverage report
./scripts/generate_coverage_report.sh

# View report in browser
xdg-open build_coverage/coverage/html/index.html
```

## Prerequisites

Install coverage tools for your platform:

### Ubuntu/Debian
```bash
sudo apt-get install lcov gcov
```

### openSUSE
```bash
sudo zypper install lcov gcc
```

### macOS
```bash
brew install lcov
```

## Build Types

### Coverage Build Type
A special build type optimized for coverage measurement:
- Disables optimizations (`-O0`)
- Enables coverage flags (`--coverage`)
- Includes debug symbols (`-g`)
- Enables all tests

```bash
cmake .. -DCMAKE_BUILD_TYPE=Coverage
```

### Enabling Coverage in Other Builds
```bash
cmake .. -DENABLE_COVERAGE=ON
```

## CMake Targets

### coverage
Runs all tests and generates full HTML coverage report:
```bash
make coverage
```

### coverage-quick
Runs tests and shows summary without HTML generation:
```bash
make coverage-quick
```

### coverage-reset
Resets coverage counters to zero:
```bash
make coverage-reset
```

### coverage-view
Opens the HTML report in your browser:
```bash
make coverage-view
```

## Scripts

### build_coverage.sh
Builds Gate Computer with coverage enabled:
```bash
./scripts/build_coverage.sh
```

### generate_coverage_report.sh
Generates detailed coverage report with statistics:
```bash
./scripts/generate_coverage_report.sh
```

### check_coverage_threshold.sh
Enforces minimum coverage thresholds (default 70%):
```bash
./scripts/check_coverage_threshold.sh [line_threshold] [func_threshold]
```

### coverage_ci.sh
Runs coverage in CI/CD environments:
```bash
./scripts/coverage_ci.sh
```

## Coverage Reports

### HTML Report
Located at: `build_coverage/coverage/html/index.html`
- Interactive file browser
- Line-by-line coverage visualization
- Function coverage statistics
- Branch coverage information

### Summary Statistics
- **Line Coverage**: Percentage of code lines executed
- **Function Coverage**: Percentage of functions called
- **Branch Coverage**: Percentage of branches taken

### Coverage Files
- `coverage.info`: Raw coverage data
- `coverage_cleaned.info`: Filtered coverage (excludes system headers)
- `*.gcda`: Runtime coverage data files
- `*.gcno`: Compile-time coverage metadata

## Best Practices

### 1. Regular Coverage Checks
Run coverage before commits:
```bash
./scripts/generate_coverage_report.sh
./scripts/check_coverage_threshold.sh
```

### 2. Focus on Critical Code
Prioritize coverage for:
- Core algorithms (basefold, gf128)
- Security-critical code
- Public APIs
- Error handling paths

### 3. Exclude Test Code
Coverage already excludes:
- `/usr/*` (system headers)
- `*/vendor/*` (third-party code)
- `*/build/*` (generated files)
- `*/tests/*` (test code itself)

### 4. Target Coverage Goals
- **70%** minimum for production code
- **80%** for critical modules
- **90%** for security components

## Integration with CI/CD

### GitHub Actions Example
```yaml
- name: Build with Coverage
  run: ./scripts/build_coverage.sh

- name: Run Coverage Analysis
  run: ./scripts/coverage_ci.sh

- name: Upload Coverage Report
  uses: actions/upload-artifact@v3
  with:
    name: coverage-report
    path: build_coverage/coverage/html/
```

### GitLab CI Example
```yaml
coverage:
  script:
    - ./scripts/coverage_ci.sh
  artifacts:
    paths:
      - build_coverage/coverage/html/
    reports:
      coverage_report:
        coverage_format: cobertura
        path: build_coverage/coverage/coverage.xml
```

## Troubleshooting

### Missing lcov
```
ERROR: lcov is not installed
```
Install lcov for your platform (see Prerequisites).

### No coverage data
```
No coverage data found
```
Ensure tests are actually running and code is being executed.

### Low coverage in module
Check if module has sufficient tests:
```bash
ls modules/*/tests/
```

## Converting F810 to TRUE

With this coverage infrastructure in place, F810 ("Code coverage is measured") can now be converted from FALSE to TRUE:

1. **Coverage tools integrated** ✓
2. **CMake support added** ✓
3. **Scripts for automation** ✓
4. **HTML reports generated** ✓
5. **Threshold enforcement** ✓
6. **CI/CD ready** ✓

Now Gate Computer has comprehensive code coverage measurement!