#!/bin/bash
# SPDX-FileCopyrightText: 2025 Rhett Creighton
# SPDX-License-Identifier: Apache-2.0

# coverage_ci.sh - Run coverage in CI/CD environment

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

# CI-friendly output
echo "::group::Building with coverage"
"$SCRIPT_DIR/build_coverage.sh"
echo "::endgroup::"

echo "::group::Running tests and generating coverage"
cd "$PROJECT_ROOT/build_coverage"
make coverage-quick
echo "::endgroup::"

echo "::group::Coverage summary"
lcov --summary coverage/coverage.info
echo "::endgroup::"

# Check thresholds (70% for both line and function coverage)
"$SCRIPT_DIR/check_coverage_threshold.sh" 70 70