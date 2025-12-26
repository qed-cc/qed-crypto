#!/bin/bash
# SPDX-FileCopyrightText: 2025 Rhett Creighton
# SPDX-License-Identifier: Apache-2.0

# generate_coverage_report.sh - Generate detailed code coverage report

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
BUILD_DIR="$PROJECT_ROOT/build_coverage"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

echo "==== Gate Computer Code Coverage Report Generator ===="

# Check if coverage build exists
if [ ! -d "$BUILD_DIR" ]; then
    echo -e "${RED}ERROR: Coverage build not found!${NC}"
    echo "Please run: $SCRIPT_DIR/build_coverage.sh first"
    exit 1
fi

cd "$BUILD_DIR"

# Reset coverage counters
echo "Resetting coverage counters..."
make coverage-reset

# Run all tests
echo "Running all tests..."
make test ARGS="--output-on-failure" || true

# Generate coverage report
echo "Generating coverage report..."
make coverage

# Extract summary statistics
echo ""
echo "==== Coverage Summary ===="

# Parse the lcov summary output
COVERAGE_INFO="$BUILD_DIR/coverage/coverage_cleaned.info"
if [ -f "$COVERAGE_INFO" ]; then
    # Get line coverage
    LINE_COV=$(lcov --summary "$COVERAGE_INFO" 2>&1 | grep "lines......" | sed 's/.*: \([0-9.]*\)%.*/\1/')
    FUNC_COV=$(lcov --summary "$COVERAGE_INFO" 2>&1 | grep "functions.." | sed 's/.*: \([0-9.]*\)%.*/\1/')
    
    # Color-code the output
    if (( $(echo "$LINE_COV > 80" | bc -l) )); then
        LINE_COLOR=$GREEN
    elif (( $(echo "$LINE_COV > 60" | bc -l) )); then
        LINE_COLOR=$YELLOW
    else
        LINE_COLOR=$RED
    fi
    
    echo -e "Line Coverage: ${LINE_COLOR}${LINE_COV}%${NC}"
    echo -e "Function Coverage: ${LINE_COLOR}${FUNC_COV}%${NC}"
    
    # List files with low coverage
    echo ""
    echo "Files with coverage < 50%:"
    lcov --list "$COVERAGE_INFO" | awk '$2 < 50 && $1 != "Total:" {print "  " $1 " - " $2 "%"}'
fi

echo ""
echo "==== Report Location ===="
echo "HTML Report: file://$BUILD_DIR/coverage/html/index.html"
echo ""
echo "To view in browser, run:"
echo "  xdg-open $BUILD_DIR/coverage/html/index.html"