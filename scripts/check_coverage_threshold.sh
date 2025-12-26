#!/bin/bash
# SPDX-FileCopyrightText: 2025 Rhett Creighton
# SPDX-License-Identifier: Apache-2.0

# check_coverage_threshold.sh - Enforce minimum code coverage thresholds

set -e

# Default thresholds (can be overridden by command line args)
LINE_THRESHOLD=${1:-70}
FUNC_THRESHOLD=${2:-70}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
BUILD_DIR="$PROJECT_ROOT/build_coverage"
COVERAGE_INFO="$BUILD_DIR/coverage/coverage_cleaned.info"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
NC='\033[0m'

echo "==== Checking Code Coverage Thresholds ===="
echo "Line coverage threshold: ${LINE_THRESHOLD}%"
echo "Function coverage threshold: ${FUNC_THRESHOLD}%"

# Check if coverage info exists
if [ ! -f "$COVERAGE_INFO" ]; then
    echo -e "${RED}ERROR: Coverage info not found!${NC}"
    echo "Please run coverage analysis first:"
    echo "  $SCRIPT_DIR/generate_coverage_report.sh"
    exit 1
fi

# Extract coverage percentages
LINE_COV=$(lcov --summary "$COVERAGE_INFO" 2>&1 | grep "lines......" | sed 's/.*: \([0-9.]*\)%.*/\1/')
FUNC_COV=$(lcov --summary "$COVERAGE_INFO" 2>&1 | grep "functions.." | sed 's/.*: \([0-9.]*\)%.*/\1/')

echo ""
echo "Current coverage:"
echo "  Line coverage: ${LINE_COV}%"
echo "  Function coverage: ${FUNC_COV}%"

# Check thresholds
FAILED=0

if (( $(echo "$LINE_COV < $LINE_THRESHOLD" | bc -l) )); then
    echo -e "${RED}FAIL: Line coverage ${LINE_COV}% is below threshold ${LINE_THRESHOLD}%${NC}"
    FAILED=1
else
    echo -e "${GREEN}PASS: Line coverage ${LINE_COV}% meets threshold${NC}"
fi

if (( $(echo "$FUNC_COV < $FUNC_THRESHOLD" | bc -l) )); then
    echo -e "${RED}FAIL: Function coverage ${FUNC_COV}% is below threshold ${FUNC_THRESHOLD}%${NC}"
    FAILED=1
else
    echo -e "${GREEN}PASS: Function coverage ${FUNC_COV}% meets threshold${NC}"
fi

# Show files with lowest coverage
if [ $FAILED -eq 1 ]; then
    echo ""
    echo "Files needing attention (lowest coverage):"
    lcov --list "$COVERAGE_INFO" | sort -k2 -n | head -10 | awk '$1 != "Total:" {print "  " $1 " - " $2 "%"}'
fi

exit $FAILED