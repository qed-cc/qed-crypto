/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

# Truth List View Default Update

## Summary

Updated the truth challenge game to default to the list view instead of the interactive game view, as per user preference.

## Changes Made

### 1. Added New Truth T311
- File: `modules/truth_verifier/src/implementation_truths.c`
- Added truth T311: "Truth challenge list view is the default UI"
- Added verification function `verify_T311_list_view_default()`
- Status: VERIFIED ✓

### 2. Updated Truth Challenge Launcher
- File: `apps/truth_challenge_game/truth_challenge_launcher.c`
- Changed default from game view to list view
- Added command-line options:
  - `--help` / `-h`: Show usage
  - `--game` / `-g`: Launch interactive game view
  - `--list` / `-l`: Launch list view (default)
- Updated messages to reflect the current view type

### 3. Updated Documentation
- File: `CLAUDE.md`
- Added section explaining the two UI modes
- Documented that list view is now the default
- Provided usage examples for both modes

## Usage

```bash
# Default: opens list view
./truth_challenge_launcher

# For interactive game view
./truth_challenge_launcher --game

# For list view explicitly  
./truth_challenge_launcher --list
```

## Verification

The new truth T311 is verified by the truth verifier:
```bash
./build/bin/verify_truths --id T311
# Output: Truth T311: VERIFIED
# Details: Launcher defaults to list view
```

## Benefits

1. **Better Overview**: List view provides a comprehensive view of all truths
2. **Search & Filter**: Easy to find specific truths
3. **Batch Management**: Can quickly review and manage multiple truths
4. **Still Accessible**: Game view remains available with --game flag