# 🔥 Aggressive Cleanup Plan - Round 2

## Current State: Still Too Many Files!
- 51 documents in root directory alone
- Multiple versions of same concepts
- Too many "status" and "summary" files

## 🗑️ Delete These NOW

### Circular Recursion Spam (9 files → 0)
```bash
rm -f CIRCULAR_RECURSION_*.md
```
These all say the same thing in different ways!

### Cleanup Meta-Documents (7 files → 1)
```bash
rm -f CLAUDE_CLEANED.md
rm -f CLAUDE_MD_CLEANUP_CHECKLIST.md
rm -f CLAUDE_MD_CLEANUP_SUMMARY.md
rm -f CLEANUP_STATUS.md
rm -f CLEANUP_SUMMARY_2025.md
rm -f DETECTIVE_FINDINGS_REPORT.md
# Keep only: CLEANUP_COMPLETE_SUMMARY.md
```

### Project Status Confusion (5+ files → 1)
```bash
rm -f PROJECT_STRUCTURE.md  # We have MASTER_PROJECT_STRUCTURE.md
rm -f PROJECT_STATUS_VERIFIED.md
rm -f PROJECT_STATUS_*.md
rm -f STATUS_*.md
```

### SHA3 Duplicates
```bash
rm -f SHA3_DEFAULT_UPDATE.md
rm -f SHA3_ONLY_ARCHITECTURE.md
```

### Timing/Performance Duplicates
```bash
rm -f TIMING_ATTACK_VULNERABILITY_REPORT.md
```

### POS Implementation Status Files
```bash
rm -f POS_IMPLEMENTATION_SUMMARY.md
rm -f POS_WIP_ANALYSIS.md
```

## 📁 Consolidate Documentation

### Move to docs/
- All technical specs → docs/specs/
- All security reports → docs/security/
- All implementation guides → docs/guides/

### Root Should Only Have:
1. README.md
2. LICENSE
3. CHANGELOG.md
4. START_HERE.md
5. CLAUDE.md
6. BUILD_WORKING_CONFIG.sh

## 🎯 Final Structure

```
cmptr/
├── README.md              # Project overview
├── START_HERE.md          # Quick start
├── CLAUDE.md              # AI developer guide
├── LICENSE                # Legal
├── CHANGELOG.md           # Version history
├── BUILD_WORKING_CONFIG.sh # Build script
│
├── docs/                  # ALL other documentation
│   ├── architecture/      # Design docs
│   ├── security/          # Security analysis
│   ├── guides/            # How-to guides
│   └── specs/             # Technical specs
│
├── modules/               # Code modules
├── examples/              # Example code
├── tools/                 # Utilities
└── build/                 # Build output
```

## 🚀 Execute Plan

```bash
# 1. Delete redundant files
./execute_aggressive_cleanup.sh

# 2. Move remaining docs
mkdir -p docs/{architecture,security,guides,specs}
mv *_SPEC.md docs/specs/
mv *_SECURITY*.md docs/security/
# etc...

# 3. Update references
# Fix any broken links in remaining files
```

## 📊 Expected Results

| Location | Before | After | Reduction |
|----------|--------|-------|-----------|
| Root | 51 files | 6 files | 88% |
| Total | ~200 files | ~100 files | 50% |

## 💡 Benefits

1. **Clear root** - Only essentials visible
2. **No duplicates** - One source of truth
3. **Organized docs** - Easy to find info
4. **Less confusion** - Obvious what matters

This will make the project SUPER clear!