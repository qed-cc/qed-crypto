#!/usr/bin/env python3
"""
Visualize the confidence boost paths for truths using ASCII art
"""

def draw_confidence_path(truth_id, statement, base_conf, wip_truths):
    """Draw ASCII visualization of confidence boost path"""
    print(f"\n{'='*80}")
    print(f"{truth_id}: {statement}")
    print(f"{'='*80}")
    
    # Draw confidence scale
    print("\nConfidence Scale:")
    print("0%    25%    50%    75%    90% 95% 99% 100%")
    print("|-----|-----|-----|-----|----|---|---|---|")
    
    # Draw current position
    pos = int(base_conf * 0.42)  # Scale to fit 42 char display
    print(" " * pos + "▲")
    print(" " * pos + f"|-- Current: {base_conf}%")
    
    # Draw WIP truth contributions
    cumulative = base_conf
    for wip in wip_truths:
        cumulative += wip['boost']
        new_pos = int(cumulative * 0.42)
        if wip.get('verified', False):
            print(" " * new_pos + f"✓ {wip['id']} (+{wip['boost']}%)")
        else:
            print(" " * new_pos + f"○ {wip['id']} (+{wip['boost']}%)")
    
    # Draw target
    target_pos = int(99 * 0.42)
    print(" " * target_pos + "▼")
    print(" " * target_pos + "|-- Target: 99%")
    
    # Summary
    verified_boost = sum(w['boost'] for w in wip_truths if w.get('verified', False))
    potential_boost = sum(w['boost'] for w in wip_truths if not w.get('verified', False))
    
    print(f"\nProgress:")
    print(f"  Base confidence:     {base_conf}%")
    print(f"  Verified boosts:    +{verified_boost}%")
    print(f"  Current total:       {base_conf + verified_boost}%")
    print(f"  Potential boosts:   +{potential_boost}%")
    print(f"  Potential total:     {base_conf + verified_boost + potential_boost}%")
    
    if base_conf + verified_boost + potential_boost >= 99:
        print(f"  Status:              ✓ Path to 99% identified!")
    else:
        print(f"  Status:              ✗ Need more WIP truths")

def main():
    print("CONFIDENCE BOOST PATH VISUALIZATION")
    print("Shows how WIP truths boost confidence to 99%")
    
    # Example 1: T001 with partial progress
    t001_wips = [
        {'id': 'T001A', 'boost': 1.0, 'verified': False},
        {'id': 'T001B', 'boost': 1.0, 'verified': True},  # ✓ Verified!
        {'id': 'T001C', 'boost': 2.0, 'verified': False},
    ]
    draw_confidence_path("T001", "Zero-knowledge proof system", 95.0, t001_wips)
    
    # Example 2: T006 very close to target
    t006_wips = [
        {'id': 'T006_Y', 'boost': 0.1, 'verified': False},
    ]
    draw_confidence_path("T006", "SHA3-only hashing", 98.9, t006_wips)
    
    # Example 3: T004 with multiple small boosts needed
    t004_wips = [
        {'id': 'T004A', 'boost': 0.5, 'verified': False},
        {'id': 'T004B', 'boost': 0.5, 'verified': False},
        {'id': 'T004C', 'boost': 0.5, 'verified': False},
    ]
    draw_confidence_path("T004", "122-bit security level", 97.5, t004_wips)
    
    # Show overall system status
    print("\n" + "="*80)
    print("SYSTEM-WIDE CONFIDENCE STATUS")
    print("="*80)
    
    total_truths = 77
    at_99_percent = 3
    near_pass = 3
    have_wip_paths = 6
    need_wip_generation = total_truths - at_99_percent - have_wip_paths
    
    print(f"\nTotal truths in system: {total_truths}")
    print(f"├─ Already at 99%+: {at_99_percent} ({at_99_percent/total_truths*100:.1f}%)")
    print(f"├─ Near-pass (98-99%): {near_pass} ({near_pass/total_truths*100:.1f}%)")
    print(f"├─ Have WIP paths: {have_wip_paths} ({have_wip_paths/total_truths*100:.1f}%)")
    print(f"└─ Need WIP generation: {need_wip_generation} ({need_wip_generation/total_truths*100:.1f}%)")
    
    print("\nConfidence Distribution:")
    print("  99%+ ████ (4%)")
    print("  98%  ████ (4%)")  
    print("  95%  ████████ (8%)")
    print("  90%  ████████████ (12%)")
    print("  <90% ████████████████████████████████████████████████████████████ (72%)")
    
    print("\nKey Insight: Most truths need significant work to reach 99% confidence.")
    print("Focus on near-pass truths (98%+) for quick wins!")

if __name__ == "__main__":
    main()