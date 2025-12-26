#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2025 Rhett Creighton
# SPDX-License-Identifier: Apache-2.0

"""
Analyze the Gate Computer Truth Bucket System
Extracts truth structure from source files and maps dependencies
"""

import os
import re
import glob
from collections import defaultdict

class TruthAnalyzer:
    def __init__(self, base_path):
        self.base_path = base_path
        self.truths = {}
        self.categories = defaultdict(list)
        self.dependencies = defaultdict(set)
        
    def parse_truth_files(self):
        """Parse all truth verifier source files"""
        src_path = os.path.join(self.base_path, "modules/truth_verifier/src")
        
        for filepath in glob.glob(os.path.join(src_path, "*.c")):
            with open(filepath, 'r') as f:
                content = f.read()
                self._extract_truths(content, os.path.basename(filepath))
    
    def _extract_truths(self, content, filename):
        """Extract truth definitions from C source"""
        # Pattern to find truth registration
        register_pattern = r'\.id\s*=\s*"([^"]+)".*?\.type\s*=\s*(\w+).*?\.statement\s*=\s*"([^"]+)".*?\.category\s*=\s*"([^"]+)"'
        
        for match in re.finditer(register_pattern, content, re.DOTALL):
            truth_id = match.group(1)
            truth_type = match.group(2)
            statement = match.group(3)
            category = match.group(4)
            
            self.truths[truth_id] = {
                'type': truth_type,
                'statement': statement,
                'category': category,
                'file': filename
            }
            
            self.categories[category].append(truth_id)
            
        # Extract dependencies from verification functions
        self._extract_dependencies(content)
    
    def _extract_dependencies(self, content):
        """Extract truth dependencies from verification logic"""
        # Look for patterns like verify_by_id("T004")
        dep_pattern = r'truth_verifier_verify_by_id\("([^"]+)"'
        
        # Find the current function context
        func_pattern = r'truth_result_t\s+verify_(\w+)\s*\([^)]+\)\s*\{([^}]+)\}'
        
        for func_match in re.finditer(func_pattern, content, re.DOTALL):
            func_name = func_match.group(1)
            func_body = func_match.group(2)
            
            # Extract truth ID from function name
            id_match = re.search(r'([TADFUP]\d+|[A-Z]+\d*)', func_name)
            if id_match:
                current_id = id_match.group(1)
                
                # Find dependencies in function body
                for dep_match in re.finditer(dep_pattern, func_body):
                    dep_id = dep_match.group(1)
                    self.dependencies[current_id].add(dep_id)
    
    def analyze_axioms(self):
        """Identify and analyze fundamental axioms"""
        axioms = {}
        
        # A-series are axioms
        for truth_id, info in self.truths.items():
            if truth_id.startswith('A') and info['type'] == 'BUCKET_PHILOSOPHICAL':
                axioms[truth_id] = info
                
        # Special axioms from documentation
        if 'A001' not in axioms:
            axioms['A001'] = {
                'type': 'BUCKET_PHILOSOPHICAL',
                'statement': 'Only SHA3 is allowed for hashing',
                'category': 'axiom'
            }
        
        if 'A002' not in axioms:
            axioms['A002'] = {
                'type': 'BUCKET_PHILOSOPHICAL', 
                'statement': 'All proofs MUST be zero-knowledge',
                'category': 'axiom'
            }
            
        return axioms
    
    def find_key_truths(self):
        """Identify key truths based on importance"""
        key_truths = []
        
        # Security critical truths
        security_truths = ['T004', 'T005', 'T201', 'T202', 'T203', 'T204', 'T205', 'T206']
        
        # System level truths
        system_truths = ['T800', 'T801', 'T802', 'T803', 'T804']
        
        # Master truths
        master_truths = [tid for tid in self.truths if 'MASTER' in tid]
        
        key_truths.extend(security_truths)
        key_truths.extend(system_truths)
        key_truths.extend(master_truths)
        
        return list(set(key_truths))
    
    def generate_report(self):
        """Generate comprehensive truth analysis report"""
        print("=== GATE COMPUTER TRUTH BUCKET ANALYSIS ===\n")
        
        # Summary statistics
        print(f"Total truths registered: {len(self.truths)}")
        print(f"Categories: {len(self.categories)}")
        print(f"Truth types:")
        
        type_counts = defaultdict(int)
        for info in self.truths.values():
            type_counts[info['type']] += 1
            
        for truth_type, count in sorted(type_counts.items()):
            print(f"  {truth_type}: {count}")
        
        print("\n" + "="*60 + "\n")
        
        # Axioms
        axioms = self.analyze_axioms()
        print("FUNDAMENTAL AXIOMS:")
        for axiom_id, info in sorted(axioms.items()):
            print(f"  {axiom_id}: {info['statement']}")
        
        print("\n" + "="*60 + "\n")
        
        # Key truths
        key_truths = self.find_key_truths()
        print("KEY TRUTHS:")
        for truth_id in sorted(key_truths):
            if truth_id in self.truths:
                info = self.truths[truth_id]
                print(f"\n{truth_id}: {info['statement']}")
                print(f"  Category: {info['category']}")
                print(f"  Type: {info['type']}")
                if truth_id in self.dependencies:
                    print(f"  Dependencies: {', '.join(sorted(self.dependencies[truth_id]))}")
        
        print("\n" + "="*60 + "\n")
        
        # Categories
        print("TRUTH CATEGORIES:")
        for category, truth_ids in sorted(self.categories.items()):
            print(f"\n{category}: ({len(truth_ids)} truths)")
            for tid in sorted(truth_ids)[:5]:  # Show first 5
                if tid in self.truths:
                    print(f"  {tid}: {self.truths[tid]['statement'][:60]}...")
            if len(truth_ids) > 5:
                print(f"  ... and {len(truth_ids) - 5} more")
        
        print("\n" + "="*60 + "\n")
        
        # Dependency chains
        print("DEPENDENCY CHAINS TO AXIOMS:")
        for truth_id in ['T004', 'T201', 'T504', 'T804']:
            if truth_id in self.truths:
                print(f"\n{truth_id} dependency chain:")
                self._print_dependency_chain(truth_id, indent=0)
    
    def _print_dependency_chain(self, truth_id, indent=0, visited=None):
        """Print dependency chain for a truth"""
        if visited is None:
            visited = set()
            
        if truth_id in visited:
            print("  " * indent + f"[{truth_id}] (circular)")
            return
            
        visited.add(truth_id)
        
        if truth_id in self.truths:
            info = self.truths[truth_id]
            print("  " * indent + f"[{truth_id}] {info['statement'][:50]}...")
            
            if truth_id in self.dependencies:
                for dep in sorted(self.dependencies[truth_id]):
                    self._print_dependency_chain(dep, indent + 1, visited.copy())

def main():
    # Find project root
    script_dir = os.path.dirname(os.path.abspath(__file__))
    project_root = os.path.abspath(os.path.join(script_dir, "../../.."))
    
    analyzer = TruthAnalyzer(project_root)
    
    print("Parsing truth files...")
    analyzer.parse_truth_files()
    
    print(f"Found {len(analyzer.truths)} truths\n")
    
    analyzer.generate_report()
    
    # Export data
    import json
    export_data = {
        'truths': analyzer.truths,
        'categories': dict(analyzer.categories),
        'dependencies': {k: list(v) for k, v in analyzer.dependencies.items()},
        'axioms': analyzer.analyze_axioms(),
        'key_truths': analyzer.find_key_truths()
    }
    
    with open('truth_analysis.json', 'w') as f:
        json.dump(export_data, f, indent=2)
    
    print("\nExported detailed analysis to truth_analysis.json")

if __name__ == "__main__":
    main()