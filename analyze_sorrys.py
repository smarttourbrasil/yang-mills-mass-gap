#!/usr/bin/env python3
"""Analyze all sorry statements in the Yang-Mills repository."""

import os
import re
from pathlib import Path
from collections import defaultdict

def find_sorry_statements(root_dir):
    """Find all sorry statements in .lean files."""
    sorry_data = []
    
    for lean_file in Path(root_dir).rglob("*.lean"):
        with open(lean_file, 'r', encoding='utf-8') as f:
            lines = f.readlines()
            
        for i, line in enumerate(lines, 1):
            if 'sorry' in line.lower():
                # Get context (5 lines before)
                context_start = max(0, i-6)
                context = ''.join(lines[context_start:i])
                
                sorry_data.append({
                    'file': str(lean_file.relative_to(root_dir)),
                    'line': i,
                    'context': context,
                    'line_content': line.strip()
                })
    
    return sorry_data

def categorize_sorry(sorry_info):
    """Categorize sorry by difficulty."""
    file = sorry_info['file']
    context = sorry_info['context'].lower()
    
    # Easy: Standard mathematical results
    easy_keywords = [
        'continuous', 'measurable', 'integrable', 'compact',
        'embedding', 'convergence', 'limit', 'bounded'
    ]
    
    # Medium: Physical hypotheses
    medium_keywords = [
        'brst', 'gauge', 'gribov', 'ghost', 'yang-mills',
        'qcd', 'lattice', 'topological', 'entropy'
    ]
    
    # Hard: Original conjectures
    hard_keywords = [
        'mass gap', 'confinement', 'ricci', 'curvature',
        'holographic', 'entropic'
    ]
    
    if any(kw in context for kw in easy_keywords):
        return 'EASY'
    elif any(kw in context for kw in hard_keywords):
        return 'HARD'
    elif any(kw in context for kw in medium_keywords):
        return 'MEDIUM'
    else:
        # Default to medium
        return 'MEDIUM'

def main():
    root = Path('/home/ubuntu/yang-mills-mass-gap/YangMills')
    
    print("🔍 Analyzing all sorry statements...\n")
    
    sorrys = find_sorry_statements(root)
    
    print(f"📊 Total sorry statements found: {len(sorrys)}\n")
    
    # Categorize by difficulty
    by_difficulty = defaultdict(list)
    for sorry in sorrys:
        category = categorize_sorry(sorry)
        by_difficulty[category].append(sorry)
    
    # Categorize by directory
    by_dir = defaultdict(list)
    for sorry in sorrys:
        dir_name = sorry['file'].split('/')[0] if '/' in sorry['file'] else 'Root'
        by_dir[dir_name].append(sorry)
    
    # Print summary
    print("=" * 80)
    print("SUMMARY BY DIFFICULTY")
    print("=" * 80)
    for difficulty in ['EASY', 'MEDIUM', 'HARD']:
        count = len(by_difficulty[difficulty])
        print(f"{difficulty:10s}: {count:3d} sorry statements")
    print()
    
    print("=" * 80)
    print("SUMMARY BY DIRECTORY")
    print("=" * 80)
    for dir_name in sorted(by_dir.keys()):
        count = len(by_dir[dir_name])
        print(f"{dir_name:20s}: {count:3d} sorry statements")
    print()
    
    # Print Refinement Layer details
    print("=" * 80)
    print("REFINEMENT LAYER DETAILS (Priority)")
    print("=" * 80)
    refinement_sorrys = [s for s in sorrys if 'Refinement' in s['file']]
    print(f"Total in Refinement: {len(refinement_sorrys)}\n")
    
    ref_by_file = defaultdict(list)
    for sorry in refinement_sorrys:
        ref_by_file[sorry['file']].append(sorry)
    
    for file in sorted(ref_by_file.keys()):
        count = len(ref_by_file[file])
        difficulty_counts = defaultdict(int)
        for sorry in ref_by_file[file]:
            diff = categorize_sorry(sorry)
            difficulty_counts[diff] += 1
        
        easy = difficulty_counts['EASY']
        medium = difficulty_counts['MEDIUM']
        hard = difficulty_counts['HARD']
        
        print(f"{file}")
        print(f"  Total: {count} | Easy: {easy} | Medium: {medium} | Hard: {hard}")
    
    print("\n" + "=" * 80)
    print("RECOMMENDED ATTACK PLAN")
    print("=" * 80)
    print("Week 1: Attack EASY sorrys (quick wins)")
    print(f"  Target: {len(by_difficulty['EASY'])} sorrys")
    print("  Strategy: Adapt from mathlib4, standard proofs")
    print()
    print("Week 2-3: Attack MEDIUM sorrys")
    print(f"  Target: {len(by_difficulty['MEDIUM'])} sorrys")
    print("  Strategy: Literature justification, physical arguments")
    print()
    print("Month 2-3: Attack HARD sorrys (with community)")
    print(f"  Target: {len(by_difficulty['HARD'])} sorrys")
    print("  Strategy: Collaboration, may become separate papers")
    print("=" * 80)

if __name__ == '__main__':
    main()
