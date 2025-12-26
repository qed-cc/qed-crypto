#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2025 Rhett Creighton
# SPDX-License-Identifier: Apache-2.0

"""Convert HTML file to C string literal for embedding"""

import sys
import os

def html_to_c_string(html_file):
    with open(html_file, 'r') as f:
        content = f.read()
    
    # Escape special characters
    content = content.replace('\\', '\\\\')
    content = content.replace('"', '\\"')
    content = content.replace('\n', '\\n"\n"')
    
    # Wrap in quotes
    return f'"{content}"'

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: generate_embedded_html.py <html_file>")
        sys.exit(1)
    
    html_file = sys.argv[1]
    if not os.path.exists(html_file):
        print(f"Error: {html_file} not found")
        sys.exit(1)
    
    c_string = html_to_c_string(html_file)
    
    # Write to header file
    with open("truth_game_embedded.h", 'w') as f:
        f.write(c_string)
    
    print("Generated truth_game_embedded.h")