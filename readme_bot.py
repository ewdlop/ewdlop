#!/usr/bin/env python3
"""
GitHub Bot to change all README.md files to "Please readme.md"

This script finds all README.md files in the repository and replaces their content
with the text "Please readme.md".
"""

import os
import sys
from pathlib import Path


def find_readme_files(root_path: str) -> list[Path]:
    """Find all README.md files in the given root path."""
    readme_files = []
    root = Path(root_path)
    
    # Use glob to find all README.md files recursively
    for readme_path in root.rglob("README.md"):
        # Skip files in .git directory
        if ".git" not in str(readme_path):
            readme_files.append(readme_path)
    
    return readme_files


def update_readme_content(readme_path: Path, new_content: str) -> bool:
    """Update the content of a README.md file."""
    try:
        with open(readme_path, 'w', encoding='utf-8') as f:
            f.write(new_content)
        print(f"✓ Updated: {readme_path}")
        return True
    except Exception as e:
        print(f"✗ Error updating {readme_path}: {e}")
        return False


def main():
    """Main function to execute the README modification bot."""
    # Default to current directory if no argument provided
    root_path = sys.argv[1] if len(sys.argv) > 1 else "."
    
    print(f"🤖 README Bot: Searching for README.md files in {root_path}")
    
    # Find all README.md files
    readme_files = find_readme_files(root_path)
    
    if not readme_files:
        print("No README.md files found.")
        return
    
    print(f"Found {len(readme_files)} README.md file(s):")
    for readme_path in readme_files:
        print(f"  - {readme_path}")
    
    # Check if --force flag is provided to skip confirmation
    force_mode = len(sys.argv) > 2 and "--force" in sys.argv
    
    if not force_mode:
        # Ask for confirmation before proceeding
        confirm = input("\nDo you want to replace the content of these files with 'Please readme.md'? (y/N): ")
        if confirm.lower() != 'y':
            print("Operation cancelled.")
            return
    else:
        print("\n🚀 Force mode enabled, proceeding without confirmation...")
    
    # Content to replace with
    new_content = "Please readme.md\n"
    
    # Update each README file
    success_count = 0
    for readme_path in readme_files:
        if update_readme_content(readme_path, new_content):
            success_count += 1
    
    print(f"\n🎉 Bot completed! Successfully updated {success_count}/{len(readme_files)} files.")


if __name__ == "__main__":
    main()