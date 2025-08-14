#!/usr/bin/env python3
"""
GitHub Bot to replace README.md files with "Please readme.md" files

This script finds all README.md files in the repository, saves their content,
deletes the README.md files, and creates new "Please readme.md" files with the original content.
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


def replace_readme_with_please_readme(readme_path: Path) -> bool:
    """Replace README.md with 'Please readme.md' containing the original content."""
    try:
        # Read the original content
        with open(readme_path, 'r', encoding='utf-8') as f:
            original_content = f.read()
        
        # Get the directory and create the new file path
        directory = readme_path.parent
        new_file_path = directory / "Please readme.md"
        
        # Write the original content to the new file
        with open(new_file_path, 'w', encoding='utf-8') as f:
            f.write(original_content)
        
        # Remove the original README.md file
        readme_path.unlink()
        
        print(f"✓ Replaced: {readme_path} → {new_file_path}")
        return True
    except Exception as e:
        print(f"✗ Error replacing {readme_path}: {e}")
        return False


def main():
    """Main function to execute the README replacement bot."""
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
        confirm = input("\nDo you want to replace these README.md files with 'Please readme.md' files? (y/N): ")
        if confirm.lower() != 'y':
            print("Operation cancelled.")
            return
    else:
        print("\n🚀 Force mode enabled, proceeding without confirmation...")
    
    # Replace each README.md file with "Please readme.md"
    success_count = 0
    for readme_path in readme_files:
        if replace_readme_with_please_readme(readme_path):
            success_count += 1
    
    print(f"\n🎉 Bot completed! Successfully replaced {success_count}/{len(readme_files)} README.md files with 'Please readme.md' files.")


if __name__ == "__main__":
    main()