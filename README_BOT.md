# README Bot

A GitHub bot that automatically replaces all README.md files with "Please readme.md" files containing the original content.

## Features

- 🔍 Automatically finds all README.md files in the repository (recursively)
- 📝 Deletes README.md files and creates "Please readme.md" files with the original content
- 🤖 Can be run manually or via GitHub Actions
- ⚡ Force mode for automated execution
- 🚫 Skips files in .git directory

## Usage

### Manual Execution

```bash
# Interactive mode (asks for confirmation)
python3 readme_bot.py

# Force mode (no confirmation)
python3 readme_bot.py . --force

# Specify custom directory
python3 readme_bot.py /path/to/directory --force
```

### GitHub Actions

The bot can also run automatically via GitHub Actions:

- **Manual trigger**: Go to Actions tab and run "README Bot" workflow
- **Scheduled**: Runs daily at 2 AM UTC (can be modified in `.github/workflows/readme-bot.yml`)

## How It Works

1. **Finds** all README.md files in the repository
2. **Reads** the original content from each README.md file
3. **Creates** a new "Please readme.md" file with the original content
4. **Deletes** the original README.md file

## Files

- `readme_bot.py` - Main bot script
- `.github/workflows/readme-bot.yml` - GitHub Actions workflow

## Requirements

- Python 3.x
- No additional dependencies required (uses only standard library)