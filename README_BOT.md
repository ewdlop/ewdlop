# README Bot

A GitHub bot that automatically changes all README.md files in the repository to contain "Please readme.md".

## Features

- 🔍 Automatically finds all README.md files in the repository (recursively)
- 📝 Replaces their content with "Please readme.md"
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

## Files

- `readme_bot.py` - Main bot script
- `.github/workflows/readme-bot.yml` - GitHub Actions workflow

## Requirements

- Python 3.x
- No additional dependencies required (uses only standard library)