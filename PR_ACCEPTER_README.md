# Out-of-Here PR Accepter Bot

A creative and random pull request acceptance bot that automatically evaluates and merges PRs based on mystical, mathematical, and chaotic criteria.

## Features

- 🎭 **Creative Evaluation**: Uses unconventional criteria like cosmic timing, lucky numbers, and mathematical content
- 🎲 **Controlled Randomness**: Incorporates chaos while maintaining some predictability
- 🤖 **Automatic Merging**: Merges PRs that achieve "out-of-here" status
- 📊 **Transparent Scoring**: Provides detailed evaluation comments on each PR
- ⚡ **GitHub Actions Integration**: Runs automatically on PR events
- 🔮 **Mystical Threshold**: Requires ≥5 points for automatic acceptance

## How It Works

The bot evaluates PRs using eight creative criteria:

### 1. 🌙 Cosmic Alignment (0-3 points)
- Bonus points for PRs submitted during mystical hours (3 AM, 1 PM, 11 PM)

### 2. 🍀 Lucky Numbers (0-2 points)  
- PR numbers divisible by 7 receive luck bonuses

### 3. ✨ Creative Titles (0-N points)
- Points for including creative words: magic, cosmic, quantum, recursive, meta, holomorphic, categorical, monad, functor, topology, manifold, please

### 4. 👤 Author Characteristics (0-2 points)
- Perfect 7-character usernames or bot-friendly names

### 5. 🎨 File Diversity (0-2 points)
- Bonus for PRs touching 3+ different file types

### 6. 📐 Mathematical Content (0-N points)
- Points for math-related keywords: theorem, proof, lemma, category, coq, formal, verification

### 7. 🎲 Chaos Magic (varies)
- Pure randomness: d20 roll where 18+ gives +5 points, 1 gives -2 points

### 8. 📏 Perfect Size (0-2 points)
- PRs with 42-420 total line changes hit the sweet spot

## Usage

### Automatic Trigger
The bot runs automatically when:
- New PRs are opened
- PRs are updated (synchronize)
- PRs are reopened

### Manual Trigger
You can manually trigger evaluation:
1. Go to the Actions tab
2. Run "Out-of-Here PR Accepter" workflow
3. Optionally specify a PR number

### Acceptance Threshold
- **Minimum Score**: 5/20 points required for automatic merge
- **Evaluation**: Every PR gets a detailed comment with scoring breakdown
- **Transparency**: All criteria and reasoning are clearly documented

## Examples

### High-Scoring PR Example
```
🎭 Out-of-Here PR Accepter Bot Evaluation

Score: 8/20

Criteria met:
- 🌙 Cosmic alignment: PR submitted during mystical hour 23
- ✨ Creative title contains: 'categorical'
- 📐 Mathematical content: theorem, proof, category
- 🎲 Chaos magic: Rolled natural 19!

🎉 Result: ACCEPTED! This PR has achieved out-of-here status!
```

### Low-Scoring PR Example
```
🎭 Out-of-Here PR Accepter Bot Evaluation

Score: 2/20

Criteria met:
- 🍀 Lucky PR number: #14 is divisible by 7
- 🎨 Diverse file types: py, md

🚫 Result: Not quite out-of-here enough (needed ≥5 points)
```

## Files

- `pr_accepter_bot.py` - Main bot script with evaluation logic
- `.github/workflows/pr-accepter.yml` - GitHub Actions workflow
- `PR_ACCEPTER_README.md` - This documentation

## Configuration

The bot can be customized by modifying `pr_accepter_bot.py`:

- **Acceptance threshold**: Change the minimum score in `should_accept_pr()`
- **Criteria weights**: Adjust point values for different factors
- **Creative words**: Add/remove words in the creative titles list
- **Merge method**: Choose between 'merge', 'squash', or 'rebase'

## Requirements

- Python 3.x
- `requests` library (automatically installed in GitHub Actions)
- GitHub token with appropriate permissions

## Permissions Required

The GitHub Actions workflow needs:
- `contents: write` - To merge PRs
- `pull-requests: write` - To merge and comment on PRs  
- `issues: write` - To add comments

## Safety Features

- Only evaluates open PRs
- Provides detailed reasoning for all decisions
- Graceful error handling for API failures
- Manual override capability via workflow dispatch

## Philosophy

This bot embraces the playful and experimental nature of the repository while maintaining practical functionality. It encourages creative contributions and adds an element of fun to the development process, perfectly complementing the existing README bot.

The "out-of-here" concept represents contributions that go beyond the ordinary - whether through timing, creativity, mathematical depth, or pure serendipity. It's not just about code quality, but about the magic of the moment when a contribution is made.

## Limitations

- Requires manual intervention for merge conflicts
- API rate limits may affect operation
- Chaos factor means some randomness in outcomes
- Not suitable for critical production repositories (this is experimental!)

## Contributing

Want to improve the bot? Consider:
- Adding new creative evaluation criteria
- Implementing seasonal or date-based bonuses
- Creating themed scoring for special occasions
- Enhancing the randomness algorithms
- Adding support for different repository types