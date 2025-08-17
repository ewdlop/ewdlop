# C# Language Proposal Crawler

A Python script that crawls https://github.com/dotnet/csharplang/issues to identify and explain cool C# language design proposals.

## Features

- 🔍 **Automated Crawling**: Fetches issues from the dotnet/csharplang repository
- 🎯 **Smart Filtering**: Identifies language design proposals based on labels and content
- 🌟 **Coolness Analysis**: Scores proposals based on community engagement, language impact, and innovation
- 📊 **Detailed Reports**: Generates comprehensive markdown reports with explanations
- 🚀 **Fallback Mode**: Works with mock data when API access is limited

## How It Works

The crawler:

1. **Fetches Issues**: Uses GitHub API to retrieve issues from dotnet/csharplang
2. **Filters Proposals**: Identifies language design proposals using:
   - Labels containing "proposal", "language", or "feature"
   - Titles containing "proposal"
   - Other proposal indicators
3. **Analyzes Coolness**: Evaluates proposals based on:
   - Community engagement (comment count)
   - Language impact keywords (generic, pattern, async, etc.)
   - Important labels (championed, approved, etc.)
   - Innovation indicators (new, introduce, novel, etc.)
4. **Generates Explanations**: Creates detailed explanations of why each proposal is interesting
5. **Produces Reports**: Outputs ranked lists with comprehensive analysis

## Usage

### Basic Usage
```bash
# Analyze top 10 proposals (default)
python3 csharp_language_crawler.py

# Analyze top 5 proposals
python3 csharp_language_crawler.py 5

# Analyze top 20 proposals
python3 csharp_language_crawler.py 20
```

### Requirements

- Python 3.7+
- `requests` library (automatically falls back to mock data if not available)
- Internet connection (for GitHub API access)

### Installation

```bash
# Make the script executable
chmod +x csharp_language_crawler.py

# Run directly
./csharp_language_crawler.py 10
```

## Output

The crawler generates:

1. **Console Output**: Real-time progress and summary
2. **Markdown Report**: Timestamped file with detailed analysis (e.g., `csharp_proposals_20240117_143022.md`)

### Sample Output

```markdown
# 🚀 Cool C# Language Design Proposals

## 1. **Abstract static interface members** (Issue #4907)
🌟 Coolness Score: 10/10

📝 **What it is:** This feature allows interfaces to declare abstract static members...

🎯 **Why it's cool:** High community engagement (156 comments); Involves generic (language impact)...

📊 **Status:** Closed
💬 **Community Interest:** 156 comments
🏷️ **Labels:** Proposal, Championed, Language-Feature
```

## Coolness Scoring Algorithm

The crawler uses a sophisticated scoring system:

- **Community Engagement** (0-3 points): Based on comment count
- **Language Impact** (0-N points): Keywords like generic, pattern, async, memory
- **Label Importance** (0-3 points): Championed, approved, working set
- **Innovation Factors** (0-N points): New, novel, first-class, native

Maximum score is capped at 10/10.

## Mock Data Mode

When GitHub API is not accessible, the crawler uses high-quality mock data featuring real C# language proposals like:

- Required members
- List patterns  
- Generic attributes
- Abstract static interface members
- Primary constructors
- Raw string literals

## Example Proposals Analyzed

The crawler identifies and explains proposals such as:

- **Primary Constructors**: Concise constructor parameter declaration
- **List Patterns**: Pattern matching for sequences and collections
- **Generic Attributes**: Strongly-typed attribute parameters
- **Required Members**: Mandatory initialization checking
- **Abstract Static Interface Members**: Static methods in interfaces

## API Rate Limiting

The GitHub API has rate limits:
- **60 requests/hour** for unauthenticated requests
- **5000 requests/hour** for authenticated requests

The crawler automatically falls back to mock data when rate limited.

## Contributing

To extend the crawler:

1. **Add New Filters**: Modify `filter_proposals()` to catch more proposal types
2. **Enhance Scoring**: Update `analyze_coolness()` with new criteria
3. **Improve Explanations**: Extend `explain_proposal()` with better summaries
4. **Add Features**: Include proposal status tracking, author analysis, etc.

## Files Generated

- `csharp_proposals_YYYYMMDD_HHMMSS.md`: Timestamped analysis report
- Console output with real-time progress

## License

This tool is designed for educational and research purposes to help understand C# language evolution.