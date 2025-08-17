# C# Language Proposal Crawler

A Python script that crawls https://github.com/dotnet/csharplang/issues to identify and explain cool C# language design proposals with both rule-based and AI-powered analysis.

## Features

- 🔍 **Automated Crawling**: Fetches issues from the dotnet/csharplang repository
- 🎯 **Smart Filtering**: Identifies language design proposals based on labels and content
- 🌟 **Hybrid Scoring**: Combines rule-based analysis with optional LLM-powered insights
- 🤖 **AI Enhancement**: Uses OpenAI GPT-3.5 for nuanced proposal analysis (optional)
- 📊 **Detailed Reports**: Generates comprehensive markdown reports with explanations
- 🚀 **Fallback Mode**: Works with mock data when API access is limited
- 🔧 **Configurable**: Enable/disable LLM scoring based on your needs

## How It Works

The crawler offers two scoring modes:

### Rule-Based Scoring (Default Fallback)
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

### LLM-Enhanced Scoring (Optional)
- **AI Analysis**: Uses OpenAI GPT-3.5 to evaluate proposals for innovation, impact, and elegance
- **Intelligent Insights**: Provides nuanced explanations beyond keyword matching
- **Hybrid Approach**: Combines AI insights (60% weight) with rule-based scoring (40% weight)
- **Fallback Safe**: Automatically falls back to rule-based scoring if LLM is unavailable

## Usage

### Basic Usage
```bash
# Analyze top 10 proposals with LLM scoring (if available)
python3 csharp_language_crawler.py

# Analyze top 5 proposals with LLM scoring
python3 csharp_language_crawler.py 5

# Analyze top 20 proposals without LLM (rule-based only)
python3 csharp_language_crawler.py 20 --no-llm
```

### LLM Configuration

To enable LLM-enhanced scoring:

```bash
# Set your OpenAI API key
export OPENAI_API_KEY="your-api-key-here"

# Run with LLM scoring
python3 csharp_language_crawler.py 10
```

### Requirements

- Python 3.7+
- `requests` library (automatically falls back to mock data if not available)
- `openai` library (optional, for LLM features)
- Internet connection (for GitHub API access)
- OpenAI API key (optional, for LLM scoring)

### Installation

```bash
# Install required packages
pip install requests

# Optional: Install OpenAI for LLM features
pip install openai

# Make the script executable
chmod +x csharp_language_crawler.py

# Run directly
./csharp_language_crawler.py 10
```

## Output

The crawler generates:

1. **Console Output**: Real-time progress and summary with scoring method indication
2. **Markdown Report**: Timestamped file with detailed analysis (e.g., `csharp_proposals_llm_20240117_143022.md` or `csharp_proposals_rules_20240117_143022.md`)

### Sample Output (LLM-Enhanced)

```markdown
# 🚀 Cool C# Language Design Proposals

*Generated on 2024-01-17 14:30:22 using 🤖 LLM-enhanced scoring*

## 1. **Abstract static interface members** (Issue #4907)
🌟 Coolness Score: 9/10 (LLM: 8.5/10)

📝 **What it is:** This feature allows interfaces to declare abstract static members...

🎯 **Why it's cool:** High community engagement (156 comments); Involves generic (language impact); LLM analysis (score: 8.5/10)...

🤖 **LLM Analysis:** This proposal represents a significant advancement in C# generics, enabling true static polymorphism. The innovation allows for more elegant generic math and operator overloading patterns...

📊 **Status:** Closed
💬 **Community Interest:** 156 comments
🏷️ **Labels:** Proposal, Championed, Language-Feature
```

## Coolness Scoring Algorithm

The crawler uses a sophisticated hybrid scoring system:

### Rule-Based Components (40% weight when LLM enabled, 100% when disabled)
- **Community Engagement** (0-3 points): Based on comment count
- **Language Impact** (0-N points): Keywords like generic, pattern, async, memory
- **Label Importance** (0-3 points): Championed, approved, working set
- **Innovation Factors** (0-N points): New, novel, first-class, native

### LLM Enhancement (60% weight when enabled)
- **AI Analysis**: GPT-3.5 evaluates proposals for innovation, technical merit, and impact
- **Contextual Understanding**: Goes beyond keyword matching to understand proposal significance
- **Nuanced Scoring**: Provides explanations for why proposals are interesting or impactful

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

- `csharp_proposals_llm_YYYYMMDD_HHMMSS.md`: LLM-enhanced analysis report
- `csharp_proposals_rules_YYYYMMDD_HHMMSS.md`: Rule-based analysis report
- Console output with real-time progress and configuration info

## Configuration Examples

```bash
# Use LLM scoring with API key from environment
export OPENAI_API_KEY="sk-..."
python3 csharp_language_crawler.py 5

# Force rule-based scoring only
python3 csharp_language_crawler.py 10 --no-llm

# Run without OpenAI library (automatic fallback to rule-based)
python3 csharp_language_crawler.py
```

## Performance Notes

- **LLM Mode**: Slower due to API calls, but provides richer analysis
- **Rule Mode**: Fast, reliable, works offline with mock data
- **Hybrid Approach**: Best of both worlds when LLM is available
- **Rate Limiting**: Both GitHub and OpenAI APIs have rate limits

## License

This tool is designed for educational and research purposes to help understand C# language evolution.