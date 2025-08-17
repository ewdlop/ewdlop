#!/usr/bin/env python3
"""
C# Language Proposal Crawler

This script crawls https://github.com/dotnet/csharplang/issues to identify and explain
cool C# language design proposals. It fetches issues from the repository, filters for
language proposals, and provides explanations of interesting features and their impact.

Features:
- Rule-based scoring system
- Optional LLM-enhanced scoring for more nuanced analysis
- Fallback to mock data when APIs are unavailable
"""

import json
import os
import re
import sys
from datetime import datetime
from typing import Dict, List, Optional, Tuple
from dataclasses import dataclass

try:
    import requests
    REQUESTS_AVAILABLE = True
except ImportError:
    REQUESTS_AVAILABLE = False
    print("Warning: requests library not available, using mock data mode")

# OpenAI integration for LLM-based scoring
LLM_AVAILABLE = False
try:
    import openai
    LLM_AVAILABLE = True
except ImportError:
    pass


@dataclass
class LanguageProposal:
    """Represents a C# language design proposal."""
    number: int
    title: str
    labels: List[str]
    state: str
    body: str
    url: str
    created_at: str
    comments_count: int = 0
    llm_score: Optional[float] = None
    llm_analysis: Optional[str] = None


class CSharpLanguageCrawler:
    """Crawler for C# language design proposals from the dotnet/csharplang repository."""
    
    def __init__(self, use_llm: bool = True, openai_api_key: Optional[str] = None):
        self.base_url = "https://api.github.com/repos/dotnet/csharplang"
        self.headers = {
            'User-Agent': 'C# Language Proposal Crawler/1.0',
            'Accept': 'application/vnd.github.v3+json'
        }
        self.proposals: List[LanguageProposal] = []
        self.use_llm = use_llm and LLM_AVAILABLE
        
        # Initialize OpenAI if available and requested
        if self.use_llm:
            api_key = openai_api_key or os.getenv('OPENAI_API_KEY')
            if api_key:
                openai.api_key = api_key
                print("🤖 LLM scoring enabled")
            else:
                self.use_llm = False
                print("⚠️  LLM scoring disabled: No OpenAI API key found")
        elif use_llm and not LLM_AVAILABLE:
            print("⚠️  LLM scoring disabled: openai library not available")
        
    def fetch_issues(self, max_pages: int = 5) -> List[Dict]:
        """Fetch issues from the GitHub API."""
        if not REQUESTS_AVAILABLE:
            return self._get_mock_data()
            
        all_issues = []
        
        for page in range(1, max_pages + 1):
            try:
                url = f"{self.base_url}/issues?per_page=100&page={page}&state=all"
                response = requests.get(url, headers=self.headers, timeout=10)
                
                if response.status_code == 200:
                    issues = response.json()
                    if not issues:  # No more issues
                        break
                    all_issues.extend(issues)
                    print(f"Fetched page {page}: {len(issues)} issues")
                elif response.status_code == 403:
                    print("API rate limited or blocked, falling back to mock data")
                    return self._get_mock_data()
                else:
                    print(f"API request failed with status {response.status_code}")
                    break
                    
            except Exception as e:
                print(f"Error fetching page {page}: {e}")
                break
                
        return all_issues
    
    def _get_mock_data(self) -> List[Dict]:
        """Provide mock data when API is not accessible."""
        return [
            {
                "number": 7314,
                "title": "Required members",
                "labels": [
                    {"name": "Proposal"},
                    {"name": "Championed"},
                    {"name": "Language-Feature"}
                ],
                "state": "closed",
                "body": "# Required members\n\n## Summary\n\nThis proposal adds a way to specify that a constructor should not be considered complete unless certain members have been initialized...",
                "html_url": "https://github.com/dotnet/csharplang/issues/7314",
                "created_at": "2024-01-15T10:30:00Z",
                "comments": 45
            },
            {
                "number": 6911,
                "title": "List patterns",
                "labels": [
                    {"name": "Proposal"},
                    {"name": "Championed"},
                    {"name": "Language-Feature"}
                ],
                "state": "closed",
                "body": "# List patterns\n\n## Summary\n\nList patterns extend pattern matching to match sequences and lists, allowing developers to match against the contents and structure of collections...",
                "html_url": "https://github.com/dotnet/csharplang/issues/6911",
                "created_at": "2023-08-22T14:20:00Z",
                "comments": 89
            },
            {
                "number": 5295,
                "title": "Generic attributes",
                "labels": [
                    {"name": "Proposal"},
                    {"name": "Championed"},
                    {"name": "Language-Feature"}
                ],
                "state": "closed",
                "body": "# Generic attributes\n\n## Summary\n\nAllow attributes to be generic, enabling strongly-typed attribute parameters and reducing the need for reflection in attribute-based frameworks...",
                "html_url": "https://github.com/dotnet/csharplang/issues/5295",
                "created_at": "2022-04-10T09:15:00Z",
                "comments": 67
            },
            {
                "number": 4907,
                "title": "Abstract static interface members",
                "labels": [
                    {"name": "Proposal"},
                    {"name": "Championed"},
                    {"name": "Language-Feature"}
                ],
                "state": "closed",
                "body": "# Abstract static interface members\n\n## Summary\n\nThis feature allows interfaces to declare abstract static members, enabling generic programming with static methods and operators...",
                "html_url": "https://github.com/dotnet/csharplang/issues/4907",
                "created_at": "2022-01-18T16:45:00Z",
                "comments": 156
            },
            {
                "number": 6739,
                "title": "Primary constructors for classes and structs",
                "labels": [
                    {"name": "Proposal"},
                    {"name": "Championed"},
                    {"name": "Language-Feature"}
                ],
                "state": "closed",
                "body": "# Primary constructors for classes and structs\n\n## Summary\n\nExtend primary constructors (already available for records) to classes and structs, providing a more concise way to declare constructor parameters...",
                "html_url": "https://github.com/dotnet/csharplang/issues/6739",
                "created_at": "2023-03-28T11:30:00Z",
                "comments": 234
            },
            {
                "number": 4726,
                "title": "Raw string literals",
                "labels": [
                    {"name": "Proposal"},
                    {"name": "Championed"},
                    {"name": "Language-Feature"}
                ],
                "state": "closed",
                "body": "# Raw string literals\n\n## Summary\n\nIntroduce raw string literals that can contain any sequence of characters without escape sequences, making it easier to work with complex strings...",
                "html_url": "https://github.com/dotnet/csharplang/issues/4726",
                "created_at": "2021-09-14T13:20:00Z",
                "comments": 98
            }
        ]
    
    def filter_proposals(self, issues: List[Dict]) -> List[LanguageProposal]:
        """Filter issues to find language design proposals."""
        proposals = []
        
        for issue in issues:
            # Skip pull requests
            if 'pull_request' in issue:
                continue
                
            # Check if it's a proposal based on labels and title
            labels = [label['name'] for label in issue.get('labels', [])]
            title = issue.get('title', '').lower()
            
            # Filter criteria for language proposals
            is_proposal = (
                any('proposal' in label.lower() for label in labels) or
                'proposal' in title or
                any('language' in label.lower() for label in labels) or
                any('feature' in label.lower() for label in labels)
            )
            
            if is_proposal:
                proposal = LanguageProposal(
                    number=issue.get('number', 0),
                    title=issue.get('title', ''),
                    labels=labels,
                    state=issue.get('state', 'unknown'),
                    body=issue.get('body', '') or '',
                    url=issue.get('html_url', ''),
                    created_at=issue.get('created_at', ''),
                    comments_count=issue.get('comments', 0)
                )
                proposals.append(proposal)
        
        return proposals
    
    def analyze_with_llm(self, proposal: LanguageProposal) -> Tuple[float, str]:
        """Use LLM to analyze and score a proposal."""
        if not self.use_llm:
            return 0.0, "LLM not available"
        
        try:
            # Prepare content for LLM analysis
            content = f"""
Title: {proposal.title}
Labels: {', '.join(proposal.labels)}
Comments: {proposal.comments_count}
State: {proposal.state}

Description:
{proposal.body[:1000]}...
"""
            
            prompt = f"""Analyze this C# language design proposal and provide:
1. A score from 1-10 for how "cool" and impactful this proposal is
2. A brief analysis explaining why it's interesting

Consider factors like:
- Innovation and novelty
- Impact on C# language evolution
- Developer productivity benefits
- Technical complexity and elegance
- Community interest level

Proposal to analyze:
{content}

Respond in this format:
Score: X/10
Analysis: [Your analysis here]"""
            
            response = openai.ChatCompletion.create(
                model="gpt-3.5-turbo",
                messages=[
                    {"role": "system", "content": "You are an expert C# language designer and developer who evaluates programming language proposals."},
                    {"role": "user", "content": prompt}
                ],
                max_tokens=300,
                temperature=0.7
            )
            
            response_text = response.choices[0].message.content.strip()
            
            # Parse the response
            score = 5.0  # default
            analysis = response_text
            
            lines = response_text.split('\n')
            for line in lines:
                if line.startswith('Score:'):
                    try:
                        score_text = line.split(':')[1].strip()
                        score = float(score_text.split('/')[0])
                    except:
                        pass
                elif line.startswith('Analysis:'):
                    analysis = line.split('Analysis:', 1)[1].strip()
                    break
            
            return min(max(score, 1.0), 10.0), analysis
            
        except Exception as e:
            print(f"⚠️  LLM analysis failed for proposal #{proposal.number}: {e}")
            return 0.0, f"LLM analysis failed: {str(e)}"
    
    def analyze_coolness(self, proposal: LanguageProposal) -> Tuple[int, str]:
        """Analyze how 'cool' a proposal is and provide explanation."""
        coolness_score = 0
        reasons = []
        
        # Get LLM analysis if available
        llm_score = 0.0
        llm_analysis = ""
        if self.use_llm and proposal.llm_score is None:
            llm_score, llm_analysis = self.analyze_with_llm(proposal)
            proposal.llm_score = llm_score
            proposal.llm_analysis = llm_analysis
        elif proposal.llm_score is not None:
            llm_score = proposal.llm_score
            llm_analysis = proposal.llm_analysis or ""
        
        # Factor 1: Community engagement (comments)
        if proposal.comments_count > 100:
            coolness_score += 3
            reasons.append(f"High community engagement ({proposal.comments_count} comments)")
        elif proposal.comments_count > 50:
            coolness_score += 2
            reasons.append(f"Good community discussion ({proposal.comments_count} comments)")
        elif proposal.comments_count > 20:
            coolness_score += 1
            reasons.append(f"Decent community interest ({proposal.comments_count} comments)")
        
        # Factor 2: Language impact keywords
        title_lower = proposal.title.lower()
        body_lower = proposal.body.lower()
        
        impact_keywords = {
            'generic': 2,
            'pattern': 2,
            'async': 2,
            'performance': 2,
            'unsafe': 1,
            'reflection': 1,
            'interop': 1,
            'memory': 2,
            'syntax': 1,
            'operator': 1,
            'linq': 2,
            'expression': 1,
            'delegate': 1,
            'interface': 1,
            'inheritance': 1,
            'nullable': 2,
            'required': 1,
            'primary': 1,
            'record': 1,
            'struct': 1,
            'tuple': 1
        }
        
        for keyword, score in impact_keywords.items():
            if keyword in title_lower or keyword in body_lower:
                coolness_score += score
                reasons.append(f"Involves {keyword} (language impact)")
        
        # Factor 3: Labels indicating importance
        important_labels = {
            'championed': 3,
            'approved': 2,
            'working set': 2,
            'language-feature': 1,
            'enhancement': 1
        }
        
        for label in proposal.labels:
            label_lower = label.lower()
            for important, score in important_labels.items():
                if important in label_lower:
                    coolness_score += score
                    reasons.append(f"Label: {label}")
                    break
        
        # Factor 4: Novelty and innovation indicators
        innovation_keywords = {
            'new': 1,
            'introduce': 1,
            'novel': 2,
            'first-class': 2,
            'native': 1,
            'built-in': 1,
            'compiler': 1
        }
        
        for keyword, score in innovation_keywords.items():
            if keyword in title_lower or keyword in body_lower:
                coolness_score += score
                reasons.append(f"Innovation keyword: {keyword}")
        
        # Factor 5: LLM enhancement (if available)
        if llm_score > 0:
            # Weight LLM score and combine with rule-based score
            llm_weighted = int(llm_score * 0.6)  # 60% weight for LLM
            coolness_score = int(coolness_score * 0.4 + llm_weighted)  # 40% weight for rules
            reasons.append(f"LLM analysis (score: {llm_score:.1f}/10)")
            if llm_analysis:
                reasons.append(f"LLM insight: {llm_analysis[:100]}...")
        
        explanation = "; ".join(reasons) if reasons else "Standard proposal"
        return min(coolness_score, 10), explanation  # Cap at 10
    
    def explain_proposal(self, proposal: LanguageProposal) -> str:
        """Generate a detailed explanation of why the proposal is interesting."""
        coolness, analysis = self.analyze_coolness(proposal)
        
        # Extract summary from body if available
        summary = ""
        body_lines = proposal.body.split('\n')
        for i, line in enumerate(body_lines):
            if line.strip().lower().startswith('## summary'):
                # Look for the next few lines after summary
                for j in range(i + 1, min(i + 10, len(body_lines))):
                    if body_lines[j].strip() and not body_lines[j].startswith('#'):
                        summary = body_lines[j].strip()
                        break
                break
        
        if not summary and len(body_lines) > 0:
            # Use the first substantial line as summary
            for line in body_lines:
                if len(line.strip()) > 50 and not line.startswith('#'):
                    summary = line.strip()[:200] + "..."
                    break
        
        explanation = f"""
**{proposal.title}** (Issue #{proposal.number})
🌟 Coolness Score: {coolness}/10"""
        
        # Add LLM score if available
        if proposal.llm_score and proposal.llm_score > 0:
            explanation += f" (LLM: {proposal.llm_score:.1f}/10)"
        
        explanation += f"""

📝 **What it is:** {summary or "A C# language enhancement proposal"}

🎯 **Why it's cool:** {analysis}"""
        
        # Add LLM analysis if available
        if proposal.llm_analysis and proposal.llm_analysis.strip():
            explanation += f"""

🤖 **LLM Analysis:** {proposal.llm_analysis}"""
        
        explanation += f"""

📊 **Status:** {proposal.state.title()}
💬 **Community Interest:** {proposal.comments_count} comments
🏷️ **Labels:** {', '.join(proposal.labels) if proposal.labels else 'None'}

🔗 **Link:** {proposal.url}
"""
        return explanation.strip()
    
    def crawl_and_analyze(self, max_proposals: int = 10) -> str:
        """Main method to crawl and analyze proposals."""
        print("🔍 Crawling C# Language Design Proposals...")
        
        # Fetch issues
        issues = self.fetch_issues()
        print(f"📥 Fetched {len(issues)} total issues")
        
        # Filter for proposals
        self.proposals = self.filter_proposals(issues)
        print(f"🎯 Found {len(self.proposals)} language proposals")
        
        if not self.proposals:
            return "No language proposals found."
        
        # Sort by coolness score
        proposal_scores = []
        for proposal in self.proposals:
            score, _ = self.analyze_coolness(proposal)
            proposal_scores.append((score, proposal))
        
        proposal_scores.sort(key=lambda x: x[0], reverse=True)
        
        # Generate report
        llm_status = "🤖 LLM-enhanced" if self.use_llm else "📏 Rule-based"
        report = f"""# 🚀 Cool C# Language Design Proposals

*Generated on {datetime.now().strftime('%Y-%m-%d %H:%M:%S')} using {llm_status} scoring*

Found {len(self.proposals)} language design proposals from the dotnet/csharplang repository.
Here are the top {min(max_proposals, len(self.proposals))} coolest ones:

---

"""
        
        for i, (score, proposal) in enumerate(proposal_scores[:max_proposals], 1):
            report += f"## {i}. {self.explain_proposal(proposal)}\n\n---\n\n"
        
        report += f"""## 📊 Summary Statistics

- **Total Proposals Analyzed:** {len(self.proposals)}
- **Average Coolness Score:** {sum(score for score, _ in proposal_scores) / len(proposal_scores):.1f}/10
- **Most Discussed:** {max(self.proposals, key=lambda p: p.comments_count).title} ({max(p.comments_count for p in self.proposals)} comments)
- **Scoring Method:** {"LLM-enhanced (OpenAI GPT-3.5)" if self.use_llm else "Rule-based algorithm"}
- **Repository:** https://github.com/dotnet/csharplang

*This analysis combines community engagement, language impact, innovation factors{", and AI insights" if self.use_llm else ""}.*
"""
        
        return report


def main():
    """Main function to run the crawler."""
    max_proposals = 10
    use_llm = True
    
    # Parse command line arguments
    if len(sys.argv) > 1:
        try:
            max_proposals = int(sys.argv[1])
        except ValueError:
            print("Usage: python3 csharp_language_crawler.py [max_proposals] [--no-llm]")
            print("  max_proposals: Number of proposals to analyze (default: 10)")
            print("  --no-llm: Disable LLM scoring and use only rule-based analysis")
            return
    
    # Check for --no-llm flag
    if '--no-llm' in sys.argv:
        use_llm = False
    
    # Show configuration
    print("🔧 Configuration:")
    print(f"   📊 Max proposals: {max_proposals}")
    print(f"   🤖 LLM scoring: {'Enabled' if use_llm else 'Disabled'}")
    if use_llm and not os.getenv('OPENAI_API_KEY'):
        print("   ⚠️  Note: Set OPENAI_API_KEY environment variable for LLM scoring")
    print()
    
    crawler = CSharpLanguageCrawler(use_llm=use_llm)
    report = crawler.crawl_and_analyze(max_proposals)
    
    # Save report to file
    timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
    scoring_method = "llm" if crawler.use_llm else "rules"
    filename = f"csharp_proposals_{scoring_method}_{timestamp}.md"
    
    with open(filename, 'w', encoding='utf-8') as f:
        f.write(report)
    
    print(f"\n📄 Report saved to: {filename}")
    print("\n" + "="*60)
    print(report)


if __name__ == "__main__":
    main()