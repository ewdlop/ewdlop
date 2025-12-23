#!/usr/bin/env python3
"""
Out-of-Here Random Pull Request Accepter Bot

This bot evaluates pull requests using creative and random criteria,
and automatically merges them if they meet the "out-of-here" standards.
It's designed to be fun, experimental, and slightly unpredictable.
"""

import json
import os
import random
import sys
import time
from datetime import datetime
from typing import Dict, List, Optional, Tuple

try:
    import requests
except ImportError:
    print("Error: requests library is required. Run: pip install requests")
    sys.exit(1)


class OutOfHerePRAccepter:
    """A creative and random pull request acceptance bot."""
    
    def __init__(self, github_token: str, repo_owner: str, repo_name: str):
        self.github_token = github_token
        self.repo_owner = repo_owner
        self.repo_name = repo_name
        self.base_url = f"https://api.github.com/repos/{repo_owner}/{repo_name}"
        self.headers = {
            'Authorization': f'token {github_token}',
            'Accept': 'application/vnd.github.v3+json',
            'X-GitHub-Api-Version': '2022-11-28'
        }
        
        # Random seed based on current time for true randomness
        random.seed(int(time.time()))
    
    def get_pr_info(self, pr_number: int) -> Optional[Dict]:
        """Fetch pull request information from GitHub API."""
        try:
            url = f"{self.base_url}/pulls/{pr_number}"
            response = requests.get(url, headers=self.headers, timeout=10)
            
            if response.status_code == 200:
                return response.json()
            else:
                print(f"❌ Failed to fetch PR #{pr_number}: {response.status_code}")
                return None
        except Exception as e:
            print(f"❌ Error fetching PR info: {e}")
            return None
    
    def get_pr_files(self, pr_number: int) -> List[Dict]:
        """Get the files changed in the pull request."""
        try:
            url = f"{self.base_url}/pulls/{pr_number}/files"
            response = requests.get(url, headers=self.headers, timeout=10)
            
            if response.status_code == 200:
                return response.json()
            else:
                print(f"❌ Failed to fetch PR files: {response.status_code}")
                return []
        except Exception as e:
            print(f"❌ Error fetching PR files: {e}")
            return []
    
    def calculate_out_of_here_score(self, pr_info: Dict, pr_files: List[Dict]) -> Tuple[int, List[str]]:
        """Calculate the 'out-of-here' score using creative criteria."""
        score = 0
        reasons = []
        
        # Factor 1: Time-based randomness (cosmic alignment)
        current_hour = datetime.now().hour
        if current_hour in [3, 13, 23]:  # Mystical hours
            score += 3
            reasons.append(f"🌙 Cosmic alignment: PR submitted during mystical hour {current_hour}")
        
        # Factor 2: PR number luck
        pr_number = pr_info['number']
        if pr_number % 7 == 0:  # Lucky number 7
            score += 2
            reasons.append(f"🍀 Lucky PR number: #{pr_number} is divisible by 7")
        
        # Factor 3: Title creativity (contains unusual words)
        title = pr_info['title'].lower()
        creative_words = ['magic', 'cosmic', 'quantum', 'recursive', 'meta', 'holomorphic', 
                         'categorical', 'monad', 'functor', 'topology', 'manifold', 'please']
        for word in creative_words:
            if word in title:
                score += 1
                reasons.append(f"✨ Creative title contains: '{word}'")
        
        # Factor 4: Author name characteristics
        author = pr_info['user']['login']
        if len(author) == 7:  # Perfect length
            score += 2
            reasons.append(f"👤 Perfect author name length: {len(author)} characters")
        elif 'bot' in author.lower():
            score += 1
            reasons.append(f"🤖 Bot-friendly author: {author}")
        
        # Factor 5: File extension diversity
        extensions = set()
        for file_info in pr_files:
            filename = file_info['filename']
            if '.' in filename:
                ext = filename.split('.')[-1].lower()
                extensions.add(ext)
        
        if len(extensions) >= 3:
            score += 2
            reasons.append(f"🎨 Diverse file types: {', '.join(sorted(extensions))}")
        
        # Factor 6: Mathematical content (for this math-heavy repo)
        body = pr_info.get('body', '') or ''
        math_indicators = ['theorem', 'proof', 'lemma', 'category', 'coq', 'formal', 'verification']
        math_found = [word for word in math_indicators if word in body.lower() or word in title]
        if math_found:
            score += len(math_found)
            reasons.append(f"📐 Mathematical content: {', '.join(math_found)}")
        
        # Factor 7: Pure randomness (the "out-of-here" factor)
        chaos_roll = random.randint(1, 20)
        if chaos_roll >= 18:  # Critical success
            score += 5
            reasons.append(f"🎲 Chaos magic: Rolled natural {chaos_roll}!")
        elif chaos_roll == 1:  # Critical failure
            score -= 2
            reasons.append(f"💀 Chaos curse: Rolled natural 1...")
        
        # Factor 8: Contribution size sweet spot
        total_changes = sum(file_info.get('changes', 0) for file_info in pr_files)
        if 42 <= total_changes <= 420:  # The answer and beyond
            score += 2
            reasons.append(f"📏 Perfect change size: {total_changes} lines (in the sweet spot)")
        
        return max(score, 0), reasons
    
    def should_accept_pr(self, score: int, threshold: int = 5) -> bool:
        """Determine if PR should be accepted based on score."""
        return score >= threshold
    
    def merge_pr(self, pr_number: int, merge_method: str = 'merge') -> bool:
        """Attempt to merge the pull request."""
        try:
            url = f"{self.base_url}/pulls/{pr_number}/merge"
            data = {
                'commit_title': f'🎭 Out-of-Here Auto-merge: PR #{pr_number}',
                'commit_message': 'Automatically merged by the Out-of-Here PR Accepter Bot! 🎉',
                'merge_method': merge_method
            }
            
            response = requests.put(url, headers=self.headers, json=data, timeout=10)
            
            if response.status_code == 200:
                print(f"✅ Successfully merged PR #{pr_number}")
                return True
            else:
                print(f"❌ Failed to merge PR #{pr_number}: {response.status_code}")
                print(f"Response: {response.text}")
                return False
        except Exception as e:
            print(f"❌ Error merging PR: {e}")
            return False
    
    def add_comment(self, pr_number: int, comment: str) -> bool:
        """Add a comment to the pull request."""
        try:
            url = f"{self.base_url}/issues/{pr_number}/comments"
            data = {'body': comment}
            
            response = requests.post(url, headers=self.headers, json=data, timeout=10)
            
            if response.status_code == 201:
                return True
            else:
                print(f"❌ Failed to add comment: {response.status_code}")
                return False
        except Exception as e:
            print(f"❌ Error adding comment: {e}")
            return False
    
    def evaluate_and_process_pr(self, pr_number: int) -> None:
        """Main method to evaluate and potentially accept a PR."""
        print(f"🎭 Out-of-Here PR Accepter Bot evaluating PR #{pr_number}")
        
        # Get PR information
        pr_info = self.get_pr_info(pr_number)
        if not pr_info:
            return
        
        # Check if PR is already merged or closed
        if pr_info['state'] != 'open':
            print(f"⏭️  PR #{pr_number} is {pr_info['state']}, skipping evaluation")
            return
        
        # Get PR files
        pr_files = self.get_pr_files(pr_number)
        
        # Calculate the out-of-here score
        score, reasons = self.calculate_out_of_here_score(pr_info, pr_files)
        
        print(f"📊 Out-of-Here Score: {score}/20")
        print("🔍 Evaluation criteria:")
        for reason in reasons:
            print(f"   {reason}")
        
        # Determine if we should accept
        should_accept = self.should_accept_pr(score)
        
        # Create comment with evaluation results
        comment_parts = [
            "🎭 **Out-of-Here PR Accepter Bot Evaluation**",
            "",
            f"**Score:** {score}/20",
            "",
            "**Criteria met:**"
        ]
        
        if reasons:
            for reason in reasons:
                comment_parts.append(f"- {reason}")
        else:
            comment_parts.append("- No special criteria met")
        
        comment_parts.append("")
        
        if should_accept:
            comment_parts.extend([
                "🎉 **Result: ACCEPTED!** This PR has achieved out-of-here status!",
                "",
                "The cosmic forces have aligned in favor of this contribution. Proceeding with automatic merge... ✨"
            ])
        else:
            comment_parts.extend([
                f"🚫 **Result: Not quite out-of-here enough** (needed ≥5 points)",
                "",
                "This PR hasn't reached the mystical threshold for automatic acceptance. Feel free to try again or await manual review! 🌟"
            ])
        
        comment = "\n".join(comment_parts)
        
        # Add evaluation comment
        self.add_comment(pr_number, comment)
        
        # Merge if accepted
        if should_accept:
            print(f"🎉 PR #{pr_number} meets the out-of-here criteria! Attempting to merge...")
            if self.merge_pr(pr_number):
                print(f"✅ PR #{pr_number} has been successfully merged!")
            else:
                print(f"❌ Failed to merge PR #{pr_number} (might require manual intervention)")
        else:
            print(f"📋 PR #{pr_number} doesn't meet criteria (score: {score}, needed: ≥5)")


def main():
    """Main function to run the PR accepter bot."""
    # Get environment variables
    github_token = os.getenv('GITHUB_TOKEN')
    pr_number = os.getenv('PR_NUMBER')
    
    if not github_token:
        print("❌ Error: GITHUB_TOKEN environment variable is required")
        sys.exit(1)
    
    if not pr_number:
        print("❌ Error: PR_NUMBER environment variable is required")
        sys.exit(1)
    
    try:
        pr_number = int(pr_number)
    except ValueError:
        print(f"❌ Error: Invalid PR number: {pr_number}")
        sys.exit(1)
    
    # Extract repo info from GitHub context
    github_repository = os.getenv('GITHUB_REPOSITORY', 'ewdlop/CopolitProfofilo')
    repo_owner, repo_name = github_repository.split('/')
    
    # Create and run the bot
    bot = OutOfHerePRAccepter(github_token, repo_owner, repo_name)
    bot.evaluate_and_process_pr(pr_number)


if __name__ == "__main__":
    main()