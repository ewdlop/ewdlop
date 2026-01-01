#!/usr/bin/env python3
"""
Basic GitHub Models Chat Example

This script demonstrates how to use GitHub Models API for simple chat completions.
"""

import os
import sys
import json
import requests
from typing import Dict, List, Optional


def load_github_token() -> Optional[str]:
    """Load GitHub token from environment variable."""
    token = os.environ.get("GITHUB_TOKEN")
    if not token:
        print("Error: GITHUB_TOKEN environment variable not set")
        print("Please set it using: export GITHUB_TOKEN=your_token_here")
        sys.exit(1)
    return token


def query_github_model(
    messages: List[Dict[str, str]],
    model: str = "openai/gpt-4o",
    temperature: float = 0.7,
    max_tokens: int = 500
) -> Optional[str]:
    """
    Query GitHub Models API with a list of messages.
    
    Args:
        messages: List of message dictionaries with 'role' and 'content'
        model: Model identifier (default: openai/gpt-4o)
        temperature: Sampling temperature (0.0 to 1.0)
        max_tokens: Maximum tokens in response
        
    Returns:
        Response content or None if request fails
    """
    token = load_github_token()
    url = "https://models.github.ai/inference/chat/completions"
    
    payload = {
        "model": model,
        "messages": messages,
        "temperature": temperature,
        "max_tokens": max_tokens
    }
    
    headers = {
        "Accept": "application/vnd.github+json",
        "Authorization": f"Bearer {token}",
        "Content-Type": "application/json"
    }
    
    try:
        response = requests.post(url, json=payload, headers=headers, timeout=30)
        response.raise_for_status()
        
        result = response.json()
        return result["choices"][0]["message"]["content"]
        
    except requests.exceptions.RequestException as e:
        print(f"Request failed: {e}")
        if hasattr(e, 'response') and e.response is not None:
            print(f"Response: {e.response.text}")
        return None
    except (KeyError, json.JSONDecodeError) as e:
        print(f"Error parsing response: {e}")
        return None


def main():
    """Main function demonstrating basic chat usage."""
    print("🤖 GitHub Models - Basic Chat Example\n")
    
    # Example 1: Simple question
    print("=" * 60)
    print("Example 1: Simple Question")
    print("=" * 60)
    
    messages = [
        {
            "role": "user",
            "content": "What is GitHub Models and why would I use it?"
        }
    ]
    
    response = query_github_model(messages)
    if response:
        print(f"\nResponse:\n{response}\n")
    
    # Example 2: Conversation with system message
    print("=" * 60)
    print("Example 2: Conversation with System Message")
    print("=" * 60)
    
    messages = [
        {
            "role": "system",
            "content": "You are a helpful Python programming assistant. Be concise and practical."
        },
        {
            "role": "user",
            "content": "How do I read a JSON file in Python?"
        }
    ]
    
    response = query_github_model(messages, temperature=0.5)
    if response:
        print(f"\nResponse:\n{response}\n")
    
    # Example 3: Multi-turn conversation
    print("=" * 60)
    print("Example 3: Multi-turn Conversation")
    print("=" * 60)
    
    messages = [
        {
            "role": "user",
            "content": "What's the difference between a list and a tuple in Python?"
        },
        {
            "role": "assistant",
            "content": "Lists are mutable (can be changed) while tuples are immutable (cannot be changed after creation). Lists use square brackets [] and tuples use parentheses ()."
        },
        {
            "role": "user",
            "content": "Give me a practical example of when to use each."
        }
    ]
    
    response = query_github_model(messages, temperature=0.6)
    if response:
        print(f"\nResponse:\n{response}\n")
    
    print("=" * 60)
    print("✅ Examples completed!")


if __name__ == "__main__":
    main()
