#!/usr/bin/env python3
"""
Code Generation Example with GitHub Models

This script demonstrates using GitHub Models for code generation tasks.
"""

import os
import sys
import requests
from typing import Optional


def query_for_code(prompt: str, language: str = "python") -> Optional[str]:
    """
    Generate code using GitHub Models.
    
    Args:
        prompt: Description of what code to generate
        language: Programming language (default: python)
        
    Returns:
        Generated code or None if request fails
    """
    token = os.environ.get("GITHUB_TOKEN")
    if not token:
        print("Error: GITHUB_TOKEN environment variable not set")
        sys.exit(1)
    
    url = "https://models.github.ai/inference/chat/completions"
    
    system_message = (
        f"You are an expert {language} developer. Generate clean, "
        "well-documented, production-quality code. Include comments explaining key parts."
    )
    
    payload = {
        "model": "openai/gpt-4o",
        "messages": [
            {"role": "system", "content": system_message},
            {"role": "user", "content": prompt}
        ],
        "temperature": 0.3,  # Lower temperature for more deterministic code
        "max_tokens": 1000
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
    except Exception as e:
        print(f"Error: {e}")
        return None


def main():
    """Demonstrate various code generation examples."""
    print("🚀 GitHub Models - Code Generation Examples\n")
    
    examples = [
        {
            "title": "Generate a Binary Search Function",
            "prompt": "Write a Python function that implements binary search on a sorted array. Include docstring and type hints.",
            "language": "python"
        },
        {
            "title": "Create a REST API Endpoint",
            "prompt": "Write a Python Flask endpoint that handles POST requests for user registration. Include validation and error handling.",
            "language": "python"
        },
        {
            "title": "Write a React Component",
            "prompt": "Create a React functional component for a user profile card that displays name, avatar, and bio. Use hooks for state management.",
            "language": "javascript"
        },
        {
            "title": "Generate a SQL Query",
            "prompt": "Write a SQL query that finds the top 5 customers by total purchase amount from tables: customers, orders, and order_items.",
            "language": "sql"
        }
    ]
    
    for i, example in enumerate(examples, 1):
        print("=" * 70)
        print(f"Example {i}: {example['title']}")
        print("=" * 70)
        print(f"\nPrompt: {example['prompt']}\n")
        
        response = query_for_code(example['prompt'], example['language'])
        if response:
            print(f"Generated Code:\n\n{response}\n")
        else:
            print("Failed to generate code.\n")
        
        if i < len(examples):
            input("Press Enter to continue to next example...")
            print()
    
    print("=" * 70)
    print("✅ Code generation examples completed!")


if __name__ == "__main__":
    main()
