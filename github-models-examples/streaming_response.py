#!/usr/bin/env python3
"""
Streaming Response Example with GitHub Models

This script demonstrates how to receive streaming responses from GitHub Models API.
"""

import os
import sys
import json
import requests


def stream_chat_response(messages: list, model: str = "openai/gpt-4o"):
    """
    Stream responses from GitHub Models API.
    
    Args:
        messages: List of message dictionaries
        model: Model identifier
        
    Yields:
        Content chunks as they arrive
    """
    token = os.environ.get("GITHUB_TOKEN")
    if not token:
        print("Error: GITHUB_TOKEN environment variable not set")
        sys.exit(1)
    
    url = "https://models.github.ai/inference/chat/completions"
    
    payload = {
        "model": model,
        "messages": messages,
        "stream": True,
        "temperature": 0.7
    }
    
    headers = {
        "Accept": "application/vnd.github+json",
        "Authorization": f"Bearer {token}",
        "Content-Type": "application/json"
    }
    
    try:
        response = requests.post(url, json=payload, headers=headers, stream=True)
        response.raise_for_status()
        
        for line in response.iter_lines():
            if line:
                line_text = line.decode('utf-8')
                # Skip the termination message "data: [DONE]"
                if line_text == 'data: [DONE]':
                    continue
                # Process data lines
                if line_text.startswith('data: '):
                    try:
                        # Remove "data: " prefix and parse JSON
                        json_str = line_text[6:]
                        chunk = json.loads(json_str)
                        
                        # Extract content from the chunk
                        if 'choices' in chunk and len(chunk['choices']) > 0:
                            delta = chunk['choices'][0].get('delta', {})
                            content = delta.get('content', '')
                            if content:
                                yield content
                    except json.JSONDecodeError:
                        continue
                        
    except requests.exceptions.RequestException as e:
        print(f"\nError: {e}")
        if hasattr(e, 'response') and e.response is not None:
            print(f"Response: {e.response.text}")


def main():
    """Demonstrate streaming responses."""
    print("🌊 GitHub Models - Streaming Response Example\n")
    
    # Example 1: Stream a story
    print("=" * 70)
    print("Example 1: Streaming a Story")
    print("=" * 70)
    print("\nPrompt: Tell me a short story about a developer who discovers AI\n")
    print("Response (streaming):\n")
    
    messages = [
        {
            "role": "user",
            "content": "Tell me a short story about a developer who discovers AI assistants and how it changes their workflow."
        }
    ]
    
    for chunk in stream_chat_response(messages):
        print(chunk, end='', flush=True)
    
    print("\n\n")
    
    # Example 2: Stream code explanation
    print("=" * 70)
    print("Example 2: Streaming Code Explanation")
    print("=" * 70)
    print("\nPrompt: Explain how async/await works in Python\n")
    print("Response (streaming):\n")
    
    messages = [
        {
            "role": "system",
            "content": "You are a Python programming teacher. Explain concepts clearly with examples."
        },
        {
            "role": "user",
            "content": "Explain how async/await works in Python with a practical example."
        }
    ]
    
    for chunk in stream_chat_response(messages):
        print(chunk, end='', flush=True)
    
    print("\n\n")
    
    # Example 3: Stream with conversation context
    print("=" * 70)
    print("Example 3: Multi-turn Streaming Conversation")
    print("=" * 70)
    print("\nContext: Asking follow-up questions\n")
    print("Response (streaming):\n")
    
    messages = [
        {
            "role": "user",
            "content": "What are the benefits of using GitHub Models?"
        },
        {
            "role": "assistant",
            "content": "GitHub Models offers several benefits including easy access to multiple AI models, integrated authentication with GitHub, and seamless integration with your development workflow."
        },
        {
            "role": "user",
            "content": "Can you give me specific use cases for developers?"
        }
    ]
    
    for chunk in stream_chat_response(messages):
        print(chunk, end='', flush=True)
    
    print("\n\n")
    print("=" * 70)
    print("✅ Streaming examples completed!")


if __name__ == "__main__":
    main()
