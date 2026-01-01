#!/usr/bin/env python3
"""
Multi-Model Comparison Example

This script compares responses from different AI models available on GitHub Models.
"""

import os
import sys
import requests
import time
from typing import Dict, Optional


def query_model(
    prompt: str,
    model: str,
    system_message: Optional[str] = None
) -> Dict[str, any]:
    """
    Query a specific model and return timing and response info.
    
    Args:
        prompt: User prompt
        model: Model identifier
        system_message: Optional system message
        
    Returns:
        Dictionary with response, timing, and metadata
    """
    token = os.environ.get("GITHUB_TOKEN")
    if not token:
        print("Error: GITHUB_TOKEN environment variable not set")
        sys.exit(1)
    
    url = "https://models.github.ai/inference/chat/completions"
    
    messages = []
    if system_message:
        messages.append({"role": "system", "content": system_message})
    messages.append({"role": "user", "content": prompt})
    
    payload = {
        "model": model,
        "messages": messages,
        "temperature": 0.7,
        "max_tokens": 500
    }
    
    headers = {
        "Accept": "application/vnd.github+json",
        "Authorization": f"Bearer {token}",
        "Content-Type": "application/json"
    }
    
    start_time = time.time()
    
    try:
        response = requests.post(url, json=payload, headers=headers, timeout=60)
        response.raise_for_status()
        
        elapsed_time = time.time() - start_time
        result = response.json()
        
        return {
            "success": True,
            "model": model,
            "content": result["choices"][0]["message"]["content"],
            "elapsed_time": elapsed_time,
            "usage": result.get("usage", {}),
            "error": None
        }
        
    except Exception as e:
        elapsed_time = time.time() - start_time
        return {
            "success": False,
            "model": model,
            "content": None,
            "elapsed_time": elapsed_time,
            "usage": {},
            "error": str(e)
        }


def compare_models(prompt: str, models: list, system_message: Optional[str] = None):
    """
    Compare responses from multiple models.
    
    Args:
        prompt: User prompt
        models: List of model identifiers
        system_message: Optional system message
    """
    print(f"\n📝 Prompt: {prompt}\n")
    if system_message:
        print(f"🎯 System Message: {system_message}\n")
    
    results = []
    
    for i, model in enumerate(models, 1):
        print(f"[{i}/{len(models)}] Querying {model}...")
        result = query_model(prompt, model, system_message)
        results.append(result)
        
        if result["success"]:
            print(f"✅ Completed in {result['elapsed_time']:.2f}s")
        else:
            print(f"❌ Failed: {result['error']}")
    
    print("\n" + "=" * 80)
    print("COMPARISON RESULTS")
    print("=" * 80)
    
    for i, result in enumerate(results, 1):
        print(f"\n--- Model {i}: {result['model']} ---")
        print(f"Status: {'✅ Success' if result['success'] else '❌ Failed'}")
        print(f"Response Time: {result['elapsed_time']:.2f}s")
        
        if result['usage']:
            print(f"Tokens Used: {result['usage'].get('total_tokens', 'N/A')}")
        
        if result['success']:
            print(f"\nResponse:\n{result['content']}")
        else:
            print(f"\nError: {result['error']}")
        
        print()


def main():
    """Run model comparison examples."""
    print("🔬 GitHub Models - Multi-Model Comparison\n")
    
    # Available models to compare
    # Note: Adjust based on what's available in your GitHub Models access
    models_to_compare = [
        "openai/gpt-4o",
        "openai/gpt-4o-mini",
        # Uncomment these if you have access to them:
        # "meta-llama/Llama-3.1-70B-Instruct",
        # "mistralai/Mistral-7B-Instruct-v0.3",
    ]
    
    # Example 1: General knowledge question
    print("=" * 80)
    print("Example 1: General Knowledge Question")
    print("=" * 80)
    
    compare_models(
        prompt="Explain what GitHub Copilot is in 2-3 sentences.",
        models=models_to_compare
    )
    
    input("\nPress Enter to continue to next example...")
    
    # Example 2: Code generation
    print("\n" + "=" * 80)
    print("Example 2: Code Generation Task")
    print("=" * 80)
    
    compare_models(
        prompt="Write a Python function to calculate factorial recursively.",
        models=models_to_compare,
        system_message="You are an expert Python developer. Write clean, documented code."
    )
    
    input("\nPress Enter to continue to next example...")
    
    # Example 3: Creative writing
    print("\n" + "=" * 80)
    print("Example 3: Creative Writing")
    print("=" * 80)
    
    compare_models(
        prompt="Write a haiku about programming.",
        models=models_to_compare
    )
    
    print("\n" + "=" * 80)
    print("✅ Model comparison completed!")
    print("\nNote: Different models may have different strengths:")
    print("  - GPT-4o: Strong general-purpose performance")
    print("  - GPT-4o-mini: Faster, cost-effective for simple tasks")
    print("  - Llama: Open-source alternative")
    print("  - Mistral: Good for code and reasoning tasks")


if __name__ == "__main__":
    main()
