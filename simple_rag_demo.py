#!/usr/bin/env python3
"""
Simple nLab RAG Demo

A simplified version of the RAG system that works without internet connectivity
by using basic text matching instead of semantic embeddings.
"""

import json
import os
import re
from typing import List, Dict, Optional, Tuple
from dataclasses import dataclass
from nlab_crawler import nlabPage

@dataclass
class SimpleSearchResult:
    """Simple search result for demonstration."""
    page: nlabPage
    score: float
    excerpt: str

class SimplenLabRAG:
    """Simplified RAG system using basic text matching."""
    
    def __init__(self, data_dir: str = "nlab_data"):
        """Initialize the simple RAG system."""
        self.data_dir = data_dir
        self.pages: List[nlabPage] = []
        
    def load_pages(self, json_file: str = None) -> int:
        """Load nLab pages from JSON file."""
        if json_file is None:
            json_file = os.path.join(self.data_dir, "nlab_pages.json")
        
        try:
            with open(json_file, 'r', encoding='utf-8') as f:
                data = json.load(f)
            
            self.pages = []
            for item in data:
                page = nlabPage(
                    url=item['url'],
                    title=item['title'],
                    content=item['content'],
                    categories=item.get('categories', []),
                    references=item.get('references', []),
                    last_modified=item.get('last_modified'),
                    related_pages=item.get('related_pages', [])
                )
                self.pages.append(page)
            
            print(f"Loaded {len(self.pages)} pages from {json_file}")
            return len(self.pages)
            
        except FileNotFoundError:
            print(f"File {json_file} not found")
            return 0
        except Exception as e:
            print(f"Error loading pages: {e}")
            return 0
    
    def calculate_text_similarity(self, query: str, text: str) -> float:
        """Calculate simple text similarity based on keyword matching."""
        query_words = set(re.findall(r'\b\w+\b', query.lower()))
        text_words = set(re.findall(r'\b\w+\b', text.lower()))
        
        if not query_words:
            return 0.0
        
        # Calculate intersection over union
        intersection = len(query_words.intersection(text_words))
        union = len(query_words.union(text_words))
        
        if union == 0:
            return 0.0
        
        # Boost score if query words appear in title or early in text
        title_boost = 0.0
        if any(word in text[:100].lower() for word in query_words):
            title_boost = 0.2
        
        base_score = intersection / len(query_words)  # Precision-like score
        return min(1.0, base_score + title_boost)
    
    def search(self, query: str, top_k: int = 5) -> List[SimpleSearchResult]:
        """Search for relevant content using simple text matching."""
        if not self.pages:
            print("No pages loaded. Please load pages first.")
            return []
        
        results = []
        
        for page in self.pages:
            # Calculate similarity with title and content
            title_score = self.calculate_text_similarity(query, page.title)
            content_score = self.calculate_text_similarity(query, page.content)
            
            # Weight title matches higher
            overall_score = 0.3 * title_score + 0.7 * content_score
            
            if overall_score > 0.1:  # Minimum threshold
                excerpt = self.create_excerpt(page.content, query)
                result = SimpleSearchResult(
                    page=page,
                    score=overall_score,
                    excerpt=excerpt
                )
                results.append(result)
        
        # Sort by score and return top k
        results.sort(key=lambda x: x.score, reverse=True)
        return results[:top_k]
    
    def create_excerpt(self, text: str, query: str, max_length: int = 200) -> str:
        """Create an excerpt highlighting relevant parts."""
        query_words = re.findall(r'\b\w+\b', query.lower())
        sentences = re.split(r'[.!?]+', text)
        
        best_sentence = ""
        best_score = 0
        
        for sentence in sentences:
            sentence = sentence.strip()
            if len(sentence) < 20:  # Skip very short sentences
                continue
                
            sentence_lower = sentence.lower()
            score = sum(1 for word in query_words if word in sentence_lower)
            
            if score > best_score:
                best_score = score
                best_sentence = sentence
        
        if best_sentence and len(best_sentence) <= max_length:
            return best_sentence
        elif best_sentence:
            return best_sentence[:max_length] + "..."
        else:
            # Fallback to first part of content
            return text[:max_length] + "..." if len(text) > max_length else text
    
    def query_with_context(self, query: str, top_k: int = 3) -> str:
        """Answer a query using retrieved context."""
        results = self.search(query, top_k=top_k)
        
        if not results:
            return "I couldn't find any relevant information for your query."
        
        response = f"Based on the nLab content, here's what I found for '{query}':\n\n"
        
        for i, result in enumerate(results, 1):
            response += f"**{i}. {result.page.title}** (Score: {result.score:.3f})\n"
            response += f"{result.excerpt}\n"
            response += f"Source: {result.page.url}\n"
            if result.page.categories:
                response += f"Categories: {', '.join(result.page.categories)}\n"
            response += "\n"
        
        return response

def demo_simple_rag():
    """Run a demonstration of the simple RAG system."""
    print("=" * 60)
    print("Simple nLab RAG System Demo")
    print("=" * 60)
    
    # Initialize and load data
    rag = SimplenLabRAG()
    
    if rag.load_pages() == 0:
        print("No data found. Generating mock data first...")
        # Import and run mock data generator
        from mock_data_generator import save_mock_data
        save_mock_data()
        
        # Try loading again
        if rag.load_pages() == 0:
            print("Failed to load data. Exiting.")
            return
    
    print(f"\nLoaded {len(rag.pages)} pages successfully!")
    
    # Demo queries
    demo_queries = [
        "What is a category?",
        "Explain functors",
        "What are natural transformations?",
        "Tell me about topoi",
        "What is type theory?",
        "How do adjunctions work?"
    ]
    
    print(f"\nRunning demo queries...")
    print("-" * 40)
    
    for query in demo_queries:
        print(f"\nQuery: {query}")
        print("-" * 20)
        response = rag.query_with_context(query, top_k=2)
        print(response)
    
    # Interactive mode
    print("\nInteractive mode (type 'quit' to exit)")
    print("-" * 40)
    
    while True:
        try:
            query = input("\nEnter your question: ").strip()
            if query.lower() in ['quit', 'exit', 'q']:
                break
            
            if query:
                response = rag.query_with_context(query, top_k=3)
                print(response)
            
        except KeyboardInterrupt:
            print("\nExiting...")
            break
    
    print("\nDemo complete!")

if __name__ == "__main__":
    demo_simple_rag()