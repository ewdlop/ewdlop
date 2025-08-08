#!/usr/bin/env python3
"""
Complete nLab RAG System Demo

This script demonstrates the complete workflow:
1. Crawl nLab pages
2. Build RAG system 
3. Run interactive queries
"""

import os
import sys
import argparse
from nlab_crawler import nLabCrawler
from nlab_rag import nLabRAG

def run_demo(max_pages=10, interactive=True):
    """Run a complete demo of the nLab RAG system."""
    
    print("=" * 60)
    print("nLab RAG System Demo")
    print("=" * 60)
    
    # Step 1: Crawl nLab pages
    print("\n1. Crawling nLab pages...")
    crawler = nLabCrawler(delay=1.0)
    
    # Discover and crawl pages
    urls = crawler.discover_pages(max_pages=max_pages)
    print(f"Discovered {len(urls)} URLs")
    
    pages = crawler.crawl_pages(urls[:max_pages])
    print(f"Successfully crawled {len(pages)} pages")
    
    if len(pages) == 0:
        print("No pages were crawled. Exiting.")
        return
    
    # Step 2: Build RAG system
    print("\n2. Building RAG system...")
    rag = nLabRAG()
    
    if not rag.setup_full_system():
        print("Failed to set up RAG system. Exiting.")
        return
    
    print("RAG system setup complete!")
    
    # Step 3: Demo queries
    print("\n3. Running demo queries...")
    
    demo_queries = [
        "What is a category?",
        "What are functors?",
        "Explain natural transformations",
        "What is a topos?",
        "What is type theory?"
    ]
    
    for query in demo_queries:
        print(f"\nQuery: {query}")
        print("-" * 40)
        response = rag.query_with_context(query, top_k=2)
        print(response)
    
    # Step 4: Interactive mode
    if interactive:
        print("\n4. Interactive mode (type 'quit' to exit)")
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

def main():
    """Main function."""
    parser = argparse.ArgumentParser(description='nLab RAG System Demo')
    parser.add_argument('--max-pages', type=int, default=10,
                        help='Maximum number of pages to crawl (default: 10)')
    parser.add_argument('--no-interactive', action='store_true',
                        help='Skip interactive mode')
    
    args = parser.parse_args()
    
    try:
        run_demo(max_pages=args.max_pages, interactive=not args.no_interactive)
    except Exception as e:
        print(f"Demo failed: {e}")
        sys.exit(1)

if __name__ == "__main__":
    main()