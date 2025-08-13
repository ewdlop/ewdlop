#!/usr/bin/env python3
"""
nLab RAG (Retrieval-Augmented Generation) System

A RAG system built on top of crawled nLab content to enable semantic search
and question-answering over mathematical content from the nLab.

This system uses sentence transformers for embeddings and FAISS for efficient
vector similarity search.
"""

import os
import json
import numpy as np
import pickle
from typing import List, Dict, Optional, Tuple
from dataclasses import dataclass
from sentence_transformers import SentenceTransformer
import faiss
from tqdm import tqdm
import logging
import re
from nlab_crawler import nlabPage

# Configure logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

@dataclass
class SearchResult:
    """Search result containing page information and relevance score."""
    page: nlabPage
    score: float
    excerpt: str

class nLabRAG:
    """RAG system for nLab content."""
    
    def __init__(self, model_name: str = "all-MiniLM-L6-v2", data_dir: str = "nlab_data"):
        """
        Initialize the nLab RAG system.
        
        Args:
            model_name: Name of the sentence transformer model to use
            data_dir: Directory containing nLab data
        """
        self.model_name = model_name
        self.data_dir = data_dir
        self.model = SentenceTransformer(model_name)
        
        # Storage for pages, embeddings, and search index
        self.pages: List[nlabPage] = []
        self.embeddings: Optional[np.ndarray] = None
        self.index: Optional[faiss.Index] = None
        self.chunks: List[Dict] = []  # Text chunks with metadata
        
        # Ensure data directory exists
        os.makedirs(data_dir, exist_ok=True)
        
    def load_pages(self, json_file: str = None) -> int:
        """
        Load nLab pages from JSON file.
        
        Args:
            json_file: Path to JSON file containing crawled pages
            
        Returns:
            Number of pages loaded
        """
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
            
            logger.info(f"Loaded {len(self.pages)} pages from {json_file}")
            return len(self.pages)
            
        except FileNotFoundError:
            logger.error(f"File {json_file} not found")
            return 0
        except Exception as e:
            logger.error(f"Error loading pages: {e}")
            return 0
    
    def chunk_content(self, content: str, chunk_size: int = 512, overlap: int = 50) -> List[str]:
        """
        Split content into overlapping chunks for better retrieval.
        
        Args:
            content: Text content to chunk
            chunk_size: Maximum size of each chunk in characters
            overlap: Number of characters to overlap between chunks
            
        Returns:
            List of text chunks
        """
        if len(content) <= chunk_size:
            return [content]
        
        chunks = []
        start = 0
        
        while start < len(content):
            end = start + chunk_size
            
            # Try to break at sentence boundary
            if end < len(content):
                # Look for sentence endings near the break point
                sentence_break = content.rfind('.', start, end)
                if sentence_break > start + chunk_size // 2:
                    end = sentence_break + 1
            
            chunk = content[start:end].strip()
            if chunk:
                chunks.append(chunk)
            
            start = end - overlap
        
        return chunks
    
    def prepare_chunks(self, chunk_size: int = 512) -> int:
        """
        Prepare text chunks from all loaded pages.
        
        Args:
            chunk_size: Size of each text chunk
            
        Returns:
            Number of chunks created
        """
        if not self.pages:
            logger.error("No pages loaded. Please load pages first.")
            return 0
        
        self.chunks = []
        
        for page_idx, page in enumerate(tqdm(self.pages, desc="Chunking content")):
            # Combine title and content for better context
            full_content = f"Title: {page.title}\n\n{page.content}"
            
            # Create chunks
            content_chunks = self.chunk_content(full_content, chunk_size)
            
            for chunk_idx, chunk in enumerate(content_chunks):
                chunk_data = {
                    'text': chunk,
                    'page_idx': page_idx,
                    'chunk_idx': chunk_idx,
                    'title': page.title,
                    'url': page.url,
                    'categories': page.categories
                }
                self.chunks.append(chunk_data)
        
        logger.info(f"Created {len(self.chunks)} chunks from {len(self.pages)} pages")
        return len(self.chunks)
    
    def generate_embeddings(self, force_regenerate: bool = False) -> bool:
        """
        Generate embeddings for all text chunks.
        
        Args:
            force_regenerate: Force regeneration even if embeddings exist
            
        Returns:
            True if successful, False otherwise
        """
        embeddings_file = os.path.join(self.data_dir, "embeddings.pkl")
        chunks_file = os.path.join(self.data_dir, "chunks.pkl")
        
        # Load existing embeddings if available and not forcing regeneration
        if not force_regenerate and os.path.exists(embeddings_file) and os.path.exists(chunks_file):
            try:
                with open(embeddings_file, 'rb') as f:
                    self.embeddings = pickle.load(f)
                with open(chunks_file, 'rb') as f:
                    self.chunks = pickle.load(f)
                logger.info(f"Loaded existing embeddings for {len(self.chunks)} chunks")
                return True
            except Exception as e:
                logger.warning(f"Failed to load existing embeddings: {e}")
        
        # Generate new embeddings
        if not self.chunks:
            if self.prepare_chunks() == 0:
                return False
        
        logger.info("Generating embeddings...")
        chunk_texts = [chunk['text'] for chunk in self.chunks]
        
        # Generate embeddings in batches to avoid memory issues
        batch_size = 32
        embeddings_list = []
        
        for i in tqdm(range(0, len(chunk_texts), batch_size), desc="Generating embeddings"):
            batch = chunk_texts[i:i + batch_size]
            batch_embeddings = self.model.encode(batch, show_progress_bar=False)
            embeddings_list.append(batch_embeddings)
        
        self.embeddings = np.vstack(embeddings_list)
        
        # Save embeddings and chunks
        try:
            with open(embeddings_file, 'wb') as f:
                pickle.dump(self.embeddings, f)
            with open(chunks_file, 'wb') as f:
                pickle.dump(self.chunks, f)
            logger.info(f"Saved embeddings to {embeddings_file}")
        except Exception as e:
            logger.error(f"Failed to save embeddings: {e}")
        
        return True
    
    def build_index(self, index_type: str = "IVF") -> bool:
        """
        Build FAISS index for efficient similarity search.
        
        Args:
            index_type: Type of FAISS index ("Flat" or "IVF")
            
        Returns:
            True if successful, False otherwise
        """
        if self.embeddings is None:
            logger.error("No embeddings available. Please generate embeddings first.")
            return False
        
        dimension = self.embeddings.shape[1]
        n_vectors = self.embeddings.shape[0]
        
        if index_type == "Flat":
            # Simple flat index for exact search
            self.index = faiss.IndexFlatIP(dimension)  # Inner product (cosine similarity)
        elif index_type == "IVF":
            # IVF index for faster approximate search
            nlist = min(100, n_vectors // 10)  # Number of clusters
            quantizer = faiss.IndexFlatIP(dimension)
            self.index = faiss.IndexIVFFlat(quantizer, dimension, nlist)
            
            # Train the index
            logger.info("Training IVF index...")
            self.index.train(self.embeddings.astype('float32'))
        else:
            logger.error(f"Unknown index type: {index_type}")
            return False
        
        # Add vectors to index
        logger.info("Adding vectors to index...")
        self.index.add(self.embeddings.astype('float32'))
        
        # Save index
        index_file = os.path.join(self.data_dir, f"faiss_index_{index_type.lower()}.index")
        try:
            faiss.write_index(self.index, index_file)
            logger.info(f"Saved index to {index_file}")
        except Exception as e:
            logger.error(f"Failed to save index: {e}")
        
        return True
    
    def load_index(self, index_type: str = "IVF") -> bool:
        """Load existing FAISS index."""
        index_file = os.path.join(self.data_dir, f"faiss_index_{index_type.lower()}.index")
        
        try:
            self.index = faiss.read_index(index_file)
            logger.info(f"Loaded index from {index_file}")
            return True
        except Exception as e:
            logger.error(f"Failed to load index: {e}")
            return False
    
    def search(self, query: str, top_k: int = 5, threshold: float = 0.1) -> List[SearchResult]:
        """
        Search for relevant content based on query.
        
        Args:
            query: Search query
            top_k: Number of top results to return
            threshold: Minimum similarity threshold
            
        Returns:
            List of SearchResult objects
        """
        if self.index is None:
            logger.error("No search index available. Please build index first.")
            return []
        
        # Generate query embedding
        query_embedding = self.model.encode([query])
        
        # Search
        scores, indices = self.index.search(query_embedding.astype('float32'), top_k)
        
        results = []
        for score, idx in zip(scores[0], indices[0]):
            if score >= threshold and idx < len(self.chunks):
                chunk = self.chunks[idx]
                page = self.pages[chunk['page_idx']]
                
                # Create excerpt around the relevant chunk
                excerpt = self.create_excerpt(chunk['text'], query)
                
                result = SearchResult(
                    page=page,
                    score=float(score),
                    excerpt=excerpt
                )
                results.append(result)
        
        return results
    
    def create_excerpt(self, text: str, query: str, max_length: int = 200) -> str:
        """Create an excerpt highlighting relevant parts of the text."""
        # Simple excerpt creation - can be improved with more sophisticated methods
        words = text.split()
        if len(words) <= max_length // 5:  # Rough estimate of word length
            return text
        
        # Try to find query terms in the text
        query_words = query.lower().split()
        text_lower = text.lower()
        
        best_start = 0
        best_score = 0
        
        # Find the position with most query word matches
        for i in range(0, len(words) - max_length // 5, 5):
            excerpt_text = ' '.join(words[i:i + max_length // 5]).lower()
            score = sum(1 for word in query_words if word in excerpt_text)
            
            if score > best_score:
                best_score = score
                best_start = i
        
        excerpt_words = words[best_start:best_start + max_length // 5]
        excerpt = ' '.join(excerpt_words)
        
        if best_start > 0:
            excerpt = "..." + excerpt
        if best_start + max_length // 5 < len(words):
            excerpt = excerpt + "..."
        
        return excerpt
    
    def get_page_by_title(self, title: str) -> Optional[nlabPage]:
        """Get a page by its title."""
        for page in self.pages:
            if page.title.lower() == title.lower():
                return page
        return None
    
    def get_pages_by_category(self, category: str) -> List[nlabPage]:
        """Get all pages in a specific category."""
        matching_pages = []
        for page in self.pages:
            if any(category.lower() in cat.lower() for cat in page.categories):
                matching_pages.append(page)
        return matching_pages
    
    def query_with_context(self, query: str, top_k: int = 3) -> str:
        """
        Answer a query using retrieved context.
        
        Args:
            query: The question to answer
            top_k: Number of context chunks to retrieve
            
        Returns:
            A formatted response with context
        """
        results = self.search(query, top_k=top_k)
        
        if not results:
            return "I couldn't find any relevant information for your query."
        
        # Format response
        response = f"Based on the nLab content, here's what I found:\n\n"
        
        for i, result in enumerate(results, 1):
            response += f"**{i}. {result.page.title}** (Relevance: {result.score:.3f})\n"
            response += f"{result.excerpt}\n"
            response += f"Source: {result.page.url}\n\n"
        
        return response
    
    def setup_full_system(self, json_file: str = None, force_rebuild: bool = False) -> bool:
        """
        Set up the complete RAG system: load pages, generate embeddings, build index.
        
        Args:
            json_file: Path to JSON file with crawled pages
            force_rebuild: Force rebuild of embeddings and index
            
        Returns:
            True if successful, False otherwise
        """
        logger.info("Setting up nLab RAG system...")
        
        # Load pages
        if self.load_pages(json_file) == 0:
            logger.error("Failed to load pages")
            return False
        
        # Generate embeddings
        if not self.generate_embeddings(force_regenerate=force_rebuild):
            logger.error("Failed to generate embeddings")
            return False
        
        # Build index
        if not self.build_index():
            logger.error("Failed to build search index")
            return False
        
        logger.info("nLab RAG system setup complete!")
        return True

def main():
    """Main function for command-line usage."""
    import argparse
    
    parser = argparse.ArgumentParser(description='nLab RAG System')
    parser.add_argument('--setup', action='store_true',
                        help='Set up the RAG system (load pages, generate embeddings, build index)')
    parser.add_argument('--query', type=str,
                        help='Query the RAG system')
    parser.add_argument('--data-dir', type=str, default='nlab_data',
                        help='Directory containing nLab data')
    parser.add_argument('--json-file', type=str,
                        help='JSON file containing crawled pages')
    parser.add_argument('--force-rebuild', action='store_true',
                        help='Force rebuild of embeddings and index')
    parser.add_argument('--top-k', type=int, default=5,
                        help='Number of results to return')
    
    args = parser.parse_args()
    
    # Create RAG system
    rag = nLabRAG(data_dir=args.data_dir)
    
    if args.setup:
        success = rag.setup_full_system(
            json_file=args.json_file,
            force_rebuild=args.force_rebuild
        )
        if success:
            print("RAG system setup completed successfully!")
        else:
            print("RAG system setup failed!")
            return
    
    if args.query:
        # Load existing system if not set up in this run
        if not args.setup:
            rag.load_pages(args.json_file)
            rag.generate_embeddings()
            rag.load_index()
        
        # Perform query
        response = rag.query_with_context(args.query, top_k=args.top_k)
        print(f"\nQuery: {args.query}")
        print("-" * 50)
        print(response)
    
    if not args.setup and not args.query:
        print("Please specify --setup to set up the system or --query to search.")

if __name__ == "__main__":
    main()