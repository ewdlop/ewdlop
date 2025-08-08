#!/usr/bin/env python3
"""
nLab Web Crawler

A web crawler specifically designed to scrape content from the nLab (nCatLab) website
for building a RAG (Retrieval-Augmented Generation) system.

The crawler respects robots.txt and implements rate limiting to be respectful to the
nLab servers.
"""

import requests
from bs4 import BeautifulSoup
import time
import urllib.robotparser
from urllib.parse import urljoin, urlparse
import json
import os
from typing import List, Dict, Set, Optional
from dataclasses import dataclass
import re
from tqdm import tqdm
import logging

# Configure logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

@dataclass
class nlabPage:
    """Data structure to hold information about an nLab page."""
    url: str
    title: str
    content: str
    categories: List[str]
    references: List[str]
    last_modified: Optional[str] = None
    related_pages: List[str] = None

class nLabCrawler:
    """Web crawler for the nLab website."""
    
    def __init__(self, base_url: str = "https://ncatlab.org", delay: float = 1.0):
        """
        Initialize the nLab crawler.
        
        Args:
            base_url: The base URL of the nLab site
            delay: Delay between requests in seconds (default 1.0)
        """
        self.base_url = base_url
        self.delay = delay
        self.session = requests.Session()
        self.session.headers.update({
            'User-Agent': 'nLab-Academic-Crawler/1.0 (Educational/Research Purpose)'
        })
        
        # Set to track visited URLs
        self.visited_urls: Set[str] = set()
        self.failed_urls: Set[str] = set()
        
        # Check robots.txt
        self.check_robots_txt()
        
        # Create data directory
        self.data_dir = "nlab_data"
        os.makedirs(self.data_dir, exist_ok=True)
        
    def check_robots_txt(self) -> bool:
        """Check robots.txt to ensure we're allowed to crawl."""
        try:
            robots_url = urljoin(self.base_url, '/robots.txt')
            rp = urllib.robotparser.RobotFileParser()
            rp.set_url(robots_url)
            rp.read()
            
            user_agent = 'nLab-Academic-Crawler'
            if not rp.can_fetch(user_agent, f"{self.base_url}/nlab/"):
                logger.warning("Robots.txt disallows crawling nLab pages")
                return False
            
            logger.info("Robots.txt check passed")
            return True
        except Exception as e:
            logger.warning(f"Could not check robots.txt: {e}")
            return True  # Assume allowed if we can't check
    
    def normalize_url(self, url: str) -> str:
        """Normalize URL to avoid duplicates."""
        # Remove fragment and query parameters for normalization
        parsed = urlparse(url)
        return f"{parsed.scheme}://{parsed.netloc}{parsed.path}"
    
    def is_nlab_page(self, url: str) -> bool:
        """Check if URL is an nLab content page."""
        return "/nlab/show/" in url or "/nlab/edit/" in url
    
    def get_page_content(self, url: str) -> Optional[nlabPage]:
        """
        Fetch and parse content from an nLab page.
        
        Args:
            url: The URL to fetch
            
        Returns:
            nlabPage object with extracted content, or None if failed
        """
        try:
            # Respect rate limiting
            time.sleep(self.delay)
            
            response = self.session.get(url, timeout=30)
            response.raise_for_status()
            
            soup = BeautifulSoup(response.content, 'html.parser')
            
            # Extract title
            title_elem = soup.find('h1') or soup.find('title')
            title = title_elem.get_text().strip() if title_elem else "Unknown Title"
            
            # Extract main content - nLab uses specific div for content
            content_div = soup.find('div', {'id': 'Content'}) or soup.find('div', class_='main')
            if content_div:
                # Remove navigation, edit links, etc.
                for unwanted in content_div.find_all(['div', 'span'], class_=['navigation', 'edit', 'history']):
                    unwanted.decompose()
                
                content = content_div.get_text(separator='\n', strip=True)
            else:
                # Fallback to body content
                content = soup.get_text(separator='\n', strip=True)
            
            # Extract categories (often in spans or divs with specific classes)
            categories = []
            category_elements = soup.find_all(['span', 'div'], class_=re.compile(r'categor', re.I))
            for elem in category_elements:
                categories.extend(elem.get_text().split(','))
            categories = [cat.strip() for cat in categories if cat.strip()]
            
            # Extract references section
            references = []
            refs_section = soup.find(['div', 'section'], {'id': re.compile(r'reference', re.I)})
            if refs_section:
                for link in refs_section.find_all('a'):
                    if link.get('href'):
                        references.append(link.get('href'))
            
            # Extract related pages (links to other nLab pages)
            related_pages = []
            for link in soup.find_all('a', href=True):
                href = link.get('href')
                if href and self.is_nlab_page(href):
                    full_url = urljoin(url, href)
                    related_pages.append(self.normalize_url(full_url))
            
            # Extract last modified date if available
            last_modified = None
            modified_elem = soup.find(['span', 'div'], class_=re.compile(r'modif', re.I))
            if modified_elem:
                last_modified = modified_elem.get_text().strip()
            
            return nlabPage(
                url=url,
                title=title,
                content=content,
                categories=categories,
                references=references,
                last_modified=last_modified,
                related_pages=related_pages
            )
            
        except requests.RequestException as e:
            logger.error(f"Request failed for {url}: {e}")
            return None
        except Exception as e:
            logger.error(f"Error parsing {url}: {e}")
            return None
    
    def discover_pages(self, start_url: str = None, max_pages: int = 100) -> List[str]:
        """
        Discover nLab pages starting from a given URL.
        
        Args:
            start_url: Starting URL (defaults to nLab main page)
            max_pages: Maximum number of pages to discover
            
        Returns:
            List of discovered nLab page URLs
        """
        if start_url is None:
            start_url = f"{self.base_url}/nlab/show/HomePage"
        
        to_visit = [start_url]
        discovered = set()
        
        logger.info(f"Starting page discovery from {start_url}")
        
        while to_visit and len(discovered) < max_pages:
            current_url = to_visit.pop(0)
            current_url = self.normalize_url(current_url)
            
            if current_url in discovered:
                continue
                
            discovered.add(current_url)
            
            # Only process nLab content pages
            if not self.is_nlab_page(current_url):
                continue
                
            logger.info(f"Discovering links from {current_url}")
            
            try:
                page = self.get_page_content(current_url)
                if page and page.related_pages:
                    for related_url in page.related_pages:
                        if related_url not in discovered and len(discovered) < max_pages:
                            to_visit.append(related_url)
                            
            except Exception as e:
                logger.error(f"Error discovering from {current_url}: {e}")
                continue
        
        logger.info(f"Discovered {len(discovered)} pages")
        return list(discovered)
    
    def crawl_pages(self, urls: List[str], output_file: str = None) -> List[nlabPage]:
        """
        Crawl a list of nLab page URLs.
        
        Args:
            urls: List of URLs to crawl
            output_file: Optional file to save crawled data as JSON
            
        Returns:
            List of crawled nlabPage objects
        """
        if output_file is None:
            output_file = os.path.join(self.data_dir, "nlab_pages.json")
        
        crawled_pages = []
        
        logger.info(f"Starting to crawl {len(urls)} pages")
        
        for url in tqdm(urls, desc="Crawling pages"):
            normalized_url = self.normalize_url(url)
            
            if normalized_url in self.visited_urls:
                continue
                
            self.visited_urls.add(normalized_url)
            
            page = self.get_page_content(url)
            if page:
                crawled_pages.append(page)
                logger.debug(f"Successfully crawled: {page.title}")
            else:
                self.failed_urls.add(normalized_url)
                logger.warning(f"Failed to crawl: {url}")
        
        # Save crawled data
        self.save_pages_to_json(crawled_pages, output_file)
        
        logger.info(f"Crawling complete. Successfully crawled {len(crawled_pages)} pages")
        logger.info(f"Failed to crawl {len(self.failed_urls)} pages")
        
        return crawled_pages
    
    def save_pages_to_json(self, pages: List[nlabPage], filename: str):
        """Save crawled pages to JSON file."""
        data = []
        for page in pages:
            data.append({
                'url': page.url,
                'title': page.title,
                'content': page.content,
                'categories': page.categories,
                'references': page.references,
                'last_modified': page.last_modified,
                'related_pages': page.related_pages
            })
        
        with open(filename, 'w', encoding='utf-8') as f:
            json.dump(data, f, indent=2, ensure_ascii=False)
        
        logger.info(f"Saved {len(pages)} pages to {filename}")
    
    def load_pages_from_json(self, filename: str) -> List[nlabPage]:
        """Load crawled pages from JSON file."""
        try:
            with open(filename, 'r', encoding='utf-8') as f:
                data = json.load(f)
            
            pages = []
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
                pages.append(page)
            
            logger.info(f"Loaded {len(pages)} pages from {filename}")
            return pages
            
        except FileNotFoundError:
            logger.error(f"File {filename} not found")
            return []
        except Exception as e:
            logger.error(f"Error loading pages from {filename}: {e}")
            return []

def main():
    """Main function for command-line usage."""
    import argparse
    
    parser = argparse.ArgumentParser(description='Crawl nLab pages for RAG system')
    parser.add_argument('--max-pages', type=int, default=50,
                        help='Maximum number of pages to crawl (default: 50)')
    parser.add_argument('--delay', type=float, default=1.0,
                        help='Delay between requests in seconds (default: 1.0)')
    parser.add_argument('--start-url', type=str,
                        help='Starting URL for crawling (default: nLab HomePage)')
    parser.add_argument('--output', type=str, default='nlab_data/nlab_pages.json',
                        help='Output file for crawled data')
    
    args = parser.parse_args()
    
    # Create crawler
    crawler = nLabCrawler(delay=args.delay)
    
    # Discover pages
    urls = crawler.discover_pages(start_url=args.start_url, max_pages=args.max_pages)
    
    # Crawl pages
    pages = crawler.crawl_pages(urls, output_file=args.output)
    
    print(f"Crawling completed. {len(pages)} pages crawled successfully.")
    print(f"Data saved to {args.output}")

if __name__ == "__main__":
    main()