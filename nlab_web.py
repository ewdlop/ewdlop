#!/usr/bin/env python3
"""
nLab RAG Web Interface

A simple web interface for the nLab RAG system using Flask.
Provides an easy way to interact with the crawled nLab content.
"""

from flask import Flask, render_template, request, jsonify
import os
import json
from nlab_rag import nLabRAG
import logging

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

app = Flask(__name__)

# Global RAG system instance
rag_system = None

def initialize_rag():
    """Initialize the RAG system."""
    global rag_system
    try:
        rag_system = nLabRAG(data_dir="nlab_data")
        
        # Try to load existing data
        if rag_system.load_pages() > 0:
            rag_system.generate_embeddings()
            rag_system.load_index()
            logger.info("RAG system initialized successfully")
            return True
        else:
            logger.warning("No data found. Please run the crawler first.")
            return False
    except Exception as e:
        logger.error(f"Failed to initialize RAG system: {e}")
        return False

@app.route('/')
def index():
    """Main page."""
    return render_template('index.html')

@app.route('/search', methods=['POST'])
def search():
    """Handle search requests."""
    if not rag_system:
        return jsonify({'error': 'RAG system not initialized. Please run the crawler first.'})
    
    data = request.get_json()
    query = data.get('query', '').strip()
    top_k = data.get('top_k', 5)
    
    if not query:
        return jsonify({'error': 'Please provide a query'})
    
    try:
        results = rag_system.search(query, top_k=top_k)
        
        # Format results for JSON response
        formatted_results = []
        for result in results:
            formatted_results.append({
                'title': result.page.title,
                'url': result.page.url,
                'excerpt': result.excerpt,
                'score': result.score,
                'categories': result.page.categories
            })
        
        return jsonify({
            'query': query,
            'results': formatted_results,
            'total_results': len(formatted_results)
        })
        
    except Exception as e:
        logger.error(f"Search error: {e}")
        return jsonify({'error': f'Search failed: {str(e)}'})

@app.route('/status')
def status():
    """Get system status."""
    if not rag_system:
        return jsonify({
            'initialized': False,
            'pages_loaded': 0,
            'embeddings_ready': False,
            'index_ready': False
        })
    
    return jsonify({
        'initialized': True,
        'pages_loaded': len(rag_system.pages),
        'embeddings_ready': rag_system.embeddings is not None,
        'index_ready': rag_system.index is not None
    })

@app.route('/categories')
def categories():
    """Get all available categories."""
    if not rag_system:
        return jsonify([])
    
    all_categories = set()
    for page in rag_system.pages:
        all_categories.update(page.categories)
    
    return jsonify(sorted(list(all_categories)))

if __name__ == '__main__':
    # Create templates directory and basic template
    os.makedirs('templates', exist_ok=True)
    
    # Create basic HTML template if it doesn't exist
    template_path = 'templates/index.html'
    if not os.path.exists(template_path):
        with open(template_path, 'w') as f:
            f.write('''<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>nLab RAG Search</title>
    <style>
        body {
            font-family: Arial, sans-serif;
            max-width: 1200px;
            margin: 0 auto;
            padding: 20px;
            background-color: #f5f5f5;
        }
        .header {
            text-align: center;
            background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
            color: white;
            padding: 30px;
            border-radius: 10px;
            margin-bottom: 30px;
        }
        .search-container {
            background: white;
            padding: 30px;
            border-radius: 10px;
            box-shadow: 0 4px 6px rgba(0, 0, 0, 0.1);
            margin-bottom: 30px;
        }
        .search-box {
            width: 100%;
            padding: 15px;
            font-size: 16px;
            border: 2px solid #ddd;
            border-radius: 5px;
            margin-bottom: 15px;
        }
        .search-button {
            background: #667eea;
            color: white;
            padding: 15px 30px;
            font-size: 16px;
            border: none;
            border-radius: 5px;
            cursor: pointer;
        }
        .search-button:hover {
            background: #5a6fd8;
        }
        .results-container {
            background: white;
            padding: 30px;
            border-radius: 10px;
            box-shadow: 0 4px 6px rgba(0, 0, 0, 0.1);
        }
        .result-item {
            border-bottom: 1px solid #eee;
            padding: 20px 0;
        }
        .result-item:last-child {
            border-bottom: none;
        }
        .result-title {
            font-size: 18px;
            font-weight: bold;
            color: #333;
            margin-bottom: 10px;
        }
        .result-excerpt {
            color: #666;
            line-height: 1.6;
            margin-bottom: 10px;
        }
        .result-meta {
            font-size: 14px;
            color: #999;
        }
        .result-score {
            background: #667eea;
            color: white;
            padding: 3px 8px;
            border-radius: 3px;
            font-size: 12px;
        }
        .loading {
            text-align: center;
            color: #666;
            font-style: italic;
        }
        .error {
            background: #fee;
            color: #c33;
            padding: 15px;
            border-radius: 5px;
            margin: 20px 0;
        }
        .status {
            background: #efe;
            color: #363;
            padding: 15px;
            border-radius: 5px;
            margin: 20px 0;
        }
    </style>
</head>
<body>
    <div class="header">
        <h1>nLab RAG Search</h1>
        <p>Search through nLab mathematical content using semantic similarity</p>
    </div>

    <div class="search-container">
        <input type="text" id="searchQuery" class="search-box" placeholder="Enter your question about mathematics, category theory, type theory..." />
        <button onclick="performSearch()" class="search-button">Search</button>
        
        <div id="status"></div>
    </div>

    <div id="results" class="results-container" style="display: none;"></div>

    <script>
        // Check system status on page load
        window.onload = function() {
            checkStatus();
        };

        function checkStatus() {
            fetch('/status')
                .then(response => response.json())
                .then(data => {
                    const statusDiv = document.getElementById('status');
                    if (data.initialized) {
                        statusDiv.innerHTML = `<div class="status">System ready: ${data.pages_loaded} pages loaded</div>`;
                    } else {
                        statusDiv.innerHTML = `<div class="error">System not initialized. Please run the crawler first.</div>`;
                    }
                })
                .catch(error => {
                    console.error('Status check failed:', error);
                });
        }

        function performSearch() {
            const query = document.getElementById('searchQuery').value.trim();
            if (!query) {
                alert('Please enter a search query');
                return;
            }

            const resultsDiv = document.getElementById('results');
            resultsDiv.style.display = 'block';
            resultsDiv.innerHTML = '<div class="loading">Searching...</div>';

            fetch('/search', {
                method: 'POST',
                headers: {
                    'Content-Type': 'application/json',
                },
                body: JSON.stringify({
                    query: query,
                    top_k: 5
                })
            })
            .then(response => response.json())
            .then(data => {
                if (data.error) {
                    resultsDiv.innerHTML = `<div class="error">${data.error}</div>`;
                    return;
                }

                if (data.results.length === 0) {
                    resultsDiv.innerHTML = '<div class="loading">No results found</div>';
                    return;
                }

                let html = `<h3>Found ${data.total_results} results for "${data.query}"</h3>`;
                
                data.results.forEach(result => {
                    html += `
                        <div class="result-item">
                            <div class="result-title">${result.title}</div>
                            <div class="result-excerpt">${result.excerpt}</div>
                            <div class="result-meta">
                                <span class="result-score">Score: ${result.score.toFixed(3)}</span>
                                <a href="${result.url}" target="_blank">View on nLab</a>
                                ${result.categories.length > 0 ? ' | Categories: ' + result.categories.join(', ') : ''}
                            </div>
                        </div>
                    `;
                });

                resultsDiv.innerHTML = html;
            })
            .catch(error => {
                console.error('Search failed:', error);
                resultsDiv.innerHTML = '<div class="error">Search failed. Please try again.</div>';
            });
        }

        // Allow search on Enter key
        document.getElementById('searchQuery').addEventListener('keypress', function(e) {
            if (e.key === 'Enter') {
                performSearch();
            }
        });
    </script>
</body>
</html>''')
    
    # Initialize the RAG system
    if initialize_rag():
        print("Starting nLab RAG web interface...")
        print("Open http://localhost:5000 in your browser")
        app.run(debug=True, host='0.0.0.0', port=5000)
    else:
        print("Failed to initialize RAG system. Please run the crawler first:")
        print("python nlab_crawler.py --max-pages 20")
        print("python nlab_rag.py --setup")