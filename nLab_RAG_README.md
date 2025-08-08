# nLab Web Crawler and RAG System

A sophisticated web crawler and Retrieval-Augmented Generation (RAG) system specifically designed for the [nLab](https://ncatlab.org/) (nCatLab) collaborative mathematics wiki. This system complements the existing Coq formalization library by providing semantic search and question-answering capabilities over nLab's mathematical content.

## Overview

This project extends the existing nLab Coq Library with modern AI capabilities, creating a bridge between formal mathematical proofs and natural language mathematical discourse. The system includes:

1. **Web Crawler**: Respectfully scrapes nLab pages while following robots.txt and implementing rate limiting
2. **RAG System**: Uses sentence transformers and FAISS for semantic search over mathematical content
3. **Web Interface**: Flask-based web UI for easy interaction with the system
4. **Integration**: Seamlessly integrates with the existing Coq formalization project

## Features

### 🕷️ nLab Web Crawler
- **Respectful crawling** with robots.txt compliance and rate limiting
- **Content extraction** optimized for nLab's mathematical content structure
- **Metadata extraction** including categories, references, and related pages
- **Robust error handling** and logging for reliable operation
- **JSON export** for easy integration with other tools

### 🔍 RAG System
- **Semantic search** using state-of-the-art sentence transformers
- **Efficient indexing** with FAISS for fast similarity search
- **Text chunking** with overlap for better context preservation
- **Multi-modal retrieval** supporting both exact and approximate search
- **Relevance scoring** for quality ranking of results

### 🌐 Web Interface
- **Clean, modern UI** for easy interaction
- **Real-time search** with instant results
- **Context highlighting** showing relevant excerpts
- **Source attribution** with direct links to nLab pages
- **Category browsing** for exploration of mathematical topics

## Installation

### Prerequisites
- Python 3.8 or higher
- Git (for repository operations)
- 2GB+ RAM (for embedding models)
- 1GB+ disk space (for data storage)

### Setup

1. **Clone the repository** (if not already cloned):
```bash
git clone https://github.com/ewdlop/CopolitProfofilo.git
cd CopolitProfofilo
```

2. **Install Python dependencies**:
```bash
pip install -r requirements.txt
```

3. **Verify installation**:
```bash
python -c "import sentence_transformers, faiss, flask; print('All dependencies installed successfully!')"
```

## Quick Start

### Option 1: Run the Complete Demo
```bash
# Run demo with 10 pages (recommended for first time)
python nlab_demo.py --max-pages 10

# Run demo with more pages (slower but more comprehensive)
python nlab_demo.py --max-pages 50
```

### Option 2: Step-by-Step Setup

1. **Crawl nLab pages**:
```bash
# Crawl 20 pages (adjust as needed)
python nlab_crawler.py --max-pages 20 --delay 1.0
```

2. **Set up RAG system**:
```bash
# Build embeddings and search index
python nlab_rag.py --setup
```

3. **Start web interface**:
```bash
# Launch web server
python nlab_web.py
```

4. **Open browser** and navigate to `http://localhost:5000`

### Option 3: Command Line Queries
```bash
# Query the system directly
python nlab_rag.py --query "What is a category?"
python nlab_rag.py --query "Explain functors and natural transformations"
```

## Usage Examples

### Web Interface
1. Open `http://localhost:5000` in your browser
2. Enter mathematical questions like:
   - "What is a category?"
   - "Explain natural transformations"
   - "What are topoi?"
   - "How do functors work?"
3. Browse results with relevance scores and source links

### Python API
```python
from nlab_rag import nLabRAG

# Initialize RAG system
rag = nLabRAG()
rag.setup_full_system()

# Perform semantic search
results = rag.search("category theory", top_k=5)

# Get formatted response
response = rag.query_with_context("What is a functor?")
print(response)
```

### Command Line
```bash
# Search with different parameters
python nlab_rag.py --query "type theory" --top-k 3

# Force rebuild of embeddings
python nlab_rag.py --setup --force-rebuild
```

## Configuration

### Crawler Settings
Modify `nlab_crawler.py` for custom crawler behavior:
```python
crawler = nLabCrawler(
    base_url="https://ncatlab.org",
    delay=1.0  # Seconds between requests
)
```

### RAG Settings
Customize the RAG system in `nlab_rag.py`:
```python
rag = nLabRAG(
    model_name="all-MiniLM-L6-v2",  # Sentence transformer model
    data_dir="nlab_data"            # Data storage directory
)
```

### Web Interface
Configure the Flask app in `nlab_web.py`:
```python
app.run(
    debug=False,    # Set to False for production
    host='0.0.0.0', # Listen on all interfaces
    port=5000       # Port number
)
```

## Project Structure

```
CopolitProfofilo/
├── README.md                    # This file
├── requirements.txt             # Python dependencies
├── nlab_crawler.py             # Web crawler implementation
├── nlab_rag.py                 # RAG system implementation
├── nlab_web.py                 # Web interface
├── nlab_demo.py                # Complete system demo
├── nlab_data/                  # Data storage directory
│   ├── nlab_pages.json         # Crawled page content
│   ├── embeddings.pkl          # Vector embeddings
│   ├── chunks.pkl              # Text chunks
│   └── faiss_index_*.index     # Search indices
├── templates/                  # Web interface templates
│   └── index.html              # Main web page
├── CategoryTheory/             # Coq formalization files
├── TypeTheory/                 # Coq formalization files
├── Foundations/                # Coq formalization files
└── ... (other Coq directories)
```

## Integration with Coq Library

This RAG system complements the existing Coq formalization by:

1. **Providing context** for formal development through semantic search
2. **Bridging informal and formal** mathematics by connecting nLab articles to Coq definitions
3. **Supporting exploration** of mathematical concepts before formalization
4. **Enabling documentation** linking between formal proofs and informal explanations

### Example Workflow
1. Use RAG system to explore a mathematical concept (e.g., "adjoint functors")
2. Read relevant nLab content to understand the concept
3. Refer to existing Coq formalization in `CategoryTheory/Adjunctions.v`
4. Extend or modify the formal development as needed

## Advanced Usage

### Custom Models
Use different sentence transformer models:
```python
# More powerful but slower model
rag = nLabRAG(model_name="all-mpnet-base-v2")

# Multilingual model
rag = nLabRAG(model_name="paraphrase-multilingual-MiniLM-L12-v2")
```

### Batch Processing
Process multiple queries efficiently:
```python
queries = [
    "What is a category?",
    "Explain functors",
    "What are natural transformations?"
]

for query in queries:
    results = rag.search(query, top_k=3)
    print(f"Query: {query}")
    for result in results:
        print(f"  - {result.page.title} (score: {result.score:.3f})")
```

### Data Export
Export processed data for analysis:
```python
# Export all pages with embeddings
import json
import numpy as np

# Save embeddings separately
np.save('nlab_embeddings.npy', rag.embeddings)

# Export page metadata
metadata = [{
    'title': page.title,
    'url': page.url,
    'categories': page.categories,
    'content_length': len(page.content)
} for page in rag.pages]

with open('nlab_metadata.json', 'w') as f:
    json.dump(metadata, f, indent=2)
```

## Performance Optimization

### For Large Datasets
- Use IVF index for faster search: `rag.build_index(index_type="IVF")`
- Increase chunk size for longer documents: `rag.prepare_chunks(chunk_size=1024)`
- Use GPU acceleration if available: `model_name="all-MiniLM-L6-v2"` with CUDA

### Memory Management
- Process embeddings in batches to reduce memory usage
- Use memory mapping for large embedding files
- Clean up unused variables after processing

## Troubleshooting

### Common Issues

1. **"No pages crawled"**
   - Check internet connection
   - Verify nLab website accessibility
   - Reduce max_pages parameter for testing

2. **"RAG system not initialized"**
   - Run crawler first: `python nlab_crawler.py --max-pages 10`
   - Then set up RAG: `python nlab_rag.py --setup`

3. **"FAISS installation issues"**
   - Use `faiss-cpu` for compatibility: `pip install faiss-cpu`
   - For better performance, install `faiss-gpu` if CUDA available

4. **"Sentence transformers model download fails"**
   - Check internet connection
   - Try a different model: `model_name="all-MiniLM-L6-v2"`
   - Clear Hugging Face cache if needed

### Debug Mode
Enable detailed logging:
```python
import logging
logging.basicConfig(level=logging.DEBUG)

# Then run any component
python nlab_rag.py --query "debug test"
```

## Contributing

This RAG system is designed to complement the existing Coq formalization project. Contributions are welcome in several areas:

### Crawler Improvements
- Better content extraction for specific nLab page types
- Support for additional mathematical wikis
- Enhanced metadata extraction

### RAG Enhancements
- Integration with mathematical knowledge bases
- Support for mathematical notation in queries
- Improved chunking strategies for mathematical content

### Web Interface
- Better mathematical rendering (MathJax integration)
- Advanced filtering and sorting options
- Export functionality for results

### Integration Features
- Direct links between nLab content and Coq definitions
- Automated suggestion of formalization candidates
- Cross-referencing between informal and formal mathematics

## License

This project follows the same academic sharing principles as the main nLab Coq Library, designed to support mathematical research and education.

## References

- [nLab](https://ncatlab.org/) - The collaborative mathematics wiki
- [Sentence Transformers](https://www.sbert.net/) - For semantic embeddings
- [FAISS](https://faiss.ai/) - For efficient similarity search
- [Coq](https://coq.inria.fr/) - The Coq proof assistant
- [Mathematical Components](https://github.com/math-comp/math-comp) - Related formalization project

## Citation

If you use this RAG system in academic work, please cite:
```
nLab RAG System - A Retrieval-Augmented Generation system for nLab mathematical content
GitHub Repository: https://github.com/ewdlop/CopolitProfofilo
```

---

*This RAG system bridges the gap between informal mathematical discourse and formal verification, supporting the broader goal of making mathematics more accessible and verifiable.*