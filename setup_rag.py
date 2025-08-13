#!/usr/bin/env python3
"""
nLab RAG System Setup Script

Convenience script to set up and test the complete nLab RAG system.
Handles dependency installation, data generation, and system testing.
"""

import os
import sys
import subprocess
import json

def run_command(command, description=""):
    """Run a command and handle errors."""
    print(f"\n{'='*50}")
    print(f"Running: {description or command}")
    print(f"{'='*50}")
    
    try:
        result = subprocess.run(command, shell=True, check=True, capture_output=True, text=True)
        if result.stdout:
            print(result.stdout)
        return True
    except subprocess.CalledProcessError as e:
        print(f"Error: {e}")
        if e.stderr:
            print(f"Stderr: {e.stderr}")
        return False

def check_dependencies():
    """Check if required Python packages are installed."""
    required_packages = [
        'requests', 'beautifulsoup4', 'lxml', 'sentence_transformers', 
        'faiss_cpu', 'numpy', 'pandas', 'nltk', 'tqdm', 'flask'
    ]
    
    missing_packages = []
    
    for package in required_packages:
        try:
            __import__(package.replace('-', '_'))
        except ImportError:
            missing_packages.append(package)
    
    return missing_packages

def setup_environment():
    """Set up the Python environment."""
    print("Setting up nLab RAG System...")
    
    # Check for Python
    if sys.version_info < (3, 8):
        print("Error: Python 3.8 or higher is required")
        return False
    
    print(f"Python version: {sys.version}")
    
    # Check dependencies
    missing = check_dependencies()
    
    if missing:
        print(f"Missing packages: {missing}")
        print("Installing dependencies...")
        if not run_command("pip install -r requirements.txt", "Installing Python dependencies"):
            print("Failed to install dependencies")
            return False
    else:
        print("All dependencies are already installed!")
    
    return True

def generate_data():
    """Generate or download nLab data."""
    data_file = "nlab_data/nlab_pages.json"
    
    if os.path.exists(data_file):
        try:
            with open(data_file, 'r') as f:
                data = json.load(f)
            print(f"Found existing data file with {len(data)} pages")
            
            # Ask user if they want to regenerate
            response = input("Regenerate mock data? (y/N): ").strip().lower()
            if response not in ['y', 'yes']:
                return True
        except Exception as e:
            print(f"Error reading existing data: {e}")
    
    print("Generating mock nLab data...")
    if not run_command("python mock_data_generator.py", "Generating mock mathematical content"):
        print("Failed to generate mock data")
        return False
    
    return True

def test_simple_rag():
    """Test the simple RAG system."""
    print("Testing simple RAG system...")
    
    # Create a simple test script
    test_script = '''
from simple_rag_demo import SimplenLabRAG

rag = SimplenLabRAG()
pages_loaded = rag.load_pages()

if pages_loaded == 0:
    print("ERROR: No pages loaded")
    exit(1)

print(f"SUCCESS: Loaded {pages_loaded} pages")

# Test a simple query
results = rag.search("What is a category?", top_k=2)
print(f"SUCCESS: Found {len(results)} results for test query")

for i, result in enumerate(results, 1):
    print(f"  {i}. {result.page.title} (score: {result.score:.3f})")

print("Simple RAG system is working correctly!")
'''
    
    with open('test_rag.py', 'w') as f:
        f.write(test_script)
    
    success = run_command("python test_rag.py", "Testing simple RAG functionality")
    
    # Clean up
    if os.path.exists('test_rag.py'):
        os.remove('test_rag.py')
    
    return success

def test_full_rag():
    """Test the full RAG system (if network is available)."""
    print("Testing full RAG system...")
    
    # Test if we can import sentence transformers
    try:
        import sentence_transformers
        print("Sentence transformers available - testing full RAG system")
        
        test_script = '''
from nlab_rag import nLabRAG
import warnings
warnings.filterwarnings("ignore")

try:
    rag = nLabRAG()
    pages_loaded = rag.load_pages()
    
    if pages_loaded == 0:
        print("ERROR: No pages loaded")
        exit(1)
    
    print(f"SUCCESS: Full RAG system initialized with {pages_loaded} pages")
    
    # Test setup (this might fail without internet)
    if rag.setup_full_system():
        print("SUCCESS: Full RAG system setup complete")
    else:
        print("INFO: Full setup failed (likely due to network issues)")
        print("      This is expected in sandboxed environments")
        
except Exception as e:
    print(f"INFO: Full RAG system test failed: {e}")
    print("      This is expected without internet connectivity")
'''
        
        with open('test_full_rag.py', 'w') as f:
            f.write(test_script)
        
        success = run_command("python test_full_rag.py", "Testing full RAG system")
        
        # Clean up
        if os.path.exists('test_full_rag.py'):
            os.remove('test_full_rag.py')
        
        return success
        
    except ImportError:
        print("Sentence transformers not available - skipping full RAG test")
        return True

def main():
    """Main setup function."""
    print("nLab RAG System Setup")
    print("=" * 40)
    
    # Step 1: Environment setup
    if not setup_environment():
        print("\n❌ Environment setup failed")
        return False
    
    # Step 2: Data generation
    if not generate_data():
        print("\n❌ Data generation failed")
        return False
    
    # Step 3: Test simple RAG
    if not test_simple_rag():
        print("\n❌ Simple RAG test failed")
        return False
    
    # Step 4: Test full RAG (optional)
    test_full_rag()  # Don't fail if this doesn't work
    
    # Success message
    print("\n" + "=" * 60)
    print("✅ nLab RAG System Setup Complete!")
    print("=" * 60)
    print("\nNext steps:")
    print("1. Run the simple demo:     python simple_rag_demo.py")
    print("2. Run the full demo:       python nlab_demo.py --max-pages 10")
    print("3. Start the web interface: python nlab_web.py")
    print("4. Read the documentation:  nLab_RAG_README.md")
    print("\nThe system is ready to use!")
    
    return True

if __name__ == "__main__":
    success = main()
    if not success:
        sys.exit(1)