# GitHub Models Examples

This directory contains practical examples for using GitHub Models API.

## 📁 Contents

- **`basic_chat.py`** - Simple chat completion example in Python
- **`basic_chat.js`** - Simple chat completion example in JavaScript/Node.js
- **`code_generation.py`** - Code generation example
- **`streaming_response.py`** - Streaming responses example
- **`multi_model_comparison.py`** - Compare responses from different models

## 🚀 Setup

### Python Examples

1. **Install dependencies**:
   ```bash
   pip install requests python-dotenv
   ```

2. **Set up your environment**:
   ```bash
   # Create a .env file
   echo "GITHUB_TOKEN=your_github_token_here" > .env
   ```

3. **Run an example**:
   ```bash
   python basic_chat.py
   ```

### JavaScript Examples

1. **Install dependencies** (optional):
   ```bash
   npm install dotenv
   # or
   npm install
   ```
   
   Note: The examples use Node.js native `https` module, so no additional HTTP library is needed.

2. **Set up your environment**:
   ```bash
   # Create a .env file
   echo "GITHUB_TOKEN=your_github_token_here" > .env
   ```

3. **Run an example**:
   ```bash
   node basic_chat.js
   ```

## 🔑 Getting Your GitHub Token

1. Go to https://github.com/settings/tokens
2. Click "Generate new token (classic)"
3. Give it a descriptive name
4. Select the `models` scope
5. Click "Generate token"
6. Copy the token and save it securely

## ⚠️ Security Notes

- **Never commit your `.env` file** to version control
- Keep your GitHub token secure
- Rotate tokens regularly
- Use minimal scopes necessary

## 📚 Learn More

- [GitHub Models Quickstart Guide](../GITHUB_MODELS_QUICKSTART.md)
- [Official Documentation](https://docs.github.com/en/github-models)
- [Model Marketplace](https://github.com/marketplace/models)
