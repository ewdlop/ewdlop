# GitHub Models Quickstart Guide

This guide helps you get started with **GitHub Models** — an AI inference API that allows you to access and run various AI models directly within the GitHub platform using only your GitHub credentials.

## 🌟 What is GitHub Models?

GitHub Models is a feature that provides:
- **AI Inference API**: Run AI models like GPT-4o, Llama 3.1, Mistral, and more
- **Integrated Authentication**: Use your GitHub personal access token (PAT)
- **Model Playground**: Test and compare models interactively
- **Seamless Integration**: Works with GitHub Actions, Codespaces, and your local development

## 🚀 Getting Started

### Prerequisites

1. **GitHub Account**: You need a GitHub account
2. **Personal Access Token (PAT)**: Create a token with `models` scope
   - Go to: https://github.com/settings/tokens
   - Click "Generate new token (classic)"
   - Select the `models` scope
   - Save your token securely

### Quick Setup

#### Option 1: Using Python

```python
import os
import requests

# Set your GitHub token
GITHUB_TOKEN = os.environ.get("GITHUB_TOKEN")

# API endpoint
url = "https://models.github.ai/inference/chat/completions"

# Request payload
payload = {
    "model": "openai/gpt-4o",
    "messages": [
        {
            "role": "user",
            "content": "What is GitHub Models?"
        }
    ]
}

# Headers
headers = {
    "Accept": "application/vnd.github+json",
    "Authorization": f"Bearer {GITHUB_TOKEN}",
    "Content-Type": "application/json"
}

# Make the request
response = requests.post(url, json=payload, headers=headers)

# Print the response
if response.status_code == 200:
    result = response.json()
    print(result["choices"][0]["message"]["content"])
else:
    print(f"Error: {response.status_code}")
    print(response.text)
```

#### Option 2: Using JavaScript/Node.js

```javascript
const https = require('https');

const GITHUB_TOKEN = process.env.GITHUB_TOKEN;

function queryGitHubModel() {
  const payload = JSON.stringify({
    model: 'openai/gpt-4o',
    messages: [
      {
        role: 'user',
        content: 'What is GitHub Models?'
      }
    ]
  });
  
  const options = {
    hostname: 'models.github.ai',
    port: 443,
    path: '/inference/chat/completions',
    method: 'POST',
    headers: {
      'Accept': 'application/vnd.github+json',
      'Authorization': `Bearer ${GITHUB_TOKEN}`,
      'Content-Type': 'application/json',
      'Content-Length': Buffer.byteLength(payload)
    }
  };
  
  const req = https.request(options, (res) => {
    let data = '';
    
    res.on('data', (chunk) => {
      data += chunk;
    });
    
    res.on('end', () => {
      if (res.statusCode === 200) {
        const result = JSON.parse(data);
        console.log(result.choices[0].message.content);
      } else {
        console.error(`Error: ${res.statusCode}`);
        console.error(data);
      }
    });
  });
  
  req.on('error', (error) => {
    console.error('Request error:', error);
  });
  
  req.write(payload);
  req.end();
}

queryGitHubModel();
```


#### Option 3: Using cURL

```bash
curl -L -X POST \
  -H "Accept: application/vnd.github+json" \
  -H "Authorization: Bearer YOUR_GITHUB_TOKEN" \
  -H "Content-Type: application/json" \
  https://models.github.ai/inference/chat/completions \
  -d '{
    "model": "openai/gpt-4o",
    "messages": [
      {
        "role": "user",
        "content": "What is GitHub Models?"
      }
    ]
  }'
```

## 📚 Available Models

GitHub Models provides access to various AI models:

### Chat/Completion Models
- **OpenAI**: `openai/gpt-4o`, `openai/gpt-4o-mini`
- **Meta Llama**: `meta-llama/Llama-3.1-405B-Instruct`, `meta-llama/Llama-3.1-70B-Instruct`
- **Mistral**: `mistralai/Mistral-7B-Instruct-v0.3`, `mistralai/Mixtral-8x7B-Instruct-v0.1`
- **DeepSeek**: `deepseek-ai/DeepSeek-V2.5`
- **Cohere**: `cohere/command-r-plus`

### Image Models
- **DALL-E**: `openai/dall-e-3` (for image generation)
- **Stable Diffusion**: Various versions available

### Code Models
- **Codex**: Specialized for code generation and understanding

## 🎮 Using the Playground

GitHub Models includes an interactive playground:

1. Visit: https://github.com/marketplace/models
2. Select a model to test
3. Enter prompts and adjust parameters
4. Compare responses between different models
5. Export your configuration for use in code

## 🔧 Advanced Usage

### With Parameters

```python
payload = {
    "model": "openai/gpt-4o",
    "messages": [
        {"role": "system", "content": "You are a helpful coding assistant."},
        {"role": "user", "content": "Write a Python function to calculate fibonacci numbers."}
    ],
    "temperature": 0.7,
    "max_tokens": 500,
    "top_p": 0.95
}
```

### Streaming Responses

```python
payload = {
    "model": "openai/gpt-4o",
    "messages": [{"role": "user", "content": "Tell me a story"}],
    "stream": True
}

response = requests.post(url, json=payload, headers=headers, stream=True)

for line in response.iter_lines():
    if line:
        print(line.decode('utf-8'))
```

### Error Handling

```python
try:
    response = requests.post(url, json=payload, headers=headers, timeout=30)
    response.raise_for_status()
    result = response.json()
    print(result["choices"][0]["message"]["content"])
except requests.exceptions.RequestException as e:
    print(f"Request failed: {e}")
except KeyError as e:
    print(f"Unexpected response format: {e}")
```

## 🔐 Security Best Practices

1. **Never commit tokens**: Use environment variables or secret management
2. **Rotate tokens regularly**: Update your PAT periodically
3. **Use minimal scopes**: Only grant necessary permissions
4. **Monitor usage**: Check your API usage in GitHub settings
5. **Validate inputs**: Sanitize user inputs before sending to models

## 📊 Rate Limits and Quotas

- **Free tier**: Available for experimentation and development
- **Rate limits**: Vary by model and usage pattern
- **Production use**: Consider Azure AI for enterprise deployment

## 🎯 Use Cases

### Code Generation
```python
messages = [
    {"role": "system", "content": "You are an expert Python developer."},
    {"role": "user", "content": "Create a REST API endpoint for user authentication"}
]
```

### Documentation
```python
messages = [
    {"role": "user", "content": "Document this function: " + code_snippet}
]
```

### Code Review
```python
messages = [
    {"role": "system", "content": "You are a senior code reviewer."},
    {"role": "user", "content": "Review this code for security issues: " + code}
]
```

### Learning and Explanation
```python
messages = [
    {"role": "user", "content": "Explain async/await in JavaScript with examples"}
]
```

## 🔄 Integration with GitHub Actions

```yaml
name: AI Code Review

on:
  pull_request:
    types: [opened, synchronize]

jobs:
  ai-review:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      
      - name: Run AI Code Review
        env:
          GITHUB_TOKEN: ${{ secrets.GITHUB_TOKEN }}
        run: |
          python scripts/ai_review.py
```

## 🌐 Moving to Production

For production deployments:
1. **Azure AI**: Use Azure AI for enterprise-grade deployment
2. **Monitoring**: Implement logging and monitoring
3. **Caching**: Cache responses where appropriate
4. **Fallbacks**: Implement fallback strategies for API failures
5. **Cost Management**: Monitor and optimize API usage

## 📖 Additional Resources

- **Official Documentation**: https://docs.github.com/en/github-models
- **Model Marketplace**: https://github.com/marketplace/models
- **API Reference**: https://docs.github.com/en/rest/models
- **Community Examples**: https://github.com/topics/github-models

## 💡 Tips and Tricks

1. **Experiment in the playground** before implementing in code
2. **Use system messages** to set consistent behavior
3. **Implement retries** for transient failures
4. **Cache responses** for repeated queries
5. **Monitor token usage** to optimize costs
6. **Version your prompts** in `.prompt.yml` files

## 🤝 Contributing

Found a bug or have a suggestion? Please open an issue or submit a pull request!

## 📝 License

This guide is provided as-is for educational and development purposes.

---

**Happy coding with GitHub Models!** 🚀
