#!/usr/bin/env node
/**
 * Basic GitHub Models Chat Example (JavaScript/Node.js)
 * 
 * This script demonstrates how to use GitHub Models API for simple chat completions.
 */

const https = require('https');

/**
 * Load GitHub token from environment variable
 */
function loadGitHubToken() {
  const token = process.env.GITHUB_TOKEN;
  if (!token) {
    console.error('Error: GITHUB_TOKEN environment variable not set');
    console.error('Please set it using: export GITHUB_TOKEN=your_token_here');
    process.exit(1);
  }
  return token;
}

/**
 * Query GitHub Models API with messages
 * 
 * @param {Array} messages - Array of message objects with role and content
 * @param {string} model - Model identifier
 * @param {number} temperature - Sampling temperature (0.0 to 1.0)
 * @param {number} maxTokens - Maximum tokens in response
 * @returns {Promise<string|null>} Response content or null if request fails
 */
function queryGitHubModel(
  messages,
  model = 'openai/gpt-4o',
  temperature = 0.7,
  maxTokens = 500
) {
  return new Promise((resolve, reject) => {
    const token = loadGitHubToken();
    
    const payload = JSON.stringify({
      model: model,
      messages: messages,
      temperature: temperature,
      max_tokens: maxTokens
    });
    
    const options = {
      hostname: 'models.github.ai',
      port: 443,
      path: '/inference/chat/completions',
      method: 'POST',
      headers: {
        'Accept': 'application/vnd.github+json',
        'Authorization': `Bearer ${token}`,
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
          try {
            const result = JSON.parse(data);
            resolve(result.choices[0].message.content);
          } catch (error) {
            console.error('Error parsing response:', error);
            reject(error);
          }
        } else {
          console.error(`Request failed with status ${res.statusCode}`);
          console.error('Response:', data);
          reject(new Error(`HTTP ${res.statusCode}`));
        }
      });
    });
    
    req.on('error', (error) => {
      console.error('Request error:', error);
      reject(error);
    });
    
    req.write(payload);
    req.end();
  });
}

/**
 * Main function demonstrating basic chat usage
 */
async function main() {
  console.log('🤖 GitHub Models - Basic Chat Example (Node.js)\n');
  
  try {
    // Example 1: Simple question
    console.log('='.repeat(60));
    console.log('Example 1: Simple Question');
    console.log('='.repeat(60));
    
    let messages = [
      {
        role: 'user',
        content: 'What is GitHub Models and why would I use it?'
      }
    ];
    
    let response = await queryGitHubModel(messages);
    console.log(`\nResponse:\n${response}\n`);
    
    // Example 2: Conversation with system message
    console.log('='.repeat(60));
    console.log('Example 2: Conversation with System Message');
    console.log('='.repeat(60));
    
    messages = [
      {
        role: 'system',
        content: 'You are a helpful JavaScript programming assistant. Be concise and practical.'
      },
      {
        role: 'user',
        content: 'How do I read a JSON file in Node.js?'
      }
    ];
    
    response = await queryGitHubModel(messages, 'openai/gpt-4o', 0.5);
    console.log(`\nResponse:\n${response}\n`);
    
    // Example 3: Multi-turn conversation
    console.log('='.repeat(60));
    console.log('Example 3: Multi-turn Conversation');
    console.log('='.repeat(60));
    
    messages = [
      {
        role: 'user',
        content: 'What is the difference between let, const, and var in JavaScript?'
      },
      {
        role: 'assistant',
        content: 'var is function-scoped and can be redeclared. let is block-scoped and cannot be redeclared. const is also block-scoped but cannot be reassigned.'
      },
      {
        role: 'user',
        content: 'Give me a practical example showing when to use each.'
      }
    ];
    
    response = await queryGitHubModel(messages, 'openai/gpt-4o', 0.6);
    console.log(`\nResponse:\n${response}\n`);
    
    console.log('='.repeat(60));
    console.log('✅ Examples completed!');
    
  } catch (error) {
    console.error('Error running examples:', error);
    process.exit(1);
  }
}

// Run the main function
if (require.main === module) {
  main();
}

module.exports = { queryGitHubModel };
