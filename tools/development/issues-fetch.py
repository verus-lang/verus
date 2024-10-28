
import requests
import json

# Replace with your personal access token
GITHUB_TOKEN = 'github_pat_...'
REPO_OWNER = 'verus-lang'
REPO_NAME = 'verus'

url = f'https://api.github.com/repos/{REPO_OWNER}/{REPO_NAME}/issues'
url += '?state=open'

headers = {
    'Authorization': f'token {GITHUB_TOKEN}',
    'Accept': 'application/vnd.github.v3+json'
}

def fetch_issues(url):
    issues = []
    while url:
        response = requests.get(url, headers=headers)
        response_data = response.json()
        issues.extend(response_data)
        
        if 'next' in response.links:
            url = response.links['next']['url']
        else:
            url = None
    return issues

all_issues = fetch_issues(url)
all_issues = [i for i in all_issues if 'pull_request' not in i]

with open('issues.json', 'w') as file:
    json.dump(all_issues, file, indent=4)

print(f'Saved {len(all_issues)} issues to issues.json')
