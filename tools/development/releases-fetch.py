
import requests
import json

GITHUB_TOKEN = 'github_pat_...'
REPO_OWNER = 'verus-lang'
REPO_NAME = 'verus'

def fetch_all_releases():
    url = f'https://api.github.com/repos/{REPO_OWNER}/{REPO_NAME}/releases'
    headers = {
        'Authorization': f'token {GITHUB_TOKEN}',
        'Accept': 'application/vnd.github.v3+json'
    }
    response = requests.get(url, headers=headers)
    response.raise_for_status()
    return response.json()

all_releases = fetch_all_releases()
with open('releases.json', 'w') as file:
    json.dump(all_releases, file, indent=4)

print(f'Saved {len(all_releases)} releases to releases.json')