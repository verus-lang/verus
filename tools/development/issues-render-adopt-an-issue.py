import json
import json
import markdown

with open('issues.json', 'r') as json_file:
    issues = json.load(json_file)
    
md = ""

for issue in issues:
    md += f"## [{issue['number']}]({issue['html_url']}) {issue['title']}\n"
    md += "\n"
    if len(issue['labels']) != 0:
        md += "**Labels**: "
        for label in issue['labels']:
            md += f"`{label['name']}` "
        md += "\n"
    if len(issue['assignees']) != 0:
        md += "**Assignees**: "
        for assignee in issue['assignees']:
            md += f"`{assignee['login']}` "
        md += "\n"
    md += "\n"
    md += "\n"
    md += "**Nominated as adoptable**: \n"
    md += "\n"
    md += "**Adopter**: \n"
    md += "\n"
    
html = markdown.markdown(md)

with open('issues.html', 'w') as file:
    file.write(html)