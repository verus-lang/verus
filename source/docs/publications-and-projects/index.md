---
layout: default
---

<div class="hero">
    <!--<div class="main relative card header">
        <h1>Overview</h1>
    </div>-->
    <div class="main relative card header">
      Please see below for <a href="#publications">research publications</a> about and using Verus, 
      as well as <a href="#projects">projects</a> built using Verus.
      To add your work here, please open a pull request that adds a new file to the 
      <a href="https://github.com/verus-lang/verus/tree/main/source/docs/publications-and-projects">'source/docs/publications-and-projects' directory</a>.
    </div>

    <div class="main relative card header">
        <h1>Verus — Publications</h1><a name="publications"/>
    </div>


    {% for t in site.pubtypes %}

    <div class="main relative card header">
        {% if t == "internal" %}
        <h2>Publications by the Verus team</h2>
        {% endif %}
        {% if t == "external" %}
        <h2>Publications using Verus</h2>
        {% endif %}
        <br/>

        <ul class="publication">

        {% assign projects = site.projects | where: "type", t %}
        {% for project in projects %}
            <li>
                <div>
                  <a href="{{ project.pdf }}" class="paper-title">{{ project.title }}</a>
                  {% if project.code %}
                    &nbsp;&nbsp;[<a href="{{ project.code }}">code</a>]
                  {% endif %}
                  <br/>
                  {{ project.authors }}
                </div>
                <div style="display: inline-block" class="publication-location">
                  {{ project.venue }},
                </div>
                {{ project.date | date: "%B, %Y" }}
                <br/>
                {% if project.award %}
                  <b> <a href="https://www.vecteezy.com/free-vector/award-symbol"><img style="vertical-align:middle" alt="Award icon from Vecteezy.com" src="award.jpg"/></a> 
                  {{ project.award }}</b>
                {% endif %}
            </li>
        {% endfor %}

        </ul>

    </div>

    {% endfor %}

    <div class="main relative card header">
        <h1>Verus — Projects</h1><a name="projects"/>
    </div>
    <div class="main relative card header">
        <ul class="publication">

        {% assign projects = site.projects | where: "type", "project" %}
        {% for project in projects %}
            <li>
                <div>
                  <a href="{{ project.code }}" class="paper-title">{{ project.title }}</a>
                </div>
                {{ project.content }}
            </li>
        {% endfor %}

        </ul>
    </div>
</div>
