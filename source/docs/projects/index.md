---
layout: default
---

<div class="hero">
    <div class="main relative card header">
        <h1>Verus — Research</h1>
    </div>
    <div class="main relative card header">
        <h2>Publications by the Verus team</h2>
        <ul class="publication">

        {% assign internal = site.projects | where: "type", "internal" %}
        {% for project in internal  %}
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
            </li>
        {% endfor %}

        </ul>
    </div>
    <div class="main relative card header">
        <h2>Publications using Verus</h2>
        <ul class="publication">

        {% assign external = site.projects | where: "type", "external" %}
        {% for project in external%}
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
            </li>
        {% endfor %}

        </ul>
    </div>
    <div class="main relative card header">
        <h1>Verus — Projects</h1>
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
