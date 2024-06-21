---
title: "An Append-only Log on Persistent Memory"
date: 2024-05-01
type: project
code: https://github.com/microsoft/verified-storage.git
---
The implementation handles crash consistency, ensuring that even if the process or machine crashes, it acts like an append-only log across the crashes. It also handles bit corruption, detecting if metadata read from persistent memory is corrupted.
