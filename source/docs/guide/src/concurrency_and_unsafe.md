# Concurrency and Unsafe Code

Verus provides a framework based on "tokenized state machines" 
for verifing programs that require a nontrivial ownership discipline.
This includes *multi-threaded concurrent code* as well as 
code that needs *unsafe features* (e.g., raw pointers and unsafe cells).

The topic is sufficiently complex that we cover it in a 
[separate tutorial and reference book](https://verus-lang.github.io/verus/state_machines/intro.html).

