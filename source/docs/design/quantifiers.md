# Trigger selection for operators

We do not plan to automatically select triggers for arithmetic operations (unlike dafnly). Arithmetic operations like `k * d` aren't very reliable triggers, since Z3 can internally reorder the operations (e.g. `d * k`).  You can wrap the operations in a function (`mul(k, d)`) or avoid the quantifier in the first place (`v % d == 0`).
