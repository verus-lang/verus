# Chained operators

In spec code, equality and inequality operators can be chained. For example,
`a <= b < c`
is equivalent to
`a <= b && b < c`.

Chained inequalities support `<`, `<=`, `>`, `>=`, and `==`, and support sequences of chained
operators of arbitrary length.
