#!/usr/bin/env python3
"""Mechanical Kani-harness generator for vstd `assume_specification` contracts.

Reads the six std_specs files the survey rated ~100% translatable
(num, cmp, ops, bits, result, option), extracts every `assume_specification`
item together with its INLINE postcondition, and emits a Kani harness for the
*mechanically translatable* subset into `src/generated.rs`. Anything that cannot
be translated is SKIPPED and recorded with a concrete reason in
`GENERATED_REPORT.md`. Nothing is ever approximated: an item is translated only
if every leaf of its postcondition falls inside the documented grammar below.

--------------------------------------------------------------------------------
TRANSLATION RULES (the entire trusted surface of this generator)
--------------------------------------------------------------------------------
An `assume_specification[<recv>::method](params) -> ret <postcond>;` is
translated iff:

  R1. It has an INLINE postcondition of one of these two shapes:
        `returns ( EXPR )`                       (postcond is `result == EXPR`)
        `ensures  IDENT == EXPR ,`               (single equality clause)
      Items with no inline postcondition (bare `-> T;`) are NOT translatable:
      their contract lives on an extension trait / separate spec fn, whose
      resolution is out of scope (would require inlining, i.e. approximation).

  R2. Every parameter type is a concrete Rust scalar after macro substitution
      (`$uN`/`$iN` -> a concrete integer type, or a literal scalar type).
      Reference / &mut / generic-type parameters are NOT translatable.

  R3. EXPR is built ONLY from this grammar (anything else -> skip):
        e ::= INT_LITERAL | PARAM
            | <$uN>::MAX | <$uN>::MIN | <$iN>::MAX | <$iN>::MIN
            | e + e | e - e | e * e | e / e | e % e | - e
            | e == e | e != e | e < e | e <= e | e > e | e >= e
            | e && e | e || e | ! e
            | if e { e } else { e }
            | None | Some( e as $uN ) | Some( e as $iN )
            | ( e ) | e as int | e as $uN | e as $iN
      A reference to ANY named function or spec fn (e.g. `rust_div`,
      `rust_rem`, `next_multiple_of`, `checked_div`, `wrapping_add`,
      `u8_trailing_zeros`, `is_variant`, `is_ok`, ...) is OUTSIDE the grammar
      and forces a skip with reason "references non-translatable symbol: X".

  R4. Integer semantics. Verus spec expressions compute over unbounded `int`.
      We evaluate the postcondition in Rust `i128`:
        - every integer parameter/const is widened `(p as i128)`;
        - `+ - *` are i128 arithmetic;
        - `/` is Verus Euclidean division  -> `.div_euclid()`;
        - `%` is Verus Euclidean remainder -> `.rem_euclid()`
          (for the guarded signed specs the divisor is never 0 and never the
           MIN/-1 overflow case, so these do not panic; for unsigned operands
           div_euclid/rem_euclid coincide with `/`,`%`).
      A `Some(inner as $T)` casts the i128 result back to the concrete `$T`.

  R5. Widening soundness. i128 must hold every intermediate for the concrete
      type, or we skip (never silently wrap):
        - `+ - %`  need  bits+2  signed bits;
        - `*`      needs 2*bits+2 signed bits.
      Hence 128-bit types are skipped entirely, and `*`-containing specs are
      skipped for 64-bit types (usize/isize are 64-bit on the CI target).

  R6. Tractability cap. CBMC bit-blasts arithmetic to SAT, so wide multiply and
      (especially) division/remainder are not solvable within a CI budget.
      Measured on Kani 0.67.0 / CBMC 6.10.0 / Kissat: div|rem is tractable only
      at 8-bit (~4s), multiply up to 16-bit (~5s), and add|sub scale linearly to
      64-bit (<1s). So div|rem specs are emitted only for 8-bit types, and
      multiply specs only for <=16-bit types. This is a resource bound, not a
      soundness bound: the skipped specs are translatable but too expensive.

The emitted harness is:
    #[cfg(kani)] #[kani::proof]
    fn gen_<ty>_<method>() {
        let p0: T0 = kani::any(); ...        // R2 inputs
        // (kani::assume(requires) for any precondition; none of the translated
        //  num.rs specs carry an executable precondition, so this is empty here)
        let spec = <translated EXPR>;        // R3/R4
        assert_eq!(spec, <recv>.method(args)); // call real std, check ensures
    }

Because every translated spec is a CURRENT (post-fix) vstd spec believed
correct, the ORACLE is: all generated harnesses must PASS. Any failure is
either a generator bug (fix the generator) or a genuine spec/std disagreement
(report loudly with the counterexample; never edit vstd).

Usage:  python3 generate.py [STD_SPECS_DIR] [OUT_DIR]
"""

import os, re, sys

STD = sys.argv[1] if len(sys.argv) > 1 else os.path.join(
    os.path.dirname(os.path.abspath(__file__)), "..", "..", "source", "vstd", "std_specs")
OUT = sys.argv[2] if len(sys.argv) > 2 else os.path.dirname(os.path.abspath(__file__))

FILES = ["num.rs", "cmp.rs", "ops.rs", "bits.rs", "result.rs", "option.rs"]

# Concrete integer instantiations of the num_specs! macro pair ($uN,$iN).
# usize/isize are 64-bit on the x86_64 CI target. 128-bit is skipped (R5).
INT_PAIRS = [
    ("u8", "i8", 8), ("u16", "i16", 16), ("u32", "i32", 32),
    ("u64", "i64", 64), ("usize", "isize", 64),
    ("u128", "i128", 128),   # will be skipped by R5
]

# ---------------------------------------------------------------------------
# Extraction: pull each `assume_specification ... ;` clause from a file, along
# with whether it sits inside the num_specs! macro (so $uN/$iN are live).
# ---------------------------------------------------------------------------
def clause_of(text, start):
    depth = 0
    i = start
    while i < len(text):
        c = text[i]
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif c == ";" and depth == 0:
            return text[start:i]
        i += 1
    return text[start:start + 800]

def extract_sites(fname):
    """Return list of dicts describing each assume_specification site."""
    path = os.path.join(STD, fname)
    text = open(path).read()
    sites = []
    for m in re.finditer(r"assume_specification", text):
        clause = clause_of(text, m.start())
        line = text[:m.start()].count("\n") + 1
        sites.append({"file": fname, "line": line, "clause": clause})
    return sites

# recv is between the first '[' and its matching ']'
def parse_recv(clause):
    lb = clause.find("[")
    if lb < 0:
        return None
    depth = 0
    for i in range(lb, len(clause)):
        if clause[i] == "[":
            depth += 1
        elif clause[i] == "]":
            depth -= 1
            if depth == 0:
                return clause[lb + 1:i].strip()
    return None

# params between the '(' ')' that follow the recv ']'
def parse_params(clause):
    rb = clause.find("]")
    if rb < 0:
        return None
    lp = clause.find("(", rb)
    if lp < 0:
        return None
    depth = 0
    for i in range(lp, len(clause)):
        if clause[i] == "(":
            depth += 1
        elif clause[i] == ")":
            depth -= 1
            if depth == 0:
                inner = clause[lp + 1:i]
                return inner, i
    return None

def split_top(s, sep=","):
    out, depth, cur = [], 0, ""
    for c in s:
        if c in "([{<":
            depth += 1
        elif c in ")]}>":
            depth -= 1
        if c == sep and depth == 0:
            out.append(cur); cur = ""
        else:
            cur += c
    if cur.strip():
        out.append(cur)
    return out

# postcondition: prefer `returns ( EXPR )`; else `ensures IDENT == EXPR`
def parse_postcond(clause, after):
    tail = clause[after:]
    mr = re.search(r"\breturns\b", tail)
    if mr:
        rest = tail[mr.end():]
        stripped = rest.lstrip()
        # Only a `returns ( EXPR )` form is a parenthesized postcondition. A
        # `returns g(args)` (e.g. `$mod_u::wrapping_add(x,y)`) must NOT be
        # mistaken for it — take the whole expression instead so the translator
        # sees (and rejects) the function reference.
        if stripped.startswith("("):
            lp = rest.find("(")
            depth = 0
            for i in range(lp, len(rest)):
                if rest[i] == "(":
                    depth += 1
                elif rest[i] == ")":
                    depth -= 1
                    if depth == 0:
                        return ("returns", rest[lp + 1:i].strip())
        expr = re.split(r"\bopens_invariants\b|\bno_unwind\b", rest)[0].strip()
        return ("returns", expr)
    me = re.search(r"\bensures\b", tail)
    if me:
        body = tail[me.end():]
        body = re.split(r"\bno_unwind\b|\bopens_invariants\b", body)[0]
        clauses = [c.strip() for c in split_top(body) if c.strip()]
        if len(clauses) == 1 and "==" in clauses[0]:
            lhs, rhs = clauses[0].split("==", 1)
            return ("ensures_eq", (lhs.strip(), rhs.strip()))
        return ("ensures_multi", clauses)
    return (None, None)

# ---------------------------------------------------------------------------
# Expression grammar: tokenizer + Pratt parser + emitter (R3/R4)
# ---------------------------------------------------------------------------
SENT = {"<$uN>::MAX": "UMAX", "<$uN>::MIN": "UMIN",
        "<$iN>::MAX": "IMAX", "<$iN>::MIN": "IMIN"}

class Untranslatable(Exception):
    pass

def tokenize(expr):
    # normalize sentinels & casts to atomic tokens
    s = expr
    for k, v in SENT.items():
        s = s.replace(k, f" @{v} ")
    s = s.replace(" as $uN", " @ASU").replace(" as $iN", " @ASI")
    s = s.replace(" as int", " @ASINT").replace(" as nat", " @ASINT")
    toks = []
    i, n = 0, len(s)
    two = {"==", "!=", "<=", ">=", "&&", "||"}
    while i < n:
        c = s[i]
        if c.isspace() or c == ",":
            i += 1; continue
        if c == "@":
            j = i + 1
            while j < n and (s[j].isalpha()):
                j += 1
            toks.append(("SENT", s[i + 1:j])); i = j; continue
        if s[i:i + 2] in two:
            toks.append(("OP", s[i:i + 2])); i += 2; continue
        if c in "+-*/%<>!(){}":
            toks.append(("OP", c)); i += 1; continue
        if c.isdigit():
            j = i
            while j < n and (s[j].isdigit() or s[j] == "_"):
                j += 1
            toks.append(("INT", s[i:j].replace("_", ""))); i = j; continue
        if c.isalpha() or c == "_":
            j = i
            while j < n and (s[j].isalnum() or s[j] == "_"):
                j += 1
            toks.append(("ID", s[i:j])); i = j; continue
        raise Untranslatable(f"unexpected char {c!r} in expr")
    return toks

KNOWN_ID = {"None", "Some", "if", "else", "true", "false"}

class Parser:
    def __init__(self, toks):
        self.toks = toks; self.i = 0
    def peek(self):
        return self.toks[self.i] if self.i < len(self.toks) else (None, None)
    def next(self):
        t = self.peek(); self.i += 1; return t
    def expect(self, val):
        t = self.next()
        if t[1] != val:
            raise Untranslatable(f"expected {val!r} got {t}")
    def parse(self):
        e = self.expr()
        if self.i != len(self.toks):
            raise Untranslatable("trailing tokens")
        return e
    # precedence climbing
    def expr(self):
        return self.or_()
    def or_(self):
        e = self.and_()
        while self.peek() == ("OP", "||"):
            self.next(); e = ("||", e, self.and_())
        return e
    def and_(self):
        e = self.cmp()
        while self.peek() == ("OP", "&&"):
            self.next(); e = ("&&", e, self.cmp())
        return e
    def cmp(self):
        e = self.add()
        while self.peek()[0] == "OP" and self.peek()[1] in ("==", "!=", "<", "<=", ">", ">="):
            op = self.next()[1]; e = (op, e, self.add())
        return e
    def add(self):
        e = self.mul()
        while self.peek()[0] == "OP" and self.peek()[1] in ("+", "-"):
            op = self.next()[1]; e = (op, e, self.mul())
        return e
    def mul(self):
        e = self.unary()
        while self.peek()[0] == "OP" and self.peek()[1] in ("*", "/", "%"):
            op = self.next()[1]; e = (op, e, self.unary())
        return e
    def unary(self):
        if self.peek() == ("OP", "-"):
            self.next(); return ("neg", self.unary())
        if self.peek() == ("OP", "!"):
            self.next(); return ("not", self.unary())
        return self.postfix()
    def postfix(self):
        e = self.primary()
        while self.peek()[0] == "SENT" and self.peek()[1] in ("ASU", "ASI", "ASINT"):
            k = self.next()[1]; e = ("cast", k, e)
        return e
    def primary(self):
        t = self.peek()
        if t == ("OP", "("):
            self.next(); e = self.expr(); self.expect(")"); return e
        if t[0] == "INT":
            self.next(); return ("int", t[1])
        if t[0] == "SENT":
            self.next(); return ("sent", t[1])
        if t[0] == "ID":
            self.next()
            name = t[1]
            if name == "if":
                cond = self.expr(); self.expect("{"); a = self.expr(); self.expect("}")
                el = self.next()
                if el != ("ID", "else"):
                    raise Untranslatable("if without else")
                self.expect("{"); b = self.expr(); self.expect("}")
                return ("if", cond, a, b)
            if name == "None":
                return ("none",)
            if name == "Some":
                self.expect("("); inner = self.expr(); self.expect(")")
                return ("some", inner)
            if name in ("true", "false"):
                return ("bool", name)
            # any other identifier: check it is a bare parameter, else untranslatable
            if self.peek() == ("OP", "(") or self.peek() == ("SENT", None):
                raise Untranslatable(f"references non-translatable symbol: {name}")
            return ("param", name)
        raise Untranslatable(f"cannot parse primary at {t}")

# ---- emitter ----
class Emitter:
    def __init__(self, U, I, params):
        self.U, self.I, self.params = U, I, params  # params: name->concrete type
    def emit_int(self, e):
        k = e[0]
        if k == "int":
            return f"{e[1]}i128"
        if k == "neg":
            return f"-({self.emit_int(e[1])})"
        if k in ("+", "-", "*"):
            return f"({self.emit_int(e[1])}) {k} ({self.emit_int(e[2])})"
        if k in ("/", "%"):
            # `/` and `%` are Verus Euclidean. They never overflow the native
            # width here (unsigned operands, or signed guarded against MIN/-1),
            # so compute them in the NATIVE type and widen the (in-range) result.
            # This avoids 128-bit division, which is pathological for CBMC's SAT
            # backend. Only same-typed bare-parameter operands are supported.
            a, b = e[1], e[2]
            if a[0] == "param" and b[0] == "param" \
               and self.params.get(a[1]) == self.params.get(b[1]):
                meth = "div_euclid" if k == "/" else "rem_euclid"
                return f"(({a[1]}).{meth}({b[1]}) as i128)"
            raise Untranslatable(f"'{k}' with non-scalar-parameter operands "
                                 f"(cannot bound width without native eval)")
        if k == "param":
            if e[1] not in self.params:
                raise Untranslatable(f"unknown parameter {e[1]}")
            return f"({e[1]} as i128)"
        if k == "sent":
            m = {"UMAX": f"{self.U}::MAX", "UMIN": f"{self.U}::MIN",
                 "IMAX": f"{self.I}::MAX", "IMIN": f"{self.I}::MIN"}[e[1]]
            return f"({m} as i128)"
        if k == "cast":
            if e[1] == "ASINT":
                return self.emit_int(e[2])
            t = self.U if e[1] == "ASU" else self.I
            return f"((({self.emit_int(e[2])}) as {t}) as i128)"
        raise Untranslatable(f"not an int expr: {k}")
    def emit_cond(self, e):
        k = e[0]
        if k == "||":
            return f"({self.emit_cond(e[1])}) || ({self.emit_cond(e[2])})"
        if k == "&&":
            return f"({self.emit_cond(e[1])}) && ({self.emit_cond(e[2])})"
        if k == "not":
            return f"!({self.emit_cond(e[1])})"
        if k in ("==", "!=", "<", "<=", ">", ">="):
            return f"({self.emit_int(e[1])}) {k} ({self.emit_int(e[2])})"
        if k == "bool":
            return e[1]
        raise Untranslatable(f"not a bool expr: {k}")
    def emit_val(self, e, surface):
        """surface: ('opt', T) | ('scalar', T) | ('bool',)"""
        k = e[0]
        if k == "if":
            return (f"if {self.emit_cond(e[1])} {{ {self.emit_val(e[2], surface)} }} "
                    f"else {{ {self.emit_val(e[3], surface)} }}")
        if surface[0] == "opt":
            T = surface[1]
            if k == "none":
                return "None"
            if k == "some":
                inner = e[1]
                # inner is `E as $T` (cast) or plain arithmetic
                if inner[0] == "cast":
                    return f"Some(({self.emit_int(inner[2])}) as {T})"
                return f"Some(({self.emit_int(inner)}) as {T})"
            raise Untranslatable(f"option surface got {k}")
        if surface[0] == "scalar":
            T = surface[1]
            if k == "sent":
                return {"UMAX": f"{self.U}::MAX", "UMIN": f"{self.U}::MIN",
                        "IMAX": f"{self.I}::MAX", "IMIN": f"{self.I}::MIN"}[e[1]]
            if k == "cast":
                return f"({self.emit_int(e[2])}) as {T}"
            # plain arithmetic value
            return f"({self.emit_int(e)}) as {T}"
        if surface[0] == "bool":
            return self.emit_cond(e)
        raise Untranslatable("bad surface")

# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------
def concretize(s, U, I):
    return s.replace("$uN", U).replace("$iN", I)

def gen_num_site(site, U, I, bits, skips, harnesses):
    clause = site["clause"]
    recv = parse_recv(clause)
    if recv is None:
        return
    # only handle inherent integer methods `<$uN>::m` / `<$iN>::m` (skip trait `as`)
    if " as " in recv:
        skips.append((site, U, "trait-method item carries no inline postcondition "
                      "(contract on extension trait)"))
        return
    mm = re.match(r"<\$([ui]N)>::(\w+)", recv.replace(" ", ""))
    if not mm:
        skips.append((site, U, f"receiver {recv!r} not a concrete integer method"))
        return
    signed = mm.group(1) == "iN"
    method = mm.group(2)
    recv_ty = I if signed else U
    pp = parse_params(clause)
    if pp is None:
        skips.append((site, U, "could not parse parameter list"))
        return
    params_src, after = pp
    params = []
    for p in split_top(params_src):
        p = p.strip()
        if ":" not in p:
            skips.append((site, U, "malformed parameter"))
            return
        name, ty = p.split(":", 1)
        name, ty = name.strip(), concretize(ty.strip(), U, I)
        if "&" in ty or "mut" in ty:
            skips.append((site, U, "reference / &mut parameter (R2)"))
            return
        params.append((name, ty))
    kind, pc = parse_postcond(clause, after)
    if kind is None:
        skips.append((site, U, "no inline postcondition (bare `-> T;`) (R1)"))
        return
    if kind == "ensures_multi":
        skips.append((site, U, "multi-clause ensures (R1: single equality only)"))
        return
    expr = pc if kind == "returns" else pc[1]
    if "$mod" in expr:
        skips.append((site, U, "references macro-local spec module ($mod_*) — "
                      "postcondition delegates to a vstd wrapping/spec fn (R3)"))
        return
    # determine return/surface type
    rt = clause[clause.find("->", after) + 2:]
    rt = re.split(r"\breturns\b|\bensures\b|\bno_unwind\b|\bopens_invariants\b|;", rt)[0]
    rt = concretize(rt.strip(), U, I)
    rt = re.sub(r"^\([^:]*:\s*", "", rt).rstrip(")").strip()  # strip `(res: T)`
    if rt.startswith("Option<"):
        surface = ("opt", rt[len("Option<"):-1].strip())
    elif rt == "bool":
        surface = ("bool",)
    else:
        surface = ("scalar", rt)
    # width guard (R5): i128 must hold every intermediate value.
    has_mul = "*" in expr
    has_divrem = ("/" in expr) or ("%" in expr)
    need = (2 * bits + 2) if has_mul else (bits + 2)
    if need > 127:
        skips.append((site, U, f"i128 widening insufficient: needs {need} bits "
                      f"({'product' if has_mul else 'sum'} of {bits}-bit) (R5)"))
        return
    # tractability cap (R6): CBMC bit-blasts arithmetic, so wide multiply and
    # (especially) division/remainder are not solvable within a CI budget.
    # Measured on Kani 0.67.0 / CBMC 6.10.0 / Kissat: div|rem tractable only at
    # 8-bit (~4s), multiply up to 16-bit (~5s), add|sub linear to 64-bit (<1s).
    if has_divrem and bits > 8:
        skips.append((site, U, "R6 tractability: division/remainder is only "
                      "CBMC-tractable at 8-bit within the CI budget"))
        return
    if has_mul and bits > 16:
        skips.append((site, U, "R6 tractability: multiplication is only "
                      "CBMC-tractable up to 16-bit within the CI budget"))
        return
    # translate
    try:
        ast = Parser(tokenize(expr)).parse()
        em = Emitter(U, I, {n: t for n, t in params})
        val = em.emit_val(ast, surface)
    except Untranslatable as ex:
        skips.append((site, U, str(ex)))
        return
    # build the std call: first param is the receiver (self by value)
    recv_name = params[0][0]
    args = ", ".join(n for n, _ in params[1:])
    call = f"{recv_name}.{method}({args})"
    inputs = "\n    ".join(f"let {n}: {t} = kani::any();" for n, t in params)
    fn = f"gen_{recv_ty}_{method}"
    body = f"""#[cfg(kani)]
#[kani::proof]
fn {fn}() {{
    // std_specs/{site['file']}  <{recv_ty}>::{method}
    {inputs}
    let spec: {rt} = {val};
    assert_eq!(spec, {call});
}}"""
    harnesses.append((fn, body))

def main():
    report = []
    harnesses = []
    skips = []
    per_file = {}
    # num.rs : instantiate the macro over concrete int pairs
    num_sites = extract_sites("num.rs")
    per_file["num.rs"] = {"sites": len(num_sites)}
    for site in num_sites:
        for (U, I, bits) in INT_PAIRS:
            gen_num_site(site, U, I, bits, skips, harnesses)
    # The other five files: extract & attempt; the grammar naturally rejects
    # them (no inline postcond / spec-fn references / generics / floats).
    other_hcount0 = len(harnesses)
    for fname in ["cmp.rs", "ops.rs", "bits.rs", "result.rs", "option.rs"]:
        sites = extract_sites(fname)
        per_file[fname] = {"sites": len(sites)}
        for site in sites:
            recv = parse_recv(site["clause"]) or ""
            pp = parse_params(site["clause"])
            if pp is None:
                skips.append((site, "-", "could not parse parameters"))
                continue
            kind, pc = parse_postcond(site["clause"], pp[1])
            if kind is None:
                skips.append((site, "-", "no inline postcondition (contract on "
                              "extension trait / separate spec fn) (R1)"))
                continue
            if kind == "ensures_multi":
                skips.append((site, "-", "multi-clause ensures (R1)"))
                continue
            expr = pc if kind == "returns" else pc[1]
            # generic / reference / float receivers are not concretizable here
            if "$uN" in expr or "$iN" in expr:
                skips.append((site, "-", "macro-parametric outside num_specs (unhandled)"))
                continue
            try:
                ast = Parser(tokenize(expr)).parse()
            except Untranslatable as ex:
                skips.append((site, "-", str(ex)))
                continue
            # If it parsed, it still needs concrete scalar params to emit; these
            # files' translatable-looking items are all generic (T/E) or float.
            skips.append((site, "-", "postcondition parses but receiver/params are "
                          "generic or float; no concrete scalar instantiation (R2)"))

    # ---- write generated.rs ----
    harnesses.sort()
    out_rs = os.path.join(OUT, "src", "generated.rs")
    with open(out_rs, "w") as f:
        f.write("// @generated by generate.py — DO NOT EDIT BY HAND.\n")
        f.write("// Mechanical Kani harnesses for vstd assume_specification contracts.\n")
        f.write("// See generate.py for the translation rules and GENERATED_REPORT.md\n")
        f.write("// for coverage and per-item skip reasons.\n")
        f.write("#![allow(unused, clippy::all)]\n\n")
        for _, body in harnesses:
            f.write(body + "\n\n")
    # ---- write report ----
    rep = os.path.join(OUT, "GENERATED_REPORT.md")
    with open(rep, "w") as f:
        f.write("# Generated-harness coverage report\n\n")
        f.write(f"Generator: `generate.py`  •  std_specs: `{os.path.relpath(STD, OUT)}`\n\n")
        f.write(f"**Emitted {len(harnesses)} Kani harnesses** into `src/generated.rs`.\n\n")
        f.write("## Per-file textual `assume_specification` sites\n\n")
        f.write("| file | sites | harnesses emitted |\n|---|---|---|\n")
        # count emitted per file
        emitted_num = len(harnesses)  # all emitted come from num.rs
        for fname in FILES:
            n = per_file.get(fname, {}).get("sites", 0)
            e = emitted_num if fname == "num.rs" else 0
            f.write(f"| {fname} | {n} | {e} |\n")
        f.write(f"\nTotal textual sites across the six files: "
                f"{sum(per_file[x]['sites'] for x in per_file)}.\n")
        f.write(f"num.rs sites are macro templates instantiated over "
                f"{len(INT_PAIRS)} integer pairs.\n\n")
        f.write("## Skips (grouped by reason)\n\n")
        by_reason = {}
        for site, U, reason in skips:
            by_reason.setdefault(reason, []).append((site, U))
        for reason in sorted(by_reason, key=lambda r: -len(by_reason[r])):
            items = by_reason[reason]
            f.write(f"### {reason}  — {len(items)}\n\n")
            shown = {}
            for site, U in items:
                key = (site["file"], site["line"])
                shown.setdefault(key, set()).add(U)
            for (fn, ln), us in sorted(shown.items()):
                usl = ",".join(sorted(u for u in us if u != "-"))
                extra = f"  [types: {usl}]" if usl else ""
                f.write(f"- `{fn}:{ln}`{extra}\n")
            f.write("\n")
        f.write("## Emitted harnesses\n\n")
        for fn, _ in harnesses:
            f.write(f"- `{fn}`\n")
    print(f"emitted {len(harnesses)} harnesses -> {out_rs}")
    print(f"skips: {len(skips)}  (see {rep})")
    # brief per-reason tally to stdout
    tally = {}
    for _, _, reason in skips:
        tally[reason] = tally.get(reason, 0) + 1
    for reason, n in sorted(tally.items(), key=lambda kv: -kv[1]):
        print(f"  {n:4}  {reason}")

if __name__ == "__main__":
    main()
