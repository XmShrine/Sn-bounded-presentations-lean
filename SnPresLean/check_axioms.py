"""Numerical sanity checks of the four axioms of SnPres/Axioms.lean.

The relator sets below are exactly those of `sundayRels`, `carmichaelRels`, `mooreRels`; the
orders of the presented groups are computed by Todd-Coxeter coset enumeration over the trivial
subgroup.  Nagura's statement is checked in its integer form for 25 <= m <= 200000.
These checks are not part of the formal proof; they only guard against mis-stated axioms.
Run:  python3 check_axioms.py
"""
import math

def coset_enumerate(ngens, relators, subgens, max_cosets=4_000_000):
    L2 = 2 * ngens; table = [[-1] * L2]; par = [0]
    def fr(w):
        st = []
        for a in w:
            if st and st[-1] == a ^ 1: st.pop()
            else: st.append(a)
        return st
    def cr(w):
        w = fr(w)
        while len(w) >= 2 and w[0] == w[-1] ^ 1: w = w[1:-1]
        return w
    rels = [r for r in (cr(r) for r in relators) if r]
    def rep(c):
        r = c
        while par[r] != r: r = par[r]
        while par[c] != r: nx = par[c]; par[c] = r; c = nx
        return r
    def merge(k, l, q):
        k = rep(k); l = rep(l)
        if k == l: return
        if k > l: k, l = l, k
        par[l] = k; q.append(l)
    def coinc(a, b):
        q = []; merge(a, b, q); i = 0
        while i < len(q):
            e = q[i]; i += 1
            for xx in range(L2):
                f = table[e][xx]
                if f != -1:
                    xi = xx ^ 1
                    if table[f][xi] == e: table[f][xi] = -1
                    e1 = rep(e); f1 = rep(f)
                    if table[e1][xx] != -1: merge(f1, table[e1][xx], q)
                    elif table[f1][xi] != -1: merge(e1, table[f1][xi], q)
                    else: table[e1][xx] = f1; table[f1][xi] = e1
    def new():
        if len(table) >= max_cosets: raise RuntimeError("coset limit")
        table.append([-1] * L2); par.append(len(par)); return len(par) - 1
    def saf(c, w):
        f = c; b = c; i = 0; j = len(w) - 1
        while True:
            while i <= j and table[f][w[i]] != -1: f = table[f][w[i]]; i += 1
            if i > j:
                if f != b: coinc(f, b)
                return
            while j >= i and table[b][w[j] ^ 1] != -1: b = table[b][w[j] ^ 1]; j -= 1
            if j < i: coinc(f, b); return
            elif i == j: table[f][w[i]] = b; table[b][w[i] ^ 1] = f; return
            else:
                nn = new(); table[f][w[i]] = nn; table[nn][w[i] ^ 1] = f
    for w in subgens:
        w = fr(w)
        if w: saf(0, w)
    c = 0
    while c < len(table):
        if par[c] == c:
            for r in rels:
                if par[c] != c: break
                saf(c, r)
            if par[c] == c:
                for xx in range(L2):
                    if par[c] != c: break
                    if table[c][xx] == -1:
                        nn = new(); table[c][xx] = nn; table[nn][xx ^ 1] = c
        c += 1
    return sum(1 for i in range(len(par)) if par[i] == i)

def g(i): return 2 * i
def gi(i): return 2 * i + 1
def order(ngens, rels): return coset_enumerate(ngens, rels, [])

ok = True
for p in [5, 7, 11, 13, 17]:
    a, c = g(0), g(1)
    h = (p + 1) // 2
    rels = [[a] * p, [a, c, a, c, a, gi(1)], ([a] * h + [c] + [a] * 4 + [c]) * 2]
    o = order(2, rels); want = p * (p * p - 1) // 2; ok &= (o == want)
    print("Sunday     p=%2d: |G| = %6d   p(p^2-1)/2 = %6d" % (p, o, want))
for M in range(1, 6):
    rels = [[g(i)] * 3 for i in range(M)] + [[g(i), g(j)] * 2 for i in range(M) for j in range(i + 1, M)]
    o = order(M, rels); want = math.factorial(M + 2) // 2; ok &= (o == want)
    print("Carmichael M=%2d: |G| = %6d   (M+2)!/2   = %6d" % (M, o, want))
for n in range(2, 8):
    k = n - 1
    rels = [[g(i)] * 2 for i in range(k)] + [[g(i), g(i + 1)] * 3 for i in range(k - 1)] + \
           [[g(i), g(j)] * 2 for i in range(k) for j in range(i + 2, k)]
    o = order(k, rels); want = math.factorial(n); ok &= (o == want)
    print("Moore      n=%2d: |G| = %6d   n!         = %6d" % (n, o, want))
N = 240000
sieve = bytearray([1]) * (N + 1); sieve[0] = sieve[1] = 0
for i in range(2, int(N ** 0.5) + 1):
    if sieve[i]: sieve[i * i::i] = bytearray(len(sieve[i * i::i]))
nxt = [0] * (N + 2); q = 0
for i in range(N, -1, -1):
    if sieve[i]: q = i
    nxt[i] = q
bad = [m for m in range(25, 200001) if not (5 * nxt[m + 1] < 6 * m)]
ok &= not bad
print("Nagura: counterexamples m in [25, 200000]:", bad[:10])
print("ALL OK" if ok else "MISMATCH")
