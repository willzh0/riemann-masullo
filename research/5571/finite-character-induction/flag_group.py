"""Verify both quadratic flag characters of GL(3,2) using Python 3 only."""
from collections import Counter
from itertools import product


def compose(g, h):
    return tuple(g[i] for i in h)


# Vectors are encoded by their three binary coordinates. The columns are u,v,w.
G = []
for u, v, w in product(range(1, 8), repeat=3):
    g = (0, u, v, u ^ v, w, u ^ w, v ^ w, u ^ v ^ w)
    if len(set(g)) == 8:
        G.append(g)
identity = tuple(range(8))
inverse = {g: tuple(g.index(i) for i in range(8)) for g in G}


def conjugate(g, h):
    return compose(compose(g, h), inverse[g])


def cyclic(g):
    powers = {identity}
    t = g
    while t != identity:
        powers.add(t)
        t = compose(t, g)
    return powers


def normalizer(S):
    return {g for g in G if all(conjugate(g, h) in S for h in S)}


H = {g for g in G if g[1] == 1 and g[2] in (2, 3)}
A = {h for h in H if h[2] & 1 == 0}
B = {h for h in H if h[4] & 2 == 0}
assert (len(G), len(H), len(A), len(B)) == (168, 8, 4, 4)
assert normalizer(H) == H and len(normalizer(A)) == len(normalizer(B)) == 24
assert [sum(all(h[i] == i for h in S) for i in range(8)) for S in (A, B)] == [4, 2]

# Representatives and the projection G -> G/H for left cosets.
reps, coset = [], {}
for g in G:
    if g not in coset:
        idx = len(reps)
        reps.append(g)
        for h in H:
            coset[compose(g, h)] = idx


def signed_cycles(g, ker):
    """Cycle lengths and sign products for the actual induced monomial matrices."""
    cycles, seen = [], set()
    for j in range(len(reps)):
        if j in seen:
            continue
        i, length, sign = j, 0, 1
        while i not in seen:
            seen.add(i)
            t = compose(g, reps[i])
            i = coset[t]
            s = compose(inverse[reps[i]], t)
            assert s in H
            length += 1
            sign *= 1 if s in ker else -1
        cycles.append((length, sign))
    return cycles


def determinant(cycles):
    # Multiply (1-sign*T**length) with ascending integer coefficients.
    coeffs = [1]
    for length, sign in cycles:
        out = coeffs + [0] * length
        for i, c in enumerate(coeffs):
            out[i + length] -= sign * c
        coeffs = out
    return tuple(coeffs)


forms = {1: [(1, 1)] * 21, 2: [(1, 1)] + [(2, 1)] * 10,
         3: [(3, 1)] * 7, 4: [(1, -1)] + [(4, 1)] * 5, 7: [(7, 1)] * 3}
order = {g: len(cyclic(g)) for g in G}
chi, perm = {}, {}
for g in G:
    ca, cb = signed_cycles(g, A), signed_cycles(g, B)
    assert determinant(ca) == determinant(cb) == determinant(forms[order[g]])
    chi[g] = sum(s for d, s in ca if d == 1)
    perm[g] = sum(d == 1 for d, _ in ca)

unseen, table = set(G), []
while unseen:
    g = min(unseen)
    C = {conjugate(t, g) for t in G}
    unseen -= C
    table.append((order[g], len(C), len(C & H), len(C & A), len(C & B), chi[g]))
table.sort()
assert table == [(1, 1, 1, 1, 1, 21), (2, 21, 5, 3, 3, 1), (3, 56, 0, 0, 0, 0),
                 (4, 42, 2, 0, 0, -1), (7, 24, 0, 0, 0, 0), (7, 24, 0, 0, 0, 0)]
print("order, class size, intersections with H/A/B, common induced trace:", table)

# Rohrlich and the septic discriminant identify D=I=N(C_p), P=C_p at p=3,7.
def fixed_dimension(S, character):
    total = sum(character[h] for h in S)
    assert total % len(S) == 0
    return total // len(S)


for p, dims in [(3, (6, 7, 4, 7)), (7, (1, 3, 1, 3))]:
    P = cyclic(next(g for g in G if order[g] == p))
    I = normalizer(P)
    got = tuple(fixed_dimension(S, char) for char in (perm, chi) for S in (I, P))
    assert got == dims
    print("p, |I|, |P|, dim(W^I,W^P,V^I,V^P):", p, len(I), len(P), got)

involution = next(g for g in G if order[g] == 2)
conjugates = [conjugate(inverse[t], involution) for t in reps]
real_signs = Counter((int(h in A)*2-1, int(h in B)*2-1) for h in conjugates if h in H)
assert real_signs == {(1, 1): 1, (1, -1): 2, (-1, 1): 2}
assert ((21 + chi[involution]) // 2, (21 - chi[involution]) // 2) == (11, 10)
print("real-place sign pairs:", sorted(real_signs.items()))