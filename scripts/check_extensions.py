#!/usr/bin/env python3
"""Independent exact replay of the cloning consult extensions.

Uses only Python's standard library and Fraction arithmetic. Quadratic-form
identities are checked as complete rational coefficient matrices, rather than
at sampled Kraus operators. The signed identity is checked coefficient by
coefficient in a^2, ab, b^2. Real symmetric coefficient identities also prove
the corresponding complex Hermitian identities, applied to real and imaginary
parts independently. Concrete channel fidelities are computed directly on all
six complex Pauli density matrices, with real/imaginary parts kept separate.

This is an independent mathematical replay, not a substitute for Lean kernel
checking. Run with: python scripts/check_extensions.py
"""

from fractions import Fraction as F
import sys


CHECKS = 0
FAILURES = []


def check(label, condition):
    global CHECKS
    CHECKS += 1
    if not condition:
        FAILURES.append(label)
        print("FAIL:", label)


def zeros(n, m=None):
    return [[F(0) for _ in range(n if m is None else m)] for _ in range(n)]


def eye(n):
    return [[F(i == j) for j in range(n)] for i in range(n)]


def transpose(a):
    return [list(row) for row in zip(*a)]


def add(*matrices):
    return [[sum((a[i][j] for a in matrices), F(0))
             for j in range(len(matrices[0][0]))]
            for i in range(len(matrices[0]))]


def scale(c, a):
    return [[F(c) * x for x in row] for row in a]


def mul(a, b):
    return [[sum((a[i][k] * b[k][j] for k in range(len(b))), F(0))
             for j in range(len(b[0]))] for i in range(len(a))]


def outer(v, w):
    return [[x * y for y in w] for x in v]


def trace(a):
    return sum((a[i][i] for i in range(len(a))), F(0))


def dot(v, w):
    return sum((x * y for x, y in zip(v, w)), F(0))


def matvec(a, v):
    return [dot(row, v) for row in a]


def vadd(*vectors):
    return [sum((v[i] for v in vectors), F(0)) for i in range(len(vectors[0]))]


def vscale(c, v):
    return [F(c) * x for x in v]


def is_psd(a):
    """Exact symmetric Schur-complement test, including zero pivots."""
    if a != transpose(a):
        return False
    a = [row[:] for row in a]
    for k in range(len(a)):
        pivot = a[k][k]
        if pivot < 0:
            return False
        if pivot == 0:
            if any(a[i][k] != 0 for i in range(k + 1, len(a))):
                return False
            continue
        for i in range(k + 1, len(a)):
            for j in range(k + 1, len(a)):
                a[i][j] -= a[i][k] * a[k][j] / pivot
    return True


# Coordinates are input first: index(r,a,b) = 4*r + 2*a + b.
def basis(r, a, b):
    v = [F(0)] * 8
    v[4 * r + 2 * a + b] = F(1)
    return v


I8 = eye(8)
U = [vadd(basis(0, 0, j), basis(1, 1, j)) for j in range(2)]
V = [vadd(basis(0, j, 0), basis(1, j, 1)) for j in range(2)]
OM1 = add(*(outer(u, u) for u in U))
OM2 = add(*(outer(v, v) for v in V))
C1 = basis(0, 1, 1)
C2 = basis(1, 0, 0)
C3 = vadd(basis(0, 0, 0), vscale(-1, basis(1, 1, 0)),
          vscale(-1, basis(1, 0, 1)))
C4 = vadd(basis(1, 1, 1), vscale(-1, basis(0, 0, 1)),
          vscale(-1, basis(0, 1, 0)))
COMPLEMENT = add(outer(C1, C1), outer(C2, C2),
                 scale(F(1, 3), outer(C3, C3)),
                 scale(F(1, 3), outer(C4, C4)))


# E1. The full-range Gram identity, as an 8 by 8 coefficient identity.
CROSS = add(*(add(outer(u, v), outer(v, u)) for u, v in zip(U, V)))
GRAM_LHS = add(scale(3, I8), scale(-2, OM1), scale(-2, OM2), CROSS)
check("E1 full-range Gram identity, all 64 coefficients",
      GRAM_LHS == scale(3, COMPLEMENT))
check("E1 Gram complement is a rank-four orthogonal projector",
      mul(COMPLEMENT, COMPLEMENT) == COMPLEMENT and trace(COMPLEMENT) == 4)
check("E1 missing cross term is detected (negative control)",
      add(scale(3, I8), scale(-2, OM1), scale(-2, OM2)) != GRAM_LHS)


# E2. The signed SOS as three coefficient matrices, with no sampling in a,b.
# w_j = a*(u_j-2*v_j) + b*(2*u_j-v_j).
WA = [vadd(u, vscale(-2, v)) for u, v in zip(U, V)]
WB = [vadd(vscale(2, u), vscale(-1, v)) for u, v in zip(U, V)]
SIGNED_LHS = {
    "a^2": add(scale(2, I8), scale(-1, OM1)),
    "ab": add(scale(5, I8), scale(-2, OM1), scale(-2, OM2)),
    "b^2": add(scale(2, I8), scale(-1, OM2)),
}
SIGNED_RHS = {
    "a^2": add(scale(F(1, 3), add(*(outer(w, w) for w in WA))),
                scale(2, COMPLEMENT)),
    "ab": add(scale(F(1, 3), add(*(add(outer(x, y), outer(y, x))
                                      for x, y in zip(WA, WB)))),
               scale(5, COMPLEMENT)),
    "b^2": add(scale(F(1, 3), add(*(outer(w, w) for w in WB))),
                scale(2, COMPLEMENT)),
}
for monomial in SIGNED_LHS:
    check(f"E2 signed SOS coefficient {monomial}, all 64 entries",
          SIGNED_LHS[monomial] == SIGNED_RHS[monomial])


def signed_matrix(a, b):
    return add(scale(a * a, SIGNED_LHS["a^2"]),
               scale(a * b, SIGNED_LHS["ab"]),
               scale(b * b, SIGNED_LHS["b^2"]))


for a, b in [(3, -1), (-1, 3), (-3, 1), (2, -1), (-1, 2),
             (1, 1), (0, 1), (1, 0), (0, 0), (1, -1), (3, -2)]:
    p = (2 * a + b) * (a + 2 * b)
    m = signed_matrix(a, b)
    check(f"E2 PSD domain at ({a},{b}) is P >= 0", is_psd(m) == (p >= 0))
    if p < 0:
        check(f"E2 explicit negative direction outside domain at ({a},{b})",
              dot(C1, matvec(m, C1)) == p and p < 0)


# E3. Canonical projection and its exact Pythagorean and gap identities.
V1 = vadd(vscale(2, basis(0, 0, 0)), basis(1, 0, 1), basis(1, 1, 0))
V2 = vadd(vscale(F(1, 2), basis(0, 0, 1)),
          vscale(F(1, 2), basis(0, 1, 0)), basis(1, 1, 1))
P = add(scale(F(1, 6), outer(V1, V1)), scale(F(2, 3), outer(V2, V2)))
R = add(I8, scale(-1, P))
Q = add(scale(3, I8), scale(-1, OM1), scale(-1, OM2))
check("E3 optimal-space basis norms and orthogonality",
      dot(V1, V1) == 6 and dot(V2, V2) == F(3, 2) and dot(V1, V2) == 0)
check("E3 orthogonal projector, all coefficients",
      P == transpose(P) and mul(P, P) == P and trace(P) == 2)
check("E3 exact coercivity Q = 2(I-P) + complement",
      Q == add(scale(2, R), COMPLEMENT))
check("E3 coercivity remainder is PSD", is_psd(add(Q, scale(-2, R))))

# The variables in this identity are k_0,...,k_7,x,y; this checks every term.
DISTANCE_MAP = [I8[i] + [-V1[i], -V2[i]] for i in range(8)]
DISTANCE_LHS = mul(transpose(DISTANCE_MAP), DISTANCE_MAP)
DISTANCE_RHS = zeros(10)
for i in range(8):
    for j in range(8):
        DISTANCE_RHS[i][j] = R[i][j]
XERR = vscale(F(-1, 6), V1) + [F(1), F(0)]
YERR = vscale(F(-2, 3), V2) + [F(0), F(1)]
DISTANCE_RHS = add(DISTANCE_RHS, scale(6, outer(XERR, XERR)),
                   scale(F(3, 2), outer(YERR, YERR)))
check("E3 projection distance identity, all 100 coefficients",
      DISTANCE_LHS == DISTANCE_RHS)
P_WRONG = add(scale(F(1, 5), outer(V1, V1)), scale(F(2, 3), outer(V2, V2)))
check("E3 perturbed projection coefficient is detected (negative control)",
      mul(P_WRONG, P_WRONG) != P_WRONG)
SINGLET_DIRECTION = vadd(basis(0, 0, 1), vscale(-1, basis(0, 1, 0)))
check("E3 spectral gap 2 is attained off the kernel",
      matvec(P, SINGLET_DIRECTION) == [F(0)] * 8 and
      matvec(Q, SINGLET_DIRECTION) == vscale(2, SINGLET_DIRECTION))
check("E3 increasing gap 2 to 201/100 fails (negative control)",
      dot(SINGLET_DIRECTION,
          matvec(add(Q, scale(F(-201, 100), R)), SINGLET_DIRECTION)) < 0)


# E4. Direct channel calculations on density matrices; square roots are
# avoided by carrying the positive common Kraus weight 1/(2s).
def asym_ops(a, b):
    a, b = F(a), F(b)
    return ([[a + b, F(0)], [F(0), b], [F(0), a], [F(0), F(0)]],
            [[F(0), F(0)], [a, F(0)], [b, F(0)], [F(0), a + b]])


def vec(k):
    return [k[x][r] for r in range(2) for x in range(4)]


def action(a, b, rho):
    ops = asym_ops(a, b)
    s = F(a) ** 2 + F(a) * F(b) + F(b) ** 2
    return scale(1 / (2 * s), add(*(mul(mul(k, rho), transpose(k)) for k in ops)))


def marginal(m, clone):
    if clone == 1:
        return [[sum((m[2 * a + k][2 * b + k] for k in range(2)), F(0))
                 for b in range(2)] for a in range(2)]
    return [[sum((m[2 * k + a][2 * k + b] for k in range(2)), F(0))
             for b in range(2)] for a in range(2)]


Z2 = zeros(2)
PAULI_STATES = [
    ([[F(1), F(0)], [F(0), F(0)]], Z2),
    ([[F(0), F(0)], [F(0), F(1)]], Z2),
    ([[F(1, 2), F(1, 2)], [F(1, 2), F(1, 2)]], Z2),
    ([[F(1, 2), F(-1, 2)], [F(-1, 2), F(1, 2)]], Z2),
    (scale(F(1, 2), eye(2)), [[F(0), F(-1, 2)], [F(1, 2), F(0)]]),
    (scale(F(1, 2), eye(2)), [[F(0), F(1, 2)], [F(-1, 2), F(0)]]),
]


def averages(a, b):
    result = []
    for clone in (1, 2):
        total = F(0)
        for re, im in PAULI_STATES:
            out_re = marginal(action(a, b, re), clone)
            out_im = marginal(action(a, b, im), clone)
            total += trace(mul(re, out_re)) - trace(mul(im, out_im))
        result.append(total / 6)
    return tuple(result)


def input_partial_trace(j):
    return [[sum((j[4 * r + x][4 * s + x] for x in range(4)), F(0))
             for s in range(2)] for r in range(2)]


def choi(a, b):
    s = F(a) ** 2 + F(a) * F(b) + F(b) ** 2
    return scale(1 / (2 * s), add(*(outer(vec(k), vec(k)) for k in asym_ops(a, b))))


WITNESSES = [(3, -1, F(13, 14), F(5, 14)),
             (2, -1, F(5, 6), F(1, 3)),
             (-1, 2, F(1, 3), F(5, 6)),
             (1, 1, F(5, 6), F(5, 6)),
             (1, -1, F(1, 2), F(1, 2))]
for a, b, f1, f2 in WITNESSES:
    j = choi(a, b)
    check(f"E4 channel at ({a},{b}) is CP and TP",
          is_psd(j) and input_partial_trace(j) == eye(2))
    check(f"E4 all six Pauli states give averages ({f1},{f2}) at ({a},{b})",
          averages(a, b) == (f1, f2))
    full_left = 3 * (f1 + f2) - F(7, 2)
    full_rad = (3 * f1 - 1) * (3 * f2 - 1)
    check(f"E4 full-range bound at ({a},{b})",
          full_rad >= 0 and (full_left <= 0 or full_left ** 2 <= full_rad))
    if (2 * a + b) * (a + 2 * b) >= 0:
        check(f"E4 signed objective attained at ({a},{b})",
              a * b == a * (a + 2 * b) * (1 - f1) + b * (2 * a + b) * (1 - f2))
        check(f"E4 full-range curved boundary attained at ({a},{b})",
              full_left >= 0 and full_left ** 2 == full_rad)

check("E4 clone/anticlone support value is exactly 1",
      3 * F(13, 14) - 5 * F(5, 14) == 1)
check("E4 BH Choi matrix is the canonical projector", choi(1, 1) == P)

# Trace-preservation constraints on the signed support are nondegenerate.
A0, A1 = (vec(k) for k in asym_ops(3, -1))
T00 = input_partial_trace(outer(A0, A0))
T11 = input_partial_trace(outer(A1, A1))
T01 = input_partial_trace(outer(A0, A1))
check("E4 signed equality support has nonsingular TP equations",
      T00 == [[F(4), F(0)], [F(0), F(10)]] and
      T11 == [[F(10), F(0)], [F(0), F(4)]] and
      T01 == [[F(0), F(0)], [F(-6), F(0)]] and
      T00[0][0] * T11[1][1] - T00[1][1] * T11[0][0] == -84)


# E5. Sharpness of the stability coefficient, including arbitrarily small
# rational parameters of the already defined asymmetric family.
for t in [F(1, 2), F(1, 10), F(1, 100), F(1, 10000)]:
    a, b = 1 + t, 1 - t
    f1, f2 = averages(a, b)
    epsilon = F(5, 6) - (f1 + f2) / 2
    residual = trace(mul(R, choi(a, b)))
    check(f"E5 exact near-optimal deficit and imbalance at t={t}",
          epsilon == t ** 2 / (3 * (3 + t ** 2)) and
          f1 - f2 == 2 * t / (3 + t ** 2))
    check(f"E5 sharp distance coefficient 6 at t={t}",
          residual == 6 * epsilon and epsilon > 0)

# A point satisfying the old error-form inequality can violate the new one.
fake_f1, fake_f2 = F(9, 10), F(1, 3)
fake_left = 3 * (fake_f1 + fake_f2) - F(7, 2)
fake_rad = (3 * fake_f1 - 1) * (3 * fake_f2 - 1)
check("E5 full-range bound detects (9/10,1/3) (negative control)",
      fake_left > 0 and fake_left ** 2 > fake_rad and
      (1 - fake_f1) + (1 - fake_f2) >= F(1, 2))

print(f"{CHECKS} exact extension checks, {len(FAILURES)} failures")
print("VERDICT: PASS" if not FAILURES else "VERDICT: FAIL")
sys.exit(bool(FAILURES))
