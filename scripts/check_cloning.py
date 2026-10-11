#!/usr/bin/env python3
"""Standard-library replay of the identities behind the compared statements of Challenge.lean (the finder/checker
split: the Lean development is the trust chain, this script a second implementation). Gaussian
rationals (pairs of Fractions) and explicit matrices as nested lists; nothing imported beyond fractions, itertools,
random and sys. Every number is computed from the definitions: the six Pauli states, the Kraus action, the partial
traces and the fidelities exactly as Challenge.lean defines them (index 4r + 2a + b for the entry K (a, b) r); the
matrices and vectors the proofs use are compared against these computations, never used as inputs. Checks: the
six-state sums as quadratic forms (6 W_i = 1 + Omega_i); the symmetric certificate 5 - 12W >= 0 with its rational LDL,
kernel and the six-term sum of squares; trace preservation pinning the Bužek-Hillery Choi matrix; the
Bužek-Hillery channel, marginals and fidelities; the asymmetric family at eight rational points of the conic
(channel, marginals, fidelities, equality, the certificate's LDL and kernel, the trace-preservation solve); the
largest-eigenvalue formula at non-conic weights; the universal-NOT floor and its witness; the polynomial sum of
squares of the asymmetric certificate on a 4 x 4 grid of weights. Ends with VERDICT: PASS or VERDICT: FAIL; no
check uses assert; exit status 0 on PASS only.

    python -I scripts/check_cloning.py
"""

from fractions import Fraction as Fr
from itertools import product
import random
import sys

random.seed(20261011)
FAILS = []
CHECKS = 0


def check(label, ok):
    global CHECKS
    CHECKS += 1
    if not ok:
        FAILS.append(label)
        print("FAIL", label)


# ---------------------------------------------------------------- Gaussian rationals and matrices
class G:
    __slots__ = ("re", "im")

    def __init__(self, re=0, im=0):
        self.re, self.im = Fr(re), Fr(im)

    def __add__(self, o):
        o = g(o); return G(self.re + o.re, self.im + o.im)

    __radd__ = __add__

    def __sub__(self, o):
        o = g(o); return G(self.re - o.re, self.im - o.im)

    def __rsub__(self, o):
        return g(o) - self

    def __mul__(self, o):
        o = g(o); return G(self.re * o.re - self.im * o.im, self.re * o.im + self.im * o.re)

    __rmul__ = __mul__

    def __neg__(self):
        return G(-self.re, -self.im)

    def __truediv__(self, o):
        o = g(o); d = o.re * o.re + o.im * o.im
        return G((self.re * o.re + self.im * o.im) / d, (self.im * o.re - self.re * o.im) / d)

    def conj(self):
        return G(self.re, -self.im)

    def __eq__(self, o):
        o = g(o); return self.re == o.re and self.im == o.im

    def __hash__(self):
        return hash((self.re, self.im))

    def __repr__(self):
        if self.im == 0:
            return str(self.re)
        return f"({self.re}{'+' if self.im >= 0 else '-'}{abs(self.im)}i)"


def g(x):
    return x if isinstance(x, G) else G(x, 0)


I_ = G(0, 1)


def zeros(n, m):
    return [[G() for _ in range(m)] for _ in range(n)]


def eye(n):
    M = zeros(n, n)
    for i in range(n):
        M[i][i] = G(1)
    return M


def madd(A, B):
    return [[A[i][j] + B[i][j] for j in range(len(A[0]))] for i in range(len(A))]


def msub(A, B):
    return [[A[i][j] - B[i][j] for j in range(len(A[0]))] for i in range(len(A))]


def msc(c, A):
    return [[g(c) * A[i][j] for j in range(len(A[0]))] for i in range(len(A))]


def mmul(A, B):
    n, k, m = len(A), len(B), len(B[0])
    return [[sum((A[i][t] * B[t][j] for t in range(k)), G()) for j in range(m)] for i in range(n)]


def dag(A):
    return [[A[j][i].conj() for j in range(len(A))] for i in range(len(A[0]))]


def meq(A, B):
    return all(A[i][j] == B[i][j] for i in range(len(A)) for j in range(len(A[0])))


def trace(A):
    return sum((A[i][i] for i in range(len(A))), G())


def outer(u, v):
    """u v^dagger"""
    return [[u[i] * v[j].conj() for j in range(len(v))] for i in range(len(u))]


def vec(K):
    """vec of a 4x2 Kraus operator: index 4 r + 2 a1 + a2 (r the input, (a1, a2) the output row (2 a1 + a2))."""
    return [K[x][r] for r in range(2) for x in range(4)]


def unvec(k):
    return [[k[4 * r + x] for r in range(2)] for x in range(4)]


# ---------------------------------------------------------------- the definitions
def kraus_apply(Ks, rho):
    out = zeros(4, 4)
    for K in Ks:
        out = madd(out, mmul(mmul(K, rho), dag(K)))
    return out


def is_channel(Ks):
    S = zeros(2, 2)
    for K in Ks:
        S = madd(S, mmul(dag(K), K))
    return meq(S, eye(2))


def trace_out_second(M):  # Tr over a2: (a, b) -> sum_k M[(a,k)][(b,k)]
    return [[sum((M[2 * a + k][2 * b + k] for k in range(2)), G()) for b in range(2)] for a in range(2)]


def trace_out_first(M):  # Tr over a1: (a, b) -> sum_k M[(k,a)][(k,b)]
    return [[sum((M[2 * k + a][2 * k + b] for k in range(2)), G()) for b in range(2)] for a in range(2)]


def fidelity(rho, sigma):
    return trace(mmul(rho, sigma)).re


def proj(psi):
    return outer(psi, psi)


def F1(Ks, psi):
    rho = proj(psi)
    return fidelity(rho, trace_out_second(kraus_apply(Ks, rho)))


def F2(Ks, psi):
    rho = proj(psi)
    return fidelity(rho, trace_out_first(kraus_apply(Ks, rho)))


# the six Pauli eigenstates as density matrices (1 +- sigma)/2 and as vectors (the equatorial ones unnormalised, norm^2 2)
SX = [[G(0), G(1)], [G(1), G(0)]]
SY = [[G(0), -I_], [I_, G(0)]]
SZ = [[G(1), G(0)], [G(0), G(-1)]]
PAULI_STATES = []
for S in (SZ, SX, SY):
    for sgn in (1, -1):
        PAULI_STATES.append(msc(Fr(1, 2), madd(eye(2), msc(sgn, S))))
PAULI_VECS = [([G(1), G(0)], 1), ([G(0), G(1)], 1), ([G(1), G(1)], 2), ([G(1), G(-1)], 2),
              ([G(1), I_], 2), ([G(1), -I_], 2)]  # (vector, norm^2)


def six_avg(Ks, which):
    tot = Fr(0)
    for rho in PAULI_STATES:
        out = kraus_apply(Ks, rho)
        red = trace_out_second(out) if which == 1 else trace_out_first(out)
        tot += fidelity(rho, red)
    return tot / 6


# ---------------------------------------------------------------- H0: the Pauli states are the projectors of the six vectors
for s, (v, n2) in enumerate(PAULI_VECS):
    check(f"H0 pauliState {s} = psi psi^dagger / norm^2", meq(PAULI_STATES[s], msc(Fr(1, n2), proj(v))))
    check(f"H0 pauliState {s} has trace 1", trace(PAULI_STATES[s]) == G(1))
    check(f"H0 pauliState {s} is a projector", meq(mmul(PAULI_STATES[s], PAULI_STATES[s]), PAULI_STATES[s]))

# ---------------------------------------------------------------- H1: the Hermitian form of the six-state sums, by polarization
E = [[G(1 if i == j else 0) for j in range(8)] for i in range(8)]  # basis vectors of C^8


def form(which):
    """Matrix of the Hermitian form k |-> 6 * sixAvg_which([unvec k]) = sum over the six states of F_which."""
    def q(k):
        return 6 * six_avg([unvec(k)], which)

    def qc(k):  # complex-valued sesquilinear form via polarization
        return q(k)

    M = zeros(8, 8)
    for i in range(8):
        for j in range(8):
            # <e_i, M e_j> = (q(e_i+e_j) - q(e_i-e_j) + i q(e_i - i e_j) - i q(e_i + i e_j)) / 4   (physics convention: conj-linear in the first slot)
            ep = [E[i][t] + E[j][t] for t in range(8)]
            em = [E[i][t] - E[j][t] for t in range(8)]
            ei = [E[i][t] - I_ * E[j][t] for t in range(8)]
            ej = [E[i][t] + I_ * E[j][t] for t in range(8)]
            val = (G(q(ep)) - G(q(em)) + I_ * G(q(ei)) - I_ * G(q(ej))) / 4
            M[i][j] = val
    return M


SIXW1 = form(1)   # 6 W1
SIXW2 = form(2)   # 6 W2
TWELVEW = madd(SIXW1, SIXW2)  # 12 W


def quad(M, k):
    return sum((k[i].conj() * M[i][j] * k[j] for i in range(8) for j in range(8)), G())


# the form reproduces the definition on random Gaussian-integer Kraus operators (so the polarization is right)
for trial in range(30):
    k = [G(random.randint(-3, 3), random.randint(-3, 3)) for _ in range(8)]
    v = quad(TWELVEW, k)
    check(f"H1 form reproduces the six-state sum (trial {trial})", v.im == 0 and v.re == 6 * (six_avg([unvec(k)], 1) + six_avg([unvec(k)], 2)))

# the claimed 12W (compared, not used)
CLAIM = zeros(8, 8)
for i, d in enumerate([4, 3, 3, 2, 2, 3, 3, 4]):
    CLAIM[i][i] = G(d)
for (i, j) in [(0, 5), (0, 6), (1, 7), (2, 7)]:
    CLAIM[i][j] = G(1); CLAIM[j][i] = G(1)
check("H1 12W equals the claimed matrix", meq(TWELVEW, CLAIM))

# the structural claim 6 W_i = 1 + Omega_i, Omega_1 = |Om><Om|_{R A1} (x) 1_{A2}, Omega_2 = |Om><Om|_{R A2} (x) 1_{A1}
def omega(which):
    M = zeros(8, 8)
    for r, a1, a2, rp, b1, b2 in product(range(2), repeat=6):
        if which == 1:
            ok = (r == a1) and (rp == b1) and (a2 == b2)
        else:
            ok = (r == a2) and (rp == b2) and (a1 == b1)
        if ok:
            M[4 * r + 2 * a1 + a2][4 * rp + 2 * b1 + b2] = G(1)
    return M


OM1, OM2 = omega(1), omega(2)
check("H1 6 W1 = 1 + Omega_1", meq(SIXW1, madd(eye(8), OM1)))
check("H1 6 W2 = 1 + Omega_2", meq(SIXW2, madd(eye(8), OM2)))

# ---------------------------------------------------------------- H2: the symmetric certificate 5 - 12W >= 0, kernel span{v1, v2}
M5 = msub(msc(5, eye(8)), TWELVEW)


def ldl(M):
    """Exact LDL^dagger of a Hermitian matrix with no pivoting (returns (L, D) or None if a zero pivot has a nonzero column below)."""
    n = len(M)
    A = [row[:] for row in M]
    L = eye(n)
    D = [G() for _ in range(n)]
    for j in range(n):
        s = A[j][j]
        for k in range(j):
            s = s - L[j][k] * L[j][k].conj() * D[k]
        D[j] = s
        for i in range(j + 1, n):
            t = A[i][j]
            for k in range(j):
                t = t - L[i][k] * L[j][k].conj() * D[k]
            if D[j] == G(0):
                if t != G(0):
                    return None
                L[i][j] = G()
            else:
                L[i][j] = t / D[j]
    return L, D


res = ldl(M5)
check("H2 LDL of 5 - 12W exists without pivoting", res is not None)
L, D = res
Dm = zeros(8, 8)
for i in range(8):
    Dm[i][i] = D[i]
check("H2 L D L^dagger = 5 - 12W", meq(mmul(mmul(L, Dm), dag(L)), M5))
check("H2 every pivot is real and nonnegative", all(d.im == 0 and d.re >= 0 for d in D))
check("H2 exactly two zero pivots (rank 6)", sum(1 for d in D if d == G(0)) == 2)
print("H2 pivots of 5 - 12W:", [str(d) for d in D])
V1 = [G(2), G(0), G(0), G(0), G(0), G(1), G(1), G(0)]            # 2|000> + |101> + |110>
V2 = [G(0), G(Fr(1, 2)), G(Fr(1, 2)), G(0), G(0), G(0), G(0), G(1)]  # (|001> + |010>)/2 + |111>


def mv(M, v):
    return [sum((M[i][j] * v[j] for j in range(len(v))), G()) for i in range(len(M))]


check("H2 v1 in the kernel", all(x == G(0) for x in mv(M5, V1)))
check("H2 v2 in the kernel", all(x == G(0) for x in mv(M5, V2)))
# the shifted matrix (5 - eps) - 12W is not PSD for every eps > 0 (a kernel vector becomes negative)
check("H2 the constant 5 cannot be lowered", quad(msub(msc(Fr(4999, 1000), eye(8)), TWELVEW), V1).re < 0)

# the six-term SOS, as an identity of forms: 5|k|^2 - 12 q(k) = sum c_t |<w_t, k>|^2
# k_{ab,r} = K(a,b) r -> index 4 r + 2 a + b
def idx(a, b, r):
    return 4 * r + 2 * a + b


def unitv(pairs):
    v = [G() for _ in range(8)]
    for (coef, (a, b, r)) in pairs:
        v[idx(a, b, r)] = g(coef)
    return v


SOS = [
    (1, unitv([(1, (0, 0, 0)), (-1, (0, 1, 1)), (-1, (1, 0, 1))])),
    (2, unitv([(1, (0, 1, 0)), (Fr(-1, 2), (1, 1, 1))])),
    (2, unitv([(1, (1, 0, 0)), (Fr(-1, 2), (1, 1, 1))])),
    (3, unitv([(1, (1, 1, 0))])),
    (3, unitv([(1, (0, 0, 1))])),
    (1, unitv([(1, (0, 1, 1)), (-1, (1, 0, 1))])),
]
SOSM = zeros(8, 8)
for c, w in SOS:
    SOSM = madd(SOSM, msc(c, outer(w, w)))
check("H2 the six-term SOS equals 5 - 12W as a form", meq(SOSM, M5))

# uniqueness: Tr_out of v1 v1^dagger, v2 v2^dagger, v1 v2^dagger, and the trace-preservation solve
def tr_out(J):  # Tr over (a1, a2): R x R
    return [[sum((J[4 * r + x][4 * rp + x] for x in range(4)), G()) for rp in range(2)] for r in range(2)]


T11, T22, T12 = tr_out(outer(V1, V1)), tr_out(outer(V2, V2)), tr_out(outer(V1, V2))
check("H2 Tr_out v1v1 = diag(4,2)", meq(T11, [[G(4), G(0)], [G(0), G(2)]]))
check("H2 Tr_out v2v2 = diag(1/2,1)", meq(T22, [[G(Fr(1, 2)), G(0)], [G(0), G(1)]]))
check("H2 Tr_out v1v2 = E_10", meq(T12, [[G(0), G(0)], [G(1), G(0)]]))
# x T11 + y T22 + z T12 + conj(z) T12^dagger = 1  =>  z = 0, 4x + y/2 = 1, 2x + y = 1  =>  x = 1/6, y = 2/3
x, y = Fr(1, 6), Fr(2, 3)
check("H2 trace preservation solves to (1/6, 2/3, 0)", 4 * x + y / 2 == 1 and 2 * x + y == 1 and meq(madd(msc(x, T11), msc(y, T22)), eye(2)))
# and the system is nondegenerate: the 2x2 real system has determinant 4*1 - (1/2)*2 = 3 != 0
check("H2 the diagonal system is nondegenerate", Fr(4) * 1 - Fr(1, 2) * 2 != 0)

# ---------------------------------------------------------------- H3: the Buzek-Hillery channel
V1M = [[G(2), G(0)], [G(0), G(1)], [G(0), G(1)], [G(0), G(0)]]     # V1|0> = 2|00>, V1|1> = |01> + |10>
V2M = [[G(0), G(0)], [G(Fr(1, 2)), G(0)], [G(Fr(1, 2)), G(0)], [G(0), G(1)]]  # V2|0> = (|01>+|10>)/2, V2|1> = |11>
check("H3 (1/6) V1^dag V1 + (2/3) V2^dag V2 = 1", meq(madd(msc(Fr(1, 6), mmul(dag(V1M), V1M)), msc(Fr(2, 3), mmul(dag(V2M), V2M))), eye(2)))
check("H3 vec V1 = v1, vec V2 = v2", vec(V1M) == V1 and vec(V2M) == V2)


def bh_channel(rho):
    return madd(msc(Fr(1, 6), mmul(mmul(V1M, rho), dag(V1M))), msc(Fr(2, 3), mmul(mmul(V2M, rho), dag(V2M))))


def depol(eta, rho):  # eta rho + ((1 - eta)/2) Tr(rho) 1
    return madd(msc(eta, rho), msc((1 - Fr(eta)) / 2 * trace(rho), eye(2)))


for a in range(2):
    for b in range(2):
        Eab = zeros(2, 2); Eab[a][b] = G(1)
        out = bh_channel(Eab)
        check(f"H3 BH marginal 1 on E{a}{b} is (2/3) rho + (1/6) Tr 1", meq(trace_out_second(out), depol(Fr(2, 3), Eab)))
        check(f"H3 BH marginal 2 on E{a}{b} is (2/3) rho + (1/6) Tr 1", meq(trace_out_first(out), depol(Fr(2, 3), Eab)))
        check(f"H3 BH is trace preserving on E{a}{b}", trace(out) == trace(Eab))
# the Choi matrix J = sum_{r,r'} |r><r'| (x) BH(|r><r'|) in (R, A1, A2) order equals (1/6) v1v1 + (2/3) v2v2
JBH = zeros(8, 8)
for r in range(2):
    for rp in range(2):
        Err = zeros(2, 2); Err[r][rp] = G(1)
        out = bh_channel(Err)
        for xx in range(4):
            for yy in range(4):
                JBH[4 * r + xx][4 * rp + yy] = out[xx][yy]
check("H3 Choi(BH) = (1/6) v1v1 + (2/3) v2v2", meq(JBH, madd(msc(Fr(1, 6), outer(V1, V1)), msc(Fr(2, 3), outer(V2, V2)))))
check("H3 Tr(J_BH W) = 5/6", (quad(TWELVEW, V1) * Fr(1, 6) + quad(TWELVEW, V2) * Fr(2, 3)).re / 12 == Fr(5, 6))
# fidelity 5/6 on random Gaussian-integer psi: F(psi) is homogeneous of degree 4, so F = (5/6) |psi|^4
for trial in range(40):
    psi = [G(random.randint(-4, 4), random.randint(-4, 4)) for _ in range(2)]
    n2 = sum((p * p.conj() for p in psi), G()).re
    if n2 == 0:
        continue
    rho = proj(psi)
    out = bh_channel(rho)
    f1 = fidelity(rho, trace_out_second(out)); f2 = fidelity(rho, trace_out_first(out))
    check(f"H3 BH fidelities 5/6 (trial {trial})", f1 == Fr(5, 6) * n2 * n2 and f2 == Fr(5, 6) * n2 * n2)
# six-state averages of the BH map through the channel map (not Kraus ops, which need sqrt 6): compute directly
tot1 = tot2 = Fr(0)
for rho in PAULI_STATES:
    out = bh_channel(rho)
    tot1 += fidelity(rho, trace_out_second(out)); tot2 += fidelity(rho, trace_out_first(out))
check("H3 BH six-state averages 5/6, 5/6", tot1 / 6 == Fr(5, 6) and tot2 / 6 == Fr(5, 6))

# ---------------------------------------------------------------- H4/H5: the asymmetric family and its certificate
def asym_ops(al, be):
    """A0, A1 as 4x2 matrices over the field of (al, be) (Fractions here, at rational conic points)."""
    al, be = g(al), g(be)
    A0 = [[al + be, G(0)], [G(0), be], [G(0), al], [G(0), G(0)]]   # A0|0> = (a+b)|00>, A0|1> = a|10> + b|01>
    A1 = [[G(0), G(0)], [al, G(0)], [be, G(0)], [G(0), al + be]]   # A1|0> = a|01> + b|10>, A1|1> = (a+b)|11>
    return A0, A1


def asym_channel(al, be, rho):
    A0, A1 = asym_ops(al, be)
    return msc(Fr(1, 2), madd(mmul(mmul(A0, rho), dag(A0)), mmul(mmul(A1, rho), dag(A1))))


def conic_point(t):
    t = Fr(t)
    d = 1 + t + t * t
    return (1 - t * t) / d, (2 * t + t * t) / d


TS = [Fr(1, 2), Fr(1, 3), Fr(2, 5), Fr(3, 7), Fr(1, 7), Fr(0), Fr(1), Fr(5, 9)]
for t in TS:
    al, be = conic_point(t)
    check(f"H4 conic point t={t} satisfies a^2+ab+b^2=1", al * al + al * be + be * be == 1 and al >= 0 and be >= 0)
    A0, A1 = asym_ops(al, be)
    check(f"H4 (1/2)(A0^dag A0 + A1^dag A1) = 1 at t={t}", meq(msc(Fr(1, 2), madd(mmul(dag(A0), A0), mmul(dag(A1), A1))), eye(2)))
    for a in range(2):
        for b in range(2):
            Eab = zeros(2, 2); Eab[a][b] = G(1)
            out = asym_channel(al, be, Eab)
            check(f"H4 marginal 1 is (1-b^2) rho + (b^2/2) Tr 1 at t={t}, E{a}{b}", meq(trace_out_second(out), depol(1 - be * be, Eab)))
            check(f"H4 marginal 2 is (1-a^2) rho + (a^2/2) Tr 1 at t={t}, E{a}{b}", meq(trace_out_first(out), depol(1 - al * al, Eab)))
    # six-state averages and the weighted identity with equality
    f1 = f2 = Fr(0)
    for rho in PAULI_STATES:
        out = asym_channel(al, be, rho)
        f1 += fidelity(rho, trace_out_second(out)); f2 += fidelity(rho, trace_out_first(out))
    f1, f2 = f1 / 6, f2 / 6
    check(f"H4 averages (1 - b^2/2, 1 - a^2/2) at t={t}", f1 == 1 - be * be / 2 and f2 == 1 - al * al / 2)
    check(f"H4 equality (a^2+2ab) F1 + (2ab+b^2) F2 = 1 + 2ab at t={t}", (al * al + 2 * al * be) * f1 + (2 * al * be + be * be) * f2 == 1 + 2 * al * be)
    check(f"H4 homogeneous equality ab = a(a+2b) D1 + b(2a+b) D2 at t={t}", al * be == al * (al + 2 * be) * (1 - f1) + be * (2 * al + be) * (1 - f2))
    # the Choi matrix is (1/2)(vec A0 vec A0^dag + vec A1 vec A1^dag), the vec's being the w_j up to normalisation
    w0, w1 = vec(A0), vec(A1)
    # the certificate: (1 + 2ab)/2 * 1 - (a(a+2b) W1 + b(2a+b) W2) with W_i = (1 + Omega_i)/6 ... as forms on vec(K):
    # a * sixAvg1 + b * sixAvg2 = sum_i k_i^dag (a W1 + b W2) k_i and sum_i |k_i|^2 = 2, so the bound 1 + 2ab needs
    # (1 + 2ab)/2 * 1 - (a W1 + b W2) >= 0 with a = al(al+2be), b = be(2al+be).
    aw, bw = al * (al + 2 * be), be * (2 * al + be)
    Mab = msub(msc((1 + 2 * al * be) / 2, eye(8)), madd(msc(aw / 6, SIXW1), msc(bw / 6, SIXW2)))
    res = ldl(Mab)
    check(f"H5 LDL of the asymmetric certificate exists at t={t}", res is not None)
    if res is not None:
        Lt, Dt = res
        check(f"H5 pivots nonnegative at t={t}", all(d.im == 0 and d.re >= 0 for d in Dt))
        nz = sum(1 for d in Dt if d == G(0))
        check(f"H5 kernel dimension 2 at t={t} (al, be > 0) else as expected", (nz == 2) if (al > 0 and be > 0) else (nz >= 2))
    check(f"H5 w0 in the kernel at t={t}", all(x == G(0) for x in mv(Mab, w0)))
    check(f"H5 w1 in the kernel at t={t}", all(x == G(0) for x in mv(Mab, w1)))
    # the constant cannot be lowered
    check(f"H5 the constant cannot be lowered at t={t}", quad(msub(Mab, msc(Fr(1, 10 ** 6), eye(8))), w0).re < 0)
    # uniqueness: Tr_out of the Gram of w0, w1 and the trace-preservation solve
    if al > 0 and be > 0:
        T00, T11_, T01 = tr_out(outer(w0, w0)), tr_out(outer(w1, w1)), tr_out(outer(w0, w1))
        # x T00 + y T11 + z T01 + conj z T01^dag = 1: T01 is off-diagonal (a multiple of E10) so z = 0; diagonal 2x2 system
        check(f"H5 Tr_out w0 w1 is off-diagonal at t={t}", T01[0][0] == G(0) and T01[1][1] == G(0) and T01[1][0] != G(0))
        a11, a12, a21, a22 = T00[0][0].re, T11_[0][0].re, T00[1][1].re, T11_[1][1].re
        det = a11 * a22 - a12 * a21
        check(f"H5 the diagonal system is nondegenerate at t={t}", det != 0)
        xs = (a22 - a12) / det; ys = (a11 - a21) / det
        check(f"H5 trace preservation forces (1/2, 1/2) at t={t}", xs == Fr(1, 2) and ys == Fr(1, 2))

# the symmetric point is al = be = 1/sqrt 3: compare the maps through x = al^2 = be^2 = al*be = 1/3 (linear in these)
def asym_channel_sq(x, y, z, rho):
    """The family written in (x, y, z) = (al^2, al be, be^2): entries of A_j rho A_j^dag are linear in x, y, z."""
    # expand symbolically: build with al, be as formal square roots via the three products
    # A0 rho A0^dag entries: (al+be)^2 = x+2y+z, (al+be)al = x+y, (al+be)be = y+z, al^2 = x, al be = y, be^2 = z
    out = zeros(4, 4)
    # A0 = [[al+be, 0],[0, be],[0, al],[0,0]];  (A0 rho A0^dag)[i][j] = A0[i][0]*... use a generic bilinear expansion
    # represent A0 rows as linear forms in (al, be): row0 = (1,1)*e0, row1 = (0,1)*e1, row2 = (1,0)*e1
    rows0 = [((1, 1), 0), ((0, 1), 1), ((1, 0), 1), ((0, 0), 0)]
    rows1 = [((0, 0), 0), ((1, 0), 0), ((0, 1), 0), ((1, 1), 1)]

    def prod(c1, c2):  # (p1 al + q1 be)(p2 al + q2 be) = p1 p2 x + (p1 q2 + q1 p2) y + q1 q2 z
        (p1, q1), (p2, q2) = c1, c2
        return p1 * p2 * x + (p1 * q2 + q1 * p2) * y + q1 * q2 * z

    for rows in (rows0, rows1):
        for i in range(4):
            for j in range(4):
                (ci, ri), (cj, rj) = rows[i], rows[j]
                out[i][j] = out[i][j] + g(prod(ci, cj)) * rho[ri][rj] * Fr(1, 2)
    return out


for a in range(2):
    for b in range(2):
        Eab = zeros(2, 2); Eab[a][b] = G(1)
        check(f"H4 the family at (1/3,1/3,1/3) is the BH channel on E{a}{b}", meq(asym_channel_sq(Fr(1, 3), Fr(1, 3), Fr(1, 3), Eab), bh_channel(Eab)))
for t in TS:
    al, be = conic_point(t)
    for a in range(2):
        for b in range(2):
            Eab = zeros(2, 2); Eab[a][b] = G(1)
            check(f"H4 the (x,y,z) form agrees with the (al,be) form at t={t}, E{a}{b}", meq(asym_channel_sq(al * al, al * be, be * be, Eab), asym_channel(al, be, Eab)))

# ---------------------------------------------------------------- H5 at non-conic weights: lambda_max(a Omega1 + b Omega2) = a + b + sqrt(a^2 - ab + b^2)
# checked through the form: for (a, b) with a^2 - ab + b^2 a rational square, (a + b + s)/... : the matrix
# (a+b+s) 1 - (a Omega1 + b Omega2) is PSD with a 2-dimensional kernel (a, b > 0). Pairs (a, b, s): (3, 8, 7), (5, 8, 7), (7, 15, 13), (1, 1, 1).
for (a_, b_, s_) in [(3, 8, 7), (5, 8, 7), (7, 15, 13), (1, 1, 1), (8, 3, 7), (0, 1, 1), (1, 0, 1)]:
    check(f"H5 s^2 = a^2 - ab + b^2 for ({a_},{b_},{s_})", s_ * s_ == a_ * a_ - a_ * b_ + b_ * b_)
    Mw = msub(msc(a_ + b_ + s_, eye(8)), madd(msc(a_, OM1), msc(b_, OM2)))
    res = ldl(Mw)
    check(f"H5 lambda_max formula PSD at ({a_},{b_})", res is not None and all(d.im == 0 and d.re >= 0 for d in res[1]))
    if res is not None:
        nz = sum(1 for d in res[1] if d == G(0))
        check(f"H5 kernel dimension at ({a_},{b_}) is 2", nz == 2)
    check(f"H5 lambda_max cannot be lowered at ({a_},{b_})", ldl(msub(Mw, msc(Fr(1, 10 ** 6), eye(8)))) is None or any(d.re < 0 for d in ldl(msub(Mw, msc(Fr(1, 10 ** 6), eye(8))))[1]))

# ---------------------------------------------------------------- the universal-NOT floor: 6 sixAvg_i(K) = sum_i |k_i|^2 + sum_i <k_i, Omega_i k_i> >= sum |k_i|^2 = 2
check("H2 Omega_1 is PSD (a nonnegative form)", all(d.im == 0 and d.re >= 0 for d in ldl(OM1)[1]))
check("H2 Omega_2 is PSD (a nonnegative form)", all(d.im == 0 and d.re >= 0 for d in ldl(OM2)[1]))
# a channel attaining 1/3 on clone 1: the transpose-type map (universal NOT) on clone 1 with a constant clone 2
# N(rho) = (1/3)(Tr rho 1 + sigma_y rho^T sigma_y) = (1/3)(Tr rho 1 + (det-adjugate)): check the six-state average of N tensor (1/2) is 1/3
def unot(rho):
    rt = [[rho[j][i] for j in range(2)] for i in range(2)]
    return msc(Fr(1, 3), madd(msc(trace(rho), eye(2)), mmul(mmul(SY, rt), SY)))


def kron(A, B):
    return [[A[i // 2][j // 2] * B[i % 2][j % 2] for j in range(4)] for i in range(4)]


tot1 = tot2 = Fr(0)
for rho in PAULI_STATES:
    out = kron(unot(rho), msc(Fr(1, 2), eye(2)))
    tot1 += fidelity(rho, trace_out_second(out)); tot2 += fidelity(rho, trace_out_first(out))
check("NOT floor attained: six-state averages (1/3, 1/2) for UNOT x maximally mixed", tot1 / 6 == Fr(1, 3) and tot2 / 6 == Fr(1, 2))
# its Choi matrix is PSD (it is a channel): J = sum |r><r'| (x) out(E_rr')
JN = zeros(8, 8)
for r in range(2):
    for rp in range(2):
        Err = zeros(2, 2); Err[r][rp] = G(1)
        out = kron(unot(Err), msc(Fr(1, 2), eye(2)))
        for xx in range(4):
            for yy in range(4):
                JN[4 * r + xx][4 * rp + yy] = out[xx][yy]
resN = ldl(JN)
check("NOT floor witness is completely positive (Choi PSD)", resN is not None and all(d.im == 0 and d.re >= 0 for d in resN[1]))
check("NOT floor witness is trace preserving", meq(tr_out(JN), eye(2)))

# ---------------------------------------------------------------- H6: Cerf's form from the homogeneous bound, numerically on grid points of channels? (a deduction, not a computation) -- checked as algebra
# with a = sqrt(2 D2) t, b = sqrt(2 D1) t the homogeneous bound reads g <= 2 g^2 + 2 g (D1 + D2) with g = sqrt(D1 D2): verified symbolically by the identity below on rational squares
for (D1, D2) in [(Fr(1, 6), Fr(1, 6)), (Fr(1, 8), Fr(1, 2)), (Fr(9, 50), Fr(2, 25)), (Fr(1, 18), Fr(8, 18))]:
    # pick a^2 = 2 D2, b^2 = 2 D1 with rational square roots when possible: use squares directly
    import math
    a2, b2 = 2 * D2, 2 * D1
    # the inequality ab <= a(a+2b)D1 + b(2a+b)D2 with a = sqrt(a2), b = sqrt(b2), ab = sqrt(a2 b2): check both sides as polynomials in ab = g2 where g2^2 = a2 b2
    # RHS - LHS = a2 D1 + b2 D2 + 2ab(D1 + D2) - ab = 2 D1 D2 + 2 D1 D2 + 2 ab (D1 + D2) - ab = 4 D1 D2 + ab (2(D1+D2) - 1)
    # with ab = 2 sqrt(D1 D2) = 2 g: = 4 g^2 + 2 g (2(D1+D2) - 1) = 2 g (2 g + 2 (D1 + D2) - 1) >= 0 iff D1 + D2 + g >= 1/2.  (an identity; nothing numeric to check here)
    pass
check("H6 algebra: a2 D1 + b2 D2 = 4 D1 D2 when a2 = 2 D2, b2 = 2 D1", all(2 * D2 * D1 + 2 * D1 * D2 == 4 * D1 * D2 for (D1, D2) in [(Fr(1, 6), Fr(1, 6)), (Fr(1, 8), Fr(1, 2))]))

# ---------------------------------------------------------------- a random channel never beats the bounds (consistency, random Kraus families made trace preserving by Gram-Schmidt-free scaling is not exact; use random CP maps J and the bound Tr(JW) <= (5/6) Tr J / 2 ... as forms)
for trial in range(20):
    k = [G(random.randint(-3, 3), random.randint(-3, 3)) for _ in range(8)]
    n2 = sum((x * x.conj() for x in k), G()).re
    if n2 == 0:
        continue
    v = quad(TWELVEW, k).re
    check(f"consistency: 12 q(k) <= 5 |k|^2 (trial {trial})", v <= 5 * n2)
    for t in TS:
        al, be = conic_point(t)
        aw, bw = al * (al + 2 * be), be * (2 * al + be)
        lhs = (aw * quad(SIXW1, k).re + bw * quad(SIXW2, k).re) / 6
        check(f"consistency: asymmetric form at t={t} (trial {trial})", lhs <= (1 + 2 * al * be) / 2 * n2)

# ---------------------------------------------------------------- H5': the polynomial SOS identity of the asymmetric certificate (a grid in (a, b) pins a bivariate quadratic)
# (2a+b)(a+2b) |k|^2 - [a(a+2b) sum_j |<u_j,k>|^2 + b(2a+b) sum_j |<v_j,k>|^2]
#   = (1/3) sum_j |(a+2b)<u_j,k> - (2a+b)<v_j,k>|^2 + (2a+b)(a+2b) [ |k_011|^2 + |k_100|^2 + |k_000 - k_110 - k_101|^2/3 + |k_111 - k_001 - k_010|^2/3 ]
# with u_j = |00j> + |11j>, v_j = |0j0> + |1j1> (indices r a1 a2), and the complement vectors as written.
def e8(r, a1, a2):
    v = [G() for _ in range(8)]
    v[4 * r + 2 * a1 + a2] = G(1)
    return v


def vadd(*vs):
    return [sum((v[i] for v in vs), G()) for i in range(8)]


def vsc(c, v):
    return [g(c) * x for x in v]


U = [vadd(e8(0, 0, j), e8(1, 1, j)) for j in range(2)]
VV = [vadd(e8(0, j, 0), e8(1, j, 1)) for j in range(2)]
C1, C2 = e8(0, 1, 1), e8(1, 0, 0)
C3 = vadd(e8(0, 0, 0), vsc(-1, e8(1, 1, 0)), vsc(-1, e8(1, 0, 1)))
C4 = vadd(e8(1, 1, 1), vsc(-1, e8(0, 0, 1)), vsc(-1, e8(0, 1, 0)))
check("H5' u_j are the Omega_1 range vectors: Omega_1 = sum_j u_j u_j^dag", meq(OM1, madd(outer(U[0], U[0]), outer(U[1], U[1]))))
check("H5' v_j are the Omega_2 range vectors: Omega_2 = sum_j v_j v_j^dag", meq(OM2, madd(outer(VV[0], VV[0]), outer(VV[1], VV[1]))))
for ca in (Fr(0), Fr(1), Fr(2), Fr(3, 7)):
    for cb in (Fr(0), Fr(1), Fr(5, 2), Fr(2, 9)):
        lam = (2 * ca + cb) * (ca + 2 * cb)
        LHS = msub(msc(lam, eye(8)), madd(msc(ca * (ca + 2 * cb), OM1), msc(cb * (2 * ca + cb), OM2)))
        RHS = zeros(8, 8)
        for j in range(2):
            w = vadd(vsc(ca + 2 * cb, U[j]), vsc(-(2 * ca + cb), VV[j]))
            RHS = madd(RHS, msc(Fr(1, 3), outer(w, w)))
        for (c, nrm) in ((C1, 1), (C2, 1), (C3, 3), (C4, 3)):
            RHS = madd(RHS, msc(lam / nrm, outer(c, c)))
        check(f"H5' polynomial SOS identity at (a,b)=({ca},{cb})", meq(LHS, RHS))
# the complement vectors are orthogonal to every u_j, v_j and to each other
def dotc(x, y):
    return sum((x[i].conj() * y[i] for i in range(8)), G())


check("H5' complement vectors orthogonal to u_j, v_j", all(dotc(c, w) == G(0) for c in (C1, C2, C3, C4) for w in U + VV))
check("H5' complement vectors mutually orthogonal", all(dotc(c, d) == G(0) for c in (C1, C2, C3, C4) for d in (C1, C2, C3, C4) if c is not d))
check("H5' complement norms 1, 1, 3, 3", [dotc(c, c) for c in (C1, C2, C3, C4)] == [G(1), G(1), G(3), G(3)])
# the per-Kraus identities 6 sixAvg_i(K) = |K|^2 + sum_j |<u_j,k>|^2 (resp. v_j): the same as 6 W_i = 1 + Omega_i, restated entrywise
for trial in range(10):
    k = [G(random.randint(-3, 3), random.randint(-3, 3)) for _ in range(8)]
    n2 = sum((x * x.conj() for x in k), G())
    s1 = 6 * six_avg([unvec(k)], 1); s2 = 6 * six_avg([unvec(k)], 2)
    check(f"H5' 6 sixAvg_1 = |k|^2 + sum_j |<u_j,k>|^2 (trial {trial})", G(s1) == n2 + sum((dotc(U[j], k) * dotc(U[j], k).conj() for j in range(2)), G()))
    check(f"H5' 6 sixAvg_2 = |k|^2 + sum_j |<v_j,k>|^2 (trial {trial})", G(s2) == n2 + sum((dotc(VV[j], k) * dotc(VV[j], k).conj() for j in range(2)), G()))
print(f"{CHECKS} checks, {len(FAILS)} failures")
print("VERDICT: PASS" if not FAILS else "VERDICT: FAIL")
sys.exit(0 if not FAILS else 1)
