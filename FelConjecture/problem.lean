import Mathlib

/-
# Problem: Fel's Conjecture for Numerical Semigroups

A numerical semigroup $S \subseteq \mathbb{N}$ is a subset containing 0, closed under addition,
with finite complement (the set of gaps $\Delta = \mathbb{N} \setminus S$).

Given generators $\{d_1, \ldots, d_m\}$ with $\gcd = 1$, we define:
- Gap power sums: $G_r(S) = \sum_{g \in \Delta} g^r$
- Gap polynomial: $\Phi_S(z) = \sum_{g \in \Delta} z^g$
- Hilbert series: $H_S(z) = \sum_{s \in S} z^s$
- Product polynomial: $P_S(z) = \prod_{i=1}^{m}(1 - z^{d_i})$, $\pi_m = \prod_{i=1}^{m} d_i$
- Hilbert numerator: $Q_S(z)$ satisfying $H_S(z) = Q_S(z) / P_S(z)$
- Alternating power sums: $C_n(S) = \sum_{j \geq 1} c_j \cdot j^n$ where $Q_S(z) = 1 - \sum_{j \geq 1} c_j z^j$
- Invariants: $K_p(S) = \frac{(-1)^m \cdot p!}{(m+p)! \cdot \pi_m} \cdot C_{m+p}(S)$
- $T_n(\sigma) = n! \cdot [t^n] \prod_{i=1}^{m} \frac{e^{d_i t} - 1}{d_i t}$
- $T_n(\delta) = \frac{n!}{2^n} \cdot [t^n] \frac{t}{e^t - 1} \cdot \prod_{i=1}^{m} \frac{e^{d_i t} - 1}{d_i t}$

Fel's Conjecture states that for all $p \geq 0$:
$K_p(S) = \sum_{r=0}^{p} \binom{p}{r} \cdot T_{p-r}(\sigma) \cdot G_r(S) + \frac{2^{p+1}}{p+1} \cdot T_{p+1}(\delta)$
-/

-- A numerical semigroup is an additive submonoid of ℕ with finite complement
-- We define it as a structure with the required properties
structure NumericalSemigroup where
  carrier : Set ℕ
  zero_mem : 0 ∈ carrier
  add_mem : ∀ a b, a ∈ carrier → b ∈ carrier → a + b ∈ carrier
  finite_complement : (carrier)ᶜ.Finite

namespace NumericalSemigroup

-- The gap set (complement of the semigroup in ℕ)
noncomputable def gaps (S : NumericalSemigroup) : Finset ℕ := S.finite_complement.toFinset

-- Gap power sum: G_r(S) = sum_{g in Delta} g^r (Definition 3)
noncomputable def gapPowerSum (S : NumericalSemigroup) (r : ℕ) : ℚ :=
  ∑ g ∈ S.gaps, (g : ℚ) ^ r

-- Gap polynomial: Phi_S(z) = sum_{g in Delta} z^g (Definition 4)
noncomputable def gapPolynomial (S : NumericalSemigroup) : Polynomial ℚ :=
  ∑ g ∈ S.gaps, Polynomial.X ^ g

-- Hilbert series: H_S(z) = sum_{s in S} z^s (Definition 5)
-- Defined as a formal power series
-- We use Classical decidability since membership in S.carrier is not decidable in general
noncomputable def hilbertSeries (S : NumericalSemigroup) : PowerSeries ℚ :=
  PowerSeries.mk fun n => if Classical.propDecidable (n ∈ S.carrier) |>.decide then 1 else 0

-- Lemma 1 (Semigroup-Gap Decomposition): H_S(z) + Phi_S(z) = 1/(1-z)
-- Equivalently: H_S(z) + Phi_S(z) = sum_{n >= 0} z^n
theorem semigroupGapDecomposition (S : NumericalSemigroup) :
    S.hilbertSeries + (S.gapPolynomial : PowerSeries ℚ) = PowerSeries.mk (1 : ℕ → ℚ) := by
  sorry

end NumericalSemigroup

-- A generating set for a numerical semigroup consists of:
-- - A finite list of positive integers d_1, ..., d_m
-- - whose gcd is 1
-- - such that S equals the set of all non-negative integer linear combinations

structure NumericalSemigroupGenerators (S : NumericalSemigroup) where
  m : ℕ                           -- number of generators (embedding dimension)
  hm_pos : 0 < m                  -- at least one generator
  d : Fin m → ℕ                   -- the generators d_1, ..., d_m
  hd_pos : ∀ i, 0 < d i           -- each generator is positive
  hgcd : (Finset.univ.image d).gcd id = 1  -- gcd of generators is 1
  generates : S.carrier = {n : ℕ | ∃ (c : Fin m → ℕ), n = ∑ i, c i * d i}

namespace NumericalSemigroupGenerators

-- Product of generators: pi_m = prod_{i=1}^{m} d_i (Definition 6)
def pi_m {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) : ℕ :=
  ∏ i : Fin G.m, G.d i

-- Product polynomial: P_S(z) = prod_{i=1}^{m} (1 - z^{d_i}) (Definition 6)
noncomputable def productPolynomial {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) :
    Polynomial ℤ :=
  ∏ i : Fin G.m, (1 - Polynomial.X ^ (G.d i))

-- Helper: upper bound on the degree of Q_S
noncomputable def hilbertNumeratorDegBound {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) :
    ℕ :=
  G.productPolynomial.natDegree + S.gaps.sup id + 1

-- The Hilbert numerator polynomial Q_S(z) (Definition 7)
-- Defined using the Numerator Identity from Lemma 2:
-- Q_S(z) = P_S(z)/(1-z) - P_S(z) * Phi_S(z)
-- We compute coefficients directly: coeff n Q = (sum_{k=0}^n P.coeff k) - sum_{g in gaps, g <= n} P.coeff (n-g)
noncomputable def hilbertNumerator {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) :
    Polynomial ℤ :=
  let P := G.productPolynomial
  let bound := G.hilbertNumeratorDegBound
  ∑ n ∈ Finset.range bound,
    Polynomial.monomial n
      ((∑ k ∈ Finset.range (n + 1), P.coeff k) -
       (∑ g ∈ S.gaps.filter (· ≤ n), P.coeff (n - g)))

-- Lemma 2 (Numerator Identity): Q_S(z) = P_S(z)/(1-z) - P_S(z) * Phi_S(z)
-- The Hilbert numerator satisfies: Q_S * (1 - z) = P_S - P_S * Phi_S * (1 - z)
-- equivalently: P_S * H_S = Q_S (as power series, using H_S + Phi_S = 1/(1-z))
theorem numeratorIdentity {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) :
    S.hilbertSeries * (G.productPolynomial.map (Int.castRingHom ℚ) : PowerSeries ℚ) =
    (G.hilbertNumerator.map (Int.castRingHom ℚ) : PowerSeries ℚ) := by
  sorry

-- Coefficients for the alternating power sum (Definition 8)
-- Write Q_S(z) = 1 - sum_{j >= 1} c_j z^j
-- Then c_j = -(Q_S.coeff j) for j >= 1
noncomputable def numeratorCoeff {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S)
    (j : ℕ) : ℤ :=
  if j = 0 then 0 else -G.hilbertNumerator.coeff j

-- Alternating power sum: C_n(S) = sum_{j >= 1} c_j * j^n (Definition 8)
noncomputable def alternatingPowerSum {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S)
    (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range G.hilbertNumeratorDegBound,
    (G.numeratorCoeff j : ℚ) * (j : ℚ) ^ n

-- Invariant K_p: K_p(S) = ((-1)^m * p!) / ((m+p)! * pi_m) * C_{m+p}(S) (Definition 9)
noncomputable def K_invariant {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S)
    (p : ℕ) : ℚ :=
  ((-1 : ℚ) ^ G.m * (p.factorial : ℚ)) / (((G.m + p).factorial : ℚ) * (G.pi_m : ℚ)) *
    G.alternatingPowerSum (G.m + p)

-- For T_n(sigma) and T_n(delta), we define the generating power series (Definitions 10-11)

-- The power series (exp(d*t) - 1)/(d*t) = sum_{k>=0} d^k * t^k / (k+1)!
noncomputable def scaledExpFactor {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S)
    (i : Fin G.m) : PowerSeries ℚ :=
  PowerSeries.mk fun k => (G.d i : ℚ) ^ k / ((k + 1).factorial : ℚ)

-- A(t) = prod_{i=1}^{m} (exp(d_i t) - 1)/(d_i t) (Definition 10)
noncomputable def A_series {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) :
    PowerSeries ℚ :=
  ∏ i : Fin G.m, G.scaledExpFactor i

-- T_n(sigma) = n! * [t^n] A(t) (Definition 10)
noncomputable def T_sigma {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n : ℕ) : ℚ :=
  (n.factorial : ℚ) * (PowerSeries.coeff n) (G.A_series)

-- B(t) = (t / (exp(t) - 1)) * A(t) (Definition 11)
-- The factor t/(exp(t) - 1) is the Bernoulli generating function
-- Mathlib: bernoulliPowerSeries * (exp - 1) = X, so bernoulliPowerSeries = X / (exp - 1) = t/(e^t - 1)
noncomputable def B_series {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) :
    PowerSeries ℚ :=
  bernoulliPowerSeries ℚ * G.A_series

-- T_n(delta) = (n! / 2^n) * [t^n] B(t) (Definition 11)
noncomputable def T_delta {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n : ℕ) : ℚ :=
  (n.factorial : ℚ) / (2 ^ n : ℚ) * (PowerSeries.coeff n) (G.B_series)

end NumericalSemigroupGenerators

-- Main Statement: Fel's Conjecture
-- For every integer p >= 0:
-- K_p(S) = sum_{r=0}^{p} C(p,r) * T_{p-r}(sigma) * G_r(S) + (2^{p+1}/(p+1)) * T_{p+1}(delta)

theorem fels_conjecture (S : NumericalSemigroup) (G : NumericalSemigroupGenerators S) (p : ℕ) :
    G.K_invariant p =
      ∑ r ∈ Finset.range (p + 1),
        (p.choose r : ℚ) * G.T_sigma (p - r) * S.gapPowerSum r +
      (2 ^ (p + 1) : ℚ) / ((p : ℚ) + 1) * G.T_delta (p + 1) := by
  sorry
