module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Algebra.Ring.Parity

import Mathlib.Tactic

/-!
# Core Definitions and Ford's Lemma 7.2 for Carmichael's Totient Conjecture

Formalizes:
- `IsCarmichaelCounterexample x`: `x > 0` is the unique preimage of `φ(x)`, i.e., `A(φ(x)) = 1`.
- `rad n`: the squarefree kernel `s(n) = ∏ p ∈ n.primeFactors, p`.
- Fact 1 (`totient_even_of_ge_three`): `3 ≤ n → Even (Nat.totient n)`.
- Fact 2 (`totient_two_mul_odd`): `Odd n → Nat.totient (2 * n) = Nat.totient n`.
- Corollary (`four_dvd_counterexample`): `IsCarmichaelCounterexample x → 4 ∣ x`.
- Step 0 (`totient_div_of_dvd_div_rad`): properties of `e ∣ w / rad w`.
- Step 1 (`prime_dvd_of_ford_7_2`): `P = 1 + e * φ(d)` prime implies `P ∣ x`.
- Step 2 (`prime_sq_dvd_of_ford_7_2`): `P ∣ x` and all primes of `P - 1` divide `x` implies `P^2 ∣ x`.
- Full Ford Lemma 7.2 (`ford_lemma_7_2`): `P^2 ∣ x`.
-/

@[expose] public section

namespace CarmichaelTotient

/-- `x` is a **Carmichael totient counterexample** if `x > 0` and `x` is the unique
natural number with Euler totient equal to `φ(x)` (equivalently `A(φ(x)) = 1`). -/
def IsCarmichaelCounterexample (x : ℕ) : Prop :=
  0 < x ∧ ∀ y : ℕ, Nat.totient y = Nat.totient x → y = x

/-- The squarefree kernel (radical) `s(n) = ∏_{p ∣ n} p`, i.e., the product of
the distinct prime factors of `n`. -/
def rad (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, p

/-- **Fact 1**: `φ(n)` is even for every `n ≥ 3`. -/
theorem totient_even_of_ge_three {n : ℕ} (hn : 3 ≤ n) : Even (Nat.totient n) :=
  Nat.totient_even (by omega)

/-- **Fact 2**: For odd `n`, `φ(2 * n) = φ(n)`. -/
theorem totient_two_mul_odd {n : ℕ} (hn : Odd n) : Nat.totient (2 * n) = Nat.totient n := by
  have hcop : Nat.Coprime 2 n := by
    rw [Nat.coprime_two_left]
    exact hn
  rw [Nat.totient_mul hcop, Nat.totient_two, one_mul]

/-- **Corollary**: Every Carmichael totient counterexample is divisible by `4`. -/
theorem four_dvd_counterexample {x : ℕ} (hx : IsCarmichaelCounterexample x) : 4 ∣ x := by
  by_cases hodd : Odd x
  · have heq : Nat.totient (2 * x) = Nat.totient x := totient_two_mul_odd hodd
    have h2x : 2 * x = x := hx.2 (2 * x) heq
    have hxpos : 0 < x := hx.1
    omega
  · rw [Nat.not_odd_iff_even] at hodd
    rcases hodd with ⟨y, rfl⟩
    by_cases hy : Odd y
    · have heq : Nat.totient y = Nat.totient (y + y) := by
        rw [← two_mul]
        exact (totient_two_mul_odd hy).symm
      have hyx : y = y + y := hx.2 y heq
      have hxpos : 0 < y + y := hx.1
      omega
    · rw [Nat.not_odd_iff_even] at hy
      rcases hy with ⟨z, rfl⟩
      exact ⟨z, by ring⟩

/-- `rad n` is always positive. -/
theorem rad_pos (n : ℕ) : 0 < rad n := by
  unfold rad
  exact Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos

/-- Every prime factor of `n` divides `rad n`. -/
theorem dvd_rad_of_mem_primeFactors {n p : ℕ} (hp : p ∈ n.primeFactors) : p ∣ rad n := by
  unfold rad
  exact Finset.dvd_prod_of_mem _ hp

/-- `rad w` divides `w` for every `w : ℕ`. -/
theorem rad_dvd_self (w : ℕ) : rad w ∣ w := by
  unfold rad
  exact Nat.prod_primeFactors_dvd w

/-- Multiplying `z` by `m` whose prime factors all divide `z` multiplies `φ(z)` by `m`. -/
theorem totient_mul_of_primes_dvd :
    ∀ m z : ℕ, (∀ p : ℕ, Nat.Prime p → p ∣ m → p ∣ z) →
      Nat.totient (z * m) = Nat.totient z * m := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro z hprimes
    rcases eq_or_ne m 0 with rfl | hm0
    · simp
    rcases eq_or_ne m 1 with rfl | hm1
    · simp
    have hm_gt : 1 < m := by omega
    let p := m.minFac
    have hp : Nat.Prime p := Nat.minFac_prime hm1
    have hpm : p ∣ m := Nat.minFac_dvd m
    have hpz : p ∣ z := hprimes p hp hpm
    rcases hpm with ⟨m', hm'⟩
    have hm'_lt : m' < m := by
      have hp2 : 2 ≤ p := hp.two_le
      have hm'_pos : 0 < m' := by
        by_contra h
        have : m' = 0 := by omega
        rw [this, mul_zero] at hm'
        exact hm0 hm'
      nlinarith
    have hprimes' : ∀ q : ℕ, Nat.Prime q → q ∣ m' → q ∣ z := by
      intro q hq hqm'
      exact hprimes q hq (hm' ▸ dvd_mul_of_dvd_right hqm' p)
    have hih : Nat.totient (z * m') = Nat.totient z * m' := ih m' hm'_lt z hprimes'
    have hpdvd : p ∣ z * m' := dvd_mul_of_dvd_left hpz m'
    calc
      Nat.totient (z * m) = Nat.totient (p * (z * m')) := by rw [hm']; ring_nf
      _ = p * Nat.totient (z * m') := Nat.totient_mul_of_prime_of_dvd hp hpdvd
      _ = p * (Nat.totient z * m') := by rw [hih]
      _ = Nat.totient z * (p * m') := by ring
      _ = Nat.totient z * m := by rw [← hm']

/-- **Step 0**: If `0 < w` and `e ∣ w / rad w`, then `e ∣ w`, every prime divisor of `e`
divides `w`, and `φ(w / e) * e = φ(w)`. -/
theorem totient_div_of_dvd_div_rad {w e : ℕ} (hw : 0 < w) (he : e ∣ w / rad w) :
    e ∣ w ∧ (∀ p : ℕ, Nat.Prime p → p ∣ e → p ∣ w) ∧ Nat.totient (w / e) * e = Nat.totient w := by
  have hrad_dvd : rad w ∣ w := rad_dvd_self w
  have hw_eq : w / rad w * rad w = w := Nat.div_mul_cancel hrad_dvd
  have hq_pos : 0 < w / rad w := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, zero_mul] at hw_eq
    omega
  rcases he with ⟨t, ht⟩
  have he_pos : 0 < e := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, zero_mul] at ht
    omega
  have hw_fac : w = e * (t * rad w) := by
    calc
      w = w / rad w * rad w := hw_eq.symm
      _ = (e * t) * rad w := by rw [ht]
      _ = e * (t * rad w) := by ring
  have hedvd : e ∣ w := ⟨t * rad w, hw_fac⟩
  have hwe_eq : w / e = t * rad w := by
    conv_lhs => rw [hw_fac]
    exact Nat.mul_div_cancel_left (t * rad w) he_pos
  have hprimes_w : ∀ p : ℕ, Nat.Prime p → p ∣ e → p ∣ w := fun p _ hpe => dvd_trans hpe hedvd
  have hprimes_we : ∀ p : ℕ, Nat.Prime p → p ∣ e → p ∣ w / e := by
    intro p hp hpe
    have hpw : p ∣ w := hprimes_w p hp hpe
    have hmem : p ∈ w.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpw, by omega⟩
    have hprad : p ∣ rad w := dvd_rad_of_mem_primeFactors hmem
    rw [hwe_eq]
    exact dvd_mul_of_dvd_right hprad t
  have htot : Nat.totient (w / e) * e = Nat.totient w := by
    have h1 := totient_mul_of_primes_dvd e (w / e) hprimes_we
    rw [Nat.div_mul_cancel hedvd] at h1
    exact h1.symm
  exact ⟨hedvd, hprimes_w, htot⟩

/-- **Step 1 of Ford's Lemma 7.2**: Under the coprime-divisor and `e ∣ (x/d)/rad(x/d)`
hypotheses, if `P = 1 + e * φ(d)` is prime then `P ∣ x`. -/
theorem prime_dvd_of_ford_7_2 {x d e : ℕ}
    (hx : IsCarmichaelCounterexample x)
    (hd : d ∣ x)
    (hcop : Nat.Coprime d (x / d))
    (he : e ∣ (x / d) / rad (x / d))
    (hP : Nat.Prime (1 + e * Nat.totient d)) :
    (1 + e * Nat.totient d) ∣ x := by
  set w := x / d
  set P := 1 + e * Nat.totient d
  have hdw : d * w = x := Nat.mul_div_cancel' hd
  have hw_pos : 0 < w := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, mul_zero] at hdw
    have := hx.1
    omega
  obtain ⟨hedvd, _, htot_w⟩ := totient_div_of_dvd_div_rad hw_pos he
  by_contra hPndvd
  have hwe_dvd_x : w / e ∣ x := dvd_trans (Nat.div_dvd_of_dvd hedvd) (hdw ▸ dvd_mul_left w d)
  have hPndvd_we : ¬ P ∣ w / e := fun h => hPndvd (dvd_trans h hwe_dvd_x)
  have hcopP : Nat.Coprime P (w / e) := hP.coprime_iff_not_dvd.mpr hPndvd_we
  let y := P * (w / e)
  have hy_tot : Nat.totient y = Nat.totient x := by
    calc
      Nat.totient y = Nat.totient P * Nat.totient (w / e) := Nat.totient_mul hcopP
      _ = (P - 1) * Nat.totient (w / e) := by rw [Nat.totient_prime hP]
      _ = (e * Nat.totient d) * Nat.totient (w / e) := by simp [P]
      _ = Nat.totient d * (Nat.totient (w / e) * e) := by ring
      _ = Nat.totient d * Nat.totient w := by rw [htot_w]
      _ = Nat.totient (d * w) := (Nat.totient_mul hcop).symm
      _ = Nat.totient x := by rw [hdw]
  have hyx : y = x := hx.2 y hy_tot
  exact hPndvd (hyx ▸ dvd_mul_right P (w / e))

/-- General Step 2 swap: if `x` is a Carmichael counterexample, `P` is prime, `P ∣ x`, and
every prime dividing `P - 1` divides `x`, then `P ^ 2 ∣ x`. -/
theorem prime_sq_dvd_of_pred_primes_dvd {x P : ℕ}
    (hx : IsCarmichaelCounterexample x)
    (hP : Nat.Prime P)
    (hPdvd : P ∣ x)
    (hpred : ∀ q : ℕ, Nat.Prime q → q ∣ P - 1 → q ∣ x) :
    P ^ 2 ∣ x := by
  by_contra hsq
  set z := x / P
  have hPz : P * z = x := Nat.mul_div_cancel' hPdvd
  have hPndvd_z : ¬ P ∣ z := by
    intro h
    rcases h with ⟨k, hk⟩
    apply hsq
    refine ⟨k, ?_⟩
    calc
      x = P * z := hPz.symm
      _ = P * (P * k) := by rw [hk]
      _ = P ^ 2 * k := by ring
  have hcopPz : Nat.Coprime P z := hP.coprime_iff_not_dvd.mpr hPndvd_z
  have hP2 : 2 ≤ P := hP.two_le
  have hpred_z : ∀ q : ℕ, Nat.Prime q → q ∣ P - 1 → q ∣ z := by
    intro q hq hqPm1
    have hqx : q ∣ P * z := hPz ▸ hpred q hq hqPm1
    rcases hq.dvd_mul.mp hqx with hqP | hqz
    · have hqeq : q = P := (Nat.prime_dvd_prime_iff_eq hq hP).mp hqP
      have hle : q ≤ P - 1 := Nat.le_of_dvd (by omega) hqPm1
      omega
    · exact hqz
  let y := z * (P - 1)
  have hy_tot : Nat.totient y = Nat.totient x := by
    calc
      Nat.totient y = Nat.totient z * (P - 1) := totient_mul_of_primes_dvd (P - 1) z hpred_z
      _ = (P - 1) * Nat.totient z := by ring
      _ = Nat.totient P * Nat.totient z := by rw [Nat.totient_prime hP]
      _ = Nat.totient (P * z) := (Nat.totient_mul hcopPz).symm
      _ = Nat.totient x := by rw [hPz]
  have hyx : y = x := hx.2 y hy_tot
  have hPy : P ∣ z * (P - 1) := by rwa [← hyx] at hPdvd
  rcases hP.dvd_mul.mp hPy with hPz' | hPPm1
  · exact hPndvd_z hPz'
  · have hle : P ≤ P - 1 := Nat.le_of_dvd (by omega) hPPm1
    omega

/-- **Step 2 of Ford's Lemma 7.2**: Given `P = 1 + e * φ(d) ∣ x`, the radical condition
`rad (φ(d)) ∣ x` and `e ∣ (x/d) / rad(x/d)` force `P ^ 2 ∣ x`. -/
theorem prime_sq_dvd_of_ford_7_2 {x d e : ℕ}
    (hx : IsCarmichaelCounterexample x)
    (hd : d ∣ x)
    (hrad : rad (Nat.totient d) ∣ x)
    (he : e ∣ (x / d) / rad (x / d))
    (hP : Nat.Prime (1 + e * Nat.totient d))
    (hPdvd : (1 + e * Nat.totient d) ∣ x) :
    (1 + e * Nat.totient d) ^ 2 ∣ x := by
  set w := x / d
  have hdw : d * w = x := Nat.mul_div_cancel' hd
  have hd_pos : 0 < d := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, zero_mul] at hdw
    have := hx.1
    omega
  have hw_pos : 0 < w := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, mul_zero] at hdw
    have := hx.1
    omega
  obtain ⟨_, hprimes_w, _⟩ := totient_div_of_dvd_div_rad hw_pos he
  apply prime_sq_dvd_of_pred_primes_dvd hx hP hPdvd
  intro q hq hqPm1
  have hqmul : q ∣ e * Nat.totient d := by simpa using hqPm1
  rcases hq.dvd_mul.mp hqmul with hqe | hqd
  · exact dvd_trans (hprimes_w q hq hqe) (hdw ▸ dvd_mul_left w d)
  · have htot_pos : 0 < Nat.totient d := Nat.totient_pos.mpr hd_pos
    have hmem : q ∈ (Nat.totient d).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hq, hqd, by omega⟩
    exact dvd_trans (dvd_rad_of_mem_primeFactors hmem) hrad

/-- **Ford's Lemma 7.2** (Ford 1998, Ramanujan J. 2; Carmichael 1922 / Klee 1947):
If `x` is a Carmichael counterexample, `d` is a unitary divisor of `x` (`d ∣ x` and
`Nat.Coprime d (x / d)`), `rad (φ(d)) ∣ x`, `e ∣ (x / d) / rad (x / d)`, and
`P = 1 + e * φ(d)` is prime, then `P ^ 2 ∣ x`. -/
theorem ford_lemma_7_2 {x d e : ℕ}
    (hx : IsCarmichaelCounterexample x)
    (hd : d ∣ x)
    (hcop : Nat.Coprime d (x / d))
    (hrad : rad (Nat.totient d) ∣ x)
    (he : e ∣ (x / d) / rad (x / d))
    (hP : Nat.Prime (1 + e * Nat.totient d)) :
    (1 + e * Nat.totient d) ^ 2 ∣ x :=
  prime_sq_dvd_of_ford_7_2 hx hd hrad he hP (prime_dvd_of_ford_7_2 hx hd hcop he hP)

end CarmichaelTotient
