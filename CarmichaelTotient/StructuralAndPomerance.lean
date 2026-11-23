module

public import CarmichaelTotient.Carmichael1922

import Mathlib.Tactic

/-!
# Pomerance's Criterion, Klee's Reduced Counterexamples, and Erdős's Multiplication Theorem

Formalizes structural and valence-multiplication theorems for Euler's totient function and
Carmichael's Totient Conjecture:

1. **Exact `p`-adic valuation of `φ(n)`** (`totient_factorization_eq` and `prime_dvd_totient_iff`):
   For `n ≠ 0` and prime `p`,
   `v_p(φ(n)) = (v_p(n) - 1) + ∑_{q ∈ primeFactors(n) \ {p}} v_p(q - 1)`,
   hence `p ∣ φ(n) ↔ p ^ 2 ∣ n ∨ ∃ q ∈ n.primeFactors, p ∣ q - 1`.
2. **Pomerance's (1974) Sufficient Condition** (`pomerance_sufficient_condition`, Proc. AMS 43):
   If `0 < x` and `∀ p, p.Prime → (p - 1) ∣ φ(x) → p ^ 2 ∣ x`, then `IsCarmichaelCounterexample x`
   (`A(φ(x)) = 1`), together with the exclusion corollary
   `pomerance_conjecture_excludes_pomerance_numbers`.
3. **Klee's (1947) Reduced & Minimal Counterexample Theorems** (Bull. AMS 53, Theorem 2 &
   Corollary 2.1):
   - Every counterexample has a reduced counterexample divisor (`exists_reduced_counterexample_dvd`),
     and if any counterexample exists there is a minimal one (`exists_minimal_counterexample`).
   - `not_eight_dvd_of_reduced` / `exact_four_dvd_of_reduced`: every reduced (hence every minimal)
     counterexample satisfies `4 ∣ x ∧ ¬ 8 ∣ x` (`2 ^ 2 ∥ x`).
   - `not_fermat_prime_dvd_of_reduced`: no prime of the form `2 ^ m + 1` with `2 ≤ m` divides a
     reduced (or minimal) counterexample; in particular `5 ∤ x`, `17 ∤ x`, `257 ∤ x`, `65537 ∤ x`.
4. **Erdős's (1958) Valence-Preserving Fiber Bijection & Counterexample Multiplication**
   (Acta Arith. 4):
   - `erdos_1958_totient_fiber_eq`: for any `m > 0`, `k > 0`, prime `q > k * m + 1`, and prime
     `P = 1 + k * q` such that `1 + j * q` is composite for all other divisors `j ∣ k * m`,
     `φ(y) = (P - 1) * m ↔ ∃ z, φ(z) = m ∧ y = P * z` (exact valence preservation `A((P-1)m) = A(m)`),
     witnessed non-vacuously at `(m, k, q, P) = (1, 2, 5, 11)` (`totient_eq_ten_iff`).
   - `erdos_1958_counterexample_step` & `erdos_1958_infinitude_from_sieve`: multiplying any
     counterexample `x` by such an Erdős prime `P` produces a strictly larger (unreduced)
     counterexample `P * x` with `P ∥ P * x`, yielding infinitely many counterexamples from
     Erdős's Brun-sieve prime supply.
-/

@[expose] public section

namespace CarmichaelTotient

/-! ## Exact prime-power valuation of `φ(n)` -/

/-- Exact `p`-adic valuation formula for `φ(n)` (`n ≠ 0`, `p` prime):
`(φ(n)).factorization p = (n.factorization p - 1) + ∑ q ∈ n.primeFactors.erase p, (q - 1).factorization p`. -/
theorem totient_factorization_eq {n p : ℕ} (hn : n ≠ 0) (hp : Nat.Prime p) :
    (Nat.totient n).factorization p =
      (n.factorization p - 1) + ∑ q ∈ n.primeFactors.erase p, (q - 1).factorization p := by
  rw [Nat.totient_eq_prod_factorization hn]
  change (∏ q ∈ n.factorization.support, (q ^ (n.factorization q - 1) * (q - 1))).factorization p = _
  rw [Nat.support_factorization]
  have hne : ∀ q ∈ n.primeFactors, q ^ (n.factorization q - 1) * (q - 1) ≠ 0 := by
    intro q hq
    have hqp : Nat.Prime q := Nat.prime_of_mem_primeFactors hq
    have hq2 : 2 ≤ q := hqp.two_le
    exact mul_ne_zero (pow_ne_zero _ hqp.ne_zero) (by omega)
  rw [Nat.factorization_prod hne, Finsupp.finsetSum_apply]
  have hterm_other : ∀ q ∈ n.primeFactors.erase p,
      (q ^ (n.factorization q - 1) * (q - 1)).factorization p = (q - 1).factorization p := by
    intro q hq
    have hq_mem : q ∈ n.primeFactors := Finset.mem_of_mem_erase hq
    have hqp : Nat.Prime q := Nat.prime_of_mem_primeFactors hq_mem
    have hq_ne : q ≠ p := Finset.ne_of_mem_erase hq
    have hq2 : 2 ≤ q := hqp.two_le
    rw [Nat.factorization_mul (pow_ne_zero _ hqp.ne_zero) (by omega), Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, hqp.factorization,
      Finsupp.single_eq_of_ne (Ne.symm hq_ne), smul_zero, zero_add]
  by_cases hmem : p ∈ n.primeFactors
  · rw [← Finset.add_sum_erase _ _ hmem]
    congr 1
    · have hp2 : 2 ≤ p := hp.two_le
      have hpm1_ndvd : ¬ p ∣ p - 1 := by
        intro hd
        have := Nat.le_of_dvd (by omega) hd
        omega
      rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (by omega), Finsupp.add_apply,
        Nat.factorization_pow, Finsupp.smul_apply, hp.factorization_self, smul_eq_mul, mul_one,
        Nat.factorization_eq_zero_of_not_dvd hpm1_ndvd, add_zero]
    · exact Finset.sum_congr rfl hterm_other
  · have hfp0 : n.factorization p = 0 := by
      rw [Nat.mem_primeFactors] at hmem
      by_contra hne0
      exact hmem ⟨hp, Nat.dvd_of_factorization_pos hne0, hn⟩
    have herase : n.primeFactors.erase p = n.primeFactors := Finset.erase_eq_of_notMem hmem
    rw [hfp0, Nat.zero_sub, zero_add]
    conv_lhs => rw [← herase]
    exact Finset.sum_congr rfl hterm_other

/-- A prime `p` divides `φ(n)` (`n ≠ 0`) if and only if either `p ^ 2 ∣ n` or `p ∣ q - 1` for some
prime factor `q` of `n`. -/
theorem prime_dvd_totient_iff {n p : ℕ} (hn : n ≠ 0) (hp : Nat.Prime p) :
    p ∣ Nat.totient n ↔ p ^ 2 ∣ n ∨ ∃ q ∈ n.primeFactors, p ∣ q - 1 := by
  have htot_pos : 0 < Nat.totient n := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn)
  have htot_ne : Nat.totient n ≠ 0 := by omega
  have hdvd_iff : p ∣ Nat.totient n ↔ 0 < (Nat.totient n).factorization p := by
    constructor
    · intro hd
      exact hp.factorization_pos_of_dvd htot_ne hd
    · intro hpos
      exact Nat.dvd_of_factorization_pos (by omega)
  rw [hdvd_iff, totient_factorization_eq hn hp]
  constructor
  · intro hpos
    by_cases h1 : 0 < n.factorization p - 1
    · left
      have h2 : 2 ≤ n.factorization p := by omega
      rw [← Nat.factorization_le_iff_dvd (pow_ne_zero 2 hp.ne_zero) hn]
      intro r
      by_cases hr : r = p
      · subst hr
        rw [Nat.factorization_pow, Finsupp.smul_apply, hp.factorization_self]
        simpa using h2
      · rw [Nat.factorization_pow, Finsupp.smul_apply, hp.factorization,
          Finsupp.single_eq_of_ne hr]
        simp
    · right
      have h10 : n.factorization p - 1 = 0 := by omega
      rw [h10, zero_add] at hpos
      obtain ⟨q, hq_erase, hq_pos⟩ := Finset.sum_pos_iff.mp hpos
      have hq_mem : q ∈ n.primeFactors := Finset.mem_of_mem_erase hq_erase
      exact ⟨q, hq_mem, Nat.dvd_of_factorization_pos (by omega)⟩
  · rintro (hsq | ⟨q, hq_mem, hp_qm1⟩)
    · have hle := (Nat.factorization_le_iff_dvd (pow_ne_zero 2 hp.ne_zero) hn).mpr hsq p
      rw [Nat.factorization_pow, Finsupp.smul_apply, hp.factorization_self] at hle
      have h2 : 2 ≤ n.factorization p := by simpa using hle
      omega
    · have hqp : Nat.Prime q := Nat.prime_of_mem_primeFactors hq_mem
      have hq2 : 2 ≤ q := hqp.two_le
      have hq_ne_p : q ≠ p := by
        intro heq
        subst heq
        have := Nat.le_of_dvd (by omega) hp_qm1
        omega
      have hq_erase : q ∈ n.primeFactors.erase p := Finset.mem_erase.mpr ⟨hq_ne_p, hq_mem⟩
      have hfp_pos : 0 < (q - 1).factorization p :=
        hp.factorization_pos_of_dvd (by omega) hp_qm1
      have hsum_pos : 0 < ∑ r ∈ n.primeFactors.erase p, (r - 1).factorization p :=
        lt_of_lt_of_le hfp_pos
          (Finset.single_le_sum (f := fun r => (r - 1).factorization p)
            (fun _ _ => Nat.zero_le _) hq_erase)
      omega

/-! ## Pomerance's (1974) Sufficient Condition and Prime Conjecture Link -/

/-- **Pomerance's Sufficient Condition** (Pomerance, Proc. AMS 43, 1974, Theorem):
If `x > 0` satisfies `(p - 1) ∣ φ(x) → p ^ 2 ∣ x` for every prime `p`, then `x` is a
Carmichael totient counterexample (`A(φ(x)) = 1`). -/
theorem pomerance_sufficient_condition {x : ℕ} (hx : 0 < x)
    (hpom : ∀ p : ℕ, Nat.Prime p → (p - 1) ∣ Nat.totient x → p ^ 2 ∣ x) :
    IsCarmichaelCounterexample x := by
  refine ⟨hx, ?_⟩
  intro y hy
  have htot_pos : 0 < Nat.totient x := Nat.totient_pos.mpr hx
  have hy_pos : 0 < y := by
    by_contra h0
    have hy0 : y = 0 := by omega
    rw [hy0, Nat.totient_zero] at hy
    omega
  have hx_ne : x ≠ 0 := by omega
  have hy_ne : y ≠ 0 := by omega
  by_contra hne
  have hfac_ne : x.factorization ≠ y.factorization := fun h =>
    hne (Nat.eq_of_factorization_eq hy_ne hx_ne fun p =>
      (congrFun (congrArg DFunLike.coe h) p).symm)
  let D := (x.primeFactors ∪ y.primeFactors).filter fun p => x.factorization p ≠ y.factorization p
  have hD_nonempty : D.Nonempty := by
    by_contra hD_empty
    rw [Finset.not_nonempty_iff_eq_empty] at hD_empty
    apply hfac_ne
    ext p
    by_cases hp : p ∈ x.primeFactors ∪ y.primeFactors
    · by_contra hp_ne
      have hmem : p ∈ D := Finset.mem_filter.mpr ⟨hp, hp_ne⟩
      rw [hD_empty] at hmem
      simp at hmem
    · simp only [Finset.mem_union, not_or] at hp
      have hx0 : x.factorization p = 0 := by
        by_contra h
        exact hp.1 (Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors
          (Nat.support_factorization x ▸ Finsupp.mem_support_iff.mpr h),
          Nat.dvd_of_factorization_pos h, hx_ne⟩)
      have hy0 : y.factorization p = 0 := by
        by_contra h
        exact hp.2 (Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors
          (Nat.support_factorization y ▸ Finsupp.mem_support_iff.mpr h),
          Nat.dvd_of_factorization_pos h, hy_ne⟩)
      rw [hx0, hy0]
  let p := D.max' hD_nonempty
  have hpD : p ∈ D := Finset.max'_mem D hD_nonempty
  obtain ⟨hp_union, hp_diff⟩ := Finset.mem_filter.mp hpD
  have hp_prime : Nat.Prime p := by
    rcases Finset.mem_union.mp hp_union with hpx | hpy
    · exact Nat.prime_of_mem_primeFactors hpx
    · exact Nat.prime_of_mem_primeFactors hpy
  have hpm1_dvd : (p - 1) ∣ Nat.totient x := by
    rcases Finset.mem_union.mp hp_union with hpx | hpy
    · have hpx_dvd : p ∣ x := Nat.dvd_of_mem_primeFactors hpx
      have := Nat.totient_dvd_of_dvd hpx_dvd
      rwa [Nat.totient_prime hp_prime] at this
    · have hpy_dvd : p ∣ y := Nat.dvd_of_mem_primeFactors hpy
      have := Nat.totient_dvd_of_dvd hpy_dvd
      rwa [Nat.totient_prime hp_prime, hy] at this
  have hp_sq_x : p ^ 2 ∣ x := hpom p hp_prime hpm1_dvd
  have hfx_ge2 : 2 ≤ x.factorization p := by
    have hle := (Nat.factorization_le_iff_dvd (pow_ne_zero 2 hp_prime.ne_zero) hx_ne).mpr hp_sq_x p
    rw [Nat.factorization_pow, Finsupp.smul_apply, hp_prime.factorization_self] at hle
    simpa using hle
  -- Every q > p has equal valuation in x and y, and every q < p has (q - 1).factorization p = 0.
  have hsum_eq :
      (∑ q ∈ x.primeFactors.erase p, (q - 1).factorization p) =
        ∑ q ∈ y.primeFactors.erase p, (q - 1).factorization p := by
    have hfilter_eq :
        (x.primeFactors.erase p).filter (fun q => p < q) =
          (y.primeFactors.erase p).filter (fun q => p < q) := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨hq_ne, hqx⟩, hpq⟩
        refine ⟨⟨hq_ne, ?_⟩, hpq⟩
        have hq_eq : x.factorization q = y.factorization q := by
          by_contra hne_q
          have hqD : q ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hqx, hne_q⟩
          have hle := Finset.le_max' D q hqD
          omega
        have hfx_pos : 0 < x.factorization q :=
          (Nat.prime_of_mem_primeFactors hqx).factorization_pos_of_dvd hx_ne
            (Nat.dvd_of_mem_primeFactors hqx)
        have hfy_pos : 0 < y.factorization q := by omega
        exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hqx,
          Nat.dvd_of_factorization_pos (by omega), hy_ne⟩
      · rintro ⟨⟨hq_ne, hqy⟩, hpq⟩
        refine ⟨⟨hq_ne, ?_⟩, hpq⟩
        have hq_eq : x.factorization q = y.factorization q := by
          by_contra hne_q
          have hqD : q ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_union_right _ hqy, hne_q⟩
          have hle := Finset.le_max' D q hqD
          omega
        have hfy_pos : 0 < y.factorization q :=
          (Nat.prime_of_mem_primeFactors hqy).factorization_pos_of_dvd hy_ne
            (Nat.dvd_of_mem_primeFactors hqy)
        have hfx_pos : 0 < x.factorization q := by omega
        exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hqy,
          Nat.dvd_of_factorization_pos (by omega), hx_ne⟩
    have hzero_le : ∀ s : Finset ℕ, (∀ q ∈ s, 2 ≤ q) →
        ∑ q ∈ s, (q - 1).factorization p =
          ∑ q ∈ s.filter (fun q => p < q), (q - 1).factorization p := by
      intro s hs
      rw [← Finset.sum_filter_add_sum_filter_not s (fun q => p < q)]
      suffices h0 : ∑ q ∈ s.filter (fun q => ¬ p < q), (q - 1).factorization p = 0 by
        omega
      refine Finset.sum_eq_zero fun q hq => ?_
      obtain ⟨hqs, hle⟩ := Finset.mem_filter.mp hq
      have hq2 : 2 ≤ q := hs q hqs
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hd
      have := Nat.le_of_dvd (by omega) hd
      omega
    rw [hzero_le (x.primeFactors.erase p) (fun q hq =>
        (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hq)).two_le),
      hzero_le (y.primeFactors.erase p) (fun q hq =>
        (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hq)).two_le),
      hfilter_eq]
  have htot_fac : (Nat.totient y).factorization p = (Nat.totient x).factorization p := by
    rw [hy]
  rw [totient_factorization_eq hy_ne hp_prime, totient_factorization_eq hx_ne hp_prime,
    ← hsum_eq] at htot_fac
  have hsub_eq : y.factorization p - 1 = x.factorization p - 1 := by omega
  have hval_eq : x.factorization p = y.factorization p := by omega
  exact hp_diff hval_eq

/-- **Pomerance's Prime Conjecture Excludes Pomerance Numbers** (Pomerance 1974):
If for every finite nonempty set `S` of primes there exists a prime `p ∉ S` with
`(p - 1) ∣ ∏ q ∈ S, q * (q - 1)`, then no `x > 0` satisfies Pomerance's sufficient condition. -/
theorem pomerance_conjecture_excludes_pomerance_numbers
    (hconj : ∀ S : Finset ℕ, S.Nonempty → (∀ q ∈ S, Nat.Prime q) →
      ∃ p : ℕ, Nat.Prime p ∧ p ∉ S ∧ (p - 1) ∣ ∏ q ∈ S, q * (q - 1))
    {x : ℕ} (hx : 0 < x)
    (hpom : ∀ p : ℕ, Nat.Prime p → (p - 1) ∣ Nat.totient x → p ^ 2 ∣ x) :
    False := by
  have hx_ne : x ≠ 0 := by omega
  have h4 : 2 ^ 2 ∣ x := hpom 2 Nat.prime_two (by norm_num)
  have h2mem : 2 ∈ x.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, dvd_trans (by norm_num : 2 ∣ 4) h4, hx_ne⟩
  obtain ⟨p, hp, hp_notMem, hpm1⟩ :=
    hconj x.primeFactors ⟨2, h2mem⟩ (fun q hq => Nat.prime_of_mem_primeFactors hq)
  have hprod_dvd : (∏ q ∈ x.primeFactors, q * (q - 1)) ∣ Nat.totient x := by
    rw [Nat.totient_eq_prod_factorization hx_ne]
    change _ ∣ ∏ q ∈ x.factorization.support, (q ^ (x.factorization q - 1) * (q - 1))
    rw [Nat.support_factorization]
    refine Finset.prod_dvd_prod_of_dvd _ _ fun q hq => ?_
    have hqp : Nat.Prime q := Nat.prime_of_mem_primeFactors hq
    have hqm1_dvd : (q - 1) ∣ Nat.totient x := by
      have := Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hq)
      rwa [Nat.totient_prime hqp] at this
    have hq_sq : q ^ 2 ∣ x := hpom q hqp hqm1_dvd
    have hle := (Nat.factorization_le_iff_dvd (pow_ne_zero 2 hqp.ne_zero) hx_ne).mpr hq_sq q
    rw [Nat.factorization_pow, Finsupp.smul_apply, hqp.factorization_self] at hle
    have hfq : 2 ≤ x.factorization q := by simpa using hle
    refine mul_dvd_mul_right ?_ (q - 1)
    simpa using Nat.pow_dvd_pow q (by omega : 1 ≤ x.factorization q - 1)
  have hp_sq : p ^ 2 ∣ x := hpom p hp (dvd_trans hpm1 hprod_dvd)
  have hp_dvd : p ∣ x := dvd_trans (dvd_pow_self p (by norm_num : 2 ≠ 0)) hp_sq
  exact hp_notMem (Nat.mem_primeFactors.mpr ⟨hp, hp_dvd, hx_ne⟩)

/-! ## Klee's (1947) Reduced & Minimal Counterexample Theorems -/

/-- `x` is a **reduced Carmichael counterexample** (Klee 1947, §2) if `x` is a Carmichael
counterexample and no proper divisor of `x` is a Carmichael counterexample. -/
def IsReducedCounterexample (x : ℕ) : Prop :=
  IsCarmichaelCounterexample x ∧ ∀ d : ℕ, d ∣ x → d < x → ¬ IsCarmichaelCounterexample d

/-- `x` is the **minimal Carmichael counterexample** if `x` is a Carmichael counterexample and
no smaller natural number is a Carmichael counterexample. -/
def IsMinimalCounterexample (x : ℕ) : Prop :=
  IsCarmichaelCounterexample x ∧ ∀ y : ℕ, y < x → ¬ IsCarmichaelCounterexample y

/-- Every minimal Carmichael counterexample is reduced. -/
theorem isReduced_of_isMinimal {x : ℕ} (hx : IsMinimalCounterexample x) :
    IsReducedCounterexample x :=
  ⟨hx.1, fun d _ hlt => hx.2 d hlt⟩

/-- If any Carmichael counterexample exists, then a minimal Carmichael counterexample exists. -/
theorem exists_minimal_counterexample (h : ∃ x : ℕ, IsCarmichaelCounterexample x) :
    ∃ x₀ : ℕ, IsMinimalCounterexample x₀ := by
  classical
  exact ⟨Nat.find h, Nat.find_spec h, fun y hy => Nat.find_min h hy⟩

/-- Every Carmichael counterexample has a reduced Carmichael counterexample divisor. -/
theorem exists_reduced_counterexample_dvd :
    ∀ x : ℕ, IsCarmichaelCounterexample x → ∃ d : ℕ, d ∣ x ∧ IsReducedCounterexample d := by
  intro x
  induction x using Nat.strong_induction_on with
  | h x ih =>
    intro hx
    by_cases hred : ∀ d : ℕ, d ∣ x → d < x → ¬ IsCarmichaelCounterexample d
    · exact ⟨x, dvd_rfl, hx, hred⟩
    · push Not at hred
      obtain ⟨d, hd_dvd, hd_lt, hd_ce⟩ := hred
      obtain ⟨r, hr_dvd, hr_red⟩ := ih d hd_lt hd_ce
      exact ⟨r, dvd_trans hr_dvd hd_dvd, hr_red⟩

/-- **Klee (1947), Theorem 2(a)**: `8` does not divide any reduced Carmichael counterexample. -/
theorem not_eight_dvd_of_reduced {x : ℕ} (hx : IsReducedCounterexample x) : ¬ (8 ∣ x) := by
  rcases hx with ⟨hx_ce, hred⟩
  rintro ⟨k, hk⟩
  have hk_pos : 0 < k := by
    have := hx_ce.1
    omega
  let z := 4 * k
  have hxz : x = 2 * z := by
    dsimp [z]
    omega
  have hz_pos : 0 < z := by omega
  have hz_dvd : z ∣ x := ⟨2, by omega⟩
  have hz_lt : z < x := by omega
  have hnot_z : ¬ IsCarmichaelCounterexample z := hred z hz_dvd hz_lt
  have hex_y : ∃ y : ℕ, Nat.totient y = Nat.totient z ∧ y ≠ z := by
    unfold IsCarmichaelCounterexample at hnot_z
    push Not at hnot_z
    exact hnot_z hz_pos
  obtain ⟨y, hy_tot, hy_ne⟩ := hex_y
  have hx_tot : Nat.totient x = 2 * Nat.totient z := by
    rw [hxz]
    exact Nat.totient_mul_of_prime_of_dvd Nat.prime_two ⟨2 * k, by dsimp [z]; ring⟩
  by_cases hy2 : 2 ∣ y
  · have h2y_tot : Nat.totient (2 * y) = Nat.totient x := by
      rw [Nat.totient_mul_of_prime_of_dvd Nat.prime_two hy2, hy_tot, hx_tot]
    have h2y_eq : 2 * y = x := hx_ce.2 (2 * y) h2y_tot
    exact hy_ne (by omega)
  · have hy_odd : Odd y := Nat.odd_iff.mpr (by omega)
    have hcop4y : Nat.Coprime 4 y := by
      have hcop2y : Nat.Coprime 2 y := Nat.coprime_two_left.mpr hy_odd
      have : (4 : ℕ) = 2 ^ 2 := by norm_num
      rw [this]
      exact hcop2y.pow_left 2
    have h4y_tot : Nat.totient (4 * y) = Nat.totient x := by
      rw [Nat.totient_mul hcop4y, show Nat.totient 4 = 2 by decide, hy_tot, hx_tot]
    have h4y_eq : 4 * y = x := hx_ce.2 (4 * y) h4y_tot
    apply hy2
    exact ⟨k, by omega⟩

/-- Every reduced Carmichael counterexample is divisible by `4` to the exact first power of `4`
(`4 ∣ x ∧ ¬ 8 ∣ x`, i.e., `2 ^ 2 ∥ x`). -/
theorem exact_four_dvd_of_reduced {x : ℕ} (hx : IsReducedCounterexample x) :
    4 ∣ x ∧ ¬ (8 ∣ x) :=
  ⟨four_dvd_counterexample hx.1, not_eight_dvd_of_reduced hx⟩

/-- **Klee (1947), Corollary 2.1**: No prime of the form `F = 2 ^ m + 1` with `2 ≤ m` (in
particular, no Fermat prime greater than `3`) divides a reduced Carmichael counterexample. -/
theorem not_fermat_prime_dvd_of_reduced {x m : ℕ} (hx : IsReducedCounterexample x)
    (hm : 2 ≤ m) (hF : Nat.Prime (2 ^ m + 1)) :
    ¬ ((2 ^ m + 1) ∣ x) := by
  have hnot8 : ¬ (8 ∣ x) := not_eight_dvd_of_reduced hx
  rcases hx with ⟨hx_ce, hred⟩
  set F := 2 ^ m + 1
  have h2m_pos : 0 < 2 ^ m := pow_pos (by norm_num) m
  have h2m_ge4 : 4 ≤ 2 ^ m := by
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hm
    simpa using this
  have hF_ge5 : 5 ≤ F := by omega
  have hF_sub1 : F - 1 = 2 ^ m := by omega
  have hx_ne : x ≠ 0 := Nat.ne_of_gt hx_ce.1
  intro hFdvd
  let a := x.factorization F
  have ha_pos : 1 ≤ a := hF.factorization_pos_of_dvd hx_ne hFdvd
  have hFa_dvd : F ^ a ∣ x := Nat.ordProj_dvd x F
  let u := x / F ^ a
  have hxu : F ^ a * u = x := Nat.mul_div_cancel' hFa_dvd
  have hcopFu : Nat.Coprime F u := by
    have hndvd : ¬ F ∣ u := Nat.not_dvd_ordCompl hF hx_ne
    exact hF.coprime_iff_not_dvd.mpr hndvd
  have hu_pos : 0 < u := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, mul_zero] at hxu
    exact hx_ne hxu.symm
  have hu_dvd : u ∣ x := ⟨F ^ a, by rw [← hxu, mul_comm]⟩
  have hFa_gt1 : 1 < F ^ a := by
    calc
      1 < F ^ 1 := by simp; omega
      _ ≤ F ^ a := Nat.pow_le_pow_right (by omega) ha_pos
  have hu_lt : u < x := by nlinarith
  have hnot_u : ¬ IsCarmichaelCounterexample u := hred u hu_dvd hu_lt
  have hex_y : ∃ y : ℕ, Nat.totient y = Nat.totient u ∧ y ≠ u := by
    unfold IsCarmichaelCounterexample at hnot_u
    push Not at hnot_u
    exact hnot_u hu_pos
  obtain ⟨y, hy_tot, hy_ne⟩ := hex_y
  have hy_ne0 : y ≠ 0 := by
    intro h0
    rw [h0, Nat.totient_zero] at hy_tot
    have := Nat.totient_pos.mpr hu_pos
    omega
  have hx_tot : Nat.totient x = F ^ (a - 1) * 2 ^ m * Nat.totient u := by
    rw [← hxu, Nat.totient_mul (hcopFu.pow_left a), Nat.totient_prime_pow hF ha_pos, hF_sub1]
  by_cases hFy : F ∣ y
  · let b := y.factorization F
    have hb_pos : 1 ≤ b := hF.factorization_pos_of_dvd hy_ne0 hFy
    have hFb_dvd : F ^ b ∣ y := Nat.ordProj_dvd y F
    let w := y / F ^ b
    have hyw : F ^ b * w = y := Nat.mul_div_cancel' hFb_dvd
    have hcopFw : Nat.Coprime F w :=
      hF.coprime_iff_not_dvd.mpr (Nat.not_dvd_ordCompl hF hy_ne0)
    have hy_tot_eq : Nat.totient y = F ^ (b - 1) * 2 ^ m * Nat.totient w := by
      rw [← hyw, Nat.totient_mul (hcopFw.pow_left b), Nat.totient_prime_pow hF hb_pos, hF_sub1]
    have hcopF2 : Nat.Coprime F 2 := by
      rw [Nat.coprime_primes hF Nat.prime_two]
      omega
    have hab_pos : 1 ≤ a + b - 1 := by omega
    have hab_eq : a + b - 1 - 1 = (a - 1) + (b - 1) := by omega
    by_cases hw2 : 2 ∣ w
    · let y' := F ^ (a + b - 1) * (2 ^ m * w)
      have hcop_y' : Nat.Coprime (F ^ (a + b - 1)) (2 ^ m * w) :=
        ((hcopF2.pow_right m).mul_right hcopFw).pow_left (a + b - 1)
      have h2mw_tot : Nat.totient (2 ^ m * w) = 2 ^ m * Nat.totient w := by
        rw [mul_comm]
        have hpr : ∀ q : ℕ, Nat.Prime q → q ∣ 2 ^ m → q ∣ w := by
          intro q hq hqd
          have hq2 : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow hqd)
          rwa [hq2]
        rw [totient_mul_of_primes_dvd (2 ^ m) w hpr, mul_comm]
      have hy'_tot : Nat.totient y' = Nat.totient x := by
        dsimp [y']
        rw [Nat.totient_mul hcop_y', Nat.totient_prime_pow hF hab_pos, hF_sub1, h2mw_tot,
          hab_eq, pow_add, hx_tot, ← hy_tot, hy_tot_eq]
        ring
      have hy'_eq : y' = x := hx_ce.2 y' hy'_tot
      apply hnot8
      rw [← hy'_eq]
      refine dvd_mul_of_dvd_right ?_ _
      have h4_dvd_2m : 4 ∣ 2 ^ m := by
        simpa using Nat.pow_dvd_pow 2 hm
      rcases h4_dvd_2m with ⟨c1, hc1⟩
      rcases hw2 with ⟨c2, hc2⟩
      exact ⟨c1 * c2, by rw [hc1, hc2]; ring⟩
    · have hw_odd : Odd w := Nat.odd_iff.mpr (by omega)
      let y' := 2 ^ (m + 1) * (F ^ (a + b - 1) * w)
      have hcop_2_Fw : Nat.Coprime (2 ^ (m + 1)) (F ^ (a + b - 1) * w) := by
        have hcop2w : Nat.Coprime 2 w := Nat.coprime_two_left.mpr hw_odd
        exact ((hcopF2.symm.pow_right (a + b - 1)).mul_right hcop2w).pow_left (m + 1)
      have hy'_tot : Nat.totient y' = Nat.totient x := by
        dsimp [y']
        rw [Nat.totient_mul hcop_2_Fw, Nat.totient_prime_pow Nat.prime_two (by omega),
          Nat.add_sub_cancel, show 2 - 1 = 1 by rfl, mul_one,
          Nat.totient_mul (hcopFw.pow_left (a + b - 1)),
          Nat.totient_prime_pow hF hab_pos, hF_sub1, hab_eq, pow_add,
          hx_tot, ← hy_tot, hy_tot_eq]
        ring
      have hy'_eq : y' = x := hx_ce.2 y' hy'_tot
      apply hnot8
      rw [← hy'_eq]
      refine dvd_mul_of_dvd_left ?_ _
      have h8 : (8 : ℕ) = 2 ^ 3 := by norm_num
      rw [h8]
      exact Nat.pow_dvd_pow 2 (by omega)
  · have hcopFy : Nat.Coprime F y := hF.coprime_iff_not_dvd.mpr hFy
    let y' := F ^ a * y
    have hy'_tot : Nat.totient y' = Nat.totient x := by
      dsimp [y']
      rw [Nat.totient_mul (hcopFy.pow_left a), hy_tot,
        ← Nat.totient_mul (hcopFu.pow_left a), hxu]
    have hy'_eq : F ^ a * y = F ^ a * u := by
      calc
        F ^ a * y = y' := rfl
        _ = x := hx_ce.2 y' hy'_tot
        _ = F ^ a * u := hxu.symm
    have hFa_pos : 0 < F ^ a := pow_pos (by omega) a
    exact hy_ne (Nat.eq_of_mul_eq_mul_left hFa_pos hy'_eq)

/-- Concrete Klee exclusions: `5, 17, 257, 65537` never divide a reduced counterexample. -/
theorem fermat_primes_not_dvd_of_reduced {x : ℕ} (hx : IsReducedCounterexample x) :
    ¬ (5 ∣ x) ∧ ¬ (17 ∣ x) ∧ ¬ (257 ∣ x) ∧ ¬ (65537 ∣ x) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact not_fermat_prime_dvd_of_reduced (m := 2) hx (by omega) (by norm_num)
  · exact not_fermat_prime_dvd_of_reduced (m := 4) hx (by omega) (by norm_num)
  · exact not_fermat_prime_dvd_of_reduced (m := 8) hx (by omega) (by norm_num)
  · have h65537 : Nat.Prime (2 ^ 16 + 1) := by
      have hp : Nat.Prime 65537 :=
        prime_of_pratt_cert 65537 3 17 (List.replicate 16 2)
          (by decide) (by decide) (by decide)
          (fun q hq => by rw [List.mem_replicate] at hq; exact hq.2 ▸ Nat.prime_two)
          (by decide) (by decide)
      simpa using hp
    exact not_fermat_prime_dvd_of_reduced (m := 16) hx (by omega) h65537

/-- Minimal Carmichael counterexample exclusions (`4 ∥ x₀` and `5, 17, 257, 65537 ∤ x₀`). -/
theorem minimal_counterexample_structure {x₀ : ℕ} (hx₀ : IsMinimalCounterexample x₀) :
    4 ∣ x₀ ∧ ¬ (8 ∣ x₀) ∧ ¬ (5 ∣ x₀) ∧ ¬ (17 ∣ x₀) ∧ ¬ (257 ∣ x₀) ∧ ¬ (65537 ∣ x₀) := by
  have hred := isReduced_of_isMinimal hx₀
  obtain ⟨h4, h8⟩ := exact_four_dvd_of_reduced hred
  obtain ⟨h5, h17, h257, h65537⟩ := fermat_primes_not_dvd_of_reduced hred
  exact ⟨h4, h8, h5, h17, h257, h65537⟩

/-! ## Erdős's (1958) Valence-Preserving Fiber Bijection & Multiplication Theorem -/

/-- Exact criterion for `P * x` (`P` prime, `P ∤ x`, `P ∤ φ(x)`) to be a Carmichael
counterexample when `x` is one: `P * x` is a counterexample iff every preimage of
`(P - 1) * φ(x)` is divisible by `P`. -/
theorem erdos_mul_prime_counterexample_iff {x P : ℕ}
    (hx : IsCarmichaelCounterexample x)
    (hP : Nat.Prime P)
    (hPx : ¬ P ∣ x)
    (hPtot : ¬ P ∣ Nat.totient x) :
    IsCarmichaelCounterexample (P * x) ↔
      ∀ y : ℕ, Nat.totient y = (P - 1) * Nat.totient x → P ∣ y := by
  have hcopPx : Nat.Coprime P x := hP.coprime_iff_not_dvd.mpr hPx
  have hPx_tot : Nat.totient (P * x) = (P - 1) * Nat.totient x := by
    rw [Nat.totient_mul hcopPx, Nat.totient_prime hP]
  constructor
  · intro hce y hy
    have hy_eq : y = P * x := hce.2 y (hy.trans hPx_tot.symm)
    exact hy_eq ▸ dvd_mul_right P x
  · intro hdiv
    refine ⟨mul_pos hP.pos hx.1, ?_⟩
    intro y hy
    rw [hPx_tot] at hy
    obtain ⟨z, rfl⟩ := hdiv y hy
    have hPz : ¬ P ∣ z := by
      intro hPz_dvd
      have htot_mul : Nat.totient (P * z) = P * Nat.totient z :=
        Nat.totient_mul_of_prime_of_dvd hP hPz_dvd
      rw [htot_mul] at hy
      have hPdvd_prod : P ∣ (P - 1) * Nat.totient x := ⟨Nat.totient z, hy.symm⟩
      rcases hP.dvd_mul.mp hPdvd_prod with hPPm1 | hPtx
      · have hP2 : 2 ≤ P := hP.two_le
        have := Nat.le_of_dvd (by omega) hPPm1
        omega
      · exact hPtot hPtx
    have hcopPz : Nat.Coprime P z := hP.coprime_iff_not_dvd.mpr hPz
    rw [Nat.totient_mul hcopPz, Nat.totient_prime hP] at hy
    have hPm1_pos : 0 < P - 1 := by
      have := hP.two_le
      omega
    have hz_tot : Nat.totient z = Nat.totient x := Nat.eq_of_mul_eq_mul_left hPm1_pos hy
    rw [hx.2 z hz_tot]

/-- **Erdős's (1958) Valence-Preserving Fiber Bijection** (Acta Arith. 4):
For any `m > 0`, `k > 0`, prime `q > k * m + 1`, and prime `P = 1 + k * q` such that
`1 + j * q` is composite for all divisors `j ∣ k * m` with `j ≠ k`, the totient fiber of
`(P - 1) * m = k * q * m` is in exact bijection with the totient fiber of `m` via `z ↦ P * z`. -/
theorem erdos_1958_totient_fiber_eq {m k q y : ℕ}
    (hm : 0 < m)
    (hk : 0 < k)
    (hq : Nat.Prime q)
    (hq_gt : k * m + 1 < q)
    (hP : Nat.Prime (1 + k * q))
    (hexcl : ∀ j : ℕ, j ∣ k * m → j ≠ k → ¬ Nat.Prime (1 + j * q)) :
    Nat.totient y = k * q * m ↔ ∃ z : ℕ, Nat.totient z = m ∧ y = (1 + k * q) * z := by
  set P := 1 + k * q
  have hkm_pos : 0 < k * m := mul_pos hk hm
  have hP_sub1 : P - 1 = k * q := by dsimp [P]; omega
  constructor
  · intro hy
    have hy_ne0 : y ≠ 0 := by
      intro h0
      rw [h0, Nat.totient_zero] at hy
      have := mul_pos (mul_pos hk hq.pos) hm
      omega
    have hq_dvd_tot : q ∣ Nat.totient y := ⟨k * m, by rw [hy]; ring⟩
    have hPy : P ∣ y := by
      rcases (prime_dvd_totient_iff hy_ne0 hq).mp hq_dvd_tot with hq_sq | ⟨Q, hQ_mem, hq_Qm1⟩
      · exfalso
        have htot_q2 : Nat.totient (q ^ 2) ∣ Nat.totient y := Nat.totient_dvd_of_dvd hq_sq
        rw [Nat.totient_prime_pow hq (by norm_num), pow_one, hy] at htot_q2
        have hqm1_dvd : q - 1 ∣ k * m := by
          rcases htot_q2 with ⟨t, ht⟩
          refine ⟨t, ?_⟩
          have h1 : q * (k * m) = q * ((q - 1) * t) := by
            calc
              q * (k * m) = k * q * m := by ring
              _ = q * (q - 1) * t := ht
              _ = q * ((q - 1) * t) := by ring
          exact Nat.eq_of_mul_eq_mul_left hq.pos h1
        have hle := Nat.le_of_dvd hkm_pos hqm1_dvd
        omega
      · have hQp : Nat.Prime Q := Nat.prime_of_mem_primeFactors hQ_mem
        have hQ_dvd_y : Q ∣ y := Nat.dvd_of_mem_primeFactors hQ_mem
        rcases hq_Qm1 with ⟨j, hj⟩
        have hQ2 : 2 ≤ Q := hQp.two_le
        have hj_pos : 0 < j := by
          by_contra hj0
          have hjz : j = 0 := by omega
          rw [hjz, mul_zero] at hj
          omega
        have hQ_eq : Q = 1 + j * q := by
          have hj' : Q - 1 = j * q := by rw [hj, mul_comm]
          omega
        have hQm1_dvd : Q - 1 ∣ Nat.totient y := by
          have := Nat.totient_dvd_of_dvd hQ_dvd_y
          rwa [Nat.totient_prime hQp] at this
        rw [hj, hy] at hQm1_dvd
        have hj_dvd : j ∣ k * m := by
          rcases hQm1_dvd with ⟨t, ht⟩
          refine ⟨t, ?_⟩
          have h1 : q * (k * m) = q * (j * t) := by
            calc
              q * (k * m) = k * q * m := by ring
              _ = q * j * t := ht
              _ = q * (j * t) := by ring
          exact Nat.eq_of_mul_eq_mul_left hq.pos h1
        have hjk : j = k := by
          by_contra hne
          exact hexcl j hj_dvd hne (hQ_eq ▸ hQp)
        subst hjk
        have hQP : Q = P := by dsimp [P]; omega
        rwa [← hQP]
    rcases hPy with ⟨z, rfl⟩
    have hPz : ¬ P ∣ z := by
      intro hPz_dvd
      have htot_mul : Nat.totient (P * z) = P * Nat.totient z :=
        Nat.totient_mul_of_prime_of_dvd hP hPz_dvd
      rw [htot_mul] at hy
      have hPdvd : P ∣ k * q * m := ⟨Nat.totient z, hy.symm⟩
      have hcop_P_kq : Nat.Coprime P (k * q) := by
        dsimp [P]
        simp [add_comm]
      have hPdvd_m : P ∣ m := hcop_P_kq.dvd_of_dvd_mul_left hPdvd
      have hle := Nat.le_of_dvd hm hPdvd_m
      have hP_gt_m : m < P := by
        dsimp [P]
        nlinarith
      omega
    have hcopPz : Nat.Coprime P z := hP.coprime_iff_not_dvd.mpr hPz
    rw [Nat.totient_mul hcopPz, Nat.totient_prime hP, hP_sub1] at hy
    have hkq_pos : 0 < k * q := mul_pos hk hq.pos
    exact ⟨z, Nat.eq_of_mul_eq_mul_left hkq_pos hy, rfl⟩
  · rintro ⟨z, hz_tot, rfl⟩
    have hPz : ¬ P ∣ z := by
      intro hPz_dvd
      have hPm1_dvd : P - 1 ∣ Nat.totient z := by
        have := Nat.totient_dvd_of_dvd hPz_dvd
        rwa [Nat.totient_prime hP] at this
      rw [hP_sub1, hz_tot] at hPm1_dvd
      have hle := Nat.le_of_dvd hm hPm1_dvd
      nlinarith
    have hcopPz : Nat.Coprime P z := hP.coprime_iff_not_dvd.mpr hPz
    rw [Nat.totient_mul hcopPz, Nat.totient_prime hP, hP_sub1, hz_tot]

/-- Concrete non-vacuity witness for `erdos_1958_totient_fiber_eq` at `(m, k, q, P) = (1, 2, 5, 11)`:
`φ(y) = 10 ↔ y = 11 ∨ y = 22`. -/
theorem totient_eq_ten_iff (y : ℕ) : Nat.totient y = 10 ↔ y = 11 ∨ y = 22 := by
  have hbij := erdos_1958_totient_fiber_eq (m := 1) (k := 2) (q := 5) (y := y)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by
      intro j hj hne
      have hj12 : j = 1 ∨ j = 2 := by
        have hle : j ≤ 2 := Nat.le_of_dvd (by norm_num) hj
        have hpos : 0 < j := Nat.pos_of_dvd_of_pos hj (by norm_num)
        omega
      rcases hj12 with rfl | rfl
      · norm_num
      · exact False.elim (hne rfl))
  norm_num at hbij
  rw [hbij]
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz12 : z = 1 ∨ z = 2 := Nat.totient_eq_one_iff.mp hz
    rcases hz12 with rfl | rfl <;> omega
  · rintro (rfl | rfl)
    · exact ⟨1, by decide, by norm_num⟩
    · exact ⟨2, by decide, by norm_num⟩

/-- **Erdős's (1958) Counterexample Multiplication Step**:
Given a Carmichael counterexample `x` and an Erdős multiplier `(k, q)` for `m = φ(x)`,
`(1 + k * q) * x` is a strictly larger Carmichael counterexample in which `1 + k * q` appears to
the first power (`¬ (1 + k * q) ^ 2 ∣ (1 + k * q) * x`). -/
theorem erdos_1958_counterexample_step {x k q : ℕ}
    (hx : IsCarmichaelCounterexample x)
    (hk : 0 < k)
    (hq : Nat.Prime q)
    (hq_gt : k * Nat.totient x + 1 < q)
    (hP : Nat.Prime (1 + k * q))
    (hexcl : ∀ j : ℕ, j ∣ k * Nat.totient x → j ≠ k → ¬ Nat.Prime (1 + j * q)) :
    IsCarmichaelCounterexample ((1 + k * q) * x) ∧
      x < (1 + k * q) * x ∧
      ¬ ((1 + k * q) ^ 2 ∣ (1 + k * q) * x) := by
  set P := 1 + k * q
  have hm : 0 < Nat.totient x := Nat.totient_pos.mpr hx.1
  have hPx : ¬ P ∣ x := by
    intro hd
    have hPm1_dvd : P - 1 ∣ Nat.totient x := by
      have := Nat.totient_dvd_of_dvd hd
      rwa [Nat.totient_prime hP] at this
    have hle := Nat.le_of_dvd hm hPm1_dvd
    have : P - 1 = k * q := by dsimp [P]; omega
    nlinarith
  have hcopPx : Nat.Coprime P x := hP.coprime_iff_not_dvd.mpr hPx
  have hPx_tot : Nat.totient (P * x) = k * q * Nat.totient x := by
    have hPsub : P - 1 = k * q := by dsimp [P]; omega
    rw [Nat.totient_mul hcopPx, Nat.totient_prime hP, hPsub]
  refine ⟨⟨mul_pos hP.pos hx.1, ?_⟩, ?_, ?_⟩
  · intro y hy
    rw [hPx_tot] at hy
    obtain ⟨z, hz_tot, rfl⟩ :=
      (erdos_1958_totient_fiber_eq hm hk hq hq_gt hP hexcl).mp hy
    rw [hx.2 z hz_tot]
  · have hP2 : 2 ≤ P := hP.two_le
    have hx_pos : 0 < x := hx.1
    nlinarith
  · intro hsq
    rw [sq, mul_dvd_mul_iff_left hP.ne_zero] at hsq
    exact hPx hsq

/-- **Erdős's (1958) Infinitude Theorem from Sieve Supply**:
Under the existence of arbitrarily large Erdős multipliers `(k, q)` (proved in Erdős 1958 by
Brun's sieve), the existence of a single Carmichael counterexample implies infinitely many
Carmichael counterexamples. -/
theorem erdos_1958_infinitude_from_sieve
    (hsieve : ∀ m B : ℕ, 0 < m → ∃ k q : ℕ, 0 < k ∧ Nat.Prime q ∧ k * m + 1 < q ∧
      B < 1 + k * q ∧ Nat.Prime (1 + k * q) ∧
      ∀ j : ℕ, j ∣ k * m → j ≠ k → ¬ Nat.Prime (1 + j * q))
    (hex : ∃ x : ℕ, IsCarmichaelCounterexample x) :
    Set.Infinite {x : ℕ | IsCarmichaelCounterexample x} := by
  rcases hex with ⟨x₀, hx₀⟩
  apply Set.infinite_of_forall_exists_gt
  intro n
  have hm : 0 < Nat.totient x₀ := Nat.totient_pos.mpr hx₀.1
  obtain ⟨k, q, hk, hq, hq_gt, hB, hP, hexcl⟩ := hsieve (Nat.totient x₀) n hm
  obtain ⟨hce, _, _⟩ := erdos_1958_counterexample_step hx₀ hk hq hq_gt hP hexcl
  refine ⟨(1 + k * q) * x₀, hce, ?_⟩
  have hx₀_pos : 1 ≤ x₀ := hx₀.1
  nlinarith

end CarmichaelTotient
