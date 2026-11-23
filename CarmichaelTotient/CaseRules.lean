module

public import CarmichaelTotient.Lemma72
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.ZMod.Units
public import Mathlib.GroupTheory.OrderOfElement

import Mathlib.Tactic

/-!
# First Forced Squares, Case I/II Step Rules, Bit-Sum Soundness, and Certificate Bridge

Formalizes:
1. First forced squares of Carmichael (1922): `9 ∣ x`, `49 ∣ x`, `43^2 ∣ x`, and closure of the
   `d = 1` chain (`1807 = 13 * 139`, only `e ∈ {1, 2, 6, 42}` among divisors of `2 * 3 * 7 * 43`
   give prime `1 + e`).
2. Exact Case I / Case II split (`carmichael_case_split`): either `9 ∣ x ∧ ¬ 27 ∣ x ∧ 13^2 ∣ x`
   (Case I) or `27 ∣ x` (Case II).
3. Case I & Case II certificate step rules matching `ct_bound_check.py` (`CASE_FORMS`):
   `step_6k_plus_1`, `step_case1_12k_plus_1`, `step_case2_18k_plus_1`, plus inductive closures
   `ForcedCase1` / `ForcedCase2`.
4. Square-product divisibility (`base_mul_prod_sq_dvd_case1`, `base_mul_prod_sq_dvd_case2`,
   `base_mul_prod_sq_dvd`) for finite prime sets and pairwise-disjoint chunks.
5. Exact bit-length and base-10 digit lower-bound soundness (`digit_bound_of_bit_sum`,
   `digit_bound_strict_of_bit_sum`, `two_pow_log2_le_self`) matching `ct_bound_check.py`.
6. Multi-witness Lucas primality soundness (`prime_of_lucas_witnesses`, Ford Lemma 7.3) matching
   `ct_bound_check.py`'s per-factor witness check.
7. Parameterized `CarmichaelBoundCertificate` bridge (`carmichael_bound_from_certificate`)
   connecting the unconditional step & bit-sum soundness theorems to external large-scale runs
   such as `ct-bound-3` (explicitly parameterized, never claimed unconditional for `10^100B`).
-/

@[expose] public section

namespace CarmichaelTotient

/-! ## Divisibility helpers for `w / rad w` -/

/-- If `e * rad w ∣ w`, then `e ∣ w / rad w`. -/
theorem dvd_div_rad_of_mul_rad_dvd {w e : ℕ} (h : e * rad w ∣ w) :
    e ∣ w / rad w := by
  have hrad_pos : 0 < rad w := rad_pos w
  rcases h with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  have h1 : w = (e * t) * rad w := by
    calc
      w = e * rad w * t := ht
      _ = (e * t) * rad w := by ring
  conv_lhs => arg 1; rw [h1]
  rw [Nat.mul_div_cancel _ hrad_pos]

/-- Product of pairwise `Nat.Coprime` divisors of `n` divides `n`. -/
theorem finset_prod_dvd_of_nat_coprime {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {f : ι → ℕ} {n : ℕ}
    (hcop : Set.Pairwise (s : Set ι) fun a b => Nat.Coprime (f a) (f b))
    (hdvd : ∀ a ∈ s, f a ∣ n) :
    (∏ a ∈ s, f a) ∣ n := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hcop_s : Set.Pairwise (s : Set ι) fun x y => Nat.Coprime (f x) (f y) :=
      hcop.mono (by simp)
    have hdvd_s : (∏ x ∈ s, f x) ∣ n := ih hcop_s fun x hx => hdvd x (Finset.mem_insert_of_mem hx)
    have hcop_a : Nat.Coprime (f a) (∏ x ∈ s, f x) :=
      Nat.Coprime.prod_right fun x hx =>
        hcop (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hx) (fun h => ha (h ▸ hx))
    exact hcop_a.mul_dvd_of_dvd_of_dvd (hdvd a (Finset.mem_insert_self a s)) hdvd_s

/-- If `0 < w`, `p` is prime, and `p ^ (a + 1) ∣ w`, then `p ^ a ∣ w / rad w`. -/
theorem prime_pow_dvd_div_rad {w p a : ℕ} (hw : 0 < w) (hp : Nat.Prime p)
    (hdvd : p ^ (a + 1) ∣ w) : p ^ a ∣ w / rad w := by
  have hpw : p ∣ w := dvd_trans (dvd_pow_self p (Nat.succ_ne_zero a)) hdvd
  have hmem : p ∈ w.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpw, by omega⟩
  set r := ∏ q ∈ w.primeFactors.erase p, q
  have hrad_eq : rad w = p * r := by
    unfold rad
    exact (Finset.mul_prod_erase w.primeFactors id hmem).symm
  have hr_dvd_w : r ∣ w := by
    have : r ∣ rad w := ⟨p, by rw [hrad_eq, mul_comm]⟩
    exact dvd_trans this (rad_dvd_self w)
  have hcop : Nat.Coprime (p ^ (a + 1)) r := by
    refine Nat.Coprime.pow_left (a + 1) ?_
    refine Nat.Coprime.prod_right fun q hq => ?_
    have hq_mem : q ∈ w.primeFactors := Finset.mem_of_mem_erase hq
    have hq_ne : q ≠ p := Finset.ne_of_mem_erase hq
    have hq_prime : Nat.Prime q := Nat.prime_of_mem_primeFactors hq_mem
    exact (Nat.coprime_primes hp hq_prime).mpr (Ne.symm hq_ne)
  have hmul_dvd : p ^ (a + 1) * r ∣ w := hcop.mul_dvd_of_dvd_of_dvd hdvd hr_dvd_w
  apply dvd_div_rad_of_mul_rad_dvd
  have heq : p ^ a * rad w = p ^ (a + 1) * r := by
    rw [hrad_eq, pow_succ]
    ring
  rw [heq]
  exact hmul_dvd

/-- If `0 < w` and every `p ∈ K` is prime with `p ^ 2 ∣ w`, then `∏ p ∈ K, p ∣ w / rad w`. -/
theorem prod_primes_dvd_div_rad {w : ℕ} {K : Finset ℕ} (hw : 0 < w)
    (hK : ∀ p ∈ K, Nat.Prime p ∧ p ^ 2 ∣ w) :
    (∏ p ∈ K, p) ∣ w / rad w := by
  apply finset_prod_dvd_of_nat_coprime
  · intro p hp q hq hpq
    exact (Nat.coprime_primes (hK p hp).1 (hK q hq).1).mpr hpq
  · intro p hp
    have h1 := prime_pow_dvd_div_rad hw (hK p hp).1 (hK p hp).2
    simpa using h1

/-- Product of primes `≥ 5` is coprime to `2` and `3`. -/
theorem coprime_of_primes_ge_five {K : Finset ℕ} (hK : ∀ p ∈ K, Nat.Prime p ∧ 5 ≤ p) :
    Nat.Coprime 2 (∏ p ∈ K, p) ∧ Nat.Coprime 3 (∏ p ∈ K, p) := by
  constructor
  · refine Nat.Coprime.prod_right fun p hp => ?_
    have ⟨hpr, h5⟩ := hK p hp
    exact (Nat.coprime_primes Nat.prime_two hpr).mpr (by omega)
  · refine Nat.Coprime.prod_right fun p hp => ?_
    have ⟨hpr, h5⟩ := hK p hp
    exact (Nat.coprime_primes Nat.prime_three hpr).mpr (by omega)

/-- Explicit values of `rad` at `1` and `6`. -/
theorem rad_one : rad 1 = 1 := by
  simp [rad]

theorem rad_six : rad 6 = 6 := by
  have h6 : (6 : ℕ) = 2 * 3 := by norm_num
  have hpf : (6 : ℕ).primeFactors = {2, 3} := by
    rw [h6, Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.Prime.primeFactors Nat.prime_two, Nat.Prime.primeFactors Nat.prime_three]
    rfl
  simp [rad, hpf]

/-! ## First forced squares (Carmichael 1922) -/

/-- Every Carmichael counterexample is divisible by `9`. -/
theorem nine_dvd_counterexample {x : ℕ} (hx : IsCarmichaelCounterexample x) : 9 ∣ x := by
  have h4 : 2 ^ (1 + 1) ∣ x := by simpa using four_dvd_counterexample hx
  have h2 : 2 ∣ x / rad x := by
    have := prime_pow_dvd_div_rad hx.1 Nat.prime_two h4
    simpa using this
  have hstep := ford_lemma_7_2 (x := x) (d := 1) (e := 2) hx
    (one_dvd x)
    (by simp)
    (by simp [rad_one])
    (by simpa using h2)
    (by norm_num)
  norm_num at hstep
  exact hstep

/-- Every Carmichael counterexample is divisible by `49`. -/
theorem fortynine_dvd_counterexample {x : ℕ} (hx : IsCarmichaelCounterexample x) : 49 ∣ x := by
  have h4 : 2 ^ (1 + 1) ∣ x := by simpa using four_dvd_counterexample hx
  have h9 : 3 ^ (1 + 1) ∣ x := by simpa using nine_dvd_counterexample hx
  have h2 : 2 ∣ x / rad x := by
    have := prime_pow_dvd_div_rad hx.1 Nat.prime_two h4
    simpa using this
  have h3 : 3 ∣ x / rad x := by
    have := prime_pow_dvd_div_rad hx.1 Nat.prime_three h9
    simpa using this
  have h6 : 6 ∣ x / rad x := by
    have hcop : Nat.Coprime 2 3 := by decide
    have := hcop.mul_dvd_of_dvd_of_dvd h2 h3
    norm_num at this
    exact this
  have hstep := ford_lemma_7_2 (x := x) (d := 1) (e := 6) hx
    (one_dvd x)
    (by simp)
    (by simp [rad_one])
    (by simpa using h6)
    (by norm_num)
  norm_num at hstep
  exact hstep

/-- Every Carmichael counterexample is divisible by `43 ^ 2`. -/
theorem fortythree_sq_dvd_counterexample {x : ℕ} (hx : IsCarmichaelCounterexample x) :
    43 ^ 2 ∣ x := by
  have h4 : 2 ^ (1 + 1) ∣ x := by simpa using four_dvd_counterexample hx
  have h9 : 3 ^ (1 + 1) ∣ x := by simpa using nine_dvd_counterexample hx
  have h49 : 7 ^ (1 + 1) ∣ x := by simpa using fortynine_dvd_counterexample hx
  have h2 : 2 ∣ x / rad x := by
    have := prime_pow_dvd_div_rad hx.1 Nat.prime_two h4
    simpa using this
  have h3 : 3 ∣ x / rad x := by
    have := prime_pow_dvd_div_rad hx.1 Nat.prime_three h9
    simpa using this
  have h7 : 7 ∣ x / rad x := by
    have := prime_pow_dvd_div_rad hx.1 (by norm_num : Nat.Prime 7) h49
    simpa using this
  have h6 : 6 ∣ x / rad x := by
    have := (by decide : Nat.Coprime 2 3).mul_dvd_of_dvd_of_dvd h2 h3
    norm_num at this
    exact this
  have h42 : 42 ∣ x / rad x := by
    have := (by decide : Nat.Coprime 6 7).mul_dvd_of_dvd_of_dvd h6 h7
    norm_num at this
    exact this
  have hstep := ford_lemma_7_2 (x := x) (d := 1) (e := 42) hx
    (one_dvd x)
    (by simp)
    (by simp [rad_one])
    (by simpa using h42)
    (by norm_num)
  norm_num at hstep
  exact hstep

/-- Helper for splitting divisors of `p * m` when `p` is prime. -/
private theorem dvd_prime_mul {p m e : ℕ} (hp : Nat.Prime p) (he : e ∣ p * m) :
    e ∣ m ∨ ∃ e', e' ∣ m ∧ e = p * e' := by
  by_cases hpe : p ∣ e
  · rcases hpe with ⟨e', rfl⟩
    right
    exact ⟨e', (mul_dvd_mul_iff_left hp.ne_zero).mp he, rfl⟩
  · left
    exact (hp.coprime_iff_not_dvd.mpr hpe).symm.dvd_of_dvd_mul_left he

/-- Closure of the `d = 1` chain: `1807 = 13 * 139` is composite, and among all 16 divisors `e`
of `2 * 3 * 7 * 43 = 1806`, `1 + e` is prime if and only if `e ∈ {1, 2, 6, 42}`. -/
theorem d_one_chain_closed :
    (¬ Nat.Prime 1807 ∧ 1807 = 13 * 139) ∧
      ∀ e : ℕ, e ∣ 2 * 3 * 7 * 43 → (Nat.Prime (1 + e) ↔ e ∈ ({1, 2, 6, 42} : Finset ℕ)) := by
  have h1807 : ¬ Nat.Prime 1807 ∧ 1807 = 13 * 139 := ⟨by norm_num, by norm_num⟩
  refine ⟨h1807, ?_⟩
  intro e he
  have he' : e ∣ 2 * (3 * (7 * 43)) := by simpa [mul_assoc] using he
  have hcases : e ∈ ({1, 2, 3, 6, 7, 14, 21, 42, 43, 86, 129, 258, 301, 602, 903, 1806} :
      Finset ℕ) := by
    have h43 : ∀ d, d ∣ 43 → d = 1 ∨ d = 43 := fun d hd =>
      (Nat.dvd_prime (by norm_num : Nat.Prime 43)).mp hd
    have h7 : ∀ d, d ∣ 7 * 43 → d = 1 ∨ d = 43 ∨ d = 7 ∨ d = 301 := by
      intro d hd
      rcases dvd_prime_mul (by norm_num : Nat.Prime 7) hd with h | ⟨d', hd', rfl⟩
      · rcases h43 d h with rfl | rfl <;> omega
      · rcases h43 d' hd' with rfl | rfl <;> omega
    have h3 : ∀ d, d ∣ 3 * (7 * 43) →
        d = 1 ∨ d = 43 ∨ d = 7 ∨ d = 301 ∨ d = 3 ∨ d = 129 ∨ d = 21 ∨ d = 903 := by
      intro d hd
      rcases dvd_prime_mul Nat.prime_three hd with h | ⟨d', hd', rfl⟩
      · rcases h7 d h with rfl | rfl | rfl | rfl <;> omega
      · rcases h7 d' hd' with rfl | rfl | rfl | rfl <;> omega
    rcases dvd_prime_mul Nat.prime_two he' with h | ⟨d', hd', rfl⟩
    · rcases h3 e h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · rcases h3 d' hd' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  simp only [Finset.mem_insert, Finset.mem_singleton] at hcases ⊢
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

/-! ## Case I / Case II step rules -/

/-- **Step rule `6k + 1`** (valid in both Case I and Case II):
For any finite set `K` of primes `≥ 5` whose squares divide `x`, if `6 * (∏ p ∈ K, p) + 1` is
prime then its square divides `x`. -/
theorem step_6k_plus_1 {x : ℕ} {K : Finset ℕ}
    (hx : IsCarmichaelCounterexample x)
    (hK : ∀ p ∈ K, Nat.Prime p ∧ 5 ≤ p ∧ p ^ 2 ∣ x)
    (hP : Nat.Prime (6 * (∏ p ∈ K, p) + 1)) :
    (6 * (∏ p ∈ K, p) + 1) ^ 2 ∣ x := by
  set k := ∏ p ∈ K, p
  have h4 : 2 ^ (1 + 1) ∣ x := by simpa using four_dvd_counterexample hx
  have h9 : 3 ^ (1 + 1) ∣ x := by simpa using nine_dvd_counterexample hx
  have h2 : 2 ∣ x / rad x := by
    have := prime_pow_dvd_div_rad hx.1 Nat.prime_two h4
    simpa using this
  have h3 : 3 ∣ x / rad x := by
    have := prime_pow_dvd_div_rad hx.1 Nat.prime_three h9
    simpa using this
  have h6 : 6 ∣ x / rad x := by
    have := (by decide : Nat.Coprime 2 3).mul_dvd_of_dvd_of_dvd h2 h3
    norm_num at this
    exact this
  have hk : k ∣ x / rad x :=
    prod_primes_dvd_div_rad hx.1 fun p hp => ⟨(hK p hp).1, (hK p hp).2.2⟩
  have ⟨hcop2, hcop3⟩ := coprime_of_primes_ge_five fun p hp => ⟨(hK p hp).1, (hK p hp).2.1⟩
  have hcop6 : Nat.Coprime 6 k := by
    have : (6 : ℕ) = 2 * 3 := by norm_num
    rw [this]
    exact hcop2.mul_left hcop3
  have h6k : 6 * k ∣ x / rad x := hcop6.mul_dvd_of_dvd_of_dvd h6 hk
  have hP' : Nat.Prime (1 + (6 * k) * Nat.totient 1) := by
    simpa [Nat.totient_one, add_comm] using hP
  have hstep := ford_lemma_7_2 (x := x) (d := 1) (e := 6 * k) hx
    (one_dvd x)
    (by simp)
    (by simp [rad_one])
    (by simpa using h6k)
    hP'
  simpa [Nat.totient_one, add_comm] using hstep

/-- **Case I step rule `12k + 1`** (when `¬ 27 ∣ x`, using `d = 9`, `φ(9) = 6`, `e = 2k`):
For any finite set `K` of primes `≥ 5` whose squares divide `x`, if `12 * (∏ p ∈ K, p) + 1` is
prime then its square divides `x`. -/
theorem step_case1_12k_plus_1 {x : ℕ} {K : Finset ℕ}
    (hx : IsCarmichaelCounterexample x)
    (h27 : ¬ 27 ∣ x)
    (hK : ∀ p ∈ K, Nat.Prime p ∧ 5 ≤ p ∧ p ^ 2 ∣ x)
    (hP : Nat.Prime (12 * (∏ p ∈ K, p) + 1)) :
    (12 * (∏ p ∈ K, p) + 1) ^ 2 ∣ x := by
  set k := ∏ p ∈ K, p
  set w := x / 9
  have h9 : 9 ∣ x := nine_dvd_counterexample hx
  have h9w : 9 * w = x := Nat.mul_div_cancel' h9
  have hw_pos : 0 < w := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, mul_zero] at h9w
    have := hx.1
    omega
  have h3ndvd_w : ¬ 3 ∣ w := by
    intro h3w
    rcases h3w with ⟨t, ht⟩
    apply h27
    refine ⟨t, ?_⟩
    calc
      x = 9 * w := h9w.symm
      _ = 9 * (3 * t) := by rw [ht]
      _ = 27 * t := by ring
  have hcop9w : Nat.Coprime 9 w := by
    have hcop3w : Nat.Coprime 3 w := Nat.prime_three.coprime_iff_not_dvd.mpr h3ndvd_w
    have : (9 : ℕ) = 3 ^ 2 := by norm_num
    rw [this]
    exact hcop3w.pow_left 2
  have h4w : 2 ^ (1 + 1) ∣ w := by
    have h4x : 4 ∣ 9 * w := h9w.symm ▸ four_dvd_counterexample hx
    have hcop49 : Nat.Coprime 4 9 := by decide
    have := hcop49.dvd_of_dvd_mul_left h4x
    simpa using this
  have h2w : 2 ∣ w / rad w := by
    have := prime_pow_dvd_div_rad hw_pos Nat.prime_two h4w
    simpa using this
  have hKw : ∀ p ∈ K, Nat.Prime p ∧ p ^ 2 ∣ w := by
    intro p hp
    have ⟨hpr, h5, hp2x⟩ := hK p hp
    have hcop_p9 : Nat.Coprime (p ^ 2) 9 := by
      have hcop_p3 : Nat.Coprime p 3 := (Nat.coprime_primes hpr Nat.prime_three).mpr (by omega)
      have : (9 : ℕ) = 3 ^ 2 := by norm_num
      rw [this]
      exact (hcop_p3.pow_left 2).pow_right 2
    exact ⟨hpr, hcop_p9.dvd_of_dvd_mul_left (h9w.symm ▸ hp2x)⟩
  have hkw : k ∣ w / rad w := prod_primes_dvd_div_rad hw_pos hKw
  have ⟨hcop2, _⟩ := coprime_of_primes_ge_five fun p hp => ⟨(hK p hp).1, (hK p hp).2.1⟩
  have h2k : 2 * k ∣ w / rad w := hcop2.mul_dvd_of_dvd_of_dvd h2w hkw
  have htot9 : Nat.totient 9 = 6 := by decide
  have hrad9 : rad (Nat.totient 9) ∣ x := by
    rw [htot9, rad_six]
    have h2x : 2 ∣ x := dvd_trans (by norm_num : 2 ∣ 4) (four_dvd_counterexample hx)
    have h3x : 3 ∣ x := dvd_trans (by norm_num : 3 ∣ 9) h9
    have := (by decide : Nat.Coprime 2 3).mul_dvd_of_dvd_of_dvd h2x h3x
    norm_num at this
    exact this
  have hPeq : 1 + (2 * k) * Nat.totient 9 = 12 * k + 1 := by
    rw [htot9]
    ring
  have hstep := ford_lemma_7_2 (x := x) (d := 9) (e := 2 * k) hx h9 hcop9w hrad9 h2k (hPeq.symm ▸ hP)
  rwa [hPeq] at hstep

/-- **Case II step rule `18k + 1`** (when `27 ∣ x`, using `d = 1`, `e = 18k`):
For any finite set `K` of primes `≥ 5` whose squares divide `x`, if `18 * (∏ p ∈ K, p) + 1` is
prime then its square divides `x`. -/
theorem step_case2_18k_plus_1 {x : ℕ} {K : Finset ℕ}
    (hx : IsCarmichaelCounterexample x)
    (h27 : 27 ∣ x)
    (hK : ∀ p ∈ K, Nat.Prime p ∧ 5 ≤ p ∧ p ^ 2 ∣ x)
    (hP : Nat.Prime (18 * (∏ p ∈ K, p) + 1)) :
    (18 * (∏ p ∈ K, p) + 1) ^ 2 ∣ x := by
  set k := ∏ p ∈ K, p
  have h4 : 2 ^ (1 + 1) ∣ x := by simpa using four_dvd_counterexample hx
  have h2 : 2 ∣ x / rad x := by
    have := prime_pow_dvd_div_rad hx.1 Nat.prime_two h4
    simpa using this
  have h9 : 9 ∣ x / rad x := by
    have h33 : 3 ^ (2 + 1) ∣ x := by simpa using h27
    have := prime_pow_dvd_div_rad hx.1 Nat.prime_three h33
    simpa using this
  have h18 : 18 ∣ x / rad x := by
    have := (by decide : Nat.Coprime 2 9).mul_dvd_of_dvd_of_dvd h2 h9
    norm_num at this
    exact this
  have hk : k ∣ x / rad x :=
    prod_primes_dvd_div_rad hx.1 fun p hp => ⟨(hK p hp).1, (hK p hp).2.2⟩
  have ⟨hcop2, hcop3⟩ := coprime_of_primes_ge_five fun p hp => ⟨(hK p hp).1, (hK p hp).2.1⟩
  have hcop18 : Nat.Coprime 18 k := by
    have : (18 : ℕ) = 2 * 3 ^ 2 := by norm_num
    rw [this]
    exact hcop2.mul_left (hcop3.pow_left 2)
  have h18k : 18 * k ∣ x / rad x := hcop18.mul_dvd_of_dvd_of_dvd h18 hk
  have hP' : Nat.Prime (1 + (18 * k) * Nat.totient 1) := by
    simpa [Nat.totient_one, add_comm] using hP
  have hstep := ford_lemma_7_2 (x := x) (d := 1) (e := 18 * k) hx
    (one_dvd x)
    (by simp)
    (by simp [rad_one])
    (by simpa using h18k)
    hP'
  simpa [Nat.totient_one, add_comm] using hstep

/-- In Case I (`¬ 27 ∣ x`), `13 ^ 2 ∣ x`. -/
theorem thirteen_sq_dvd_case1 {x : ℕ} (hx : IsCarmichaelCounterexample x) (h27 : ¬ 27 ∣ x) :
    13 ^ 2 ∣ x := by
  have hstep := step_case1_12k_plus_1 (x := x) (K := ∅) hx h27 (by simp) (by norm_num)
  simpa using hstep

/-- **Exact Case I / Case II split** (Carmichael 1922; Ford 1998 §7.3):
Every Carmichael counterexample satisfies either `(9 ∣ x ∧ ¬ 27 ∣ x ∧ 13 ^ 2 ∣ x)` (Case I)
or `27 ∣ x` (Case II). -/
theorem carmichael_case_split {x : ℕ} (hx : IsCarmichaelCounterexample x) :
    (9 ∣ x ∧ ¬ 27 ∣ x ∧ 13 ^ 2 ∣ x) ∨ 27 ∣ x := by
  by_cases h27 : 27 ∣ x
  · exact Or.inr h27
  · exact Or.inl ⟨nine_dvd_counterexample hx, h27, thirteen_sq_dvd_case1 hx h27⟩

/-! ## Inductive closure of Case I and Case II step rules -/

/-- Primes `p ≥ 5` derivable in Case I (`¬ 27 ∣ x`) by repeated application of the
`6k + 1` and `12k + 1` rules (starting from `K = ∅`, which gives `7` and `13`). -/
inductive ForcedCase1 : ℕ → Prop
  | step6 {K : Finset ℕ} :
      (∀ q ∈ K, ForcedCase1 q) →
      Nat.Prime (6 * (∏ q ∈ K, q) + 1) →
      ForcedCase1 (6 * (∏ q ∈ K, q) + 1)
  | step12 {K : Finset ℕ} :
      (∀ q ∈ K, ForcedCase1 q) →
      Nat.Prime (12 * (∏ q ∈ K, q) + 1) →
      ForcedCase1 (12 * (∏ q ∈ K, q) + 1)

/-- Primes `p ≥ 5` derivable in Case II (`27 ∣ x`) by repeated application of the
`6k + 1` and `18k + 1` rules (starting from `K = ∅`, which gives `7` and `19`). -/
inductive ForcedCase2 : ℕ → Prop
  | step6 {K : Finset ℕ} :
      (∀ q ∈ K, ForcedCase2 q) →
      Nat.Prime (6 * (∏ q ∈ K, q) + 1) →
      ForcedCase2 (6 * (∏ q ∈ K, q) + 1)
  | step18 {K : Finset ℕ} :
      (∀ q ∈ K, ForcedCase2 q) →
      Nat.Prime (18 * (∏ q ∈ K, q) + 1) →
      ForcedCase2 (18 * (∏ q ∈ K, q) + 1)

/-- Every prime in `ForcedCase1` is prime, `≥ 5`, and its square divides any Case I
counterexample. -/
theorem forcedCase1_sound {x p : ℕ} (hx : IsCarmichaelCounterexample x) (h27 : ¬ 27 ∣ x)
    (hp : ForcedCase1 p) : Nat.Prime p ∧ 5 ≤ p ∧ p ^ 2 ∣ x := by
  induction hp with
  | step6 _ hprime ih =>
    have hk_pos : 1 ≤ ∏ q ∈ _, q := Finset.one_le_prod fun q hq => by
      have := (ih q hq).2.1
      omega
    exact ⟨hprime, by omega, step_6k_plus_1 hx ih hprime⟩
  | step12 _ hprime ih =>
    have hk_pos : 1 ≤ ∏ q ∈ _, q := Finset.one_le_prod fun q hq => by
      have := (ih q hq).2.1
      omega
    exact ⟨hprime, by omega, step_case1_12k_plus_1 hx h27 ih hprime⟩

/-- Every prime in `ForcedCase2` is prime, `≥ 5`, and its square divides any Case II
counterexample. -/
theorem forcedCase2_sound {x p : ℕ} (hx : IsCarmichaelCounterexample x) (h27 : 27 ∣ x)
    (hp : ForcedCase2 p) : Nat.Prime p ∧ 5 ≤ p ∧ p ^ 2 ∣ x := by
  induction hp with
  | step6 _ hprime ih =>
    have hk_pos : 1 ≤ ∏ q ∈ _, q := Finset.one_le_prod fun q hq => by
      have := (ih q hq).2.1
      omega
    exact ⟨hprime, by omega, step_6k_plus_1 hx ih hprime⟩
  | step18 _ hprime ih =>
    have hk_pos : 1 ≤ ∏ q ∈ _, q := Finset.one_le_prod fun q hq => by
      have := (ih q hq).2.1
      omega
    exact ⟨hprime, by omega, step_case2_18k_plus_1 hx h27 ih hprime⟩

/-! ## Square-product divisibility -/

/-- For any finite set `S` of primes `≥ 5` whose squares divide `x`, the product
`(4 * 9) * ∏ p ∈ S, p ^ 2` divides `x`. -/
theorem base_mul_prod_sq_dvd_case1 {x : ℕ} (hx : IsCarmichaelCounterexample x)
    (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p ∧ 5 ≤ p ∧ p ^ 2 ∣ x) :
    (4 * 9) * (∏ p ∈ S, p ^ 2) ∣ x := by
  have hbase : 4 * 9 ∣ x :=
    (by decide : Nat.Coprime 4 9).mul_dvd_of_dvd_of_dvd
      (four_dvd_counterexample hx) (nine_dvd_counterexample hx)
  have hprod : (∏ p ∈ S, p ^ 2) ∣ x := by
    apply finset_prod_dvd_of_nat_coprime
    · intro p hp q hq hpq
      exact ((Nat.coprime_primes (hS p hp).1 (hS q hq).1).mpr hpq).pow 2 2
    · intro p hp
      exact (hS p hp).2.2
  have hcop : Nat.Coprime (4 * 9) (∏ p ∈ S, p ^ 2) := by
    have ⟨hcop2, hcop3⟩ := coprime_of_primes_ge_five fun p hp => ⟨(hS p hp).1, (hS p hp).2.1⟩
    have hsq : (∏ p ∈ S, p ^ 2) = (∏ p ∈ S, p) ^ 2 := Finset.prod_pow S 2 (fun p => p)
    rw [hsq]
    have h4 : Nat.Coprime 4 (∏ p ∈ S, p) := by
      have : (4 : ℕ) = 2 ^ 2 := by norm_num
      rw [this]
      exact hcop2.pow_left 2
    have h9 : Nat.Coprime 9 (∏ p ∈ S, p) := by
      have : (9 : ℕ) = 3 ^ 2 := by norm_num
      rw [this]
      exact hcop3.pow_left 2
    exact (h4.mul_left h9).pow_right 2
  exact hcop.mul_dvd_of_dvd_of_dvd hbase hprod

/-- For any finite set `S` of primes `≥ 5` whose squares divide a Case II counterexample
(`27 ∣ x`), the product `(4 * 27) * ∏ p ∈ S, p ^ 2` divides `x`. -/
theorem base_mul_prod_sq_dvd_case2 {x : ℕ} (hx : IsCarmichaelCounterexample x) (h27 : 27 ∣ x)
    (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p ∧ 5 ≤ p ∧ p ^ 2 ∣ x) :
    (4 * 27) * (∏ p ∈ S, p ^ 2) ∣ x := by
  have hbase : 4 * 27 ∣ x :=
    (by decide : Nat.Coprime 4 27).mul_dvd_of_dvd_of_dvd (four_dvd_counterexample hx) h27
  have hprod : (∏ p ∈ S, p ^ 2) ∣ x := by
    apply finset_prod_dvd_of_nat_coprime
    · intro p hp q hq hpq
      exact ((Nat.coprime_primes (hS p hp).1 (hS q hq).1).mpr hpq).pow 2 2
    · intro p hp
      exact (hS p hp).2.2
  have hcop : Nat.Coprime (4 * 27) (∏ p ∈ S, p ^ 2) := by
    have ⟨hcop2, hcop3⟩ := coprime_of_primes_ge_five fun p hp => ⟨(hS p hp).1, (hS p hp).2.1⟩
    have hsq : (∏ p ∈ S, p ^ 2) = (∏ p ∈ S, p) ^ 2 := Finset.prod_pow S 2 (fun p => p)
    rw [hsq]
    have h4 : Nat.Coprime 4 (∏ p ∈ S, p) := by
      have : (4 : ℕ) = 2 ^ 2 := by norm_num
      rw [this]
      exact hcop2.pow_left 2
    have h27c : Nat.Coprime 27 (∏ p ∈ S, p) := by
      have : (27 : ℕ) = 3 ^ 3 := by norm_num
      rw [this]
      exact hcop3.pow_left 3
    exact (h4.mul_left h27c).pow_right 2
  exact hcop.mul_dvd_of_dvd_of_dvd hbase hprod

/-- Unified square-product divisibility statement covering both Case I (`4 * 9`) and Case II
(`4 * 27`). -/
theorem base_mul_prod_sq_dvd {x : ℕ} (hx : IsCarmichaelCounterexample x)
    (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p ∧ 5 ≤ p ∧ p ^ 2 ∣ x) :
    (4 * 9) * (∏ p ∈ S, p ^ 2) ∣ x ∧ (27 ∣ x → (4 * 27) * (∏ p ∈ S, p ^ 2) ∣ x) :=
  ⟨base_mul_prod_sq_dvd_case1 hx S hS, fun h27 => base_mul_prod_sq_dvd_case2 hx h27 S hS⟩

/-- Chunked product identity: for pairwise-disjoint prime chunks `chunkPrimes c`,
`∏ c ∈ chunks, (∏ p ∈ chunkPrimes c, p) ^ 2 = ∏ p ∈ chunks.biUnion chunkPrimes, p ^ 2`. -/
theorem prod_chunk_sq_eq_biUnion {ι : Type*} [DecidableEq ι]
    (chunks : Finset ι) (chunkPrimes : ι → Finset ℕ)
    (hdisj : Set.PairwiseDisjoint (chunks : Set ι) chunkPrimes) :
    (∏ c ∈ chunks, (∏ p ∈ chunkPrimes c, p) ^ 2) =
      ∏ p ∈ chunks.biUnion chunkPrimes, p ^ 2 := by
  rw [Finset.prod_biUnion hdisj]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [Finset.prod_pow]

/-! ## Bit-length & base-10 digit lower-bound soundness (`ct_bound_check.py`) -/

/-- Exact link to Python's `n.bit_length() - 1`: for `n > 0`, `2 ^ n.log2 ≤ n`. -/
theorem two_pow_log2_le_self {n : ℕ} (hn : 0 < n) : 2 ^ n.log2 ≤ n := by
  rw [Nat.log2_eq_log_two]
  exact Nat.pow_log_le_self 2 (by omega)

/-- Helper: `∏ c ∈ s, a ^ f c = a ^ ∑ c ∈ s, f c`. -/
private theorem prod_pow_eq_pow_sum_nat {ι : Type*} (s : Finset ι) (a : ℕ) (f : ι → ℕ) :
    (∏ c ∈ s, a ^ f c) = a ^ (∑ c ∈ s, f c) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert c s hc ih =>
    rw [Finset.prod_insert hc, Finset.sum_insert hc, pow_add, ih]

/-- **Bit-sum to base-10 digit bound soundness** (exact match to `ct_bound_check.py`'s `bits_of`
and `log10_2_below`):
If `B * ∏ c ∈ chunks, (G c) ^ 2 ∣ x` (`0 < x`), `2 ^ b0 ≤ B`, `∀ c ∈ chunks, 2 ^ (bc c) ≤ (G c)^2`,
`0 < q10`, and `10 ^ p10 < 2 ^ q10`, then `10 ^ (p10 * (b0 + ∑ c ∈ chunks, bc c) / q10) ≤ x`. -/
theorem digit_bound_of_bit_sum {ι : Type*}
    {x B b0 p10 q10 : ℕ} {chunks : Finset ι} {G bc : ι → ℕ}
    (hx : 0 < x)
    (hdvd : B * (∏ c ∈ chunks, (G c) ^ 2) ∣ x)
    (hb0 : 2 ^ b0 ≤ B)
    (hbc : ∀ c ∈ chunks, 2 ^ (bc c) ≤ (G c) ^ 2)
    (hq10 : 0 < q10)
    (hlog : 10 ^ p10 < 2 ^ q10) :
    10 ^ (p10 * (b0 + ∑ c ∈ chunks, bc c) / q10) ≤ x := by
  have _ := hq10
  set bits := b0 + ∑ c ∈ chunks, bc c
  set D := p10 * bits / q10
  have hprod_le : 2 ^ (∑ c ∈ chunks, bc c) ≤ ∏ c ∈ chunks, (G c) ^ 2 := by
    rw [← prod_pow_eq_pow_sum_nat chunks 2 bc]
    exact Finset.prod_le_prod fun c hc => hbc c hc
  have hbits_le_x : 2 ^ bits ≤ x := by
    calc
      2 ^ bits = 2 ^ b0 * 2 ^ (∑ c ∈ chunks, bc c) := pow_add 2 b0 _
      _ ≤ B * (∏ c ∈ chunks, (G c) ^ 2) := Nat.mul_le_mul hb0 hprod_le
      _ ≤ x := Nat.le_of_dvd hx hdvd
  rcases Nat.eq_zero_or_pos p10 with rfl | hp10
  · simp [D]
    omega
  have hDq : D * q10 ≤ p10 * bits := Nat.div_mul_le_self (p10 * bits) q10
  have hpow_le : (10 ^ D) ^ p10 ≤ x ^ p10 := by
    calc
      (10 ^ D) ^ p10 = (10 ^ p10) ^ D := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≤ (2 ^ q10) ^ D := Nat.pow_le_pow_left (le_of_lt hlog) D
      _ = 2 ^ (D * q10) := by rw [← pow_mul, mul_comm]
      _ ≤ 2 ^ (p10 * bits) := Nat.pow_le_pow_right (by norm_num) hDq
      _ = (2 ^ bits) ^ p10 := by rw [← pow_mul, mul_comm]
      _ ≤ x ^ p10 := Nat.pow_le_pow_left hbits_le_x p10
  exact (Nat.pow_le_pow_iff_left (by omega : p10 ≠ 0)).mp hpow_le

/-- Strict version of `digit_bound_of_bit_sum`: whenever the resulting digit count `D` is
positive, `10 ^ D < x`. -/
theorem digit_bound_strict_of_bit_sum {ι : Type*}
    {x B b0 p10 q10 : ℕ} {chunks : Finset ι} {G bc : ι → ℕ}
    (hx : 0 < x)
    (hdvd : B * (∏ c ∈ chunks, (G c) ^ 2) ∣ x)
    (hb0 : 2 ^ b0 ≤ B)
    (hbc : ∀ c ∈ chunks, 2 ^ (bc c) ≤ (G c) ^ 2)
    (hq10 : 0 < q10)
    (hlog : 10 ^ p10 < 2 ^ q10)
    (hDpos : 0 < p10 * (b0 + ∑ c ∈ chunks, bc c) / q10) :
    10 ^ (p10 * (b0 + ∑ c ∈ chunks, bc c) / q10) < x := by
  have _ := hq10
  set bits := b0 + ∑ c ∈ chunks, bc c
  set D := p10 * bits / q10
  have hp10 : 0 < p10 := by
    by_contra h
    have h0 : p10 = 0 := by omega
    simp [D, h0] at hDpos
  have hprod_le : 2 ^ (∑ c ∈ chunks, bc c) ≤ ∏ c ∈ chunks, (G c) ^ 2 := by
    rw [← prod_pow_eq_pow_sum_nat chunks 2 bc]
    exact Finset.prod_le_prod fun c hc => hbc c hc
  have hbits_le_x : 2 ^ bits ≤ x := by
    calc
      2 ^ bits = 2 ^ b0 * 2 ^ (∑ c ∈ chunks, bc c) := pow_add 2 b0 _
      _ ≤ B * (∏ c ∈ chunks, (G c) ^ 2) := Nat.mul_le_mul hb0 hprod_le
      _ ≤ x := Nat.le_of_dvd hx hdvd
  have hDq : D * q10 ≤ p10 * bits := Nat.div_mul_le_self (p10 * bits) q10
  have hpow_lt : (10 ^ D) ^ p10 < x ^ p10 := by
    calc
      (10 ^ D) ^ p10 = (10 ^ p10) ^ D := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ < (2 ^ q10) ^ D := Nat.pow_lt_pow_left hlog (by omega : D ≠ 0)
      _ = 2 ^ (D * q10) := by rw [← pow_mul, mul_comm]
      _ ≤ 2 ^ (p10 * bits) := Nat.pow_le_pow_right (by norm_num) hDq
      _ = (2 ^ bits) ^ p10 := by rw [← pow_mul, mul_comm]
      _ ≤ x ^ p10 := Nat.pow_le_pow_left hbits_le_x p10
  exact (Nat.pow_lt_pow_iff_left (by omega : p10 ≠ 0)).mp hpow_lt

/-! ## Multi-witness Lucas primality test (Ford Lemma 7.3 / `ct_bound_check.py`) -/

/-- **Ford Lemma 7.3 / Multi-witness Lucas primality test** (the exact primality check used in
`ct_bound_check.py`): if `p ≥ 2` and for every prime divisor `q` of `p - 1` there exists a
witness `a` with `a ^ (p - 1) % p = 1` and `a ^ ((p - 1) / q) % p ≠ 1`, then `p` is prime. -/
theorem prime_of_lucas_witnesses {p : ℕ} (hp : 2 ≤ p)
    (hw : ∀ q : ℕ, Nat.Prime q → q ∣ p - 1 →
      ∃ a : ℕ, a ^ (p - 1) % p = 1 ∧ a ^ ((p - 1) / q) % p ≠ 1) :
    Nat.Prime p := by
  have : NeZero p := ⟨by omega⟩
  have hpm1_pos : 0 < p - 1 := by omega
  have htot_pos : 0 < Nat.totient p := Nat.totient_pos.mpr (by omega)
  have htot_le : Nat.totient p ≤ p - 1 := by
    have := Nat.totient_lt p (by omega)
    omega
  have hdvd : p - 1 ∣ Nat.totient p := by
    rw [← Nat.factorization_le_iff_dvd (by omega) (by omega)]
    intro q
    by_cases hq : Nat.Prime q ∧ q ∣ p - 1
    · rcases hq with ⟨hq_prime, hq_dvd⟩
      obtain ⟨a, ha1, haq⟩ := hw q hq_prime hq_dvd
      have hcast1 : ((a : ZMod p) ^ (p - 1)) = 1 := by
        rw [← Nat.cast_pow]
        conv_rhs => rw [← Nat.cast_one]
        rw [ZMod.natCast_eq_natCast_iff]
        change a ^ (p - 1) % p = 1 % p
        rw [ha1, Nat.mod_eq_of_lt (by omega)]
      have hcastq : ((a : ZMod p) ^ ((p - 1) / q)) ≠ 1 := by
        intro h
        rw [← Nat.cast_pow] at h
        have h' : ((a ^ ((p - 1) / q) : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
          simpa using h
        rw [ZMod.natCast_eq_natCast_iff] at h'
        change a ^ ((p - 1) / q) % p = 1 % p at h'
        have h1m : 1 % p = 1 := Nat.mod_eq_of_lt (by omega)
        rw [h1m] at h'
        exact haq h'
      have hunit : IsUnit (a : ZMod p) := by
        rw [isUnit_iff_exists_inv]
        refine ⟨(a : ZMod p) ^ (p - 2), ?_⟩
        rw [← pow_succ']
        have : p - 2 + 1 = p - 1 := by omega
        rw [this, hcast1]
      rcases hunit with ⟨u, hu⟩
      have hu1 : u ^ (p - 1) = 1 := by
        apply Units.ext
        simpa [hu] using hcast1
      have huq : u ^ ((p - 1) / q) ≠ 1 := by
        intro h
        apply hcastq
        simpa [hu] using congrArg Units.val h
      set d := orderOf u
      have hd_dvd_pm1 : d ∣ p - 1 := orderOf_dvd_of_pow_eq_one hu1
      have hd_ndvd_div : ¬ d ∣ (p - 1) / q := fun h => huq (orderOf_dvd_iff_pow_eq_one.mp h)
      have hd_dvd_tot : d ∣ Nat.totient p := by
        have hcard : Fintype.card (ZMod p)ˣ = Nat.totient p := ZMod.card_units_eq_totient p
        rw [← hcard]
        exact orderOf_dvd_card
      have hd_pos : 0 < d := orderOf_pos u
      have hle_d : (p - 1).factorization q ≤ d.factorization q := by
        by_contra hlt
        have hlt' : d.factorization q < (p - 1).factorization q := Nat.lt_of_not_ge hlt
        have hqd : q * d ∣ p - 1 := by
          rw [← Nat.factorization_le_iff_dvd (mul_ne_zero hq_prime.ne_zero (by omega)) (by omega)]
          intro r
          rw [Nat.factorization_mul hq_prime.ne_zero (by omega)]
          simp only [Finsupp.add_apply]
          by_cases hr : r = q
          · subst hr
            rw [hq_prime.factorization_self]
            omega
          · have hq0 : q.factorization r = 0 := by
              rw [hq_prime.factorization]
              exact Finsupp.single_eq_of_ne hr
            rw [hq0, zero_add]
            exact (Nat.factorization_le_iff_dvd (by omega) (by omega)).mpr hd_dvd_pm1 r
        apply hd_ndvd_div
        rcases hqd with ⟨t, ht⟩
        refine ⟨t, ?_⟩
        have h1 : p - 1 = (d * t) * q := by
          calc
            p - 1 = q * d * t := ht
            _ = (d * t) * q := by ring
        rw [h1, Nat.mul_div_cancel _ hq_prime.pos]
      have hd_le_tot : d.factorization q ≤ (Nat.totient p).factorization q :=
        (Nat.factorization_le_iff_dvd (by omega) (by omega)).mpr hd_dvd_tot q
      exact le_trans hle_d hd_le_tot
    · have h0 : (p - 1).factorization q = 0 := by
        by_cases hqp : Nat.Prime q
        · have hnd : ¬ q ∣ p - 1 := fun hd => hq ⟨hqp, hd⟩
          exact Nat.factorization_eq_zero_of_not_dvd hnd
        · exact Nat.factorization_eq_zero_of_not_prime (p - 1) hqp
      rw [h0]
      exact Nat.zero_le _
  have htot_eq : Nat.totient p = p - 1 := le_antisymm htot_le (Nat.le_of_dvd htot_pos hdvd)
  exact (Nat.totient_eq_iff_prime (by omega)).mp htot_eq

/-! ## Conditional `ct-bound-3` Certificate Bridge -/

/-- A verified Case I certificate witnessing pairwise-disjoint chunks of Case I forced primes
(`ForcedCase1`), bit-length lower bounds on base `4 * 9` and each chunk square product, and an
exact rational lower bound `p10 / q10 < log10(2)` (`10 ^ p10 < 2 ^ q10`). -/
structure Case1Certificate where
  ι : Type
  [decEq : DecidableEq ι]
  chunks : Finset ι
  chunkPrimes : ι → Finset ℕ
  pairwiseDisjoint : Set.PairwiseDisjoint (chunks : Set ι) chunkPrimes
  allForced : ∀ c ∈ chunks, ∀ p ∈ chunkPrimes c, ForcedCase1 p
  b0 : ℕ
  hb0 : 2 ^ b0 ≤ 4 * 9
  bc : ι → ℕ
  hbc : ∀ c ∈ chunks, 2 ^ (bc c) ≤ (∏ p ∈ chunkPrimes c, p) ^ 2
  p10 : ℕ
  q10 : ℕ
  hq10 : 0 < q10
  hlog : 10 ^ p10 < 2 ^ q10

attribute [instance] Case1Certificate.decEq

/-- Base-10 digit lower bound certified by a `Case1Certificate`. -/
def Case1Certificate.digits (cert : Case1Certificate) : ℕ :=
  cert.p10 * (cert.b0 + ∑ c ∈ cert.chunks, cert.bc c) / cert.q10

/-- A verified Case II certificate witnessing pairwise-disjoint chunks of Case II forced primes
(`ForcedCase2`), bit-length lower bounds on base `4 * 27` and each chunk square product, and an
exact rational lower bound `p10 / q10 < log10(2)` (`10 ^ p10 < 2 ^ q10`). -/
structure Case2Certificate where
  ι : Type
  [decEq : DecidableEq ι]
  chunks : Finset ι
  chunkPrimes : ι → Finset ℕ
  pairwiseDisjoint : Set.PairwiseDisjoint (chunks : Set ι) chunkPrimes
  allForced : ∀ c ∈ chunks, ∀ p ∈ chunkPrimes c, ForcedCase2 p
  b0 : ℕ
  hb0 : 2 ^ b0 ≤ 4 * 27
  bc : ι → ℕ
  hbc : ∀ c ∈ chunks, 2 ^ (bc c) ≤ (∏ p ∈ chunkPrimes c, p) ^ 2
  p10 : ℕ
  q10 : ℕ
  hq10 : 0 < q10
  hlog : 10 ^ p10 < 2 ^ q10

attribute [instance] Case2Certificate.decEq

/-- Base-10 digit lower bound certified by a `Case2Certificate`. -/
def Case2Certificate.digits (cert : Case2Certificate) : ℕ :=
  cert.p10 * (cert.b0 + ∑ c ∈ cert.chunks, cert.bc c) / cert.q10

/-- Paired Case I + Case II certificate interface matching the external `ct-bound-3`
1.965B-prime verification pipeline (`ct_bound_check.py`). This structure is an explicit
parameterized bridge: the `ct-bound-3` bound `10^100,000,160,994` is NOT proved unconditionally
in the Lean kernel; rather, `carmichael_bound_from_certificate` proves that ANY valid pair of
Case I and Case II certificates unconditionally forces `10 ^ min(D₁, D₂) ≤ x`. -/
structure CarmichaelBoundCertificate where
  case1 : Case1Certificate
  case2 : Case2Certificate

/-- Overall digit lower bound `min(D₁, D₂)` certified by a `CarmichaelBoundCertificate`. -/
def CarmichaelBoundCertificate.digits (cert : CarmichaelBoundCertificate) : ℕ :=
  min cert.case1.digits cert.case2.digits

/-- Soundness of a `Case1Certificate` on any Case I counterexample (`¬ 27 ∣ x`). -/
theorem case1_bound_from_certificate (cert : Case1Certificate) {x : ℕ}
    (hx : IsCarmichaelCounterexample x) (h27 : ¬ 27 ∣ x) :
    10 ^ cert.digits ≤ x := by
  have hS : ∀ p ∈ cert.chunks.biUnion cert.chunkPrimes, Nat.Prime p ∧ 5 ≤ p ∧ p ^ 2 ∣ x := by
    intro p hp
    rcases Finset.mem_biUnion.mp hp with ⟨c, hc, hpc⟩
    exact forcedCase1_sound hx h27 (cert.allForced c hc p hpc)
  have hdvd : (4 * 9) * (∏ c ∈ cert.chunks, (∏ p ∈ cert.chunkPrimes c, p) ^ 2) ∣ x := by
    rw [prod_chunk_sq_eq_biUnion cert.chunks cert.chunkPrimes cert.pairwiseDisjoint]
    exact base_mul_prod_sq_dvd_case1 hx _ hS
  exact digit_bound_of_bit_sum hx.1 hdvd cert.hb0 cert.hbc cert.hq10 cert.hlog

/-- Soundness of a `Case2Certificate` on any Case II counterexample (`27 ∣ x`). -/
theorem case2_bound_from_certificate (cert : Case2Certificate) {x : ℕ}
    (hx : IsCarmichaelCounterexample x) (h27 : 27 ∣ x) :
    10 ^ cert.digits ≤ x := by
  have hS : ∀ p ∈ cert.chunks.biUnion cert.chunkPrimes, Nat.Prime p ∧ 5 ≤ p ∧ p ^ 2 ∣ x := by
    intro p hp
    rcases Finset.mem_biUnion.mp hp with ⟨c, hc, hpc⟩
    exact forcedCase2_sound hx h27 (cert.allForced c hc p hpc)
  have hdvd : (4 * 27) * (∏ c ∈ cert.chunks, (∏ p ∈ cert.chunkPrimes c, p) ^ 2) ∣ x := by
    rw [prod_chunk_sq_eq_biUnion cert.chunks cert.chunkPrimes cert.pairwiseDisjoint]
    exact base_mul_prod_sq_dvd_case2 hx h27 _ hS
  exact digit_bound_of_bit_sum hx.1 hdvd cert.hb0 cert.hbc cert.hq10 cert.hlog

/-- **Conditional `ct-bound-3` certificate bridge**:
For any valid `CarmichaelBoundCertificate`, every Carmichael totient counterexample satisfies
`10 ^ cert.digits ≤ x`. -/
theorem carmichael_bound_from_certificate (cert : CarmichaelBoundCertificate) {x : ℕ}
    (hx : IsCarmichaelCounterexample x) :
    10 ^ cert.digits ≤ x := by
  rcases carmichael_case_split hx with ⟨_, h27, _⟩ | h27
  · exact le_trans (Nat.pow_le_pow_right (by norm_num) (min_le_left _ _))
      (case1_bound_from_certificate cert.case1 hx h27)
  · exact le_trans (Nat.pow_le_pow_right (by norm_num) (min_le_right _ _))
      (case2_bound_from_certificate cert.case2 hx h27)

/-- Strict version of `carmichael_bound_from_certificate` when `0 < cert.digits`. -/
theorem carmichael_bound_strict_from_certificate (cert : CarmichaelBoundCertificate)
    (hD : 0 < cert.digits) {x : ℕ} (hx : IsCarmichaelCounterexample x) :
    10 ^ cert.digits < x := by
  have hD1 : 0 < cert.case1.digits := lt_of_lt_of_le hD (min_le_left _ _)
  have hD2 : 0 < cert.case2.digits := lt_of_lt_of_le hD (min_le_right _ _)
  rcases carmichael_case_split hx with ⟨_, h27, _⟩ | h27
  · have hS : ∀ p ∈ cert.case1.chunks.biUnion cert.case1.chunkPrimes,
        Nat.Prime p ∧ 5 ≤ p ∧ p ^ 2 ∣ x := by
      intro p hp
      rcases Finset.mem_biUnion.mp hp with ⟨c, hc, hpc⟩
      exact forcedCase1_sound hx h27 (cert.case1.allForced c hc p hpc)
    have hdvd : (4 * 9) * (∏ c ∈ cert.case1.chunks,
        (∏ p ∈ cert.case1.chunkPrimes c, p) ^ 2) ∣ x := by
      rw [prod_chunk_sq_eq_biUnion cert.case1.chunks cert.case1.chunkPrimes
        cert.case1.pairwiseDisjoint]
      exact base_mul_prod_sq_dvd_case1 hx _ hS
    exact lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (min_le_left _ _))
      (digit_bound_strict_of_bit_sum hx.1 hdvd cert.case1.hb0 cert.case1.hbc
        cert.case1.hq10 cert.case1.hlog hD1)
  · have hS : ∀ p ∈ cert.case2.chunks.biUnion cert.case2.chunkPrimes,
        Nat.Prime p ∧ 5 ≤ p ∧ p ^ 2 ∣ x := by
      intro p hp
      rcases Finset.mem_biUnion.mp hp with ⟨c, hc, hpc⟩
      exact forcedCase2_sound hx h27 (cert.case2.allForced c hc p hpc)
    have hdvd : (4 * 27) * (∏ c ∈ cert.case2.chunks,
        (∏ p ∈ cert.case2.chunkPrimes c, p) ^ 2) ∣ x := by
      rw [prod_chunk_sq_eq_biUnion cert.case2.chunks cert.case2.chunkPrimes
        cert.case2.pairwiseDisjoint]
      exact base_mul_prod_sq_dvd_case2 hx h27 _ hS
    exact lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (min_le_right _ _))
      (digit_bound_strict_of_bit_sum hx.1 hdvd cert.case2.hb0 cert.case2.hbc
        cert.case2.hq10 cert.case2.hlog hD2)

end CarmichaelTotient
