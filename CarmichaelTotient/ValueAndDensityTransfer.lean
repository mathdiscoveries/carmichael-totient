module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Analysis.Complex.ExponentialBounds
public import CarmichaelTotient.Lemma72
public import CarmichaelTotient.CaseRules
public import CarmichaelTotient.TreeAndKleeBounds

import Mathlib.Tactic

/-!
# Totient Value Transfer, Ford's Lemmas 7.4–7.5, and Singleton Density Bound

Formalizes Section 3 (Corollary 3) of the Carmichael totient manuscript inside Lean 4:

1. **Reciprocal-sum totient-value transfer (`totient_value_gt_of_forced_primes`):**
   If `d = b * ∏ p ∈ S, p ^ 2 ∣ x` (`b ∈ {36, 108}`, `p ≥ 5` prime for `p ∈ S`),
   `6 * 10 ^ D ≤ d`, and `∑ p ∈ S, (1 / p : ℝ) < 1 / 2`, then `10 ^ D < Nat.totient x`.
2. **Ford's Lemmas 7.4–7.5 (`ford_lemma_7_4_7_5`):**
   For every `a ≥ 2` and `X : ℕ`, the count `VDiv X a` of totient values `n ≤ X` whose
   every positive preimage is divisible by `a ^ 2` satisfies `VDiv X a ≤ V (X / a)`.
3. **Limiting singleton density bound (`liminf_V1_div_V_le_two_div_min`):**
   If every Carmichael counterexample `x` satisfies `a₁ ^ 2 ∣ x ∨ a₂ ^ 2 ∣ x` with
   `2 ≤ a₁, a₂`, then `Filter.liminf (fun X => (V1 X : ℝ) / (V X : ℝ)) Filter.atTop ≤ 2 / min a₁ a₂`.
   Proved via Chebyshev's elementary lower bound `Chebyshev.pi_ge` already in Mathlib.
4. **Combined Corollary 3 certificate bridge (`corollary_value_and_density_transfer`)**
   and **unconditional pure-kernel density bound (`carmichael_liminf_density_lt_10_pow_neg_5057`)**
   derived directly from `masaiValetteCase1Cert` and `masaiValetteCase2Cert`.
-/

@[expose] public section

namespace CarmichaelTotient

open Filter Finset

/-! ## Part 1: Weierstrass Product Bound and Totient Value Transfer -/

/-- Elementary Weierstrass lower bound: for `0 ≤ u i ≤ 1`,
`1 - ∑ i ∈ S, u i ≤ ∏ i ∈ S, (1 - u i)`. -/
theorem one_sub_sum_le_prod_one_sub {α : Type*} [DecidableEq α] (S : Finset α) (u : α → ℝ)
    (hu0 : ∀ i ∈ S, 0 ≤ u i) (hu1 : ∀ i ∈ S, u i ≤ 1) :
    1 - ∑ i ∈ S, u i ≤ ∏ i ∈ S, (1 - u i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have ha0 : 0 ≤ u a := hu0 a (Finset.mem_insert_self a s)
    have ha1 : u a ≤ 1 := hu1 a (Finset.mem_insert_self a s)
    have hs0 : ∀ i ∈ s, 0 ≤ u i := fun i hi => hu0 i (Finset.mem_insert_of_mem hi)
    have hs1 : ∀ i ∈ s, u i ≤ 1 := fun i hi => hu1 i (Finset.mem_insert_of_mem hi)
    have hsum_nonneg : 0 ≤ ∑ i ∈ s, u i := Finset.sum_nonneg hs0
    have hih : 1 - ∑ i ∈ s, u i ≤ ∏ i ∈ s, (1 - u i) := ih hs0 hs1
    have hmul : (1 - u a) * (1 - ∑ i ∈ s, u i) ≤ (1 - u a) * ∏ i ∈ s, (1 - u i) :=
      mul_le_mul_of_nonneg_left hih (by linarith)
    nlinarith

/-- Exact totient ratio of `b * ∏ p ∈ S, p ^ 2` when `b ∈ {36, 108}` and every `p ∈ S`
is a prime `≥ 5`. -/
theorem totient_forcedDivisor_eq_real {b : ℕ} {S : Finset ℕ}
    (hb : b = 36 ∨ b = 108) (hS : ∀ p ∈ S, Nat.Prime p ∧ 5 ≤ p) :
    (Nat.totient (b * ∏ p ∈ S, p ^ 2) : ℝ) =
      ((b * ∏ p ∈ S, p ^ 2 : ℕ) : ℝ) * (1 / 3 : ℝ) * ∏ p ∈ S, (1 - (1 : ℝ) / (p : ℝ)) := by
  have hcop_b : Nat.Coprime b (∏ p ∈ S, p ^ 2) := by
    refine Nat.Coprime.prod_right fun p hp => ?_
    obtain ⟨hp_prime, hp5⟩ := hS p hp
    refine Nat.Coprime.pow_right 2 ?_
    rcases hb with rfl | rfl
    · have h2 : ¬ p ∣ 2 := fun h => by have := Nat.le_of_dvd (by decide) h; omega
      have h3 : ¬ p ∣ 3 := fun h => by have := Nat.le_of_dvd (by decide) h; omega
      have h36 : ¬ p ∣ 36 := by
        intro h
        have : p ∣ 2 ^ 2 * 3 ^ 2 := by simpa using h
        rcases hp_prime.dvd_mul.mp this with h2' | h3'
        · exact h2 (hp_prime.dvd_of_dvd_pow h2')
        · exact h3 (hp_prime.dvd_of_dvd_pow h3')
      exact (hp_prime.coprime_iff_not_dvd.mpr h36).symm
    · have h2 : ¬ p ∣ 2 := fun h => by have := Nat.le_of_dvd (by decide) h; omega
      have h3 : ¬ p ∣ 3 := fun h => by have := Nat.le_of_dvd (by decide) h; omega
      have h108 : ¬ p ∣ 108 := by
        intro h
        have : p ∣ 2 ^ 2 * 3 ^ 3 := by simpa using h
        rcases hp_prime.dvd_mul.mp this with h2' | h3'
        · exact h2 (hp_prime.dvd_of_dvd_pow h2')
        · exact h3 (hp_prime.dvd_of_dvd_pow h3')
      exact (hp_prime.coprime_iff_not_dvd.mpr h108).symm
  have hphi_b : (Nat.totient b : ℝ) = (b : ℝ) * (1 / 3 : ℝ) := by
    rcases hb with rfl | rfl
    · have : Nat.totient 36 = 12 := by decide
      rw [this]; norm_num
    · have : Nat.totient 108 = 36 := by decide
      rw [this]; norm_num
  have hphi_prod : ∀ T : Finset ℕ, (∀ p ∈ T, Nat.Prime p) →
      (Nat.totient (∏ p ∈ T, p ^ 2) : ℝ) =
        ((∏ p ∈ T, p ^ 2 : ℕ) : ℝ) * ∏ p ∈ T, (1 - (1 : ℝ) / (p : ℝ)) := by
    intro T hT
    induction T using Finset.induction_on with
    | empty => simp
    | @insert q t hqt ih =>
      have hq : Nat.Prime q := hT q (Finset.mem_insert_self q t)
      have ht : ∀ p ∈ t, Nat.Prime p := fun p hp => hT p (Finset.mem_insert_of_mem hp)
      have hcop_qt : Nat.Coprime (q ^ 2) (∏ p ∈ t, p ^ 2) := by
        refine Nat.Coprime.prod_right fun p hp => ?_
        have hne : q ≠ p := fun h => hqt (h ▸ hp)
        exact ((Nat.coprime_primes hq (ht p hp)).mpr hne).pow 2 2
      rw [Finset.prod_insert hqt, Finset.prod_insert hqt, Nat.totient_mul hcop_qt,
        Nat.cast_mul, Nat.cast_mul, ih ht]
      have hphi_q2 : (Nat.totient (q ^ 2) : ℝ) = ((q ^ 2 : ℕ) : ℝ) * (1 - (1 : ℝ) / (q : ℝ)) := by
        rw [Nat.totient_prime_pow hq (by decide : 0 < 2)]
        have hq_pos : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
        have hq1 : (1 : ℕ) ≤ q := hq.one_le
        push_cast [hq1]
        field_simp [hq_pos]
      rw [hphi_q2]
      ring
  rw [Nat.totient_mul hcop_b, Nat.cast_mul, Nat.cast_mul, hphi_b,
    hphi_prod S (fun p hp => (hS p hp).1)]
  ring

/-- **Totient Value Transfer (Corollary 3, Part 1):**
If `d = b * ∏ p ∈ S, p ^ 2 ∣ x` (`b ∈ {36, 108}`, primes `p ≥ 5`), `6 * 10 ^ D ≤ d`,
and `∑ p ∈ S, (1 / p : ℝ) < 1 / 2`, then `10 ^ D < Nat.totient x`. -/
theorem totient_value_gt_of_forced_primes
    {D b x : ℕ} {S : Finset ℕ}
    (hx : 0 < x)
    (hb : b = 36 ∨ b = 108)
    (hS : ∀ p ∈ S, Nat.Prime p ∧ 5 ≤ p)
    (hdvd : b * ∏ p ∈ S, p ^ 2 ∣ x)
    (hbig : 6 * 10 ^ D ≤ b * ∏ p ∈ S, p ^ 2)
    (hrec : ∑ p ∈ S, (1 : ℝ) / (p : ℝ) < 1 / 2) :
    10 ^ D < Nat.totient x := by
  set d : ℕ := b * ∏ p ∈ S, p ^ 2
  have hd_pos : 0 < d := by
    have h6 : 0 < 6 * 10 ^ D := by positivity
    exact lt_of_lt_of_le h6 hbig
  have hprod_ge : (1 : ℝ) - ∑ p ∈ S, (1 : ℝ) / (p : ℝ) ≤ ∏ p ∈ S, (1 - (1 : ℝ) / (p : ℝ)) := by
    refine one_sub_sum_le_prod_one_sub S (fun p => (1 : ℝ) / (p : ℝ)) ?_ ?_
    · intro p hp
      have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr (hS p hp).1.pos
      positivity
    · intro p hp
      have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hS p hp).1.one_le
      exact div_le_one_of_le₀ hp1 (by linarith)
  have hprod_gt : (1 / 2 : ℝ) < ∏ p ∈ S, (1 - (1 : ℝ) / (p : ℝ)) := by linarith
  have hphi_d : (Nat.totient d : ℝ) = (d : ℝ) * (1 / 3 : ℝ) * ∏ p ∈ S, (1 - (1 : ℝ) / (p : ℝ)) :=
    totient_forcedDivisor_eq_real hb hS
  have hd_real_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd_pos
  have hphi_d_gt : (d : ℝ) * (1 / 6 : ℝ) < (Nat.totient d : ℝ) := by
    rw [hphi_d]
    have hmul : (d : ℝ) * (1 / 3 : ℝ) * (1 / 2 : ℝ) <
        (d : ℝ) * (1 / 3 : ℝ) * ∏ p ∈ S, (1 - (1 : ℝ) / (p : ℝ)) :=
      mul_lt_mul_of_pos_left hprod_gt (by positivity)
    linarith
  have hbig_real : (6 : ℝ) * ((10 ^ D : ℕ) : ℝ) ≤ (d : ℝ) := by exact_mod_cast hbig
  have h10_lt_phi_d : ((10 ^ D : ℕ) : ℝ) < (Nat.totient d : ℝ) := by linarith
  have h10_lt_phi_d_nat : 10 ^ D < Nat.totient d := by exact_mod_cast h10_lt_phi_d
  have hphi_dvd : Nat.totient d ∣ Nat.totient x := Nat.totient_dvd_of_dvd hdvd
  have hphi_x_pos : 0 < Nat.totient x := Nat.totient_pos.mpr hx
  exact lt_of_lt_of_le h10_lt_phi_d_nat (Nat.le_of_dvd hphi_x_pos hphi_dvd)

/-! ## Part 2: Totient Counting Functions and Ford's Lemmas 7.4–7.5 -/

/-- `n` lies in the image of Euler's totient on positive integers. -/
def IsTotientValue (n : ℕ) : Prop :=
  ∃ y : ℕ, 0 < y ∧ Nat.totient y = n

/-- `V X`: count of distinct totient values `1 ≤ n ≤ X`. -/
noncomputable def V (X : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 X).filter (fun n => IsTotientValue n)).card

/-- `V1 X`: count of singleton totient values `1 ≤ n ≤ X` (those with `A(n) = 1`). -/
noncomputable def V1 (X : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 X).filter
    (fun n => ∃ x : ℕ, IsCarmichaelCounterexample x ∧ Nat.totient x = n)).card

/-- `VDiv X a`: count of totient values `1 ≤ n ≤ X` whose every positive preimage is
divisible by `a ^ 2` (denoted `V(X; a²)` in Ford 1998, Lemmas 7.4–7.5). -/
noncomputable def VDiv (X a : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 X).filter
    (fun n => IsTotientValue n ∧ ∀ y : ℕ, 0 < y → Nat.totient y = n → a ^ 2 ∣ y)).card

/-- Multiplicativity when every prime factor of `u` already divides `z`:
`φ(u * z) = u * φ(z)`. -/
theorem totient_mul_of_prime_dvd {u z : ℕ} (hu : 0 < u) (_hz : 0 < z)
    (hdvd : ∀ p : ℕ, Nat.Prime p → p ∣ u → p ∣ z) :
    Nat.totient (u * z) = u * Nat.totient z := by
  induction u using Nat.strong_induction_on with
  | h u ih =>
    by_cases hu1 : u = 1
    · subst hu1; simp
    · obtain ⟨p, hp_prime, hpu⟩ := Nat.exists_prime_and_dvd (by omega : u ≠ 1)
      rcases hpu with ⟨u', rfl⟩
      have hu'_pos : 0 < u' := Nat.pos_of_mul_pos_left hu
      have hpz : p ∣ z := hdvd p hp_prime (dvd_mul_right p u')
      have hp_u'z : p ∣ u' * z := dvd_mul_of_dvd_right hpz u'
      have hmul : p * u' * z = p * (u' * z) := mul_assoc p u' z
      rw [hmul, Nat.totient_mul_of_prime_of_dvd hp_prime hp_u'z]
      have hlt : u' < p * u' := lt_mul_of_one_lt_left hu'_pos hp_prime.one_lt
      have hsub : ∀ q : ℕ, Nat.Prime q → q ∣ u' → q ∣ z :=
        fun q hq hqu' => hdvd q hq (dvd_mul_of_dvd_right hqu' p)
      rw [ih u' hlt hu'_pos hsub, mul_assoc]

/-- Totient power scaling: for `a ≥ 1`, `r ≥ 1`, `t ≥ 1`,
`φ(a ^ t * r) = a ^ (t - 1) * φ(a * r)` without any coprimality assumption on `a` and `r`. -/
theorem totient_pow_mul_eq {a t r : ℕ} (ha : 0 < a) (ht : 1 ≤ t) (hr : 0 < r) :
    Nat.totient (a ^ t * r) = a ^ (t - 1) * Nat.totient (a * r) := by
  have hpow : a ^ t * r = a ^ (t - 1) * (a * r) := by
    calc a ^ t * r = a ^ (t - 1 + 1) * r := by rw [Nat.sub_add_cancel ht]
      _ = (a ^ (t - 1) * a) * r := by rw [pow_succ]
      _ = a ^ (t - 1) * (a * r) := by rw [mul_assoc]
  rw [hpow]
  refine totient_mul_of_prime_dvd (pow_pos ha _) (mul_pos ha hr) ?_
  intro p hp hpdvd
  exact dvd_mul_of_dvd_left (hp.dvd_of_dvd_pow hpdvd) r

/-- Every positive `y` divisible by `a ^ 2` (`a ≥ 2`) factors as `y = a ^ t * r` with
`2 ≤ t`, `0 < r`, and `¬ (a ∣ r)`. -/
theorem exists_max_pow_dvd {a y : ℕ} (ha : 2 ≤ a) (hy : 0 < y) (hsq : a ^ 2 ∣ y) :
    ∃ t r : ℕ, 2 ≤ t ∧ 0 < r ∧ ¬ (a ∣ r) ∧ y = a ^ t * r := by
  have haux : ∀ m : ℕ, 0 < m → ∃ k r : ℕ, 0 < r ∧ ¬ (a ∣ r) ∧ m = a ^ k * r := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hm
      by_cases hdiv : a ∣ m
      · rcases hdiv with ⟨m', rfl⟩
        have hm'_pos : 0 < m' := Nat.pos_of_mul_pos_left hm
        have hlt : m' < a * m' := lt_mul_of_one_lt_left hm'_pos (by omega)
        obtain ⟨k, r, hr, hndiv, heq⟩ := ih m' hlt hm'_pos
        refine ⟨k + 1, r, hr, hndiv, ?_⟩
        rw [heq, pow_succ']; ring
      · exact ⟨0, m, hm, hdiv, by simp⟩
  rcases hsq with ⟨w, rfl⟩
  have hw_pos : 0 < w := Nat.pos_of_mul_pos_left hy
  obtain ⟨k, r, hr, hndiv, heq⟩ := haux w hw_pos
  refine ⟨k + 2, r, by omega, hr, hndiv, ?_⟩
  rw [heq, pow_add]; ring

/-- **Ford's Lemmas 7.4–7.5 (1998):**
For every `a ≥ 2` and `X : ℕ`, `VDiv X a ≤ V (X / a)`. -/
theorem ford_lemma_7_4_7_5 {X a : ℕ} (ha : 2 ≤ a) :
    VDiv X a ≤ V (X / a) := by
  classical
  set S := (Finset.Icc 1 X).filter
    (fun n => IsTotientValue n ∧ ∀ y : ℕ, 0 < y → Nat.totient y = n → a ^ 2 ∣ y)
  set T := (Finset.Icc 1 (X / a)).filter (fun n => IsTotientValue n)
  change S.card ≤ T.card
  set Slo := S.filter (fun n => n ≤ X / a)
  set Shi := S.filter (fun n => X / a < n)
  have hsplit : S.card = Slo.card + Shi.card := by
    have hdisj : Disjoint Slo Shi := by
      rw [Finset.disjoint_left]
      intro n h1 h2
      simp only [Slo, Shi, Finset.mem_filter] at h1 h2
      omega
    have hunion : Slo ∪ Shi = S := by
      ext n
      simp only [Slo, Shi, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨hS, _⟩ | ⟨hS, _⟩) <;> exact hS
      · intro hS
        by_cases hle : n ≤ X / a
        · exact Or.inl ⟨hS, hle⟩
        · exact Or.inr ⟨hS, by omega⟩
    rw [← hunion, Finset.card_union_of_disjoint hdisj]
  have hSlo_sub : Slo ⊆ T := by
    intro n hn
    simp only [Slo, S, T, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    exact ⟨⟨hn.1.1.1, hn.2⟩, hn.1.2.1⟩
  have hT_split : T.card = Slo.card + (T \ Slo).card := by
    rw [← Finset.card_sdiff_add_card_eq_card hSlo_sub, add_comm]
  rw [hsplit, hT_split]
  apply Nat.add_le_add_left
  -- Construct an injection f : Shi → T \ Slo via n = φ(a^t * r) ↦ φ(a * r)
  have hchoice : ∀ n ∈ Shi, ∃ t r : ℕ, 2 ≤ t ∧ 0 < r ∧ ¬ (a ∣ r) ∧
      Nat.totient (a ^ t * r) = n := by
    intro n hn
    simp only [Shi, S, Finset.mem_filter] at hn
    obtain ⟨y, hy_pos, hy_phi⟩ := hn.1.2.1
    have hsq : a ^ 2 ∣ y := hn.1.2.2 y hy_pos hy_phi
    obtain ⟨t, r, ht, hr, hndiv, rfl⟩ := exists_max_pow_dvd ha hy_pos hsq
    exact ⟨t, r, ht, hr, hndiv, hy_phi⟩
  let f : ℕ → ℕ := fun n =>
    if h : n ∈ Shi then
      let t := (hchoice n h).choose
      let r := (hchoice n h).choose_spec.choose
      Nat.totient (a * r)
    else 0
  have hf_maps : ∀ n ∈ Shi, f n ∈ T \ Slo := by
    intro n hn
    simp only [f, hn, ↓reduceDIte]
    set t := (hchoice n hn).choose
    set r := (hchoice n hn).choose_spec.choose
    have hspec := (hchoice n hn).choose_spec.choose_spec
    obtain ⟨ht, hr, hndiv, hphi⟩ := hspec
    have ha_pos : 0 < a := by omega
    have har_pos : 0 < a * r := mul_pos ha_pos hr
    have hrel : n = a ^ (t - 1) * Nat.totient (a * r) := by
      rw [← hphi, totient_pow_mul_eq ha_pos (by omega) hr]
    have ha_le_pow : a ≤ a ^ (t - 1) := by
      have : a ^ 1 ≤ a ^ (t - 1) := Nat.pow_le_pow_right ha_pos (by omega)
      simpa using this
    have hphi_pos : 1 ≤ Nat.totient (a * r) := Nat.totient_pos.mpr har_pos
    have hn_le_X : n ≤ X := by
      simp only [Shi, S, Finset.mem_filter, Finset.mem_Icc] at hn
      exact hn.1.1.2
    have hphi_le : Nat.totient (a * r) ≤ X / a := by
      rw [Nat.le_div_iff_mul_le ha_pos]
      calc Nat.totient (a * r) * a
          = a * Nat.totient (a * r) := mul_comm _ _
        _ ≤ a ^ (t - 1) * Nat.totient (a * r) := Nat.mul_le_mul_right _ ha_le_pow
        _ = n := hrel.symm
        _ ≤ X := hn_le_X
    rw [Finset.mem_sdiff]
    refine ⟨?_, ?_⟩
    · simp only [T, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hphi_pos, hphi_le⟩, ⟨a * r, har_pos, rfl⟩⟩
    · intro hmem
      simp only [Slo, S, Finset.mem_filter] at hmem
      have hsq : a ^ 2 ∣ a * r := hmem.1.2.2 (a * r) har_pos rfl
      rw [sq] at hsq
      have : a ∣ r := (Nat.mul_dvd_mul_iff_left ha_pos).mp hsq
      exact hndiv this
  have hf_inj : Set.InjOn f (Shi : Set ℕ) := by
    intro n₁ hn₁ n₂ hn₂ heq
    simp only [Finset.mem_coe] at hn₁ hn₂
    have hf1 : f n₁ = Nat.totient (a * (hchoice n₁ hn₁).choose_spec.choose) := by
      simp only [f, hn₁, ↓reduceDIte]
    have hf2 : f n₂ = Nat.totient (a * (hchoice n₂ hn₂).choose_spec.choose) := by
      simp only [f, hn₂, ↓reduceDIte]
    rw [hf1, hf2] at heq
    set t₁ := (hchoice n₁ hn₁).choose
    set r₁ := (hchoice n₁ hn₁).choose_spec.choose
    have hspec₁ := (hchoice n₁ hn₁).choose_spec.choose_spec
    set t₂ := (hchoice n₂ hn₂).choose
    set r₂ := (hchoice n₂ hn₂).choose_spec.choose
    have hspec₂ := (hchoice n₂ hn₂).choose_spec.choose_spec
    have ha_pos : 0 < a := by omega
    have hrel₁ : n₁ = a ^ (t₁ - 1) * Nat.totient (a * r₁) := by
      rw [← hspec₁.2.2.2, totient_pow_mul_eq ha_pos (by omega) hspec₁.2.1]
    have hrel₂ : n₂ = a ^ (t₂ - 1) * Nat.totient (a * r₂) := by
      rw [← hspec₂.2.2.2, totient_pow_mul_eq ha_pos (by omega) hspec₂.2.1]
    have hn₁_hi : X / a < n₁ := (Finset.mem_filter.mp hn₁).2
    have hn₂_hi : X / a < n₂ := (Finset.mem_filter.mp hn₂).2
    have hn₁_le : n₁ ≤ X := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hn₁).1).1).2
    have hn₂_le : n₂ ≤ X := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hn₂).1).1).2
    have hno_lt : ∀ u v k₁ k₂ : ℕ, X / a < u → v ≤ X →
        u = a ^ k₁ * Nat.totient (a * r₁) → v = a ^ k₂ * Nat.totient (a * r₁) →
        ¬ (k₁ < k₂) := by
      intro u v k₁ k₂ hu hv hu_eq hv_eq hlt
      have hmul : v = a ^ (k₂ - k₁) * u := by
        rw [hu_eq, hv_eq, ← mul_assoc, ← pow_add, Nat.sub_add_cancel (le_of_lt hlt)]
      have ha_le : a ≤ a ^ (k₂ - k₁) := by
        have : a ^ 1 ≤ a ^ (k₂ - k₁) := Nat.pow_le_pow_right ha_pos (by omega)
        simpa using this
      have hgt : X < a * u := by
        have h1 : X / a + 1 ≤ u := hu
        have h2 : a * (X / a + 1) ≤ a * u := Nat.mul_le_mul_left a h1
        have h3 : a * (X / a + 1) = a * (X / a) + a := by ring
        have hdiv : a * (X / a) + X % a = X := Nat.div_add_mod X a
        have hmod : X % a < a := Nat.mod_lt X ha_pos
        omega
      have hv_ge : a * u ≤ v := by
        rw [hmul]; exact Nat.mul_le_mul_right u ha_le
      omega
    have hnot1 : ¬ (t₁ - 1 < t₂ - 1) :=
      hno_lt n₁ n₂ (t₁ - 1) (t₂ - 1) hn₁_hi hn₂_le hrel₁ (heq ▸ hrel₂)
    have hnot2 : ¬ (t₂ - 1 < t₁ - 1) :=
      hno_lt n₂ n₁ (t₂ - 1) (t₁ - 1) hn₂_hi hn₁_le (heq ▸ hrel₂) hrel₁
    have ht_eq : t₁ - 1 = t₂ - 1 := by omega
    rw [hrel₁, hrel₂, ht_eq, heq]
  exact Finset.card_le_card_of_injOn f hf_maps hf_inj

/-- Monotonicity of `V`. -/
theorem V_mono : Monotone V := by
  intro X Y hXY
  classical
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.Icc_subset_Icc_right hXY))

/-- Every prime `p ≤ X + 1` produces a distinct totient value `p - 1 ∈ [1, X]`, so
`Nat.primeCounting (X + 1) ≤ V X`. -/
theorem primeCounting_le_V (X : ℕ) : Nat.primeCounting (X + 1) ≤ V X := by
  classical
  rw [← Nat.primesLE_card_eq_primeCounting]
  unfold V
  refine Finset.card_le_card_of_injOn (fun p => p - 1) ?_ ?_
  · intro p hp
    rw [Finset.mem_coe] at hp ⊢
    rw [Finset.mem_filter, Finset.mem_Icc]
    have hp_prime : Nat.Prime p := (Nat.mem_primesBelow.mp hp).2
    have hp_lt : p < X + 2 := (Nat.mem_primesBelow.mp hp).1
    have hp2 : 2 ≤ p := hp_prime.two_le
    dsimp only
    exact ⟨⟨by omega, by omega⟩, ⟨p, hp_prime.pos, Nat.totient_prime hp_prime⟩⟩
  · intro p hp q hq heq
    rw [Finset.mem_coe] at hp hq
    have hp2 : 2 ≤ p := (Nat.mem_primesBelow.mp hp).2.two_le
    have hq2 : 2 ≤ q := (Nat.mem_primesBelow.mp hq).2.two_le
    dsimp only at heq
    omega

/-- `V X ≥ 1` for every `X ≥ 1` (witnessed by `φ(1) = 1`). -/
theorem V_pos {X : ℕ} (hX : 1 ≤ X) : 0 < V X := by
  classical
  unfold V
  refine Finset.card_pos.mpr ⟨1, ?_⟩
  simp only [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨le_rfl, hX⟩, ⟨1, by decide, Nat.totient_one⟩⟩

/-- Splitting singleton totients across two forced square divisors `a₁ ^ 2` and `a₂ ^ 2`:
`V1 X ≤ 2 * V (X / min a₁ a₂)`. -/
theorem V1_le_two_mul_V_div {a₁ a₂ : ℕ} (ha₁ : 2 ≤ a₁) (ha₂ : 2 ≤ a₂)
    (hcov : ∀ x : ℕ, IsCarmichaelCounterexample x → a₁ ^ 2 ∣ x ∨ a₂ ^ 2 ∣ x) (X : ℕ) :
    V1 X ≤ 2 * V (X / min a₁ a₂) := by
  classical
  set S1 := (Finset.Icc 1 X).filter
    (fun n => ∃ x : ℕ, IsCarmichaelCounterexample x ∧ Nat.totient x = n)
  set D1 := (Finset.Icc 1 X).filter
    (fun n => IsTotientValue n ∧ ∀ y : ℕ, 0 < y → Nat.totient y = n → a₁ ^ 2 ∣ y)
  set D2 := (Finset.Icc 1 X).filter
    (fun n => IsTotientValue n ∧ ∀ y : ℕ, 0 < y → Nat.totient y = n → a₂ ^ 2 ∣ y)
  have hsub : S1 ⊆ D1 ∪ D2 := by
    intro n hn
    simp only [S1, D1, D2, Finset.mem_union, Finset.mem_filter] at hn ⊢
    obtain ⟨hIcc, x, hx, hxphi⟩ := hn
    rcases hcov x hx with h1 | h2
    · refine Or.inl ⟨hIcc, ⟨x, hx.1, hxphi⟩, ?_⟩
      intro y _ hyphi
      have hyx : y = x := hx.2 y (hyphi.trans hxphi.symm)
      exact hyx ▸ h1
    · refine Or.inr ⟨hIcc, ⟨x, hx.1, hxphi⟩, ?_⟩
      intro y _ hyphi
      have hyx : y = x := hx.2 y (hyphi.trans hxphi.symm)
      exact hyx ▸ h2
  have hle_sum : V1 X ≤ VDiv X a₁ + VDiv X a₂ := by
    calc V1 X = S1.card := rfl
      _ ≤ (D1 ∪ D2).card := Finset.card_le_card hsub
      _ ≤ D1.card + D2.card := Finset.card_union_le D1 D2
      _ = VDiv X a₁ + VDiv X a₂ := rfl
  have h1 : VDiv X a₁ ≤ V (X / a₁) := ford_lemma_7_4_7_5 ha₁
  have h2 : VDiv X a₂ ≤ V (X / a₂) := ford_lemma_7_4_7_5 ha₂
  have hA1 : X / a₁ ≤ X / min a₁ a₂ :=
    Nat.div_le_div_left (min_le_left a₁ a₂) (by omega)
  have hA2 : X / a₂ ≤ X / min a₁ a₂ :=
    Nat.div_le_div_left (min_le_right a₁ a₂) (by omega)
  calc V1 X ≤ VDiv X a₁ + VDiv X a₂ := hle_sum
    _ ≤ V (X / a₁) + V (X / a₂) := Nat.add_le_add h1 h2
    _ ≤ V (X / min a₁ a₂) + V (X / min a₁ a₂) := Nat.add_le_add (V_mono hA1) (V_mono hA2)
    _ = 2 * V (X / min a₁ a₂) := by ring

/-- Elementary linear Bernoulli bound: for `δ ≥ 0` and `k : ℕ`, `1 + k * δ ≤ (1 + δ) ^ k`. -/
private theorem one_add_mul_le_pow_nonneg {δ : ℝ} (hδ : 0 ≤ δ) :
    ∀ k : ℕ, 1 + (k : ℝ) * δ ≤ (1 + δ) ^ k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    push_cast
    have h1 : (1 + (k : ℝ) * δ) * (1 + δ) ≤ (1 + δ) ^ k * (1 + δ) :=
      mul_le_mul_of_nonneg_right ih (by linarith)
    have h2 : 0 ≤ (k : ℝ) * δ ^ 2 := by positivity
    linarith

/-- Elementary quadratic binomial lower bound: for `δ ≥ 0` and `k : ℕ`,
`((k : ℝ) * ((k : ℝ) - 1) / 2) * δ ^ 2 ≤ (1 + δ) ^ k`. -/
private theorem quad_le_one_add_pow {δ : ℝ} (hδ : 0 ≤ δ) :
    ∀ k : ℕ, ((k : ℝ) * ((k : ℝ) - 1) / 2) * δ ^ 2 ≤ (1 + δ) ^ k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hlin : 1 + (k : ℝ) * δ ≤ (1 + δ) ^ k := one_add_mul_le_pow_nonneg hδ k
    have hmul : (1 + δ) ^ (k + 1) = (1 + δ) ^ k + δ * (1 + δ) ^ k := by
      rw [pow_succ]; ring
    have h1 : δ * (1 + (k : ℝ) * δ) ≤ δ * (1 + δ) ^ k :=
      mul_le_mul_of_nonneg_left hlin hδ
    push_cast
    nlinarith

/-- Helper: `V(X)` cannot satisfy `V(A ^ k * X₀) ≤ r ^ k * V(X₀)` for all `k` when
`2 ≤ A`, `2 ≤ X₀`, and `0 < r < A`. -/
private theorem not_V_iterated_le {A X₀ : ℕ} {r : ℝ}
    (hA : 2 ≤ A) (hX₀ : 2 ≤ X₀) (hr0 : 0 < r) (hrA : r < (A : ℝ))
    (hiter : ∀ k : ℕ, (V (A ^ k * X₀) : ℝ) ≤ r ^ k * (V X₀ : ℝ)) : False := by
  set q : ℝ := (A : ℝ) / r
  have hq : 1 < q := (one_lt_div hr0).mpr hrA
  set δ : ℝ := q - 1
  have hδ : 0 < δ := sub_pos.mpr hq
  have hlogA_pos : 0 < Real.log (A : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < A))
  have hlogX_pos : 0 < Real.log (X₀ : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < X₀))
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  -- Pick k ≥ 4 large enough that (k - 1) * δ^2 / 2 > (4 / log 2) * ((V X₀) * (log A + log X₀) + 2)
  set M : ℝ := (4 / Real.log 2) * (((V X₀ : ℝ) + 1) * (Real.log (A : ℝ) + Real.log (X₀ : ℝ)) + 2)
  have hM_pos : 0 < M := by positivity
  obtain ⟨k₀, hk₀⟩ := exists_nat_gt (2 * M / δ ^ 2 + 2)
  set k : ℕ := max k₀ 8
  have hk8 : 8 ≤ k := le_max_right _ _
  have hkk₀ : (k₀ : ℝ) ≤ (k : ℝ) := by exact_mod_cast le_max_left k₀ 8
  have hk_big : 2 * M / δ ^ 2 + 2 < (k : ℝ) := lt_of_lt_of_le hk₀ hkk₀
  have hq_pow : (k : ℝ) * M < q ^ k := by
    have hquad := quad_le_one_add_pow (le_of_lt hδ) k
    have hq_eq : 1 + δ = q := by ring
    rw [hq_eq] at hquad
    have hstep : M < ((k : ℝ) - 1) / 2 * δ ^ 2 := by
      have h1 : 2 * M / δ ^ 2 < (k : ℝ) - 1 := by linarith
      have h2 : 2 * M < ((k : ℝ) - 1) * δ ^ 2 := (div_lt_iff₀ (sq_pos_of_pos hδ)).mp h1
      linarith
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    have hmul : (k : ℝ) * M < (k : ℝ) * (((k : ℝ) - 1) / 2 * δ ^ 2) :=
      mul_lt_mul_of_pos_left hstep hk_pos
    linarith
  -- Evaluate at n = A ^ k * X₀ (n ≥ 512)
  set n : ℕ := A ^ k * X₀
  have hn_ge_512 : 512 ≤ n := by
    have hA8 : 256 ≤ A ^ k := by
      calc 256 = 2 ^ 8 := by decide
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk8
        _ ≤ A ^ k := Nat.pow_le_pow_left hA k
    calc 512 = 256 * 2 := by decide
      _ ≤ A ^ k * X₀ := Nat.mul_le_mul hA8 hX₀
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  -- Upper bound on log n: log (A^k * X₀) = k * log A + log X₀ ≤ k * (log A + log X₀)
  have hlogn_le : Real.log (n : ℝ) ≤ (k : ℝ) * (Real.log (A : ℝ) + Real.log (X₀ : ℝ)) := by
    have hcast : (n : ℝ) = (A : ℝ) ^ k * (X₀ : ℝ) := by push_cast [n]; rfl
    rw [hcast, Real.log_mul (pow_ne_zero k (by positivity)) (by positivity), Real.log_pow]
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
    nlinarith
  -- Lower bound on V n via Chebyshev.pi_ge:
  have hpi_le_V : (Nat.primeCounting n : ℝ) ≤ (V n : ℝ) := by
    have h1 : Nat.primeCounting n ≤ Nat.primeCounting (n + 1) :=
      Nat.monotone_primeCounting (Nat.le_succ n)
    have h2 : Nat.primeCounting (n + 1) ≤ V n := primeCounting_le_V n
    exact_mod_cast le_trans h1 h2
  have hcheb : ((n : ℝ) * Real.log 2 - Real.log ((n : ℝ) + 1)) / Real.log (n : ℝ) ≤
      (Nat.primeCounting n : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one] using Chebyshev.pi_ge n
  -- Bound log (n + 1) ≤ (n / 2) * log 2 for n ≥ 512 via 2 * √(n + 1) ≤ n / 4 < (n / 2) * log 2
  have hlog2_half : (1 / 2 : ℝ) < Real.log 2 := by
    have h := Real.log_two_gt_d9
    linarith
  have hlog_n1_le : Real.log ((n : ℝ) + 1) ≤ (n : ℝ) * (Real.log 2 / 2) := by
    have hsqrt_pos : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have hlog_sqrt : Real.log ((n : ℝ) + 1) = 2 * Real.log (Real.sqrt ((n : ℝ) + 1)) := by
      rw [Real.log_sqrt (by positivity)]; ring
    have hlog_le_sub : Real.log (Real.sqrt ((n : ℝ) + 1)) ≤ Real.sqrt ((n : ℝ) + 1) - 1 :=
      Real.log_le_sub_one_of_pos hsqrt_pos
    have hsqrt_le : 2 * Real.sqrt ((n : ℝ) + 1) ≤ (n : ℝ) / 4 := by
      have hn_real : (512 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_512
      have hsq : Real.sqrt ((n : ℝ) + 1) ≤ (n : ℝ) / 8 := by
        rw [Real.sqrt_le_left (by positivity)]
        nlinarith
      linarith
    have hn4 : (n : ℝ) / 4 ≤ (n : ℝ) * (Real.log 2 / 2) := by nlinarith
    linarith
  -- Therefore ((n * log 2) / 2) / log n ≤ V n ≤ r^k * V X₀
  have hlow : (n : ℝ) * (Real.log 2 / 2) / Real.log (n : ℝ) ≤ (V n : ℝ) := by
    have hnum : (n : ℝ) * (Real.log 2 / 2) ≤ (n : ℝ) * Real.log 2 - Real.log ((n : ℝ) + 1) := by
      linarith
    have hdiv : (n : ℝ) * (Real.log 2 / 2) / Real.log (n : ℝ) ≤
        ((n : ℝ) * Real.log 2 - Real.log ((n : ℝ) + 1)) / Real.log (n : ℝ) :=
      div_le_div_of_nonneg_right hnum (le_of_lt hlogn_pos)
    exact le_trans (le_trans hdiv hcheb) hpi_le_V
  have hup : (V n : ℝ) ≤ r ^ k * (V X₀ : ℝ) := hiter k
  have hcomb : (n : ℝ) * (Real.log 2 / 2) ≤ r ^ k * (V X₀ : ℝ) * Real.log (n : ℝ) := by
    have := (div_le_iff₀ hlogn_pos).mp (le_trans hlow hup)
    linarith
  -- Substitute n = A^k * X₀ ≥ 2 * A^k and log n ≤ k * (log A + log X₀), divide by r^k
  have hn_ge_2A : 2 * (A : ℝ) ^ k ≤ (n : ℝ) := by
    have hX2 : (2 : ℝ) ≤ (X₀ : ℝ) := by exact_mod_cast hX₀
    have hcast : (n : ℝ) = (A : ℝ) ^ k * (X₀ : ℝ) := by push_cast [n]; rfl
    rw [hcast]
    nlinarith [pow_nonneg (Nat.cast_nonneg (α := ℝ) A) k]
  have hA_le : (A : ℝ) ^ k * Real.log 2 ≤ r ^ k * ((V X₀ : ℝ) * ((k : ℝ) * (Real.log (A : ℝ) + Real.log (X₀ : ℝ)))) := by
    have h1 : (A : ℝ) ^ k * Real.log 2 ≤ (n : ℝ) * (Real.log 2 / 2) := by nlinarith
    have h2 : r ^ k * (V X₀ : ℝ) * Real.log (n : ℝ) ≤
        r ^ k * (V X₀ : ℝ) * ((k : ℝ) * (Real.log (A : ℝ) + Real.log (X₀ : ℝ))) :=
      mul_le_mul_of_nonneg_left hlogn_le (by positivity)
    linarith
  have hrk_pos : 0 < r ^ k := pow_pos hr0 k
  have hq_le : q ^ k * Real.log 2 ≤ (k : ℝ) * ((V X₀ : ℝ) * (Real.log (A : ℝ) + Real.log (X₀ : ℝ))) := by
    have hq_eq : q ^ k = (A : ℝ) ^ k / r ^ k := by rw [div_pow]
    rw [hq_eq, div_mul_eq_mul_div, div_le_iff₀ hrk_pos]
    linarith
  -- Compare with hq_pow : k * M < q ^ k
  have hM_mul : (k : ℝ) * ((V X₀ : ℝ) * (Real.log (A : ℝ) + Real.log (X₀ : ℝ))) < (k : ℝ) * M * Real.log 2 := by
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    have hM_log2 : M * Real.log 2 = 4 * (((V X₀ : ℝ) + 1) * (Real.log (A : ℝ) + Real.log (X₀ : ℝ)) + 2) := by
      simp only [M]
      field_simp [ne_of_gt hlog2_pos]
    have hlt_inner : (V X₀ : ℝ) * (Real.log (A : ℝ) + Real.log (X₀ : ℝ)) < M * Real.log 2 := by
      rw [hM_log2]
      nlinarith
    have := mul_lt_mul_of_pos_left hlt_inner hk_pos
    linarith
  have hq_mul : (k : ℝ) * M * Real.log 2 < q ^ k * Real.log 2 :=
    mul_lt_mul_of_pos_right hq_pow hlog2_pos
  linarith

/-- **Limiting Singleton Density Bound (Ford 1998, Section 7.2 / Corollary 3, Part 2):**
If every Carmichael counterexample `x` satisfies `a₁ ^ 2 ∣ x ∨ a₂ ^ 2 ∣ x` with `2 ≤ a₁, a₂`,
then for every `c > 2 / min a₁ a₂` there are arbitrarily large `X` with `V1 X / V X < c`,
and hence `Filter.liminf (fun X : ℕ => (V1 X : ℝ) / (V X : ℝ)) Filter.atTop ≤ 2 / min a₁ a₂`. -/
theorem frequently_V1_div_V_lt {a₁ a₂ : ℕ} (ha₁ : 2 ≤ a₁) (ha₂ : 2 ≤ a₂)
    (hcov : ∀ x : ℕ, IsCarmichaelCounterexample x → a₁ ^ 2 ∣ x ∨ a₂ ^ 2 ∣ x)
    {c : ℝ} (hc : (2 : ℝ) / (min a₁ a₂ : ℕ) < c) :
    ∃ᶠ X : ℕ in atTop, (V1 X : ℝ) / (V X : ℝ) < c := by
  rw [Filter.frequently_atTop]
  intro N
  by_contra hno
  push Not at hno
  set A : ℕ := min a₁ a₂
  have hA : 2 ≤ A := le_min ha₁ ha₂
  have hA_pos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast (by omega : 0 < A)
  have hc_pos : 0 < c := lt_trans (by positivity) hc
  set r : ℝ := 2 / c
  have hr0 : 0 < r := by positivity
  have hrA : r < (A : ℝ) := by
    rw [div_lt_iff₀ hc_pos]
    have h1 := (div_lt_iff₀ hA_pos).mp hc
    linarith
  set X₀ : ℕ := max N 2
  have hX₀ : 2 ≤ X₀ := le_max_right N 2
  have hiter : ∀ k : ℕ, (V (A ^ k * X₀) : ℝ) ≤ r ^ k * (V X₀ : ℝ) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      set X : ℕ := A ^ (k + 1) * X₀
      have hX_ge_N : N ≤ X := by
        have h1 : 1 ≤ A ^ (k + 1) := Nat.one_le_pow _ _ (by omega)
        calc N ≤ X₀ := le_max_left N 2
          _ = 1 * X₀ := (one_mul _).symm
          _ ≤ A ^ (k + 1) * X₀ := Nat.mul_le_mul_right X₀ h1
      have hX_pos : 1 ≤ X := by
        have : 2 ≤ X := le_trans hX₀ (by
          calc X₀ = 1 * X₀ := (one_mul _).symm
            _ ≤ A ^ (k + 1) * X₀ := Nat.mul_le_mul_right X₀ (Nat.one_le_pow _ _ (by omega)))
        omega
      have hV_pos : (0 : ℝ) < (V X : ℝ) := Nat.cast_pos.mpr (V_pos hX_pos)
      have hge : c ≤ (V1 X : ℝ) / (V X : ℝ) := hno X hX_ge_N
      have hmul_c : c * (V X : ℝ) ≤ (V1 X : ℝ) := (le_div_iff₀ hV_pos).mp hge
      have hV1_le : (V1 X : ℝ) ≤ 2 * (V (X / A) : ℝ) := by
        exact_mod_cast V1_le_two_mul_V_div ha₁ ha₂ hcov X
      have hdiv_eq : X / A = A ^ k * X₀ := by
        have hX_eq : X = A * (A ^ k * X₀) := by simp only [X, pow_succ']; ring
        rw [hX_eq, Nat.mul_div_right _ (by omega : 0 < A)]
      rw [hdiv_eq] at hV1_le
      have hstep : (V X : ℝ) ≤ r * (V (A ^ k * X₀) : ℝ) := by
        have : c * (V X : ℝ) ≤ 2 * (V (A ^ k * X₀) : ℝ) := le_trans hmul_c hV1_le
        rw [show r = 2 / c from rfl, div_mul_eq_mul_div, le_div_iff₀ hc_pos]
        linarith
      calc (V X : ℝ) ≤ r * (V (A ^ k * X₀) : ℝ) := hstep
        _ ≤ r * (r ^ k * (V X₀ : ℝ)) := mul_le_mul_of_nonneg_left ih (le_of_lt hr0)
        _ = r ^ (k + 1) * (V X₀ : ℝ) := by rw [pow_succ']; ring
  exact not_V_iterated_le hA hX₀ hr0 hrA hiter

/-- **`Filter.liminf` form of Ford's Singleton Density Bound:**
`Filter.liminf (fun X => (V1 X : ℝ) / (V X : ℝ)) Filter.atTop ≤ 2 / min a₁ a₂`. -/
theorem liminf_V1_div_V_le_two_div_min {a₁ a₂ : ℕ} (ha₁ : 2 ≤ a₁) (ha₂ : 2 ≤ a₂)
    (hcov : ∀ x : ℕ, IsCarmichaelCounterexample x → a₁ ^ 2 ∣ x ∨ a₂ ^ 2 ∣ x) :
    Filter.liminf (fun X : ℕ => ((V1 X : ℝ) / (V X : ℝ))) Filter.atTop ≤
      (2 : ℝ) / (min a₁ a₂ : ℕ) := by
  have hbdd : Filter.IsBoundedUnder (· ≥ ·) atTop (fun X : ℕ => ((V1 X : ℝ) / (V X : ℝ))) :=
    ⟨0, Filter.eventually_map.mpr (Filter.Eventually.of_forall fun X => by positivity)⟩
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hfreq := frequently_V1_div_V_lt ha₁ ha₂ hcov
    (c := (2 : ℝ) / (min a₁ a₂ : ℕ) + ε) (by linarith)
  exact Filter.liminf_le_of_frequently_le (hfreq.mono fun X hX => le_of_lt hX) hbdd

/-! ## Part 3: Combined Corollary 3 Bridge and Unconditional Pure-Kernel Instantiation -/

/-- Every prime in `ForcedCase1` is prime and at least `5`. -/
theorem forcedCase1_prime_ge_five {p : ℕ} (hp : ForcedCase1 p) : Nat.Prime p ∧ 5 ≤ p := by
  induction hp with
  | step6 _ hprime ih =>
    have hk_pos : 1 ≤ ∏ q ∈ _, q := Finset.one_le_prod fun q hq => by have := (ih q hq).2; omega
    exact ⟨hprime, by omega⟩
  | step12 _ hprime ih =>
    have hk_pos : 1 ≤ ∏ q ∈ _, q := Finset.one_le_prod fun q hq => by have := (ih q hq).2; omega
    exact ⟨hprime, by omega⟩

/-- Every prime in `ForcedCase2` is prime and at least `5`. -/
theorem forcedCase2_prime_ge_five {p : ℕ} (hp : ForcedCase2 p) : Nat.Prime p ∧ 5 ≤ p := by
  induction hp with
  | step6 _ hprime ih =>
    have hk_pos : 1 ≤ ∏ q ∈ _, q := Finset.one_le_prod fun q hq => by have := (ih q hq).2; omega
    exact ⟨hprime, by omega⟩
  | step18 _ hprime ih =>
    have hk_pos : 1 ≤ ∏ q ∈ _, q := Finset.one_le_prod fun q hq => by have := (ih q hq).2; omega
    exact ⟨hprime, by omega⟩

/-- **Combined Corollary 3 (Totient Value and Density Transfer):**
Given Case I and Case II forced prime sets `S₁, S₂` (`p ≥ 5` prime) such that:
- `d₁ = 36 * ∏ p ∈ S₁, p ^ 2 > 6 * 10 ^ (2 * H)` with `∑ p ∈ S₁, (1/p : ℝ) < 1/2`,
- `d₂ = 108 * ∏ p ∈ S₂, p ^ 2 > 12 * 10 ^ (2 * H)` with `∑ p ∈ S₂, (1/p : ℝ) < 1/2`,
every singleton totient value `m = φ(x)` satisfies `10 ^ (2 * H) < m`, and
`Filter.liminf (fun X => (V1 X : ℝ) / (V X : ℝ)) Filter.atTop < 1 / 10 ^ H`. -/
theorem corollary_value_and_density_transfer
    {H : ℕ} {S₁ S₂ : Finset ℕ}
    (hS₁ : ∀ p ∈ S₁, ForcedCase1 p)
    (hS₂ : ∀ p ∈ S₂, ForcedCase2 p)
    (hbig₁ : 6 * 10 ^ (2 * H) < 36 * ∏ p ∈ S₁, p ^ 2)
    (hbig₂ : 12 * 10 ^ (2 * H) < 108 * ∏ p ∈ S₂, p ^ 2)
    (hrec₁ : ∑ p ∈ S₁, (1 : ℝ) / (p : ℝ) < 1 / 2)
    (hrec₂ : ∑ p ∈ S₂, (1 : ℝ) / (p : ℝ) < 1 / 2) :
    (∀ x : ℕ, IsCarmichaelCounterexample x → 10 ^ (2 * H) < Nat.totient x) ∧
    Filter.liminf (fun X : ℕ => ((V1 X : ℝ) / (V X : ℝ))) Filter.atTop <
      1 / (10 : ℝ) ^ H := by
  have hS₁_prime : ∀ p ∈ S₁, Nat.Prime p ∧ 5 ≤ p := fun p hp => forcedCase1_prime_ge_five (hS₁ p hp)
  have hS₂_prime : ∀ p ∈ S₂, Nat.Prime p ∧ 5 ≤ p := fun p hp => forcedCase2_prime_ge_five (hS₂ p hp)
  constructor
  · intro x hx
    rcases carmichael_case_split hx with ⟨_, h27, _⟩ | h27
    · have hS₁x : ∀ p ∈ S₁, Nat.Prime p ∧ 5 ≤ p ∧ p ^ 2 ∣ x := fun p hp =>
        forcedCase1_sound hx h27 (hS₁ p hp)
      have hdvd : 36 * ∏ p ∈ S₁, p ^ 2 ∣ x := by
        simpa [show 4 * 9 = 36 by decide] using base_mul_prod_sq_dvd_case1 hx S₁ hS₁x
      exact totient_value_gt_of_forced_primes hx.1 (Or.inl rfl) hS₁_prime hdvd
        (le_of_lt hbig₁) hrec₁
    · have hS₂x : ∀ p ∈ S₂, Nat.Prime p ∧ 5 ≤ p ∧ p ^ 2 ∣ x := fun p hp =>
        forcedCase2_sound hx h27 (hS₂ p hp)
      have hdvd : 108 * ∏ p ∈ S₂, p ^ 2 ∣ x := by
        simpa [show 4 * 27 = 108 by decide] using base_mul_prod_sq_dvd_case2 hx h27 S₂ hS₂x
      exact totient_value_gt_of_forced_primes hx.1 (Or.inr rfl) hS₂_prime hdvd
        (by omega) hrec₂
  · set a₁ : ℕ := 6 * ∏ p ∈ S₁, p
    set a₂ : ℕ := 6 * ∏ p ∈ S₂, p
    have ha₁_sq : a₁ ^ 2 = 36 * ∏ p ∈ S₁, p ^ 2 := by
      simp only [a₁, mul_pow, Finset.prod_pow]; ring
    have ha₂_sq : 3 * a₂ ^ 2 = 108 * ∏ p ∈ S₂, p ^ 2 := by
      simp only [a₂, mul_pow, Finset.prod_pow]; ring
    have ha₁_gt : 2 * 10 ^ H < a₁ := by
      have h4 : (2 * 10 ^ H) ^ 2 = 4 * 10 ^ (2 * H) := by
        rw [mul_pow, ← pow_mul, mul_comm H 2]; ring
      have hsq : (2 * 10 ^ H) ^ 2 < a₁ ^ 2 := by
        rw [h4, ha₁_sq]
        exact lt_of_le_of_lt (Nat.mul_le_mul_right _ (by decide : 4 ≤ 6)) hbig₁
      by_contra hle
      push Not at hle
      exact not_lt_of_ge (Nat.pow_le_pow_left hle 2) hsq
    have ha₂_gt : 2 * 10 ^ H < a₂ := by
      have h12 : 3 * (2 * 10 ^ H) ^ 2 = 12 * 10 ^ (2 * H) := by
        rw [mul_pow, ← pow_mul, mul_comm H 2]; ring
      have hsq : 3 * (2 * 10 ^ H) ^ 2 < 3 * a₂ ^ 2 := by
        rw [h12, ha₂_sq]; exact hbig₂
      by_contra hle
      push Not at hle
      exact not_lt_of_ge (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left hle 2)) hsq
    have ha₁_ge2 : 2 ≤ a₁ := by
      have : 1 ≤ 10 ^ H := Nat.one_le_pow _ _ (by decide)
      omega
    have ha₂_ge2 : 2 ≤ a₂ := by
      have : 1 ≤ 10 ^ H := Nat.one_le_pow _ _ (by decide)
      omega
    have hcov : ∀ x : ℕ, IsCarmichaelCounterexample x → a₁ ^ 2 ∣ x ∨ a₂ ^ 2 ∣ x := by
      intro x hx
      rcases carmichael_case_split hx with ⟨_, h27, _⟩ | h27
      · left
        rw [ha₁_sq]
        have hS₁x : ∀ p ∈ S₁, Nat.Prime p ∧ 5 ≤ p ∧ p ^ 2 ∣ x := fun p hp =>
          forcedCase1_sound hx h27 (hS₁ p hp)
        simpa [show 4 * 9 = 36 by decide] using base_mul_prod_sq_dvd_case1 hx S₁ hS₁x
      · right
        have hS₂x : ∀ p ∈ S₂, Nat.Prime p ∧ 5 ≤ p ∧ p ^ 2 ∣ x := fun p hp =>
          forcedCase2_sound hx h27 (hS₂ p hp)
        have hdvd : 3 * a₂ ^ 2 ∣ x := by
          rw [ha₂_sq]
          simpa [show 4 * 27 = 108 by decide] using base_mul_prod_sq_dvd_case2 hx h27 S₂ hS₂x
        exact dvd_of_mul_left_dvd hdvd
    have hlim := liminf_V1_div_V_le_two_div_min ha₁_ge2 ha₂_ge2 hcov
    have hmin_gt : 2 * 10 ^ H < min a₁ a₂ := lt_min ha₁_gt ha₂_gt
    have hmin_real : (2 : ℝ) * (10 : ℝ) ^ H < (min a₁ a₂ : ℕ) := by exact_mod_cast hmin_gt
    have hdiv_lt : (2 : ℝ) / (min a₁ a₂ : ℕ) < 1 / (10 : ℝ) ^ H := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      linarith
    exact lt_of_le_of_lt hlim hdiv_lt

private theorem ten_pow_le_ten_pow {m n : ℕ} (h : m ≤ n) : (10 : ℕ) ^ m ≤ (10 : ℕ) ^ n :=
  Nat.pow_le_pow_right (by decide : 0 < 10) h

private theorem lt_of_sq_lt_sq {u v : ℕ} (h : u ^ 2 < v ^ 2) : u < v := by
  by_contra hle
  push Not at hle
  exact not_lt_of_ge (Nat.pow_le_pow_left hle 2) h

private theorem lt_of_three_mul_sq_lt {u v : ℕ} (h : 3 * u ^ 2 < 3 * v ^ 2) : u < v := by
  by_contra hle
  push Not at hle
  exact not_lt_of_ge (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left hle 2)) h

private theorem density_bound_of_square_bounds {H D1 D2 a₁ a₂ : ℕ}
    (hH1 : 2 * H + 1 ≤ D1) (hH2 : 2 * H + 3 ≤ D2)
    (hd1 : 10 ^ D1 < a₁ ^ 2) (hd2 : 10 ^ D2 < 3 * a₂ ^ 2)
    (hcov : ∀ x : ℕ, IsCarmichaelCounterexample x → a₁ ^ 2 ∣ x ∨ a₂ ^ 2 ∣ x) :
    Filter.liminf (fun X : ℕ => ((V1 X : ℝ) / (V X : ℝ))) Filter.atTop <
      1 / (10 : ℝ) ^ H := by
  have h10pos : 0 < (10 : ℕ) ^ H := Nat.pow_pos (by decide : 0 < 10)
  have ha₁_gt : 2 * 10 ^ H < a₁ := by
    have h4 : (2 * 10 ^ H) ^ 2 = 4 * 10 ^ (2 * H) := by
      rw [mul_pow, ← pow_mul, mul_comm H 2]; ring
    have hle : 4 * 10 ^ (2 * H) ≤ 10 ^ D1 := by
      calc 4 * 10 ^ (2 * H) ≤ 10 * 10 ^ (2 * H) := Nat.mul_le_mul_right _ (by decide : 4 ≤ 10)
        _ = 10 ^ (2 * H + 1) := by rw [pow_succ, mul_comm]
        _ ≤ 10 ^ D1 := ten_pow_le_ten_pow hH1
    exact lt_of_sq_lt_sq (h4.symm ▸ lt_of_le_of_lt hle hd1)
  have ha₂_gt : 2 * 10 ^ H < a₂ := by
    have h12 : 3 * (2 * 10 ^ H) ^ 2 = 12 * 10 ^ (2 * H) := by
      rw [mul_pow, ← pow_mul, mul_comm H 2]; ring
    have hle : 12 * 10 ^ (2 * H) ≤ 10 ^ D2 := by
      calc 12 * 10 ^ (2 * H) ≤ 10 ^ 3 * 10 ^ (2 * H) :=
            Nat.mul_le_mul_right _ (by decide : 12 ≤ 10 ^ 3)
        _ = 10 ^ (2 * H + 3) := by rw [pow_add, mul_comm]
        _ ≤ 10 ^ D2 := ten_pow_le_ten_pow hH2
    exact lt_of_three_mul_sq_lt (h12.symm ▸ lt_of_le_of_lt hle hd2)
  have ha₁_ge2 : 2 ≤ a₁ := le_trans (Nat.le_mul_of_pos_right 2 h10pos) (le_of_lt ha₁_gt)
  have ha₂_ge2 : 2 ≤ a₂ := le_trans (Nat.le_mul_of_pos_right 2 h10pos) (le_of_lt ha₂_gt)
  have hlim := liminf_V1_div_V_le_two_div_min ha₁_ge2 ha₂_ge2 hcov
  have hmin_gt : 2 * 10 ^ H < min a₁ a₂ := lt_min ha₁_gt ha₂_gt
  have hmin_real : (2 : ℝ) * (10 : ℝ) ^ H < (min a₁ a₂ : ℕ) := by exact_mod_cast hmin_gt
  have hdiv_lt : (2 : ℝ) / (min a₁ a₂ : ℕ) < 1 / (10 : ℝ) ^ H := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    linarith
  exact lt_of_le_of_lt hlim hdiv_lt

/-- **Unconditional Pure-Kernel Limiting Density Bound:**
Combining `masaiValetteCase1Cert` (`10,240` digits) and `masaiValetteCase2Cert` (`10,117` digits)
with Ford's Lemmas 7.4–7.5 yields
`Filter.liminf (fun X => (V1 X : ℝ) / (V X : ℝ)) Filter.atTop < 1 / 10 ^ 5057`
purely inside the Lean 4 kernel (zero external certificates, zero `native_decide`). -/
theorem carmichael_liminf_density_lt_10_pow_neg_5057 :
    Filter.liminf (fun X : ℕ => ((V1 X : ℝ) / (V X : ℝ))) Filter.atTop <
      1 / (10 : ℝ) ^ 5057 := by
  rcases exists_masaiValetteCase1Cert with ⟨c1, hc1⟩
  rcases exists_masaiValetteCase2Cert with ⟨c2, hc2⟩
  set S₁ := c1.chunks.biUnion c1.chunkPrimes
  set S₂ := c2.chunks.biUnion c2.chunkPrimes
  set a₁ : ℕ := 6 * ∏ p ∈ S₁, p
  set a₂ : ℕ := 6 * ∏ p ∈ S₂, p
  have ha₁_sq : a₁ ^ 2 = (4 * 9) * ∏ c ∈ c1.chunks, (∏ p ∈ c1.chunkPrimes c, p) ^ 2 := by
    rw [prod_chunk_sq_eq_biUnion c1.chunks c1.chunkPrimes c1.pairwiseDisjoint]
    simp only [a₁, S₁, mul_pow, Finset.prod_pow]; ring
  have ha₂_sq : 3 * a₂ ^ 2 = (4 * 27) * ∏ c ∈ c2.chunks, (∏ p ∈ c2.chunkPrimes c, p) ^ 2 := by
    rw [prod_chunk_sq_eq_biUnion c2.chunks c2.chunkPrimes c2.pairwiseDisjoint]
    simp only [a₂, S₂, mul_pow, Finset.prod_pow]; ring
  have h10_lt_d1 : 10 ^ 10240 < a₁ ^ 2 := by
    have hD1 : 0 < c1.digits := lt_of_lt_of_le (by decide : 0 < 10240) hc1
    have hpos1 : 0 < a₁ ^ 2 := by
      rw [ha₁_sq]
      refine mul_pos (by decide) (Finset.prod_pos fun c hc => pow_pos (Finset.prod_pos fun p hp => ?_) 2)
      exact (forcedCase1_prime_ge_five (c1.allForced c hc p hp)).1.pos
    have hgt := digit_bound_strict_of_bit_sum hpos1 (ha₁_sq.symm ▸ dvd_rfl)
      c1.hb0 c1.hbc c1.hq10 c1.hlog hD1
    exact lt_of_le_of_lt (ten_pow_le_ten_pow hc1) hgt
  have h10_lt_d2 : 10 ^ 10117 < 3 * a₂ ^ 2 := by
    have hD2 : 0 < c2.digits := lt_of_lt_of_le (by decide : 0 < 10117) hc2
    have hpos2 : 0 < 3 * a₂ ^ 2 := by
      rw [ha₂_sq]
      refine mul_pos (by decide) (Finset.prod_pos fun c hc => pow_pos (Finset.prod_pos fun p hp => ?_) 2)
      exact (forcedCase2_prime_ge_five (c2.allForced c hc p hp)).1.pos
    have hgt := digit_bound_strict_of_bit_sum hpos2 (ha₂_sq.symm ▸ dvd_rfl)
      c2.hb0 c2.hbc c2.hq10 c2.hlog hD2
    exact lt_of_le_of_lt (ten_pow_le_ten_pow hc2) hgt
  have hcov : ∀ x : ℕ, IsCarmichaelCounterexample x → a₁ ^ 2 ∣ x ∨ a₂ ^ 2 ∣ x := by
    intro x hx
    rcases carmichael_case_split hx with ⟨_, h27, _⟩ | h27
    · left
      rw [ha₁_sq, prod_chunk_sq_eq_biUnion c1.chunks c1.chunkPrimes c1.pairwiseDisjoint]
      refine base_mul_prod_sq_dvd_case1 hx _ fun p hp => ?_
      rcases Finset.mem_biUnion.mp hp with ⟨c, hc, hpc⟩
      exact forcedCase1_sound hx h27 (c1.allForced c hc p hpc)
    · right
      have hdvd : 3 * a₂ ^ 2 ∣ x := by
        rw [ha₂_sq, prod_chunk_sq_eq_biUnion c2.chunks c2.chunkPrimes c2.pairwiseDisjoint]
        refine base_mul_prod_sq_dvd_case2 hx h27 _ fun p hp => ?_
        rcases Finset.mem_biUnion.mp hp with ⟨c, hc, hpc⟩
        exact forcedCase2_sound hx h27 (c2.allForced c hc p hpc)
      exact dvd_of_mul_left_dvd hdvd
  exact density_bound_of_square_bounds (by decide : 2 * 5057 + 1 ≤ 10240)
    (by decide : 2 * 5057 + 3 ≤ 10117) h10_lt_d1 h10_lt_d2 hcov

end CarmichaelTotient
