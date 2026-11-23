module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Order.LiminfLimsup
public import CarmichaelTotient

/-!
# Palomar Solution: Carmichael's Totient Conjecture (`10^10,117 < x`), Structural Theory, and Ford's `k = 10` Lower Bound
-/

@[expose] public section

namespace CarmichaelChallenge

def IsCarmichaelCounterexample (x : ℕ) : Prop :=
  0 < x ∧ ∀ y : ℕ, Nat.totient y = Nat.totient x → y = x

def IsMinimalCounterexample (x : ℕ) : Prop :=
  IsCarmichaelCounterexample x ∧ ∀ y : ℕ, y < x → ¬ IsCarmichaelCounterexample y

def rad (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, p

def IsDivisibleTotientWitness (k m : ℕ) : Prop :=
  (∃ x : ℕ, 0 < x ∧ Nat.totient x = m) ∧
    ∀ y : ℕ, 0 < y → Nat.totient y = m → k ∣ y

theorem carmichael_case1_gt_10_pow_10240 {x : ℕ}
    (hx : IsCarmichaelCounterexample x) (h27 : ¬ 27 ∣ x) :
    10 ^ 10240 < x :=
  CarmichaelTotient.carmichael_case1_gt_10_pow_10240 hx h27

theorem carmichael_case2_gt_10_pow_10117 {x : ℕ}
    (hx : IsCarmichaelCounterexample x) (h27 : 27 ∣ x) :
    10 ^ 10117 < x :=
  CarmichaelTotient.carmichael_case2_gt_10_pow_10117 hx h27

theorem carmichael_counterexample_gt_10_pow_10117 {x : ℕ}
    (hx : IsCarmichaelCounterexample x) :
    10 ^ 10117 < x :=
  CarmichaelTotient.carmichael_counterexample_gt_10_pow_10117 hx

theorem ford_lemma_7_2 {x d e : ℕ}
    (hx : IsCarmichaelCounterexample x)
    (hd : d ∣ x)
    (hcop : Nat.Coprime d (x / d))
    (hrad : rad (Nat.totient d) ∣ x)
    (he : e ∣ (x / d) / rad (x / d))
    (hP : Nat.Prime (1 + e * Nat.totient d)) :
    (1 + e * Nat.totient d) ^ 2 ∣ x :=
  CarmichaelTotient.ford_lemma_7_2 hx hd hcop hrad he hP

theorem minimal_counterexample_structure {x₀ : ℕ} (hx₀ : IsMinimalCounterexample x₀) :
    4 ∣ x₀ ∧ ¬ (8 ∣ x₀) ∧ ¬ (5 ∣ x₀) ∧ ¬ (17 ∣ x₀) ∧ ¬ (257 ∣ x₀) ∧ ¬ (65537 ∣ x₀) :=
  CarmichaelTotient.minimal_counterexample_structure hx₀

theorem pomerance_sufficient_condition {x : ℕ} (hx : 0 < x)
    (hpom : ∀ p : ℕ, Nat.Prime p → (p - 1) ∣ Nat.totient x → p ^ 2 ∣ x) :
    IsCarmichaelCounterexample x :=
  CarmichaelTotient.pomerance_sufficient_condition hx hpom

theorem no_k6_witness_implies_carmichael
    (h6 : ¬ ∃ m : ℕ, IsDivisibleTotientWitness 6 m) :
    ∀ x : ℕ, ¬ IsCarmichaelCounterexample x :=
  CarmichaelTotient.no_k6_witness_implies_carmichael h6

theorem k10_witness_ge_32000 {m : ℕ} (hm : IsDivisibleTotientWitness 10 m) :
    32000 ≤ m :=
  CarmichaelTotient.k10_witness_ge_32000 hm

theorem totient_eq_ten_iff (y : ℕ) : Nat.totient y = 10 ↔ y = 11 ∨ y = 22 :=
  CarmichaelTotient.totient_eq_ten_iff y

theorem k11_witness_110 : IsDivisibleTotientWitness 11 110 :=
  CarmichaelTotient.k11_witness_110

def IsTotientValue (n : ℕ) : Prop :=
  ∃ y : ℕ, 0 < y ∧ Nat.totient y = n

noncomputable def V (X : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 X).filter (fun n => IsTotientValue n)).card

noncomputable def V1 (X : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 X).filter
    (fun n => ∃ x : ℕ, IsCarmichaelCounterexample x ∧ Nat.totient x = n)).card

noncomputable def VDiv (X a : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 X).filter
    (fun n => IsTotientValue n ∧ ∀ y : ℕ, 0 < y → Nat.totient y = n → a ^ 2 ∣ y)).card

theorem totient_value_gt_of_forced_primes
    {D b x : ℕ} {S : Finset ℕ}
    (hx : 0 < x)
    (hb : b = 36 ∨ b = 108)
    (hS : ∀ p ∈ S, Nat.Prime p ∧ 5 ≤ p)
    (hdvd : b * ∏ p ∈ S, p ^ 2 ∣ x)
    (hbig : 6 * 10 ^ D ≤ b * ∏ p ∈ S, p ^ 2)
    (hrec : ∑ p ∈ S, (1 : ℝ) / (p : ℝ) < 1 / 2) :
    10 ^ D < Nat.totient x :=
  CarmichaelTotient.totient_value_gt_of_forced_primes hx hb hS hdvd hbig hrec

theorem ford_lemma_7_4_7_5 {X a : ℕ} (ha : 2 ≤ a) :
    VDiv X a ≤ V (X / a) :=
  CarmichaelTotient.ford_lemma_7_4_7_5 ha

theorem liminf_V1_div_V_le_two_div_min {a₁ a₂ : ℕ} (ha₁ : 2 ≤ a₁) (ha₂ : 2 ≤ a₂)
    (hcov : ∀ x : ℕ, IsCarmichaelCounterexample x → a₁ ^ 2 ∣ x ∨ a₂ ^ 2 ∣ x) :
    Filter.liminf (fun X : ℕ => ((V1 X : ℝ) / (V X : ℝ))) Filter.atTop ≤
      (2 : ℝ) / (min a₁ a₂ : ℕ) :=
  CarmichaelTotient.liminf_V1_div_V_le_two_div_min ha₁ ha₂ hcov

theorem carmichael_liminf_density_lt_10_pow_neg_5057 :
    Filter.liminf (fun X : ℕ => ((V1 X : ℝ) / (V X : ℝ))) Filter.atTop <
      1 / (10 : ℝ) ^ 5057 :=
  CarmichaelTotient.carmichael_liminf_density_lt_10_pow_neg_5057

end CarmichaelChallenge
