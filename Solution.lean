module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Nat.Factorization.Basic
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

end CarmichaelChallenge
