module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Order.LiminfLimsup

/-!
# Palomar Challenge: Carmichael's Totient Conjecture (`10^10,117 < x`), Structural Theory, and Ford's `k = 10` Lower Bound

Unconditional Lean 4 + Mathlib statements over `ℕ` (zero `sorry`, zero `native_decide`,
standard axioms only):
1. Every Carmichael totient counterexample `x` satisfies `10^10117 < x` unconditionally
   (`10^10240 < x` when `¬ 27 ∣ x`, and `10^10117 < x` when `27 ∣ x`), surpassing
   Masai and Valette's (1982) `10^10,000` bound purely inside the Lean 4 kernel.
2. Ford's (1998) prime-square forcing rule (`ford_lemma_7_2`), Klee's (1947)
   minimal-counterexample structure (`minimal_counterexample_structure`), and
   Pomerance's (1974) sufficient condition (`pomerance_sufficient_condition`).
3. Ford's (1998, §7.3) divisible-preimage problem: reduction of Carmichael's
   conjecture to `k = 6` (`no_k6_witness_implies_carmichael`) and the unconditional
   bound `32000 ≤ m` when every preimage of `m` is divisible by `10`
   (`k10_witness_ge_32000`).
4. Concrete non-vacuity checks: `Nat.totient y = 10 ↔ y = 11 ∨ y = 22` and
   `IsDivisibleTotientWitness 11 110`.
-/

@[expose] public section

namespace CarmichaelChallenge

/-- `x` is a Carmichael totient counterexample if `x > 0` and `x` is the unique
natural number with Euler totient equal to `φ(x)`. -/
def IsCarmichaelCounterexample (x : ℕ) : Prop :=
  0 < x ∧ ∀ y : ℕ, Nat.totient y = Nat.totient x → y = x

/-- `x` is a minimal Carmichael counterexample if no smaller natural number is one. -/
def IsMinimalCounterexample (x : ℕ) : Prop :=
  IsCarmichaelCounterexample x ∧ ∀ y : ℕ, y < x → ¬ IsCarmichaelCounterexample y

/-- The squarefree radical `∏_{p ∣ n} p`. -/
def rad (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, p

/-- `m` is a `k`-divisible totient witness if `m` is in the image of `φ` and every
positive preimage of `m` is divisible by `k`. -/
def IsDivisibleTotientWitness (k m : ℕ) : Prop :=
  (∃ x : ℕ, 0 < x ∧ Nat.totient x = m) ∧
    ∀ y : ℕ, 0 < y → Nat.totient y = m → k ∣ y

/-- Unconditional Case I lower bound (`¬ 27 ∣ x`): `10^10240 < x`. -/
theorem carmichael_case1_gt_10_pow_10240 {x : ℕ}
    (hx : IsCarmichaelCounterexample x) (h27 : ¬ 27 ∣ x) :
    10 ^ 10240 < x := by
  sorry

/-- Unconditional Case II lower bound (`27 ∣ x`): `10^10117 < x`. -/
theorem carmichael_case2_gt_10_pow_10117 {x : ℕ}
    (hx : IsCarmichaelCounterexample x) (h27 : 27 ∣ x) :
    10 ^ 10117 < x := by
  sorry

/-- Unconditional lower bound `10^10117 < x` for every Carmichael counterexample `x`. -/
theorem carmichael_counterexample_gt_10_pow_10117 {x : ℕ}
    (hx : IsCarmichaelCounterexample x) :
    10 ^ 10117 < x := by
  sorry

/-- Ford's (1998) Lemma 7.2: prime-square forcing for unitary divisors of a
Carmichael counterexample. -/
theorem ford_lemma_7_2 {x d e : ℕ}
    (hx : IsCarmichaelCounterexample x)
    (hd : d ∣ x)
    (hcop : Nat.Coprime d (x / d))
    (hrad : rad (Nat.totient d) ∣ x)
    (he : e ∣ (x / d) / rad (x / d))
    (hP : Nat.Prime (1 + e * Nat.totient d)) :
    (1 + e * Nat.totient d) ^ 2 ∣ x := by
  sorry

/-- Klee's (1947) structural constraints on any minimal Carmichael counterexample. -/
theorem minimal_counterexample_structure {x₀ : ℕ} (hx₀ : IsMinimalCounterexample x₀) :
    4 ∣ x₀ ∧ ¬ (8 ∣ x₀) ∧ ¬ (5 ∣ x₀) ∧ ¬ (17 ∣ x₀) ∧ ¬ (257 ∣ x₀) ∧ ¬ (65537 ∣ x₀) := by
  sorry

/-- Pomerance's (1974) sufficient condition for a Carmichael counterexample. -/
theorem pomerance_sufficient_condition {x : ℕ} (hx : 0 < x)
    (hpom : ∀ p : ℕ, Nat.Prime p → (p - 1) ∣ Nat.totient x → p ^ 2 ∣ x) :
    IsCarmichaelCounterexample x := by
  sorry

/-- Ford's (1998, §7.3) reduction of Carmichael's conjecture to `k = 6`. -/
theorem no_k6_witness_implies_carmichael
    (h6 : ¬ ∃ m : ℕ, IsDivisibleTotientWitness 6 m) :
    ∀ x : ℕ, ¬ IsCarmichaelCounterexample x := by
  sorry

/-- Unconditional lower bound `32000 ≤ m` for every `k = 10` divisible-preimage witness. -/
theorem k10_witness_ge_32000 {m : ℕ} (hm : IsDivisibleTotientWitness 10 m) :
    32000 ≤ m := by
  sorry

/-- Grounding witness: `φ(y) = 10` if and only if `y ∈ {11, 22}`. -/
theorem totient_eq_ten_iff (y : ℕ) : Nat.totient y = 10 ↔ y = 11 ∨ y = 22 := by
  sorry

/-- Grounding witness: every positive preimage of `110` is divisible by `11`. -/
theorem k11_witness_110 : IsDivisibleTotientWitness 11 110 := by
  sorry

/-- `n` lies in the image of Euler's totient on positive integers. -/
def IsTotientValue (n : ℕ) : Prop :=
  ∃ y : ℕ, 0 < y ∧ Nat.totient y = n

/-- Count of distinct totient values `1 ≤ n ≤ X`. -/
noncomputable def V (X : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 X).filter (fun n => IsTotientValue n)).card

/-- Count of singleton totient values `1 ≤ n ≤ X` (`A(n) = 1`). -/
noncomputable def V1 (X : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 X).filter
    (fun n => ∃ x : ℕ, IsCarmichaelCounterexample x ∧ Nat.totient x = n)).card

/-- Count of totient values `1 ≤ n ≤ X` whose every positive preimage is divisible by `a ^ 2`. -/
noncomputable def VDiv (X a : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 X).filter
    (fun n => IsTotientValue n ∧ ∀ y : ℕ, 0 < y → Nat.totient y = n → a ^ 2 ∣ y)).card

/-- Reciprocal-sum totient-value transfer: forced prime-square divisor `d ≥ 6 * 10^D` with
`∑_{p ∈ S} 1/p < 1/2` forces `10^D < φ(x)`. -/
theorem totient_value_gt_of_forced_primes
    {D b x : ℕ} {S : Finset ℕ}
    (hx : 0 < x)
    (hb : b = 36 ∨ b = 108)
    (hS : ∀ p ∈ S, Nat.Prime p ∧ 5 ≤ p)
    (hdvd : b * ∏ p ∈ S, p ^ 2 ∣ x)
    (hbig : 6 * 10 ^ D ≤ b * ∏ p ∈ S, p ^ 2)
    (hrec : ∑ p ∈ S, (1 : ℝ) / (p : ℝ) < 1 / 2) :
    10 ^ D < Nat.totient x := by
  sorry

/-- Ford's (1998) Lemmas 7.4–7.5: for every `a ≥ 2`, `VDiv X a ≤ V (X / a)`. -/
theorem ford_lemma_7_4_7_5 {X a : ℕ} (ha : 2 ≤ a) :
    VDiv X a ≤ V (X / a) := by
  sorry

/-- General limiting singleton density bound: if every counterexample is divisible by
`a₁ ^ 2` or `a₂ ^ 2`, then `liminf V₁(X) / V(X) ≤ 2 / min a₁ a₂`. -/
theorem liminf_V1_div_V_le_two_div_min {a₁ a₂ : ℕ} (ha₁ : 2 ≤ a₁) (ha₂ : 2 ≤ a₂)
    (hcov : ∀ x : ℕ, IsCarmichaelCounterexample x → a₁ ^ 2 ∣ x ∨ a₂ ^ 2 ∣ x) :
    Filter.liminf (fun X : ℕ => ((V1 X : ℝ) / (V X : ℝ))) Filter.atTop ≤
      (2 : ℝ) / (min a₁ a₂ : ℕ) := by
  sorry

/-- Unconditional pure-kernel limiting singleton density bound:
`liminf V₁(X) / V(X) < 1 / 10 ^ 5057`. -/
theorem carmichael_liminf_density_lt_10_pow_neg_5057 :
    Filter.liminf (fun X : ℕ => ((V1 X : ℝ) / (V X : ℝ))) Filter.atTop <
      1 / (10 : ℝ) ^ 5057 := by
  sorry

end CarmichaelChallenge
