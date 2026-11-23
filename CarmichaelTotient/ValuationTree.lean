module

public import CarmichaelTotient.StructuralAndPomerance

import Mathlib.Tactic

/-!
# Multi-Branch Valuation Case Trees & Ford's `k = 10` Divisible-Preimage Descent (`K = 50` / `K = 60`)

Formalizes two tightly coupled multi-branch valuation descent frameworks:

## Part I: Multi-Branch Valuation Case Trees for Carmichael Counterexamples
1. `ExactPowDvd p a x` (`p ^ a ∥ x`): `p ^ a ∣ x ∧ ¬ p ^ (a + 1) ∣ x`, binary split completeness
   (`exactPowDvd_or_succ_pow_dvd`), and unitary-divisor synthesis (`unitary_of_exactPowDvd_finset`).
2. `ford_product_split_counterexample`: Multi-prime product generalization of Ford's Lemma 7.2
   Step 1 — if `∏_{P ∈ S} (P - 1) = e * φ(d)` for a nonempty set `S` of primes, then `∃ P ∈ S, P ∣ x`.
3. `CarmichaelValuationTree` & `carmichaelValuationTree_sound`: General multi-branch valuation
   tree supporting leaf lower bounds, unitary-divisor square forcing, binary prime-power splits
   (`p ^ k ∥ x` vs `p ^ (k + 1) ∣ x`), and multi-prime product splits.
4. `step_case2b_54k_plus_1` & `klee_three_way_case_split`: Klee's (1947) 3-way split on the
   3-adic valuation (`3 ^ 2 ∥ x`, `3 ^ 3 ∥ x`, `3 ^ 4 ∣ x`) with the `54k + 1` rule when `81 ∣ x`.

## Part II: Ford's (1998, §7.3) Divisible-Preimage Question & `k = 10` Descent Tree
1. `IsDivisibleTotientWitness k m`: totient `m` whose positive preimages are all divisible by `k`.
   - `no_k6_witness_implies_carmichael`: Ford's reduction of Carmichael's Conjecture to `k = 6`.
   - `k11_witness_110`, `k9_witness_54`, `k3_witness_54`: Ford's concrete witnesses `m = 110` for
     `k = 11` and `m = 54` for `k ∈ {3, 9}` (non-vacuity of `IsDivisibleTotientWitness`).
2. `k = 10` structural lemmas (`t3-1.md`, `t3-descent-1.md`):
   - `k10_witness_iff` (Proposition 1),
   - `k10_lemma_A` (`4 ∣ x ∧ 25 ∣ x ∧ 40 ∣ m`),
   - `k10_lemma_C_five` & `k10_lemma_C_two` (Lemma C multi-prime product splits),
   - `k10_lemma_B` & `k10_lemma_B2` (Lemmas B & B2 prime-5 and prime-2 analogues with the exact
     `F17-A` parity/5-divisibility guard `¬ 2 ∣ d ∨ t = 0` / `¬ 5 ∣ d ∨ t = 0`),
   - `k10_witness_ge_32000` (Proposition 3: unconditional proof that every `k = 10` witness
     satisfies `32000 ≤ m`).
3. `K10DescentTree`, `K10RungCertificate`, & `k10_bound_from_rung_certificate`:
   Exact soundness and root-enumeration completeness theorem modeling `descent_check.py` (used by
   the pod's `t3-descent-1` `K = 30`, `t3-descent-2` `K = 50` 5,681-root, and `t3-descent-3`
   `K = 60` 8,243-root certificates), together with an unconditional kernel witness
   `k10RungCertificate_4 : K10RungCertificate 4` proving `10 ^ 4 ≤ m`.
-/

@[expose] public section

namespace CarmichaelTotient

/-! ## Part I: Exact Valuation & Multi-Branch Carmichael Valuation Case Trees -/

/-- Exact prime-power divisibility `p ^ a ∥ x`: `p ^ a ∣ x` and `¬ p ^ (a + 1) ∣ x`. -/
def ExactPowDvd (p a x : ℕ) : Prop :=
  p ^ a ∣ x ∧ ¬ p ^ (a + 1) ∣ x

/-- Binary valuation-split completeness: `p ^ a ∣ x` implies `p ^ a ∥ x` or `p ^ (a + 1) ∣ x`. -/
theorem exactPowDvd_or_succ_pow_dvd {p a x : ℕ} (h : p ^ a ∣ x) :
    ExactPowDvd p a x ∨ p ^ (a + 1) ∣ x := by
  by_cases h1 : p ^ (a + 1) ∣ x
  · exact Or.inr h1
  · exact Or.inl ⟨h, h1⟩

/-- If `x > 0` and `p` is prime, `x` has exact prime-power divisibility at `a = x.factorization p`. -/
theorem exactPowDvd_factorization {p x : ℕ} (hp : Nat.Prime p) (hx : 0 < x) :
    ExactPowDvd p (x.factorization p) x := by
  have hx_ne : x ≠ 0 := Nat.ne_of_gt hx
  refine ⟨Nat.ordProj_dvd x p, ?_⟩
  intro hsucc
  have hle :=
    (Nat.factorization_le_iff_dvd (pow_ne_zero _ hp.ne_zero) hx_ne).mpr hsucc p
  rw [Nat.factorization_pow, Finsupp.smul_apply, hp.factorization_self] at hle
  simp at hle

/-- If `p` is prime and `ExactPowDvd p a x`, then `p ^ a` is a unitary divisor of `x`. -/
theorem coprime_div_of_exactPowDvd {p a x : ℕ} (hp : Nat.Prime p) (h : ExactPowDvd p a x) :
    Nat.Coprime (p ^ a) (x / p ^ a) := by
  have hcop_p : Nat.Coprime p (x / p ^ a) := by
    rw [hp.coprime_iff_not_dvd]
    rintro ⟨t, ht⟩
    apply h.2
    refine ⟨t, ?_⟩
    have hmul : p ^ a * (x / p ^ a) = x := Nat.mul_div_cancel' h.1
    calc
      x = p ^ a * (x / p ^ a) := hmul.symm
      _ = p ^ a * (p * t) := by rw [ht]
      _ = p ^ (a + 1) * t := by rw [pow_succ]; ring
  exact hcop_p.pow_left a

/-- Synthesizing a composite unitary divisor from any finite set `D` of primes with known exact
valuations in `x`. -/
theorem unitary_of_exactPowDvd_finset {D : Finset ℕ} {exp : ℕ → ℕ} {x : ℕ}
    (hD : ∀ p ∈ D, Nat.Prime p ∧ ExactPowDvd p (exp p) x) :
    (∏ p ∈ D, p ^ exp p) ∣ x ∧
      Nat.Coprime (∏ p ∈ D, p ^ exp p) (x / ∏ p ∈ D, p ^ exp p) := by
  have hdvd : (∏ p ∈ D, p ^ exp p) ∣ x := by
    apply finset_prod_dvd_of_nat_coprime
    · intro p hp q hq hpq
      exact ((Nat.coprime_primes (hD p hp).1 (hD q hq).1).mpr hpq).pow (exp p) (exp q)
    · intro p hp
      exact (hD p hp).2.1
  refine ⟨hdvd, ?_⟩
  set d := ∏ p ∈ D, p ^ exp p
  have hdx : d * (x / d) = x := Nat.mul_div_cancel' hdvd
  refine Nat.Coprime.prod_left fun p hp => ?_
  have ⟨hpr, hexact⟩ := hD p hp
  have hcop_p : Nat.Coprime p (x / d) := by
    rw [hpr.coprime_iff_not_dvd]
    rintro ⟨t, ht⟩
    have hp_dvd_d : p ^ exp p ∣ d := Finset.dvd_prod_of_mem (fun q => q ^ exp q) hp
    rcases hp_dvd_d with ⟨r, hr⟩
    apply hexact.2
    refine ⟨r * t, ?_⟩
    have h1 : x = (p ^ exp p * r) * (p * t) := by
      calc
        x = d * (x / d) := hdx.symm
        _ = d * (p * t) := by rw [ht]
        _ = (p ^ exp p * r) * (p * t) := by rw [hr]
    rw [h1, pow_succ]
    ring
  exact hcop_p.pow_left (exp p)

/-- Totient of a product of distinct primes in a `Finset ℕ`. -/
theorem totient_prod_primes {S : Finset ℕ} (hS : ∀ P ∈ S, Nat.Prime P) :
    Nat.totient (∏ P ∈ S, P) = ∏ P ∈ S, (P - 1) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert P s hPs ih =>
    rw [Finset.prod_insert hPs, Finset.prod_insert hPs]
    have hP : Nat.Prime P := hS P (Finset.mem_insert_self P s)
    have hs : ∀ Q ∈ s, Nat.Prime Q := fun Q hQ => hS Q (Finset.mem_insert_of_mem hQ)
    have hcop : Nat.Coprime P (∏ Q ∈ s, Q) := by
      refine Nat.Coprime.prod_right fun Q hQ => ?_
      exact (Nat.coprime_primes hP (hs Q hQ)).mpr (fun h => hPs (h ▸ hQ))
    rw [Nat.totient_mul hcop, Nat.totient_prime hP, ih hs]

/-- **Multi-Prime Product Generalization of Ford's Lemma 7.2 Step 1**:
If `x` is a Carmichael counterexample, `d` is a unitary divisor of `x`, `e ∣ (x/d)/rad(x/d)`,
and `S` is a nonempty finite set of primes with `∏_{P ∈ S} (P - 1) = e * φ(d)`, then at least
one `P ∈ S` divides `x`. -/
theorem ford_product_split_counterexample {x d e : ℕ} {S : Finset ℕ}
    (hx : IsCarmichaelCounterexample x)
    (hd : d ∣ x)
    (hcop : Nat.Coprime d (x / d))
    (he : e ∣ (x / d) / rad (x / d))
    (hS_ne : S.Nonempty)
    (hS_prime : ∀ P ∈ S, Nat.Prime P)
    (hprod : (∏ P ∈ S, (P - 1)) = e * Nat.totient d) :
    ∃ P ∈ S, P ∣ x := by
  by_contra hall
  push Not at hall
  set w := x / d
  have hdw : d * w = x := Nat.mul_div_cancel' hd
  have hw_pos : 0 < w := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, mul_zero] at hdw
    have := hx.1
    omega
  obtain ⟨hedvd, _, htot_w⟩ := totient_div_of_dvd_div_rad hw_pos he
  have hwe_dvd_x : w / e ∣ x := dvd_trans (Nat.div_dvd_of_dvd hedvd) (hdw ▸ dvd_mul_left w d)
  have hcopS : Nat.Coprime (∏ P ∈ S, P) (w / e) := by
    refine Nat.Coprime.prod_left fun P hP => ?_
    have hndvd : ¬ P ∣ w / e := fun h => hall P hP (dvd_trans h hwe_dvd_x)
    exact (hS_prime P hP).coprime_iff_not_dvd.mpr hndvd
  let y := (∏ P ∈ S, P) * (w / e)
  have hy_tot : Nat.totient y = Nat.totient x := by
    calc
      Nat.totient y = Nat.totient (∏ P ∈ S, P) * Nat.totient (w / e) := Nat.totient_mul hcopS
      _ = (∏ P ∈ S, (P - 1)) * Nat.totient (w / e) := by rw [totient_prod_primes hS_prime]
      _ = (e * Nat.totient d) * Nat.totient (w / e) := by rw [hprod]
      _ = Nat.totient d * (Nat.totient (w / e) * e) := by ring
      _ = Nat.totient d * Nat.totient w := by rw [htot_w]
      _ = Nat.totient (d * w) := (Nat.totient_mul hcop).symm
      _ = Nat.totient x := by rw [hdw]
  have hyx : y = x := hx.2 y hy_tot
  obtain ⟨P₀, hP₀⟩ := hS_ne
  have hP₀_dvd_prod : P₀ ∣ ∏ P ∈ S, P := Finset.dvd_prod_of_mem id hP₀
  exact hall P₀ hP₀ (hyx ▸ dvd_mul_of_dvd_left hP₀_dvd_prod (w / e))

/-- Valuation node constraint `(p, k, exact)` in a multi-branch valuation case tree:
asserts `p` is prime and either `p ^ k ∥ x` (`exact = true`) or `p ^ k ∣ x` (`exact = false`). -/
structure ValConstraint where
  p : ℕ
  k : ℕ
  exact : Bool
  deriving DecidableEq, Repr

/-- Semantics of a `ValConstraint` at a positive integer `x`. -/
def ValConstraint.holds (c : ValConstraint) (x : ℕ) : Prop :=
  Nat.Prime c.p ∧ (if c.exact then ExactPowDvd c.p c.k x else c.p ^ c.k ∣ x)

/-- Regardless of `c.exact`, `c.holds x` implies `c.p ^ c.k ∣ x`. -/
theorem ValConstraint.pow_dvd_of_holds {c : ValConstraint} {x : ℕ} (h : c.holds x) :
    c.p ^ c.k ∣ x := by
  rcases h with ⟨_, hd⟩
  by_cases hex : c.exact
  · simp only [hex, ↓reduceIte] at hd
    exact hd.1
  · simp only [hex, Bool.false_eq_true, ↓reduceIte] at hd
    exact hd

/-- General multi-branch valuation case tree for Carmichael's Totient Conjecture, generalizing
the 2-way Case I/II split and Klee's 3-way split to arbitrary trees of prime-power valuation
splits, unitary-divisor square forcings, and multi-prime product splits. -/
inductive CarmichaelValuationTree : List ValConstraint → ℕ → Prop
  | leaf (st : List ValConstraint) (B : ℕ) (P : Finset ℕ) (exp : ℕ → ℕ) :
      (∀ p ∈ P, ∃ exact, (⟨p, exp p, exact⟩ : ValConstraint) ∈ st) →
      B ≤ (∏ p ∈ P, p ^ exp p) →
      CarmichaelValuationTree st B
  | forceSq (st : List ValConstraint) (B : ℕ) (D : Finset ℕ) (exp : ℕ → ℕ) (e : ℕ) :
      (∀ p ∈ D, (⟨p, exp p, true⟩ : ValConstraint) ∈ st) →
      (∀ x : ℕ, IsCarmichaelCounterexample x → (∀ c ∈ st, c.holds x) →
        let d := ∏ p ∈ D, p ^ exp p
        rad (Nat.totient d) ∣ x ∧ e ∣ (x / d) / rad (x / d)) →
      Nat.Prime (1 + e * Nat.totient (∏ p ∈ D, p ^ exp p)) →
      CarmichaelValuationTree
        (⟨1 + e * Nat.totient (∏ p ∈ D, p ^ exp p), 2, false⟩ :: st) B →
      CarmichaelValuationTree st B
  | powerSplit (st : List ValConstraint) (B : ℕ) (p k : ℕ) :
      (⟨p, k, false⟩ : ValConstraint) ∈ st →
      CarmichaelValuationTree (⟨p, k, true⟩ :: st) B →
      CarmichaelValuationTree (⟨p, k + 1, false⟩ :: st) B →
      CarmichaelValuationTree st B
  | productSplit (st : List ValConstraint) (B : ℕ) (D : Finset ℕ) (exp : ℕ → ℕ)
      (e : ℕ) (S : Finset ℕ) :
      (∀ p ∈ D, (⟨p, exp p, true⟩ : ValConstraint) ∈ st) →
      (∀ x : ℕ, IsCarmichaelCounterexample x → (∀ c ∈ st, c.holds x) →
        let d := ∏ p ∈ D, p ^ exp p
        e ∣ (x / d) / rad (x / d)) →
      S.Nonempty →
      (∀ P ∈ S, Nat.Prime P) →
      (∏ P ∈ S, (P - 1)) = e * Nat.totient (∏ p ∈ D, p ^ exp p) →
      (∀ P ∈ S, CarmichaelValuationTree (⟨P, 1, false⟩ :: st) B) →
      CarmichaelValuationTree st B

/-- **Soundness & Completeness of `CarmichaelValuationTree`**:
Every valid closed `CarmichaelValuationTree` from a satisfied state `st` forces `B ≤ x` for
every Carmichael counterexample `x`. -/
theorem carmichaelValuationTree_sound {st : List ValConstraint} {B x : ℕ}
    (hx : IsCarmichaelCounterexample x)
    (htree : CarmichaelValuationTree st B)
    (hst : ∀ c ∈ st, c.holds x) :
    B ≤ x := by
  induction htree with
  | leaf st B P exp hmem hBle =>
    have hdvd : (∏ p ∈ P, p ^ exp p) ∣ x := by
      apply finset_prod_dvd_of_nat_coprime
      · intro p hp q hq hpq
        obtain ⟨ex1, hm1⟩ := hmem p hp
        obtain ⟨ex2, hm2⟩ := hmem q hq
        exact ((Nat.coprime_primes (hst _ hm1).1 (hst _ hm2).1).mpr hpq).pow (exp p) (exp q)
      · intro p hp
        obtain ⟨ex, hm⟩ := hmem p hp
        exact ValConstraint.pow_dvd_of_holds (hst _ hm)
    exact le_trans hBle (Nat.le_of_dvd hx.1 hdvd)
  | forceSq st B D exp e hD hside hP _ ih =>
    have hD_exact : ∀ p ∈ D, Nat.Prime p ∧ ExactPowDvd p (exp p) x := by
      intro p hp
      have hc := hst _ (hD p hp)
      exact ⟨hc.1, by simpa [ValConstraint.holds] using hc.2⟩
    obtain ⟨hd_dvd, hd_cop⟩ := unitary_of_exactPowDvd_finset hD_exact
    obtain ⟨hrad, he⟩ := hside x hx hst
    have hsq := ford_lemma_7_2 hx hd_dvd hd_cop hrad he hP
    apply ih
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact ⟨hP, hsq⟩
    · exact hst c hc'
  | powerSplit st B p k hmem _ _ ihExact ihSucc =>
    have hc := hst _ hmem
    have hpk : p ^ k ∣ x := ValConstraint.pow_dvd_of_holds hc
    rcases exactPowDvd_or_succ_pow_dvd hpk with hexact | hsucc
    · apply ihExact
      intro c hc'
      rcases List.mem_cons.mp hc' with rfl | htail
      · exact ⟨hc.1, hexact⟩
      · exact hst c htail
    · apply ihSucc
      intro c hc'
      rcases List.mem_cons.mp hc' with rfl | htail
      · exact ⟨hc.1, hsucc⟩
      · exact hst c htail
  | productSplit st B D exp e S hD hside hSne hSprime hprod _ ih =>
    have hD_exact : ∀ p ∈ D, Nat.Prime p ∧ ExactPowDvd p (exp p) x := by
      intro p hp
      have hc := hst _ (hD p hp)
      exact ⟨hc.1, by simpa [ValConstraint.holds] using hc.2⟩
    obtain ⟨hd_dvd, hd_cop⟩ := unitary_of_exactPowDvd_finset hD_exact
    have he := hside x hx hst
    obtain ⟨P, hPS, hPdvd⟩ :=
      ford_product_split_counterexample hx hd_dvd hd_cop he hSne hSprime hprod
    apply ih P hPS
    intro c hc
    rcases List.mem_cons.mp hc with rfl | htail
    · exact ⟨hSprime P hPS, by simpa using hPdvd⟩
    · exact hst c htail

/-- In Case II (`27 ∣ x`), `19 ^ 2 ∣ x`. -/
theorem nineteen_sq_dvd_case2 {x : ℕ} (hx : IsCarmichaelCounterexample x) (h27 : 27 ∣ x) :
    19 ^ 2 ∣ x := by
  have h := step_case2_18k_plus_1 (x := x) (K := ∅) hx h27 (by simp) (by norm_num)
  simpa using h

/-- **Klee (1947) Case III step rule `54k + 1`** (when `81 ∣ x`, using `d = 1, e = 54k`):
For any finite set `K` of primes `≥ 5` whose squares divide `x`, if `54 * (∏ p ∈ K, p) + 1`
is prime then its square divides `x`. -/
theorem step_case2b_54k_plus_1 {x : ℕ} {K : Finset ℕ}
    (hx : IsCarmichaelCounterexample x)
    (h81 : 81 ∣ x)
    (hK : ∀ p ∈ K, Nat.Prime p ∧ 5 ≤ p ∧ p ^ 2 ∣ x)
    (hP : Nat.Prime (54 * (∏ p ∈ K, p) + 1)) :
    (54 * (∏ p ∈ K, p) + 1) ^ 2 ∣ x := by
  set k := ∏ p ∈ K, p
  have h4 : 2 ^ (1 + 1) ∣ x := by simpa using four_dvd_counterexample hx
  have h2 : 2 ∣ x / rad x := by simpa using prime_pow_dvd_div_rad hx.1 Nat.prime_two h4
  have h27 : 27 ∣ x / rad x := by
    have h34 : 3 ^ (3 + 1) ∣ x := by simpa using h81
    simpa using prime_pow_dvd_div_rad hx.1 Nat.prime_three h34
  have h54 : 54 ∣ x / rad x := by
    have := (by decide : Nat.Coprime 2 27).mul_dvd_of_dvd_of_dvd h2 h27
    norm_num at this
    exact this
  have hk : k ∣ x / rad x :=
    prod_primes_dvd_div_rad hx.1 fun p hp => ⟨(hK p hp).1, (hK p hp).2.2⟩
  have ⟨hcop2, hcop3⟩ := coprime_of_primes_ge_five fun p hp => ⟨(hK p hp).1, (hK p hp).2.1⟩
  have hcop54 : Nat.Coprime 54 k := by
    have : (54 : ℕ) = 2 * 3 ^ 3 := by norm_num
    rw [this]
    exact hcop2.mul_left (hcop3.pow_left 3)
  have h54k : 54 * k ∣ x / rad x := hcop54.mul_dvd_of_dvd_of_dvd h54 hk
  have hP' : Nat.Prime (1 + (54 * k) * Nat.totient 1) := by
    simpa [Nat.totient_one, add_comm] using hP
  have hstep := ford_lemma_7_2 (x := x) (d := 1) (e := 54 * k) hx
    (one_dvd x) (by simp) (by simp [rad_one]) (by simpa using h54k) hP'
  simpa [Nat.totient_one, add_comm] using hstep

/-- **Klee's (1947) Three-Way Valuation Split**:
Every Carmichael counterexample falls into one of Klee's three cases on the 3-adic valuation:
`(3 ^ 2 ∥ x ∧ 13 ^ 2 ∣ x) ∨ (3 ^ 3 ∥ x ∧ 19 ^ 2 ∣ x) ∨ (81 ∣ x ∧ 19 ^ 2 ∣ x)`. -/
theorem klee_three_way_case_split {x : ℕ} (hx : IsCarmichaelCounterexample x) :
    (ExactPowDvd 3 2 x ∧ 13 ^ 2 ∣ x) ∨
      (ExactPowDvd 3 3 x ∧ 19 ^ 2 ∣ x) ∨
      (81 ∣ x ∧ 19 ^ 2 ∣ x) := by
  have h9 : 3 ^ 2 ∣ x := by simpa using nine_dvd_counterexample hx
  rcases exactPowDvd_or_succ_pow_dvd h9 with hex2 | h27
  · exact Or.inl ⟨hex2, thirteen_sq_dvd_case1 hx (by simpa using hex2.2)⟩
  · have h27' : 27 ∣ x := by simpa using h27
    rcases exactPowDvd_or_succ_pow_dvd h27 with hex3 | h81
    · exact Or.inr (Or.inl ⟨hex3, nineteen_sq_dvd_case2 hx h27'⟩)
    · exact Or.inr (Or.inr ⟨by simpa using h81, nineteen_sq_dvd_case2 hx h27'⟩)

/-! ## Part II: Ford's (1998, §7.3) Divisible-Preimage Question & `k = 10` Descent Tree -/

/-- `m` is a **divisible-by-`k` totient witness** (Ford 1998, §7.3, counted by `V(x; k)`) if `m`
is a totient (`∃ x > 0, φ(x) = m`) and every positive preimage `y` with `φ(y) = m` satisfies
`k ∣ y`. -/
def IsDivisibleTotientWitness (k m : ℕ) : Prop :=
  (∃ x : ℕ, 0 < x ∧ Nat.totient x = m) ∧
    ∀ y : ℕ, 0 < y → Nat.totient y = m → k ∣ y

/-- **Ford's (1998, §7.3) Reduction of Carmichael's Conjecture to `k = 6`**:
If no totient `m` has all of its positive preimages divisible by `6`, then no Carmichael
counterexample exists. -/
theorem no_k6_witness_implies_carmichael
    (h6 : ¬ ∃ m : ℕ, IsDivisibleTotientWitness 6 m) :
    ∀ x : ℕ, ¬ IsCarmichaelCounterexample x := by
  intro x hx
  apply h6
  refine ⟨Nat.totient x, ⟨x, hx.1, rfl⟩, ?_⟩
  intro y _ hy
  have hyx : y = x := hx.2 y hy
  subst hyx
  have h2 : 2 ∣ y := dvd_trans (by norm_num : 2 ∣ 4) (four_dvd_counterexample hx)
  have h3 : 3 ∣ y := dvd_trans (by norm_num : 3 ∣ 9) (nine_dvd_counterexample hx)
  have h6y := (by decide : Nat.Coprime 2 3).mul_dvd_of_dvd_of_dvd h2 h3
  norm_num at h6y
  exact h6y

/-- Helper: `φ(n)` is never an odd integer greater than `1`. -/
theorem not_totient_odd_gt_one {n m : ℕ} (hm_odd : Odd m) (hm_gt : 1 < m) :
    Nat.totient n ≠ m := by
  intro h
  by_cases hn3 : 3 ≤ n
  · have heven : Even (Nat.totient n) := totient_even_of_ge_three hn3
    rw [h] at heven
    exact (Nat.not_even_iff_odd.mpr hm_odd) heven
  · interval_cases n <;> simp [Nat.totient_zero, Nat.totient_one, Nat.totient_two] at h <;> omega

/-- **Ford's Concrete Witness for `k = 11`**: `m = 110` is a totient (`φ(121) = 110`) all of whose
positive preimages are divisible by `11` (`121` and `242`). -/
theorem k11_witness_110 : IsDivisibleTotientWitness 11 110 := by
  refine ⟨⟨121, by norm_num, by decide⟩, ?_⟩
  intro y hy_pos hy_tot
  have hy_ne : y ≠ 0 := Nat.ne_of_gt hy_pos
  have h11_tot : 11 ∣ Nat.totient y := by rw [hy_tot]; norm_num
  rcases (prime_dvd_totient_iff hy_ne (by norm_num : Nat.Prime 11)).mp h11_tot with
    hsq | ⟨q, hq_mem, h11_qm1⟩
  · exact dvd_trans (dvd_pow_self 11 (by norm_num : 2 ≠ 0)) hsq
  · exfalso
    have hqp : Nat.Prime q := Nat.prime_of_mem_primeFactors hq_mem
    have hq_dvd_y : q ∣ y := Nat.dvd_of_mem_primeFactors hq_mem
    have hqm1_dvd : q - 1 ∣ 110 := by
      rw [← hy_tot, ← Nat.totient_prime hqp]
      exact Nat.totient_dvd_of_dvd hq_dvd_y
    rcases h11_qm1 with ⟨j, hj⟩
    have hj_pos : 0 < j := by
      have hq2 := hqp.two_le
      by_contra h0
      have hj0 : j = 0 := by omega
      rw [hj0, mul_zero] at hj
      omega
    have hj_dvd : j ∣ 10 := by
      rw [hj] at hqm1_dvd
      rcases hqm1_dvd with ⟨t, ht⟩
      exact ⟨t, by linarith⟩
    have hj_cases : j = 1 ∨ j = 2 ∨ j = 5 ∨ j = 10 := by
      have hle : j ≤ 10 := Nat.le_of_dvd (by norm_num) hj_dvd
      interval_cases j <;> omega
    have hq_eq : q = 1 + 11 * j := by
      have hq2 := hqp.two_le
      omega
    rcases hj_cases with rfl | rfl | rfl | rfl
    · rw [hq_eq] at hqp; norm_num at hqp
    · have hq23 : q = 23 := by omega
      subst hq23
      have h23_sq : ¬ 23 ^ 2 ∣ y := by
        intro hsq23
        have hd := Nat.totient_dvd_of_dvd hsq23
        rw [Nat.totient_prime_pow (by norm_num : Nat.Prime 23) (by norm_num), hy_tot] at hd
        norm_num at hd
      have hcop23 : Nat.Coprime 23 (y / 23) := by
        rw [hqp.coprime_iff_not_dvd]
        rintro ⟨t, ht⟩
        apply h23_sq
        have hmul : 23 * (y / 23) = y := Nat.mul_div_cancel' hq_dvd_y
        exact ⟨t, by rw [← hmul, ht]; ring⟩
      have hmul_tot : Nat.totient 23 * Nat.totient (y / 23) = 110 := by
        rw [← Nat.totient_mul hcop23, Nat.mul_div_cancel' hq_dvd_y, hy_tot]
      have h22 : Nat.totient 23 = 22 := by decide
      rw [h22] at hmul_tot
      have htot5 : Nat.totient (y / 23) = 5 := by omega
      exact not_totient_odd_gt_one (by decide : Odd 5) (by norm_num) htot5
    · rw [hq_eq] at hqp; norm_num at hqp
    · rw [hq_eq] at hqp; norm_num at hqp

/-- **Ford's Concrete Witness for `k = 9` (and `k = 3`)**: `m = 54` is a totient (`φ(81) = 54`)
all of whose positive preimages (`81` and `162`) are divisible by `9`. -/
theorem k9_witness_54 : IsDivisibleTotientWitness 9 54 := by
  refine ⟨⟨81, by norm_num, by decide⟩, ?_⟩
  intro y hy_pos hy_tot
  have hy_ne : y ≠ 0 := Nat.ne_of_gt hy_pos
  have hno_ge5 : ∀ q ∈ y.primeFactors, q = 2 ∨ q = 3 := by
    intro q hq_mem
    have hqp : Nat.Prime q := Nat.prime_of_mem_primeFactors hq_mem
    have hq_dvd : q ∣ y := Nat.dvd_of_mem_primeFactors hq_mem
    have hqm1_dvd : q - 1 ∣ 54 := by
      rw [← hy_tot, ← Nat.totient_prime hqp]
      exact Nat.totient_dvd_of_dvd hq_dvd
    have hq_le : q ≤ 55 := by
      have := Nat.le_of_dvd (by norm_num) hqm1_dvd
      omega
    have hcases : q = 2 ∨ q = 3 ∨ q = 7 ∨ q = 19 := by
      have hq2 := hqp.two_le
      by_contra hbad
      interval_cases q <;> first | omega | (revert hqp hqm1_dvd; decide)
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exfalso
      have h7_sq : ¬ 7 ^ 2 ∣ y := by
        intro hsq
        have hd := Nat.totient_dvd_of_dvd hsq
        rw [Nat.totient_prime_pow (by norm_num : Nat.Prime 7) (by norm_num), hy_tot] at hd
        norm_num at hd
      have hcop7 : Nat.Coprime 7 (y / 7) := by
        rw [hqp.coprime_iff_not_dvd]
        rintro ⟨t, ht⟩
        apply h7_sq
        have hmul : 7 * (y / 7) = y := Nat.mul_div_cancel' hq_dvd
        exact ⟨t, by rw [← hmul, ht]; ring⟩
      have hmul_tot : Nat.totient 7 * Nat.totient (y / 7) = 54 := by
        rw [← Nat.totient_mul hcop7, Nat.mul_div_cancel' hq_dvd, hy_tot]
      have h6 : Nat.totient 7 = 6 := by decide
      rw [h6] at hmul_tot
      have htot9 : Nat.totient (y / 7) = 9 := by omega
      exact not_totient_odd_gt_one (by decide : Odd 9) (by norm_num) htot9
    · exfalso
      have h19_sq : ¬ 19 ^ 2 ∣ y := by
        intro hsq
        have hd := Nat.totient_dvd_of_dvd hsq
        rw [Nat.totient_prime_pow (by norm_num : Nat.Prime 19) (by norm_num), hy_tot] at hd
        norm_num at hd
      have hcop19 : Nat.Coprime 19 (y / 19) := by
        rw [hqp.coprime_iff_not_dvd]
        rintro ⟨t, ht⟩
        apply h19_sq
        have hmul : 19 * (y / 19) = y := Nat.mul_div_cancel' hq_dvd
        exact ⟨t, by rw [← hmul, ht]; ring⟩
      have hmul_tot : Nat.totient 19 * Nat.totient (y / 19) = 54 := by
        rw [← Nat.totient_mul hcop19, Nat.mul_div_cancel' hq_dvd, hy_tot]
      have h18 : Nat.totient 19 = 18 := by decide
      rw [h18] at hmul_tot
      have htot3 : Nat.totient (y / 19) = 3 := by omega
      exact not_totient_odd_gt_one (by decide : Odd 3) (by norm_num) htot3
  have hfac3 : (Nat.totient y).factorization 3 = 3 := by
    rw [hy_tot]
    have h54 : (54 : ℕ) = 2 * 3 ^ 3 := by norm_num
    rw [h54, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.prime_two.factorization, Finsupp.single_eq_of_ne (by omega), zero_add,
      Nat.factorization_pow, Finsupp.smul_apply, Nat.prime_three.factorization_self]
    rfl
  rw [totient_factorization_eq hy_ne Nat.prime_three] at hfac3
  have hsum0 : ∑ q ∈ y.primeFactors.erase 3, (q - 1).factorization 3 = 0 := by
    refine Finset.sum_eq_zero fun q hq => ?_
    have hq_ne : q ≠ 3 := Finset.ne_of_mem_erase hq
    rcases hno_ge5 q (Finset.mem_of_mem_erase hq) with rfl | rfl
    · simp
    · exact False.elim (hq_ne rfl)
  rw [hsum0, add_zero] at hfac3
  have hfy : y.factorization 3 = 4 := by omega
  have h81 : 3 ^ 4 ∣ y := by
    rw [← hfy]
    exact Nat.ordProj_dvd y 3
  exact dvd_trans (by norm_num : 9 ∣ 3 ^ 4) h81

/-- `m = 54` is also a witness for `k = 3`. -/
theorem k3_witness_54 : IsDivisibleTotientWitness 3 54 :=
  ⟨k9_witness_54.1, fun y hy htot => dvd_trans (by norm_num : 3 ∣ 9) (k9_witness_54.2 y hy htot)⟩

/-! ### `k = 10` Structural Reduction, Lemmas A, B, B2, C, and Proposition 3 -/

/-- **Proposition 1 (`t3-1.md`)**: `m` is a `k = 10` witness iff `m` is a totient with no odd
positive preimage and no positive preimage coprime to `5`. -/
theorem k10_witness_iff (m : ℕ) :
    IsDivisibleTotientWitness 10 m ↔
      (∃ x : ℕ, 0 < x ∧ Nat.totient x = m) ∧
        (∀ y : ℕ, 0 < y → Nat.totient y = m → 2 ∣ y ∧ 5 ∣ y) := by
  unfold IsDivisibleTotientWitness
  refine and_congr_right fun _ => forall_congr' fun y => imp_congr_right fun _ =>
    imp_congr_right fun _ => ?_
  constructor
  · intro h10
    exact ⟨dvd_trans (by norm_num : 2 ∣ 10) h10, dvd_trans (by norm_num : 5 ∣ 10) h10⟩
  · rintro ⟨h2, h5⟩
    have := (by decide : Nat.Coprime 2 5).mul_dvd_of_dvd_of_dvd h2 h5
    norm_num at this
    exact this

/-- **Lemma A (`t3-1.md`)**: Every positive preimage `x` of a `k = 10` witness `m` satisfies
`4 ∣ x`, `25 ∣ x`, `100 ∣ x`, and `40 ∣ m`. -/
theorem k10_lemma_A {m x : ℕ}
    (hm : IsDivisibleTotientWitness 10 m)
    (hx_pos : 0 < x)
    (hx_tot : Nat.totient x = m) :
    4 ∣ x ∧ 25 ∣ x ∧ 100 ∣ x ∧ 40 ∣ m := by
  have ⟨h2x, h5x⟩ := ((k10_witness_iff m).mp hm).2 x hx_pos hx_tot
  have h4 : 4 ∣ x := by
    rcases h2x with ⟨y, rfl⟩
    have hy_pos : 0 < y := by omega
    by_cases hy_even : 2 ∣ y
    · rcases hy_even with ⟨z, rfl⟩
      exact ⟨z, by ring⟩
    · exfalso
      have hy_odd : Odd y := Nat.odd_iff.mpr (by omega)
      have hy_tot : Nat.totient y = m := by
        rw [← hx_tot, totient_two_mul_odd hy_odd]
      have ⟨h2y, _⟩ := ((k10_witness_iff m).mp hm).2 y hy_pos hy_tot
      rcases h2y with ⟨z, rfl⟩
      rcases hy_odd with ⟨u, hu⟩
      omega
  have h25 : 25 ∣ x := by
    by_contra hnot25
    have hex5 : ExactPowDvd 5 1 x := ⟨by simpa using h5x, by simpa using hnot25⟩
    have hcop5 : Nat.Coprime 5 (x / 5) := by
      simpa using coprime_div_of_exactPowDvd (by norm_num : Nat.Prime 5) hex5
    set w := x / 5
    have h5w : 5 * w = x := Nat.mul_div_cancel' h5x
    have hw_pos : 0 < w := Nat.pos_of_ne_zero fun h0 => by
      rw [h0, mul_zero] at h5w
      omega
    have h2w : 2 ∣ w := by
      have h4_5w : 4 ∣ 5 * w := h5w.symm ▸ h4
      have h4w : 4 ∣ w := (by decide : Nat.Coprime 4 5).dvd_of_dvd_mul_left h4_5w
      exact dvd_trans (by norm_num : 2 ∣ 4) h4w
    let x' := w * 4
    have hx'_pos : 0 < x' := by dsimp [x']; omega
    have hx'_tot : Nat.totient x' = m := by
      have hpr4 : ∀ q : ℕ, Nat.Prime q → q ∣ 4 → q ∣ w := by
        intro q hq hq4
        have hq2 : q = 2 := by
          have : 4 = 2 ^ 2 := by norm_num
          rw [this] at hq4
          exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow hq4)
        rwa [hq2]
      calc
        Nat.totient (w * 4) = Nat.totient w * 4 := totient_mul_of_primes_dvd 4 w hpr4
        _ = Nat.totient 5 * Nat.totient w := by
          have : Nat.totient 5 = 4 := by decide
          rw [this]; ring
        _ = Nat.totient (5 * w) := (Nat.totient_mul hcop5).symm
        _ = m := by rw [h5w, hx_tot]
    have ⟨_, h5x'⟩ := ((k10_witness_iff m).mp hm).2 x' hx'_pos hx'_tot
    have hcop5_x' : Nat.Coprime 5 (w * 4) :=
      hcop5.mul_right (by decide : Nat.Coprime 5 4)
    exact (by norm_num : ¬ (5 ∣ 1)) (hcop5_x'.gcd_eq_one ▸ Nat.dvd_gcd dvd_rfl h5x')
  have h100 : 100 ∣ x := by
    have := (by decide : Nat.Coprime 4 25).mul_dvd_of_dvd_of_dvd h4 h25
    norm_num at this
    exact this
  have h40 : 40 ∣ m := by
    have hd := Nat.totient_dvd_of_dvd h100
    have htot100 : Nat.totient 100 = 40 := by decide
    rwa [htot100, hx_tot] at hd
  exact ⟨h4, h25, h100, h40⟩

/-- **Lemma C for Prime `5` (`t3-descent-1.md`, §1)**:
Let `x > 0` be a preimage of a `k = 10` witness `m`. Suppose `d ∣ x`, `gcd(d, x/d) = 1`, `5 ∣ d`,
`e ∣ (x/d) / rad(x/d)`, `(¬ 2 ∣ d ∨ t = 0)`, and `(∏_{P ∈ S} (P - 1)) * 2 ^ t = e * φ(d)` for a
finite set `S` of primes none equal to `5` (note: `S` may even be empty when `e * φ(d) = 2 ^ t`,
producing an immediate contradiction!). Then `∃ P ∈ S, P ∣ x`. -/
theorem k10_lemma_C_five {m x d e t : ℕ} {S : Finset ℕ}
    (hm : IsDivisibleTotientWitness 10 m)
    (hx_pos : 0 < x)
    (hx_tot : Nat.totient x = m)
    (hd : d ∣ x)
    (hcop : Nat.Coprime d (x / d))
    (h5d : 5 ∣ d)
    (he : e ∣ (x / d) / rad (x / d))
    (hguard : ¬ (2 ∣ d) ∨ t = 0)
    (hS_prime : ∀ P ∈ S, Nat.Prime P ∧ P ≠ 5)
    (hprod : (∏ P ∈ S, (P - 1)) * 2 ^ t = e * Nat.totient d) :
    ∃ P ∈ S, P ∣ x := by
  by_contra hall
  push Not at hall
  obtain ⟨h4x, _, _, _⟩ := k10_lemma_A hm hx_pos hx_tot
  -- First note 2 ∉ S since 2 ∣ 4 ∣ x.
  have hS_odd : ∀ P ∈ S, P ≠ 2 := by
    intro P hP rfl
    exact hall 2 hP (dvd_trans (by norm_num : 2 ∣ 4) h4x)
  set w := x / d
  have hdw : d * w = x := Nat.mul_div_cancel' hd
  have hw_pos : 0 < w := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, mul_zero] at hdw
    omega
  obtain ⟨hedvd, _, htot_w⟩ := totient_div_of_dvd_div_rad hw_pos he
  have hwe_pos : 0 < w / e := Nat.div_pos (Nat.le_of_dvd hw_pos hedvd)
    (Nat.pos_of_dvd_of_pos hedvd hw_pos)
  have hwe_dvd_x : w / e ∣ x := dvd_trans (Nat.div_dvd_of_dvd hedvd) (hdw ▸ dvd_mul_left w d)
  -- Check (w / e) * 2 ^ t has totient φ(w / e) * 2 ^ t:
  have h2t_tot : Nat.totient ((w / e) * 2 ^ t) = Nat.totient (w / e) * 2 ^ t := by
    rcases hguard with h2ndvd_d | rfl
    · have h2d_cop : Nat.Coprime 4 d := by
        have hcop2d : Nat.Coprime 2 d := Nat.prime_two.coprime_iff_not_dvd.mpr h2ndvd_d
        have : (4 : ℕ) = 2 ^ 2 := by norm_num
        rw [this]
        exact hcop2d.pow_left 2
      have h4w : 4 ∣ w := h2d_cop.dvd_of_dvd_mul_left (hdw.symm ▸ h4x)
      have h2w : 2 ∣ w := dvd_trans (by norm_num : 2 ∣ 4) h4w
      have h2_mem : 2 ∈ w.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2w, Nat.ne_of_gt hw_pos⟩
      have h2_rad : 2 ∣ rad w := dvd_rad_of_mem_primeFactors h2_mem
      have hrad_dvd_we : rad w ∣ w / e := by
        rcases he with ⟨u, hu⟩
        have hw_eq : w = e * (u * rad w) := by
          calc
            w = w / rad w * rad w := (Nat.div_mul_cancel (rad_dvd_self w)).symm
            _ = (e * u) * rad w := by rw [hu]
            _ = e * (u * rad w) := by ring
        have he_pos : 0 < e := Nat.pos_of_dvd_of_pos hedvd hw_pos
        have hwe_eq : w / e = u * rad w := by
          conv_lhs => rw [hw_eq]
          exact Nat.mul_div_cancel_left _ he_pos
        rw [hwe_eq]
        exact dvd_mul_left (rad w) u
      have h2_we : 2 ∣ w / e := dvd_trans h2_rad hrad_dvd_we
      apply totient_mul_of_primes_dvd
      intro q hq hq2t
      have hq2 : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow hq2t)
      rwa [hq2]
    · simp
  let x' := (∏ P ∈ S, P) * ((w / e) * 2 ^ t)
  have hx'_pos : 0 < x' := mul_pos
    (Finset.prod_pos fun P hP => (hS_prime P hP).1.pos)
    (mul_pos hwe_pos (pow_pos (by norm_num) t))
  have hcop_S_rhs : Nat.Coprime (∏ P ∈ S, P) ((w / e) * 2 ^ t) := by
    refine Nat.Coprime.prod_left fun P hP => ?_
    have hPp : Nat.Prime P := (hS_prime P hP).1
    have hcop_we : Nat.Coprime P (w / e) :=
      hPp.coprime_iff_not_dvd.mpr fun h => hall P hP (dvd_trans h hwe_dvd_x)
    have hcop_2t : Nat.Coprime P (2 ^ t) :=
      ((Nat.coprime_primes hPp Nat.prime_two).mpr (hS_odd P hP)).pow_right t
    exact hcop_we.mul_right hcop_2t
  have hx'_tot : Nat.totient x' = m := by
    calc
      Nat.totient x' = Nat.totient (∏ P ∈ S, P) * Nat.totient ((w / e) * 2 ^ t) :=
        Nat.totient_mul hcop_S_rhs
      _ = (∏ P ∈ S, (P - 1)) * (Nat.totient (w / e) * 2 ^ t) := by
        rw [totient_prod_primes (fun P hP => (hS_prime P hP).1), h2t_tot]
      _ = ((∏ P ∈ S, (P - 1)) * 2 ^ t) * Nat.totient (w / e) := by ring
      _ = (e * Nat.totient d) * Nat.totient (w / e) := by rw [hprod]
      _ = Nat.totient d * (Nat.totient (w / e) * e) := by ring
      _ = Nat.totient d * Nat.totient w := by rw [htot_w]
      _ = Nat.totient (d * w) := (Nat.totient_mul hcop).symm
      _ = m := by rw [hdw, hx_tot]
  have ⟨_, h5x'⟩ := ((k10_witness_iff m).mp hm).2 x' hx'_pos hx'_tot
  -- Yet 5 is coprime to x'!
  have hcop5_x' : Nat.Coprime 5 x' := by
    have hcop5_S : Nat.Coprime 5 (∏ P ∈ S, P) := by
      refine Nat.Coprime.prod_right fun P hP => ?_
      exact (Nat.coprime_primes (by norm_num) (hS_prime P hP).1).mpr (Ne.symm (hS_prime P hP).2)
    have hcop5_w : Nat.Coprime 5 w := hcop.coprime_dvd_left h5d
    have hcop5_we : Nat.Coprime 5 (w / e) := hcop5_w.coprime_dvd_right (Nat.div_dvd_of_dvd hedvd)
    have hcop5_2t : Nat.Coprime 5 (2 ^ t) := (by decide : Nat.Coprime 5 2).pow_right t
    exact hcop5_S.mul_right (hcop5_we.mul_right hcop5_2t)
  exact (by norm_num : ¬ (5 ∣ 1)) (hcop5_x'.gcd_eq_one ▸ Nat.dvd_gcd dvd_rfl h5x')

/-- **Lemma C for Prime `2` (`t3-descent-1.md`, §1)**:
Let `x > 0` be a preimage of a `k = 10` witness `m`. Suppose `d ∣ x`, `gcd(d, x/d) = 1`, `2 ∣ d`,
`e ∣ (x/d) / rad(x/d)`, `(¬ 5 ∣ d ∨ t = 0)`, and `(∏_{P ∈ S} (P - 1)) * 5 ^ t = e * φ(d)` for a
finite set `S` of odd primes (`P ≠ 2`). Then `∃ P ∈ S, P ∣ x`. -/
theorem k10_lemma_C_two {m x d e t : ℕ} {S : Finset ℕ}
    (hm : IsDivisibleTotientWitness 10 m)
    (hx_pos : 0 < x)
    (hx_tot : Nat.totient x = m)
    (hd : d ∣ x)
    (hcop : Nat.Coprime d (x / d))
    (h2d : 2 ∣ d)
    (he : e ∣ (x / d) / rad (x / d))
    (hguard : ¬ (5 ∣ d) ∨ t = 0)
    (hS_prime : ∀ P ∈ S, Nat.Prime P ∧ P ≠ 2)
    (hprod : (∏ P ∈ S, (P - 1)) * 5 ^ t = e * Nat.totient d) :
    ∃ P ∈ S, P ∣ x := by
  by_contra hall
  push Not at hall
  obtain ⟨_, h25x, _, _⟩ := k10_lemma_A hm hx_pos hx_tot
  set w := x / d
  have hdw : d * w = x := Nat.mul_div_cancel' hd
  have hw_pos : 0 < w := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, mul_zero] at hdw
    omega
  obtain ⟨hedvd, _, htot_w⟩ := totient_div_of_dvd_div_rad hw_pos he
  have hwe_pos : 0 < w / e := Nat.div_pos (Nat.le_of_dvd hw_pos hedvd)
    (Nat.pos_of_dvd_of_pos hedvd hw_pos)
  have hwe_dvd_x : w / e ∣ x := dvd_trans (Nat.div_dvd_of_dvd hedvd) (hdw ▸ dvd_mul_left w d)
  have h5t_tot : Nat.totient ((w / e) * 5 ^ t) = Nat.totient (w / e) * 5 ^ t := by
    rcases hguard with h5ndvd_d | rfl
    · have h25d_cop : Nat.Coprime 25 d := by
        have hcop5d : Nat.Coprime 5 d :=
          (by norm_num : Nat.Prime 5).coprime_iff_not_dvd.mpr h5ndvd_d
        have : (25 : ℕ) = 5 ^ 2 := by norm_num
        rw [this]
        exact hcop5d.pow_left 2
      have h25w : 25 ∣ w := h25d_cop.dvd_of_dvd_mul_left (hdw.symm ▸ h25x)
      have h5w : 5 ∣ w := dvd_trans (by norm_num : 5 ∣ 25) h25w
      have h5_mem : 5 ∈ w.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨by norm_num, h5w, Nat.ne_of_gt hw_pos⟩
      have h5_rad : 5 ∣ rad w := dvd_rad_of_mem_primeFactors h5_mem
      have hrad_dvd_we : rad w ∣ w / e := by
        rcases he with ⟨u, hu⟩
        have hw_eq : w = e * (u * rad w) := by
          calc
            w = w / rad w * rad w := (Nat.div_mul_cancel (rad_dvd_self w)).symm
            _ = (e * u) * rad w := by rw [hu]
            _ = e * (u * rad w) := by ring
        have he_pos : 0 < e := Nat.pos_of_dvd_of_pos hedvd hw_pos
        have hwe_eq : w / e = u * rad w := by
          conv_lhs => rw [hw_eq]
          exact Nat.mul_div_cancel_left _ he_pos
        rw [hwe_eq]
        exact dvd_mul_left (rad w) u
      have h5_we : 5 ∣ w / e := dvd_trans h5_rad hrad_dvd_we
      apply totient_mul_of_primes_dvd
      intro q hq hq5t
      have hq5 : q = 5 :=
        (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hq5t)
      rwa [hq5]
    · simp
  let x' := (∏ P ∈ S, P) * ((w / e) * 5 ^ t)
  have hx'_pos : 0 < x' := mul_pos
    (Finset.prod_pos fun P hP => (hS_prime P hP).1.pos)
    (mul_pos hwe_pos (pow_pos (by norm_num) t))
  have hcop_S_rhs : Nat.Coprime (∏ P ∈ S, P) ((w / e) * 5 ^ t) := by
    refine Nat.Coprime.prod_left fun P hP => ?_
    have hPp : Nat.Prime P := (hS_prime P hP).1
    have hcop_we : Nat.Coprime P (w / e) :=
      hPp.coprime_iff_not_dvd.mpr fun h => hall P hP (dvd_trans h hwe_dvd_x)
    have hcop_5t : Nat.Coprime P (5 ^ t) := by
      by_cases hP5 : P = 5
      · subst hP5
        -- Note if 5 ∈ S, 5 ∣ x, contradicting hall 5 hP!
        exact False.elim (hall 5 hP (dvd_trans (by norm_num : 5 ∣ 25) h25x))
      · exact ((Nat.coprime_primes hPp (by norm_num)).mpr hP5).pow_right t
    exact hcop_we.mul_right hcop_5t
  have hx'_tot : Nat.totient x' = m := by
    calc
      Nat.totient x' = Nat.totient (∏ P ∈ S, P) * Nat.totient ((w / e) * 5 ^ t) :=
        Nat.totient_mul hcop_S_rhs
      _ = (∏ P ∈ S, (P - 1)) * (Nat.totient (w / e) * 5 ^ t) := by
        rw [totient_prod_primes (fun P hP => (hS_prime P hP).1), h5t_tot]
      _ = ((∏ P ∈ S, (P - 1)) * 5 ^ t) * Nat.totient (w / e) := by ring
      _ = (e * Nat.totient d) * Nat.totient (w / e) := by rw [hprod]
      _ = Nat.totient d * (Nat.totient (w / e) * e) := by ring
      _ = Nat.totient d * Nat.totient w := by rw [htot_w]
      _ = Nat.totient (d * w) := (Nat.totient_mul hcop).symm
      _ = m := by rw [hdw, hx_tot]
  have ⟨h2x', _⟩ := ((k10_witness_iff m).mp hm).2 x' hx'_pos hx'_tot
  have hcop2_x' : Nat.Coprime 2 x' := by
    have hcop2_S : Nat.Coprime 2 (∏ P ∈ S, P) := by
      refine Nat.Coprime.prod_right fun P hP => ?_
      exact (Nat.coprime_primes Nat.prime_two (hS_prime P hP).1).mpr (Ne.symm (hS_prime P hP).2)
    have hcop2_w : Nat.Coprime 2 w := hcop.coprime_dvd_left h2d
    have hcop2_we : Nat.Coprime 2 (w / e) := hcop2_w.coprime_dvd_right (Nat.div_dvd_of_dvd hedvd)
    have hcop2_5t : Nat.Coprime 2 (5 ^ t) := (by decide : Nat.Coprime 2 5).pow_right t
    exact hcop2_S.mul_right (hcop2_we.mul_right hcop2_5t)
  exact (by norm_num : ¬ (2 ∣ 1)) (hcop2_x'.gcd_eq_one ▸ Nat.dvd_gcd dvd_rfl h2x')

/-- **Lemma B (`t3-1.md`, repaired `F17-A`)**: Prime-5 single-prime forcing rule (`S = {P}`).
Note: `rad(φ(d)) ∣ x` is kept in `t3-1.md` for uniform tracking of `P - 1`'s primes in the tree,
while `P ∣ x` itself already follows from `(P - 1) * 2 ^ t = e * φ(d)` and `(¬ 2 ∣ d ∨ t = 0)`. -/
theorem k10_lemma_B {m x d e t P : ℕ}
    (hm : IsDivisibleTotientWitness 10 m)
    (hx_pos : 0 < x)
    (hx_tot : Nat.totient x = m)
    (hd : d ∣ x)
    (hcop : Nat.Coprime d (x / d))
    (h5d : 5 ∣ d)
    (he : e ∣ (x / d) / rad (x / d))
    (hguard : ¬ (2 ∣ d) ∨ t = 0)
    (hP : Nat.Prime P)
    (hprod : (P - 1) * 2 ^ t = e * Nat.totient d) :
    P ∣ x := by
  by_cases hP5 : P = 5
  · subst hP5
    exact dvd_trans h5d hd
  · obtain ⟨Q, hQmem, hQdvd⟩ :=
      k10_lemma_C_five (S := {P}) hm hx_pos hx_tot hd hcop h5d he hguard
        (fun Q hQ => ⟨(Finset.mem_singleton.mp hQ) ▸ hP, (Finset.mem_singleton.mp hQ) ▸ hP5⟩)
        (by simpa using hprod)
    rwa [Finset.mem_singleton.mp hQmem] at hQdvd

/-- **Lemma B2 (`t3-1.md`, repaired `F17-A`)**: Prime-2 single-prime forcing rule (`S = {P}`). -/
theorem k10_lemma_B2 {m x d e t P : ℕ}
    (hm : IsDivisibleTotientWitness 10 m)
    (hx_pos : 0 < x)
    (hx_tot : Nat.totient x = m)
    (hd : d ∣ x)
    (hcop : Nat.Coprime d (x / d))
    (h2d : 2 ∣ d)
    (he : e ∣ (x / d) / rad (x / d))
    (hguard : ¬ (5 ∣ d) ∨ t = 0)
    (hP : Nat.Prime P)
    (hprod : (P - 1) * 5 ^ t = e * Nat.totient d) :
    P ∣ x := by
  by_cases hP2 : P = 2
  · subst hP2
    exact dvd_trans h2d hd
  · obtain ⟨Q, hQmem, hQdvd⟩ :=
      k10_lemma_C_two (S := {P}) hm hx_pos hx_tot hd hcop h2d he hguard
        (fun Q hQ => ⟨(Finset.mem_singleton.mp hQ) ▸ hP, (Finset.mem_singleton.mp hQ) ▸ hP2⟩)
        (by simpa using hprod)
    rwa [Finset.mem_singleton.mp hQmem] at hQdvd

/-- Helper: Round-1 prime-5 forcing from `ExactPowDvd 5 b x` (`2 ≤ b`) and `2 ^ a ∣ x` (`2 ≤ a`). -/
theorem k10_round1_five_force {m x a b i t P : ℕ}
    (hm : IsDivisibleTotientWitness 10 m)
    (hx_pos : 0 < x)
    (hx_tot : Nat.totient x = m)
    (ha : 2 ^ a ∣ x)
    (hb : ExactPowDvd 5 b x)
    (hb_ge2 : 2 ≤ b)
    (hi : i + 1 ≤ a)
    (hP : Nat.Prime P)
    (hprod : (P - 1) * 2 ^ t = 2 ^ i * (4 * 5 ^ (b - 1))) :
    P ∣ x := by
  have hcop5 : Nat.Coprime (5 ^ b) (x / 5 ^ b) :=
    coprime_div_of_exactPowDvd (by norm_num) hb
  have h5_dvd_5b : 5 ∣ 5 ^ b := dvd_pow_self 5 (by omega)
  have h2_ndvd_5b : ¬ (2 ∣ 5 ^ b) := by
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h
    norm_num at this
  set w := x / 5 ^ b
  have hdw : 5 ^ b * w = x := Nat.mul_div_cancel' hb.1
  have hw_pos : 0 < w := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, mul_zero] at hdw
    omega
  have h2a_w : 2 ^ a ∣ w := by
    have hcop_2a_5b : Nat.Coprime (2 ^ a) (5 ^ b) :=
      ((by decide : Nat.Coprime 2 5).pow_left a).pow_right b
    exact hcop_2a_5b.dvd_of_dvd_mul_left (hdw.symm ▸ ha)
  have h2i1_w : 2 ^ (i + 1) ∣ w := dvd_trans (Nat.pow_dvd_pow 2 hi) h2a_w
  have he : 2 ^ i ∣ w / rad w := prime_pow_dvd_div_rad hw_pos Nat.prime_two h2i1_w
  have htot_5b : Nat.totient (5 ^ b) = 4 * 5 ^ (b - 1) := by
    rw [Nat.totient_prime_pow (by norm_num : Nat.Prime 5) (by omega)]
    ring
  exact k10_lemma_B hm hx_pos hx_tot hb.1 hcop5 h5_dvd_5b he (Or.inl h2_ndvd_5b) hP
    (htot_5b ▸ hprod)

/-- Helper: Round-1 prime-2 forcing from `ExactPowDvd 2 a x` (`2 ≤ a`) and `5 ^ b ∣ x` (`2 ≤ b`). -/
theorem k10_round1_two_force {m x a b j t P : ℕ}
    (hm : IsDivisibleTotientWitness 10 m)
    (hx_pos : 0 < x)
    (hx_tot : Nat.totient x = m)
    (ha : ExactPowDvd 2 a x)
    (ha_ge2 : 2 ≤ a)
    (hb : 5 ^ b ∣ x)
    (hj : j + 1 ≤ b)
    (hP : Nat.Prime P)
    (hprod : (P - 1) * 5 ^ t = 5 ^ j * 2 ^ (a - 1)) :
    P ∣ x := by
  have hcop2 : Nat.Coprime (2 ^ a) (x / 2 ^ a) :=
    coprime_div_of_exactPowDvd Nat.prime_two ha
  have h2_dvd_2a : 2 ∣ 2 ^ a := dvd_pow_self 2 (by omega)
  have h5_ndvd_2a : ¬ (5 ∣ 2 ^ a) := by
    intro h
    have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) h
    norm_num at this
  set w := x / 2 ^ a
  have hdw : 2 ^ a * w = x := Nat.mul_div_cancel' ha.1
  have hw_pos : 0 < w := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, mul_zero] at hdw
    omega
  have h5b_w : 5 ^ b ∣ w := by
    have hcop_5b_2a : Nat.Coprime (5 ^ b) (2 ^ a) :=
      ((by decide : Nat.Coprime 5 2).pow_left b).pow_right a
    exact hcop_5b_2a.dvd_of_dvd_mul_left (hdw.symm ▸ hb)
  have h5j1_w : 5 ^ (j + 1) ∣ w := dvd_trans (Nat.pow_dvd_pow 5 hj) h5b_w
  have he : 5 ^ j ∣ w / rad w := prime_pow_dvd_div_rad hw_pos (by norm_num) h5j1_w
  have htot_2a : Nat.totient (2 ^ a) = 2 ^ (a - 1) := by
    rw [Nat.totient_prime_pow Nat.prime_two (by omega)]
    simp
  exact k10_lemma_B2 hm hx_pos hx_tot ha.1 hcop2 h2_dvd_2a he (Or.inl h5_ndvd_2a) hP
    (htot_2a ▸ hprod)

private theorem k10_totient_bound2 {m x e2 e5 : ℕ}
    (hm_pos : 0 < m) (hx_tot : Nat.totient x = m)
    (he2 : 1 ≤ e2) (he5 : 1 ≤ e5) (hd2 : 2 ^ e2 ∣ x) (hd5 : 5 ^ e5 ∣ x) :
    2 ^ (e2 - 1) * (5 ^ (e5 - 1) * 4) ≤ m := by
  have hcop : Nat.Coprime (2 ^ e2) (5 ^ e5) :=
    ((by decide : Nat.Coprime 2 5).pow_left e2).pow_right e5
  have hmul : 2 ^ e2 * 5 ^ e5 ∣ x := hcop.mul_dvd_of_dvd_of_dvd hd2 hd5
  have htot : Nat.totient (2 ^ e2 * 5 ^ e5) = 2 ^ (e2 - 1) * (5 ^ (e5 - 1) * 4) := by
    rw [Nat.totient_mul hcop, Nat.totient_prime_pow Nat.prime_two he2,
      Nat.totient_prime_pow (by norm_num) he5]
    ring
  exact htot ▸ Nat.le_of_dvd hm_pos (hx_tot ▸ Nat.totient_dvd_of_dvd hmul)

private theorem k10_totient_bound3 {m x e2 e5 p : ℕ}
    (hm_pos : 0 < m) (hx_tot : Nat.totient x = m)
    (he2 : 1 ≤ e2) (he5 : 1 ≤ e5) (hp : Nat.Prime p) (hp3 : 3 ≤ p) (hp5 : p ≠ 5)
    (hd2 : 2 ^ e2 ∣ x) (hd5 : 5 ^ e5 ∣ x) (hdp : p ∣ x) :
    2 ^ (e2 - 1) * (5 ^ (e5 - 1) * 4) * (p - 1) ≤ m := by
  have hcop25 : Nat.Coprime (2 ^ e2) (5 ^ e5) :=
    ((by decide : Nat.Coprime 2 5).pow_left e2).pow_right e5
  have hcop_p : Nat.Coprime (2 ^ e2 * 5 ^ e5) p := by
    have hc2 : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (by omega)
    have hc5 : Nat.Coprime 5 p := (Nat.coprime_primes (by norm_num) hp).mpr (Ne.symm hp5)
    exact (hc2.pow_left e2).mul_left (hc5.pow_left e5)
  have hmul : 2 ^ e2 * 5 ^ e5 * p ∣ x :=
    hcop_p.mul_dvd_of_dvd_of_dvd (hcop25.mul_dvd_of_dvd_of_dvd hd2 hd5) hdp
  have htot : Nat.totient (2 ^ e2 * 5 ^ e5 * p) =
      2 ^ (e2 - 1) * (5 ^ (e5 - 1) * 4) * (p - 1) := by
    rw [Nat.totient_mul hcop_p, Nat.totient_mul hcop25,
      Nat.totient_prime_pow Nat.prime_two he2,
      Nat.totient_prime_pow (by norm_num) he5, Nat.totient_prime hp]
    ring
  exact htot ▸ Nat.le_of_dvd hm_pos (hx_tot ▸ Nat.totient_dvd_of_dvd hmul)

private theorem k10_totient_bound4 {m x e2 e5 p q : ℕ}
    (hm_pos : 0 < m) (hx_tot : Nat.totient x = m)
    (he2 : 1 ≤ e2) (he5 : 1 ≤ e5) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hp3 : 3 ≤ p) (hq3 : 3 ≤ q) (hp5 : p ≠ 5) (hq5 : q ≠ 5) (hpq : p ≠ q)
    (hd2 : 2 ^ e2 ∣ x) (hd5 : 5 ^ e5 ∣ x) (hdp : p ∣ x) (hdq : q ∣ x) :
    2 ^ (e2 - 1) * (5 ^ (e5 - 1) * 4) * (p - 1) * (q - 1) ≤ m := by
  have hcop25 : Nat.Coprime (2 ^ e2) (5 ^ e5) :=
    ((by decide : Nat.Coprime 2 5).pow_left e2).pow_right e5
  have hcop_p : Nat.Coprime (2 ^ e2 * 5 ^ e5) p :=
    (((Nat.coprime_primes Nat.prime_two hp).mpr (by omega)).pow_left e2).mul_left
      (((Nat.coprime_primes (by norm_num) hp).mpr (Ne.symm hp5)).pow_left e5)
  have hcop_q : Nat.Coprime (2 ^ e2 * 5 ^ e5 * p) q :=
    ((((Nat.coprime_primes Nat.prime_two hq).mpr (by omega)).pow_left e2).mul_left
      (((Nat.coprime_primes (by norm_num) hq).mpr (Ne.symm hq5)).pow_left e5)).mul_left
      ((Nat.coprime_primes hp hq).mpr hpq)
  have hmul : 2 ^ e2 * 5 ^ e5 * p * q ∣ x :=
    hcop_q.mul_dvd_of_dvd_of_dvd
      (hcop_p.mul_dvd_of_dvd_of_dvd (hcop25.mul_dvd_of_dvd_of_dvd hd2 hd5) hdp) hdq
  have htot : Nat.totient (2 ^ e2 * 5 ^ e5 * p * q) =
      2 ^ (e2 - 1) * (5 ^ (e5 - 1) * 4) * (p - 1) * (q - 1) := by
    rw [Nat.totient_mul hcop_q, Nat.totient_mul hcop_p, Nat.totient_mul hcop25,
      Nat.totient_prime_pow Nat.prime_two he2, Nat.totient_prime_pow (by norm_num) he5,
      Nat.totient_prime hp, Nat.totient_prime hq]
    ring
  exact htot ▸ Nat.le_of_dvd hm_pos (hx_tot ▸ Nat.totient_dvd_of_dvd hmul)

/-- **Proposition 3 (`t3-forcing-1.md`)**: Every `k = 10` witness satisfies `32000 ≤ m`
unconditionally from Round 1 forcing alone. -/
theorem k10_witness_ge_32000 {m : ℕ} (hm : IsDivisibleTotientWitness 10 m) :
    32000 ≤ m := by
  rcases hm.1 with ⟨x, hx_pos, hx_tot⟩
  obtain ⟨h4x, h25x, _, _⟩ := k10_lemma_A hm hx_pos hx_tot
  have hx_ne : x ≠ 0 := Nat.ne_of_gt hx_pos
  have hm_pos : 0 < m := hx_tot ▸ Nat.totient_pos.mpr hx_pos
  generalize ha_def : x.factorization 2 = a
  generalize hb_def : x.factorization 5 = b
  have ha_exact : ExactPowDvd 2 a x := ha_def ▸ exactPowDvd_factorization Nat.prime_two hx_pos
  have hb_exact : ExactPowDvd 5 b x := hb_def ▸ exactPowDvd_factorization (by norm_num) hx_pos
  have ha_ge2 : 2 ≤ a := by
    have h4 : 2 ^ 2 ∣ x := by simpa using h4x
    have hle := (Nat.factorization_le_iff_dvd (by norm_num) hx_ne).mpr h4 2
    rw [Nat.factorization_pow, Finsupp.smul_apply, Nat.prime_two.factorization_self, ha_def] at hle
    simpa using hle
  have hb_ge2 : 2 ≤ b := by
    have h25 : 5 ^ 2 ∣ x := by simpa using h25x
    have hle := (Nat.factorization_le_iff_dvd (by norm_num) hx_ne).mpr h25 5
    rw [Nat.factorization_pow, Finsupp.smul_apply,
      (by norm_num : Nat.Prime 5).factorization_self, hb_def] at hle
    simpa using hle
  clear ha_def hb_def
  by_cases hb7 : 7 ≤ b
  · have h57 : 5 ^ 7 ∣ x := dvd_trans (Nat.pow_dvd_pow 5 hb7) hb_exact.1
    have hle := k10_totient_bound2 hm_pos hx_tot (by decide) (by decide) (show 2 ^ 2 ∣ x from h4x) h57
    exact le_trans (by norm_num) hle
  · have hb_cases : b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 := by
      clear h4x h25x ha_exact hb_exact
      omega
    rcases hb_cases with rfl | rfl | rfl | rfl | rfl
    · -- b = 2
      have hi0 : 0 + 1 ≤ a := le_trans (by decide : 1 ≤ 2) ha_ge2
      have hi1 : 1 + 1 ≤ a := ha_ge2
      have h11 : 11 ∣ x := k10_round1_five_force (i := 0) (t := 1) hm hx_pos hx_tot
        ha_exact.1 hb_exact (by decide) hi0 (by norm_num) (by norm_num)
      have h41 : 41 ∣ x := k10_round1_five_force (i := 1) (t := 0) hm hx_pos hx_tot
        ha_exact.1 hb_exact (by decide) hi1 (by norm_num) (by norm_num)
      by_cases ha3 : 3 ≤ a
      · have h23 : 2 ^ 3 ∣ x := dvd_trans (Nat.pow_dvd_pow 2 ha3) ha_exact.1
        have hle := k10_totient_bound4 hm_pos hx_tot (by decide) (by decide) (by norm_num)
          (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide)
          h23 hb_exact.1 h11 h41
        exact le_trans (by norm_num) hle
      · have ha2 : a = 2 := le_antisymm (Nat.le_of_lt_succ (Nat.lt_of_not_ge ha3)) ha_ge2
        subst ha2
        have h3 : 3 ∣ x := k10_round1_two_force (j := 0) (t := 0) hm hx_pos hx_tot
          ha_exact (by decide) hb_exact.1 (by decide) Nat.prime_three (by norm_num)
        have hc25 : Nat.Coprime (2 ^ 2) (5 ^ 2) :=
          ((by decide : Nat.Coprime 2 5).pow_left 2).pow_right 2
        have hc3 : Nat.Coprime (2 ^ 2 * 5 ^ 2) 3 :=
          (((by decide : Nat.Coprime 2 3).pow_left 2).mul_left
            ((by decide : Nat.Coprime 5 3).pow_left 2))
        have hc11 : Nat.Coprime (2 ^ 2 * 5 ^ 2 * 3) 11 :=
          ((((by decide : Nat.Coprime 2 11).pow_left 2).mul_left
            ((by decide : Nat.Coprime 5 11).pow_left 2)).mul_left
            (by decide : Nat.Coprime 3 11))
        have hc41 : Nat.Coprime (2 ^ 2 * 5 ^ 2 * 3 * 11) 41 :=
          (((((by decide : Nat.Coprime 2 41).pow_left 2).mul_left
            ((by decide : Nat.Coprime 5 41).pow_left 2)).mul_left
            (by decide : Nat.Coprime 3 41)).mul_left
            (by decide : Nat.Coprime 11 41))
        have hmul : 2 ^ 2 * 5 ^ 2 * 3 * 11 * 41 ∣ x :=
          hc41.mul_dvd_of_dvd_of_dvd (hc11.mul_dvd_of_dvd_of_dvd
            (hc3.mul_dvd_of_dvd_of_dvd
              (hc25.mul_dvd_of_dvd_of_dvd ha_exact.1 hb_exact.1) h3) h11) h41
        have htot : Nat.totient (2 ^ 2 * 5 ^ 2 * 3 * 11 * 41) = 32000 := by
          rw [Nat.totient_mul hc41, Nat.totient_mul hc11, Nat.totient_mul hc3,
            Nat.totient_mul hc25,
            Nat.totient_prime_pow Nat.prime_two (by norm_num),
            Nat.totient_prime_pow (by norm_num : Nat.Prime 5) (by norm_num),
            Nat.totient_prime Nat.prime_three,
            Nat.totient_prime (by norm_num : Nat.Prime 11),
            Nat.totient_prime (by norm_num : Nat.Prime 41)]
          norm_num
        exact htot ▸ Nat.le_of_dvd hm_pos (hx_tot ▸ Nat.totient_dvd_of_dvd hmul)
    · -- b = 3
      have hi0 : 0 + 1 ≤ a := le_trans (by decide : 1 ≤ 2) ha_ge2
      have h101 : 101 ∣ x := k10_round1_five_force (i := 0) (t := 0) hm hx_pos hx_tot
        ha_exact.1 hb_exact (by decide) hi0 (by norm_num) (by norm_num)
      by_cases ha3 : 3 ≤ a
      · have h23 : 2 ^ 3 ∣ x := dvd_trans (Nat.pow_dvd_pow 2 ha3) ha_exact.1
        have hle := k10_totient_bound3 hm_pos hx_tot (by decide) (by decide) (by norm_num)
          (by decide) (by decide) h23 hb_exact.1 h101
        exact le_trans (by norm_num) hle
      · have ha2 : a = 2 := le_antisymm (Nat.le_of_lt_succ (Nat.lt_of_not_ge ha3)) ha_ge2
        subst ha2
        have h3 : 3 ∣ x := k10_round1_two_force (j := 0) (t := 0) hm hx_pos hx_tot
          ha_exact (by decide) hb_exact.1 (by decide) Nat.prime_three (by norm_num)
        have hle := k10_totient_bound4 hm_pos hx_tot (by decide) (by decide) Nat.prime_three
          (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide)
          ha_exact.1 hb_exact.1 h3 h101
        exact le_trans (by norm_num) hle
    · -- b = 4
      have hi0 : 0 + 1 ≤ a := le_trans (by decide : 1 ≤ 2) ha_ge2
      have h251 : 251 ∣ x := k10_round1_five_force (i := 0) (t := 1) hm hx_pos hx_tot
        ha_exact.1 hb_exact (by decide) hi0 (by norm_num) (by norm_num)
      have hle := k10_totient_bound3 hm_pos hx_tot (by decide) (by decide) (by norm_num)
        (by decide) (by decide) (show 2 ^ 2 ∣ x from h4x) hb_exact.1 h251
      exact le_trans (by norm_num) hle
    · -- b = 5
      by_cases ha5 : 5 ≤ a
      · have h25p : 2 ^ 5 ∣ x := dvd_trans (Nat.pow_dvd_pow 2 ha5) ha_exact.1
        have hle := k10_totient_bound2 hm_pos hx_tot (by decide) (by decide) h25p hb_exact.1
        exact le_trans (by norm_num) hle
      · have ha_cases : a = 2 ∨ a = 3 ∨ a = 4 := by
          clear h4x h25x ha_exact hb_exact
          omega
        rcases ha_cases with rfl | rfl | rfl
        · have h3 : 3 ∣ x := k10_round1_two_force (j := 0) (t := 0) hm hx_pos hx_tot
            ha_exact (by decide) hb_exact.1 (by decide) Nat.prime_three (by norm_num)
          have h11 : 11 ∣ x := k10_round1_two_force (j := 1) (t := 0) hm hx_pos hx_tot
            ha_exact (by decide) hb_exact.1 (by decide) (by norm_num) (by norm_num)
          have hle := k10_totient_bound4 hm_pos hx_tot (by decide) (by decide) Nat.prime_three
            (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide)
            ha_exact.1 hb_exact.1 h3 h11
          exact le_trans (by norm_num) hle
        · have h101 : 101 ∣ x := k10_round1_two_force (j := 2) (t := 0) hm hx_pos hx_tot
            ha_exact (by decide) hb_exact.1 (by decide) (by norm_num) (by norm_num)
          have hle := k10_totient_bound3 hm_pos hx_tot (by decide) (by decide) (by norm_num)
            (by decide) (by decide) ha_exact.1 hb_exact.1 h101
          exact le_trans (by norm_num) hle
        · have h41 : 41 ∣ x := k10_round1_two_force (j := 1) (t := 0) hm hx_pos hx_tot
            ha_exact (by decide) hb_exact.1 (by decide) (by norm_num) (by norm_num)
          have hle := k10_totient_bound3 hm_pos hx_tot (by decide) (by decide) (by norm_num)
            (by decide) (by decide) ha_exact.1 hb_exact.1 h41
          exact le_trans (by norm_num) hle
    · -- b = 6
      by_cases ha3 : 3 ≤ a
      · have h23 : 2 ^ 3 ∣ x := dvd_trans (Nat.pow_dvd_pow 2 ha3) ha_exact.1
        have hle := k10_totient_bound2 hm_pos hx_tot (by decide) (by decide) h23 hb_exact.1
        exact le_trans (by norm_num) hle
      · have ha2 : a = 2 := le_antisymm (Nat.le_of_lt_succ (Nat.lt_of_not_ge ha3)) ha_ge2
        subst ha2
        have h3 : 3 ∣ x := k10_round1_two_force (j := 0) (t := 0) hm hx_pos hx_tot
          ha_exact (by decide) hb_exact.1 (by decide) Nat.prime_three (by norm_num)
        have hle := k10_totient_bound3 hm_pos hx_tot (by decide) (by decide) Nat.prime_three
          (by decide) (by decide) ha_exact.1 hb_exact.1 h3
        exact le_trans (by norm_num) hle

/-! ### `K10DescentTree` and `K10RungCertificate` Soundness (`K = 30, 50, 60` Bridge) -/

/-- Exact root condition of `descent_check.py`'s `roots(K)`:
`2 ≤ a ∧ 2 ≤ b ∧ 2 ^ (a + 1) * 5 ^ (b - 1) < 10 ^ K`. -/
def isK10Root (K a b : ℕ) : Prop :=
  2 ≤ a ∧ 2 ≤ b ∧ 2 ^ (a + 1) * 5 ^ (b - 1) < 10 ^ K

/-- Any valuation pair `(a, b)` with `2 ≤ a, 2 ≤ b` outside `roots(K)` already forces
`10 ^ K ≤ φ(2 ^ a * 5 ^ b) ≤ φ(x)`. -/
theorem k10_nonroot_closed {K a b x : ℕ}
    (hx_pos : 0 < x)
    (ha : 2 ≤ a)
    (hb : 2 ≤ b)
    (h2a : 2 ^ a ∣ x)
    (h5b : 5 ^ b ∣ x)
    (hnonroot : ¬ isK10Root K a b) :
    10 ^ K ≤ Nat.totient x := by
  have hge : 10 ^ K ≤ 2 ^ (a + 1) * 5 ^ (b - 1) := by
    unfold isK10Root at hnonroot
    omega
  have hcop : Nat.Coprime (2 ^ a) (5 ^ b) :=
    ((by decide : Nat.Coprime 2 5).pow_left a).pow_right b
  have hdvd : 2 ^ a * 5 ^ b ∣ x := hcop.mul_dvd_of_dvd_of_dvd h2a h5b
  have htot_eq : Nat.totient (2 ^ a * 5 ^ b) = 2 ^ (a + 1) * 5 ^ (b - 1) := by
    rw [Nat.totient_mul hcop, Nat.totient_prime_pow Nat.prime_two (by omega),
      Nat.totient_prime_pow (by norm_num : Nat.Prime 5) (by omega)]
    have ha_eq : 2 ^ (a - 1) * (2 - 1) * (5 ^ (b - 1) * (5 - 1)) =
        (2 ^ (a - 1) * 4) * 5 ^ (b - 1) := by ring
    rw [ha_eq]
    congr 1
    have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [h4, ← pow_add]
    congr 1
    omega
  have htot_pos : 0 < Nat.totient x := Nat.totient_pos.mpr hx_pos
  exact le_trans hge (htot_eq ▸ Nat.le_of_dvd htot_pos (Nat.totient_dvd_of_dvd hdvd))

/-- Inductive `k = 10` descent tree matching `descent_check.py`:
tracks known prime-power constraints `st`, applies Lemma B, Lemma B2, binary power splits
(`p ^ k ∥ x` vs `p ^ (k + 1) ∣ x`), and Lemma C product splits, closing each leaf once
`10 ^ K ≤ ∏_{p ∈ P} p ^ (exp p - 1) * (p - 1) = φ(∏_{p ∈ P} p ^ exp p)`. -/
inductive K10DescentTree : List ValConstraint → ℕ → Prop
  | closed (st : List ValConstraint) (K : ℕ) (P : Finset ℕ) (exp : ℕ → ℕ) :
      (∀ p ∈ P, 1 ≤ exp p ∧ ∃ exact, (⟨p, exp p, exact⟩ : ValConstraint) ∈ st) →
      10 ^ K ≤ (∏ p ∈ P, p ^ (exp p - 1) * (p - 1)) →
      K10DescentTree st K
  | forceFive (st : List ValConstraint) (K : ℕ) (D : Finset ℕ) (exp : ℕ → ℕ) (e t P : ℕ) :
      5 ∈ D →
      (∀ q ∈ D, 1 ≤ exp q ∧ (⟨q, exp q, true⟩ : ValConstraint) ∈ st) →
      (2 ∉ D ∨ t = 0) →
      (∀ m x : ℕ, IsDivisibleTotientWitness 10 m → 0 < x → Nat.totient x = m →
        (∀ c ∈ st, c.holds x) →
          let d := ∏ q ∈ D, q ^ exp q
          e ∣ (x / d) / rad (x / d)) →
      Nat.Prime P →
      (P - 1) * 2 ^ t = e * Nat.totient (∏ q ∈ D, q ^ exp q) →
      K10DescentTree (⟨P, 1, false⟩ :: st) K →
      K10DescentTree st K
  | forceTwo (st : List ValConstraint) (K : ℕ) (D : Finset ℕ) (exp : ℕ → ℕ) (e t P : ℕ) :
      2 ∈ D →
      (∀ q ∈ D, 1 ≤ exp q ∧ (⟨q, exp q, true⟩ : ValConstraint) ∈ st) →
      (5 ∉ D ∨ t = 0) →
      (∀ m x : ℕ, IsDivisibleTotientWitness 10 m → 0 < x → Nat.totient x = m →
        (∀ c ∈ st, c.holds x) →
          let d := ∏ q ∈ D, q ^ exp q
          e ∣ (x / d) / rad (x / d)) →
      Nat.Prime P →
      (P - 1) * 5 ^ t = e * Nat.totient (∏ q ∈ D, q ^ exp q) →
      K10DescentTree (⟨P, 1, false⟩ :: st) K →
      K10DescentTree st K
  | powerSplit (st : List ValConstraint) (K p k : ℕ) :
      (⟨p, k, false⟩ : ValConstraint) ∈ st →
      K10DescentTree (⟨p, k, true⟩ :: st) K →
      K10DescentTree (⟨p, k + 1, false⟩ :: st) K →
      K10DescentTree st K
  | lemmaCFive (st : List ValConstraint) (K : ℕ) (D : Finset ℕ) (exp : ℕ → ℕ)
      (e t : ℕ) (S : Finset ℕ) :
      5 ∈ D →
      (∀ q ∈ D, 1 ≤ exp q ∧ (⟨q, exp q, true⟩ : ValConstraint) ∈ st) →
      (2 ∉ D ∨ t = 0) →
      (∀ m x : ℕ, IsDivisibleTotientWitness 10 m → 0 < x → Nat.totient x = m →
        (∀ c ∈ st, c.holds x) →
          let d := ∏ q ∈ D, q ^ exp q
          e ∣ (x / d) / rad (x / d)) →
      (∀ P ∈ S, Nat.Prime P ∧ P ≠ 5) →
      (∏ P ∈ S, (P - 1)) * 2 ^ t = e * Nat.totient (∏ q ∈ D, q ^ exp q) →
      (∀ P ∈ S, K10DescentTree (⟨P, 1, false⟩ :: st) K) →
      K10DescentTree st K
  | lemmaCTwo (st : List ValConstraint) (K : ℕ) (D : Finset ℕ) (exp : ℕ → ℕ)
      (e t : ℕ) (S : Finset ℕ) :
      2 ∈ D →
      (∀ q ∈ D, 1 ≤ exp q ∧ (⟨q, exp q, true⟩ : ValConstraint) ∈ st) →
      (5 ∉ D ∨ t = 0) →
      (∀ m x : ℕ, IsDivisibleTotientWitness 10 m → 0 < x → Nat.totient x = m →
        (∀ c ∈ st, c.holds x) →
          let d := ∏ q ∈ D, q ^ exp q
          e ∣ (x / d) / rad (x / d)) →
      (∀ P ∈ S, Nat.Prime P ∧ P ≠ 2) →
      (∏ P ∈ S, (P - 1)) * 5 ^ t = e * Nat.totient (∏ q ∈ D, q ^ exp q) →
      (∀ P ∈ S, K10DescentTree (⟨P, 1, false⟩ :: st) K) →
      K10DescentTree st K

/-- Helper: totient of `∏ p ∈ P, p ^ exp p` for primes with `1 ≤ exp p`. -/
private theorem totient_prod_prime_pows {P : Finset ℕ} {exp : ℕ → ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p ∧ 1 ≤ exp p) :
    Nat.totient (∏ p ∈ P, p ^ exp p) = ∏ p ∈ P, p ^ (exp p - 1) * (p - 1) := by
  induction P using Finset.induction_on with
  | empty => simp
  | insert p s hps ih =>
    rw [Finset.prod_insert hps, Finset.prod_insert hps]
    have hp := hP p (Finset.mem_insert_self p s)
    have hs : ∀ q ∈ s, Nat.Prime q ∧ 1 ≤ exp q :=
      fun q hq => hP q (Finset.mem_insert_of_mem hq)
    have hcop : Nat.Coprime (p ^ exp p) (∏ q ∈ s, q ^ exp q) := by
      refine (Nat.Coprime.prod_right fun q hq => ?_).pow_left (exp p)
      exact ((Nat.coprime_primes hp.1 (hs q hq).1).mpr (fun h => hps (h ▸ hq))).pow_right (exp q)
    rw [Nat.totient_mul hcop, Nat.totient_prime_pow hp.1 hp.2, ih hs]

/-- Helper: if prime `r ∉ D` while every `q ∈ D` is prime, then `¬ r ∣ ∏ q ∈ D, q ^ exp q`. -/
private theorem prime_not_dvd_prod_of_notMem {D : Finset ℕ} {exp : ℕ → ℕ} {r : ℕ}
    (hr : Nat.Prime r) (hD : ∀ q ∈ D, Nat.Prime q) (hnot : r ∉ D) :
    ¬ (r ∣ ∏ q ∈ D, q ^ exp q) := by
  have hcop : Nat.Coprime r (∏ q ∈ D, q ^ exp q) := by
    refine Nat.Coprime.prod_right fun q hq => ?_
    exact ((Nat.coprime_primes hr (hD q hq)).mpr (fun h => hnot (h ▸ hq))).pow_right (exp q)
  exact hr.coprime_iff_not_dvd.mp hcop

/-- **Soundness of `K10DescentTree`**:
Every valid closed `K10DescentTree` at a satisfied node `st` proves `10 ^ K ≤ m` for any
`k = 10` witness `m = φ(x)`. -/
theorem k10DescentTree_sound {st : List ValConstraint} {K m x : ℕ}
    (hm : IsDivisibleTotientWitness 10 m)
    (hx_pos : 0 < x)
    (hx_tot : Nat.totient x = m)
    (htree : K10DescentTree st K)
    (hst : ∀ c ∈ st, c.holds x) :
    10 ^ K ≤ m := by
  have hm_pos : 0 < m := hx_tot ▸ Nat.totient_pos.mpr hx_pos
  induction htree with
  | closed st K P exp hmem hKle =>
    have hP_prime : ∀ p ∈ P, Nat.Prime p ∧ 1 ≤ exp p := by
      intro p hp
      obtain ⟨hexp1, ex, hm_st⟩ := hmem p hp
      exact ⟨(hst _ hm_st).1, hexp1⟩
    have hdvd : (∏ p ∈ P, p ^ exp p) ∣ x := by
      apply finset_prod_dvd_of_nat_coprime
      · intro p hp q hq hpq
        exact ((Nat.coprime_primes (hP_prime p hp).1 (hP_prime q hq).1).mpr hpq).pow (exp p) (exp q)
      · intro p hp
        obtain ⟨_, ex, hm_st⟩ := hmem p hp
        exact ValConstraint.pow_dvd_of_holds (hst _ hm_st)
    have htot_dvd : Nat.totient (∏ p ∈ P, p ^ exp p) ∣ m :=
      hx_tot ▸ Nat.totient_dvd_of_dvd hdvd
    rw [totient_prod_prime_pows hP_prime] at htot_dvd
    exact le_trans hKle (Nat.le_of_dvd hm_pos htot_dvd)
  | forceFive st K D exp e t P h5D hD hguard_D hside hP hprod _ ih =>
    have hD_exact : ∀ q ∈ D, Nat.Prime q ∧ ExactPowDvd q (exp q) x := by
      intro q hq
      have hc := hst _ (hD q hq).2
      exact ⟨hc.1, by simpa [ValConstraint.holds] using hc.2⟩
    obtain ⟨hd_dvd, hd_cop⟩ := unitary_of_exactPowDvd_finset hD_exact
    have h5d : 5 ∣ ∏ q ∈ D, q ^ exp q :=
      dvd_trans (dvd_pow_self 5 (by have := (hD 5 h5D).1; omega))
        (Finset.dvd_prod_of_mem (fun q => q ^ exp q) h5D)
    have hguard : ¬ (2 ∣ ∏ q ∈ D, q ^ exp q) ∨ t = 0 :=
      hguard_D.imp_left fun h2not =>
        prime_not_dvd_prod_of_notMem Nat.prime_two (fun q hq => (hD_exact q hq).1) h2not
    have he := hside m x hm hx_pos hx_tot hst
    have hPdvd := k10_lemma_B hm hx_pos hx_tot hd_dvd hd_cop h5d he hguard hP hprod
    apply ih
    intro c hc
    rcases List.mem_cons.mp hc with rfl | htail
    · exact ⟨hP, by simpa using hPdvd⟩
    · exact hst c htail
  | forceTwo st K D exp e t P h2D hD hguard_D hside hP hprod _ ih =>
    have hD_exact : ∀ q ∈ D, Nat.Prime q ∧ ExactPowDvd q (exp q) x := by
      intro q hq
      have hc := hst _ (hD q hq).2
      exact ⟨hc.1, by simpa [ValConstraint.holds] using hc.2⟩
    obtain ⟨hd_dvd, hd_cop⟩ := unitary_of_exactPowDvd_finset hD_exact
    have h2d : 2 ∣ ∏ q ∈ D, q ^ exp q :=
      dvd_trans (dvd_pow_self 2 (by have := (hD 2 h2D).1; omega))
        (Finset.dvd_prod_of_mem (fun q => q ^ exp q) h2D)
    have hguard : ¬ (5 ∣ ∏ q ∈ D, q ^ exp q) ∨ t = 0 :=
      hguard_D.imp_left fun h5not =>
        prime_not_dvd_prod_of_notMem (by norm_num) (fun q hq => (hD_exact q hq).1) h5not
    have he := hside m x hm hx_pos hx_tot hst
    have hPdvd := k10_lemma_B2 hm hx_pos hx_tot hd_dvd hd_cop h2d he hguard hP hprod
    apply ih
    intro c hc
    rcases List.mem_cons.mp hc with rfl | htail
    · exact ⟨hP, by simpa using hPdvd⟩
    · exact hst c htail
  | powerSplit st K p k hmem _ _ ihExact ihSucc =>
    have hc := hst _ hmem
    have hpk : p ^ k ∣ x := ValConstraint.pow_dvd_of_holds hc
    rcases exactPowDvd_or_succ_pow_dvd hpk with hexact | hsucc
    · apply ihExact
      intro c hc'
      rcases List.mem_cons.mp hc' with rfl | htail
      · exact ⟨hc.1, hexact⟩
      · exact hst c htail
    · apply ihSucc
      intro c hc'
      rcases List.mem_cons.mp hc' with rfl | htail
      · exact ⟨hc.1, hsucc⟩
      · exact hst c htail
  | lemmaCFive st K D exp e t S h5D hD hguard_D hside hSprime hprod _ ih =>
    have hD_exact : ∀ q ∈ D, Nat.Prime q ∧ ExactPowDvd q (exp q) x := by
      intro q hq
      have hc := hst _ (hD q hq).2
      exact ⟨hc.1, by simpa [ValConstraint.holds] using hc.2⟩
    obtain ⟨hd_dvd, hd_cop⟩ := unitary_of_exactPowDvd_finset hD_exact
    have h5d : 5 ∣ ∏ q ∈ D, q ^ exp q :=
      dvd_trans (dvd_pow_self 5 (by have := (hD 5 h5D).1; omega))
        (Finset.dvd_prod_of_mem (fun q => q ^ exp q) h5D)
    have hguard : ¬ (2 ∣ ∏ q ∈ D, q ^ exp q) ∨ t = 0 :=
      hguard_D.imp_left fun h2not =>
        prime_not_dvd_prod_of_notMem Nat.prime_two (fun q hq => (hD_exact q hq).1) h2not
    have he := hside m x hm hx_pos hx_tot hst
    obtain ⟨P, hPS, hPdvd⟩ :=
      k10_lemma_C_five hm hx_pos hx_tot hd_dvd hd_cop h5d he hguard hSprime hprod
    apply ih P hPS
    intro c hc
    rcases List.mem_cons.mp hc with rfl | htail
    · exact ⟨(hSprime P hPS).1, by simpa using hPdvd⟩
    · exact hst c htail
  | lemmaCTwo st K D exp e t S h2D hD hguard_D hside hSprime hprod _ ih =>
    have hD_exact : ∀ q ∈ D, Nat.Prime q ∧ ExactPowDvd q (exp q) x := by
      intro q hq
      have hc := hst _ (hD q hq).2
      exact ⟨hc.1, by simpa [ValConstraint.holds] using hc.2⟩
    obtain ⟨hd_dvd, hd_cop⟩ := unitary_of_exactPowDvd_finset hD_exact
    have h2d : 2 ∣ ∏ q ∈ D, q ^ exp q :=
      dvd_trans (dvd_pow_self 2 (by have := (hD 2 h2D).1; omega))
        (Finset.dvd_prod_of_mem (fun q => q ^ exp q) h2D)
    have hguard : ¬ (5 ∣ ∏ q ∈ D, q ^ exp q) ∨ t = 0 :=
      hguard_D.imp_left fun h5not =>
        prime_not_dvd_prod_of_notMem (by norm_num) (fun q hq => (hD_exact q hq).1) h5not
    have he := hside m x hm hx_pos hx_tot hst
    obtain ⟨P, hPS, hPdvd⟩ :=
      k10_lemma_C_two hm hx_pos hx_tot hd_dvd hd_cop h2d he hguard hSprime hprod
    apply ih P hPS
    intro c hc
    rcases List.mem_cons.mp hc with rfl | htail
    · exact ⟨(hSprime P hPS).1, by simpa using hPdvd⟩
    · exact hst c htail

/-- Full rung certificate structure modeling `descent_check.py` (at `K = 30`, `K = 50` with
5,681 roots, and `K = 60` with 8,243 roots): provides a closed `K10DescentTree` for every root
`(a, b)` satisfying `isK10Root K a b`. -/
structure K10RungCertificate (K : ℕ) : Prop where
  trees : ∀ a b : ℕ, isK10Root K a b →
    K10DescentTree [⟨2, a, true⟩, ⟨5, b, true⟩] K

/-- **Full Soundness & Root-Completeness Bridge for `t3-descent-1/2/3` (`K = 30, 50, 60`)**:
Any valid `K10RungCertificate K` unconditionally forces `10 ^ K ≤ m` for every `k = 10`
witness `m`. -/
theorem k10_bound_from_rung_certificate {K : ℕ} (cert : K10RungCertificate K) {m : ℕ}
    (hm : IsDivisibleTotientWitness 10 m) :
    10 ^ K ≤ m := by
  rcases hm.1 with ⟨x, hx_pos, hx_tot⟩
  obtain ⟨h4x, h25x, _, _⟩ := k10_lemma_A hm hx_pos hx_tot
  have hx_ne : x ≠ 0 := Nat.ne_of_gt hx_pos
  let a := x.factorization 2
  let b := x.factorization 5
  have ha_exact : ExactPowDvd 2 a x := exactPowDvd_factorization Nat.prime_two hx_pos
  have hb_exact : ExactPowDvd 5 b x := exactPowDvd_factorization (by norm_num) hx_pos
  have ha_ge2 : 2 ≤ a := by
    have h4 : 2 ^ 2 ∣ x := by simpa using h4x
    have hle := (Nat.factorization_le_iff_dvd (by norm_num) hx_ne).mpr h4 2
    rw [Nat.factorization_pow, Finsupp.smul_apply, Nat.prime_two.factorization_self] at hle
    simpa using hle
  have hb_ge2 : 2 ≤ b := by
    have h25 : 5 ^ 2 ∣ x := by simpa using h25x
    have hle := (Nat.factorization_le_iff_dvd (by norm_num) hx_ne).mpr h25 5
    rw [Nat.factorization_pow, Finsupp.smul_apply,
      (by norm_num : Nat.Prime 5).factorization_self] at hle
    simpa using hle
  by_cases hroot : isK10Root K a b
  · refine k10DescentTree_sound hm hx_pos hx_tot (cert.trees a b hroot) ?_
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨Nat.prime_two, ha_exact⟩
    · exact ⟨by norm_num, hb_exact⟩
  · exact hx_tot ▸ k10_nonroot_closed hx_pos ha_ge2 hb_ge2 ha_exact.1 hb_exact.1 hroot

/-- Concrete unconditional instantiation `K10RungCertificate 4` inside the Lean 4 kernel,
witnessing non-vacuity of `K10RungCertificate` and `k10_bound_from_rung_certificate` across all
roots `(a, b)` of `K = 4` (`2 ^ (a + 1) * 5 ^ (b - 1) < 10000`). -/
theorem k10RungCertificate_4 : K10RungCertificate 4 where
  trees a b hroot := by
    obtain ⟨ha2, hb2, hlt⟩ := hroot
    have hb_lt6 : b < 6 := by
      by_contra hb6
      have h5 : 5 ^ 5 ≤ 5 ^ (b - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : 2 ^ 3 ≤ 2 ^ (a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hmul : 2 ^ 3 * 5 ^ 5 ≤ 2 ^ (a + 1) * 5 ^ (b - 1) := Nat.mul_le_mul h2 h5
      norm_num at hmul hlt
      omega
    interval_cases b
    · -- b = 2: force 11 (e = 1, t = 1) then 41 (e = 2, t = 0), closing at {2, 5, 11, 41}.
      refine K10DescentTree.forceFive _ 4 {5} (fun _ => 2) 1 1 11
        (by simp) (by intro q hq; simp at hq; subst hq; simp)
        (Or.inl (by simp)) (fun _ _ _ _ _ _ => one_dvd _) (by norm_num) (by decide) ?_
      refine K10DescentTree.forceFive _ 4 {5} (fun _ => 2) 2 0 41
        (by simp) (by intro q hq; simp at hq; subst hq; simp)
        (Or.inr rfl)
        (by
          intro m x _ hx_pos _ hst
          simp only [Finset.prod_singleton]
          have h2c := hst ⟨2, a, true⟩ (by simp)
          have h5c := hst ⟨5, 2, true⟩ (by simp)
          have h2a : 2 ^ a ∣ x := h2c.2.1
          have h52 : 5 ^ 2 ∣ x := h5c.2.1
          have hdw : 25 * (x / 25) = x := Nat.mul_div_cancel' (by simpa using h52)
          have hw_pos : 0 < x / 25 := Nat.pos_of_ne_zero fun h0 => by
            rw [h0, mul_zero] at hdw; omega
          have h4x : 2 ^ (1 + 1) ∣ x := dvd_trans (Nat.pow_dvd_pow 2 ha2) h2a
          have h4w : 2 ^ (1 + 1) ∣ x / 25 :=
            (by decide : Nat.Coprime 4 25).dvd_of_dvd_mul_left (hdw.symm ▸ by simpa using h4x)
          simpa using prime_pow_dvd_div_rad hw_pos Nat.prime_two h4w)
        (by norm_num) (by decide) ?_
      refine K10DescentTree.closed _ 4 {2, 5, 11, 41}
        (fun p => if p = 2 then a else if p = 5 then 2 else 1) ?_ ?_
      · intro p hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl | rfl | rfl
        · exact ⟨by simp; omega, true, by simp⟩
        · exact ⟨by simp, true, by simp⟩
        · exact ⟨by simp, false, by simp⟩
        · exact ⟨by simp, false, by simp⟩
      · have hle_prod : (∏ p ∈ ({2, 5, 11, 41} : Finset ℕ),
            p ^ ((if p = 2 then 2 else if p = 5 then 2 else 1) - 1) * (p - 1)) ≤
          ∏ p ∈ ({2, 5, 11, 41} : Finset ℕ),
            p ^ ((if p = 2 then a else if p = 5 then 2 else 1) - 1) * (p - 1) := by
          refine Finset.prod_le_prod fun p _ => ?_
          by_cases hp2 : p = 2
          · subst hp2
            simp only [↓reduceIte]
            exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
          · simp [hp2]
        have hval : (∏ p ∈ ({2, 5, 11, 41} : Finset ℕ),
            p ^ ((if p = 2 then 2 else if p = 5 then 2 else 1) - 1) * (p - 1)) = 16000 := by
          decide
        rw [hval] at hle_prod
        exact le_trans (by norm_num : 10 ^ 4 ≤ 16000) hle_prod
    · -- b = 3: force 101 (e = 1, t = 0), closing at {2, 5, 101} (φ ≥ 20000).
      refine K10DescentTree.forceFive _ 4 {5} (fun _ => 3) 1 0 101
        (by simp) (by intro q hq; simp at hq; subst hq; simp)
        (Or.inr rfl) (fun _ _ _ _ _ _ => one_dvd _) (by norm_num) (by decide) ?_
      refine K10DescentTree.closed _ 4 {2, 5, 101}
        (fun p => if p = 2 then a else if p = 5 then 3 else 1) ?_ ?_
      · intro p hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl | rfl
        · exact ⟨by simp; omega, true, by simp⟩
        · exact ⟨by simp, true, by simp⟩
        · exact ⟨by simp, false, by simp⟩
      · have hle_prod : (∏ p ∈ ({2, 5, 101} : Finset ℕ),
            p ^ ((if p = 2 then 2 else if p = 5 then 3 else 1) - 1) * (p - 1)) ≤
          ∏ p ∈ ({2, 5, 101} : Finset ℕ),
            p ^ ((if p = 2 then a else if p = 5 then 3 else 1) - 1) * (p - 1) := by
          refine Finset.prod_le_prod fun p _ => ?_
          by_cases hp2 : p = 2
          · subst hp2
            simp only [↓reduceIte]
            exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
          · simp [hp2]
        have hval : (∏ p ∈ ({2, 5, 101} : Finset ℕ),
            p ^ ((if p = 2 then 2 else if p = 5 then 3 else 1) - 1) * (p - 1)) = 20000 := by
          decide
        rw [hval] at hle_prod
        exact le_trans (by norm_num : 10 ^ 4 ≤ 20000) hle_prod
    · -- b = 4: force 251 (e = 1, t = 1), closing at {2, 5, 251} (φ ≥ 250000).
      refine K10DescentTree.forceFive _ 4 {5} (fun _ => 4) 1 1 251
        (by simp) (by intro q hq; simp at hq; subst hq; simp)
        (Or.inl (by simp)) (fun _ _ _ _ _ _ => one_dvd _)
        (by norm_num)
        (by
          have htot625 : Nat.totient (∏ q ∈ ({5} : Finset ℕ), q ^ 4) = 500 := by
            rw [Finset.prod_singleton, Nat.totient_prime_pow (by norm_num) (by norm_num)]
            norm_num
          rw [htot625]
          norm_num)
        ?_
      refine K10DescentTree.closed _ 4 {2, 5, 251}
        (fun p => if p = 2 then a else if p = 5 then 4 else 1) ?_ ?_
      · intro p hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl | rfl
        · exact ⟨by simp; omega, true, by simp⟩
        · exact ⟨by simp, true, by simp⟩
        · exact ⟨by simp, false, by simp⟩
      · have hle_prod : (∏ p ∈ ({2, 5, 251} : Finset ℕ),
            p ^ ((if p = 2 then 2 else if p = 5 then 4 else 1) - 1) * (p - 1)) ≤
          ∏ p ∈ ({2, 5, 251} : Finset ℕ),
            p ^ ((if p = 2 then a else if p = 5 then 4 else 1) - 1) * (p - 1) := by
          refine Finset.prod_le_prod fun p _ => ?_
          by_cases hp2 : p = 2
          · subst hp2
            simp only [↓reduceIte]
            exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
          · simp [hp2]
        have hval : (∏ p ∈ ({2, 5, 251} : Finset ℕ),
            p ^ ((if p = 2 then 2 else if p = 5 then 4 else 1) - 1) * (p - 1)) = 250000 := by
          decide
        rw [hval] at hle_prod
        exact le_trans (by norm_num : 10 ^ 4 ≤ 250000) hle_prod
    · -- b = 5: since 2 ^ (a + 1) * 625 < 10000, we must have a = 2; force 3 via forceTwo!
      have ha_eq2 : a = 2 := by
        by_contra hne
        have h2 : 2 ^ 4 ≤ 2 ^ (a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        have hmul : 2 ^ 4 * 625 ≤ 2 ^ (a + 1) * 5 ^ (5 - 1) := Nat.mul_le_mul_right 625 h2
        norm_num at hmul hlt
        omega
      subst ha_eq2
      refine K10DescentTree.forceTwo _ 4 {2} (fun _ => 2) 1 0 3
        (by simp) (by intro q hq; simp at hq; subst hq; simp)
        (Or.inr rfl) (fun _ _ _ _ _ _ => one_dvd _) Nat.prime_three (by decide) ?_
      refine K10DescentTree.closed _ 4 {2, 5, 3}
        (fun p => if p = 2 then 2 else if p = 5 then 5 else 1) ?_ (by decide)
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl
      · exact ⟨by simp, true, by simp⟩
      · exact ⟨by simp, true, by simp⟩
      · exact ⟨by simp, false, by simp⟩

end CarmichaelTotient
