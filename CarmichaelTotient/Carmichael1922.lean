module

public import CarmichaelTotient.CaseRules

import Mathlib.Tactic

/-!
# Unconditional Carmichael (1922) Lower Bound (`10 ^ 37 ≤ x`, Case II `10 ^ 41 ≤ x`)

Proves unconditionally inside the Lean 4 kernel:
1. Verified structurally recursive binary modular exponentiation (`modPowAux`, `modPowFuel`)
   and Pratt/Lucas primality helper (`prime_of_pratt_cert`) built on `prime_of_lucas_witnesses`.
2. Primality of all 10 Carmichael (1922) primes:
   - Case I (`¬ 27 ∣ x`): `13, 79, 547, 3319, 1854763` (plus universal `7, 43`).
   - Case II (`27 ∣ x`): `19, 127, 2287, 101347, 304039` (plus universal `7, 43`).
3. Every prime in each list satisfies `ForcedCase1` / `ForcedCase2` via `step_6k_plus_1`,
   `step_case1_12k_plus_1`, and `step_case2_18k_plus_1`.
4. Exact divisibility bounds:
   - Case I: `39006985068987641549082746726712092964 ∣ x`, hence `10 ^ 37 ≤ x` (38 digits).
   - Case II: `282933326509039004376060391380922250272332 ∣ x`, hence `10 ^ 41 ≤ x` (42 digits).
5. Unconditional Carmichael (1922) bound: `carmichael_counterexample_ge_10_pow_37`
   (`IsCarmichaelCounterexample x → 10 ^ 37 ≤ x`).
6. Concrete `CarmichaelBoundCertificate` instantiation (`carmichael1922Certificate`) witnessing
   non-vacuity of the `ct-bound-3` certificate bridge (`digits = 37`).
-/

@[expose] public section

namespace CarmichaelTotient

/-! ## Verified binary modular exponentiation and Pratt/Lucas certificate helper -/

/-- Tail-recursive binary modular exponentiation, structurally recursive on `k : ℕ`. -/
def modPowAux : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, acc, _, _, _ => acc
  | k + 1, acc, base, exp, m =>
    if exp = 0 then acc
    else
      let acc' := if exp % 2 = 1 then (acc * base) % m else acc
      modPowAux k acc' ((base * base) % m) (exp / 2) m

/-- Binary modular exponentiation with explicit step bound `fuel`. -/
def modPowFuel (fuel a e m : ℕ) : ℕ :=
  modPowAux fuel (1 % m) (a % m) e m

/-- Loop invariant for `modPowAux`. -/
theorem modPowAux_eq : ∀ (k acc base exp m : ℕ),
    exp < 2 ^ k →
    modPowAux k (acc % m) base exp m = (acc * base ^ exp) % m
  | 0, acc, base, exp, m, hexp => by
    have h0 : exp = 0 := by simpa using hexp
    subst h0
    simp [modPowAux]
  | k + 1, acc, base, exp, m, hexp => by
    unfold modPowAux
    split_ifs with h0 hodd
    · subst h0
      simp
    · have hdiv : exp / 2 < 2 ^ k := by
        rw [pow_succ'] at hexp
        omega
      have hacc : (acc % m * base) % m = (acc * base) % m := by
        rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
      rw [hacc, modPowAux_eq k (acc * base) ((base * base) % m) (exp / 2) m hdiv]
      have hpow : ((base * base) % m) ^ (exp / 2) % m = (base * base) ^ (exp / 2) % m :=
        (Nat.pow_mod (base * base) (exp / 2) m).symm
      rw [Nat.mul_mod, hpow, ← Nat.mul_mod]
      have hexp_eq : exp = 2 * (exp / 2) + 1 := by omega
      congr 1
      calc
        acc * base * (base * base) ^ (exp / 2)
            = acc * base * (base ^ 2) ^ (exp / 2) := by rw [sq]
        _ = acc * base * base ^ (2 * (exp / 2)) := by rw [← pow_mul]
        _ = acc * (base ^ (2 * (exp / 2)) * base) := by ring
        _ = acc * base ^ (2 * (exp / 2) + 1) := by rw [← pow_succ]
        _ = acc * base ^ exp := by rw [← hexp_eq]
    · have hdiv : exp / 2 < 2 ^ k := by
        rw [pow_succ'] at hexp
        omega
      rw [modPowAux_eq k acc ((base * base) % m) (exp / 2) m hdiv]
      have hpow : ((base * base) % m) ^ (exp / 2) % m = (base * base) ^ (exp / 2) % m :=
        (Nat.pow_mod (base * base) (exp / 2) m).symm
      rw [Nat.mul_mod, hpow, ← Nat.mul_mod]
      have hexp_eq : exp = 2 * (exp / 2) := by omega
      congr 1
      calc
        acc * (base * base) ^ (exp / 2)
            = acc * (base ^ 2) ^ (exp / 2) := by rw [sq]
        _ = acc * base ^ (2 * (exp / 2)) := by rw [← pow_mul]
        _ = acc * base ^ exp := by rw [← hexp_eq]

/-- Correctness of `modPowFuel` whenever `e < 2 ^ fuel`. -/
theorem modPowFuel_eq (fuel a e m : ℕ) (he : e < 2 ^ fuel) :
    modPowFuel fuel a e m = a ^ e % m := by
  unfold modPowFuel
  rw [modPowAux_eq fuel 1 (a % m) e m he, one_mul, ← Nat.pow_mod]

/-- If a prime `q` divides the product of a list of primes `fs`, then `q ∈ fs`. -/
theorem mem_of_prime_dvd_list_prod {q : ℕ} {fs : List ℕ}
    (hq : Nat.Prime q) (hprime : ∀ r ∈ fs, Nat.Prime r) (hdvd : q ∣ fs.prod) :
    q ∈ fs := by
  induction fs with
  | nil =>
    simp only [List.prod_nil] at hdvd
    exact absurd hdvd hq.not_dvd_one
  | cons r rs ih =>
    simp only [List.prod_cons] at hdvd
    rcases hq.dvd_mul.mp hdvd with hqr | hqrs
    · have hr : Nat.Prime r := hprime r (by simp)
      have heq : q = r := (Nat.prime_dvd_prime_iff_eq hq hr).mp hqr
      simp [heq]
    · have hmem : q ∈ rs := ih (fun x hx => hprime x (by simp [hx])) hqrs
      simp [hmem]

/-- Single-witness Pratt/Lucas primality certificate checker proved directly from
`prime_of_lucas_witnesses` and `modPowFuel_eq`. -/
theorem prime_of_pratt_cert (p a fuel : ℕ) (fs : List ℕ)
    (hp : 2 ≤ p)
    (hfuel : p - 1 < 2 ^ fuel)
    (hprod : fs.prod = p - 1)
    (hprime : ∀ q ∈ fs, Nat.Prime q)
    (hfermat : modPowFuel fuel a (p - 1) p = 1)
    (horder : ∀ q ∈ fs, modPowFuel fuel a ((p - 1) / q) p ≠ 1) :
    Nat.Prime p := by
  apply prime_of_lucas_witnesses hp
  intro q hq hqd
  have hqmem : q ∈ fs := mem_of_prime_dvd_list_prod hq hprime (hprod ▸ hqd)
  have hlt : (p - 1) / q < 2 ^ fuel := lt_of_le_of_lt (Nat.div_le_self _ _) hfuel
  refine ⟨a, ?_, ?_⟩
  · rw [← modPowFuel_eq fuel a (p - 1) p hfuel]
    exact hfermat
  · rw [← modPowFuel_eq fuel a ((p - 1) / q) p hlt]
    exact horder q hqmem

/-! ## Primality proofs for all Carmichael (1922) primes -/

theorem prime_7 : Nat.Prime 7 := by norm_num
theorem prime_13 : Nat.Prime 13 := by norm_num
theorem prime_19 : Nat.Prime 19 := by norm_num
theorem prime_43 : Nat.Prime 43 := by norm_num
theorem prime_79 : Nat.Prime 79 := by norm_num
theorem prime_127 : Nat.Prime 127 := by norm_num
theorem prime_547 : Nat.Prime 547 := by norm_num

theorem prime_2287 : Nat.Prime 2287 :=
  prime_of_pratt_cert 2287 19 12 [2, 3, 3, 127]
    (by decide) (by decide) (by decide)
    (by
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact Nat.prime_two
      · exact Nat.prime_three
      · exact Nat.prime_three
      · exact prime_127)
    (by decide)
    (by decide)

theorem prime_3319 : Nat.Prime 3319 :=
  prime_of_pratt_cert 3319 6 12 [2, 3, 7, 79]
    (by decide) (by decide) (by decide)
    (by
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact Nat.prime_two
      · exact Nat.prime_three
      · exact prime_7
      · exact prime_79)
    (by decide)
    (by decide)

theorem prime_101347 : Nat.Prime 101347 :=
  prime_of_pratt_cert 101347 2 17 [2, 3, 7, 19, 127]
    (by decide) (by decide) (by decide)
    (by
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl
      · exact Nat.prime_two
      · exact Nat.prime_three
      · exact prime_7
      · exact prime_19
      · exact prime_127)
    (by decide)
    (by decide)

theorem prime_304039 : Nat.Prime 304039 :=
  prime_of_pratt_cert 304039 3 19 [2, 3, 3, 7, 19, 127]
    (by decide) (by decide) (by decide)
    (by
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Nat.prime_two
      · exact Nat.prime_three
      · exact Nat.prime_three
      · exact prime_7
      · exact prime_19
      · exact prime_127)
    (by decide)
    (by decide)

theorem prime_1854763 : Nat.Prime 1854763 :=
  prime_of_pratt_cert 1854763 2 21 [2, 3, 7, 13, 43, 79]
    (by decide) (by decide) (by decide)
    (by
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Nat.prime_two
      · exact Nat.prime_three
      · exact prime_7
      · exact prime_13
      · exact prime_43
      · exact prime_79)
    (by decide)
    (by decide)

/-! ## Case I derivation (`¬ 27 ∣ x`) and 38-digit bound (`10 ^ 37 ≤ x`) -/

/-- Carmichael (1922) Case I prime set `{7, 43, 13, 79, 547, 3319, 1854763}`. -/
def carmichaelCase1Primes : Finset ℕ :=
  {7, 43, 13, 79, 547, 3319, 1854763}

theorem forcedCase1_7 : ForcedCase1 7 := by
  have h := ForcedCase1.step6 (K := ∅) (by simp) (by simpa using prime_7)
  simpa using h

theorem forcedCase1_43 : ForcedCase1 43 := by
  have h := ForcedCase1.step6 (K := {7})
    (by intro q hq; simp at hq; subst hq; exact forcedCase1_7)
    (by simpa using prime_43)
  simpa using h

theorem forcedCase1_13 : ForcedCase1 13 := by
  have h := ForcedCase1.step12 (K := ∅) (by simp) (by simpa using prime_13)
  simpa using h

theorem forcedCase1_79 : ForcedCase1 79 := by
  have h := ForcedCase1.step6 (K := {13})
    (by intro q hq; simp at hq; subst hq; exact forcedCase1_13)
    (by simpa using prime_79)
  simpa using h

theorem forcedCase1_547 : ForcedCase1 547 := by
  have h := ForcedCase1.step6 (K := {7, 13})
    (by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact forcedCase1_7
      · exact forcedCase1_13)
    (by
      have hprod : 6 * (∏ q ∈ ({7, 13} : Finset ℕ), q) + 1 = 547 := by decide
      rw [hprod]
      exact prime_547)
  have hprod : 6 * (∏ q ∈ ({7, 13} : Finset ℕ), q) + 1 = 547 := by decide
  rwa [hprod] at h

theorem forcedCase1_3319 : ForcedCase1 3319 := by
  have h := ForcedCase1.step6 (K := {7, 79})
    (by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact forcedCase1_7
      · exact forcedCase1_79)
    (by
      have hprod : 6 * (∏ q ∈ ({7, 79} : Finset ℕ), q) + 1 = 3319 := by decide
      rw [hprod]
      exact prime_3319)
  have hprod : 6 * (∏ q ∈ ({7, 79} : Finset ℕ), q) + 1 = 3319 := by decide
  rwa [hprod] at h

theorem forcedCase1_1854763 : ForcedCase1 1854763 := by
  have h := ForcedCase1.step6 (K := {7, 13, 43, 79})
    (by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact forcedCase1_7
      · exact forcedCase1_13
      · exact forcedCase1_43
      · exact forcedCase1_79)
    (by
      have hprod : 6 * (∏ q ∈ ({7, 13, 43, 79} : Finset ℕ), q) + 1 = 1854763 := by decide
      rw [hprod]
      exact prime_1854763)
  have hprod : 6 * (∏ q ∈ ({7, 13, 43, 79} : Finset ℕ), q) + 1 = 1854763 := by decide
  rwa [hprod] at h

theorem forcedCase1_carmichael1922 : ∀ p ∈ carmichaelCase1Primes, ForcedCase1 p := by
  intro p hp
  simp only [carmichaelCase1Primes, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forcedCase1_7
  · exact forcedCase1_43
  · exact forcedCase1_13
  · exact forcedCase1_79
  · exact forcedCase1_547
  · exact forcedCase1_3319
  · exact forcedCase1_1854763

/-- Exact 38-digit divisor in Case I (`¬ 27 ∣ x`):
`4 * 9 * 7^2 * 43^2 * 13^2 * 79^2 * 547^2 * 3319^2 * 1854763^2 =
39006985068987641549082746726712092964 ∣ x`. -/
theorem carmichael_case1_exact_dvd {x : ℕ}
    (hx : IsCarmichaelCounterexample x) (h27 : ¬ 27 ∣ x) :
    39006985068987641549082746726712092964 ∣ x := by
  have hdvd := base_mul_prod_sq_dvd_case1 hx carmichaelCase1Primes fun p hp =>
    forcedCase1_sound hx h27 (forcedCase1_carmichael1922 p hp)
  have hval : (4 * 9) * (∏ p ∈ carmichaelCase1Primes, p ^ 2) =
      39006985068987641549082746726712092964 := by decide
  rwa [hval] at hdvd

/-- **Carmichael (1922) Case I bound**: `10 ^ 37 ≤ x` (at least 38 decimal digits). -/
theorem carmichael_case1_ge_10_pow_37 {x : ℕ}
    (hx : IsCarmichaelCounterexample x) (h27 : ¬ 27 ∣ x) :
    10 ^ 37 ≤ x := by
  have hdvd := carmichael_case1_exact_dvd hx h27
  have hle : 39006985068987641549082746726712092964 ≤ x := Nat.le_of_dvd hx.1 hdvd
  have h10 : 10 ^ 37 ≤ 39006985068987641549082746726712092964 := by norm_num
  exact le_trans h10 hle

/-! ## Case II derivation (`27 ∣ x`) and 42-digit bound (`10 ^ 41 ≤ x`) -/

/-- Carmichael (1922) Case II prime set `{7, 43, 19, 127, 2287, 101347, 304039}`. -/
def carmichaelCase2Primes : Finset ℕ :=
  {7, 43, 19, 127, 2287, 101347, 304039}

theorem forcedCase2_7 : ForcedCase2 7 := by
  have h := ForcedCase2.step6 (K := ∅) (by simp) (by simpa using prime_7)
  simpa using h

theorem forcedCase2_43 : ForcedCase2 43 := by
  have h := ForcedCase2.step6 (K := {7})
    (by intro q hq; simp at hq; subst hq; exact forcedCase2_7)
    (by simpa using prime_43)
  simpa using h

theorem forcedCase2_19 : ForcedCase2 19 := by
  have h := ForcedCase2.step18 (K := ∅) (by simp) (by simpa using prime_19)
  simpa using h

theorem forcedCase2_127 : ForcedCase2 127 := by
  have h := ForcedCase2.step18 (K := {7})
    (by intro q hq; simp at hq; subst hq; exact forcedCase2_7)
    (by simpa using prime_127)
  simpa using h

theorem forcedCase2_2287 : ForcedCase2 2287 := by
  have h := ForcedCase2.step18 (K := {127})
    (by intro q hq; simp at hq; subst hq; exact forcedCase2_127)
    (by simpa using prime_2287)
  simpa using h

theorem forcedCase2_101347 : ForcedCase2 101347 := by
  have h := ForcedCase2.step6 (K := {7, 19, 127})
    (by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl
      · exact forcedCase2_7
      · exact forcedCase2_19
      · exact forcedCase2_127)
    (by
      have hprod : 6 * (∏ q ∈ ({7, 19, 127} : Finset ℕ), q) + 1 = 101347 := by decide
      rw [hprod]
      exact prime_101347)
  have hprod : 6 * (∏ q ∈ ({7, 19, 127} : Finset ℕ), q) + 1 = 101347 := by decide
  rwa [hprod] at h

theorem forcedCase2_304039 : ForcedCase2 304039 := by
  have h := ForcedCase2.step18 (K := {7, 19, 127})
    (by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl
      · exact forcedCase2_7
      · exact forcedCase2_19
      · exact forcedCase2_127)
    (by
      have hprod : 18 * (∏ q ∈ ({7, 19, 127} : Finset ℕ), q) + 1 = 304039 := by decide
      rw [hprod]
      exact prime_304039)
  have hprod : 18 * (∏ q ∈ ({7, 19, 127} : Finset ℕ), q) + 1 = 304039 := by decide
  rwa [hprod] at h

theorem forcedCase2_carmichael1922 : ∀ p ∈ carmichaelCase2Primes, ForcedCase2 p := by
  intro p hp
  simp only [carmichaelCase2Primes, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forcedCase2_7
  · exact forcedCase2_43
  · exact forcedCase2_19
  · exact forcedCase2_127
  · exact forcedCase2_2287
  · exact forcedCase2_101347
  · exact forcedCase2_304039

/-- Exact 42-digit divisor in Case II (`27 ∣ x`):
`4 * 27 * 7^2 * 43^2 * 19^2 * 127^2 * 2287^2 * 101347^2 * 304039^2 =
282933326509039004376060391380922250272332 ∣ x`. -/
theorem carmichael_case2_exact_dvd {x : ℕ}
    (hx : IsCarmichaelCounterexample x) (h27 : 27 ∣ x) :
    282933326509039004376060391380922250272332 ∣ x := by
  have hdvd := base_mul_prod_sq_dvd_case2 hx h27 carmichaelCase2Primes fun p hp =>
    forcedCase2_sound hx h27 (forcedCase2_carmichael1922 p hp)
  have hval : (4 * 27) * (∏ p ∈ carmichaelCase2Primes, p ^ 2) =
      282933326509039004376060391380922250272332 := by decide
  rwa [hval] at hdvd

/-- **Carmichael (1922) Case II bound**: `10 ^ 41 ≤ x` (at least 42 decimal digits). -/
theorem carmichael_case2_ge_10_pow_41 {x : ℕ}
    (hx : IsCarmichaelCounterexample x) (h27 : 27 ∣ x) :
    10 ^ 41 ≤ x := by
  have hdvd := carmichael_case2_exact_dvd hx h27
  have hle : 282933326509039004376060391380922250272332 ≤ x := Nat.le_of_dvd hx.1 hdvd
  have h10 : 10 ^ 41 ≤ 282933326509039004376060391380922250272332 := by norm_num
  exact le_trans h10 hle

/-! ## Unconditional Carmichael (1922) 38-digit lower bound -/

/-- **Unconditional Carmichael (1922) lower bound**:
Every Carmichael totient counterexample satisfies `10 ^ 37 ≤ x` (at least 38 decimal digits). -/
theorem carmichael_counterexample_ge_10_pow_37 {x : ℕ}
    (hx : IsCarmichaelCounterexample x) :
    10 ^ 37 ≤ x := by
  rcases carmichael_case_split hx with ⟨_, h27, _⟩ | h27
  · exact carmichael_case1_ge_10_pow_37 hx h27
  · exact le_trans (by norm_num : 10 ^ 37 ≤ 10 ^ 41) (carmichael_case2_ge_10_pow_41 hx h27)

/-! ## Concrete `CarmichaelBoundCertificate` instantiation (non-vacuity witness) -/

/-- Concrete instantiation of `CarmichaelBoundCertificate` using Carmichael's (1922) prime sets
and `10 ^ 3 < 2 ^ 10`, certifying `digits = 37` (`10 ^ 37 < x`) through the exact same
certificate interface used to model `ct-bound-3`. -/
def carmichael1922Certificate : CarmichaelBoundCertificate where
  case1 :=
    { ι := Unit
      chunks := {()}
      chunkPrimes := fun _ => carmichaelCase1Primes
      pairwiseDisjoint := by
        intro a ha b hb hab
        exact False.elim (hab (Subsingleton.elim a b))
      allForced := fun _ _ p hp => forcedCase1_carmichael1922 p hp
      b0 := 5
      hb0 := by norm_num
      bc := fun _ => 119
      hbc := fun _ _ => by decide
      p10 := 3
      q10 := 10
      hq10 := by norm_num
      hlog := by norm_num }
  case2 :=
    { ι := Unit
      chunks := {()}
      chunkPrimes := fun _ => carmichaelCase2Primes
      pairwiseDisjoint := by
        intro a ha b hb hab
        exact False.elim (hab (Subsingleton.elim a b))
      allForced := fun _ _ p hp => forcedCase2_carmichael1922 p hp
      b0 := 6
      hb0 := by norm_num
      bc := fun _ => 130
      hbc := fun _ _ => by decide
      p10 := 3
      q10 := 10
      hq10 := by norm_num
      hlog := by norm_num }

theorem carmichael1922Certificate_digits : carmichael1922Certificate.digits = 37 := by
  simp [carmichael1922Certificate, CarmichaelBoundCertificate.digits,
    Case1Certificate.digits, Case2Certificate.digits]

/-- Alternative strict derivation `10 ^ 37 < x` directly via `carmichael1922Certificate`
and `carmichael_bound_strict_from_certificate`. -/
theorem carmichael_counterexample_gt_10_pow_37 {x : ℕ}
    (hx : IsCarmichaelCounterexample x) :
    10 ^ 37 < x := by
  have h := carmichael_bound_strict_from_certificate carmichael1922Certificate
    (by rw [carmichael1922Certificate_digits]; omega) hx
  rwa [carmichael1922Certificate_digits] at h

end CarmichaelTotient
