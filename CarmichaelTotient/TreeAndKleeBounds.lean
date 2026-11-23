module

public import CarmichaelTotient.StructuralAndPomerance
public import CarmichaelTotient.ValuationTree

import Mathlib.Tactic

/-!
# Pure-Kernel Unconditional `10 ^ 10,000 < x` Bound & Unified Strengthening Re-Exports

Re-exports:
- `CarmichaelTotient.StructuralAndPomerance` (Pomerance's 1974 sufficient condition, Klee's 1947
  reduced/minimal counterexample structural theorems `4 ∣ x ∧ ¬ 8 ∣ x` and Fermat-prime exclusion,
  and Erdős's 1958 valence-preserving fiber bijection & counterexample multiplication theorem).
- `CarmichaelTotient.ValuationTree` (general multi-branch `CarmichaelValuationTree` soundness,
  Klee's 3-way `54k + 1` case split, and Ford's §7.3 `k = 10` divisible-preimage descent tree
  `K10DescentTree` / `K10RungCertificate` bridging the `K = 50` and `K = 60` 8,243-root runs).

And establishes unconditionally inside the Lean 4 kernel (zero `native_decide`):
- A pure-`Bool` multi-layer bitmask Lucas ladder verifier (`evalLadder`, `splitChunks`,
  `checkCaseLadder`) using prefix/suffix factor-chain modular exponentiation (`powFactorList`,
  `checkPrefixSuffix`, max per-factor bit bound `120`) sound with respect to `ForcedCase1`,
  `ForcedCase2`, `Case1Certificate`, `Case2Certificate`, and `CarmichaelBoundCertificate`.
- 161 certified primes across Case I (81 primes up to 469 bits, 11 chunks, 34,024 bits, 10,240
  digits) and Case II (80 primes up to 470 bits, 10 chunks, 33,616 bits, 10,117 digits),
  constructing `masaiValette1982Certificate : CarmichaelBoundCertificate` (`10117 ≤ cert.digits`).
- Unconditional kernel theorems:
  - `carmichael_case1_gt_10_pow_10240`: `IsCarmichaelCounterexample x → ¬ 27 ∣ x → 10 ^ 10240 < x`
  - `carmichael_case2_gt_10_pow_10117`: `IsCarmichaelCounterexample x → 27 ∣ x → 10 ^ 10117 < x`
  - `carmichael_counterexample_gt_10_pow_10117`: `IsCarmichaelCounterexample x → 10 ^ 10117 < x`
  - `carmichael_counterexample_gt_10_pow_10000`: `IsCarmichaelCounterexample x → 10 ^ 10000 < x`
    (surpassing Masai & Valette 1982 inside the Lean 4 kernel)
  - `carmichael_counterexample_gt_10_pow_1000`: `IsCarmichaelCounterexample x → 10 ^ 1000 < x`
  - `carmichael_counterexample_gt_10_pow_400`: `IsCarmichaelCounterexample x → 10 ^ 400 < x`
    (surpassing Klee 1947 inside the Lean 4 kernel).
-/

@[expose] public section

namespace CarmichaelTotient

/-! ## Pure-Bool Bitmask Lucas Ladder & Prefix/Suffix Factor-Chain Verifier -/

/-- One step `(mult, mask, witness)` of a sliding-window Lucas primality ladder:
`mask` selects a subset `sub` of the current 16-prime seed window, forming candidate
`p = mult * sub.prod + 1` certified prime by single-witness Lucas test with base `witness`. -/
structure LadderStep where
  mult : ℕ
  mask : ℕ
  witness : ℕ
  deriving Repr, DecidableEq

/-- Select the sublist of `ws` corresponding to set bits of `mask` (LSB = head of `ws`). -/
def maskSublist : ℕ → List ℕ → List ℕ
  | _, [] => []
  | mask, w :: ws =>
    let rest := maskSublist (mask / 2) ws
    if mask % 2 == 1 then w :: rest else rest

/-- Every element of `maskSublist mask ws` belongs to `ws`. -/
theorem mem_maskSublist : ∀ {mask : ℕ} {ws : List ℕ} {x : ℕ},
    x ∈ maskSublist mask ws → x ∈ ws
  | _, [], _, h => by simp [maskSublist] at h
  | mask, w :: ws, x, h => by
    unfold maskSublist at h
    dsimp only at h
    split_ifs at h with hb
    · rcases List.mem_cons.mp h with rfl | hrest
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem w (mem_maskSublist hrest)
    · exact List.mem_cons_of_mem w (mem_maskSublist h)

/-- `maskSublist` preserves `List.Nodup`. -/
theorem nodup_maskSublist : ∀ {mask : ℕ} {ws : List ℕ},
    ws.Nodup → (maskSublist mask ws).Nodup
  | _, [], _ => by simp [maskSublist]
  | mask, w :: ws, hnd => by
    rcases List.nodup_cons.mp hnd with ⟨hw, hws⟩
    unfold maskSublist
    dsimp only
    split_ifs with hb
    · refine List.nodup_cons.mpr ⟨?_, nodup_maskSublist hws⟩
      intro hmem
      exact hw (mem_maskSublist hmem)
    · exact nodup_maskSublist hws

/-- For a duplicate-free list `l : List ℕ`, `∏ x ∈ l.toFinset, x = l.prod`. -/
theorem prod_toFinset_eq_list_prod : ∀ {l : List ℕ},
    l.Nodup → (∏ x ∈ l.toFinset, x) = l.prod
  | [], _ => by simp
  | x :: xs, hnd => by
    rcases List.nodup_cons.mp hnd with ⟨hx, hxs⟩
    have hx' : x ∉ xs.toFinset := by simpa using hx
    rw [List.toFinset_cons, Finset.prod_insert hx', List.prod_cons,
      prod_toFinset_eq_list_prod hxs]

/-- Linear pure-`Bool` check that all elements of `xs` are strictly greater than `prev`
and strictly increasing. -/
def isStrictlyIncreasingAux : ℕ → List ℕ → Bool
  | _, [] => true
  | prev, x :: xs => Nat.ble (prev + 1) x && isStrictlyIncreasingAux x xs

/-- Linear pure-`Bool` check that `l : List ℕ` is strictly increasing. -/
def isStrictlyIncreasing : List ℕ → Bool
  | [] => true
  | x :: xs => isStrictlyIncreasingAux x xs

private theorem gt_of_isStrictlyIncreasingAux : ∀ {prev : ℕ} {xs : List ℕ} {y : ℕ},
    isStrictlyIncreasingAux prev xs = true → y ∈ xs → prev < y
  | _, [], _, _, hy => by simp at hy
  | prev, x :: xs, y, h, hy => by
    simp only [isStrictlyIncreasingAux, Bool.and_eq_true, Nat.ble_eq] at h
    rcases List.mem_cons.mp hy with rfl | hmem
    · omega
    · have hxy := gt_of_isStrictlyIncreasingAux h.2 hmem
      omega

private theorem nodup_of_isStrictlyIncreasingAux : ∀ {prev : ℕ} {xs : List ℕ},
    isStrictlyIncreasingAux prev xs = true → xs.Nodup
  | _, [], _ => List.nodup_nil
  | prev, x :: xs, h => by
    simp only [isStrictlyIncreasingAux, Bool.and_eq_true, Nat.ble_eq] at h
    refine List.nodup_cons.mpr ⟨?_, nodup_of_isStrictlyIncreasingAux h.2⟩
    intro hx
    have hlt := gt_of_isStrictlyIncreasingAux h.2 hx
    omega

/-- Any list passing `isStrictlyIncreasing` is duplicate-free (`List.Nodup`). -/
theorem nodup_of_isStrictlyIncreasing {l : List ℕ} (h : isStrictlyIncreasing l = true) :
    l.Nodup := by
  cases l with
  | nil => exact List.nodup_nil
  | cons x xs =>
    exact List.nodup_cons.mpr
      ⟨fun hx => Nat.lt_irrefl x (gt_of_isStrictlyIncreasingAux h hx),
       nodup_of_isStrictlyIncreasingAux h⟩

/-- Raise `b` modulo `m` successively to each exponent in `fs`: computes `b ^ fs.prod % m`
using only per-factor binary exponentiation bound `fuel`. -/
def powFactorList (fuel b m : ℕ) : List ℕ → ℕ
  | [] => b % m
  | f :: fs => powFactorList fuel (modPowFuel fuel b f m) m fs

/-- Correctness of `powFactorList` whenever every factor in `fs` is `< 2 ^ fuel`. -/
theorem powFactorList_eq (fuel : ℕ) :
    ∀ (fs : List ℕ) (b m : ℕ),
      (∀ f ∈ fs, f < 2 ^ fuel) →
      powFactorList fuel b m fs = (b ^ fs.prod) % m
  | [], b, m, _ => by simp [powFactorList]
  | f :: fs, b, m, hfs => by
    have hf : f < 2 ^ fuel := hfs f List.mem_cons_self
    have hrest : ∀ g ∈ fs, g < 2 ^ fuel := fun g hg => hfs g (List.mem_cons_of_mem f hg)
    unfold powFactorList
    rw [powFactorList_eq fuel fs (modPowFuel fuel b f m) m hrest,
      modPowFuel_eq fuel b f m hf, ← Nat.pow_mod, ← pow_mul, ← List.prod_cons]

/-- Prefix/suffix factor-chain verifier: checks for every factor `f` in `fs` that `1 ≤ f`,
`f < 2 ^ fuel`, and `pref` raised to the product of the remaining factors is `≠ 1 (mod m)`,
returning `(ok, pref ^ fs.prod % m)`. -/
def checkPrefixSuffix (fuel m pref : ℕ) : List ℕ → Bool × ℕ
  | [] => (true, pref % m)
  | f :: fs =>
    let rem := powFactorList fuel pref m fs
    let res := checkPrefixSuffix fuel m (modPowFuel fuel pref f m) fs
    (Nat.ble 1 f && Nat.ble (f + 1) (2 ^ fuel) && (rem != 1) && res.1, res.2)

/-- Soundness invariant of `checkPrefixSuffix`. -/
theorem checkPrefixSuffix_sound (fuel m a : ℕ) :
    ∀ (fs : List ℕ) (P full : ℕ),
      checkPrefixSuffix fuel m ((a ^ P) % m) fs = (true, full) →
      (∀ f ∈ fs, 0 < f ∧ f < 2 ^ fuel) ∧
      full = (a ^ (P * fs.prod)) % m ∧
      (∀ q ∈ fs, ∃ c : ℕ, q * c = P * fs.prod ∧ (a ^ c) % m ≠ 1)
  | [], P, full, h => by
    simp only [checkPrefixSuffix, Prod.mk.injEq, Nat.mod_mod] at h
    exact ⟨by simp, by simpa using h.2.symm, by simp⟩
  | f :: fs, P, full, h => by
    unfold checkPrefixSuffix at h
    dsimp only at h
    rcases hres : checkPrefixSuffix fuel m (modPowFuel fuel ((a ^ P) % m) f m) fs with
      ⟨okR, fullR⟩
    rw [hres] at h
    simp only [Prod.mk.injEq, Bool.and_eq_true, Nat.ble_eq, bne_iff_ne] at h
    rcases h with ⟨⟨⟨⟨hf1, hffuel⟩, hrem⟩, hokR⟩, hfullR⟩
    subst hokR
    subst hfullR
    have hf_lt : f < 2 ^ fuel := by omega
    have hpref' : modPowFuel fuel ((a ^ P) % m) f m = (a ^ (P * f)) % m := by
      rw [modPowFuel_eq fuel ((a ^ P) % m) f m hf_lt, ← Nat.pow_mod, ← pow_mul]
    rw [hpref'] at hres
    have ⟨ih_bounds, ih_full, ih_ord⟩ := checkPrefixSuffix_sound fuel m a fs (P * f) fullR hres
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_cons.mp hg with rfl | hmem
      · exact ⟨by omega, hf_lt⟩
      · exact ih_bounds g hmem
    · rw [ih_full, List.prod_cons, mul_assoc]
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hmem
      · refine ⟨P * fs.prod, ?_, ?_⟩
        · rw [List.prod_cons]
          ring
        · have hfs_lt : ∀ g ∈ fs, g < 2 ^ fuel := fun g hg => (ih_bounds g hg).2
          rw [powFactorList_eq fuel fs ((a ^ P) % m) m hfs_lt, ← Nat.pow_mod, ← pow_mul] at hrem
          exact hrem
      · rcases ih_ord q hmem with ⟨c, hc_eq, hc_ne⟩
        refine ⟨c, ?_, hc_ne⟩
        rw [hc_eq, List.prod_cons, mul_assoc]

/-- Prime factorization list of an allowed multiplier `mult ∈ {6, 12, 18}`. -/
def multFactors (mult : ℕ) : List ℕ :=
  if mult == 6 then [2, 3]
  else if mult == 12 then [2, 2, 3]
  else [2, 3, 3]

private theorem multFactors_spec {mult : ℕ} (hmult : mult = 6 ∨ mult = 12 ∨ mult = 18) :
    (multFactors mult).prod = mult ∧ ∀ r ∈ multFactors mult, Nat.Prime r := by
  rcases hmult with rfl | rfl | rfl
  · refine ⟨by decide, fun r hr => ?_⟩
    simp [multFactors] at hr
    rcases hr with rfl | rfl <;> norm_num
  · refine ⟨by decide, fun r hr => ?_⟩
    simp [multFactors] at hr
    rcases hr with rfl | rfl <;> norm_num
  · refine ⟨by decide, fun r hr => ?_⟩
    simp [multFactors] at hr
    rcases hr with rfl | rfl <;> norm_num

private theorem list_prod_pos : ∀ {l : List ℕ}, (∀ x ∈ l, 0 < x) → 0 < l.prod
  | [], _ => by simp
  | x :: xs, h => by
    rw [List.prod_cons]
    exact Nat.mul_pos (h x List.mem_cons_self)
      (list_prod_pos fun y hy => h y (List.mem_cons_of_mem x hy))

/-- Soundness of a single Lucas ladder primality check for `p = mult * sub.prod + 1`
using `checkPrefixSuffix` over `multFactors mult ++ sub`. -/
theorem prime_of_ladder_step {mult fuel a : ℕ} {sub : List ℕ}
    (hmult : mult = 6 ∨ mult = 12 ∨ mult = 18)
    (hsub : ∀ r ∈ sub, Nat.Prime r)
    (hchk :
      let p := mult * sub.prod + 1
      let res := checkPrefixSuffix fuel p (a % p) (multFactors mult ++ sub)
      (res.1 && (res.2 == 1)) = true) :
    Nat.Prime (mult * sub.prod + 1) := by
  set p := mult * sub.prod + 1
  set fs := multFactors mult ++ sub
  have ⟨hmprod, hmprime⟩ := multFactors_spec hmult
  have hfs_prime : ∀ r ∈ fs, Nat.Prime r := by
    intro r hr
    rcases List.mem_append.mp hr with h1 | h2
    · exact hmprime r h1
    · exact hsub r h2
  have hsub_pos : 0 < sub.prod := list_prod_pos fun r hr => (hsub r hr).pos
  have hmult_ge : 6 ≤ mult := by rcases hmult with rfl | rfl | rfl <;> omega
  have hp2 : 2 ≤ p := by
    have : 6 * 1 ≤ mult * sub.prod := Nat.mul_le_mul hmult_ge hsub_pos
    omega
  have hfs_prod : fs.prod = p - 1 := by
    have h1 : fs.prod = mult * sub.prod := by
      rw [List.prod_append, hmprod]
    omega
  dsimp only at hchk
  rcases hres : checkPrefixSuffix fuel p (a % p) fs with ⟨okB, fullV⟩
  rw [hres] at hchk
  simp only [Bool.and_eq_true, beq_iff_eq] at hchk
  rcases hchk with ⟨rfl, rfl⟩
  have hres1 : checkPrefixSuffix fuel p ((a ^ 1) % p) fs = (true, 1) := by
    simpa [pow_one] using hres
  have ⟨_, hfull, hord⟩ := checkPrefixSuffix_sound fuel p a fs 1 1 hres1
  rw [one_mul, hfs_prod] at hfull
  apply prime_of_lucas_witnesses hp2
  intro q hq hqd
  have hqmem : q ∈ fs := mem_of_prime_dvd_list_prod hq hfs_prime (hfs_prod.symm ▸ hqd)
  rcases hord q hqmem with ⟨c, hqc, hac⟩
  rw [one_mul, hfs_prod] at hqc
  have hdiv : (p - 1) / q = c := by
    have hpm1_eq : p - 1 = c * q := by rw [← hqc, mul_comm]
    rw [hpm1_eq, Nat.mul_div_cancel c hq.pos]
  refine ⟨a, hfull.symm, ?_⟩
  rw [hdiv]
  exact hac

/-- Every prime in `ForcedCase1` is prime (directly from its inductive constructors). -/
theorem ForcedCase1.prime {p : ℕ} (hp : ForcedCase1 p) : Nat.Prime p := by
  cases hp with
  | step6 _ hpr => exact hpr
  | step12 _ hpr => exact hpr

/-- Every prime in `ForcedCase2` is prime (directly from its inductive constructors). -/
theorem ForcedCase2.prime {p : ℕ} (hp : ForcedCase2 p) : Nat.Prime p := by
  cases hp with
  | step6 _ hpr => exact hpr
  | step18 _ hpr => exact hpr

/-- Per-factor binary exponentiation fuel for the 10,000-digit ladders (all prime factors in
Layers 0..4 satisfy `f < 2 ^ 120`). -/
def ladderFactorFuel : ℕ := 120

/-- Evaluate one `LadderStep` against seed `window` with allowed multipliers `{6, allowedMult2}`. -/
def evalStep (allowedMult2 : ℕ) (window : List ℕ) (st : LadderStep) : Option ℕ :=
  if (st.mult == 6) || (st.mult == allowedMult2) then
    let sub := maskSublist st.mask window
    let p := st.mult * sub.prod + 1
    let res := checkPrefixSuffix ladderFactorFuel p (st.witness % p) (multFactors st.mult ++ sub)
    if res.1 && (res.2 == 1) then
      some p
    else
      none
  else
    none

/-- Evaluate a layer of `LadderStep`s against a fixed 16-prime seed `window`. -/
def evalLayer (allowedMult2 : ℕ) (window : List ℕ) : List LadderStep → Option (List ℕ)
  | [] => some []
  | st :: sts =>
    match evalStep allowedMult2 window st, evalLayer allowedMult2 window sts with
    | some p, some ps => some (p :: ps)
    | _, _ => none

/-- Evaluate a multi-layer Lucas ladder, updating the 16-prime sliding window after each layer
and checking strict monotonicity of each seed window and of the final prime list. -/
def evalLadderAux (allowedMult2 : ℕ) : List ℕ → List (List LadderStep) → Option (List ℕ)
  | acc, [] =>
    if isStrictlyIncreasing acc then some acc else none
  | acc, layer :: layers =>
    let window := acc.drop (acc.length - 16)
    if isStrictlyIncreasing window then
      match evalLayer allowedMult2 window layer with
      | some newPs => evalLadderAux allowedMult2 (acc ++ newPs) layers
      | none => none
    else
      none

/-- Evaluate a multi-layer Lucas ladder starting from the empty prime accumulator. -/
def evalLadder (allowedMult2 : ℕ) (layers : List (List LadderStep)) : Option (List ℕ) :=
  evalLadderAux allowedMult2 [] layers

theorem evalStep_case1_sound {window : List ℕ} {st : LadderStep} {p : ℕ}
    (hwnd_nd : window.Nodup)
    (hwnd_f : ∀ q ∈ window, ForcedCase1 q)
    (heval : evalStep 12 window st = some p) :
    ForcedCase1 p := by
  unfold evalStep at heval
  cases hmb : ((st.mult == 6) || (st.mult == 12))
  · simp [hmb] at heval
  · simp only [hmb, ↓reduceIte] at heval
    set sub := maskSublist st.mask window
    set p0 := st.mult * sub.prod + 1
    set res := checkPrefixSuffix ladderFactorFuel p0 (st.witness % p0)
      (multFactors st.mult ++ sub)
    cases hchk : (res.1 && (res.2 == 1))
    · simp [hchk] at heval
    · simp only [hchk, ↓reduceIte, Option.some.injEq] at heval
      subst heval
      simp only [Bool.or_eq_true, beq_iff_eq] at hmb
      have hsub_nd : sub.Nodup := nodup_maskSublist hwnd_nd
      have hsub_f : ∀ q ∈ sub, ForcedCase1 q := fun q hq => hwnd_f q (mem_maskSublist hq)
      have hsub_pr : ∀ q ∈ sub, Nat.Prime q := fun q hq => (hsub_f q hq).prime
      have hmult3 : st.mult = 6 ∨ st.mult = 12 ∨ st.mult = 18 := by
        rcases hmb with h6 | h12
        · exact Or.inl h6
        · exact Or.inr (Or.inl h12)
      have hp_prime : Nat.Prime (st.mult * sub.prod + 1) :=
        prime_of_ladder_step hmult3 hsub_pr hchk
      have hprod_eq : (∏ q ∈ sub.toFinset, q) = sub.prod := prod_toFinset_eq_list_prod hsub_nd
      have hK_f : ∀ q ∈ sub.toFinset, ForcedCase1 q := fun q hq =>
        hsub_f q (List.mem_toFinset.mp hq)
      change ForcedCase1 (st.mult * sub.prod + 1)
      rcases hmb with h6 | h12
      · rw [h6, ← hprod_eq] at hp_prime ⊢
        exact ForcedCase1.step6 hK_f hp_prime
      · rw [h12, ← hprod_eq] at hp_prime ⊢
        exact ForcedCase1.step12 hK_f hp_prime

theorem evalStep_case2_sound {window : List ℕ} {st : LadderStep} {p : ℕ}
    (hwnd_nd : window.Nodup)
    (hwnd_f : ∀ q ∈ window, ForcedCase2 q)
    (heval : evalStep 18 window st = some p) :
    ForcedCase2 p := by
  unfold evalStep at heval
  cases hmb : ((st.mult == 6) || (st.mult == 18))
  · simp [hmb] at heval
  · simp only [hmb, ↓reduceIte] at heval
    set sub := maskSublist st.mask window
    set p0 := st.mult * sub.prod + 1
    set res := checkPrefixSuffix ladderFactorFuel p0 (st.witness % p0)
      (multFactors st.mult ++ sub)
    cases hchk : (res.1 && (res.2 == 1))
    · simp [hchk] at heval
    · simp only [hchk, ↓reduceIte, Option.some.injEq] at heval
      subst heval
      simp only [Bool.or_eq_true, beq_iff_eq] at hmb
      have hsub_nd : sub.Nodup := nodup_maskSublist hwnd_nd
      have hsub_f : ∀ q ∈ sub, ForcedCase2 q := fun q hq => hwnd_f q (mem_maskSublist hq)
      have hsub_pr : ∀ q ∈ sub, Nat.Prime q := fun q hq => (hsub_f q hq).prime
      have hmult3 : st.mult = 6 ∨ st.mult = 12 ∨ st.mult = 18 := by
        rcases hmb with h6 | h18
        · exact Or.inl h6
        · exact Or.inr (Or.inr h18)
      have hp_prime : Nat.Prime (st.mult * sub.prod + 1) :=
        prime_of_ladder_step hmult3 hsub_pr hchk
      have hprod_eq : (∏ q ∈ sub.toFinset, q) = sub.prod := prod_toFinset_eq_list_prod hsub_nd
      have hK_f : ∀ q ∈ sub.toFinset, ForcedCase2 q := fun q hq =>
        hsub_f q (List.mem_toFinset.mp hq)
      change ForcedCase2 (st.mult * sub.prod + 1)
      rcases hmb with h6 | h18
      · rw [h6, ← hprod_eq] at hp_prime ⊢
        exact ForcedCase2.step6 hK_f hp_prime
      · rw [h18, ← hprod_eq] at hp_prime ⊢
        exact ForcedCase2.step18 hK_f hp_prime

private theorem evalLayer_case1_sound {window : List ℕ}
    (hwnd_nd : window.Nodup) (hwnd_f : ∀ q ∈ window, ForcedCase1 q) :
    ∀ {layer : List LadderStep} {ps : List ℕ},
      evalLayer 12 window layer = some ps → ∀ p ∈ ps, ForcedCase1 p
  | [], ps, h => by
    simp [evalLayer] at h
    subst h
    simp
  | st :: sts, ps, h => by
    unfold evalLayer at h
    cases hs : evalStep 12 window st with
    | none => simp [hs] at h
    | some p0 =>
      cases hls : evalLayer 12 window sts with
      | none => simp [hs, hls] at h
      | some ps0 =>
        simp [hs, hls] at h
        subst h
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hmem
        · exact evalStep_case1_sound hwnd_nd hwnd_f hs
        · exact evalLayer_case1_sound hwnd_nd hwnd_f hls p hmem

private theorem evalLayer_case2_sound {window : List ℕ}
    (hwnd_nd : window.Nodup) (hwnd_f : ∀ q ∈ window, ForcedCase2 q) :
    ∀ {layer : List LadderStep} {ps : List ℕ},
      evalLayer 18 window layer = some ps → ∀ p ∈ ps, ForcedCase2 p
  | [], ps, h => by
    simp [evalLayer] at h
    subst h
    simp
  | st :: sts, ps, h => by
    unfold evalLayer at h
    cases hs : evalStep 18 window st with
    | none => simp [hs] at h
    | some p0 =>
      cases hls : evalLayer 18 window sts with
      | none => simp [hs, hls] at h
      | some ps0 =>
        simp [hs, hls] at h
        subst h
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hmem
        · exact evalStep_case2_sound hwnd_nd hwnd_f hs
        · exact evalLayer_case2_sound hwnd_nd hwnd_f hls p hmem

private theorem evalLadderAux_case1_sound :
    ∀ {layers : List (List LadderStep)} {acc ps : List ℕ},
      (∀ q ∈ acc, ForcedCase1 q) →
      evalLadderAux 12 acc layers = some ps →
      ps.Nodup ∧ ∀ p ∈ ps, ForcedCase1 p
  | [], acc, ps, hacc, h => by
    unfold evalLadderAux at h
    split_ifs at h with hinc
    · simp only [Option.some.injEq] at h
      subst h
      exact ⟨nodup_of_isStrictlyIncreasing hinc, hacc⟩
  | layer :: layers, acc, ps, hacc, h => by
    unfold evalLadderAux at h
    dsimp only at h
    split_ifs at h with hinc
    · cases hly : evalLayer 12 (acc.drop (acc.length - 16)) layer with
      | none => simp [hly] at h
      | some newPs =>
        rw [hly] at h
        have hwnd_nd := nodup_of_isStrictlyIncreasing hinc
        have hwnd_f : ∀ q ∈ acc.drop (acc.length - 16), ForcedCase1 q := fun q hq =>
          hacc q (List.mem_of_mem_drop hq)
        have hnew_f := evalLayer_case1_sound hwnd_nd hwnd_f hly
        refine evalLadderAux_case1_sound (fun q hq => ?_) h
        rcases List.mem_append.mp hq with h1 | h2
        · exact hacc q h1
        · exact hnew_f q h2

private theorem evalLadderAux_case2_sound :
    ∀ {layers : List (List LadderStep)} {acc ps : List ℕ},
      (∀ q ∈ acc, ForcedCase2 q) →
      evalLadderAux 18 acc layers = some ps →
      ps.Nodup ∧ ∀ p ∈ ps, ForcedCase2 p
  | [], acc, ps, hacc, h => by
    unfold evalLadderAux at h
    split_ifs at h with hinc
    · simp only [Option.some.injEq] at h
      subst h
      exact ⟨nodup_of_isStrictlyIncreasing hinc, hacc⟩
  | layer :: layers, acc, ps, hacc, h => by
    unfold evalLadderAux at h
    dsimp only at h
    split_ifs at h with hinc
    · cases hly : evalLayer 18 (acc.drop (acc.length - 16)) layer with
      | none => simp [hly] at h
      | some newPs =>
        rw [hly] at h
        have hwnd_nd := nodup_of_isStrictlyIncreasing hinc
        have hwnd_f : ∀ q ∈ acc.drop (acc.length - 16), ForcedCase2 q := fun q hq =>
          hacc q (List.mem_of_mem_drop hq)
        have hnew_f := evalLayer_case2_sound hwnd_nd hwnd_f hly
        refine evalLadderAux_case2_sound (fun q hq => ?_) h
        rcases List.mem_append.mp hq with h1 | h2
        · exact hacc q h1
        · exact hnew_f q h2

/-- Soundness of `evalLadder 12`: produces a duplicate-free list of `ForcedCase1` primes. -/
theorem evalLadder_case1_sound {layers : List (List LadderStep)} {ps : List ℕ}
    (h : evalLadder 12 layers = some ps) :
    ps.Nodup ∧ ∀ p ∈ ps, ForcedCase1 p :=
  evalLadderAux_case1_sound (by simp) h

/-- Soundness of `evalLadder 18`: produces a duplicate-free list of `ForcedCase2` primes. -/
theorem evalLadder_case2_sound {layers : List (List LadderStep)} {ps : List ℕ}
    (h : evalLadder 18 layers = some ps) :
    ps.Nodup ∧ ∀ p ∈ ps, ForcedCase2 p :=
  evalLadderAux_case2_sound (by simp) h

/-! ## Chunk Slicing & Bit-Sum Certificate Construction -/

/-- Partition `ps` into chunks according to `(count, bitBound)` pairs `specs`. -/
def splitChunks : List (ℕ × ℕ) → List ℕ → Option (List (List ℕ × ℕ))
  | [], [] => some []
  | [], _ :: _ => none
  | (cnt, bc) :: specs, ps =>
    if Nat.ble cnt ps.length then
      match splitChunks specs (ps.drop cnt) with
      | some cs => some ((ps.take cnt, bc) :: cs)
      | none => none
    else
      none

/-- Pure-`Bool` check that `2 ^ bc ≤ (c.prod) ^ 2` for every `(c, bc) ∈ cs`. -/
def checkChunks : List (List ℕ × ℕ) → Bool
  | [] => true
  | (c, bc) :: cs => Nat.ble (2 ^ bc) (c.prod ^ 2) && checkChunks cs

/-- End-to-end pure-`Bool` Case I / Case II ladder & bit-sum verifier. -/
def checkCaseLadder (allowedMult2 b0 p10 q10 targetDigits : ℕ)
    (layers : List (List LadderStep)) (specs : List (ℕ × ℕ)) : Bool :=
  Nat.ble 1 q10 &&
  Nat.ble 1 targetDigits &&
  Nat.ble (10 ^ p10 + 1) (2 ^ q10) &&
  match evalLadder allowedMult2 layers with
  | none => false
  | some ps =>
    match splitChunks specs ps with
    | none => false
    | some cs =>
      checkChunks cs &&
      Nat.ble targetDigits (p10 * (b0 + (cs.map Prod.snd).sum) / q10)

theorem splitChunks_flatten :
    ∀ {specs : List (ℕ × ℕ)} {ps : List ℕ} {cs : List (List ℕ × ℕ)},
      splitChunks specs ps = some cs → (cs.map Prod.fst).flatten = ps
  | [], [], cs, h => by
    simp [splitChunks] at h
    subst h
    rfl
  | [], _ :: _, _, h => by simp [splitChunks] at h
  | (cnt, bc) :: specs, ps, cs, h => by
    unfold splitChunks at h
    cases hlen : Nat.ble cnt ps.length
    · simp [hlen] at h
    · simp only [hlen, ↓reduceIte] at h
      cases hrest : splitChunks specs (ps.drop cnt) with
      | none => simp [hrest] at h
      | some cs' =>
        simp [hrest] at h
        subst h
        simp only [List.map_cons, List.flatten_cons]
        rw [splitChunks_flatten hrest, List.take_append_drop]

private theorem mem_flatten_of_fin_get {cs : List (List ℕ × ℕ)} (i : Fin cs.length)
    {x : ℕ} (hx : x ∈ (cs[i.val]).1) :
    x ∈ (cs.map Prod.fst).flatten := by
  induction cs with
  | nil => exact Fin.elim0 i
  | cons hd tl ih =>
    rcases i with ⟨_ | j, hj⟩
    · simp only [List.getElem_cons_zero, List.map_cons, List.flatten_cons] at hx ⊢
      exact List.mem_append_left _ hx
    · simp only [List.getElem_cons_succ, List.map_cons, List.flatten_cons] at hx ⊢
      exact List.mem_append_right _ (ih ⟨j, Nat.lt_of_succ_lt_succ hj⟩ hx)

private theorem nodup_and_disjoint_of_flatten_nodup :
    ∀ {cs : List (List ℕ × ℕ)},
      (cs.map Prod.fst).flatten.Nodup →
      (∀ i : Fin cs.length, (cs[i.val]).1.Nodup) ∧
        (∀ i j : Fin cs.length, i ≠ j →
          Disjoint (cs[i.val]).1.toFinset (cs[j.val]).1.toFinset)
  | [], _ => ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | (c0, b0) :: tl, hnd => by
    simp only [List.map_cons, List.flatten_cons] at hnd
    have hnd_c0 : c0.Nodup := hnd.sublist (List.sublist_append_left c0 _)
    have hnd_tl : (tl.map Prod.fst).flatten.Nodup :=
      hnd.sublist (List.sublist_append_right c0 _)
    have hdisj_head : ∀ x ∈ c0, x ∉ (tl.map Prod.fst).flatten :=
      fun x hx0 hxtl => (List.nodup_append.mp hnd).2.2 x hx0 x hxtl rfl
    have ⟨ih_nd, ih_disj⟩ := nodup_and_disjoint_of_flatten_nodup hnd_tl
    refine ⟨?_, ?_⟩
    · intro i
      rcases i with ⟨_ | i', hi'⟩
      · exact hnd_c0
      · exact ih_nd ⟨i', Nat.lt_of_succ_lt_succ hi'⟩
    · intro i j hij
      rcases i with ⟨_ | i', hi'⟩ <;> rcases j with ⟨_ | j', hj'⟩
      · exact absurd (Fin.ext rfl) hij
      · rw [Finset.disjoint_left]
        intro x hx0 hxj
        simp only [List.getElem_cons_zero, List.mem_toFinset] at hx0
        simp only [List.getElem_cons_succ, List.mem_toFinset] at hxj
        exact hdisj_head x hx0 (mem_flatten_of_fin_get ⟨j', Nat.lt_of_succ_lt_succ hj'⟩ hxj)
      · rw [Finset.disjoint_right]
        intro x hx0 hxi
        simp only [List.getElem_cons_zero, List.mem_toFinset] at hx0
        simp only [List.getElem_cons_succ, List.mem_toFinset] at hxi
        exact hdisj_head x hx0 (mem_flatten_of_fin_get ⟨i', Nat.lt_of_succ_lt_succ hi'⟩ hxi)
      · have hij' : (⟨i', Nat.lt_of_succ_lt_succ hi'⟩ : Fin tl.length) ≠
            ⟨j', Nat.lt_of_succ_lt_succ hj'⟩ := by
          intro heq
          apply hij
          exact Fin.ext (by simpa using congrArg Fin.val heq)
        exact ih_disj _ _ hij'

private theorem checkChunks_get :
    ∀ {cs : List (List ℕ × ℕ)},
      checkChunks cs = true →
      ∀ i : Fin cs.length, 2 ^ (cs[i.val]).2 ≤ ((cs[i.val]).1.prod) ^ 2
  | [], _, i => Fin.elim0 i
  | (c0, b0) :: tl, h, i => by
    simp only [checkChunks, Bool.and_eq_true, Nat.ble_eq] at h
    rcases i with ⟨_ | j, hj⟩
    · exact h.1
    · exact checkChunks_get h.2 ⟨j, Nat.lt_of_succ_lt_succ hj⟩

private theorem fin_sum_snd_eq_list_sum :
    ∀ (cs : List (List ℕ × ℕ)),
      (∑ i : Fin cs.length, (cs[i.val]).2) = (cs.map Prod.snd).sum
  | [] => by simp
  | (c0, b0) :: tl => by
    change (∑ i : Fin (tl.length + 1), (((c0, b0) :: tl)[i.val]).2) = _
    rw [Fin.sum_univ_succ, List.map_cons, List.sum_cons]
    simp only [Fin.val_zero, List.getElem_cons_zero, Fin.val_succ, List.getElem_cons_succ]
    rw [fin_sum_snd_eq_list_sum tl]

/-- Existence of a valid `Case1Certificate` with `targetDigits ≤ cert.digits` from a verified
Case I ladder `checkCaseLadder 12 ... = true`. (Proof-irrelevant `Prop` avoids re-evaluating
`evalLadder` during downstream elaboration.) -/
theorem exists_case1Certificate_of_ladder {b0 p10 q10 targetDigits : ℕ}
    {layers : List (List LadderStep)} {specs : List (ℕ × ℕ)}
    (hb0 : 2 ^ b0 ≤ 4 * 9)
    (hcheck : checkCaseLadder 12 b0 p10 q10 targetDigits layers specs = true) :
    ∃ cert : Case1Certificate, targetDigits ≤ cert.digits := by
  unfold checkCaseLadder at hcheck
  simp only [Bool.and_eq_true, Nat.ble_eq] at hcheck
  rcases hcheck with ⟨⟨⟨hq10, _⟩, hlog⟩, hrest⟩
  cases hev : evalLadder 12 layers with
  | none => rw [hev] at hrest; simp at hrest
  | some ps =>
    rw [hev] at hrest
    dsimp only at hrest
    cases hsp : splitChunks specs ps with
    | none => rw [hsp] at hrest; simp at hrest
    | some cs =>
      rw [hsp] at hrest
      dsimp only at hrest
      simp only [Bool.and_eq_true, Nat.ble_eq] at hrest
      rcases hrest with ⟨hchk, hdig⟩
      have ⟨hps_nd, hps_f⟩ := evalLadder_case1_sound hev
      have hflat := splitChunks_flatten hsp
      have hflat_nd : (cs.map Prod.fst).flatten.Nodup := by rwa [hflat]
      have ⟨hcs_nd, hcs_disj⟩ := nodup_and_disjoint_of_flatten_nodup hflat_nd
      refine ⟨{
        ι := Fin cs.length
        chunks := Finset.univ
        chunkPrimes := fun i => (cs[i.val]).1.toFinset
        pairwiseDisjoint := fun i _ j _ hij => hcs_disj i j hij
        allForced := fun i _ p hp => by
          have hmem : p ∈ (cs.map Prod.fst).flatten :=
            mem_flatten_of_fin_get i (List.mem_toFinset.mp hp)
          rw [hflat] at hmem
          exact hps_f p hmem
        b0 := b0
        hb0 := hb0
        bc := fun i => (cs[i.val]).2
        hbc := fun i _ => by
          rw [prod_toFinset_eq_list_prod (hcs_nd i)]
          exact checkChunks_get hchk i
        p10 := p10
        q10 := q10
        hq10 := hq10
        hlog := by omega
      }, ?_⟩
      unfold Case1Certificate.digits
      dsimp only
      rw [fin_sum_snd_eq_list_sum cs]
      exact hdig

/-- Existence of a valid `Case2Certificate` with `targetDigits ≤ cert.digits` from a verified
Case II ladder `checkCaseLadder 18 ... = true`. -/
theorem exists_case2Certificate_of_ladder {b0 p10 q10 targetDigits : ℕ}
    {layers : List (List LadderStep)} {specs : List (ℕ × ℕ)}
    (hb0 : 2 ^ b0 ≤ 4 * 27)
    (hcheck : checkCaseLadder 18 b0 p10 q10 targetDigits layers specs = true) :
    ∃ cert : Case2Certificate, targetDigits ≤ cert.digits := by
  unfold checkCaseLadder at hcheck
  simp only [Bool.and_eq_true, Nat.ble_eq] at hcheck
  rcases hcheck with ⟨⟨⟨hq10, _⟩, hlog⟩, hrest⟩
  cases hev : evalLadder 18 layers with
  | none => rw [hev] at hrest; simp at hrest
  | some ps =>
    rw [hev] at hrest
    dsimp only at hrest
    cases hsp : splitChunks specs ps with
    | none => rw [hsp] at hrest; simp at hrest
    | some cs =>
      rw [hsp] at hrest
      dsimp only at hrest
      simp only [Bool.and_eq_true, Nat.ble_eq] at hrest
      rcases hrest with ⟨hchk, hdig⟩
      have ⟨hps_nd, hps_f⟩ := evalLadder_case2_sound hev
      have hflat := splitChunks_flatten hsp
      have hflat_nd : (cs.map Prod.fst).flatten.Nodup := by rwa [hflat]
      have ⟨hcs_nd, hcs_disj⟩ := nodup_and_disjoint_of_flatten_nodup hflat_nd
      refine ⟨{
        ι := Fin cs.length
        chunks := Finset.univ
        chunkPrimes := fun i => (cs[i.val]).1.toFinset
        pairwiseDisjoint := fun i _ j _ hij => hcs_disj i j hij
        allForced := fun i _ p hp => by
          have hmem : p ∈ (cs.map Prod.fst).flatten :=
            mem_flatten_of_fin_get i (List.mem_toFinset.mp hp)
          rw [hflat] at hmem
          exact hps_f p hmem
        b0 := b0
        hb0 := hb0
        bc := fun i => (cs[i.val]).2
        hbc := fun i _ => by
          rw [prod_toFinset_eq_list_prod (hcs_nd i)]
          exact checkChunks_get hchk i
        p10 := p10
        q10 := q10
        hq10 := hq10
        hlog := by omega
      }, ?_⟩
      unfold Case2Certificate.digits
      dsimp only
      rw [fin_sum_snd_eq_list_sum cs]
      exact hdig

/-! ## Unconditional 161-Prime `10 ^ 10,117 < x` Pure-Kernel Certificate Data -/

/-- 6-layer Case I bitmask Lucas ladder (81 primes up to 469 bits, 34,024 total square-product
bits, 10,240 base-10 digits via `10 ^ 31 < 2 ^ 103`). -/
def case1Layers10000 : List (List LadderStep) :=
  [
    [⟨6, 0, 3⟩, ⟨12, 0, 2⟩],
    [⟨6, 1, 3⟩, ⟨6, 2, 3⟩, ⟨12, 2, 5⟩, ⟨6, 3, 2⟩],
    [⟨12, 3, 5⟩, ⟨6, 9, 6⟩, ⟨12, 5, 2⟩, ⟨6, 10, 3⟩, ⟨12, 9, 2⟩, ⟨12, 6, 2⟩, ⟨6, 20, 2⟩,
     ⟨6, 34, 7⟩],
    [⟨6, 2208, 3⟩, ⟨6, 704, 3⟩, ⟨6, 12290, 3⟩, ⟨6, 10248, 3⟩, ⟨6, 2240, 2⟩, ⟨12, 10244, 2⟩,
     ⟨6, 8288, 3⟩, ⟨6, 6160, 2⟩, ⟨12, 704, 2⟩, ⟨12, 2240, 6⟩, ⟨12, 3104, 2⟩, ⟨12, 1344, 5⟩,
     ⟨6, 4384, 3⟩, ⟨6, 2432, 3⟩, ⟨12, 1600, 5⟩, ⟨6, 9248, 3⟩],
    [⟨12, 16401, 2⟩, ⟨12, 532, 7⟩, ⟨12, 1044, 2⟩, ⟨6, 1544, 10⟩, ⟨12, 2082, 2⟩,
     ⟨12, 1072, 2⟩, ⟨12, 8202, 7⟩, ⟨6, 9220, 6⟩, ⟨12, 8258, 2⟩, ⟨12, 416, 2⟩, ⟨6, 5136, 6⟩,
     ⟨12, 4144, 2⟩, ⟨12, 16420, 2⟩, ⟨6, 2816, 3⟩, ⟨6, 32898, 3⟩, ⟨6, 32928, 3⟩],
    [⟨6, 545, 3⟩, ⟨12, 56, 2⟩, ⟨6, 336, 3⟩, ⟨6, 352, 3⟩, ⟨12, 1030, 6⟩, ⟨6, 12296, 6⟩,
     ⟨6, 16641, 2⟩, ⟨12, 578, 2⟩, ⟨12, 388, 2⟩, ⟨6, 6656, 3⟩, ⟨6, 24608, 3⟩, ⟨12, 8708, 2⟩,
     ⟨12, 9232, 6⟩, ⟨12, 18440, 2⟩, ⟨12, 40968, 2⟩, ⟨12, 16768, 2⟩, ⟨12, 25088, 2⟩,
     ⟨6, 531, 3⟩, ⟨6, 402, 2⟩, ⟨6, 1556, 2⟩, ⟨12, 1062, 6⟩, ⟨6, 10258, 2⟩, ⟨6, 9252, 6⟩,
     ⟨6, 708, 2⟩, ⟨12, 8234, 2⟩, ⟨6, 720, 2⟩, ⟨6, 32901, 6⟩, ⟨6, 32908, 2⟩, ⟨6, 16664, 3⟩,
     ⟨6, 6658, 3⟩, ⟨12, 2186, 10⟩, ⟨12, 1289, 2⟩, ⟨6, 8592, 5⟩, ⟨12, 3096, 2⟩, ⟨12, 5154, 6⟩]
  ]

/-- 11-chunk bit-length specification for `case1Layers10000`. -/
def case1Chunks10000 : List (ℕ × ℕ) :=
  [(8, 112), (8, 307), (8, 598), (8, 928), (8, 1858), (8, 2805),
   (8, 5629), (8, 5878), (8, 7480), (8, 7488), (1, 936)]

/-- 6-layer Case II bitmask Lucas ladder (80 primes up to 470 bits, 33,616 total square-product
bits, 10,117 base-10 digits via `10 ^ 31 < 2 ^ 103`). -/
def case2Layers10000 : List (List LadderStep) :=
  [
    [⟨6, 0, 3⟩, ⟨18, 0, 2⟩],
    [⟨6, 1, 3⟩, ⟨18, 1, 3⟩],
    [⟨18, 8, 19⟩, ⟨6, 6, 3⟩, ⟨18, 5, 3⟩, ⟨6, 10, 3⟩, ⟨18, 12, 2⟩, ⟨6, 11, 2⟩, ⟨18, 11, 3⟩,
     ⟨18, 13, 5⟩],
    [⟨18, 266, 3⟩, ⟨18, 1033, 13⟩, ⟨6, 162, 3⟩, ⟨6, 640, 3⟩, ⟨6, 578, 2⟩, ⟨18, 545, 3⟩,
     ⟨6, 324, 2⟩, ⟨6, 1280, 5⟩, ⟨18, 200, 3⟩, ⟨6, 2066, 5⟩, ⟨6, 1153, 5⟩, ⟨6, 2304, 6⟩,
     ⟨6, 2068, 5⟩, ⟨6, 2177, 3⟩, ⟨18, 2113, 3⟩, ⟨18, 296, 3⟩, ⟨18, 1060, 3⟩, ⟨18, 176, 6⟩],
    [⟨6, 9218, 5⟩, ⟨6, 1096, 2⟩, ⟨6, 2084, 3⟩, ⟨6, 1284, 2⟩, ⟨6, 33281, 2⟩, ⟨18, 16897, 5⟩,
     ⟨6, 2144, 2⟩, ⟨6, 17412, 3⟩, ⟨18, 656, 3⟩, ⟨18, 4144, 3⟩, ⟨6, 16544, 2⟩,
     ⟨18, 1216, 3⟩, ⟨18, 16648, 3⟩, ⟨18, 4288, 6⟩, ⟨18, 4416, 3⟩, ⟨6, 18448, 2⟩],
    [⟨6, 35, 3⟩, ⟨6, 76, 3⟩, ⟨18, 14, 3⟩, ⟨6, 8202, 2⟩, ⟨6, 1060, 2⟩, ⟨6, 388, 2⟩,
     ⟨18, 193, 3⟩, ⟨6, 8321, 2⟩, ⟨6, 3074, 2⟩, ⟨6, 34817, 2⟩, ⟨18, 8708, 3⟩, ⟨18, 1296, 3⟩,
     ⟨18, 36866, 3⟩, ⟨18, 3088, 3⟩, ⟨6, 9728, 3⟩, ⟨6, 16409, 3⟩, ⟨6, 16410, 6⟩,
     ⟨6, 16426, 3⟩, ⟨18, 284, 2⟩, ⟨18, 2089, 3⟩, ⟨18, 550, 2⟩, ⟨6, 2148, 11⟩,
     ⟨18, 2118, 5⟩, ⟨6, 20492, 3⟩, ⟨6, 786, 6⟩, ⟨6, 40965, 3⟩, ⟨18, 4229, 2⟩,
     ⟨6, 2242, 15⟩, ⟨6, 2370, 3⟩, ⟨18, 16518, 2⟩, ⟨18, 16522, 2⟩, ⟨18, 785, 5⟩,
     ⟨6, 34881, 3⟩, ⟨18, 12305, 2⟩]
  ]

/-- 10-chunk bit-length specification for `case2Layers10000`. -/
def case2Chunks10000 : List (ℕ × ℕ) :=
  [(8, 138), (8, 401), (8, 593), (8, 932), (8, 1855),
   (8, 2800), (8, 5610), (8, 6331), (8, 7462), (8, 7488)]

section KernelEval

set_option exponentiation.threshold 16384
set_option maxRecDepth 100000

/-- Pure-kernel evaluation of the 81-prime Case I ladder (`10,240` digits). -/
theorem check_case1_10240 :
    checkCaseLadder 12 5 31 103 10240 case1Layers10000 case1Chunks10000 = true := by
  decide

/-- Pure-kernel evaluation of the 80-prime Case II ladder (`10,117` digits). -/
theorem check_case2_10117 :
    checkCaseLadder 18 6 31 103 10117 case2Layers10000 case2Chunks10000 = true := by
  decide

end KernelEval

/-- Existence of a multi-chunk `Case1Certificate` with `10240 ≤ cert.digits`. -/
theorem exists_masaiValetteCase1Cert :
    ∃ cert : Case1Certificate, 10240 ≤ cert.digits :=
  exists_case1Certificate_of_ladder (by decide : 2 ^ 5 ≤ 4 * 9) check_case1_10240

/-- Existence of a multi-chunk `Case2Certificate` with `10117 ≤ cert.digits`. -/
theorem exists_masaiValetteCase2Cert :
    ∃ cert : Case2Certificate, 10117 ≤ cert.digits :=
  exists_case2Certificate_of_ladder (by decide : 2 ^ 6 ≤ 4 * 27) check_case2_10117

/-- Verified multi-chunk Case I certificate achieving `10,240` digits. -/
noncomputable def masaiValetteCase1Cert : Case1Certificate :=
  Classical.choose exists_masaiValetteCase1Cert

theorem masaiValetteCase1Cert_digits_ge : 10240 ≤ masaiValetteCase1Cert.digits :=
  Classical.choose_spec exists_masaiValetteCase1Cert

/-- Verified multi-chunk Case II certificate achieving `10,117` digits. -/
noncomputable def masaiValetteCase2Cert : Case2Certificate :=
  Classical.choose exists_masaiValetteCase2Cert

theorem masaiValetteCase2Cert_digits_ge : 10117 ≤ masaiValetteCase2Cert.digits :=
  Classical.choose_spec exists_masaiValetteCase2Cert

/-- Concrete 161-prime `CarmichaelBoundCertificate` unconditionally verified in the Lean 4
kernel (`digits ≥ 10,117`), surpassing both Klee (1947, `10 ^ 400`) and Masai & Valette
(1982, `10 ^ 10,000`). -/
noncomputable def masaiValette1982Certificate : CarmichaelBoundCertificate where
  case1 := masaiValetteCase1Cert
  case2 := masaiValetteCase2Cert

theorem masaiValette1982Certificate_digits_ge :
    10117 ≤ masaiValette1982Certificate.digits := by
  unfold CarmichaelBoundCertificate.digits masaiValette1982Certificate
  exact le_min (le_trans (by decide : 10117 ≤ 10240) masaiValetteCase1Cert_digits_ge)
    masaiValetteCase2Cert_digits_ge

private theorem ten_pow_le_ten_pow {m n : ℕ} (h : m ≤ n) : (10 : ℕ) ^ m ≤ (10 : ℕ) ^ n :=
  Nat.pow_le_pow_right (by decide : 0 < 10) h

/-- Unconditional Case I bound (`¬ 27 ∣ x`): `10 ^ 10240 < x`. -/
theorem carmichael_case1_gt_10_pow_10240 {x : ℕ}
    (hx : IsCarmichaelCounterexample x) (h27 : ¬ 27 ∣ x) :
    10 ^ 10240 < x := by
  rcases exists_masaiValetteCase1Cert with ⟨cert, hge⟩
  have hD : 0 < cert.digits := lt_of_lt_of_le (by decide : 0 < 10240) hge
  have hS : ∀ p ∈ cert.chunks.biUnion cert.chunkPrimes,
      Nat.Prime p ∧ 5 ≤ p ∧ p ^ 2 ∣ x := by
    intro p hp
    rcases Finset.mem_biUnion.mp hp with ⟨c, hc, hpc⟩
    exact forcedCase1_sound hx h27 (cert.allForced c hc p hpc)
  have hdvd : (4 * 9) * (∏ c ∈ cert.chunks,
      (∏ p ∈ cert.chunkPrimes c, p) ^ 2) ∣ x := by
    rw [prod_chunk_sq_eq_biUnion cert.chunks cert.chunkPrimes cert.pairwiseDisjoint]
    exact base_mul_prod_sq_dvd_case1 hx _ hS
  exact lt_of_le_of_lt (ten_pow_le_ten_pow hge)
    (digit_bound_strict_of_bit_sum hx.1 hdvd cert.hb0 cert.hbc cert.hq10 cert.hlog hD)

/-- Unconditional Case II bound (`27 ∣ x`): `10 ^ 10117 < x`. -/
theorem carmichael_case2_gt_10_pow_10117 {x : ℕ}
    (hx : IsCarmichaelCounterexample x) (h27 : 27 ∣ x) :
    10 ^ 10117 < x := by
  rcases exists_masaiValetteCase2Cert with ⟨cert, hge⟩
  have hD : 0 < cert.digits := lt_of_lt_of_le (by decide : 0 < 10117) hge
  have hS : ∀ p ∈ cert.chunks.biUnion cert.chunkPrimes,
      Nat.Prime p ∧ 5 ≤ p ∧ p ^ 2 ∣ x := by
    intro p hp
    rcases Finset.mem_biUnion.mp hp with ⟨c, hc, hpc⟩
    exact forcedCase2_sound hx h27 (cert.allForced c hc p hpc)
  have hdvd : (4 * 27) * (∏ c ∈ cert.chunks,
      (∏ p ∈ cert.chunkPrimes c, p) ^ 2) ∣ x := by
    rw [prod_chunk_sq_eq_biUnion cert.chunks cert.chunkPrimes cert.pairwiseDisjoint]
    exact base_mul_prod_sq_dvd_case2 hx h27 _ hS
  exact lt_of_le_of_lt (ten_pow_le_ten_pow hge)
    (digit_bound_strict_of_bit_sum hx.1 hdvd cert.hb0 cert.hbc cert.hq10 cert.hlog hD)

/-- **Unconditional 10,117-digit Carmichael lower bound** (`10 ^ 10117 < x`), proved directly
inside the Lean 4 kernel via `carmichael_bound_strict_from_certificate` with zero `native_decide`. -/
theorem carmichael_counterexample_gt_10_pow_10117 {x : ℕ}
    (hx : IsCarmichaelCounterexample x) :
    10 ^ 10117 < x := by
  have hge := masaiValette1982Certificate_digits_ge
  have hpos : 0 < masaiValette1982Certificate.digits :=
    lt_of_lt_of_le (by decide : 0 < 10117) hge
  exact lt_of_le_of_lt (ten_pow_le_ten_pow hge)
    (carmichael_bound_strict_from_certificate masaiValette1982Certificate hpos hx)

/-- **Unconditional `10 ^ 10,000 < x` lower bound** (Masai & Valette 1982 milestone, proved
unconditionally in the Lean 4 kernel with zero `native_decide`). -/
theorem carmichael_counterexample_gt_10_pow_10000 {x : ℕ}
    (hx : IsCarmichaelCounterexample x) :
    10 ^ 10000 < x :=
  lt_of_le_of_lt (ten_pow_le_ten_pow (by decide : 10000 ≤ 10117))
    (carmichael_counterexample_gt_10_pow_10117 hx)

/-- **Unconditional `10 ^ 1,000 < x` lower bound** (`2.5×` Klee 1947's digit bound). -/
theorem carmichael_counterexample_gt_10_pow_1000 {x : ℕ}
    (hx : IsCarmichaelCounterexample x) :
    10 ^ 1000 < x :=
  lt_of_le_of_lt (ten_pow_le_ten_pow (by decide : 1000 ≤ 10117))
    (carmichael_counterexample_gt_10_pow_10117 hx)

/-- **Unconditional Klee (1947) `10 ^ 400 < x` lower bound**. -/
theorem carmichael_counterexample_gt_10_pow_400 {x : ℕ}
    (hx : IsCarmichaelCounterexample x) :
    10 ^ 400 < x :=
  lt_of_le_of_lt (ten_pow_le_ten_pow (by decide : 400 ≤ 10117))
    (carmichael_counterexample_gt_10_pow_10117 hx)

end CarmichaelTotient
