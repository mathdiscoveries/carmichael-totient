# Carmichael's Totient Conjecture: Kernel-Verified `10^10,117 < x`, Structural Theory, and Ford's `k = 10` Lower Bound

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24490744.svg)](https://doi.org/10.5281/zenodo.24490744)

Unconditional Lean 4 (`v4.35.0`) + Mathlib formalization proving:

- **`10^10,117 < x`** unconditionally for every counterexample `x` to Carmichael's totient conjecture (`10^10,240 < x` in Case I, `10^10,117 < x` in Case II) via 161 kernel-checked Lucas primality ladders (surpassing Masai and Valette's 1982 bound `10^10,000` purely inside the Lean 4 kernel).
- **Ford's Lemma 7.2** prime-square forcing rule, **Klee's (1947)** minimal-counterexample structure (`4 ∣ x₀`, `¬ 8 ∣ x₀`, exclusion of Fermat primes `5, 17, 257, 65537`), and **Pomerance's (1974)** sufficient condition.
- **Ford's (§7.3) divisible-preimage problem**: reduction of Carmichael's conjecture to `k = 6` and the unconditional lower bound **`32,000 ≤ m`** when every positive preimage of `m` is divisible by `10`.
- **Totient value & singleton density transfer**: reciprocal-sum transfer (`totient_value_gt_of_forced_primes`), Ford's Lemmas 7.4–7.5 (`ford_lemma_7_4_7_5`), general limiting density bound (`liminf_V1_div_V_le_two_div_min`), and the unconditional pure-kernel bound **`liminf V₁(X)/V(X) < 10^(-5,057)`** (`carmichael_liminf_density_lt_10_pow_neg_5057`).
- **Concrete grounding witnesses**: `φ(y) = 10 ↔ y ∈ {11, 22}` and `IsDivisibleTotientWitness 11 110`.

All proofs use only Lean's three standard axioms (`propext`, `Quot.sound`, `Classical.choice`), with zero `sorry` and zero `native_decide`. The library also formalizes the certificate soundness bridges (`CarmichaelBoundCertificate`, `K10RungCertificate`) used by the companion manuscript's larger external exact-integer bounds (`10^100,000,160,994` and `10^60`), documented at https://mathdiscoveries.org/results/carmichael-totient.

## Build & Verify

```bash
lake build Challenge Solution CarmichaelTotient
lake env lean CarmichaelTotient/Verify.lean
lake comparator --paranoid --inadvisably-no-sandbox
```
