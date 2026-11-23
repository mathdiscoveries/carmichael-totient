module

public import CarmichaelTotient

/-!
# Axiom Verification Audit for `CarmichaelTotient`

Prints the Lean 4 kernel axioms used by every formalized theorem, lemma,
proposition, and corollary in `CarmichaelTotient`. A clean audit must show ONLY
Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — NEVER
`sorryAx`, `Lean.ofReduceBool`, `Lean.trustCompiler`, or any custom axiom.
-/

-- Core definitions and Ford's Lemma 7.2 (Lemma72.lean)
#print axioms CarmichaelTotient.totient_even_of_ge_three
#print axioms CarmichaelTotient.totient_two_mul_odd
#print axioms CarmichaelTotient.four_dvd_counterexample
#print axioms CarmichaelTotient.rad_pos
#print axioms CarmichaelTotient.dvd_rad_of_mem_primeFactors
#print axioms CarmichaelTotient.rad_dvd_self
#print axioms CarmichaelTotient.totient_mul_of_primes_dvd
#print axioms CarmichaelTotient.totient_div_of_dvd_div_rad
#print axioms CarmichaelTotient.prime_dvd_of_ford_7_2
#print axioms CarmichaelTotient.prime_sq_dvd_of_pred_primes_dvd
#print axioms CarmichaelTotient.prime_sq_dvd_of_ford_7_2
#print axioms CarmichaelTotient.ford_lemma_7_2

-- First forced squares, Case I/II step rules, bit-sum soundness, and certificate bridge (CaseRules.lean)
#print axioms CarmichaelTotient.dvd_div_rad_of_mul_rad_dvd
#print axioms CarmichaelTotient.finset_prod_dvd_of_nat_coprime
#print axioms CarmichaelTotient.prime_pow_dvd_div_rad
#print axioms CarmichaelTotient.prod_primes_dvd_div_rad
#print axioms CarmichaelTotient.coprime_of_primes_ge_five
#print axioms CarmichaelTotient.rad_one
#print axioms CarmichaelTotient.rad_six
#print axioms CarmichaelTotient.nine_dvd_counterexample
#print axioms CarmichaelTotient.fortynine_dvd_counterexample
#print axioms CarmichaelTotient.fortythree_sq_dvd_counterexample
#print axioms CarmichaelTotient.d_one_chain_closed
#print axioms CarmichaelTotient.step_6k_plus_1
#print axioms CarmichaelTotient.step_case1_12k_plus_1
#print axioms CarmichaelTotient.step_case2_18k_plus_1
#print axioms CarmichaelTotient.thirteen_sq_dvd_case1
#print axioms CarmichaelTotient.carmichael_case_split
#print axioms CarmichaelTotient.forcedCase1_sound
#print axioms CarmichaelTotient.forcedCase2_sound
#print axioms CarmichaelTotient.base_mul_prod_sq_dvd_case1
#print axioms CarmichaelTotient.base_mul_prod_sq_dvd_case2
#print axioms CarmichaelTotient.base_mul_prod_sq_dvd
#print axioms CarmichaelTotient.prod_chunk_sq_eq_biUnion
#print axioms CarmichaelTotient.two_pow_log2_le_self
#print axioms CarmichaelTotient.digit_bound_of_bit_sum
#print axioms CarmichaelTotient.digit_bound_strict_of_bit_sum
#print axioms CarmichaelTotient.prime_of_lucas_witnesses
#print axioms CarmichaelTotient.case1_bound_from_certificate
#print axioms CarmichaelTotient.case2_bound_from_certificate
#print axioms CarmichaelTotient.carmichael_bound_from_certificate
#print axioms CarmichaelTotient.carmichael_bound_strict_from_certificate

-- Unconditional Carmichael (1922) lower bound and concrete certificate witness (Carmichael1922.lean)
#print axioms CarmichaelTotient.modPowAux_eq
#print axioms CarmichaelTotient.modPowFuel_eq
#print axioms CarmichaelTotient.mem_of_prime_dvd_list_prod
#print axioms CarmichaelTotient.prime_of_pratt_cert
#print axioms CarmichaelTotient.prime_7
#print axioms CarmichaelTotient.prime_13
#print axioms CarmichaelTotient.prime_19
#print axioms CarmichaelTotient.prime_43
#print axioms CarmichaelTotient.prime_79
#print axioms CarmichaelTotient.prime_127
#print axioms CarmichaelTotient.prime_547
#print axioms CarmichaelTotient.prime_2287
#print axioms CarmichaelTotient.prime_3319
#print axioms CarmichaelTotient.prime_101347
#print axioms CarmichaelTotient.prime_304039
#print axioms CarmichaelTotient.prime_1854763
#print axioms CarmichaelTotient.forcedCase1_7
#print axioms CarmichaelTotient.forcedCase1_43
#print axioms CarmichaelTotient.forcedCase1_13
#print axioms CarmichaelTotient.forcedCase1_79
#print axioms CarmichaelTotient.forcedCase1_547
#print axioms CarmichaelTotient.forcedCase1_3319
#print axioms CarmichaelTotient.forcedCase1_1854763
#print axioms CarmichaelTotient.forcedCase1_carmichael1922
#print axioms CarmichaelTotient.carmichael_case1_exact_dvd
#print axioms CarmichaelTotient.carmichael_case1_ge_10_pow_37
#print axioms CarmichaelTotient.forcedCase2_7
#print axioms CarmichaelTotient.forcedCase2_43
#print axioms CarmichaelTotient.forcedCase2_19
#print axioms CarmichaelTotient.forcedCase2_127
#print axioms CarmichaelTotient.forcedCase2_2287
#print axioms CarmichaelTotient.forcedCase2_101347
#print axioms CarmichaelTotient.forcedCase2_304039
#print axioms CarmichaelTotient.forcedCase2_carmichael1922
#print axioms CarmichaelTotient.carmichael_case2_exact_dvd
#print axioms CarmichaelTotient.carmichael_case2_ge_10_pow_41
#print axioms CarmichaelTotient.carmichael_counterexample_ge_10_pow_37
#print axioms CarmichaelTotient.carmichael1922Certificate_digits
#print axioms CarmichaelTotient.carmichael_counterexample_gt_10_pow_37

-- Pomerance's criterion, Klee's reduced counterexamples, and Erdős's multiplication theorem (StructuralAndPomerance.lean)
#print axioms CarmichaelTotient.totient_factorization_eq
#print axioms CarmichaelTotient.prime_dvd_totient_iff
#print axioms CarmichaelTotient.pomerance_sufficient_condition
#print axioms CarmichaelTotient.pomerance_conjecture_excludes_pomerance_numbers
#print axioms CarmichaelTotient.isReduced_of_isMinimal
#print axioms CarmichaelTotient.exists_minimal_counterexample
#print axioms CarmichaelTotient.exists_reduced_counterexample_dvd
#print axioms CarmichaelTotient.not_eight_dvd_of_reduced
#print axioms CarmichaelTotient.exact_four_dvd_of_reduced
#print axioms CarmichaelTotient.not_fermat_prime_dvd_of_reduced
#print axioms CarmichaelTotient.fermat_primes_not_dvd_of_reduced
#print axioms CarmichaelTotient.minimal_counterexample_structure
#print axioms CarmichaelTotient.erdos_mul_prime_counterexample_iff
#print axioms CarmichaelTotient.erdos_1958_totient_fiber_eq
#print axioms CarmichaelTotient.totient_eq_ten_iff
#print axioms CarmichaelTotient.erdos_1958_counterexample_step
#print axioms CarmichaelTotient.erdos_1958_infinitude_from_sieve

-- Multi-branch valuation case trees and Ford's k = 10 divisible-preimage descent (ValuationTree.lean)
#print axioms CarmichaelTotient.exactPowDvd_or_succ_pow_dvd
#print axioms CarmichaelTotient.exactPowDvd_factorization
#print axioms CarmichaelTotient.coprime_div_of_exactPowDvd
#print axioms CarmichaelTotient.unitary_of_exactPowDvd_finset
#print axioms CarmichaelTotient.totient_prod_primes
#print axioms CarmichaelTotient.ford_product_split_counterexample
#print axioms CarmichaelTotient.ValConstraint.pow_dvd_of_holds
#print axioms CarmichaelTotient.carmichaelValuationTree_sound
#print axioms CarmichaelTotient.nineteen_sq_dvd_case2
#print axioms CarmichaelTotient.step_case2b_54k_plus_1
#print axioms CarmichaelTotient.klee_three_way_case_split
#print axioms CarmichaelTotient.no_k6_witness_implies_carmichael
#print axioms CarmichaelTotient.not_totient_odd_gt_one
#print axioms CarmichaelTotient.k11_witness_110
#print axioms CarmichaelTotient.k9_witness_54
#print axioms CarmichaelTotient.k3_witness_54
#print axioms CarmichaelTotient.k10_witness_iff
#print axioms CarmichaelTotient.k10_lemma_A
#print axioms CarmichaelTotient.k10_lemma_C_five
#print axioms CarmichaelTotient.k10_lemma_C_two
#print axioms CarmichaelTotient.k10_lemma_B
#print axioms CarmichaelTotient.k10_lemma_B2
#print axioms CarmichaelTotient.k10_round1_five_force
#print axioms CarmichaelTotient.k10_round1_two_force
#print axioms CarmichaelTotient.k10_witness_ge_32000
#print axioms CarmichaelTotient.k10_nonroot_closed
#print axioms CarmichaelTotient.k10DescentTree_sound
#print axioms CarmichaelTotient.k10_bound_from_rung_certificate
#print axioms CarmichaelTotient.k10RungCertificate_4

-- Pure-kernel unconditional 10^10,000 < x bound and Lucas ladder verifier (TreeAndKleeBounds.lean)
#print axioms CarmichaelTotient.mem_maskSublist
#print axioms CarmichaelTotient.nodup_maskSublist
#print axioms CarmichaelTotient.prod_toFinset_eq_list_prod
#print axioms CarmichaelTotient.nodup_of_isStrictlyIncreasing
#print axioms CarmichaelTotient.powFactorList_eq
#print axioms CarmichaelTotient.checkPrefixSuffix_sound
#print axioms CarmichaelTotient.prime_of_ladder_step
#print axioms CarmichaelTotient.ForcedCase1.prime
#print axioms CarmichaelTotient.ForcedCase2.prime
#print axioms CarmichaelTotient.evalStep_case1_sound
#print axioms CarmichaelTotient.evalStep_case2_sound
#print axioms CarmichaelTotient.evalLadder_case1_sound
#print axioms CarmichaelTotient.evalLadder_case2_sound
#print axioms CarmichaelTotient.splitChunks_flatten
#print axioms CarmichaelTotient.exists_case1Certificate_of_ladder
#print axioms CarmichaelTotient.exists_case2Certificate_of_ladder
#print axioms CarmichaelTotient.check_case1_10240
#print axioms CarmichaelTotient.check_case2_10117
#print axioms CarmichaelTotient.exists_masaiValetteCase1Cert
#print axioms CarmichaelTotient.exists_masaiValetteCase2Cert
#print axioms CarmichaelTotient.masaiValetteCase1Cert
#print axioms CarmichaelTotient.masaiValetteCase1Cert_digits_ge
#print axioms CarmichaelTotient.masaiValetteCase2Cert
#print axioms CarmichaelTotient.masaiValetteCase2Cert_digits_ge
#print axioms CarmichaelTotient.masaiValette1982Certificate
#print axioms CarmichaelTotient.masaiValette1982Certificate_digits_ge
#print axioms CarmichaelTotient.carmichael_case1_gt_10_pow_10240
#print axioms CarmichaelTotient.carmichael_case2_gt_10_pow_10117
#print axioms CarmichaelTotient.carmichael_counterexample_gt_10_pow_10117
#print axioms CarmichaelTotient.carmichael_counterexample_gt_10_pow_10000
#print axioms CarmichaelTotient.carmichael_counterexample_gt_10_pow_1000
#print axioms CarmichaelTotient.carmichael_counterexample_gt_10_pow_400

-- Totient value transfer, Ford's Lemmas 7.4-7.5, and singleton density bound (ValueAndDensityTransfer.lean)
#print axioms CarmichaelTotient.one_sub_sum_le_prod_one_sub
#print axioms CarmichaelTotient.totient_forcedDivisor_eq_real
#print axioms CarmichaelTotient.totient_value_gt_of_forced_primes
#print axioms CarmichaelTotient.totient_mul_of_prime_dvd
#print axioms CarmichaelTotient.totient_pow_mul_eq
#print axioms CarmichaelTotient.exists_max_pow_dvd
#print axioms CarmichaelTotient.ford_lemma_7_4_7_5
#print axioms CarmichaelTotient.V_mono
#print axioms CarmichaelTotient.primeCounting_le_V
#print axioms CarmichaelTotient.V_pos
#print axioms CarmichaelTotient.V1_le_two_mul_V_div
#print axioms CarmichaelTotient.frequently_V1_div_V_lt
#print axioms CarmichaelTotient.liminf_V1_div_V_le_two_div_min
#print axioms CarmichaelTotient.forcedCase1_prime_ge_five
#print axioms CarmichaelTotient.forcedCase2_prime_ge_five
#print axioms CarmichaelTotient.corollary_value_and_density_transfer
#print axioms CarmichaelTotient.carmichael_liminf_density_lt_10_pow_neg_5057
