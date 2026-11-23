# The Music of the Primes: issues and repairs

Hassana Labs, 23 November 2026. A review of A.&nbsp;M. Masullo's manuscript *The Music of the Primes*. Page numbers refer to the PDF of the manuscript.

The first part lists the nine results the manuscript's argument relies on and what is proved for each. The second part lists 44 issues in manuscript order, each with a description, the repair and its status, and a derivation. `LEAN_MAP.md` gives, for every result and issue, the Lean declarations involved and what each proves; `MANIFEST.tsv` locates each declaration's source file and compiler receipt.

## Contents

- [Result 1](#result-1) — §3.2.1–3.2.2: (3.2.1.7), Theorem 3.2.2.1: The finite-idelic integral of the standard test equals the finite Hecke Euler product.
- [Result 2](#result-2) — Proposition 3.2.1.3, Theorem 3.2.2.1, Theorem 3.4.1.1: The completed Hecke L-function: archimedean factors, continuation, functional equation and poles, including norm twists.
- [Result 3](#result-3) — Zero divisor (Chapters 3, 9, 13): True analytic orders of the zeros, zero counts, Hadamard-type factorisation and weighted zero summability.
- [Result 4](#result-4) — Theorem 10.2.2.1: Spectral identification: each admitted jet lies in the spectral complement E, the residue ranges exhaust E, and the closed spans agree.
- [Result 5](#result-5) — Theorems 10.3.1.1, 10.3.2.1, 10.4.2.1: Nuclearity of P A(h) on W<sub>I</sub><sup>s</sup>(C<sub>K</sub>) for both tests h = φ<sup>#</sup> and (ℓφ)<sup>#</sup>.
- [Result 6](#result-6) — (10.4.2.29)–(10.4.2.33), (10.3.2.3): The measured jet action, and trace(P A) as the multiplicity-weighted sum over admitted zeros.
- [Result 7](#result-7) — (10.4.2.20); C.3.7.1; 12.1.1.2: Cutoff trace limits, the diagonal integral equal to the trace, and the smoothed diagonal.
- [Result 8](#result-8) — Theorem 11.3.2.1, §12.4.1 (Theorem 12.4.1.1): The geometric side: shell decomposition, orbital traces, the S-local calculation and its constants, and Haar normalisations.
- [Result 9](#result-9) — §1.4.4–1.4.5: From the trace formula to the location of the zeros.
- [Issue 1](#issue-1) — §1.4.2–1.4.3, repeated in §1.8.4.3
- [Issue 2](#issue-2) — §1.4.3
- [Issue 3](#issue-3) — §1.4.4
- [Issue 4](#issue-4) — Theorem 2.2.3.4, (2.2.3.10)–(2.2.3.12), with (A.2.2.11)
- [Issue 5](#issue-5) — (3.4.3.15), Remark 3.4.3.4
- [Issue 6](#issue-6) — (6.3.2.8); proof of Theorem 7.1.4.2
- [Issue 7](#issue-7) — Theorem 7.1.4.2(1), (7.1.4.23)
- [Issue 8](#issue-8) — Lemma 9.3.1.5, (9.3.1.6)
- [Issue 9](#issue-9) — Lemma 9.3.2.4
- [Issue 10](#issue-10) — Theorem 9.3.2.6, (9.3.2.10)
- [Issue 11](#issue-11) — (10.2.1.6), (10.2.2.5), (10.3.1.4), (10.3.2.4), (11.2.0.6)
- [Issue 12](#issue-12) — Proof of Theorem 10.2.1.1
- [Issue 13](#issue-13) — Proposition 10.2.2.2, (10.2.2.8)
- [Issue 14](#issue-14) — Theorem 10.3.1.1, proof (p. 451)
- [Issue 15](#issue-15) — (10.3.1.22)
- [Issue 16](#issue-16) — Theorem 10.3.2.1
- [Issue 17](#issue-17) — (10.3.2.8)–(10.3.2.11)
- [Issue 18](#issue-18) — Lemma 10.4.1.2
- [Issue 19](#issue-19) — Lemma 10.4.1.2, proof
- [Issue 20](#issue-20) — (10.4.2.8)
- [Issue 21](#issue-21) — Theorem 10.4.2.8, (10.4.2.21)–(10.4.2.34)
- [Issue 22](#issue-22) — (10.4.2.21)–(10.4.2.23)
- [Issue 23](#issue-23) — Theorem 10.4.2.8, proof
- [Issue 24](#issue-24) — (10.4.3.1)
- [Issue 25](#issue-25) — (10.4.3.43)–(10.4.3.45)
- [Issue 26](#issue-26) — (10.4.3.47), (10.4.3.30)
- [Issue 27](#issue-27) — Proposition 11.1.1.2, Corollary 11.1.1.4
- [Issue 28](#issue-28) — (11.2.1.2), (11.2.1.4)
- [Issue 29](#issue-29) — §11.3.1, primary divisorial stratification
- [Issue 30](#issue-30) — (11.3.1.4), used in the proof of Theorem 12.5.1.1
- [Issue 31](#issue-31) — Theorem 11.3.2.1 vs Theorem 12.5.1.1; footnote in §12.4.1
- [Issue 32](#issue-32) — (11.3.2.3)
- [Issue 33](#issue-33) — Proposition 12.2.2.2(4)
- [Issue 34](#issue-34) — §12.3; proof of Theorem 12.5.1.1
- [Issue 35](#issue-35) — Theorem 12.5.1.1, (12.5.1.4)
- [Issue 36](#issue-36) — Chapter 13; §14.1.2
- [Issue 37](#issue-37) — Theorem 13.3.1.1
- [Issue 38](#issue-38) — Corollary A.5.4.3, (A.5.4.16)
- [Issue 39](#issue-39) — Proposition B.4.3.2, Definition B.4.4.1
- [Issue 40](#issue-40) — Lemmas B.4.4.8–B.4.4.9, (B.4.4.16)
- [Issue 41](#issue-41) — Lemma C.3.4.4(2)
- [Issue 42](#issue-42) — Lemma C.3.6.3(1)
- [Issue 43](#issue-43) — Proposition C.3.6.5, proof
- [Issue 44](#issue-44) — Converse argument (Chapters 3, 7, 10)

## Results the argument relies on

<a id="result-1"></a>
### Result 1 — §3.2.1–3.2.2: (3.2.1.7), Theorem 3.2.2.1

**What the argument needs.** The finite-idelic integral of the standard test equals the finite Hecke Euler product.

**What is proved.** Proved in Lean for every number field, every unitary Hecke character and Re s > 1: integrability under the Haar measure normalised on the integral units, the shell decomposition, and equality with the Euler product (`MasulloGRH.normalizedGlobalFiniteIdelicMellin`). The Euler product converges to a nonzero holomorphic function, with its log-derivative identities (`MasulloGRH.Round11F.genuineEuler_product_converges_nonzero`).

<a id="result-2"></a>
### Result 2 — Proposition 3.2.1.3, Theorem 3.2.2.1, Theorem 3.4.1.1

**What the argument needs.** The completed Hecke L-function: archimedean factors, continuation, functional equation and poles, including norm twists.

**What is proved.** Lean, for K = ℚ: completion, reflection and norm twists through Mathlib's Dirichlet and Riemann zeta functions (`MasulloGRH.dirichletNormTwist_completion`, `MasulloGRH.rationalHeckeXi_reflection`). For general K: uniqueness of a continuation from the half-plane, the full Gamma divisor, simple poles at −iτ and 1 − iτ from a functional-equation pair, and the log-derivative reflection (`MasulloGRH.Round16A.attached_archimedean_divisor`). A continuation and functional equation for K ≠ ℚ are not yet constructed.

<a id="result-3"></a>
### Result 3 — Zero divisor (Chapters 3, 9, 13)

**What the argument needs.** True analytic orders of the zeros, zero counts, Hadamard-type factorisation and weighted zero summability.

**What is proved.** Lean, for K = ℚ: finite orders, equal multiplicities for L and its completion, finitely many zeros on compacts, and zero counts by Jensen circle means (`MasulloGRH.dirichletNormTwist_order_eq_completed`, `completedDirichlet_unitBand_count_le_circleMean`). In general: a weighted counting bound gives weighted summability (`ConditionalGRHReviewD.inverse_square_summable_of_log_count`). A count bound for an L-function and a Hadamard factorisation are not yet formalized.

<a id="result-4"></a>
### Result 4 — Theorem 10.2.2.1

**What the argument needs.** Spectral identification: each admitted jet lies in the spectral complement E, the residue ranges exhaust E, and the closed spans agree.

**What is proved.** Lean, on the actual C<sub>K</sub> for every number field, every unitary character and every Haar measure: each strictly admitted jet of order below the finite order of L lies in the orthogonal complement of the closed theta span, given local Tate division on dense tests, theta continuity and the derivative interchange (`NativeTrueOrder.admitted_same_integral_riesz_converse`). With residue exhaustion supplied, the closed jet span equals that complement (`NativeTrueOrder.continuous_theta_native_space_eq`, `ConditionalB24.native_integral_spectral_eq_geometric_orthogonal`).

<a id="result-5"></a>
### Result 5 — Theorems 10.3.1.1, 10.3.2.1, 10.4.2.1

**What the argument needs.** Nuclearity of P A(h) on W<sub>I</sub><sup>s</sup>(C<sub>K</sub>) for both tests h = φ<sup>#</sup> and (ℓφ)<sup>#</sup>.

**What is proved.** A natural-language proof of the repaired bound, through a whole-window resolvent estimate. Lean: an explicit finite-level nuclear bound (D/(Re z − β))·|F|·L<sup>d</sup>, with the column and row estimates derived (`Round197H.native_finite_level_resolvent_nuclear_bound`); it is conditional on the finite traces, the character decay, and the identity of P A(h) with the R W R assembly, and that identity is not yet proved. Also proved: the cost of P∘A is at most that of the quotient operator (`Round175H.canonical_projected_nuclear_cost_le`); finite blocks for both tests on C<sub>K</sub>; and, on the actual objects, P∘A∘M is the nuclear-norm limit of the finite-source truncations whenever A∘M is nuclear (`Q.FullSourceCutoff.both_tests_full_source_nuclearNorm_tendsto`).

<a id="result-6"></a>
### Result 6 — (10.4.2.29)–(10.4.2.33), (10.3.2.3)

**What the argument needs.** The measured jet action, and trace(P A) as the multiplicity-weighted sum over admitted zeros.

**What is proved.** Lean: the binomial jet action on the actual C<sub>K</sub>, for every number field, unitary character, z and m, and for both tests (`ActualMeasuredJetD.actual_measured_jet_action`, `Round180A.genuine_required_test_convolution_pairings`); the finite-block trace n·a<sub>0</sub>; and the multiplicity-weighted zero sum equals the nuclear trace of P∘A, given a P∘A expansion and a jet-indexed basis with its flag action (`Spectral29B.genuine_projection_trace_original_nuclear_sum`).

<a id="result-7"></a>
### Result 7 — (10.4.2.20); C.3.7.1; 12.1.1.2

**What the argument needs.** Cutoff trace limits, the diagonal integral equal to the trace, and the smoothed diagonal.

**What is proved.** Lean, on the actual objects, for every finite-rank approximation E<sub>T</sub>A, both tests and every number field, with only the parameter conditions (l ≤ r, s ≥ 0, φ continuous with compact support and vanishing on norm one): the diagonal integral equals the trace, the physical-band, shell and cutoff-regime limits hold, and the approximations converge strongly to P∘A (`PIntegrated.geometric_trace_global_operator_assembly`). For the full operator, given a nuclear expansion: diagonal integral = trace and the cutoff limits in the P∘A order (`HOperatorTrace.source_compression_trace`, `FollowupD30.cutoff_PA_trace_tendsto`). The general smoothed-diagonal trace theorem is not yet formalized.

<a id="result-8"></a>
### Result 8 — Theorem 11.3.2.1, §12.4.1 (Theorem 12.4.1.1)

**What the argument needs.** The geometric side: shell decomposition, orbital traces, the S-local calculation and its constants, and Haar normalisations.

**What is proved.** Lean, on the actual objects for both tests at finite rank, with the same parameter conditions only: signed shell unfolding of the diagonal, with the shells summing absolutely and the band truncations converging (`PIntegrated.geometric_trace_global_operator_assembly`); orbital traces with the Haar scalar proved, where the orbit diagonal of the residual kernel integrates to −c·tr(P<sub>E<sub>T</sub></sub>A) with c > 0, and integrability and the measure comparison are proved rather than assumed (`HArithmeticTrace.both_tests_full_residual_originalHaar_orbital_trace`); two-sided physical limits (`FOrbitalPhysical.both_tests_originalHaar_orbital_physical_net`); the quotient measure equals c·μ for every Haar measure (`MQuotientHaar.quotientMeasure_eq_scaled_originalHaar`); local Haar measures normalised by μ<sub>v</sub>(O<sub>v</sub><sup>×</sup>) = 1 (`MasulloGRH.exists_normalized_localHaar`); and the local expression with the constants 1/2, 1/(2π) and log N(v)/μ<sub>v</sub>(O<sub>v</sub><sup>×</sup>) reduces to finitely many places (`NLocalArithmetic.both_tests_localExpression_eq_semilocal`). Not yet stated: the local value of 11.3.2.1, Theorem 12.4.1.1 as a whole, and the T → ∞ limits of the traces.

<a id="result-9"></a>
### Result 9 — §1.4.4–1.4.5

**What the argument needs.** From the trace formula to the location of the zeros.

**What is proved.** Lean: the strip-limit endpoint, where an entire function with an O(R log R) zero count and equal strip limits across widths has all its zeros on Re = ½ (`ConditionalReviewC.entire_zeros_on_line_from_concrete_strip_limits`); the continuation endpoint of §1.4.5 (`CriticalLine21F.critical_line_of_regularized_trace_germs_and_functional_equation`); the §1.4.4 limit −L′<sub>f</sub>/L<sub>f</sub> for every number field (`Round14F.genuineEuler_primePower_cutoff_uniform`); and, for K = ℚ, Chapter 13 correction control equivalent to RH (`ManuscriptRH.chapter13_paired_control_iff_riemannHypothesis`). The strip equality these endpoints take as input is equivalent to the conclusion (see the Theorem 12.5.1.1 row below).


## Issues

<a id="issue-1"></a>
### Issue 1 — §1.4.2–1.4.3, repeated in §1.8.4.3

**Issue.** The archimedean integrals for the one-sided cutoff family are said to share a common bound. At the real place they grow like ∫dt/(t − 1) as the cutoffs approach norm one (F = ℚ, trivial character, real z > 1), so the Montel step has no uniform bound to use.

**Repair and status.** Repair: subtract a fixed reference value (or a counterterm), or use the logarithmic test. Lean: the divergence is proved (`MasulloGRH.realPlaceKernel_integrals_unbounded`); the reference-subtracted family converges uniformly at both real-place branches, with a limit holomorphic on Re z > −½ (`CriticalLineAudit.realPlaceLogDifference_full_tendstoUniformlyOn`); the counterterm and the complex-place angular bound are proved. The replacement deduction from strip limits is checked (`ConditionalReviewC.entire_zeros_on_line_from_concrete_strip_limits`).

**Printed.** Take φ_z(t) = t^{−z} on t > 1, 0 on (0, 1), with φ_z(1) = 1/2. The approximants are φ_{h,ε,z} = h·(ρ_ε ∗ φ_z), where h is a bump supported in (1, ∞) with values in [0, 1], increasing to 1_{(1,∞)}. The archimedean integrals

(1/2) ∫_{R>0} Σ_{u=±1} χ_v(tu) φ(tu) |t|^{1/2} / |1 − t| · dt/t (real places), and the matching complex-place integrals,

"are bounded above by a common constant A > 0 independent of z ∈ K and independent of the specific φ" (p. 29).

**Derivation.** Take F = Q, χ trivial, and an admissible K containing a real point z₀ > 1, for example a small disc around 2. The integrand is (1/2)φ_n(t) t^{−1/2}/|1 − t| ≥ 0, because φ_z ≥ 0, ρ_ε ≥ 0 and h ∈ [0, 1]. Also φ_n → t^{−z₀} pointwise on t > 1. By Fatou,

liminf_n ∫ φ_n(t) t^{−1/2} / |1−t| dt ≥ ∫₁² t^{−z₀−1/2}/(t − 1) dt ≥ 2^{−z₀−1/2} ∫₁² dt/(t − 1) = ∞.

So the supremum over approximants is infinite and no common A exists. Each approximant is finite on its own only because h vanishes near t = 1. Having finitely many archimedean places does not help: the singularity is local. The passage uses plain integrals with no subtraction, whereas 12.5.1.1 uses Weil's regularised ∫′.

**Fixes.**
- (a) *Logarithmic test.* Multiply pointwise by ℓ = log|·| before taking #. The integrand becomes log t · t^{−z−1/2}/(t − 1), which tends to 1 as t → 1⁺. It is then uniformly integrable for z in compact subsets of Re z > −1/2, and dominated convergence applies.
- (b) *Counterterm.* In x = log t we have dt/t = dx and |1 − eˣ| = |x|(1 + O(x)), so the density is c/x + O(1) near 0. Subtract c∫ q_n(x)η(x)/x dx, with η = 1 near 0 and compactly supported. The renormalised difference is locally bounded.
- (c) *Reference subtraction.* Fix z₀. Then (e^{−zx} − e^{−z₀x}) e^{x/2}/(eˣ − 1) = (z₀ − z) + O(x), which is bounded. The value of the functional at z₀ becomes a constant whose normalisation has to be tracked on both sides.

**Effect.** The literal Montel route in 1.4.3–1.4.5 needs one of these repairs. Both original test families, h = φ# and h = (ℓφ)#, remain in scope, and the log test alone does not give the unlogged limit. None of these repairs affects R − B_adm in item 4.

**Same passage elsewhere.** The argument is repeated word for word at §1.8.4.2–1.8.4.3, lines ~pp. 53–54, with "bounded above by a common constant" at p. 54.

---

<a id="issue-2"></a>
### Issue 2 — §1.4.3

**Issue.** The u = −1 real-place term is printed with |1 − t|; it should be |1 + t|.

**Repair and status.** Lean defines this branch with e<sup>x</sup> + 1 = |1 + t| and proves integrability, uniform cutoff convergence and holomorphy (`CriticalLineAudit.realPlaceNegLog*`).

**Printed.** The real-place term is written (1/2) ∫_{R_{>0}} Σ_{u∈{±1}} χ_v(tu)φ(tu)|t|^{1/2}/|1 − t| dt/t, with the same denominator |1 − t| for both signs.

**Derivation.** The local term is (1/2) ∫′_{R^×} φ(g)|g|^{1/2}/|1 − g| dµ_v(g). Substituting g = ut gives the denominator |1 − ut|, which is 1 + t for u = −1. As printed, the u = −1 term acquires a spurious non-integrable singularity at t = 1.

**Fix.** Replace |1 − t| by |1 − ut|.

---

<a id="issue-3"></a>
### Issue 3 — §1.4.4

**Issue.** The finite-place sum is said to tend to L′<sub>f</sub>/L<sub>f</sub>(s + ½). With the printed terms it tends to −L′<sub>f</sub>/L<sub>f</sub>(s + ½), and the sign carries into §1.4.5.

**Repair and status.** Lean: for every number field and every unitary Hecke character, the cutoff sums converge to −L′<sub>f</sub>/L<sub>f</sub>, uniformly on Re s ≥ σ > 1 (`Round14F.genuineEuler_primePower_cutoff_uniform`).

**Printed.** Lines p. 29: since φ is supported over (1, +∞), φ(q_v^{−m}) = 0 for m > 0, and the sum Σ_{v∈Σ_{F,f}} log(q_v) Σ_{m≥1} (χ(π_v^m) q_v^{−m/2} φ(q_v^m) + χ(π_v^m) q_v^{−m/2} φ(q_v^{−m})) "tends, uniformly over the compact subsets of C_{>1}, to L′_f(s + 1/2, χ)/L_f(s + 1/2, χ)."

**Derivation.** With φ(q_v^{−m}) = 0 and φ(q_v^m) → q_v^{−mz}, the sum tends to Σ_v log(q_v) Σ_{m≥1} χ(π_v)^m q_v^{−m(z+1/2)}. For the Euler product L_f(s, χ) = ∏_v (1 − χ(π_v) q_v^{−s})^{−1} we have log L_v(s) = −log(1 − χ(π_v)q_v^{−s}), so (L_v′/L_v)(s) = −log(q_v) Σ_{m≥1} χ(π_v)^m q_v^{−ms}. Hence the limit is −(L′_f/L_f)(z + 1/2). The checked declaration `MasulloGRH.Round14F.genuineEuler_primePower_cutoff_uniform` proves exactly this, with conclusion `-logDeriv (finiteHeckeL K χ) s`, for every number field K, every unitary Hecke character and Re s ≥ σ > 1.

**Fix.** Replace L′_f/L_f by −L′_f/L_f in §1.4.4 and carry the sign through the identity displayed in §1.4.5 (p. 29). The zero-freeness deduction there reads pole/holomorphy information off this identity, so the sign of every term must be rechecked.

---

<a id="issue-4"></a>
### Issue 4 — Theorem 2.2.3.4, (2.2.3.10)–(2.2.3.12), with (A.2.2.11)

**Issue.** The proof scales every archimedean coordinate by the full idelic norm, which matches the diagonal section only for F = ℚ.

**Repair and status.** Repair: use the slowest place exponent δ = 1/(2(r<sub>1</sub> + r<sub>2</sub>)) with a higher Schwartz order. Lean: decay of every order along the manuscript's place-dependent exponents (`Round197F.diagonal_norm_section_theta_decay`); on the actual objects, for every number field and every Schwartz–Bruhat test, the adelic theta series decays faster than any power (`JThetaAttachment.originalBruhat_theta_radial_bound`), which gives (2.2.3.4) for every number field.

**Printed.** Definition A.2.2.7, p. 547: s_{F,δ}(t) has component 1 at each finite place and t^{1/(N_v(r_1+r_2))} at each archimedean v, where N_v = 1 if v is real and N_v = 2 if v is complex.

In the proof (p. 83), ||x_∞||:= sup_{v∈S_∞} |x_v|_v^{N_v} with N_v = 1 (real) and N_v = 1/2 (complex). Since |·|_v is the normalized absolute value, this is max_v |x_v| in the ordinary modulus. Note that N_v here follows a different convention from A.2.2.11. The proof then states:

- (2.2.3.10), p. 84: ||t_∞ ξ E_∞|| ≥ A ||t_∞ ξ|| = A |t|_F ||ξ||.
- (2.2.3.11), p. 84: ||t_∞ ξ E_∞|| ≥ A M |t|_F, with C:= (AM)^{-1} max||B||.
- (2.2.3.12), p. 84: |f_∞(ξ t_∞ g_{0,∞})| ≤ C_{B,N′} ||ξ t_∞ g_{0,∞}||^{-N′} = C_{B,N′} t_0^{-N′} ||ξ g_{0,∞}||^{-N′} for t_0 > C.
- p. 84: choose N′ = 1 + max{r_1 + 2r_2, N}.
- (2.2.3.13), ll.4428–4430: Σ_{ξ∈I_f−{0}} |f_∞(ξ t_∞ g_{0,∞})| ≤ C_N |t|_F^{-N} = C_N |g|_F^{-N}.

**Problem.** The equalities ||t_∞ ξ|| = |t|_F ||ξ|| in (2.2.3.10) and ||ξ t_∞ g_0|| = t_0 ||ξ g_0|| in (2.2.3.12) assume that t_∞ scales every archimedean coordinate by t_0 = |t|_F. The section s_{F,δ} chosen at p. 83 does not do this.

**Derivation.** Write t = s_{F,δ}(t_0), so |t|_F = t_0. Then (t_∞ x)_v = t_0^{e_v} x_v, with e_v = 1/(r_1+r_2) for v real and e_v = 1/(2(r_1+r_2)) for v complex. Hence

||t_∞ x|| = max_v t_0^{e_v} |x_v|, and for t_0 ≥ 1: t_0^{min e_v} ||x|| ≤ ||t_∞ x|| ≤ t_0^{max e_v} ||x||.

The identity ||t_∞ x|| = t_0 ||x|| holds for all x only if every e_v = 1, which means r_1 + r_2 = 1 with the place real, i.e. F = Q. Two concrete cases:

- F imaginary quadratic: e_v = 1/2, so ||t_∞ x|| = t_0^{1/2} ||x||.
- F = Q(√2): s_{F,δ}(t_0) = (t_0^{1/2}, t_0^{1/2}), so ||t_∞ x|| = t_0^{1/2} ||x|| exactly.

In the second case the order-N′ Schwartz bound only gives |f_∞(ξ t_∞ g_0)| ≤ C_{B,N′} t_0^{-N′/2} ||ξ g_0||^{-N′}. With the printed choice N′ = 1 + max{2, N} = N + 1 (for N ≥ 2), the sum is O(t_0^{-(N+1)/2}). For N ≥ 2 that is weaker than the t_0^{-N} claimed in (2.2.3.13). More generally, for totally real F of degree n the printed choice gives only t_0^{-(N+1)/n}. So the printed argument fails for every F ≠ Q. The theorem's conclusion is still true, because a Schwartz function satisfies bounds of every order.

**Fix.** Set δ:= 1/(2(r_1+r_2)). This satisfies δ ≤ e_v for every v; when r_2 = 0 the sharper value 1/r_1 also works. For t_0 ≥ 1 we then have ||t_∞ x|| ≥ t_0^δ ||x||. Let A:= min_v inf_{e∈E_∞} |e_v|. This is positive because the closure of E_∞ is compact in GL_1(A_{F,S_∞}) (4424). Then:

- (2.2.3.10′): ||t_∞ ξ e|| ≥ A t_0^δ ||ξ|| for e ∈ E_∞.
- (2.2.3.11′): ≥ A M t_0^δ, with C:= max{1, ((AM)^{-1} max||B||)^{1/δ}}.
- (2.2.3.12′): |f_∞(ξ t_∞ g_0)| ≤ C_{B,N′} t_0^{-δN′} ||ξ g_0||^{-N′} ≤ C_{B,N′} A^{-N′} t_0^{-δN′} ||ξ||^{-N′}.

Choose N′ > r_1 + 2r_2 (for summability over the lattice, Prop. 2.2.1.3) and δN′ ≥ N, e.g. N′ = max{r_1 + 2r_2 + 1, 2(r_1+r_2)N}. Then Σ_ξ ≤ C t_0^{-N}, which is (2.2.3.13). Parts (2)–(5) reduce to (1) (p. 83, p. 85) and are unaffected.

---

<a id="issue-5"></a>
### Issue 5 — (3.4.3.15), Remark 3.4.3.4

**Issue.** Z(·, c) = L(c)Δ′(c) is asserted for every test, with holomorphy on the completed archimedean tensor product, but no uniform seminorm bounds are given.

**Repair and status.** Repair: local Taylor subtraction with Gamma-pole cancellation, extended by projective-tensor seminorms. Lean: the local pieces are proved: the Gaussian integrals equal Γ<sub>ℝ</sub> (`ConditionalA881.manuscript_real_gaussian_zeta`), the complex polar terms divided by Γ are entire (`SpectralG909.normalizedComplexPole_entire`), uniform seminorm bounds hold on the full mixed Schwartz space (`SpectralB909.mixed_weighted_bound`), and the unramified local series is proved. The global identity enters the converse theorems as a hypothesis.

**Printed.** "Z(·, c) = L(c)Δ′(c) as meromorphic S(A_F)′_β-valued functions". The argument asserts that c ↦ Δ′(c)(f) is holomorphic for every f and then applies weak-to-strong holomorphy. Remark 3.4.3.4 places Δ′(c) on the completed archimedean tensor product ⊗̂_{v|∞} S(F_v).

**Gap.** For pure tensors this is local Tate theory. For general elements of the completed tensor product it needs continuous-seminorm bounds that hold uniformly on compact sets of c. Separately, an Euler-product or functional-equation theorem does not by itself make every test integral divisible by L at its zeros.

**Repair derivation**:

*Real place,* character sgn^ε |·|^{it}, with Z_v(f, z) = ∫ f(x) sgn(x)^ε |x|^{z+it} dx/|x|.
1. Averaging over x ↦ −x keeps only the part of f with parity ε. Its Taylor expansion at 0 contains only the powers x^{ε+2j}.
2. On |x| ≤ 1, subtract the Taylor polynomial up to order 2J + ε. Since ∫₀¹ x^{ε+2j} x^{z+it−1} dx = 1/(z + it + ε + 2j),
Z_v(f, z) = Σ_{j<J} a_j(f)/(z + it + ε + 2j) + H_J(f, z),
where H_J is holomorphic on Re z > −(ε + 2J).
3. If Re z ∈ [−A, B] and 2J > A, then H_J is bounded by sup_{|x|≤1} |f^{(2J+ε)}| plus a Schwartz tail seminorm of order > B.
4. Γ_R(z + it + ε) = π^{−(z+it+ε)/2} Γ((z + it + ε)/2) has simple poles exactly where z + it + ε = −2j. So Z_v/Γ_R is entire, and |Z_v(f, z)/Γ_R| ≤ C_K p_K(f) uniformly on compact K, for a continuous Schwartz seminorm p_K.

*Complex place,* angular character e^{ikθ}: averaging over the angle keeps the powers |k| + 2j, with denominators 2(z + it) + |k| + 2j. Γ_C(s) = 2(2π)^{−s}Γ(s), taken at s = z + it + |k|/2, has poles at exactly these points.

*Passing to the completion.* On the algebraic tensor product the archimedean ratio is a multilinear form bounded by the product of these seminorms, hence by the projective tensor seminorm π(u) = inf Σ_i ∏_v p_v(f_{i,v}), uniformly on K. It therefore extends continuously to the completion. Locally uniform limits of holomorphic functions are holomorphic.

*Finite places.* For f_v locally constant with compact support, Z_v(f_v, z)/L_v(z) is a Laurent polynomial in q_v^{−z} (Tate), so it is entire.

**Fix.** Insert these uniform bounds before the weak-to-strong step. Match the constants, the space S₀ and the quotient Haar measure explicitly.

---

<a id="issue-6"></a>
### Issue 6 — (6.3.2.8); proof of Theorem 7.1.4.2

**Issue.** The pole-clearing factors have the wrong sign: (s − it<sub>0</sub>) where the residues at −it<sub>0</sub> and 1 − it<sub>0</sub> require (s + it<sub>0</sub>).

**Repair and status.** Lean: every pole clearing uses (z + iτ)(z − 1 + iτ), whose divisor is exactly the two poles (`Round12A.norm_twist_polar_divisor`).

**Printed.**
- (6.3.2.8): 0 → (s − it_0)(1 − s − it_0) ζ̂_F(s+it_0) O(C) ∩ AS(C) → ζ̂_F(s+it_0) O(C) ∩ AS(C) → C ⊕ C → 0. Lines p. 304 take residues "at s = −it_0, 1 − it_0". By contrast, (6.3.2.4) at p. 304 has (s + it_0)(1 − s − it_0).
- Proof of 7.1.4.2, p. 327: Λ(s, χ):= (½ (s + ix_0)(s − 1 − ix_0))^{δ_χ} L(s, χ). By contrast, the statement at p. 326 has (1 − s − ix_0).

**Problem.** (s − it_0) vanishes at it_0, but the pole is at −it_0. (s − 1 − ix_0) vanishes at 1 + ix_0, but the pole is at 1 − ix_0. For t_0, x_0 ≠ 0:
- the left-hand space of (6.3.2.8) is not the range given in (6.3.2.4);
- the printed Λ at p. 327 keeps a pole at 1 − ix_0, so it is not entire, and the Hadamard product (7.1.4.9) from [Bar, Thm.2] does not apply to it.

**Fix.** Replace (s − it_0) with (s + it_0) in (6.3.2.8), and (s − 1 − ix_0) with (s − 1 + ix_0) at p. 327.

---

<a id="issue-7"></a>
### Issue 7 — Theorem 7.1.4.2(1), (7.1.4.23)

**Issue.** The jet-dual space is stated to be a locally convex product. The proof computes a direct sum, which is correct: a continuous functional on an infinite product depends on finitely many coordinates.

**Repair and status.** Repair: state the direct sum. Natural-language repair. The individual-jet converse, which does not use the product, is proved in Lean (`NativeTrueOrder.admitted_same_integral_riesz_converse`); the topology itself is not formalized.

**Printed.** Z_χ "is linearly and topologically isomorphic to the locally convex product ∏_ρ J_ρ" (p. 326). The proof identifies O(C)/Λ O(C) ≅ ∏ C[s]/(s − ρ)^{N(ρ)} as a Fréchet product. It then says its continuous dual "is exactly the locally convex direct sum" ⊕ H_ρ (p. 328, citing Trèves 22.1(b)), and Z_χ = (Λ O(C))^⊥ is that dual.

**Derivation.** Let ℓ be a continuous linear functional on ∏_{ρ ∈ Z} V_ρ, with each V_ρ finite-dimensional.
1. By continuity there are a finite set F and δ > 0 such that |ℓ| ≤ 1 on U = {x: ‖x_ρ‖ < δ for ρ ∈ F}.
2. Take ρ ∉ F and v ∈ V_ρ, viewed as a coordinate vector. Then λv ∈ U for every λ ∈ C, so |λ|·|ℓ(v)| ≤ 1 for all λ, which forces ℓ(v) = 0.
3. So ℓ factors through ∏_{ρ ∈ F} V_ρ, and (∏ V_ρ)′ = ⊕ V_ρ′.

For an infinite zero set, ∏ and ⊕ are not isomorphic. The product is Fréchet with uncountable algebraic dimension. The direct sum has countable dimension and is not metrisable. So Z_χ ≅ ⊕_ρ J_ρ, with the strong dual topology.

**Fix.** State the direct sum, state any completion or density map separately, and recheck the topology used in the totality and basis steps (7.1.4.2(3)–(4) and later uses).

**Effect.** The individual-jet converse through Z = LΔ′ does not use the product claim, and residue exhaustion is a separate route.

**Same claim elsewhere.** (7.1.4.23), lines ~p. 331, makes the same "locally convex product" claim for the S₀-modified ideal, ∏ J_{S₀,p} × ∏ J_ρ.

---

<a id="issue-8"></a>
### Issue 8 — Lemma 9.3.1.5, (9.3.1.6)

**Issue.** The translation bound carries the factor |log|g||<sup>s/2</sup>, which vanishes at |g| = 1, where translation is the identity.

**Repair and status.** Repair: ‖ρ(g)‖ ≤ 2<sup>s/4</sup> max{|g|<sup>±α</sup>} (1 + log²|g|)<sup>s/4</sup>, as the proof's own (9.3.1.7) gives. Lean: the printed bound fails at g = 1 (`Round92C.printed_translation_bound_fails_at_identity`); the corrected operator bound is proved on the actual weighted L² space over C<sub>K</sub> for every number field and s ≥ 0 (`SpectralCycle8G.actualTranslation_bound`), with the representation identities and the bounded convolution operator.

**Printed.**
- p. 421: "Let I = [a,b] … s ≥ 0. The function f(g):= ρ_G(g,·) satisfies, for any continuous seminorm p on L_β(W^s_I(G)): (9.3.1.6) p(f(g)) ≤ C_p max{|g|^a_G, |g|^b_G} |log|g|_G|^{s/2}."
- The proof takes p to be the operator norm (p. 421). It ends with (9.3.1.7), p. 421: a bound C₀(C₂ + |log|g||^s C₂ + 1 + C₁|log|g||^{s′})^{1/2}.

**Problem.** For s > 0 the right side of (9.3.1.6) is 0 at every g with |g| = 1. At those g, ρ(g) is an isometry. The proof's own (9.3.1.7) keeps the additive constants that the statement drops.

**Derivation.** ‖ρ(g)u‖²_{I,s} = ∫|u(g^{−1}h)|²w(h)dµ(h) = ∫|u(h)|²w(gh)dµ(h), with w(h) = max{|h|^{2a},|h|^{2b}}(1+log²|h|)^{s/2}.
- If |g| = 1, then w(gh) = w(h), so ρ(g) is an isometry. With p the operator norm, p(f(g)) = 1, while the right side of (9.3.1.6) is C_p·1·0^{s/2} = 0.
- Near G¹: 1 = ‖ρ(g^{−1})ρ(g)‖ ≤ ‖ρ(g^{−1})‖‖ρ(g)‖ ≤ C_p² max{|g|^a,|g|^b} max{|g|^{−a},|g|^{−b}} |log|g||^s → 0 as |g| → 1. This is a contradiction on a whole neighbourhood of G¹.
- At g = 1, (9.3.1.7) is ≥ C₀(C₂+1)^{1/2} > 0. So (9.3.1.6) does not follow from its own proof.

Corrected bound. Peetre's inequality 1+(x+y)² ≤ 2(1+x²)(1+y²) and max{e^{2a(x+y)},e^{2b(x+y)}} ≤ max{e^{2ax},e^{2bx}}·max{e^{2ay},e^{2by}} give w(gh) ≤ 2^{s/2}max{|g|^{2a},|g|^{2b}}(1+log²|g|)^{s/2}w(h). Hence

‖ρ(g)‖ ≤ 2^{s/4} max{|g|^a,|g|^b} (1+(log|g|)²)^{s/4}.

This is the shape (9.3.1.7) actually produces.

**Fix.** Replace (9.3.1.6) by the bound above. There are two downstream uses. At p. 423 (proof of Lemma 9.3.2.1) the majorant "C|log|g||^s" has the same defect; integrability against Schwartz φ survives with the corrected bound. At p. 464 (proof of 10.4.2.8) the correction changes constants only and does not repair Issue 21(b).

---

<a id="issue-9"></a>
### Issue 9 — Lemma 9.3.2.4

**Issue.** Jensen's formula needs a lower bound at the centre, but Schwartz decay gives an upper bound. The lemma is false for general ϕ ∈ S<sub>E</sub>: the test with Mellin transform e<sup>z²</sup> sin z² has about 2T/π zeros per unit box.

**Repair and status.** Repair: restrict to L-functions and use the Euler-product lower bound at 2 + iT. Lean, for K = ℚ: Jensen's formula for the pole-cleared L-function, the lower bound at the centre, and the zero count bounded by a circle mean (`completedDirichlet_unitBand_count_le_circleMean`); the circle growth estimate is not yet formalized.

**Printed.**
- Statement, p. 425: "Let ϕ ∈ S_E(G). Let T ∈ ℝ. Then the number of zeros of M(ϕ)(χ|·|^z) contained in the box I × i[T,T+1] is O(log|T|), where the implied constant depends on ϕ and I."
- Proof, p. 425: "N(T) log(R/r) ≤ log(B) − log|M(ϕ)(χ|·|^{z₀})| for a large enough real number B > 0, and hence N(T) = O(log|M(ϕ)(χ|·|^{a+iT+i/2})|). Since M(ϕ) is uniformly Schwartz on every vertical strip … for every integer N ≥ 0, there exists C_N > 0 such that M(ϕ)(χ|·|^{a+iT+i/2}) = O(|T|^N) [sic; meant O(|T|^{−N})]. We deduce that N(T) = O(log|T|)."

**Problem.** Jensen's lemma ([Lang], Lemma 2.2) bounds the zero count n(r) by (log max_{|z−z₀|=R}|f| − log|f(z₀)|)/log(R/r). Getting O(log|T|) needs log(max/|f(z₀)|) = O(log|T|), and in particular a *lower* bound on |f(z₀)|. Schwartz decay gives the opposite: |f(z₀)| ≤ C_N|T|^{−N}, i.e. −log|f(z₀)| ≥ N log|T| − log C_N. That bounds the right side of Jensen from below, which is useless here. With an absolute constant B, the right side grows faster than any multiple of log|T|.

**Derivation.**
1. *The method yields at best O(T), even for a zero-free function.* Take f(z) = e^{z²} = M(ϕ₀) with ϕ₀(t) = (4π)^{−1/2}e^{−(log t)²/4}, using ∫e^{−αu²+zu}du = (π/α)^{1/2}e^{z²/(4α)}. Then |f(z₀)| = e^{a²−(T+½)²}. On the circle |z−z₀| = R the maximum is at least |f(a+i(T+½−R))| = e^{a²−(T+½−R)²}, so log(max/|f(z₀)|) ≥ 2R(T+½) − R².
2. *Counterexample to the statement.* Let α_± = (1∓i)/8 and
ϕ(t):= (2i)^{−1}[(α₊/π)^{1/2}e^{−α₊(log t)²} − (α₋/π)^{1/2}e^{−α₋(log t)²}].

Since |e^{−α_±u²}| = e^{−u²/8}, every (t∂_t)^nϕ is a polynomial in log t times e^{−(log t)²/8}, so ϕ ∈ S_E(ℝ_{>0}). Because 1/(4α_±) = 1±i, we get M(ϕ)(z) = ∫ϕ(t)t^z dt/t = (e^{(1+i)z²} − e^{(1−i)z²})/(2i) = e^{z²}sin(z²).

Its zeros are at z² = nπ (n ∈ ℤ), and all are simple away from z = 0. For n = −k < 0 they are z = ±i√(kπ). The segment i[T,T+1] contains #{k ≥ 1: T² ≤ kπ ≤ (T+1)²} ≥ (2T+1)/π − 1 of them.

For a general compact I, pick c ∈ I and replace ϕ by t^{−c}ϕ(t). This is still in S_E, and its Mellin transform is M(ϕ)(z−c). The box I × i[T,T+1] then contains ≥ (2T+1)/π − 1 zeros, which is not O(log T). Here G = ℝ_{>0} and χ = 1.
3. *The lemma still fails under the extra hypothesis of Lemma 9.3.2.5 (all zeros inside the strip).* Lemma 9.3.2.4 does not assume this. Take F(z) = e^{−z⁴}/Γ(1+z²/π). It is entire, and its zeros are exactly z = ±i√(kπ), k ≥ 1, all on iℝ.

Write 1/Γ(1+w) = −Γ(−w)sin(πw)/π. With Stirling, |sin(πw)| ≤ e^{2|xy|} and Re z⁴ = x⁴ − 6x²y² + y⁴, this gives log|F(x+iy)| ≤ −y⁴ + 6X²y² + 2X|y| + O(y² log|y|) on |x| ≤ X. So F is Schwartz on vertical strips, with derivatives controlled by Cauchy estimates. Hence F = M(ϕ) with ϕ ∈ S_E, by the isomorphism S_E ≅ AS(ℂ) used at p. 441, or directly by shifting the inverse-Mellin contour. It has the same ≍ T count per unit box.

**Fix.** The O(log|T|) count must come from arithmetic, not from Schwartz decay. Restrict the lemma to ϕ whose Mellin transform is the (completed) L(·,χ) times a factor with controlled zeros. Then apply Jensen to L at a centre 2+iT. The Euler product and |χ| = 1 give |L(2+iT,χ)| ≥ ∏_v(1+q_v^{−2})^{−1} ≥ ζ_F(2)^{−1}, and with polynomial (convexity) growth on the disc this gives O(log(q_χ(|T|+2))) zeros per unit box. Lemma 9.3.2.5, which cites 9.3.2.4 at p. 426, needs the restricted version.

---

<a id="issue-10"></a>
### Issue 10 — Theorem 9.3.2.6, (9.3.2.10)

**Issue.** The kernel intersections W<sub>≤T</sub> shrink as T grows, so their projections cannot converge to the identity; the proof of Theorem 10.2.2.1 rests on this.

**Repair and status.** Repair: project onto increasing finite jet spans. Lean: the printed step fails (`MasulloGRH.low_constraint_antitone`, `low_kernel_projection_not_identity`); finite-span projections converge strongly to the projection onto the closed span (`Round175F.finite_jet_cutoffs_tendsto`, `NestedProjection.global_projection_tendsto`); the actual Mellin jets are linearly independent across all character components on C<sub>K</sub> (`Spectral36B.native_cross_component_L2_independent`).

**Printed.** For T > 0,

W_I^s(G)_{≤T}:= ⋂ ker δ_ρ^{(k)}, over zeros ρ of M(φ)(χ|·|^ρ) with |Im ρ| ≤ T and 0 ≤ k ≤ N(ρ)−1.

The theorem states P_T → Id strongly. The proof (p. 426) says ⋃_T W_≤T is dense "since W_I^s(G)_{≤T} ⊂ W_I^s(G)_{≤T′} for every pair 0 < T < T′."

**Derivation.**
1. When T increases, the index set of the intersection grows. More constraints give a smaller space, so for T < T′ we have W_≤T′ ⊆ W_≤T. This is the reverse of the printed inclusion.
2. Fix one admitted functional u = δ_{ρ₀}^{(k₀)} with |Im ρ₀| = T₀. It is continuous and nonzero on W_I^s(G). For T ≥ T₀ we have ran P_T ⊆ ker u, so for every v:
|u(v)| = |u(v − P_T v)| ≤ ‖u‖·‖v − P_T v‖, which gives ‖v − P_T v‖ ≥ |u(v)|/‖u‖.
For any v with u(v) ≠ 0, P_T v does not converge to v.
3. What does hold: a decreasing net of orthogonal projections converges strongly to the projection onto the intersection of their ranges. So P_T → P_{W_∞}, where W_∞ = ⋂_T W_≤T is the joint kernel of all the jets. Equivalently, Id − P_T increases to the projection onto the closed span of the jet Riesz vectors.

**Fix.** Use increasing finite jet spans, or the complementary projections Id − P_T, and prove the density statement in the intended annihilator. Alternatively, use residue exhaustion E ⊆ S.

**Effect.** The proof of Theorem 10.2.2.1 (p. 446) is one sentence: "the same method as in the proof of Theorem 10.2.1.1, with Theorem 9.3.2.6 replacing Lemma 9.3.2.1". Its footnote (p. 446) reads "Return here." So the printed route to the spectral Markushevich basis has to be redone. The repair also needs finite independence across different zeros and characters: compact-character orthogonality, then independence of exponential polynomials in log|g|. The checked B16 component proves independence only within one chain. The repaired PA nuclearity argument does not use this route and is not affected.

---

<a id="issue-11"></a>
### Issue 11 — (10.2.1.6), (10.2.2.5), (10.3.1.4), (10.3.2.4), (11.2.0.6)

**Issue.** The boundary count min(N, ⌊(s − 1)/2⌋ + 1) admits a jet whose norm diverges when s is an odd integer (s = 3, m = 1).

**Repair and status.** Repair: count #{m < N : 2m + 1 < s}. Lean, on the actual C<sub>K</sub> for every number field and character: a boundary jet lies in L² if and only if 2m + 1 < s, and the admitted count is min(N, ⌈(s − 1)/2⌉) (`SpectralRound9B.genuine_boundary_mellin_memLp_iff`); at s = 2k + 1 the count is min(N, k) (`SpectralRound1B.boundaryJetOrders_odd`).

**Printed.** At b = ±α, N_{I,s}(ρ) = min(N(ρ), [(s−1)/2] + 1), "where [x] is the largest integer N ≥ 0 satisfying N ≤ x" (p. 454).

**The manuscript's own criterion.** (9.1.2.16), p. 402, with its proof at p. 402: η_{t,m} ∈ W^{−s,2} iff ∫|log|g||^{2m}(1+|log|g||²)^{−s/2} dμ < ∞, "if and only if s − 2m > 1".

**Derivation at an endpoint.** From the norm in the proof of 10.2.2.2 (lines ~p. 447):

‖η_{χ,t,b,m}‖²_{I,−s} = ∫ |g|^{2b} |log|g||^{2m} / (max{|g|^{2α}, |g|^{−2α}} · (1 + log²|g|)^{s/2}) dμ(g).

Put x = log|g|. The Haar measure pushes forward to c·dx with c > 0. For b = α:
- on x > 0 the exponential factors cancel (e^{2αx}/e^{2αx} = 1);
- on x < 0 they give e^{4αx}, which decays.

So the norm is finite iff ∫₁^∞ x^{2m}(1+x²)^{−s/2} dx < ∞. The integrand behaves like x^{2m−s}, so this happens iff 2m − s < −1, i.e. **2m + 1 < s**. The case b = −α is symmetric. At α = 0 both tails are polynomial and the condition is the same. For interior b there is exponential decay on both sides, which is why N_{I,s} = N is correct there.

**Counting.** The number of admissible degrees is #{m ≥ 0: m < (s−1)/2}.
- If s > 1 and (s−1)/2 is not an integer, the count is ⌊(s−1)/2⌋ + 1, which equals the printed cap.
- If s = 2k + 1 is an odd integer, the count is k but the printed cap is k + 1. The extra jet m = k has tail ∫ x^{2k}(1+x²)^{−(2k+1)/2} dx ~ ∫ dx/x = ∞.

**Examples.**
- s = 3, m = 1: the tail of x²(1+x²)^{−3/2} behaves like 1/x and diverges. The printed cap includes m = 1 whenever N ≥ 2.
- s = 1: the printed cap admits m = 0, whose tail (1+x²)^{−1/2} also behaves like 1/x and diverges.

**Checked in Lean.** `SpectralRound1B.boundaryJetOrders_odd` in `NativeRieszFamily.lean` proves #{j < N: 2j + 1 < 2k + 1} = min(N, k). Checked in Lean, with the standard axioms propext, Classical.choice, Quot.sound.

**Fix.** At b = ±α, count n_adm(ρ) = #{m < N(ρ): 2m + 1 < s}. At α = 0, count the single boundary line once.

**Why it matters.** Definition 10.4.3.7 (p. 473) takes s ≥ 3, so s = 3 is in range. For every s ≥ 3 the boundary count includes at least m = 0, so boundary terms never vanish identically (see item 4).

**Same cap elsewhere.** The identical formula min(N, [(s−1)/2] + 1) appears at (10.3.1.4), line ~p. 448, for the line case, and at (11.2.2.5), line ~p. 490, for ε_p. Both have the same odd-s overcount if the same membership criterion applies. Also, [x] is defined only for x ≥ 0 ("largest integer N ≥ 0"), while Theorem 10.2.2.1 allows any s ≥ 0. For s < 1 the cap is undefined as written.

---

<a id="issue-12"></a>
### Issue 12 — Proof of Theorem 10.2.1.1

**Issue.** Cites Theorem 6.3.2.1(3), which has no part (3); the biorthogonality used is in Theorem 7.1.4.2(3).

**Repair and status.** Repair: cite 7.1.4.2(3) and prove independence of the jets. Lean: on the actual C<sub>K</sub> the jets are linearly independent across all characters, exponents and orders, orthogonal across components, with Gram–Schmidt flags and finite biorthogonal systems (`Spectral36B.native_cross_component_L2_independent`, `native_gramSchmidt_flag`).

**Printed.** Lines p. 442: "Since the strong topology on (H^s_{F,a}(ω))′_β is finer than the strong topology on the continuous dual of the nuclear Fréchet space H_F(ω) = S_E(C_F)(ω)/H_{0,cont}(ω, S_0(A_F)) from Theorem 7.1.4.2, then, since the countable set of continuous functionals U(δ_ρ^{(m)}) on such quotient is topologically free by Theorem 6.3.2.1(3), so is the countable set of continuous functionals {D_t^m} from (10.2.1.9) on H^s_{F,a}(ω)." Lines p. 442: "… and their bi-orthogonal set, which exists by Theorem 6.3.2.1(3) and is the image of a countable subset of H_F(ω), is dense in H^s_{F,a}(ω)."

**Problem.** Theorem 6.3.2.1 (Global Converse Theorem, pp. 304–305) has two top-level parts. Part (1), (6.3.2.3)–(6.3.2.4), identifies the closed Mellin range. Part (2), (6.3.2.5)–(6.3.2.8), gives strict exactness of 0 → H_{0,cont}(χ|C¹, S_0) → H_{0,cont}(χ|C¹, S) → C² → 0. Part (2) contains nested items (1)–(3). Nested item (3), at p. 304, only defines the right-hand map Φ(f) ↦ (−μ_1(C¹_F) f(0) δ, μ_1(C¹_F) f̂(0) δ). Neither a top-level part (3) nor the nested item (3) says anything about topological freeness or biorthogonal sequences. Those statements are in Theorem 7.1.4.2(3), p. 327: "Any enumeration of the set of continuous functionals {U(δ_ρ^{(m)})} … admits a bi-orthogonal sequence in H_F(χ|C¹_F):= S_E(C_F)(χ|C¹_F)/H_{0,cont}(χ|C¹_F, S_0(A_F)). In particular, it is topologically free." The same sentence at p. 442 already names Theorem 7.1.4.2 as the source of H_F(ω).

**Derivation.** This is a citation check, not a mathematical step. The cited part does not exist, and the only item numbered (3) inside 6.3.2.1 has different content.

**Fix.** Replace both occurrences of "Theorem 6.3.2.1(3)" (p. 442, p. 442) with "Theorem 7.1.4.2(3)", applied with χ a lift of ω. Theorem 7.1.4.2(3) is a statement in the Fréchet quotient H_F(ω). Passing it to the Hilbert quotient H^s_{F,a}(ω) is a separate step, which the paragraph begins at p. 442.

---

<a id="issue-13"></a>
### Issue 13 — Proposition 10.2.2.2, (10.2.2.8)

**Issue.** Claims a uniform two-sided bound on the jet norms; the norms grow without bound in the jet order m and near the strip boundary.

**Repair and status.** Repair: explicit bounds depending on m and on the distance δ to the boundary. Lean, on the actual objects: the exact norm density; the log pushforward of every Haar measure is a multiple of Lebesgue measure; ‖η‖² ≤ V·2(2m)!/(2δ)<sup>2m+1</sup> inside the strip and ≤ Vπ when 2m + 2 ≤ s (`MasulloGRH.genuineSpectralJet_*_energy`); a lower bound growing like 4<sup>m</sup>, and no uniform bound (`NuclearBoundH88.jetDensity_slab_no_uniform_jet_bound`).

**Printed.**
- p. 446: "There exists C > 0 such that the functions η_{χ,t,b,m}(g):= χ(g)|g|^{it+b}(log|g|)^m as (1) χ ranges over the base-points … (2) t ranges over the imaginary parts of the zeros of L(s,χ) on the vertical line Re(s) = a, with 0 ≤ m ≤ N_{I,s}(ρ_{χ,t,b})−1 …, all satisfy (10.2.2.8) {η}_{t,b,m} ⊂ B_C:= {ϕ ∈ W^{−s}_I(C_F): 1/C ≤ ‖ϕ‖_{I,−s} ≤ C}."
- Proof, p. 447: "‖η_{χ,t,b,m}‖_{I,−s} = (∫|g|^{2b}|log|g||^{2m} / (max{|g|^{2α},|g|^{−2α}}(1+|log|g||²)^{s/2}) dµ)^{1/2} …, and so ‖η_{χ,t,m}‖_{I,−s} can only attain values within a compact interval which does not contain 0."

**Problem.** In the interior the jet order runs up to the full multiplicity, m ≤ N(ρ) − 1 ((10.2.2.6)), and b ranges over the real parts of zeros minus a. The norm grows without bound as m → ∞ and as |b| → α. The finite-values argument of Prop. 10.2.1.3, where b = 0 and m < (s−1)/2, does not transfer.

**Derivation.** ‖η_{b,m}‖² = V·E(b,m) with E(b,m) = ∫_ℝ e^{2bu−2α|u|}|u|^{2m}(1+u²)^{−s/2}du, independent of t and χ.
- *Uniform lower bound (fine).* On 1 ≤ |u| ≤ 2 we have e^{2bu−2α|u|} ≥ e^{−8α}, |u|^{2m} ≥ 1 and (1+u²)^{−s/2} ≥ 5^{−s/2}, so E ≥ 2e^{−8α}5^{−s/2}.
- *No uniform upper bound.* Let 0 ≤ b < α and δ = α − b. Then E(b,m) ≥ 2^{−s/2}∫₁^∞u^{2m−s}e^{−2δu}du. (The case b < 0 is symmetric, using u < 0.)
- For fixed m with 2m − s ≥ −1, the integral tends to ∫₁^∞u^{2m−s}du = ∞ as δ ↓ 0, by monotone convergence.
- For fixed δ > 0, it is ≥ Γ(2m−s+1)(2δ)^{−(2m−s+1)} − ∫₀¹u^{2m−s}du, which tends to ∞ super-exponentially in m.
- So sup over labels of ‖η‖ is finite only if (i) the interior multiplicities are bounded and (ii) labels with 2m ≥ s−1 keep |b| away from α. Neither is known: bounded multiplicity of zeros of Hecke L-functions is open (only N(ρ) = O(log(q|t|)) is known), and nothing excludes Re ρ − a accumulating at ±α.
- The statement is also garbled. (2) says "zeros … on the vertical line Re(s) = a", which leaves b undefined, and the proof's "‖η_{χ,t,m}‖" drops b.

**Fix.** Drop the uniform annulus. Keep the explicit label-dependent norms E(b,m)^{1/2} in every downstream estimate, i.e. in Cor. 10.2.2.3 (p. 447) and (10.4.2.24). Restate (2) as the zeros a+b+it with b ∈ [−α,α].

---

<a id="issue-14"></a>
### Issue 14 — Theorem 10.3.1.1, proof (p. 451)

**Issue.** A uniform bound on ‖η‖·‖ψ‖ is inferred from normalisation. Normalisation bounds η only, and for F = ℚ, a = ½ close zero ordinates make ‖ψ‖ unbounded.

**Repair and status.** Repair: a natural-language proof of the nuclear bound through a whole-window resolvent estimate with label-dependent costs. Lean: lower bounds, minimal lifts through residuals on the actual objects, label-dependent block costs for both tests, and the finite-level resolvent nuclear bound with derived column and row estimates (`Round197H.native_finite_level_resolvent_nuclear_bound`).

**Printed.**
- p. 444. "Let E be Banach space, and {(x_m, f_m)} ⊂ E × E′_β a Markushevich basis. We say it is: (1) Bounded iff {x_m} ⊂ E is a bounded subset. (2) Regular iff {x_m} ⊂ E is strictly bounded away from 0 ∈ E. *In particular, {f_m} ⊂ E′_β is bounded.* (3) Normalized iff it is both bounded and regular."
- Prop. 10.2.1.3 (pp. 443–444) gives C with 1/C ≤ ‖η_{χ,t,m}‖_{−s,2} ≤ C. Its proof computes ‖η_{χ,t,m}‖²_{−s,2} = ∫|log|g||^{2m}(1+|log|g||²)^{−s/2} dµ, which depends on m only.
- Cor. 10.2.1.4 (p. 444) says the η form a normalized Markushevich basis of the image of (H^s_{F,a})′ in W^{−s,2}. So in Terminology 10.2.1.2 we have E = (H^s_{F,a})′, x_m = η and f_m = ψ ∈ H^s_{F,a}.
- (10.3.1.18), p. 451: σ_m(A^{finite}_{K,(k,j)}) ≤ N_s(ρ)·C·2^{N_s(ρ)−1} Σ_{0≤i≤N_s−1} |φ̂^{(i)}(it_{k,j})|, "where C is such that ‖η_{χ_k,t_{k,j},m′}‖_{−s,2}·‖ψ_{χ_k,t_{k,j},m}‖_{s,2} ≤ C for all 0 ≤ m′ ≤ m ≤ N_s(ρ)−1."
- p. 451: "The existence of C is ensured by the Markushevich basis {η}, and hence its bi-orthogonal sequence {ψ}, being normalized (see Terminology 10.2.1.2), which implies that C can be chosen to be independent of m′ and of (k,j) (i.e. … {η} in W^{−s,2}(C_F) and its bi-orthogonal in W^{s,2}(C_F) are both contained in the closed ball of radius C^{1/2} …; see Proposition 10.2.1.3)."

**Problem.** The "in particular" in (2) is false. Normalization constrains only the sizes ‖x_m‖. A uniform bound on ‖x_m‖·‖f_m‖ is the separate property of a *bounded* (uniformly minimal) Markushevich basis. Prop. 10.2.1.3 bounds η only. For the actual system and F = ℚ, a = ½, the uniform C claimed at p. 451 does not exist.

**Derivation.**
1. *What normalization gives.* From f_m(x_m) = 1 we get ‖f_m‖ ≥ 1/‖x_m‖. So *boundedness* of {x_m} bounds ‖f_m‖ from *below*, and nothing bounds it from above. The rescaling (x_m, f_m) ↦ (λ_m x_m, λ_m^{−1} f_m) preserves the Markushevich property and every product ‖x_m‖·‖f_m‖. With λ_m = 1/‖x_m‖ it makes any Markushevich basis normalized. Normalization therefore carries no information about sup‖x_m‖‖f_m‖.
2. *Abstract counterexample.* In ℓ² with orthonormal basis (e_n), let ε_n = 2^{−n} and set
- x_{2n} = e_{2n}, x_{2n+1} = e_{2n} + ε_n e_{2n+1};
- f_{2n} = e*_{2n} − ε_n^{−1}e*_{2n+1}, f_{2n+1} = ε_n^{−1}e*_{2n+1}.

Biorthogonality: f_{2n}(x_{2n}) = 1; f_{2n}(x_{2n+1}) = 1 − ε_n^{−1}ε_n = 0; f_{2n+1}(x_{2n}) = 0; f_{2n+1}(x_{2n+1}) = 1.

Completeness: e_{2n} = x_{2n} and e_{2n+1} = ε_n^{−1}(x_{2n+1} − x_{2n}). Totality: e*_{2n} = f_{2n} + f_{2n+1} and e*_{2n+1} = ε_n f_{2n+1}.

So this is a Markushevich basis with 1 ≤ ‖x_k‖ ≤ √2, which is normalized in the sense of 10.2.1.2. But ‖f_{2n+1}‖ = 2^n, so the "in particular" fails and sup‖x_k‖‖f_k‖ = ∞.
3. *The actual system.* Take F = ℚ, χ = 1, a = ½ and any s > 1. Every η_{t,0}(g) = |g|^{it} has the same norm c_s = (V∫(1+u²)^{−s/2}du)^{1/2}. Let t ≠ t′ be ordinates of zeros of ζ on Re = ½. Biorthogonality gives ⟨η_{t,0},ψ_{t,0}⟩ = 1 and ⟨η_{t′,0},ψ_{t,0}⟩ = 0, so
1 = ⟨η_{t,0} − η_{t′,0}, ψ_{t,0}⟩ ≤ ‖η_{t,0} − η_{t′,0}‖_{−s,2}·‖ψ_{t,0}‖_{s,2}.

The difference has norm ‖η_{t,0} − η_{t′,0}‖²_{−s,2} = V∫_ℝ 4 sin²((t−t′)u/2)(1+u²)^{−s/2} du =: Vκ_s(t−t′). By dominated convergence κ_s(δ) → 0 as δ → 0, because (1+u²)^{−s/2} ∈ L¹ for s > 1. Quantitatively κ_s(δ) ≍ δ^{s−1} for 1 < s < 3 and ≍ δ² for s > 3. Hence ‖η_{t,0}‖·‖ψ_{t,0}‖ ≥ c_s(Vκ_s(t−t′))^{−1/2}.

Conrey (1989) shows that more than 2/5 of the zeros up to height T are simple and on the critical line. So (0,T] contains at least 0.4N(T) distinct ordinates, where N(T) ~ (T/2π)log T, and two of them differ by at most T/(0.4N(T)−1) = O(1/log T). Hence inf_{t≠t′}|t−t′| = 0 and sup‖η‖·‖ψ‖ = ∞.

In Hilbert-space form: ‖ψ_{t,m}‖ = 1/dist(η_{t,m}, closed span of the other η), since H ≅ (E₀^⊥)′ isometrically. Under GRH, which is what the manuscript sets out to prove, the same conclusion holds for every F and every χ.

**Fix.** In (2), delete "In particular {f_m} is bounded". The correct consequence is that boundedness of {x_m} makes {f_m} bounded away from 0. In (10.3.1.18)–(10.3.1.22), replace C by the label-dependent C_{k,j}:= max_{m′≤m}‖η_{k,j,m′}‖·‖ψ_{k,j,m}‖. The exact rank-one bound is

‖A_{(k,j)}‖_{S₁} ≤ Σ_m Σ_{i≤m} binom(m,i) |φ̂^{(i)}(it_{k,j})| ‖ψ_{k,j,m}‖ ‖η_{k,j,m−i}‖.

Its sum over (k,j) must then be proved finite. That requires a quantitative lower bound on dist(η_{k,j,m}, span of the other η) that the decay of φ̂^{(i)}(it) beats, uniformly in χ. Alternatively, one needs a block estimate that does not pass through the individual products.

---

<a id="issue-15"></a>
### Issue 15 — (10.3.1.22)

**Issue.** The index range starts at m = 1 and drops σ<sub>0</sub>.

**Repair and status.** Repair: include m = 0. Lean: the block costs include every index m = 0, …, n − 1, and the binomial block has trace n·a<sub>0</sub> (`Round175A.projected_block_nuclear_cost`, `SpectralRound1B.trace_of_binomial_jet_action`).

**Printed.**
- (10.3.1.19), p. 451: "… for 0 ≤ m ≤ N_s(ρ)−1, and σ_m(A_{K,(k,j)}) = 0 for m ≥ N_s(ρ)."
- p. 451: "Since, for every integer m ≥ 1, we have σ_m(A_{K,(k,j)}) = σ_m(A_{K′,(k,j)}) …"
- (10.3.1.22), p. 451: "σ_m(A_{(k,j)}) ≤ N_s·C·2^{N_s−1}Σ_{0≤i≤N_s−1}|φ̂^{(i)}(t_{k,j})| for 1 ≤ m ≤ N_s(ρ)−1, and σ_m(A_{(k,j)}) = 0 for m ≥ N_s(ρ)."

**Problem.** Under the 0-based convention fixed by (10.3.1.19), (10.3.1.22) leaves σ₀ = ‖A_{(k,j)}‖_{op} unbounded. Under a 1-based convention its "σ_m = 0 for m ≥ N_s" would be false. Either way one singular value is lost.

**Derivation.**
- With 0-based indexing (σ₀ ≥ σ₁ ≥ …, σ_m = 0 for m ≥ rank), ‖A_{(k,j)}‖^p_{S_p} = Σ_{m=0}^{N_s−1}σ_m^p. The printed bound covers only m ≥ 1, so the S_p norm is not controlled.
- With 1-based indexing, "σ_m = 0 for m ≥ N_s" asserts rank ≤ N_s − 1. But the matrix (10.3.1.17) is lower triangular with diagonal φ̂(it_{k,j}), so it has rank N_s whenever φ̂(it_{k,j}) ≠ 0.

**Fix.** Read "for 0 ≤ m ≤ N_s(ρ)−1" in (10.3.1.22) and "m ≥ 0" at p. 451. The bound for σ₀ follows from (10.3.1.20) by the same limit in K. Also write φ̂^{(i)}(it_{k,j}) for φ̂^{(i)}(t_{k,j}) in (10.3.1.18)/(10.3.1.22), consistent with the use at p. 452.

---

<a id="issue-16"></a>
### Issue 16 — Theorem 10.3.2.1

**Issue.** Stated for s > 1 but used for s ≥ 0; the proof gives Schatten-class convergence for p > 1, not trace class; the strip case cites the line-case Theorem 10.3.1.1.

**Repair and status.** Repair: first-power (trace-class) costs for all s ≥ 0 on the closed strip. Lean: every checked statement is for s ≥ 0, on the closed strip including the line, with first-power costs (`Round175A`, `Round180G`, `Round197H`).

**Printed.**
- (i) Thm 10.3.2.1, p. 453: "a, s ∈ ℝ … with s > 1". Thm 10.4.2.8, p. 463: "a, s real numbers, s ≥ 0", invoking (10.3.2.2)/(10.3.2.3) (p. 463). Thm 10.4.2.1 (p. 459) and Thm 10.4.2.2 (p. 460) also say s ≥ 0. The §10.4 preamble, p. 455: "We fix a real number s ≥ 0, and we assume s > 1 …".
- (ii) p. 459: "(10.4.2.5) P^spec_a∘A(φ) = S_a∘A^spec_a(φ)∘Q_a … and A^spec_a(φ) is the operator from (10.3.1.2) of Theorem 10.3.1.1." p. 459: "By Theorem 10.3.1.1, A^spec_a(φ) is nuclear." The same substitution appears in Thm 10.4.2.2's statement (p. 460: "nuclear operator from (10.3.1.2), whose trace is computed by the formula in (10.3.1.3) of Theorem 10.3.1.1"), in Prop. 10.4.2.4 (p. 460) and at p. 460.
- (iii) p. 454: "…converges in the S₁-norm topology. We aim at deducing that the sequence … in (10.3.2.1) also converges in the S₁-norm". p. 454: "In order to prove that it converges for every p > 1". p. 455: "obtain the desired convergence of (10.3.2.7) for every p > 1".

**Problem.**
- (i) For s ∈ [0,1] the theorems of §10.4.2 are stated without proof. When α > 0 the interior η are in W^{−s}_I for every s ≥ 0 (they decay exponentially), so the strip basis is not empty. But every nuclearity input requires s > 1: Thms 10.3.1.1 and 10.3.2.1, Prop. 10.2.2.2, and Prop. 9.1.2.6.
- (ii) For α > 0, A^spec_a(φ) acts on H^s_{F,a,I}. Thm 10.3.1.1 is about H^s_{F,a} (I = {0}). The proof needs Thm 10.3.2.1.
- In Thm 10.4.2.2 the cited trace formula (10.3.1.3) counts only zeros on Re = a. For α > 0 the correct formula (10.3.2.3) also counts zeros a+b+it with 0 < |b| ≤ α. So the statement of 10.4.2.2 is wrong, not only its citation.
- The proof of 10.4.2.2 (p. 461) does switch to 10.3.2.1.
- (iii) Convergence of Σ X^p for p > 1 does not give S₁ convergence. It does not give S_p convergence either, because the blocks are not mutually orthogonal.

**Derivation of (iii).** In the proof of 10.3.1.1 the S₁-Cauchy step uses ‖Σ_{(k,j)∈F}A_{(k,j)}‖_{S₁} ≤ Σ_F N_s X_{k,j}, where X_{k,j} is the right side of (10.3.1.22). This needs Σ X_{k,j} < ∞, i.e. p = 1.

Counterexample to the weaker statement: on ℓ² let T_n = n^{−1}e₁⊗e₁. Then Σ_n‖T_n‖^p_{S_q} = Σn^{−p} < ∞ for every p > 1 and every q. Yet Σ_{n≤N}T_n = H_N e₁⊗e₁ with H_N → ∞, so the series diverges in every S_q and in operator norm.

The A_{(k,j)} have non-orthogonal ranges and co-ranges (neither the ψ nor the η are orthogonal), so no orthogonality argument rescues p > 1.

**Fix.**
- (i) Restate 10.4.2.1, 10.4.2.2 and 10.4.2.8 for s > 1. Downstream, Thm 10.4.3.5 (p. 472) already assumes s > 1. Otherwise give a separate proof for 0 ≤ s ≤ 1.
- (ii) For α > 0, cite Thm 10.3.2.1 and (10.3.2.2)/(10.3.2.3) at p. 459, p. 459, p. 460, p. 460 and p. 460.
- (iii) Prove Σ_{k,j} N_{I,s}C_{k,j}2^{N_{I,s}−1}Σ_i|M(φ)^{(i)}(b+it)| < ∞, i.e. the p = 1 case. The corrected integration-by-parts bound of Issue 17, with N large, gives this for the M(φ) part. It does not remove the dependence on C_{k,j} (Issue 14, Issue 13).

---

<a id="issue-17"></a>
### Issue 17 — (10.3.2.8)–(10.3.2.11)

**Issue.** The log-power factors are replaced by a fixed Sobolev weight, although the jet order is unbounded.

**Repair and status.** Repair: keep the factors R<sup>m−i</sup>; the cost grows polynomially in m. Lean: on the actual C<sub>K</sub>, for both tests and every jet order, |∂<sup>m</sup>M(h)(z)| ≤ e<sup>αR</sup>R<sup>m</sup>‖h‖<sub>1</sub> (`Round175G.genuine_compact_mellin_derivative_bound`), and height decay with variable jet order (`Round180D.variable_order_polynomial_cost`).

Notation: I write j for the manuscript's derivative order i, to avoid a clash with √−1.

**Printed.**
- p. 454: "N_{I,s}, contrary to N_s, is unbounded if α > 0." p. 454: "We assume … that we have i ≥ N."
- (10.3.2.8), p. 455: |z^N M(φ)^{(j)}(z)| ≤ ∫∫|(t∂_t)^N(φ(τ(t)g)(log t)^j)t^{Re z}| dµ¹(g) dt/t.
- (10.3.2.9), p. 455: ≤ Σ_{0≤n≤N} binom(N,n) ∫∫ |(t∂_t)^{N−n}φ(τ(t)g)|·(j!/(j−n)!)·|log t|^{j−n} t^{Re z} dµ¹ dt/t.
- (10.3.2.10), p. 455: ≤ Σ_{0≤n≤N} binom(N,n) ∏_{0≤n≤N−1}(j−n) ∫∫ |(t∂_t)^{N−n}φ(τ(t)g)| max{t^α,t^{−α}}(1+|log t|²)^{s/2} dµ¹ dt/t.
- (10.3.2.11), p. 455: |M(φ)^{(j)}(z)| ≤ C_{N,I,s}(φ)∏_{0≤n≤N−1}(j−n)/|z|^N "for all z ∈ C_I, Im z ≠ 0", where C_{N,I,s}(φ) is "the value of each integral in the last finite sum" and so does not depend on j.
- p. 455: "∏_{0≤n≤N−1}(i−n) = C·N·O(log|τ|)".

**Problem.**
- The step (10.3.2.9) → (10.3.2.10) needs |log t|^{j−n}t^{Re z} ≤ max{t^α,t^{−α}}(1+log²t)^{s/2} on supp φ. That fails once j − n > s and |log t| > 1. The derivation never uses that z is a zero, so the restriction j ≤ N_{I,s}(z)−1 does not help; and the interior j are unbounded by the manuscript's own remark at p. 454.
- Separately, ∏_{n<N}(j−n) ≤ j^N = O((log|τ|)^N), not C·N·O(log|τ|).

**Derivation.**
- *Counterexample.* Let κ ∈ C_c^∞(ℝ) with κ ≥ 0, supp κ ⊂ [2,3] and ∫_{5/2}^3κ > 0. Set φ(g):= κ(log|g|_F)|g|_F^{−√−1} ∈ D(C_F), take χ = 1 and z = √−1 (so Re z = 0 ∈ I, Im z = 1 ≠ 0, |z| = 1). Then
M(φ)^{(j)}(z) = V∫κ(u)e^{−√−1u}e^{√−1u}u^j du = V∫κ(u)u^j du ≥ V(5/2)^j∫_{5/2}^3κ.
- The chain (10.3.2.8)–(10.3.2.11) would give |M(φ)^{(j)}(z)| ≤ C_{N,I,s}(φ)j^N for all j ≥ N, with C independent of j. That contradicts the exponential lower bound for large j.
- *Correct estimate.* If supp φ ⊂ {|log|g|| ≤ R} with R ≥ 1 and |Re z| ≤ α, then
|z|^N|M(φ)^{(j)}(z)| ≤ Σ_{n≤min(N,j)} binom(N,n)(j!/(j−n)!)R^{j−n}e^{αR}‖(t∂_t)^{N−n}φ‖_{L¹(µ)} ≤ (1+j)^N R^j e^{αR}D_N(φ),
where D_N(φ) = max_{n≤N}‖(t∂_t)^nφ‖_{L¹(µ)}. No assumption j ≥ N is needed, since terms with n > j vanish.
- *Absorbing R^j.* For zeros, j ≤ N(ρ)−1 ≤ C_χ log(|τ|+2), with C_χ depending on the conductor of χ. Then R^j ≤ (|τ|+2)^{C_χ log R}, and similarly 2^{N(ρ)} ≤ (|τ|+2)^{C_χ log 2}. Both are absorbed by choosing N > C_χ(log R + log 2) + 3, which gives the p = 1 sum of the M(φ) factors over zeros (O(log T) zeros per unit height).

**Fix.** Replace (10.3.2.10)–(10.3.2.11) by the corrected estimate above, keeping R^j and (1+j)^N. Choose N depending on R and C_χ, and establish uniformity in χ. Correct ∏(j−n) to O((log|τ|)^N).

---

<a id="issue-18"></a>
### Issue 18 — Lemma 10.4.1.2

**Issue.** The isometry of Q on G<sup>⊥</sup> is credited to the open mapping theorem, which gives only a topological isomorphism.

**Repair and status.** Repair: the quotient-norm infimum with Pythagoras. Lean: ‖Sq‖ = ‖q‖, Q∘S = id and range S = G<sup>⊥</sup> (`Round173H.quotientSection_isometry_norm`).

**Printed.** Statement, p. 456: "The assignment S_a: ψ ↦ P^spec_a(ψ̃) does not depend on the choice of ψ̃, and it is an isometric linear topological isomorphism S_a: H → P^spec_a W." Proof, pp. 456–457: "Q_a is an isometric linear topological isomorphism from P^spec_a W to H, since it is surjective, injective and open, being a quotient map. Its inverse, both left and right, is continuous, and hence S_a is continuous and bijective, hence a linear topological isomorphism by [NB, Thm.14.4.5]. Since its inverse is isometric, so is S_a."

The norm on H is the quotient norm. Lines p. 445 say H^s_{F,a,I} "is the quotient Hilbert space, equivalently (by the Open Mapping Theorem) the completion … with respect to the normed topology induced by the quotient ||·||_{I,s}-norm". So ||ψ||_H = inf{ ||ψ̃||: Qψ̃ = ψ }.

**Problem.** Being surjective, injective, continuous and open makes Q|_V a topological linear isomorphism V → H. It does not make it an isometry, because isometry is a metric property and those four properties are topological. The phrase "being a quotient map" also does not justify openness of the restriction Q|_V. Restricting an open map to a closed subspace need not give an open map. Here openness does hold, but for another reason: Q(U) = Q(U+G) and U+G = (P^spec)^{-1}(U).

**Derivation.** Replace ||·||_H by the equivalent norm ||·||':= 2||·||_H. Then Q|_V is still a continuous, open linear bijection V → (H, ||·||'), but ||Qv||' = 2||v||. So the properties the proof cites cannot imply isometry. The missing step is the distance formula. For v ∈ V and g ∈ G we have ⟨v, g⟩ = 0, so

||v + g||² = ||v||² + ||g||² ≥ ||v||², with equality iff g = 0.

Hence ||Qv||_H = inf_{g∈G} ||v+g|| = ||v||.

**Fix.** Replace the sentence at pp. 456–457 with: "For v ∈ P^spec W and g ∈ G, Pythagoras gives ||v+g||² = ||v||² + ||g||², so ||Q_a v||_H = inf_g ||v+g|| = ||v||. Thus Q_a|_{P^spec W} is isometric. It is onto H because Q_a = Q_a ∘ P^spec. It is therefore an isometric isomorphism with inverse S_a." This gives ||Q|| ≤ 1 and ||S_a|| = 1 when H ≠ 0. The Open Mapping Theorem is not needed. The same misattribution ("isometric to the quotient … by the Open Mapping Theorem") also appears at p. 439 for (10.2.1.2) and at p. 445 for (10.2.2.2). In both places the isometry needs a metric argument, not open mapping.

---

<a id="issue-19"></a>
### Issue 19 — Lemma 10.4.1.2, proof

**Issue.** Surjectivity of S<sub>a</sub> is drawn from Q∘S = id, which gives injectivity; uniqueness is argued circularly.

**Repair and status.** Lean: range S = G<sup>⊥</sup> from S∘Q = id on G<sup>⊥</sup> (`Round173A.range_S`), together with Q∘S = id and injectivity.

**Printed.** Lines p. 456: "if ϕ is orthogonal to G and satisfies Q_a(ϕ) = ψ, then so does P^spec_a(ϕ) by (10.4.1.4), and so ϕ = P^spec_a(ϕ)." Lines p. 456: "This shows that formation of S_a does not depend on the choices … Since Q_a ∘ S_a is the identity on H, we deduce that S_a: H → P^spec_a W is linear and surjective, and Q_a is a continuous left-inverse." The statement at p. 456 reads "S_a: ϕ ↦ P^spec_a(ψ̃)".

**Problem.**
1. Q ∘ S = id_H implies that S is injective (and Q surjective). It does not imply that S is surjective.
2. The argument at p. 456 shows only that P^spec fixes G^⊥, which holds by definition. It does not show that ϕ = P^spec(ψ̃) for an arbitrary lift ψ̃, and it does not show independence of the choice.
3. Typo: the variable in "ϕ ↦" should be ψ.

**Derivation.** Uniqueness: let ϕ ∈ V with Qϕ = ψ, and let ψ̃ be any lift of ψ. Then ϕ − P^spec ψ̃ ∈ V, and Q(ϕ − P^spec ψ̃) = ψ − Qψ̃ = 0 because Q = Q ∘ P^spec. So ϕ − P^spec ψ̃ ∈ V ∩ G = {0}. Independence of the choice: two lifts differ by an element of G = ker P^spec. Surjectivity onto V: for v ∈ V, S(Qv) = P^spec v = v, i.e. S ∘ Q|_V = id_V.

**Fix.** Replace the uniqueness argument with the one above, justify surjectivity by S ∘ Q|_V = id_V, and correct the typo to "S_a: ψ ↦ P^spec_a(ψ̃)".

---

<a id="issue-20"></a>
### Issue 20 — (10.4.2.8)

**Issue.** S<sub>a</sub><sup>−1</sup> is written where S<sub>a</sub> is meant.

**Repair and status.** Lean: every factorisation is P∘A = S∘Ā∘Q, with S on the left (`Round173H.projected_quotient_factorization`).

**Printed.** "(10.4.2.8) (P^spec_a∘A(φ))(ϕ) = (S_a^{−1}∘Q_a∘A(φ))(ϕ) = (S_a^{−1}∘A^spec_a(φ)∘Q_a)(ϕ) … (S_a^{−1}(ψ) is the unique element ψ̃ of P^spec_a W^s_I(C_F) such that Q_a(ψ̃) = ψ …)"

**Problem.** By (10.4.1.5), S_a: H^s_{F,a,I} → P^spec_a W^s_I. So S_a^{−1} cannot be applied to Q_a A(φ)ϕ ∈ H^s_{F,a,I}, and its output would not lie in W^s_I. The parenthetical describes S_a, not S_a^{−1}.

**Derivation.** Both sides of (10.4.2.8) must lie in W^s_I. The composite S_a∘Q_a∘A(φ) is the only well-typed one, and it equals S_a∘A^spec_a(φ)∘Q_a by Q_a A(φ) = A^spec_a(φ) Q_a. This is exactly (10.4.2.5) at p. 459.

**Fix.** Replace S_a^{−1} by S_a three times at p. 459.

---

<a id="issue-21"></a>
### Issue 21 — Theorem 10.4.2.8, (10.4.2.21)–(10.4.2.34)

**Issue.** Bounds on the dual vectors are used as bounds on the lifts, and the upper bound in (10.4.2.24) is false (α = 0, F = ℚ, a = ½). Any absolute-value majorant is at least ‖φ‖<sub>L¹</sub> for every label, so it cannot be summed. The proof ends with “Return here and complete proof.”

**Repair and status.** Repair: minimal lifts and first-power costs, with the trace limit taken in the P∘A order. Lean: lower bounds and minimal lifts on the actual objects; Lemma 10.4.2.5 without the Schauder hypothesis; bounded lifts with divergent cost for the literal convolution (`Round112D.bad_bounded_quotient_lifts_not_summable`); the (10.4.2.20) limit under first-power summability (`MasulloTrace.shifted_convolution_cutoff_tsum_of_weighted_L2`); on the actual objects, for both tests, the P∘A trace limit from a supplied A∘P expansion (`Q.FullSourceCutoff.both_tests_PA_physical_limit_of_AP`).

**Printed.**
- (a) p. 463: "upon denoting by C > 0 the real number serving as upper bound to the W^s_I-norms of the basis elements such that 1/C serves as a lower bound to their norms (C > 0 exists by Proposition 10.2.2.2), we have (10.4.2.24) 1/C − ε < ‖ψ̃_{χ,t,b,m}‖_{W^s_I(C_F)} < C + ε … and choose the lifts in (10.4.2.23) accordingly."
- The lifts come from Lemma 10.4.2.5 (pp. 461–462). Its hypothesis (10.4.2.16) puts the *primal* quotient vectors x_m in a collar r ≤ ‖x_m‖_{E/E₀} ≤ r′.
- Its proof treats only the Schauder case (p. 462: "We discuss the case of a Schauder basis.⁷"; footnote 7 at p. 462: "Return here.").
- (b) p. 464: "The S₁-norm of the finite rank operators (10.4.2.25) A(φ)ψ̃ ⊗ η equals their S₂-norm …, computed as the square of the following integral (10.4.2.26) ∫∫ |∫φ(g)ψ̃(g^{−1}x)dµ(g) η(y)|² w_{I,s}(x)w_{I,s}(y)^{−1} d(µ⊗µ)." Then come the expansion (10.4.2.27), the shearing (x,y) ↦ (g₁x, g₁y) (10.4.2.28), and the binomial expansion of η(g₁y) (10.4.2.29)–(10.4.2.33).
- p. 464: "Using the estimate in (9.3.1.6) …, combined with (10.4.2.29) and un-doing the shearing, we obtain that up to a positive real constant independent of the choice label (χ,t,b,m), the following sum is an upper bound for the S₂-norm, and hence the S₁-norm, of (10.4.2.25): (10.4.2.34) Σ_k Σ_j N_{I,s}(ρ)2^{N_{I,s}(ρ)−1} (Σ_{0≤i≤N_{I,s}−1} |M(φ)^{(i)}(b_{k,j}+it_{k,j})|)²."
- (c) p. 464: "The remaining assertions of the Theorem follow as a consequence.⁸"; footnote 8 at p. 464: "Return here and complete proof."

**Problem.**
- (a) Prop. 10.2.2.2 bounds the dual vectors η in W^{−s}_I, not the primal lifts ψ̃. The upper bound in (10.4.2.24) does not follow and is false in admissible cases.
- (b) In a rank-one operator the factor ‖η‖ does not depend on t. Any bound that takes absolute values or passes through ‖ρ(g)‖ (as "using (9.3.1.6)" does) is bounded below by a positive constant for every label, so it cannot be summable. The phase that would produce M(φ)^{(i)}(b+it) cancels in the S₂ integrand. The "constant independent of the label" is not shown to be uniform over χ, b or the jet order m, and with Issue 14 and Issue 13 it is not uniform.
- (c) The author flags the proof as incomplete. The trace limit in (10.4.2.20) is never argued.

**Derivation.**
- (a) The lower bound is fine: 1 = ⟨η,ψ̃⟩ ≤ ‖η‖_{I,−s}‖ψ̃‖ ≤ C‖ψ̃‖.
- The upper bound fails, as in N1.3: ‖ψ̃_{t,b,0}‖_{W^s_I} ≥ ‖ψ_{t,b,0}‖_H ≥ 1/‖η_{t,b,0} − η_{t′,b,0}‖_{I,−s}, and ‖η_{t,b,0} − η_{t′,b,0}‖²_{I,−s} = V∫e^{2bu−2α|u|}·4sin²((t−t′)u/2)(1+u²)^{−s/2}du → 0 as t′ → t, by dominated convergence (valid for |b| < α and any s, and for |b| = α with s > 1).
- Thm 10.4.2.8 allows α = 0. With F = ℚ, χ = 1, a = ½ and b = 0, the Conrey gap argument of Issue 14 gives sup‖ψ̃‖ = ∞, so (10.4.2.24) fails. For α > 0 the same happens at b = ½ − a whenever |½ − a| < α.
- (b) The claimed Mellin factors cannot arise.
- (i) For a rank-one operator, ‖A(φ)ψ̃ ⊗ η‖_{S₁} = ‖A(φ)ψ̃‖_{W^s_I}·‖η‖_{W^{−s}_I}. By Prop. 10.2.2.2's own formula, ‖η_{χ,t,b,m}‖² = V∫e^{2bu−2α|u|}u^{2m}(1+u²)^{−s/2}du, which is independent of t and χ. So any decay in t must come from ‖A(φ)ψ̃‖.
- In (10.4.2.26) the y-integral separates as ‖η‖². In the S₂ integrand |η(g₁y)|² = |g₁y|^{2b}(log|g₁y|)^{2m}, so the phase |g₁|^{it} expanded in (10.4.2.29)–(10.4.2.33) cancels. The factors M(φ)^{(i)}(b+it) = ∫φχ|g|^{b+it}(log|g|)^i dµ in (10.4.2.34) cannot come out of this computation.
- (ii) By Minkowski's inequality and (9.3.1.6), ‖A(φ)ψ̃‖ ≤ (∫|φ(g)|‖ρ(g)‖dµ)‖ψ̃‖. Moreover ‖ρ(g)‖ ≥ max{|g|^α,|g|^{−α}} ≥ 1: test on u supported where log|h| → ±∞, where w(gh)/w(h) → |g|^{±2α}. Since ‖ψ̃‖‖η‖ ≥ 1 by biorthogonality, this majorant is ≥ ‖φ‖_{L¹(µ)} for every label, so it is not summable.
- The fully pointwise majorant Φ = |φ|∗|ψ̃| does no better. ‖Φ‖_{L¹} = ‖φ‖_{L¹}‖ψ̃‖_{L¹}. For α = 0 and m = 0 we have |η_{t,0,0}| ≡ 1, so ‖ψ̃‖_{L¹} ≥ |⟨η,ψ̃⟩| = 1. By Prop. 9.1.2.6 (s > 1), ‖Φ‖_{s,2} ≥ C_s^{−1}‖φ‖_{L¹}, again a label-independent lower bound.
- (iii) The lifts are not pinned down by the printed conditions. Fix one h ∈ S_E(C_F) ∩ W^s_{a,I}H₀ with A(φ)h ≠ 0 and ‖h‖ small, and replace every ψ̃_label by ψ̃_label + h.
- This preserves (10.4.2.17) (η annihilates W^s_{a,I}H₀), the open condition (10.4.2.24), and membership in S_E.
- It adds A(φ)h ⊗ Σ_{F}η_label to every partial sum. For α = 0 and m = 0, ‖Σ_{t∈F}η_{t,0}‖²_{−s,2} = Σ_{t,t′∈F}K(t−t′) ≥ |F|K(0). Here K(δ) = V∫e^{iδu}(1+u²)^{−s/2}du is the Bessel-potential kernel, which is positive.
- So the added term diverges in S₁, and at least one of the two choices of lifts gives a divergent series.
- (iv) (10.4.2.34) is a sum of squares. S₁ convergence of Σ T_label needs the first-power sum Σ‖T_label‖_{S₁}.
- (c) Footnote 8 (p. 464) is attached to the sentence that is supposed to deliver (10.4.2.20). Both inputs are flagged too: footnote 6 (p. 446) on the one-line proof of Thm 10.2.2.1 (p. 446), and footnote 7 (p. 462) on the Schauder-only proof of Lemma 10.4.2.5, which is applied here to a Markushevich basis.

*Operator order (context).* By (10.4.1.10)–(10.4.1.11) (pp. 457–458), A∘P^spec = P^spec∘A + P^geom∘A∘P^spec, and the manuscript states P^geom∘A∘P^spec ≠ 0 (p. 458). Nuclearity of A∘P^spec, the operator in (10.4.2.20), is therefore equivalent to nuclearity of the off-diagonal block P^geom A P^spec. Neither 10.3.2.1 nor 10.4.2.1 controls that block, and the rank-one estimate above is the only argument offered for it. If the block is nuclear, the trace equality follows from (P^geom A P^spec)² = 0.

**Fix.** Choose lifts ψ̃_label whose Mellin transforms are localized near b+it, and prove Σ_label ‖A(φ)ψ̃_label‖_{W^s_I}‖η_label‖_{W^{−s}_I} < ∞ (or a block version). This sum must exploit the oscillation of the Mellin transform and be uniform in χ, b and m; equivalently, one needs a trace-class bound for P^geom A(φ) P^spec. Replace (10.4.2.24) by the true bounds (lower bound 1/C; no uniform upper bound). Then prove the cutoff limit ‖(M_ρ − 1)A(φ)P^spec‖_{S₁} → 0.

---

<a id="issue-22"></a>
### Issue 22 — (10.4.2.21)–(10.4.2.23)

**Issue.** The exponent is printed a + b + it (it should be b + it), the zero condition L(s + b + it, χ) uses the Sobolev index s, b is unrestricted, and the multiplicity is untruncated.

**Repair and status.** Lean uses η = χ|g|<sup>b+it</sup>(log|g|)<sup>m</sup> with zeros at a + b + it, the admitted range of b, and the corrected boundary count from the (10.2.2.5) row above (`genuineMellinJet`).

**Printed.**
- (10.2.2.4), p. 446: η_{χ,t,b,m}(g):= χ(g)|g|^{it+b}(log|g|)^m, where "ρ_{χ,t,b}:= χ|·|^{a+it+b} is a zero of L(s,χ)".
- (10.3.2.3), p. 454: the sum is over "t ∈ ℝ, b ∈ [−α,α]: L(a+b+it,χ) = 0", with integrand φ(g)χ|g|^{b+it}.
- (10.4.2.21), p. 463: "ψ_{χ,t,b,m}, (t,b) ∈ ℝ²: L(s+b+it,χ) = 0, 0 ≤ m ≤ N(ρ_{χ,t,b,m}) − 1".
- (10.4.2.22), p. 463: "η_{χ,t,b,m}(g) = χ(g)|g|^{a+b+it}(log|g|)^m", same index set. (10.4.2.23), p. 463: same index set.
- (10.4.2.29), p. 464: η_{χ,t,b,m}(gy) = χ(gy)|gy|^{b+it}(log|gy|)^m. (10.4.2.34), p. 464: M(φ)^{(i)}(b+it).

**Problem.** (10.4.2.22) contradicts (10.2.2.4), (10.4.2.29), (10.3.2.3) and (10.4.2.34). Its exponent should be b+it. The zero condition L(s+b+it,χ) = 0 uses the Sobolev degree s where a belongs. Two further index errors sit in the same displays: b is unrestricted, and the multiplicity is the full N instead of N_{I,s}.

**Derivation.**
- *Which exponent annihilates the subspace.* For f ∈ H₀, ⟨|·|^a f, χ|·|^z(log|·|)^m⟩ = ∫ f χ |g|^{a+z}(log|g|)^m dµ = ∂^m_w M_χ(f)(w) at w = a+z. The Mellin images of H₀ are the multiples of L(·,χ) (p. 441). So these functionals vanish on |·|^a H₀ exactly when a+z is a zero of order > m. For the zero a+b+it this gives z = b+it. The exponent a+b+it would instead correspond to the point 2a+b+it.
- *Membership in W^{−s}_I.* χ|g|^{c+it}(log|g|)^m lies in W^{−s}_I only if ∫e^{2cu−2α|u|}u^{2m}(1+u²)^{−s/2}du < ∞, which needs |c| ≤ α. With c = a+b this fails whenever |a+b| > α, for example when a > 2α.
- *The letter s.* In Thm 10.4.2.8 (p. 463), s is the Sobolev degree ("a, s real numbers, s ≥ 0"). So "L(s+b+it,χ) = 0" picks out zeros on Re = s+b, which is not the intended set.
- *b unrestricted.* "(t,b) ∈ ℝ²" must be b ∈ [−α,α]. By the integral above, η ∉ W^{−s}_I when |b| > α.
- *Multiplicity.* "N(ρ_{χ,t,b,m})" must be N_{I,s}(ρ_{χ,t,b}). At b = ±α with m ≥ (s−1)/2, ∫₀^∞u^{2m}(1+u²)^{−s/2}du diverges. (10.4.2.34) itself uses N_{I,s}.

**Fix.** In (10.4.2.21)–(10.4.2.23), index by (t,b) ∈ ℝ×[−α,α] with L(a+b+it,χ) = 0 and 0 ≤ m ≤ N_{I,s}(ρ_{χ,t,b}) − 1. In (10.4.2.22), write η_{χ,t,b,m}(g) = χ(g)|g|^{b+it}(log|g|)^m.

---

<a id="issue-23"></a>
### Issue 23 — Theorem 10.4.2.8, proof

**Issue.** The lifted rank-one sum equals A∘P<sup>spec</sup> only if A P<sup>geom</sup>ψ̃ = 0, which the proof never arranges.

**Repair and status.** Lean: operator-norm convergence of the lifted sums to A∘P forces A(u<sub>i</sub> − Pu<sub>i</sub>) = 0 (`Round91C.liftedSum_convergence_forces_residual_zero`); on the actual objects P<sup>spec</sup>∘A∘P<sub>W</sub> = 0 for both tests; an A∘P expansion transfers to P∘A (`Q.OrderedNuclear.AP_factors_to_PA`).

**Printed.** p. 464: "We note that we can arrange the ψ̃_{χ,t,b,m} to be in S_E(C_F), by Lemma 10.4.2.5." p. 464: "… the S₁-limit of the sum of the rank-1 operators from (10.4.2.25) exists and agrees with A(φ)∘P^spec_a, which is therefore nuclear and has the same trace as P^spec_a∘A(φ)."

**Problem.** The sum equals A(φ)∘L∘Q_a, where L is the chosen lifting. This equals A(φ)∘P^spec_a only if A(φ)P^geom ψ̃ = 0 for every label. Nothing in the proof arranges that: Lemma 10.4.2.5 controls norms only, and smooth lifts in S_E are in general not orthogonal to W^s_{a,I}H₀.

**Derivation.** Suppose T:= Σ_label⟨·,η_label⟩A(φ)ψ̃_label converges. For each label j, Lemma 10.4.1.2 gives S_aψ_j = P^spec ψ̃_j, and ⟨S_aψ_j, η_i⟩ = δ_{ij} because η_i annihilates W^s_{a,I}H₀. Hence T(S_aψ_j) = A(φ)ψ̃_j, while A(φ)P^spec(S_aψ_j) = A(φ)S_aψ_j. So T = A(φ)P^spec forces A(φ)(ψ̃_j − P^specψ̃_j) = A(φ)P^geomψ̃_j = 0 for all j.

In general D:= T − A(φ)P^spec = Σ⟨·,η_j⟩A(φ)P^geomψ̃_j. D maps into the A(φ)-invariant subspace W^s_{a,I}H₀ and vanishes on it, so D² = 0. If D is nuclear, Lidskii gives Tr D = 0, so the trace claim survives. The operator identity does not, and nuclearity of A(φ)P^spec cannot be read off from T.

**Fix.** Take the orthogonal lifts ψ̃_j:= S_aψ_j, giving up S_E-membership or proving what is needed for them. Alternatively, prove nuclearity of D separately.

---

<a id="issue-24"></a>
### Issue 24 — (10.4.3.1)

**Issue.** The factor s(s − 1) does not clear the shifted poles −iτ and 1 − iτ of norm-twisted characters and adds zeros at 0 and 1, which shrinks W<sub>χ</sub> by codimension 2.

**Repair and status.** Repair: clear with (z + iτ)(z − 1 + iτ). Lean: the failure is proved for F = ℚ (`MasulloGRH.unshiftedClearing_spurious_zero`, `unshiftedClearing_not_continuous`); the shifted factor gives exactly the two poles and no added zeros (`Round12A.norm_twist_polar_divisor`); for general K, given a continuation.

**Printed.** Line p. 464: "We let F be a number field and χ ∈ Ĉ_F a continuous character." Lines p. 465: "We defined: (10.4.3.1) Λ(s, χ):= (½ s(s−1))^{δ_χ} L(s, χ), where L(s, χ) = L(χ|·|^s_F) is the Hecke L-function, and δ_χ = 1 if χ|C¹_F = 1, and δ_χ = 0 if χ|C¹_F ≠ 1." Then W_χ:= Λ(s, χ) O(C) ∩ AS(C) (top row of (10.4.3.2)). Line p. 465: "By Theorem 6.3.2.1, L^{-1}, the top leftmost vertical arrow in (10.4.3.2), is a linear topological isomorphism" W_χ → H_{0,cont}(χ|C¹_F, S_0(A_F)). Lines p. 465 record the vertical shift i x_0, defined by χ(τ(t)) = t^{i x_0}.

**Problem.** If χ|C¹_F = 1, then χ = |·|_F^{iτ} for a unique τ ∈ R, and x_0 = τ. Notation 10.2.1.1 (p. 440) allows any unitary lift as the base point of a component, so for ω = 1 the base point may be |·|^{iτ} with τ ≠ 0. For such χ the poles are at s = −iτ and s = 1−iτ, not at 0 and 1. The manuscript uses the shifted factor elsewhere:

- Theorem 6.3.2.1(1), p. 304: the Mellin range is ((s+it_0)(1−s−it_0))^δ L(s, χ) O(C) ∩ AS(C), with residues at s = −it_0, 1−it_0 (p. 304).
- Theorem 7.1.4.2(1), ll.19136–p. 326: the ideal is (s+ix_0)^δ (1−s−ix_0)^δ L(s, χ) O(C).

So "We defined" at p. 465 misquotes the earlier definition by dropping the shift.

**Derivation.** Here L(s, χ) = ζ̂_F(s+iτ), the completed function, as in (6.3.2.8). ζ̂_F has simple poles only at 0 and 1, and it does not vanish on Re s = 0 or Re s = 1. Take τ ≠ 0.

1. At s = −iτ the factor is ½(−iτ)(−iτ−1) ≠ 0. At s = 1−iτ it is ½(1−iτ)(−iτ) ≠ 0. So Λ(s, χ) keeps both simple poles and is not entire.
2. Λ acquires simple zeros at s = 0 and s = 1, because ζ̂_F(iτ) ≠ 0 and ζ̂_F(1+iτ) ≠ 0.
3. Let R_χ:= (s+iτ)(1−s−iτ) ζ̂_F(s+iτ) O(C) ∩ AS(C), the true range by Theorem 6.3.2.1(1). For f = (s+iτ)(1−s−iτ) ζ̂_F(s+iτ) h ∈ R_χ, the quotient f/Λ = −2(s+iτ)(s−1+iτ) h / (s(s−1)) is entire iff h(0) = h(1) = 0, i.e. iff f(0) = f(1) = 0. Hence
W_χ = { f ∈ R_χ: f(0) = f(1) = 0 }.
4. The inclusion is strict. Take f(s) = (s+iτ)(1−s−iτ) ζ̂_F(s+iτ) e^{s²}. It lies in R_χ, since |e^{(σ+it)²}| = e^{σ²−t²} decays like a Gaussian on vertical strips and the cleared ζ̂_F grows at most polynomially there. Its value at 0 is f(0) = iτ(1−iτ) ζ̂_F(iτ) ≠ 0.

Consequences:

- L^{-1}(W_χ) is a proper closed subspace of codimension 2 in H_{0,cont}. So the claim at p. 465 is false.
- K_χ = AS(C)/W_χ has two extra dual functionals, f ↦ f(0) and f ↦ f(1). These are not among the D_{ρ,m} of (10.4.3.3), which are indexed by zeros of L.
- The diagram (10.4.3.2) does not hold as printed.

For τ = 0 (χ = 1) the display is correct.

**Fix.** Use Λ(s, χ):= (½ (s+ix_0)(s−1+ix_0))^{δ_χ} L(s, χ), with x_0 = x_0(χ). This matches 6.3.2.1(1) and 7.1.4.2(1) up to a constant. Alternatively, require in Notation 10.2.1.1 that the base point of the component ω = 1 be the trivial character, so that x_0 = 0.

---

<a id="issue-25"></a>
### Issue 25 — (10.4.3.43)–(10.4.3.45)

**Issue.** The tensor computes P∘A but the conclusion prints A∘P. By Remark 10.4.1.4 the two differ by P<sup>geom</sup>AP<sup>spec</sup> ≠ 0, and the geometric kernel (10.4.3.50) inherits the order.

**Repair and status.** Repair: keep P∘A. Lean, on the actual objects for every number field and both tests, with parameter conditions only: the compression equals P∘A, the coefficient tensor sums to P∘A, A∘P − P∘A = P<sup>geom</sup>AP<sup>spec</sup>, and the finite-level residual kernels converge to P∘A with cutoffs (`PIntegrated.geometric_trace_global_operator_assembly`); at finite rank the actual-jet kernel is P<sub>F</sub>∘A (`actual_finite_PA_kernel_action`).

#### (10.4.3.43)–(10.4.3.45), pp. 472–473: the construction computes PA but is printed as AP

**Printed.** The finite-rank kernels are Σ_i A(φ)′η_i ⊗ S_a(ψ_i) (10.4.3.43). The map ξ_π sends Σ φ_k ⊗ ψ_k to the operator Σ ⟨φ_k, ·⟩ψ_k (10.4.3.44). The conclusion is ξ_π(K^spec) = A(φ) ∘ P_a^spec (10.4.3.45).

**Derivation.** At every finite stage,

ξ_π(Σ A(φ)′η_i ⊗ S_aψ_i)(x) = Σ ⟨A(φ)′η_i, x⟩ S_aψ_i = Σ ⟨η_i, A(φ)x⟩ S_aψ_i = S_a(Π(A(φ)x)),

where Π(y) = Σ⟨η_i, y⟩ψ_i is the coefficient expansion of Q_a y. Line p. 459 gives S_a(Q_a y) = P_a^spec(y) for any lift y. In the limit the operator is therefore **P_a^spec ∘ A(φ)**. This agrees with the manuscript's own factorisation (10.4.2.5): P_a^spec ∘ A(φ) = S_a ∘ A_a^spec(φ) ∘ Q_a.

**What invariance gives.** By (10.4.2.6), p. 459, the geometric space G = W^s_{a,I}H_{0,cont} is A(φ)-invariant. So P A (1−P) = 0, which means **PA = PAP**. To get AP = PA you would also need (1−P)AP = 0, i.e. G^⊥ invariant as well (G reducing). Convolution is not unitary in the weighted space, so this does not come for free.

**Counterexample to the inference.** Take H = ℓ² ⊕ ℓ², G = ℓ² ⊕ 0, P(x, y) = (0, y), A(x, y) = (y, 0).
- A(G) = 0 ⊆ G, so G is invariant.
- PA = 0, which is trace class.
- AP = A, a partial isometry of infinite rank, which is not compact.

So invariance plus PA nuclear gives neither AP = PA nor AP trace class. The finite version is P = diag(1, 0), A = [[0,0],[1,0]], G = ker P: then PA = 0 and AP = A. This refutes the inference. It is not a calculation with the manuscript's actual A.

**Knock-on effect on the geometric kernel.** (10.4.3.50), p. 473, defines k^geom = φ(xy⁻¹) − k^spec. If k^spec is the kernel of PA, then k^geom represents A − PA = (1−P)A, not A − AP = A(1−P). The two differ by

(1−P)A − A(1−P) = AP − PA = AP − PAP = **(1−P)AP**.

This block maps E into G, so its diagonal in any basis adapted to E ⊕ G is zero. If it is trace class, its trace is 0. The geometric side, however, is evaluated through cut-off traces and diagonal integrals. The cutoff M_ρ does not preserve E ⊕ G, so Trace(M_ρ(1−P)AP) need not vanish. Tracelessness of the block therefore does not let you swap the kernels.

**Related.** Theorem 10.4.2.8, p. 463, is titled "convolution after projection" and states Trace(M_ρ ∘ A(φ) ∘ P_a^spec) = Trace(A_a^spec(φ)) + o(1). But (10.4.2.5) factors P∘A, not A∘P, through A_a^spec. In general: a cut-off trace limit needs the actual operator to be trace class, with strong convergence and ‖x − P_i x‖ ≤ ‖x‖. It cannot rest on an assumed PA/AP commutation.

**Fix.** There are three options:
- keep PA and redo the local calculation of Chapters 11–12 with the kernel of (1−P)A;
- prove (1−P)AP trace class with cutoff control;
- prove a reducing-subspace theorem that gives AP = PA.

Trace cyclicity alone identifies neither the kernels nor the cut-off traces. The Lean geometry work uses PA throughout: `TraceRepairE.coefficient_kernel_is_PA` / `output_kernel_is_AP`, and `Spectral29B.genuine_projection_trace_original_nuclear_sum`.

#### Remark 10.4.1.4 makes (10.4.3.45) contradict the manuscript itself

**Printed.** (10.4.1.10), p. 457: P^geom∘A(φ)∘P^geom = A(φ)∘P^geom. (10.4.1.11), p. 458: P^spec∘A(φ)∘P^spec = P^spec∘A(φ). Lines p. 458: "we do not have the stronger commutation relations A(φ)∘P^geom = P^geom∘A(φ) and A(φ)∘P^spec = P^spec∘A(φ), ultimately because P^geom∘A(φ)∘P^spec ≠ 0 … with the sole exception of the case s = α = 0". In the I = {0} construction, (10.4.3.25), p. 470, and (10.4.3.28) represent P^spec∘A(φ).

**Derivation.** Write A∘P^spec = (P^spec + P^geom)∘A∘P^spec = P^spec∘A∘P^spec + P^geom∘A∘P^spec = P^spec∘A + P^geom∘A∘P^spec, using (10.4.1.11). So A∘P^spec − P^spec∘A = P^geom∘A∘P^spec, which the remark asserts is nonzero unless s = α = 0. The tensor in (10.4.3.43) computes P^spec∘A (item Issue 25). Therefore (10.4.3.45), ξ_π(K^spec) = A(φ)∘P^spec, is false by the manuscript's own Remark 10.4.1.4 whenever (s, α) ≠ (0, 0). The I = {0} case (10.4.3.25)–(10.4.3.28) already uses the P^spec∘A order, so the general case changed the order without justification.

#### Remark 10.4.1.4, pp. 457–458. The manuscript distinguishes P∘A(φ) from A(φ)∘P (context for (10.4.3.45))

**Printed.**
- Lines p. 457: "since Id = P^geom_a + P^spec_a, and since P^geom_{ρ,a} = M_ρ ∘ P^geom_a and P^spec_{ρ,a} = M_ρ ∘ P^spec_a, we have M_ρ = P^geom_{ρ,a} + P^spec_{ρ,a}".
- Line p. 457: (10.4.1.10) P^geom_a ∘ A(φ) ∘ P^geom_a = A(φ) ∘ P^geom_a.
- Line p. 458: (10.4.1.11) P^spec_a ∘ A(φ) ∘ P^spec_a = P^spec_a ∘ A(φ).
- Lines p. 458: "while we do not have the stronger commutation relations A(φ) ∘ P^geom_a = P^geom_a ∘ A(φ) and A(φ) ∘ P^spec_a = P^spec_a ∘ A(φ), ultimately because P^geom_a ∘ A(φ) ∘ P^spec_a ≠ 0 (i.e. the continuous left-translation action of C_F on W^s_I(C_F) does not preserve the orthogonality relations …, with the sole exception of the case s = α = 0, in which case such action is through unitary automorphisms)."
- Line p. 458: "We do have P^spec_a ∘ A(φ) ∘ P^geom_a = 0, which follows from (10.4.1.10)."

**Consequence.** Inserting Id = P^geom + P^spec on the left and applying (10.4.1.11):

A(φ) ∘ P^spec = P^geom A(φ) P^spec + P^spec A(φ) P^spec = P^geom A(φ) P^spec + P^spec A(φ),

so A(φ) ∘ P^spec − P^spec ∘ A(φ) = P^geom ∘ A(φ) ∘ P^spec. The remark asserts this difference is nonzero except when s = α = 0. When the operators involved are trace class, the traces agree, since Tr(P^geom A P^spec) = Tr(A P^spec P^geom) = 0. The operators themselves differ.

This bears on the separate item about (10.4.3.45) (p. 473: "ξ_π(K^spec_{φ,a,I,s}) = A(φ) ∘ P^spec_a"). The finite kernels (10.4.3.42)–(10.4.3.43) have the form Σ_i ⟨A(φ)′ η_i, ·⟩ ⊗ S_a(ψ_i), where A(φ)′ is the transpose (so named at l.420 and l.620). ξ_π acts as Σ φ_k ⊗ ψ_k ↦ Σ ⟨φ_k, ·⟩ ψ_k (p. 473). So these kernels give x ↦ Σ_i ⟨η_i, A(φ)x⟩ S_a ψ_i. When the expansion converges, this is S_a Q_a A(φ) = P^spec ∘ A(φ), not A(φ) ∘ P^spec.

#### Theorem 10.4.3.5(3), (10.4.3.45), p. 473: the spectral kernel is attached to A(φ)∘P^spec_a but represents P^spec_a∘A(φ)

**Printed.** For the limit K^spec of the tensors (10.4.3.43), Σ_i A(φ)′η_i ⊗ S_a(ψ_i), the manuscript states ξ_π(K^spec_{φ,a,I,s}) = A(φ)∘P^spec_a (10.4.3.45). In the I = {0} case the same construction is identified as P^spec_a∘A(φ) ((10.4.3.22)–(10.4.3.25), p. 470; Remark 10.4.3.3, (10.4.3.28); compare (10.4.2.5), P^spec_a∘A(φ) = S_a∘A^spec_a(φ)∘Q_a).

**Problem.** The order is wrong in the general case. The operator built from these tensors always has its range inside the spectral subspace.

**Derivation.**
- The finite-rank operator attached to Σ_{i≤N} A′η_i ⊗ S_aψ_i is f ↦ Σ_{i≤N} ⟨η_i, A f⟩ S_aψ_i. Its range lies in S_a(H_{F,a,I}) = P_s W, a closed subspace. So the limit operator also has range in P_s W, and ξ_π(K^spec) = P_s ξ_π(K^spec).
- If ξ_π(K^spec) = A P_s, then P_g A P_s = P_g ξ_π(K^spec) = 0. This contradicts p. 458.
- On the other hand, ⟨η_i, A f⟩ = ⟨η_i, Q_a A f⟩, since η_i annihilates the geometric subspace. With (10.4.2.5) this identifies the operator as P_s A.

**Fix.** Read (10.4.3.45) as ξ_π(K^spec) = P^spec_a∘A(φ), and adjust (10.4.3.46)–(10.4.3.48) to P^geom_a∘A(φ) and M_ρ∘P^{geom/spec}_a∘A(φ). If A P_s is the operator actually needed downstream, use the block identity
A P_s = P_s A + P_g A P_s,
which follows from P_s A P_g = 0 ⇒ P_s A = P_s A P_s. If P_g A P_s is trace class, then Tr(P_g A P_s) = Tr(P_g A P_s P_g) = 0, so the uncut traces of A P_s and P_s A agree. The cutoff versions (with M_ρ) still differ and need their own identification.

---

<a id="issue-26"></a>
### Issue 26 — (10.4.3.47), (10.4.3.30)

**Issue.** A kernel labelled spectral is attached to the geometric operator.

**Repair and status.** Lean, on the actual objects at finite rank: the masked and two-sided kernels represent M<sub>ρ</sub>(1 − P<sub>E<sub>T</sub></sub>)A and M<sub>ρ</sub>(1 − P<sub>E<sub>T</sub></sub>)AM<sub>ρ</sub>, with joint limits to P<sup>spec</sup>∘A (`KPhysicalMask.both_tests_full_masked_kernel_net`, `DAllSourceKernel.both_tests_full_twosided_kernel_net`).

**Printed.**
- (10.4.3.47): "The functions w_{I,s}(y)^{-1} k^spec_{φ,a,I,s}(x, y), ρ(x) w_{I,s}(y)^{-1} k^spec_{φ,a,I,s}(x, y) are representative functions for the Hilbert–Schmidt kernel in L²(C_F × C_F, (w_{I,s}µ)^{⊗2}) of the operator A(φ)∘P^spec_a … respectively … of the operator M_ρ∘A(φ)∘P^geom_a."
- (10.4.3.48), p. 473: w(y)^{-1} ρ(x) k^geom(x, y) represents M_ρ∘A(φ)∘P^geom_a.
- (10.4.3.50): k^geom(x, y) = φ(xy^{-1}) − k^spec(x, y).
- In the I = {0} version, (10.4.3.30), the kernel ρ(x)(1 + |log|y||²)^{−s/2} k^spec is labelled P^geom_{ρ,a}∘A(φ), and (10.4.3.31) gives the same operator the kernel built from k^geom.

**Problem.** The second label must be spectral. As printed, two different kernels are assigned to one operator.

**Derivation.**
- Hilbert–Schmidt kernels relative to (wµ)^{⊗2} are unique almost everywhere. If (10.4.3.47-second) and (10.4.3.48) both hold, then ρ(x) w(y)^{-1} (k^spec − k^geom) = 0 a.e. By (10.4.3.50) this means ρ(x)(2k^spec(x, y) − φ(xy^{-1})) = 0 a.e.
- The operator with Haar kernel ρ(x)φ(xy^{-1}) is M_ρ A. So the condition says M_ρ A P_s = (1/2) M_ρ A.
- Apply this to ϕ in the geometric subspace with M_ρ A ϕ ≠ 0 (such ϕ exists for an approximate identity φ and ρ of large level). The left side is 0 and the right side is not: contradiction.
- Since ρ(x) w(y)^{-1} k^spec is ρ(x) times the first kernel, it represents M_ρ∘(operator of the first kernel).

**Fix.** Within the order used in (10.4.3.45), the second label is M_ρ∘A(φ)∘P^spec_a. If the order is corrected as in ADDITIONAL A1, it is M_ρ∘P^spec_a∘A(φ) = P^spec_{ρ,a}∘A(φ). The same correction applies to (10.4.3.30) ("P^spec_{ρ,a}∘A(φ)").

---

<a id="issue-27"></a>
### Issue 27 — Proposition 11.1.1.2, Corollary 11.1.1.4

**Issue.** A bound on the total orbit sum gives no termwise majorant for the dominated-convergence step; a moving-bump test refutes Corollary 11.1.1.4.

**Repair and status.** Repair: a termwise majorant. Lean: on the actual ideles, the orbit sums of compactly supported and Schwartz–Bruhat tensor tests converge, with absolute bounds uniform in a Schwartz seminorm ball (`Round164D.genuine_uniform_central_theta_bound`); dominated convergence with a termwise majorant for the carvings of the §12.3 decomposition (`GeometricC.lifted_diagonal_carving_limit`). Proposition 11.1.1.2 and Corollary 11.1.1.4 themselves are not stated.

**Printed.**
- Hypothesis (1), p. 476. There is a fractional ideal I_Z ⊂ F such that for every g ∈ Z the series Σ_{ξ∈I_Z∩F^×} α(ξg) converges absolutely, and its value J_F(α)(g) is Borel in g and lies in L^r(Z, η|_Z). Here α: F^×Z → R_{≥0}.
- Hypothesis (2), (11.1.1.2), p. 476. "for every g ∈ F^×Z and every integer k ≥ 0, Σ_{ξ∈F^×} |f_k(ξg)| ≤ J_F(α)(g)."
- Conclusion (2), (11.1.1.4), p. 476. Φ_F(f) ∈ L^r(Z, η|_Z) and Φ_F(f) = lim_k Φ_F(f_k) in L^r(Z, η|_Z).
- Proof, p. 477. "Since |Φ_F(f_k)| ≤ J_F(α) over Z by (11.1.1.11) … By (11.1.1.11) and Dominated Convergence, applied, for every g ∈ Z, to {f_k}_{k≥0} ⊂ L¹(F^×g, µ_g), the limit of the sequence {Φ_F(f_k)} in the L^r(F^×g, µ_g)-norm topology, is Φ_F(f). This means that Φ_F(f_k) → Φ_F(f) pointwise over Z." Here µ_g is counting measure on the orbit F^×g. The equation (11.1.1.11) it cites is the hypothesis of the later Corollary 11.1.1.5 (p. 479), and that hypothesis is stated only "over T·E^1_F".
- Corollary 11.1.1.4, p. 478.
- Hypothesis (2)(b), (11.1.1.8): for every g ∈ T·E^1_F and every k, Σ_ξ |f_k(ξg)| ≤ Σ_{ξ∈I_g∩F^×} α_g(ξ).
- Conclusion: lim_k Φ_F(f_k)(g) exists and Φ_F(f) = lim_k Φ_F(f_k) pointwise, (11.1.1.10).
- Its proof, p. 478: "We apply Proposition 11.1.1.2 to the Borel set Z:= {g}, and η:= δ_{g} … By (2.a) and (2.b), conditions (1) and (2) of Proposition 11.1.1.2 are satisfied with r = 1". The proof cites (11.1.1.12)/(11.1.1.13), which belong to Corollary 11.1.1.5; the intended references are (11.1.1.9)/(11.1.1.10).

**Problem.** To apply dominated convergence on (F^×g, µ_g), the proof needs a function h_g on the orbit with |f_k(ξg)| ≤ h_g(ξg) for all k and Σ_ξ h_g(ξg) < ∞. Hypothesis (11.1.1.2) gives only sup_k ‖f_k(·g)‖_{ℓ¹(F^×)} ≤ J(g). A uniform ℓ¹ bound does not stop the mass from escaping along the orbit. What happens then depends on how the quantifier in (2) is read.

**Derivation.**

*(a) Moving bump.* Take b ∈ C_c^∞(R) with 0 ≤ b ≤ 1, supp b ⊂ (−1/4, 1/4) and b(0) = 1. Define
f_n(x):= b(x_∞ − (n+1)) · 1_{Ẑ}(x_fin), for n ≥ 0.
- Each f_n is a pure tensor and lies in S(A_Q).
- f_n → 0 pointwise on A_Q. For a fixed x, f_n(x) = 0 as soon as n + 1 > |x_∞| + 1/4. So f:= lim f_n = 0 everywhere.
- For ξ ∈ Q^×, 1_{Ẑ}(ξ) = 1 iff ξ ∈ Q ∩ Ẑ = Z, and b(ξ − n − 1) ≠ 0 iff ξ = n + 1. Hence Σ_{ξ∈Q^×} |f_n(ξ)| = b(0) = 1 for every n. So Φ(f_n)(1) = 1 for all n while Φ(f)(1) = 0.

*(b) The reading the manuscript actually uses: the bound on Z only.* This is how the proof itself uses the bound ("over Z", p. 477). It is how Corollary 11.1.1.4 applies the proposition (Z = {g}, η = δ_g). It is how Corollary 11.1.1.5 applies it ((11.1.1.11) only "over T·E^1_F" while Z = T·E^1_F). Under this reading the moving bump is a counterexample:
- Take Z = {1} (the principal idele), η = δ_1, I_Z = Z, and α(1) = 1, α(q) = 0 for q ∈ Q^× ∖ {1}.
- Then J(1) = Σ_{ξ∈Z∖0} α(ξ) = 1 and ‖J‖_{L^r(δ_1)} = 1.
- Hypothesis (2) holds at g = 1 (1 ≤ 1), and the pointwise limit exists everywhere.
- But ‖Φ(f) − Φ(f_n)‖_{L^r(δ_1)} = 1 for all n. Conclusion (2) fails for every r ≥ 1.

The same holds if J is extended to F^×Z by orbit invariance, J(ξ·1):= J(1).

*(c) Corollary 11.1.1.4 is false as printed, with no quantifier ambiguity.*
- Let g ∈ GL_1(A_Q). Then {ξ ∈ Q: ξg_f ∈ Ẑ} = c_g Z with c_g = ∏_p p^{−v_p(g_f)} > 0. At most 1 + 1/(2|g_∞|c_g) points of c_g Z lie in the interval {ξ: |ξg_∞ − (n+1)| < 1/4}.
- So Σ_ξ |f_n(ξg)| ≤ C_g:= 1 + 1/(2|g_∞|c_g) for all n.
- Put I_g:= Z, α_g(ξg):= C_g·δ_{ξ,1}. Then (2)(a) and (2)(b) hold for every g, and (1) holds with f = 0.
- Let g_0 = ξ_0 ∈ Q^× be the point of the fundamental domain T·E^1_Q in the orbit of 1. Then Φ(f_n)(g_0) = Σ_ξ f_n(ξξ_0) = 1 for all n, while Φ(f)(g_0) = 0. So (11.1.1.10) fails.

*(d) The literal reading: (2) required at every g′ ∈ F^×Z, with J(g′):= Σ_{ξ∈I_Z∩F^×} α(ξg′) ∈ [0, ∞].* Under this reading the hypothesis forces f_k ≡ 0 on F^×Z.
- Fix g ∈ Z and ε > 0. Choose a finite set E ⊂ I_Z ∖ {0} with Σ_{ξ∈(I_Z∖0)∖E} α(ξg) < ε.
- Fix d ∈ Z_{>0} with dI_Z ⊂ O_F. For ξ ∈ E and a rational prime p, ξ ∈ pI_Z implies dξ/p ∈ O_F, hence p | N_{F/Q}(dξ) ∈ Z ∖ {0}. So only finitely many p have E ∩ pI_Z ≠ ∅. Choose a prime p outside that set.
- Since ξ ↦ pξ is a bijection of F^×, Σ_ξ |f_k(ξ·pg)| = Σ_ξ |f_k(ξg)|.
- On the other side, J(pg) = Σ_{η∈pI_Z∖0} α(ηg) < ε, because pI_Z ⊂ I_Z and pI_Z ∩ E = ∅.
- Hypothesis (2) at pg therefore gives Σ_ξ |f_k(ξg)| < ε for every ε. Hence f_k(ξg) = 0 for all ξ, k and all g ∈ Z.

So under this reading the moving bump does not satisfy the hypothesis: at g′ = 2, J(2) = Σ_{ξ∈Z∖0} α(2ξ) = 0 < 1, so the unqualified claim fails. But no nonzero sequence satisfies it either, so the proposition is true only vacuously. Moreover, Corollary 11.1.1.5 has Z = T·E^1_F and F^×Z = GL_1(A_F). If (11.1.1.11) held on all of F^×Z, the corollary's f_k would vanish on GL_1(A_F) and hence, by density of the ideles in A_F and continuity, everywhere.

*(e) Use in 11.1.2.1(3), pp. 482–483.* There α is "the pre-composition of f_∞ with the projection" (p. 483), which need not be nonnegative. Neither (1) nor (2) is verified: the text says "Proposition 11.1.1.2 therefore applies".

**Fix.**
- Replace (11.1.1.2) by a termwise majorant: there is h: F^×Z → [0, ∞) with |f_k(ξg)| ≤ h(ξg) for all k, all ξ and all g ∈ Z, and g ↦ Σ_ξ h(ξg) lies in L^r(Z, η). Then the inner dominated-convergence step gives Φ(f_k)(g) → Φ(f)(g), and the outer step (majorant Σ_ξ h(ξg)) gives L^r convergence.
- Also require lim f_k to exist on F^×Z, not only on Z (p. 476): the conclusion uses f(ξg).
- Corollary 11.1.1.4 needs the same termwise hypothesis.
- For the carvings actually used in 11.1.2.1(3), f_k = P_{S_k}(f) replaces 1_{O_v} by 1_{O_v^×} at the places v ∈ S_k ∖ S. Hence |f_k| ≤ |f| pointwise and h:= |f| works. The remaining obligation is the bound g ↦ Σ_ξ |f(ξg)| ∈ L²(τ(R_{>0})E^1_F, 1_{(1/Λ,∞)}(1 + |log|g||²)^{s/2} µ), which must be proved.

- The dominated-convergence step is invalid under every reading.
- Proposition 11.1.1.2(2) is false under the reading the manuscript itself uses (Z only) and under the orbit-invariant extension.
- The retraction is right for the literal F^×Z quantifier. But that reading does more than "need clarification": it makes the proposition vacuous, so it supports none of its applications (Corollaries 11.1.1.4 and 11.1.1.5, 11.1.2.1(3)).
- What survives in full strength is that the moving bump is an unconditional counterexample to Corollary 11.1.1.4, whose proof is precisely the Z = {g}, η = δ_g application.

---

<a id="issue-28"></a>
### Issue 28 — (11.2.1.2), (11.2.1.4)

**Issue.** The strong limit of M<sub>ρ</sub>P<sub>geom</sub>AQ<sub>L</sub> is M<sub>ρ</sub>AP<sub>geom</sub>, not M<sub>ρ</sub>P<sub>geom</sub>A. The printed form would force M<sub>ρ</sub>P<sub>geom</sub>AP<sub>spec</sub> = 0, against Remark 10.4.1.4.

**Repair and status.** Lean: the printed strong limit forces the off-diagonal block to vanish (`FollowupD30.geometric_truncation_full_limit_forces_offDiagonal`); the corrected right-truncation limit (`Q.IntegratedSourceCutoff.right_source_condensation_with_remainder`); SAS = AS on the actual objects for both tests; and the left-side limit on the actual objects.

**Printed.**
- (11.2.1.3), p. 488. P^PW_{S,Λ_0,a} is the orthogonal projector onto the absolute Paley–Wiener level W^{s,2}_a PW_{S,X,0}(…), a closed subspace of W^{s,2}_a H_{0,cont}(χ|C^1_F, S_0(A_F)). (Line p. 488 names the target "W^{s,2}_a H_{SΛ_0}(…)", inconsistent with the codomain displayed in p. 488.)
- Theorem 11.2.1.2(1), p. 488: P^PW_{S,Λ_0,a} → P^geom_a strongly.
- (11.2.1.4), p. 488: P^geom_{ρ,a}∘A(φ)∘P^PW_{S,Λ_0,a} → P^geom_{ρ,a}∘A(φ) in the sense of nuclear operators.
- (11.2.1.5): lim_{Λ_0→∞} Trace(P^geom_{ρ,a} A(φ) P^PW_{S,Λ_0,a}) = Trace(P^geom_{ρ,a} A(φ)).
- Proof, p. 488: "Both assertions follow from Corollary C.3.5.5(2) and (3)."

**Which projection is which.** Q_L:= P^PW_{S,L,a} has range inside range(P_g) (the geometric subspace), so Q_L = P_g Q_L = Q_L P_g, and Q_L → P_g strongly by (1). P^geom_{ρ,a} = M_ρ P_g. So the operator in (11.2.1.4) is T Q_L with T:= M_ρ P_g A.

**Derivation.**
- *Strong limit.* For every v, T Q_L v → T P_g v. So the strong limit is T P_g = M_ρ P_g A P_g, which equals M_ρ A P_g by (10.4.1.10). A trace-norm limit is also a strong limit, so the nuclear limit, if it exists, is M_ρ A P_g.
- *Gap from the printed limit.* T = T P_g + T P_s. Hence the printed (11.2.1.4) holds iff M_ρ P_g A P_s = 0.
- *That identity is false for large cutoffs.* The manuscript itself asserts P_g A P_s ≠ 0 (p. 458). Pick v with P_g A P_s v ≠ 0. As Λ → ∞ with εΛ = o(1), M_ρ → Id strongly (as cited at p. 482). Then M_ρ P_g A P_s v → P_g A P_s v ≠ 0, so M_ρ P_g A P_s ≠ 0 for every cutoff of large enough level. So (11.2.1.4) is false in the regime where it is used.
- *Where the proof breaks.* Corollary C.3.5.5 (p. 702) assumes that ⋃H_i is dense in the whole Hilbert space, and concludes P_i → Id, P_i T → T and T P_i → T. Here the union of Paley–Wiener levels is dense only in range(P_g). Applied in H the corollary gives nothing; applied inside range(P_g) it gives T|_{range P_g}, that is, T P_g.
- *Trace.* T is nuclear (Theorem 10.4.2.1) and Q_L is self-adjoint with Q_L → P_g strongly. Therefore ‖T Q_L − T P_g‖_1 = ‖(Q_L − P_g) T*‖_1 → 0. So
lim Tr(T Q_L) = Tr(M_ρ A P_g) = Tr(T) − Tr(T P_s).
By cyclicity (T trace class, P_s bounded),
Tr(T P_s) = Tr(P_s M_ρ P_g A) = Tr([P_s, M_ρ] P_g A), using P_s P_g = 0.
This defect vanishes when M_ρ preserves the geometric subspace. Nothing in the manuscript shows that M_ρ does, or that the defect vanishes. Without ρ it is Tr(P_s P_g A) = 0, but the cutoff destroys this.
- *Propagation.* Theorem 11.2.1.4 is deduced from 11.2.1.2 via P^PW ≤ Q^PW (p. 489), and Q^PW_{S,Λ_1,a} also tends to P_g. So (11.2.1.9)–(11.2.1.10) fail in the same way.

**Fix.**
- (11.2.1.4) should read: M_ρ P_g A(φ) P^PW_{S,Λ_0,a} → M_ρ A(φ) P_g in trace norm.
- (11.2.1.5) should read: lim Tr(…) = Tr(M_ρ A(φ) P_g) = Tr(P^geom_{ρ,a} A(φ)) − Tr(P_s M_ρ P_g A(φ)).
- To recover the printed statements one must additionally prove M_ρ P_g A P_s = 0, which contradicts the manuscript's own p. 458. Alternatively one must prove that Tr(P_s M_ρ P_g A(φ)) vanishes, or tends to 0 in the cutoff regime used downstream.
- The same corrections apply to (11.2.1.9)–(11.2.1.10).

---

<a id="issue-29"></a>
### Issue 29 — §11.3.1, primary divisorial stratification

**Issue.** The componentwise-unit strata are identified with preimages under the norm map. These differ when a prime splits: for F = ℚ(i), p = 5, the idele with components 5 and 5<sup>−1</sup> at the two places above 5 has norm 1 there but is not a unit at either.

**Repair and status.** Repair: keep the componentwise definition. Every stratum in the Lean is a componentwise unit condition at individual places; the definition `GeometricC.unitCarving` records “These are not inverse images under a field norm.” The counterexample itself is not formalized.

**Printed.** Lines pp. 492–493: "we define P_k to be the pre-image under the map |Spec(O_F)| → |Spec(Z)| of the subset T_k, and therefore the stratum GL1(A_F)_{P_k} is the pre-image under the norm map GL1(A_F) → GL1(A_Q) of the kth divisorial stratum on GL1(A_Q). Explicitly, … GL1(A_F)_{P_k} = {g: g_v ∈ O_{F_v}^× for all v ∈ ∪_{p∈T_k} S_p} … In other words, GL1(A_F)_{P_k} is the pre-image of the kth stratum GL1(A_Q)_{T_k} … under the norm map."

**Problem.** The explicit description (units at every place above p ∈ T_k) and the norm-map preimage are different sets as soon as some p ∈ T_k has two or more places above it.

**Derivation.** For g ∈ GL1(A_F), the p-component of N_{F/Q}(g) is ∏_{v|p} N_{F_v/Q_p}(g_v), with valuation Σ_{v|p} f_v·ord_v(g_v). The norm preimage of {x: x_p ∈ Z_p^×} is therefore {g: Σ_{v|p} f_v ord_v(g_v) = 0}, which contains the componentwise-unit set and is strictly larger when p splits. Take F = Q(i) and p = 5 = (2+i)(2−i), with two places v₁, v₂ of degree 1, so F_{v₁} ≅ F_{v₂} ≅ Q₅. Let g have g_{v₁} = 5, g_{v₂} = 5^{−1} and all other components 1. Then N(g)₅ = 5·5^{−1} = 1 ∈ Z₅^×, so g lies in the norm preimage, but g_{v₁} and g_{v₂} are not units, so g is not in the explicit stratum.

**Fix.** Keep the explicit componentwise definition (it is what the indicator α_k and the factorization at p. 493 use) and delete the "pre-image under the norm map" identification, or state it only when every p ∈ T_k has a single place above it. Any later step that uses norm-compatibility of the strata needs re-checking.

---

<a id="issue-30"></a>
### Issue 30 — (11.3.1.4), used in the proof of Theorem 12.5.1.1

**Issue.** The strata decrease, so the shell differences are ≤ 0 and the telescope has the opposite sign to the sum used in 12.5.1.1.

**Repair and status.** Repair: reverse the shell convention, or keep the minus sign. Lean: with the printed convention, total = residual − Σ shells, for every integrable density (`NDivisorialShells.signed_shell_reconstruction`) and for the actual finite-level residual kernel, for both tests, with the Haar scalar (`NArithmeticUnfolding.both_tests_full_originalHaar_signed_shells`); with reversed shells the plus-sign reconstruction holds (`Geometric19C.corrected_geometric_shell_eventually_reconstructs`).

**Printed.** k_{p_k}:= (α_{k+1} − α_k) k_geom (11.3.1.4), and k_geom = k_S + Σ_{p∤S} k_p (p. 491), used as ∫k_S + Σ_p ∫k_p = ∫k (p. 520).

**Problem.** Since α_{k+1} ≤ α_k (see Issue 32), each k_{p_k} is minus the restriction of k to the k-th shell. The pieces as printed add up to the wrong sign.

**Derivation.** With α_0 = 1 (P_0 = ∅) and lim α_k = β_S, telescoping gives
Σ_{j<K} (α_{j+1} − α_j) = α_K − 1 → β_S − 1.
Hence k = β_S k − Σ_p k_p. The printed identity holds only if k_S:= (2 − β_S) k, which is not an S-local kernel. The manuscript nowhere defines k_S.

**Fix.** Use positive shells: k_{p_k}:= (α_k − α_{k+1}) k and k_S:= β_S k. The shells are disjoint, so absolute integrability of the indented diagonal justifies the termwise integration.

---

<a id="issue-31"></a>
### Issue 31 — Theorem 11.3.2.1 vs Theorem 12.5.1.1; footnote in §12.4.1

**Issue.** Theorem 11.3.2.1 assumes φ supported over C<sub>F</sub><sup>>1</sup>, while 12.5.1.1 assumes only φ(C<sub>F</sub><sup>1</sup>) = 0. The author's footnote leaves the two-cutoff limit of (12.4.1.23) unfinished.

**Repair and status.** Repair: treat both sides of norm one, and carry out the two-cutoff limit. Lean: every orbital-trace statement on the actual objects allows support on both sides of C<sub>K</sub><sup>1</sup>; for the finite-level residual kernel, for both tests, the orbit diagonal integrates to −c·tr(P<sub>E<sub>T</sub></sub>A) with the Haar scalar c > 0 proved (`HArithmeticTrace.both_tests_full_residual_originalHaar_orbital_trace`). The footnote's two-cutoff limit is proved with independent endpoints on the actual adele ring and its S-local modulus, for a supplied density, the divergent term cancelling because φ(1) = 0 (`GeometricRound13D.sLocal_two_cutoff_limit_normOneVanishing`); tying λ″ = λ′ leaves a correction (`Geometric19D.synchronized_cutoff_correction`). The local value (log q<sub>v</sub>/μ<sub>v</sub>(O<sub>v</sub><sup>×</sup>))Σ<sub>k</sub>φ(π<sub>v</sub><sup>k</sup>) of 11.3.2.1 is not yet stated.

**Printed.** 11.3.2.1 says "Assume φ is supported over C_F^{>1}." Theorem 12.5.1.1 assumes only φ(C_F^1) = 0. Its proof (p. 520) then uses 11.3.2.1 to get ∫k_p(x, x) dμ = 0 for p ∤ S.

**Gap.** A smooth test that vanishes on C_F^1 can be supported on both sides of it. Splitting φ = φ·1_{>1} + φ·1_{<1} does not stay inside D(C_F). For example, φ = log|g|·b(g) with b a bump around C_F^1 vanishes on C_F^1, but φ·1_{>1} has a corner there. The piece with |g| < 1 also needs its own orbital-trace calculation.

Footnote 2 at p. 514 is the author's own unfinished note. It asks to extend Definition 9.3.3.1 to cutoffs supported on (0, λ], to use a smoothing of 1_{[1/λ″, λ]} with λ″ independent of λ, and "then study the convergence of the integral in (12.4.1.23) … as λ′, λ″ → +∞". That convergence study is not in the manuscript. The expressions from line ~p. 518 onward need a uniform limit check.

**Fix.** Either state 12.5.1.1 for φ supported on C_F^{>1}, which is all that §1.4.4 uses since φ_{h,ε,z} is supported on (1, ∞), or prove the mirror result for support in C_F^{<1} together with an approximation argument for tests that only vanish on C_F^1, and carry out the two-cutoff limit of footnote 2.

---

<a id="issue-32"></a>
### Issue 32 — (11.3.2.3)

**Issue.** Multiplying the shell by the later unit mask gives zero, so the displayed integral vanishes; the masks converge to β<sub>S</sub>, not β<sub>S′</sub>.

**Repair and status.** Repair: keep the outside-S remnant in the decomposition. Lean: the later mask annihilates the shell for every kernel and every number field (`GeometricReview18C.later_unitMask_annihilates_geometric_shell`); the masks converge to the outside-S unit indicator β<sub>S</sub>, with the corrected decomposition on the actual ideles (`Geometric19C.corrected_geometric_shell_eventually_reconstructs`); the raw outside-S mask does not descend to C<sub>K</sub> (`Geometric20C.outsideMask_no_ideleClass_descent`).

**Printed.**
- Definitions, p. 493. α_k:= 1_{GL_1(A_F)_{P_k}}, where GL_1(A_F)_{P_k} = {g: g_v ∈ O_v^× for all v ∈ P_k} and P_k ⊂ P_{k+1}. The shell kernel is (α_{k+1} − α_k) k^∆_geom (11.3.1.4).
- Lines p. 495: k^∆(τ(t), ξgτ(t)) "vanishes unless ξ ∈ F^× maps to a uniformizer in F_v^× for some v ∈ P_{k+1} − P_k". Lines p. 495 take S′ ⊇ S ∪ (P_{k+1} − P_k).
- Lines p. 495: "Multiplication of (α_{k+1} − α_k)k^∆ by the indicator function α_k (as a function of the second named variable) for k ≥ k_0 for a suitable large enough integer k_0 ≥ 0 such that the support of α_k contains GL_1(A_{F,S′}) × ∏_{v∉S′} O_v^×, preserves the value of the left side of (11.3.2.1)."
- (11.3.2.3), p. 495:
Σ_{ξ∈F^×} ∫_{E^1_F} ∫ ρ(τ(t)) ((α_{k+1} − α_k) k^∆)(τ(t), ξgτ(t)) α_{k_1}(ξgτ(t)) dµ_1(g) dt/t.
This is asserted to equal the trace of a nuclear operator.
- Lines pp. 495–496: as k_1 → +∞ "the indicator function of GL_1(A_{F,S′}) × ∏_{v∉S′} O_v^× is the limit of the α_{k_1}".

**Problem.** The mask α_{k_1} and the shell factor α_{k+1} − α_k both act on the second variable y = ξgτ(t). For k_1 ≥ k + 1 their product is identically zero.

**Derivation.**
- *Monotonicity.* P_k ⊂ P_{k+1} gives α_{k+1} ≤ α_k. So α_{k+1} − α_k = −1_{D_k}, with
D_k:= {y: y_v ∈ O_v^× for all v ∈ P_k, and y_v ∉ O_v^× for some v ∈ P_{k+1} ∖ P_k}.
- *Which variable.* A continuous homomorphism τ: R_{>0} → GL_1(A_F) has connected image, so τ(t)_v = 1 at every finite v. Hence the first variable τ(t) lies in every stratum, and α_j(τ(t)) − α_{j+1}(τ(t)) = 0. If the shell acted on the first variable, the whole left side of (11.3.2.1) would be 0. The shell is therefore in the second variable, as the proof's own description says (p. 495).
- *Annihilation.* For k_1 ≥ k + 1, α_{k_1}(y) = 1 forces y_v ∈ O_v^× for all v ∈ P_{k_1} ⊇ P_{k+1}, which contradicts y ∈ D_k. Hence
(α_{k+1} − α_k)(y) · α_{k_1}(y) = 0 for every y and every k_1 ≥ k + 1.
So the integrand of (11.3.2.3) is identically zero once k_1 ≥ k + 1. In the limit k_1 → ∞ the expression is 0, not the left side of (11.3.2.1).
- *Small k_1.* For k_1 ≤ k, α_{k_1} ≡ 1 on D_k ⊂ GL_1(A_F)_{P_k}. There the mask is the identity and produces no S′-local degeneration. No choice of k_1 both preserves the shell and degenerates it.
- *The selection condition on k_0 cannot be met.* "supp α_{k_1} ⊇ GL_1(A_{F,S′}) × ∏_{v∉S′} O_v^×" holds iff P_{k_1} ∩ S′ = ∅. But S′ ⊇ P_{k+1} ∖ P_k ⊂ P_{k_1} for k_1 ≥ k + 1, so the condition fails for every large k_1.
- *The asserted limit is wrong.* lim_{k_1} α_{k_1} = 1{g_v ∈ O_v^× for all v ∈ ⋃_k P_k}. This is β_S (with S, not S′), and β_S · (α_{k+1} − α_k) = 0.

**Fix.**
- The degeneration must use a mask that is identically 1 on the shell. One choice is γ_{k_1}:= 1{g_v ∈ O_v^× for all v ∈ P_{k_1} ∖ P_{k+1}}, whose limit is β_{S′} with S′ = S ∪ P_{k+1}.
- Alternatively, degenerate the Schwartz–Bruhat functions rather than multiplying the kernel's second variable.
- In either case one must prove separately that the part removed by the mask contributes nothing to the orbital sum, and that the mask commutes with the indentation ∆.

---

<a id="issue-33"></a>
### Issue 33 — Proposition 12.2.2.2(4)

**Issue.** The reverse implication is obtained by multiplying by a correlation that can vanish, and it fails near such points (on ℝ with H = ℤ and a triangle indentation).

**Repair and status.** Repair: restrict to points where the correlation is nonzero, or state the result almost everywhere. Lean: the correlation of (12.2.2.1) and the transport (12.2.2.3)–(12.2.2.7) on the actual ideles, with a supplied fundamental domain (`GeometricC.quotient_indentedKernel_integral`); the forward direction of (4) under bounded normalised absolute averages (`GeometricRound4D.continuous_idele_diagonal_multiplier_limit`). The reverse direction is not stated.

**Printed.**
- Line p. 509: "The point (x, y) ∈ G × G is regular for Ψ^∆_{u_0}(u) if and only if (π(x), π(y)) ∈ G/H × G/H is regular for u."
- Here Ψ^∆_{u_0}(u) = u_0^∆ · (u∘(π×π)) (12.2.2.2), with u_0^∆(x, y) = ∫_H u_0(h^{-1}x) u_0(h^{-1}y) dµ_H(h) (12.2.2.1).
- Proof: if (x, y) is regular for u∘(π×π), then by continuity of u_0^∆ and Corollary A.5.4.3, the averages of Ψ(u) converge to u_0^∆(x, y) · ũ(π(x), π(y)) ((12.2.2.22)–(12.2.2.25)). Then p. 512: "We deduce that (x, y) ∈ G × G is regular for Ψ^∆_{u_0}(u) if and only if (π(x), π(y)) is regular for u".

**Problem.** The proof establishes only the direction "u regular ⇒ Ψ(u) regular" (and even that rests on Corollary A.5.4.3; see Issue 38). The converse amounts to dividing by u_0^∆(x, y), which is impossible where u_0^∆(x, y) = 0. Because u_0 has proper support, u_0^∆ vanishes on most of G × G.

**Derivation (counterexample).** Situation 12.2.2.1 is satisfied by the following data:
- G = R, H = Z, D = [−1/2, 1/2), U_k = (−r_k, r_k) with r_k = 2^{−k−2}.
- u_0(x) = max(0, 1 − |x|). This is continuous, nonnegative and compactly supported, and Σ_n u_0(x − n) = 1, so it is an H-indentation (Lemma 12.2.1.1, Definition 12.2.1.3).
- If |x − y| > 2, no n has both |x − n| ≤ 1 and |y − n| ≤ 1. So u_0^∆ = 0 on the open set {|x − y| > 2}.
- Let E = ⋃_{j even} ([r_{j+1}, r_j) ∪ (−r_j, −r_{j+1}]) and u(a, b):= 1_{π(E)}(a), a bounded measurable function on (R/Z)².
- Average of u over π(0) + Ū_k (in each variable): |E ∩ (−r_k, r_k)|/(2r_k) = (Σ_{j≥k, j even} r_j)/(2r_k). This equals 2/3 for k even and 1/3 for k odd. So (π(0), π(0)) is not regular for u.
- The rectangles (0 + U_k) × (3 + U_k) lie in {|x − y| > 2}, where Ψ(u) ≡ 0. So every average of Ψ(u) at (0, 3) is 0, and (0, 3) is regular for Ψ(u).
- π(3) = π(0), so this is a diagonal point of G/H × G/H, the case the proposition is used for. The "only if" direction fails.
- This is the generic situation in (12.2.2.3): u_0^∆(h^{-1}x, x) = 0 for all but finitely many h ∈ H.

**Fix.** State (4) one-directionally:
- If (π(x), π(y)) is regular for u (and, by Issue 38, the absolute averages of u there are bounded), then (x, y) is regular for Ψ(u) with value u_0^∆(x, y) ũ(π(x), π(y)).
- Conversely, regularity of Ψ(u) at (x, y) implies regularity of u at (π(x), π(y)) only when u_0^∆(x, y) > 0, since 1/u_0^∆ is then continuous near (x, y), and again with bounded absolute averages.
- The almost-everywhere identity (12.2.2.9) is unaffected.

---

<a id="issue-34"></a>
### Issue 34 — §12.3; proof of Theorem 12.5.1.1

**Issue.** §12.3 is a heading with the note “Include section”, and the proof of 12.5.1.1 attributes the polar subtraction to 12.4.1.1, which has none.

**Repair and status.** Repair: supply the global-to-local decomposition. Lean: the §12.3-type decomposition, total = S-idele residual − Σ shells with absolute summability, for a supplied diagonal and fundamental domain (`GeometricC.quotient_diagonal_arithmetic_decomposition`); at finite level on the actual objects, the shell decomposition of the finite and residual diagonals (`PIntegrated.geometric_trace_global_operator_assembly`); the local expression with the constants 1/2, 1/(2π) and log N(v)/μ<sub>v</sub>(O<sub>v</sub><sup>×</sup>) reduces to finitely many places for both tests (`NLocalArithmetic.both_tests_localExpression_eq_semilocal`); the identity term φ(1)·log(λλ′) vanishes for both tests. The polar subtraction and Theorem 12.4.1.1 as a whole are not yet stated.

**Printed.**
- *§12.3.* Line p. 514: heading "12.3. Putting the pieces together: global to S-local deconstruction of the geometric kernel", followed only by the footnote marker "1" (p. 514) and the next heading 12.4 (p. 514). Footnote 1 (p. 514): "Include section."
- *Other unfinished passages in §12.4.* Footnote 2 (p. 514): "Extend Definition 9.3.3.1 … Return here and change the choice of smooth (λ, ε)-cutoff into a smoothening of 1_{[1/λ″, λ]} … Then study the convergence of the integral in (12.4.1.23), with log|w|_{F,S} replaced by log max{|w|/λ′, 1/λ″}". Footnote 3 (p. 515): "See previous footnote." Footnote 4 (p. 515): "Return here after the Proposition is updated."
- *(12.4.1.1)–(12.4.1.3), p. 514.*
µ_{S,1}(J^1_{F,S})^{-1} ∫_{J_{F,S}} k^PW_{S,φ,λ,λ′}(x, x) dµ_S(x)
= Σ_{v real} (1/2) ∫′ φ(g_v)|g_v|^{1/2}/|1 − g_v| dµ_v
+ Σ_{v complex} (1/2π) ∫′ φ(g_v)|g_v|^{1/2}/|1 − g_v| dµ_v
+ Σ_{v∈S_f} (log q_v/µ_v(O_v^×)) ∫′ φ(g_v)|g_v|^{1/2}/|1 − g_v|_v dµ_v
+ φ(1) log(λλ′) + o(1).
- *Proof of Theorem 12.5.1.1, p. 520.* "By Theorem 12.4.1.1, we further have that ∫_{C_F} k_S(x, x) dµ(x) equals the left side of (12.5.1.1) upon subtracting M(φ)(|·|^{1/2}) + M(φ)(|·|^{−1/2})."

**Problem.**
- §12.3 is empty. It is exactly the global-to-S-local identification on which the proof of 12.5.1.1 rests. No printed text identifies the S-local residual of the global geometric kernel with k^PW_{S,φ,λ,λ′}. The independent lower-cutoff limit of footnote 2 is also left undone.
- (12.4.1.1)–(12.4.1.3) contain no polar term.

**Derivation.**
- As an S-local statement, the absence of polar terms is not an error. It has the shape of Connes' S-local trace formula ([Co, §VII, Thm. 4], cited at p. 514), which has only the local principal values and the log-cutoff term. The terms M(φ)(|·|^{±1/2}) are global: they come from the conditions f(0) = f̂(0) = 0 defining S_0(A_F) (p. 18), that is, from the passage from the global geometric subspace to the S-local one.
- The error is in the citation. The proof of 12.5.1.1 attributes to Theorem 12.4.1.1 an identity containing "− M(φ)(|·|^{1/2}) − M(φ)(|·|^{−1/2})" that 12.4.1.1 does not state and that no printed result supplies.
- The same citation also silently drops:
- the normalization µ_{S,1}(J^1_{F,S})^{-1} and the change of measure µ_S → µ;
- the Paley–Wiener superscript and the limits λ, λ′ → ∞ with their o(1);
- the term φ(1) log(λλ′). Dropping this one is legitimate, since φ(C^1_F) = 0 gives φ(1) = 0.

**Fix.** Write §12.3, proving the identity ∫_{C_F} k_S(x, x) dµ = lim_{λ,λ′} µ_{S,1}(J^1)^{-1} ∫ k^PW_{S,φ,λ,λ′}(x, x) dµ_S − M(φ)(|·|^{1/2}) − M(φ)(|·|^{−1/2}), including the derivation of the two polar terms from f(0) = f̂(0) = 0. Finish footnote 2's lower-cutoff limit. Then cite 12.4.1.1 only for the local part.

- §12.3 placeholder: CONFIRMED.
- "No polar subtraction in 12.4.1.1": CONFIRMED WITH CORRECTION. The description is accurate, but it is not an error in 12.4.1.1, whose S-local formula legitimately has no polar terms. The defect is the unsupported attribution of the polar subtraction to 12.4.1.1 in the proof of 12.5.1.1 (p. 520), which depends on the missing §12.3.

---

<a id="issue-35"></a>
### Issue 35 — Theorem 12.5.1.1, (12.5.1.4)

**Issue.** The theorem sums only interior zeros, while the trace it cites (10.3.2.3) runs over the closed strip; boundary and exterior zeros are dropped.

**Repair and status.** Repair: keep the correction, Local = Poles − tr(PA) − (R − B<sub>adm</sub>). Lean: the native formula holds if and only if R − B<sub>adm</sub> = 0 (`ConditionalA26.uncorrected_native_iff_omitted_vanishes`); width differences retain the remainder; and width-independence of the remainder is equivalent to all zeros lying on Re = ½ (`BoundaryFreeTraceRepairD.remainder_independent_iff_critical_line`).

**Printed.** 12.5.1.1 sums N(c)M(φ)(c|·|^{−1/2}) over zeros "contained in the interior of the relative vertical strip Ω(C_F)_I = {σ(c) ∈ 1/2 + I}" (p. 519). The proof obtains (12.5.1.4) "by design of the global geometric kernel (Definition 10.4.3.7) and by Theorem 10.4.2.8". But 10.4.2.8 refers to the trace (10.3.2.3), whose sum runs over the **closed** interval b ∈ [−α, α] and uses N_{I,s} at b = ±α.

**Accounting** (a = 1/2, I = [−α, α], with W(c):= M(φ)(c|·|^{−1/2}), true multiplicities N(c), poles handled separately):

| Symbol | Sum over | Weight |
|---|---|---|
| S_int | \|σ(c) − ½\| < α | N(c)W(c) |
| B_adm | \|σ(c) − ½\| = α | n_adm(c)W(c), with n_adm = #{m < N(c): 2m + 1 < s} |
| R | \|σ(c) − ½\| ≥ α | N(c)W(c) (full boundary multiplicity plus all exterior zeros) |

Assuming the matching absolute convergence:
- the native zero sum is S_native = S_int + B_adm. This is the target value of tr(PA); proving it is still open (I4);
- the full zero sum is S_full = S_int + R.

The classical explicit formula reads Local(φ) = Poles(φ) − S_full, with Poles = M(φ)(|·|^{1/2}) + M(φ)(|·|^{−1/2}). Hence

**Local = Poles − S_native − (R − B_adm).**

**What each printed claim requires.**
- The printed 12.5.1.1, Local = Poles − S_int, holds iff **R = 0**: no zeros on or outside the boundary of the strip.
- The native version, Local = Poles − tr(PA), holds iff **R = B_adm**.

Checked in Lean: `TraceRepairE.strict_interior_formula_iff_total_defect_zero` proves that from T = J + B and G + O = P − T, one has G = P − J ⇔ O + B = 0. `selected_formula_iff_remainder_zero` is the same statement for tsums.

**Two widths α < β.** For the interior sums, S_int(β) − S_int(α) = R(α) − R(β). For the corrected native traces, tr(T_β) − tr(T_α) = C_α − C_β with C:= R − B_adm. This is not zero in general (`width_subtraction_retains_remainder`: Tb − Ta = Oa − Ob). Choosing widths with no zeros on the boundary removes B_adm and the boundary part of R, but the exterior part of R stays.

**The missing step is equivalent to the conclusion.** A checked Lean theorem, `BoundaryFreeTraceRepairD.remainder_independent_iff_critical_line`, shows: under the corrected strip limits and the zero-count hypothesis, the remainder is width-independent iff all zeros lie on the critical line. §1.4.5 (pp. 29–30) applies the interior-only formula at every width a > 0 to conclude that there are no zeros in C_{>1/2}. So the deleted term R − B_adm carries the whole strength of that conclusion.

Two further points:
- B_print (the printed cap from item 3) differs from B_adm at odd integer s.
- Taking s = 0 to remove the endpoints does not help: Theorem 10.4.3.6 requires s > 1 and Definition 10.4.3.7 requires s ≥ 3.

**Fix.** Keep the correction, i.e. state Local = Poles − tr(PA) − (R − B_adm). Then either prove that it vanishes using independent geometry, or prove a correctly quantified boundary-free-width formula. A local archimedean reference subtraction (item 5) removes a width-independent 1/x divergence only. It does not remove C.

**Same statement elsewhere.** The interior-only statement also appears at p. 53, with σ(c) ∈ 1/2 + I, and at p. 28, with σ(c) ∈ I. The second is a different normalisation of the same strip, so these two statements are inconsistent with each other as well.

---

<a id="issue-36"></a>
### Issue 36 — Chapter 13; §14.1.2

**Issue.** Theorem 13.3.1.2 has no statement (“Insert statement”, “Theorem ??”); Theorem 13.3.1.1 caps multiplicities at min(N, [F:ℚ]); §14.1.2 draws GRH and N(ρ) ≤ [F:ℚ] from them.

**Repair and status.** Repair: state the divisor theorem with full multiplicities. Lean, for K = ℚ: the full explicit formula with full multiplicities under the trace interface, and correction control equivalent to RH (`ManuscriptRH.chapter13_paired_control_iff_riemannHypothesis`).

**Printed.**
- Sections 13.1 "Recollections on the Explicit Formulas" and 13.2 "Holomorphic families of test functions" (p. 522) are headings with no text.
- Line p. 522: "We record here below the statement of the Trace Formula, established in Theorem 12.5.1.1".
- Theorem 13.3.1.1 (p. 522) carries footnote 1, "Correct statement." (p. 522). It contains:
- (13.3.1.1): N_spec(c):= min{N(c), [F:Q]}.
- Hypothesis (13.3.1.2): for all 0 ≤ k ≤ [F:Q]−1 and all χ ∈ Ĉ_F,
∂_s^k [ ∫_{R>0} χ(τ(t)) t^s (∫_{C¹_F} φ(τ(t)g) χ(g) dμ_1(g)) dt/t ]_{s = −i x_0(χ)} = 0.
- Identity (13.3.1.3)–(13.3.1.5):
Σ_{c: L(c)=0, σ(c)=1/2} N_spec(c) ∫_{C_F} φ(g) c(g) |g|_F^{-1/2} dμ = ∫ φ |g|^{-1/2} + ∫ φ |g|^{1/2} − Σ_{v∈S_∞} ∫′ … − Σ_{v finite} log(q_v) ∫′ …,
stated as continuous on "the [F:Q]-codimensional linear subspace A ⊂ D(C_F)".
- Lines p. 522: "Upon combining Theorem 13.3.1.1 and Theorem ??, we obtain the following: Theorem 13.3.1.2 (Divisor of L(s, χ)).²˒³", with footnotes "²Insert statement." and "³State and prove the Main Theorems, also explaining how to deduce them by approximation φ → e^{−s|log(t)|} as Re(s) > 1." No statement or proof follows; Chapter 14 begins.
- §14.1.2, p. 528, footnote "Correct this subsection." (p. 528): "The Trace Formula (Theorem 13.3.1.1) reveals constraints on the multiplicity … Indeed, Theorem 13.3.1.2, a consequence of the Trace Formula combined with the Positivity Criterion (in its form from Theorem ??), asserts that if ρ ∈ C is a non-trivial zero of L(s, χ), then ρ ∈ 1/2 + iR, and if, in addition, ρ ∉ R, i.e. ρ ≠ 1/2, then N(ρ) ≤ [F:Q]."
- The bound is treated as obtained at p. 524, p. 526, p. 530, p. 530, p. 530, p. 531 (Remark 14.1.2.4: "the Multiplicity Bound obtained in Theorem 13.3.1.2") and p. 533 ("Theorem 13.3.1.1 and hence … Theorem 13.3.1.2 through the Positivity Criterion of Weil, in its form of Theorem ??").

**Problem.**
1. Theorem 13.3.1.2 has no statement and no proof, and the auxiliary result it combines with is printed as "Theorem ??".
2. §14.1.2 attributes two conclusions to this empty theorem: every non-trivial zero lies on Re s = 1/2 (GRH), and N(ρ) ≤ [F:Q] for non-central zeros. Remark 14.1.2.4 and the passages listed above treat the bound as established. Proposition 14.1.2.3 itself is conditional on Conjectures 14.1.2.1–14.1.2.2 and does not depend on 13.3.1.2.
3. The input, Theorem 13.3.1.1, is flagged by the author as needing correction, and it is not the statement of Theorem 12.5.1.1 that it claims to record. Theorem 12.5.1.1 (p. 519):
- assumes φ(C¹_F) = 0;
- weights each zero by its full multiplicity N(c);
- sums over zeros in the interior of the strip Ω(C_F)_I = {σ(c) ∈ 1/2 + I}.
Theorem 13.3.1.1 instead:
- assumes vanishing of central Mellin jets of order < [F:Q]; at s = −i x_0(χ), c|·|^{-1/2} is the central point 1/2 − i x_0;
- weights zeros by min(N(c), [F:Q]);
- sums only over σ(c) = 1/2.
4. The route Chapter 14 names (Weil positivity) contradicts the Introduction. §1.4.6 (p. 30) says "Weil's Positivity Criterion is not used". §1.7.2 (p. 35) repeats this and explains that the only φ = ψ_1 ∗ ψ_1^# with φ(C¹_F) = 0 is φ = 0. The Introduction's deduction (§1.4.4–1.4.5, pp. 29–30) goes instead through holomorphy of L′_f/L_f, which is the route footnote 3 points to. It is an overview and is not proved anywhere in Chapter 13.
5. Minor: "ρ ∉ R, i.e. ρ ≠ 1/2" (p. 528) conflicts with p. 529, which places the central zero at s = 1/2 − i x_0.

**Derivation.** Theorem 13.3.1.1 has a spectral side containing only critical-line zeros with capped multiplicity, so it cannot by itself say anything about zeros off the line or about multiplicities above [F:Q]. Any deduction of GRH and the bound has to compare it with an identity that counts every non-trivial zero with full multiplicity (for example Weil's explicit formula on the same class A). The comparison would give, for all φ ∈ A,

Σ_{σ(c)≠1/2} N(c) M(φ)(c|·|^{-1/2}) + Σ_{σ(c)=1/2, N(c)>[F:Q]} (N(c) − [F:Q]) M(φ)(c|·|^{-1/2}) = 0.

To conclude that both index sets are empty, one then needs a uniqueness theorem: a convergent series of Mellin-evaluation functionals with nonnegative integer coefficients cannot vanish identically on A unless every coefficient is zero. Neither the comparison identity nor this uniqueness statement appears in the manuscript. That missing argument is exactly the content Theorem 13.3.1.2 would have to supply.

**Fix.** Three things are needed:
- State Theorem 13.3.1.2 and identify "Theorem ??".
- Prove the deduction from a trace formula that has been reconciled with Theorem 12.5.1.1: same hypothesis on φ, same multiplicity weights, same spectral range.
- Either remove the attribution to Weil positivity in §14.1.2 (p. 528, p. 533) or reconcile it with §§1.4.6 and 1.7.2.

Until then, §14.1.2 should describe the multiplicity bound and critical-line location as the intended content of a theorem not yet proved, not as results "obtained".

---

<a id="issue-37"></a>
### Issue 37 — Theorem 13.3.1.1

**Issue.** The test subspace is called [F:ℚ]-codimensional; its conditions are independent across infinitely many components, so the codimension is infinite.

**Repair and status.** Repair: correct the statement. Not formalized; the nearest checked results are orthogonality and independence across character components.

**Printed.** The hypothesis (13.3.1.2) is imposed "for all integers 0 ≤ k ≤ [F:Q] − 1" and "for all χ ∈ Ĉ_F". Lines p. 522 call A "the [F:Q]-codimensional linear subspace A ⊂ D(C_F) defined by the vanishing conditions from (13.3.1.2)".

**Problem.** The condition attached to χ depends only on ω = χ|C¹_F. At s = −i x_0(χ), the character χ(τ(t)) t^s equals 1, so the evaluation point is the unique character of the ω-component that is trivial on τ(R_{>0}). So the conditions ℓ_{ω,k} are indexed by (ω, k) ∈ Ĉ¹_F × {0, …, [F:Q]−1}. The group Ĉ¹_F is infinite, since C¹_F is an infinite compact group (it contains the image of Π_{v finite} O_v^×).

**Derivation.** Use C_F ≅ R_{>0} × C¹_F via τ. For ω ∈ Ĉ¹_F and a ∈ C_c^∞(R_{>0}), define φ_{ω,a}(τ(t) g_1):= a(t) ω̄(g_1). This function is in D(C_F): it is smooth and compactly supported. Then

ℓ_{ω′,k}(φ_{ω,a}) = δ_{ω,ω′} μ_1(C¹_F) ∫_{R>0} (log t)^k a(t) dt/t.

The moment map a ↦ (∫ (log t)^k a dt/t)_{k<[F:Q]} is onto C^{[F:Q]}. So the family {ℓ_{ω,k}} is linearly independent and A = ∩ ker ℓ_{ω,k} has infinite codimension. If only one χ were meant, the conditions would not cover all components, but the c-sum in (13.3.1.3) runs over all of Ω(C_F).

**Fix.** Say "the closed subspace A of countably infinite codimension, cut out by [F:Q] conditions on each component ω ∈ Ĉ¹_F", or restrict the theorem to a single component.

---

<a id="issue-38"></a>
### Issue 38 — Corollary A.5.4.3, (A.5.4.16)

**Issue.** (A.5.4.16) drops the normalisation 1/μ(U<sub>k</sub>), and the multiplier passage at every regular point is false (f = sgn·|t|<sup>−1/2</sup>, φ = sgn·|t|<sup>1/4</sup>).

**Repair and status.** Repair: require bounded normalised absolute averages. Lean: (A.5.4.16) with the normalisation kept, for any measure (`GeometricRound3D.normalized_multiplier_error_bound`); the multiplier passage on C<sub>K</sub> × C<sub>K</sub> under bounded normalised absolute averages (`GeometricRound4D.continuous_idele_diagonal_multiplier_limit`); for the clopen carving masks the passage is exact (`GeometricC.unitCarving_indicator_eventually_eq`).

The result is Corollary A.5.4.3. The equation label (A.5.4.3) at p. 583 is an unrelated display in the proof of Theorem A.5.4.1.

**Printed.**
- Statement: for f ∈ L¹_loc(G, µ_G) and φ ∈ C_c(G), lim_k A_{U_k}(φf)(x) "exists at all the points x ∈ G at which the limit of the sequence {A_{U_k}(f)(x)} exists", and equals φ(x) · lim A_{U_k}(f)(x) (A.5.4.15). Here A_{U_k}(f)(x) = µ_G(U_k)^{-1} ∫_{xU_k} f dµ_G.
- (A.5.4.16): |A_{U_k}(φf)(x) − φ(x)A_{U_k}(f)(x)| ≤ µ_G(U_k)^{-1} ∫_{xU_k} |(φ(y) − φ(x)) f(y)| dµ_G(y) ≤ sup_{y∈xU_k} |φ(y) − φ(x)| · ‖f‖_{L¹(xU_k)}.
- (A.5.4.17) then replaces ‖f‖_{L¹(xU_k)} by the fixed quantity ‖f‖_{L¹(xU_{k_0})}.
- The proof concludes that the sequence "converges if and only if {A_{U_k}(f)(x)} does."

**Problem.**
- The last inequality in (A.5.4.16) drops the factor µ_G(U_k)^{-1}. The correct bound is sup_{xU_k} |φ − φ(x)| · A_{U_k}(|f|)(x).
- A_{U_k}(|f|)(x) need not stay bounded at a point where the signed averages A_{U_k}(f)(x) converge.

**Derivation.**
- *The printed bound is false.* Take G = R, U_k = (−r, r), x = 0, f = 1_{(0,∞)}, and φ(y) = y near 0. Then the left side is (2r)^{-1} ∫_0^r y dy = r/4, while the printed right side is r · r = r². For r < 1/4 the inequality fails. The correct right side is r · (2r)^{-1} · r = r/2.
- *The corollary is false.* Take G = R with the D′-sequence U_k = (−2^{−k}, 2^{−k}) (monotone, doubling constant 2, shrinking to 0). Let f(t) = sgn(t)|t|^{−1/2} (with f(0) = 0); this is in L¹_loc. Since f is odd and U_k is symmetric, A_{U_k}(f)(0) = 0 for all k, so 0 is a regular point with value 0. Let η ∈ C_c(R) with η = 1 on [−1, 1].
- With φ(t) = η(t) sgn(t)|t|^{1/4} ∈ C_c(R): φf = |t|^{−1/4} near 0, and A_{(−r,r)}(φf)(0) = (2r)^{-1} · 2 · (4/3) r^{3/4} = (4/3) r^{−1/4} → ∞. The limit does not exist.
- With φ(t) = η(t) sgn(t)|t|^{1/2}: φf = 1 near 0. The averages tend to 1, but φ(0) · 0 = 0. The limit exists with the wrong value.
- *Downstream uses of the every-point form.* 12.1.1 (p. 500: "by Corollary A.5.4.3 we may rename…"; p. 501: "the limit in (12.1.1.13) exists and is finite exactly at the points at which…") and the forward direction of 12.2.2.2(4) (p. 511).

**Fix.** |A_{U_k}(φf)(x) − φ(x)A_{U_k}(f)(x)| ≤ sup_{xU_k} |φ − φ(x)| · A_{U_k}(|f|)(x). Hence (A.5.4.15) holds at every x where lim A_{U_k}(f)(x) exists and sup_k A_{U_k}(|f|)(x) < ∞:
- in particular at every Lebesgue point of f;
- therefore µ_G-almost everywhere, because the maximal function of f is finite a.e. by the Hardy–Littlewood maximal theorem of §A.5.3;
- the converse holds where in addition φ(x) ≠ 0.

The a.e. form cannot be restricted to the diagonal of G × G, which is a null set. Uses on the diagonal need a separate argument.

---

<a id="issue-39"></a>
### Issue 39 — Proposition B.4.3.2, Definition B.4.4.1

**Issue.** The principal-value counterterms are multiples of φ(1), so they vanish for the cutoff tests of §1.4.3 and cannot supply the missing bound.

**Repair and status.** Lean: at finite places, Weil's principal value equals the raw local term for tests vanishing on norm one, and the local terms are summable (`MasulloGRH.finiteLocalWeilPrincipalValue_eq_geometric`).

**Printed.**
- Lines pp. 28–29 set up the family:
- φ_z(t) = t^{−z} for t > 1, φ_z(t) = 0 for t < 1;
- φ_{h,ε,z} = h · (ρ_ε ∗ φ_z), with h ∈ D(R_{>0}) supported in (1, +∞) and 0 ≤ h ≤ 1, where h ↑ 1_{(1,∞)} and ε → 0;
- φ = χ · (φ_{h,ε,z}∘|·|_F).
- Lines p. 29: the integrals Σ_{v real} (1/2) ∫_{R_{>0}} Σ_{u∈{±1}} χ_v(tu)φ(tu)|t|^{1/2}/|1 − t| dt/t (and the complex analogue) "are bounded above by a common constant A > 0 independent of z ∈ K and independent of the specific φ."
- Proposition B.4.3.2:
- real v, (B.4.3.13): ⟨Ĵ_v, f⟩ = −lim_{ε→0+} (∫_{|x|≥ε} f(x) dx/|x| + 2f(0) log ε − 2(log 2π + γ) f(0));
- complex v, (B.4.3.14): the analogue with counterterms 2π f(0) log ε and −4π(log 2π + γ) f(0).
- Definition B.4.4.1:
- (B.4.4.1): C∫_{F_v^×} f dµ_v:= −⟨Ĵ_v, f⟩ for v | ∞ and −µ_v(O_v^×)⟨Ĵ_v, f⟩ for v ∤ ∞;
- (B.4.4.2): ∫′ f(x)|x|^{1/2}/|1 − x| dµ_v:= C∫ f(1 + x)|1 + x|^{−1/2} dµ_v.

**Derivation.**
- *Counterterms vanish.* Put F(x):= f(1 + x)|1 + x|^{−1/2}. Every counterterm in (B.4.3.13)–(B.4.3.14) is a multiple of F(0) = f(1). If f(1) = 0, then F(x) = O(|x|) and C∫F = ∫ F(x) dx/|x| (real case, and likewise complex), an absolutely convergent ordinary integral. At finite places, (B.4.3.5) gives C∫F = ∫F dµ_v for F vanishing near 0. The manuscript states this itself in Lemma B.4.4.3, (B.4.4.5): ∫′ = ∫ when f(1) = 0.
- *These tests vanish near norm one.* Since supp h ⊂ [1 + δ_h, T], each test above vanishes on {|g| < 1 + δ_h}, a neighbourhood of g = 1. So for them the Connes–Weil principal value equals the unregularized integral. More generally this holds for every test with φ(C^1_F) = 0. The regularization therefore cannot provide a bound the raw integral lacks.
- *The raw integral is unbounded over the family.* Take F = Q and χ = 1. Fix z ∈ K and set c:= 1/(10(1 + sup_K |z|)).
- For t ≥ e^{ε′} (ε′ the log-support radius of ρ_ε), (ρ_ε ∗ φ_z)(t) = t^{−z} ρ̂_ε(z), with ρ̂_ε(z):= ∫ ρ_ε(s) s^z ds/s → 1 uniformly on K.
- Choose h_n = 1 on [1 + 1/n, e^c] and ε small enough that e^{ε′} ≤ 1 + 1/n. For t ∈ [1, e^c], Re(t^{−z} ρ̂_ε(z)) ≥ 1/2 and t^{−1/2} ≥ 0.9.
- So the u = +1 term is at least 0.45 ∫_{1+1/n}^{e^c} dt/(t − 1) = 0.45 log(n(e^c − 1)), which tends to ∞.
- The tail t > e^c is uniformly bounded (Re z > sup I is not needed for convergence there, since the integrand is O(t^{−Re z − 3/2}) and K is compact). The u = −1 term is bounded with the correct denominator |1 + t| (see ADDITIONAL A3).
- Hence no constant A exists. The PV versions ∫′ that enter Theorem 12.5.1.1 coincide with these integrals, so they diverge too.

**Fix.** The Montel step needs uniform control of the archimedean terms across the family. This requires a family that keeps a fixed distance from norm one (and then a separate passage to the limit h → 1_{(1,∞)}), or a renormalization that subtracts the log-divergence explicitly and tracks it on both sides of the trace formula. The printed bound cannot be obtained from Definition B.4.4.1.

---

<a id="issue-40"></a>
### Issue 40 — Lemmas B.4.4.8–B.4.4.9, (B.4.4.16)

**Issue.** There is no density hypothesis on the zero set (the author's footnotes ask for one), and the zero sum lacks multiplicity weights; a discrete set can make the sum diverge.

**Repair and status.** Repair: add a multiplicity-weighted counting bound. Lean: a weighted counting bound implies weighted summability (`ConditionalGRHReviewD.summable_weight_mul_rpow_neg_of_count`); for a nonzero entire function, a multiplicity-weighted R(1 + log R) zero count gives Σ ord<sub>z</sub>/|z − c|² < ∞ (`ConditionalGRHReviewD.entire_zero_order_inverse_square_summable`); Jensen zero counts for Dirichlet L-functions over ℚ. The counting bound for Hecke zeros is not yet formalized.

**Printed.**
- Lemma B.4.4.8: if Z ⊂ Ω(G) meets every connected component discretely and inside a single vertical strip of bounded width, then for any φ ∈ D(G), Σ_{c∈Z} ∫_G φ c dµ_G converges absolutely (B.4.4.17).
- Proof: the Mellin transform Φ decays rapidly on strips, "and thereby implies the absolute convergence of the sum" (p. 624). The decay is stated only on the region where |Im s| > T *and* ‖a‖_∞ > T.
- Footnote 25 (p. 624): "Need some hypothesis on Z preventing 'too many' c ∈ Z near a given large height." Footnote 26 (p. 624): "Must explain clearly how we are bringing in that Z doesn't accumulate too much at a given height."
- Lemma B.4.4.9: for any subset Z of {c: L(c) = 0}, Σ_{c∈Z} ∫ φ c |·|^a dµ converges absolutely; the proof ends "The result then follows from Lemma B.4.4.8" (p. 625).
- (B.4.4.16) sums over c ∈ Ω(C_F) with L(c) = 0, without a multiplicity factor. Line p. 625 calls this sum "absolutely convergent by Lemma B.4.4.9".

**Problem.** Discreteness plus rapid decay bounds each term, but says nothing about how many terms there are. Lemma B.4.4.8 is false without a counting hypothesis. Lemma B.4.4.9 inherits the gap, and the explicit formula needs zeros counted with multiplicity.

**Derivation (counterexample to Lemma B.4.4.8).**
- Take G = R_{>0} with module the identity (so G^1 = {1}), µ_G = dt/t, and Ω(G) = {t ↦ t^s} ≅ C, a single component. Take φ ∈ C_c^∞(R_{>0}), φ ≠ 0.
- Its Mellin transform M(s) = ∫ φ(t) t^s dt/t = ∫ ψ(u) e^{su} du, with ψ(u) = φ(e^u) ∈ C_c^∞(R), is entire and not identically zero. So on each segment i[n, n+1] it is not identically zero, and m_n:= max_{y∈[n,n+1]} |M(iy)| > 0.
- By continuity, |M| ≥ m_n/2 on a subinterval of i[n, n+1]. Place N_n:= ⌈2/m_n⌉ distinct points of Z there.
- Then Z ⊂ iR (a strip of width 0) and Z ∩ {|Im s| ≤ T} is finite, so Z is discrete.
- But Σ_{c∈Z} |∫ φ c dµ| ≥ Σ_n N_n · m_n/2 ≥ Σ_n 1 = ∞.

Rapid decay forces m_n = O(n^{−M}), so this needs N_n growing faster than any polynomial. A polynomial counting bound #{c ∈ Z: T ≤ |Im c| ≤ T + 1, ‖a(c)‖ ≤ T} ≪ (1 + T)^A, joint in the height and in the discrete parameter a on the components of Ω(G), restores the lemma. The printed decay region also has to be the union, |Im s| > T *or* ‖a‖_∞ > T, not the intersection.

- *Multiplicity.* Weil's explicit formula counts each zero with weight ord_c L. (B.4.4.16) omits the weight. Lemma B.4.4.9, which is about subsets of the zero set, does not control the weighted sum unless the multiplicities are bounded. The bound N(T, χ) ≪ (1 + T) log(q_χ(T + 2)), counted with multiplicity and uniform in the analytic conductor, supplies both the counting and the multiplicity bound. It is not stated or proved.
- *Convergence in D(C_F)′_β.* Theorem B.4.4.7 asserts convergence in the strong dual. That needs these bounds uniformly on bounded subsets of D(C_F). Discreteness plus pointwise decay do not justify the interchange of sum and limit.

**Fix.**
- Add to Lemma B.4.4.8 a polynomial counting hypothesis on Z, joint in Im c and the component parameter.
- In Lemma B.4.4.9, verify that hypothesis for Hecke zeros via the zero-counting theorem for Hecke L-functions, counted with multiplicity.
- Insert ord_c L(c) in (B.4.4.16) and in its uses.

---

<a id="issue-41"></a>
### Issue 41 — Lemma C.3.4.4(2)

**Issue.** ‖AT‖<sub>1</sub> = ‖TA‖<sub>1</sub> is false (A = diag(1, 0), T = E<sub>12</sub>).

**Repair and status.** Repair: the two one-sided bounds suffice. Lean proves both (`traceNorm_comp_left_le`, `traceNorm_comp_right_le`).

**Printed.** "(2) For any T ∈ N(H) and A ∈ B(H), we have (C.3.4.3) ||AT||_Tr = ||TA||_Tr ≤ ||A|| ||T||_Tr." Proof, p. 698: "(2): This is [Cnw-c, Ch.3, Thm.18.11(g, e)]."

**Problem.** The two one-sided ideal inequalities are true. The equality between the two orders of composition is false.

**Derivation.** Take H = C², A = diag(1,0) = E_11 (‖A‖ = 1) and T = E_12 (singular values (1,0), so ‖T‖_1 = 1). Then:

- AT = E_11 E_12 = E_12, with singular values (1, 0), so ‖AT‖_1 = 1.
- TA = E_12 E_11 = 0, so ‖TA‖_1 = 0.

Hence ‖AT‖_1 = 1 ≠ 0 = ‖TA‖_1, while ‖AT‖_1 ≤ ‖A‖ ‖T‖_1 = 1 and ‖TA‖_1 ≤ 1 both hold. I checked the numbers with numpy. The identity that is true is ‖X‖_1 = ‖X*‖_1, which gives ‖AT‖_1 = ‖T*A*‖_1, not ‖TA‖_1.

**Fix.** Replace (C.3.4.3) with: ‖AT‖_Tr ≤ ‖A‖ ‖T‖_Tr and ‖TA‖_Tr ≤ ‖A‖ ‖T‖_Tr. Searching the manuscript turns up no citation of C.3.4.4(2) specifically. The general citations of Lemma C.3.4.4 at p. 453, p. 459, p. 501, p. 501 and p. 502 concern part (1), continuity of the trace, or S_p convergence. Wherever (2) is used, the inequalities are enough.

---

<a id="issue-42"></a>
### Issue 42 — Lemma C.3.6.3(1)

**Issue.** σ<sub>n</sub>(A + B) ≤ σ<sub>n</sub>(A) + σ<sub>n</sub>(B) is false (diag(1, 0) + diag(0, 1) at n = 2).

**Repair and status.** Repair: the Ky Fan form σ<sub>m+n−1</sub>(A + B) ≤ σ<sub>m</sub>(A) + σ<sub>n</sub>(B). Lean: the trace-norm triangle inequality and the finite rank-one costings used in its place (`traceNorm_add_le`); singular values are not formalized.

**Printed.** Definition at p. 704: σ_k(T):= inf{ ‖A − T‖: dim Im(A) ≤ k−1 }. Lemma C.3.6.3: "(1) σ_m(A+B) ≤ σ_m(A) + σ_m(B), for any A, B ∈ L(E, F). (2) |σ_m(A) − σ_m(B)| ≤ ‖A − B‖. (3) σ_{m+n}(AB) ≤ σ_m(A) σ_n(B)." Proof: "This is [Jar, §19.8, Prop. 1]." At p. 706: "the triangle inequality for ‖·‖_{S_p}, which follows from Lemma C.3.6.3(1)".

**Problem.** Part (1) is false for every m ≥ 2. Part (2) is true. Part (3) is true but weaker than the standard σ_{m+n−1}(AB) ≤ σ_m(A) σ_n(B).

**Derivation.** Take E = F = C², A = diag(1,0), B = diag(0,1), m = 2. A and B have rank 1, so σ_2(A) = σ_2(B) = 0 (take the approximant equal to the operator itself). A + B = I_2. Every R with rank ≤ 1 has a unit vector x in its kernel, so ‖(I − R)x‖ = 1 and σ_2(I_2) = 1. Hence σ_2(A+B) = 1 > 0 = σ_2(A) + σ_2(B). I checked the numbers with numpy: σ(A) = σ(B) = (1, 0) and σ(A+B) = (1, 1).

The correct additivity is σ_{m+n−1}(A+B) ≤ σ_m(A) + σ_n(B). To prove it, pick R_A of rank ≤ m−1 and R_B of rank ≤ n−1 that nearly attain σ_m(A) and σ_n(B). Then R_A + R_B has rank ≤ m+n−2, and ‖(A+B) − (R_A+R_B)‖ ≤ ‖A − R_A‖ + ‖B − R_B‖. A random 5×5 test over m, n ≤ 3 found no violation. The same-index form holds only for m = 1. Part (2) is the case n = 1 of the correct form.

Effect on p. 706: the triangle inequality for ‖·‖_{S_p} is true but does not follow from the corrected (1). The corrected (1) gives σ_{2k−1}(A+B), σ_{2k}(A+B) ≤ σ_k(A) + σ_k(B), which yields only ‖A+B‖_p ≤ 2^{1/p}(‖A‖_p + ‖B‖_p). The full triangle inequality needs Ky Fan's inequality Σ_{k≤n} σ_k(A+B) ≤ Σ_{k≤n} σ_k(A) + Σ_{k≤n} σ_k(B) for all n, plus the fact that weak majorization is preserved by the increasing convex function t ↦ t^p (followed by Minkowski in ℓ^p).

**Fix.** Replace (1) with σ_{m+n−1}(A+B) ≤ σ_m(A) + σ_n(B). Optionally sharpen (3) to σ_{m+n−1}(AB) ≤ σ_m(A) σ_n(B). At p. 706, cite the Schatten-norm triangle inequality via Ky Fan. For the finite rank-one sums in (C.3.6.13) a shorter route works: ‖X‖_{S_p} ≤ ‖X‖_{S_1}, and ‖Σ_r ⟨·, e_r⟩ u_r‖_{S_1} ≤ Σ_r ‖e_r‖ ‖u_r‖ because χ_π is an isometry onto S_1 (Prop. C.3.6.4(3)).

---

<a id="issue-43"></a>
### Issue 43 — Proposition C.3.6.5, proof

**Issue.** Typos make terms cancel to zero, and C.3.6.3(2) is cited where the ideal inequality is needed.

**Repair and status.** Lean proves the content for p = 1 and 2: finite-rank right composition, trace-norm left composition, and nested projections in nuclear norm applied to the interval convolution (`Round173E.finite_block_cutoffs_nuclear_error`, `Q.FullSourceCutoff.both_tests_full_source_nuclearNorm_tendsto`).

**Printed.**
- (C.3.6.13), p. 706: "‖C_j A − CA‖_{S_p} ≤ Σ_r |λ_r| ‖C_j f_r − C_j f_r‖_F" and "‖AB_k − AB_k‖_{S_p} ≤ Σ_r |λ_r| ‖B_k e_r − B e_r‖_E".
- p. 706: "‖⟨(B_k* e_r − B_k* e_r, ·⟩ f_r‖".
- (C.3.6.14), p. 706: "‖CAB_k − CAB_k‖_{S_p}", twice.
- p. 706: "‖C_j AB_k − CAB_k‖_{S_p} ≤ ‖C_j A − CA‖_{S_p} ‖B_k‖ by (C.3.5.11) and Lemma C.3.6.3(2)".

**Problem.**
1. As printed, the right side of the first inequality is identically 0, and so is the left side of the second.
2. The needed inequality ‖XB‖_{S_p} ≤ ‖X‖_{S_p} ‖B‖ for X: E → F and B ∈ L(E) follows from the ideal inequality σ_m(XB) ≤ σ_m(X) ‖B‖. That is the rectangular analogue of (C.3.5.11). Lemma C.3.6.3(2), Lipschitz continuity of σ_m, does not give it.

**Fix.** Read C_j f_r − C f_r, AB_k − AB, B_k* e_r − B* e_r, and CAB_k − CAB. Cite the rectangular form of (C.3.5.11), whose proof via (C.3.5.12)–(C.3.5.15) carries over verbatim, in place of C.3.6.3(2).

---

<a id="issue-44"></a>
### Issue 44 — Converse argument (Chapters 3, 7, 10)

**Issue.** The converse needs factorised tests dense in S<sub>0</sub> and theta continuous into W<sub>I</sub><sup>s</sup>; neither is shown.

**Repair and status.** Repair: a two-pivot correction, and lattice/Poisson bounds for theta. Lean: the correction and density on any topological vector space, calibrated with the actual Gaussians (`DenseS0.dense_original_kernel`, `ActualRealS0.actual_gaussian_calibration`); S<sub>0</sub> is closed in the mixed Schwartz space; lattice theta is continuous in the full mixed Schwartz test, with explicit seminorm bounds and two-sided decay (`SpectralF909.actual_ideal_theta_continuous_test`); continuity into W<sub>I</sub><sup>s</sup>(C<sub>K</sub>) enters the converse as a hypothesis.

**Gap.** The converse argument needs finite sums of factorised tests that already lie in S₀ = {f: f(0) = 0, f̂(0) = 0} to be dense in S₀. Factorised approximants of an f ∈ S₀ generally satisfy neither constraint.

**Two-evaluation correction**.
1. Let D be the span of factorised tests. Pick g ∈ D with g(0) = 1 and p:= ĝ(0) > 0: a compact-open indicator at the finite places times Gaussians at the archimedean places.
2. Let k be g dilated by r ≠ 1 at one archimedean place. Then k(0) = 1 and q:= k̂(0) = r^{−d}p ≠ p, with d = 1 at a real place and d = 2 at a complex place.
3. Set u = (qg − pk)/(q − p) and v = (k − g)/(q − p). Then u(0) = 1, û(0) = 0, v(0) = 0 and v̂(0) = 1.
4. Define Qf = f − f(0)u − f̂(0)v. It is continuous, Q = id on S₀, and Q(D) ⊆ D ∩ S₀.
5. For f ∈ S₀ and a net d_i → f in D, we get Q d_i → Qf = f. Closure is enough here, so no normability or sequential density of the LF topology is needed.

**Theta continuity on S₀** (paper level; attachment to the manuscript's source estimates not yet verified).
- At large norm, |Φ_K(f)(x)| ≤ p_N(f)|x|^{−N}.
- At small norm, Poisson summation gives Σ_γ f(γx) = |x|^{−1} Σ_γ f̂(γ/x). With f(0) = f̂(0) = 0 both γ = 0 terms drop out, which gives the matching bound.
- Taking N larger than the weight exponents and |a| bounds the H-norm by p_N(f).

---
