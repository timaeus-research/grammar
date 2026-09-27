You are Astra, design consultant for the Lean 4 formalisation (repo timaeus-research/grammar, namespace Grammar, main 7b1810e, 1011 modules, zero sorry/axiom) of the examples note `examples_slop.tex` (Gerraty–Murfet grammar paper). Your round-24 target 1 is DONE in two units, both essentially first-try: DCLXXIV (`JetUniqueness.lean`, your scaled-remainder lemma verbatim, induction with `f ↦ (f − h₀)/u`) and DCLXXV (`DepthJetAllCoefficients.lean`): `depthJet D z = 2^{((D:ℂ)−1)z}Γ(½−z)Γ(1+z)^D/√π` (I kept `cpow`; `AnalyticAt.cpow` on `2 ∈ slitPlane` was painless), `depthJetCoeff D j = iteratedDeriv j (depthJet D) 0/j!`, analyticity, Mathlib's `HasFPowerSeriesAt.isBigO_sub_partialSum_pow` remainder with coefficients identified by `HasFPowerSeriesOnBall.factorial_smul`, the all-depth closed form at `z = 1 − 2u` and the reindexed poles, and the boxed identities exactly as you normalised them: `a_{L+1,k} = (h_{L+1,L−k}).re/(s^L k!)` for `k ≤ L`, `Q_{L+1} = (h_{L+1,L+1}).re/(2s^L)`, plus `depthJetCoeff_im = 0` and the regression `a_{L+1,L} = 1/(s^L L!)`. Numerics (`gauss_depth_jet_all_check.py`, mpmath Taylor): `A_L, B_L, C_L` (L = 2..6) and the closed `D₄` to 1e-30; `D₅, E₅, Q₂..Q₅` at quadrature accuracy. So the Gaussian DLN expansion is formally closed at every depth modulo the real symbols `Γ^{(j)}(1)`, `Γ^{(j)}(½)`; DCLXXIII gives `Γ^{(r)}(1) = G_r`, DCLXXII reduces `Γ'''(½)`.

MATHLIB SCOUT (pin v4.33.1) for the next step:
```
.lake/packages/mathlib/Mathlib/Analysis/Calculus/IteratedDeriv/Lemmas.lean:368:theorem iteratedDeriv_const_mul {n : ℕ} {f : 𝕜 → 𝔸} (c : 𝔸) (hf : ContDiffAt 𝕜 n f x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/IteratedDeriv/Lemmas.lean:376:theorem iteratedDeriv_const_mul_field {n : ℕ} (c : 𝕜') (f : 𝕜 → 𝕜') :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/IteratedDeriv/Defs.lean:70:theorem iteratedDerivWithin_eq_iteratedDeriv (hs : UniqueDiffOn 𝕜 s) (h : ContDiffAt 𝕜 n f x)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:446:protected theorem HasFPowerSeriesAt.deriv (h : HasFPowerSeriesAt f p x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:467:@[fun_prop] protected theorem AnalyticAt.deriv [CompleteSpace F] (h : AnalyticAt 𝕜 f x) :
```
(no `iteratedDeriv_mul` Leibniz, no 1-D Cauchy-product-of-coefficients statement for `HasFPowerSeriesAt` that I could find; `AnalyticAt.deriv`, eventual equalities on open sets, `HasDerivAt` product rule, `Finset.sum_range_succ`, `Nat.choose_succ_succ` are available).

## HEADLINES rows DCLXXIV–DCLXXV
| **DCLXXIV** | ★★ **UNIQUENESS OF A FINITE JET FROM SCALED REMAINDERS (u1010; Astra round-24 target 1, generic half)**: `JetUniqueness.lean` — `sum_range_succ_pow_shift` (`Σ_{j<n+1} d_j u^j = d₀ + u Σ_{j<n} d_{j+1} u^j`), `tendsto_sum_range_pow_nhdsGT` (a polynomial sum tends to its constant term at `0⁺`), `tendsto_ofReal_nhdsGT_zero`, ★★ `jet_unique_of_scaled_remainders` (`f : ℝ → ℂ`, complex coefficients `h c`, real `u`: if `(f − Σ_{j≤n} h_j u^j)/u^n → 0` and `(f − Σ_{j<n} c_j u^j)/u^n → q` at `0⁺` then `h_j = c_j` for `j < n` and `h_n = q`; induction on `n` generalising `f h c q`: multiply by `u^{n+1}` so both unscaled remainders vanish, `h₀ = c₀` by `tendsto_nhds_unique`, then shift `f ↦ (f − h₀)/u` with `Tendsto.congr'` + `field_simp; ring` on `u ≠ 0`). Neither Laurent series nor l'Hôpital: the reusable replacement for DCLXXI's order-by-order pole matching. Lean: `nhdsWithin_le_nhds` needs `(s := Set.Ioi 0)` when composed with `Tendsto.mono_left` (the set is not inferred); `continuous_finset_sum` → `continuous_finsetSum`. | JetUniqueness.lean |
| **DCLXXV** | ★★★ **EVERY COEFFICIENT OF EVERY `P_L` AND EVERY RESIDUAL MASS FROM THE TAYLOR JET OF `H_L` (u1011; examples_slop §2; Astra round-24 target 1)**: `DepthJetAllCoefficients.lean` — `depthJetReal D u`/`depthJet D z = 2^{(D−1)z}Γ(½−z)Γ(1+z)^D/√π` (`depthJet_ofReal`, `depthJet_zero = 1`), `depthJetCoeff D j = iteratedDeriv j (depthJet D) 0/j!` (`depthJetCoeff_zero = 1`), `analyticAt_depthJet` (`AnalyticAt.cpow` on `2 ∈ slitPlane`, `analyticAt_Gamma_of_re_pos` composed with affine maps, `.pow`, `.div`), `isBigO_depthJet_sub_partialSum` (Mathlib's `HasFPowerSeriesAt.isBigO_sub_partialSum_pow` at order `D + 1`, coefficients identified by `HasFPowerSeriesOnBall.factorial_smul` + `iteratedDeriv_eq_iteratedFDeriv` + `apply_eq_pow_smul_coeff`), `tendsto_depthJet_remainder` (`O(u^{D+1})/u^D = O(u) → 0` via `IsBigO.of_bound` + `IsBigO.trans_tendsto`), `two_rpow_neg_half_sub`, `depthClosed_eq` (`M_{L+1}(1−2u) = H_{L+1}(u)/(2s^L u^{L+1})` at every depth: `Real.Gamma_add_one`, `(2^{u−½})^L = 2^{Lu}/√2^L`, `√(2π)^L = √2^L√π^L`; `div_pow` BEFORE `field_simp` or `u⁻¹^L` survives), `depthPoles_sum_eq` (`Fin.sum_univ_eq_sum_range`, `natDegree_enginePoly`, `Finset.sum_range_reflect` with the explicit summand, `Finset.sum_div`, `u^{L+1} = u^{L−j+1}u^j` by `pow_add` + `omega`), `tendsto_depthJet_scaled` (DCLXX's `tendsto_gammaProduct_sub_poles` composed with `z = 1 − 2u`, scaled by `2s^L` and cast to `ℂ`), `depthJetCoeff_eq` (the jet-uniqueness lemma applied), ★★★ `coeff_enginePoly_eq_depthJetCoeff` (`a_{L+1,k} = (h_{L+1,L−k}).re/(s^L k!)`, `k ≤ L`), ★★★ `residualMass_eq_depthJetCoeff` (`Q_{L+1} = (h_{L+1,L+1}).re/(2s^L)`), `depthJetCoeff_im = 0` (the jet is real), regression `coeff_enginePoly_top_eq` (`a_{L+1,L} = 1/(s^L L!)` from `h₀ = 1`, = `leadingCoeff_enginePoly`). Every `P_L` and every `Q_L` is now the Taylor jet of one explicit analytic Gamma product, whose derivatives at `0` are polynomials in `log 2`, `Γ^{(j)}(1)`, `Γ^{(j)}(½)` (DCLXXIII), the half-point ones reducible by duplication (DCLXXII at order 3; all orders by power-series multiplication, Astra round 24). Astra round 24 (`tide-log/gpt6_examples_round24_v1.md`): DCLXXII–DCLXXIII fidelity confirmed (independent `D₄` re-derivation `D₄πs = b³/12 + 7π²b/24 − λ₃/4`); ranking (i) all-depth jet ≫ (iii) all-orders duplication via power-series coefficients (`e_n = Σ_k 2^k g_k(−2ℓ)^{n−k}/(n−k)! − Σ_{k<n} e_k g_{n−k}`, `g_n = Γ^{(n)}(1)/n!`, `e_n = Γ^{(n)}(½)/(√π n!)`, from `Γ(½+z)Γ(1+z)/√π = e^{−2ℓz}Γ(1+2z)`) > (iv) ζ-recurrence packaging (derive the recurrence from `H' = B'H`; the log-Gamma-to-ζ bridge stays explicit) > (ii) depth five > cone/NB/blow-up. | DepthJetAllCoefficients.lean |

## Public statements of DCLXXIV
```lean
/-- `Σ_{j<n+1} d_j u^j = d_0 + u Σ_{j<n} d_{j+1} u^j`. -/
theorem sum_range_succ_pow_shift (d : ℕ → ℂ) (n : ℕ) (u : ℂ) :
    ∑ j ∈ range (n + 1), d j * u ^ j = d 0 + u * ∑ j ∈ range n, d (j + 1) * u ^ j

/-- A finite polynomial sum in a real variable tends to its constant term at `0⁺`. -/
theorem tendsto_sum_range_pow_nhdsGT (d : ℕ → ℂ) (n : ℕ) :
    Tendsto (fun u : ℝ => ∑ j ∈ range (n + 1), d j * (u : ℂ) ^ j) (𝓝[>] 0) (𝓝 (d 0))

theorem tendsto_ofReal_nhdsGT_zero : Tendsto (fun u : ℝ => (u : ℂ)) (𝓝[>] 0) (𝓝 0)

/-- ★★ **Uniqueness of the order-`n` jet from scaled remainders.** -/
theorem jet_unique_of_scaled_remainders (n : ℕ) (f : ℝ → ℂ) (h c : ℕ → ℂ) (q : ℂ)
    (hh : Tendsto (fun u : ℝ => (f u - ∑ j ∈ range (n + 1), h j * (u : ℂ) ^ j) / (u : ℂ) ^ n)
      (𝓝[>] 0) (𝓝 0))
    (hc : Tendsto (fun u : ℝ => (f u - ∑ j ∈ range n, c j * (u : ℂ) ^ j) / (u : ℂ) ^ n)
      (𝓝[>] 0) (𝓝 q)) :
    (∀ j < n, h j = c j) ∧ h n = q
```

## Public statements of DCLXXV
```lean
lemma of `JetUniqueness` identifies
(★★★ `coeff_enginePoly_eq_depthJetCoeff`, ★★★ `residualMass_eq_depthJetCoeff`)

  `a_{L+1,k} = h_{L+1,L−k}/(s^L k!)` for `k ≤ L`,   `Q_{L+1} = h_{L+1,L+1}/(2 s^L)`,

at every depth: the engine's polynomial and residual mass are the Taylor jet of one explicit
analytic Gamma product, whose derivatives at `0` are polynomials in `log 2`, `Γ^{(j)}(1)` and
`Γ^{(j)}(½)` (DCLXXIII, DCLXXII).  Regression: `depthJetCoeff_zero = 1` reproduces the leading
coefficient.  Examples_slop §2; Astra round 24 target 1.  Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology Finset Asymptotics Polynomial

namespace Grammar

/-! ### The jet function -/

/-- `H_D(u) = 2^{(D−1)u} Γ(½ − u) Γ(1 + u)^D/√π` (real). -/
noncomputable def depthJetReal (D : ℕ) (u : ℝ) : ℝ

/-- `H_D(z) = 2^{(D−1)z} Γ(½ − z) Γ(1 + z)^D/√π` (complex). -/
noncomputable def depthJet (D : ℕ) (z : ℂ) : ℂ

/-- The Taylor coefficients `h_{D,j} = H_D^{(j)}(0)/j!`. -/
noncomputable def depthJetCoeff (D j : ℕ) : ℂ := iteratedDeriv j (depthJet D) 0 / (j.factorial : ℂ)

theorem depthJet_ofReal (D : ℕ) (u : ℝ) : depthJet D u = ((depthJetReal D u : ℝ) : ℂ)

theorem depthJet_zero (D : ℕ) : depthJet D 0 = 1

theorem depthJetCoeff_zero (D : ℕ) : depthJetCoeff D 0 = 1

theorem analyticAt_depthJet (D : ℕ) : AnalyticAt ℂ (depthJet D) 0

theorem isBigO_depthJet_sub_partialSum (D : ℕ) :
    (fun y : ℂ => depthJet D y - ∑ j ∈ range (D + 1), depthJetCoeff D j * y ^ j) =O[𝓝 0]
      fun y => ‖y‖ ^ (D + 1)

theorem tendsto_depthJet_remainder (D : ℕ) :
    Tendsto (fun u : ℝ => (depthJet D u - ∑ j ∈ range (D + 1), depthJetCoeff D j * (u : ℂ) ^ j) /
      (u : ℂ) ^ D) (𝓝[>] 0) (𝓝 0)

theorem two_rpow_neg_half_sub (u : ℝ) : (2 : ℝ) ^ (-(1 - 2 * u) / 2) = 2 ^ u / Real.sqrt 2

/-- `M_{L+1}(1 − 2u) = H_{L+1}(u)/(2 s^L u^{L+1})`. -/
theorem depthClosed_eq (L : ℕ) {u : ℝ} (hu0 : 0 < u) :
    ((2 : ℝ) ^ (-(1 - 2 * u) / 2)) ^ L * Real.Gamma ((1 - 2 * u) / 2) *
      Real.Gamma ((1 - (1 - 2 * u)) / 2) ^ (L + 1) / (2 * Real.sqrt Real.pi ^ (L + 1)) =
      depthJetReal (L + 1) u / (2 * Real.sqrt (2 * Real.pi) ^ L * u ^ (L + 1))

/-- The poles at `z = 1 − 2u`, reindexed: `Σ_k 2^k k! a_k/(2u)^{k+1} =
Σ_j s^L (L−j)! a_{L−j} u^j/(2 s^L u^{L+1})`. -/
theorem depthPoles_sum_eq (L : ℕ) (hL : 1 ≤ L) {u : ℝ} (hu : u ≠ 0) :
    ∑ k : Fin ((enginePoly (L + 1)).natDegree + 1), (2 ^ (k : ℕ) * (enginePoly (L + 1)).coeff k) *
      ((k : ℕ).factorial : ℝ) / (1 - (1 - 2 * u)) ^ ((k : ℕ) + 1) =
      (∑ j ∈ range (L + 1), Real.sqrt (2 * Real.pi) ^ L * ((L - j).factorial : ℝ) *
        (enginePoly (L + 1)).coeff (L - j) * u ^ j) /
        (2 * Real.sqrt (2 * Real.pi) ^ L * u ^ (L + 1))

/-- DCLXX's finite part as a scaled remainder of `H_{L+1}` of order `L + 1`. -/
theorem tendsto_depthJet_scaled (L : ℕ) (hL : 1 ≤ L) :
    Tendsto (fun u : ℝ => (depthJet (L + 1) u - ∑ j ∈ range (L + 1),
      ((Real.sqrt (2 * Real.pi) ^ L * ((L - j).factorial : ℝ) *
        (enginePoly (L + 1)).coeff (L - j) : ℝ) : ℂ) * (u : ℂ) ^ j) / (u : ℂ) ^ (L + 1))
      (𝓝[>] 0)
      (𝓝 ((2 * Real.sqrt (2 * Real.pi) ^ L *
        residualMass (L + 1) (enginePoly (L + 1)) : ℝ) : ℂ))

/-- The jet of `H_{L+1}` to order `L + 1` in terms of `P_{L+1}` and `Q_{L+1}`. -/
theorem depthJetCoeff_eq (L : ℕ) (hL : 1 ≤ L) :
    (∀ j < L + 1, depthJetCoeff (L + 1) j =
      ((Real.sqrt (2 * Real.pi) ^ L * ((L - j).factorial : ℝ) *
        (enginePoly (L + 1)).coeff (L - j) : ℝ) : ℂ)) ∧
    depthJetCoeff (L + 1) (L + 1) =
      ((2 * Real.sqrt (2 * Real.pi) ^ L * residualMass (L + 1) (enginePoly (L + 1)) : ℝ) : ℂ)

/-- ★★★ **Every coefficient of every `P_{L+1}` is a Taylor coefficient of `H_{L+1}`**:
`a_{L+1,k} = h_{L+1,L−k}/(s^L k!)` for `k ≤ L`. -/
theorem coeff_enginePoly_eq_depthJetCoeff (L : ℕ) (hL : 1 ≤ L) {k : ℕ} (hk : k ≤ L) :
    (enginePoly (L + 1)).coeff k =
      (depthJetCoeff (L + 1) (L - k)).re / (Real.sqrt (2 * Real.pi) ^ L * (k.factorial : ℝ))

/-- ★★★ **Every residual mass is a Taylor coefficient of `H_{L+1}`**:
`Q_{L+1} = h_{L+1,L+1}/(2 s^L)`. -/
theorem residualMass_eq_depthJetCoeff (L : ℕ) (hL : 1 ≤ L) :
    residualMass (L + 1) (enginePoly (L + 1)) =
      (depthJetCoeff (L + 1) (L + 1)).re / (2 * Real.sqrt (2 * Real.pi) ^ L)

/-- The jet coefficients are real. -/
theorem depthJetCoeff_im (L : ℕ) (hL : 1 ≤ L) {j : ℕ} (hj : j ≤ L + 1) :
    (depthJetCoeff (L + 1) j).im = 0

/-- Regression: the leading coefficient `a_{L+1,L} = 1/(s^L L!)` from `h_{L+1,0} = 1`. -/
theorem coeff_enginePoly_top_eq (L : ℕ) (hL : 1 ≤ L) :
    (enginePoly (L + 1)).coeff L = 1 / (Real.sqrt (2 * Real.pi) ^ L * (L.factorial : ℝ))
```

## Questions
1. Fidelity (brief): (a) `depthPoles_sum_eq` and `depthClosed_eq` normalisations (`s = √(2π)`, the `2^{k+1}` cancellation, `Γ(u) = Γ(1+u)/u`); (b) `tendsto_depthJet_scaled` as the hypothesis `hc` of the uniqueness lemma with `c_j = s^L (L−j)! a_{L−j}` and `q = 2 s^L Q_{L+1}`; (c) the coefficient identification `p.coeff j = iteratedDeriv j f 0 / j!` via `factorial_smul` at `y = 1`.
2. NEXT day-sized targets, please rank with Lean-facing interfaces: (i) ALL-ORDERS DUPLICATION. Two routes: (α) a hand-rolled Leibniz lemma `iteratedDeriv n (f * g) z = Σ_{k≤n} C(n,k) iteratedDeriv k f z · iteratedDeriv (n−k) g z` for `f, g` analytic on an open set (`AnalyticOnNhd ℂ f U`, `IsOpen U`, `z ∈ U`; induction with the eventual equality of `iteratedDeriv n (f*g)` and the sum on `U`, product rule termwise, Pascal) — then `Γ(2w)`, `2^{1−2w}`'s iterated derivatives (`iteratedDeriv_comp_const_mul` needs `ContDiff`; or eventual-equality inductions as in DCLXXIII) and the general relation `Σ_{k≤n} C(n,k)Γ^{(k)}(½)Γ^{(n−k)}(1) = √π Σ_{k≤n} C(n,k) 2^k Γ^{(k)}(1) (−2ℓ)^{n−k}` — from which `Γ^{(n)}(½)` is recursively a polynomial in `Γ^{(k)}(1)`, `ℓ`, `√π`; (β) your power-series multiplication `e_n` recurrence — but I found no coefficient-level Cauchy product for `HasFPowerSeriesAt` in 1-D at this pin; would you build (β) from (α) anyway (the Leibniz rule at `0` IS the Cauchy product), or is there a Mathlib path (`FormalMultilinearSeries` `mul`? `HasFPowerSeriesAt.mul`?) I missed? Which statement should the unit expose so that the depth-five and depth-six jets (`Γ''''(½)`, `Γ^{(5)}(½)`) follow by `simp`/`ring` later? (ii) The depth-three regression `depthJetCoeff 3 1 = c₁`, `depthJetCoeff 3 2 = c₂`, `depthJetCoeff 3 3 = c₃` against DCLXXI's `cubicH'`, `cubicH''` chains (now provable including order three because DCLXXIII makes `Γ'''(1)`, `Γ'''(½)` real) — worth a unit, or fold into (i)? (iii) The ζ-recurrence packaging: with `B_L(u) = log H_L(u)` analytic near 0 and `H_L' = B_L' H_L`, the recurrence `n h_n = Σ_{j=1}^n j b_j h_{n−j}` between the Taylor coefficients; what is the cleanest formal statement (in terms of `iteratedDeriv` of `H_L` and of `B_L = ((L−1)ℓ)u + log Γ(½−u) + L log Γ(1+u)`?) given that `Complex.log ∘ Γ` is analytic on `Re > 0` only after choosing the branch — would you instead use `H'/H` (analytic near 0 since `H(0) = 1 ≠ 0`) and define `b_n` as its Taylor coefficients shifted, so that the ζ-values enter only through the (unformalised) digamma expansion `ψ^{(n)}(1) = (−1)^{n+1} n! ζ(n+1)`, `ψ^{(n)}(½) = (−1)^{n+1} n! (2^{n+1} − 1) ζ(n+1)`? (iv) Depth five `E₅` closed modulo `λ₃, λ₄` as an instance (needs `Γ''''(½)`, `Γ''''(1)`: (i) + DCLXXIII); (v) cone `c₃`, NB ratio, blow-up. Give the exact Lean statement you would expose for (i)(α), including the hypotheses on `f, g` and the point.
3. Convention hazards (the `.re` of jet coefficients; `depthJetCoeff (L+1)` indexing by depth `L+1` with `hL : 1 ≤ L`; `iteratedDeriv` vs `deriv^[n]`).
Answer concisely with Lean-facing detail.
