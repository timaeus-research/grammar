# Consult #104 — closure of E4F and the next gated phase

You are Astra, our formalisation-strategy consultant for the Lean 4/Mathlib library `Grammar`
(timaeus-research/grammar, 650 modules, zero sorry/axiom, headline theorems axiom-clean). Your audit #103
accepted phase E and set the bounded gate E4F ("F1, preferably F2"). Here is what landed since, and the
questions for the next gate.

## 1. E4F as landed (main `cf32d46`)

* **F0** (CCCXLVIII `BlowUpCubeLeadingCoefficient`): documentation corrections made as you specified (ambient
  lattice vs support; ambient chart strata with the certificate localised to `[0,1]^d`; positive-part
  density representatives vs analytic coefficient tensors; the weight factor `u^{−(h₀+1)/2}`; "odd total
  prior–observable Taylor orders cancel between paired normal-sign pieces"). Germ bridge:
  `obsRep_piece_eventuallyEq` (on the open real domain), `normalDifferential_obsRep_piece`.
* **F1** (same file): ★ `coeff_eq_zero_of_isLittleO_powSum` (a finite power sum `∑_{i∈S} c_i N^{−e_i}`,
  `e` injective on `S`, `e_i ≤ A`, that is `o(N^{−A})` has all `c_i = 0` — the minimal exponent with a
  nonzero coefficient dominates), `mem_spectrumLe_zero_iff`, `exists_boundedContinuous_eq` (Tietze extension
  of `F·p` off the cube, clamped), ★ `cube_leading_remainder` (from `tendsto_cube_laplace`, hence `1 < d`),
  ★★ `cubeCoefficient_eq_zero_of_lt` (q on the declared spectrum, exponent `< d/2`), ★★
  `cubeCoefficient_leading : C(d/2, 0) = π^{d/2} F(0) p(0)` (`1 < d`), ★★ `cube_hasExpansion_from_leading`
  (wrapper over `d/2 ≤ α ≤ A`). The `d = 1` value of `C(1/2)` is not identified (the leading-measure theorem
  of the blow-up cover needs `d ≥ 2`; E4 itself is for all `d ≥ 1`).
* **F2 step 1** (CCCXLIX `BlowUpCubeSupport`): ★ `gCoeff_eq_zero_of_not_candidate` (the assembled canonical
  coefficients of any certificate vanish off the candidate exponents `(h_i+r+1)/(2k_i)` of every chart — from
  the existing kernel support `dataBoxCoeff_eq_zero_of_not_candidate`), `pieceCert_cores_h = d−1`, ★★
  `cubeCoefficient_eq_zero_of_not_support` (C(q) = 0 unless `q.exponent = (d+ℓ)/2`), ★★
  `cubeCoefficient_eq_zero_of_lt'` (vanishing below `d/2` for EVERY `d ≥ 1`, no leading-measure input), ★★
  `cube_hasExpansion_support`, ★★ `cubeCoefficient_eq_of_packets` (packet independence on the declared
  spectrum, by the power-sum uniqueness).
* **F2 steps 2–3 (parity) DEFERRED** after the time-box: the normal-sign flip `σ* = σ` except at `β` gives
  `φ_β(R_{σ*} z) = −φ_β(R_σ z)` and `a_{σ*}(t, r) = a_σ(t, −r)`, but relating the produced coefficient
  fields (`coeffCert.field` = `JW · fϕ` convolved with the observable jets, through `boxCoeff` /
  `familySpectralCoeff`) under `r ↦ −r` is a new bridge (the `(−1)^ℓ` action on the convolution of the prior
  coefficients and observable jets). We stopped, as you advised.
* **F3** (Gamma formula) deferred.

Paper-facing statement now available: for the quadratic phase on the cube and a signed analytic packet with
`p ≥ 0`, singleton chart certificates in the signed blow-up coordinates assemble into an all-order expansion of
the original integral, `∫_{[−1,1]^d} F p e^{−N|x|²} = ∑_{ℓ : (d+ℓ)/2 ≤ A} C((d+ℓ)/2) N^{−(d+ℓ)/2} + o(N^{−A})`,
with `C(d/2) = π^{d/2}F(0)p(0)` (`d ≥ 2`), coefficients chart-local and packet-independent.

## 2. Questions

1. **Closure.** Is E4F closed at your stopping point? Anything in the F1/F2 statements you would change
   (e.g. should `cube_hasExpansion_support` be the theorem the mirror cites, or the F1 wrapper)?
2. **Direction.** The user's standing directive is "proceed on the fundamentals of the certified resolved
   geometry" (phases 2, 3, hygiene, G, E, E4F done), with a later directive that once the paper's Lean side is
   finished we move to formalising the companion note `averaging_dataset.tex` (Section 4 fluctuations are
   already fully formalised; that note's remaining content is the dataset-averaging statistics). Options for
   the next gated phase, with your #103 ranking in mind:
   (i) the parity bridge (F2 steps 2–3) as its own bounded phase — cost estimate and the exact bridge lemma?
   (ii) programme J — an observable-independent coefficient functional (the paper's "expectation functional"
   `E_n[φ] = ∑ ⟨D^r φ, B⟩` as a distribution on the strata): what would the minimal faithful statement be,
   given canonicity CCCVIII (scalar coefficients intrinsic for each `φ`)?
   (iii) E5 — the general partial-active water-filling collar (recovers G for `A = univ`, `u = 1`, and E3
   for `|A| = 1`): a genuine library generalisation; how many units?
   (iv) the intrinsic gluing of the cube charts (a resolved geometry on the blow-up with `π ≠ id`): you said a
   new global object; is there a cheaper "a.e.-disjoint wedge cover as a ResolvedGeometry on the cube itself"
   with `π = id` and components the `d` wedge faces? (The strata would be the wedge interiors and their
   pairwise intersections — null sets — so the expansion would live on the wedges' faces glued along the
   diagonals.)
   (v) complexification from real analyticity (the hygiene non-claim: `HolomorphicBoxExtension` from
   `AnalyticOnNhd ℝ` data — Mathlib has `AnalyticAt` for ℝ but no automatic complex extension).
   (vi) stop the fundamentals here and start the companion note.
   Please rank with the paper in view, give the stopping point, and for your top choice give the unit plan
   with gates (as in #98/#100/#102).
3. **The mirror.** The annotated paper mirror (`grammar_lean.tex`) now has one sentence for the cube chart
   model with dots on `cube_integral_eq_sum_chart`, `cube_integral_eq_sum_pieces`,
   `hasCoordFreeExpansion_singleton`, `piece_hasCoordFreeExpansion`, `cube_hasExpansion`,
   `cubeCoefficient_eq_zero_of_not_support`, `cube_hasExpansion_support`, `cubeCoefficient_leading`,
   `cube_hasExpansion_from_leading`, `cubeCoefficient_eq_of_packets`, `normalDifferential_obsRep_piece`,
   and states the non-claims (gluing, parity, Gamma formula). Anything to add or remove?

## 3. Material — CCCXLVIII and CCCXLIX (full sources)

```lean
/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.BlowUpCubeExpansion
import Grammar.BlowUpCubeLeadingMeasure
import Grammar.ExpansionCongruence
import Mathlib.Topology.TietzeExtension

/-!
# Coefficient fidelity of the cube expansion: germs, vanishing below `d/2`, the leading coefficient
(CCCXLVIII; phase E4F, units F0–F1, consult #103)

Consult #103 accepted phase E and asked for a bounded coefficient-fidelity gate. This file lands
F0 and F1.

* **F0 — the observable germs** (`obsRep_piece_eventuallyEq`, `normalDifferential_obsRep_piece`):
  the observable representative of a piece agrees with `F ∘ φ_β ∘ R_σ` on a neighbourhood of every
  point of the open real domain (which contains the box, hence every base point), so the normal
  differentials entering the piece coefficients are those of `F ∘ φ_β ∘ R_σ`.
* **F1 — uniqueness against the leading term.** A finite power sum `∑_{α ∈ S} c_α N^{−α}`,
  `α ≤ A`, that is `o(N^{−A})` has all coefficients zero (`coeff_eq_zero_of_isLittleO_powSum`:
  the minimal exponent with a nonzero coefficient would dominate). The unconditional leading
  remainder `∫_{cube} F p e^{−N|x|²} − π^{d/2} F(0)p(0) N^{−d/2} = o(N^{−d/2})` follows from the
  leading-measure theorem CCXCV applied to a bounded continuous extension of `F p` off the cube
  (Tietze, then clamping). Comparing with `cube_hasExpansion` at cutoff `d/2`:
  ★★ `cubeCoefficient_eq_zero_of_lt` (every coefficient of exponent `< d/2` vanishes) and
  ★★ `cubeCoefficient_leading` (`C(d/2, 0) = π^{d/2} F(0) p(0)`); hence the paper-facing wrapper
  ★★ `cube_hasExpansion_from_leading`, whose sum runs only over `d/2 ≤ α ≤ A`.
  These use the leading-measure theorem for `1 < d` (the cube blow-up of CCLXXXIII–CCXCV); the
  one-dimensional case of the vanishing statements is NOT covered here (E4 itself holds for all
  `d ≥ 1`).

Not included (F2, deferred): the parity cancellation between paired normal-sign pieces (support
`α ∈ d/2 + ℕ`) and the directional-derivative formula for the coefficients.
-/

open MeasureTheory Set Filter Topology Asymptotics
open scoped BoundedContinuousFunction

namespace Grammar

/-! ### A finite power sum that is `o(N^{−A})` with all exponents `≤ A` vanishes -/

/-- ★ **Uniqueness of a finite power sum**: if `∑_{i ∈ S} c_i N^{−e_i} = o(N^{−A})` with `e`
injective on `S` and `e_i ≤ A`, every `c_i` vanishes. -/
theorem coeff_eq_zero_of_isLittleO_powSum {ι : Type*} {S : Finset ι} {e c : ι → ℝ}
    {A : ℝ} (he : Set.InjOn e S) (hS : ∀ i ∈ S, e i ≤ A)
    (h : (fun N : ℝ => ∑ i ∈ S, c i * N ^ (-(e i))) =o[atTop] fun N : ℝ => N ^ (-A)) :
    ∀ i ∈ S, c i = 0 := by
  classical
  by_contra hne
  push Not at hne
  obtain ⟨i₀, hi₀, hc₀⟩ := hne
  set T := S.filter fun i => c i ≠ 0 with hT
  have hi₀T : i₀ ∈ T := Finset.mem_filter.2 ⟨hi₀, hc₀⟩
  obtain ⟨j₀, hj₀T, hmin⟩ := Finset.exists_min_image T e ⟨i₀, hi₀T⟩
  have hj₀S : j₀ ∈ S := (Finset.mem_filter.1 hj₀T).1
  have hcj₀ : c j₀ ≠ 0 := (Finset.mem_filter.1 hj₀T).2
  -- the sum over `S` is the sum over `T`
  have hsumT : ∀ N : ℝ, ∑ i ∈ S, c i * N ^ (-(e i)) = ∑ i ∈ T, c i * N ^ (-(e i)) := fun N =>
    (Finset.sum_filter_of_ne fun i _ hi => left_ne_zero_of_mul hi).symm
  -- `g N = N^{e j₀} · (sum)` tends to `c j₀`
  set g : ℝ → ℝ := fun N => N ^ (e j₀) * ∑ i ∈ S, c i * N ^ (-(e i)) with hg
  have hg_eq : ∀ N : ℝ, 0 < N →
      g N = c j₀ + ∑ i ∈ T.erase j₀, c i * N ^ (-(e i - e j₀)) := fun N hN => by
    simp only [hg]
    rw [hsumT, ← Finset.add_sum_erase T _ hj₀T, mul_add, Finset.mul_sum]
    congr 1
    · rw [mul_left_comm, ← Real.rpow_add hN, add_neg_cancel, Real.rpow_zero, mul_one]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_left_comm, ← Real.rpow_add hN, neg_sub, sub_eq_add_neg, add_comm]
  have hlim : Tendsto g atTop (𝓝 (c j₀)) := by
    have h2 : Tendsto (fun N : ℝ => c j₀ + ∑ i ∈ T.erase j₀, c i * N ^ (-(e i - e j₀))) atTop
        (𝓝 (c j₀ + ∑ i ∈ T.erase j₀, c i * 0)) := by
      refine tendsto_const_nhds.add (tendsto_finsetSum _ fun i hi => ?_)
      have hiT : i ∈ T := Finset.mem_of_mem_erase hi
      have hne' : e i ≠ e j₀ := fun h' =>
        Finset.ne_of_mem_erase hi (he (Finset.mem_filter.1 hiT).1 hj₀S h')
      have hlt : 0 < e i - e j₀ := sub_pos.2 (lt_of_le_of_ne (hmin i hiT) hne'.symm)
      exact tendsto_const_nhds.mul (tendsto_rpow_neg_atTop hlt)
    simp only [mul_zero, Finset.sum_const_zero, add_zero] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with N hN
    exact (hg_eq N hN).symm
  -- but `g = o(N^{e j₀ − A}) = o(1)`, so `g → 0`
  have hlo : g =o[atTop] fun N : ℝ => N ^ (e j₀) * N ^ (-A) :=
    (isBigO_refl (fun N : ℝ => N ^ (e j₀)) atTop).mul_isLittleO h
  have hbig : (fun N : ℝ => N ^ (e j₀) * N ^ (-A)) =O[atTop] fun _ : ℝ => (1 : ℝ) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with N hN
    rw [← Real.rpow_add (by linarith), Real.norm_eq_abs, norm_one, mul_one,
      abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
    exact Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith [hS j₀ hj₀S])
  have hzero : Tendsto g atTop (𝓝 0) := (isLittleO_one_iff ℝ).1 (hlo.trans_isBigO hbig)
  exact hcj₀ (tendsto_nhds_unique hlim hzero)

/-! ### Membership in the log-free spectrum -/

theorem mem_spectrumLe_zero_iff {Q : ℕ} (hQ : 0 < Q) (A : ℝ) (q : PowerLogIndex) :
    q ∈ spectrumLe Q 0 A ↔
      (∃ m : ℕ, q.exponent = (m : ℝ) / Q) ∧ q.logDegree = 0 ∧ q.exponent ≤ A := by
  unfold spectrumLe spectrumBelow
  rw [Finset.mem_filter, Finset.mem_map]
  constructor
  · rintro ⟨⟨⟨μ, j⟩, hmem, rfl⟩, hle⟩
    obtain ⟨hμ, hj⟩ := Finset.mem_product.1 hmem
    obtain ⟨m, -, rfl⟩ := Finset.mem_image.1 hμ
    refine ⟨⟨m, rfl⟩, ?_, hle⟩
    have := Finset.mem_range.1 hj
    change j = 0
    omega
  · rintro ⟨⟨m, hm⟩, hj, hle⟩
    refine ⟨⟨(q.exponent, q.logDegree), Finset.mem_product.2 ⟨?_, ?_⟩, rfl⟩, hle⟩
    · rw [hm]
      refine mem_latticeBelow hQ ?_
      rw [← hm]
      unfold cutoffExponent
      exact lt_max_of_lt_left (by linarith)
    · rw [hj]
      exact Finset.mem_range.2 Nat.one_pos

theorem exponent_injOn_spectrumLe_zero {Q : ℕ} (hQ : 0 < Q) (A : ℝ) :
    Set.InjOn PowerLogIndex.exponent (spectrumLe Q 0 A : Set PowerLogIndex) := by
  intro q hq q' hq' h
  have h1 : q.logDegree = 0 := ((mem_spectrumLe_zero_iff hQ A q).1 hq).2.1
  have h2 : q'.logDegree = 0 := ((mem_spectrumLe_zero_iff hQ A q').1 hq').2.1
  cases q; cases q'
  simp only at h h1 h2
  subst h h1 h2
  rfl

theorem scale_of_logDegree_zero {q : PowerLogIndex} (hq : q.logDegree = 0) (n : ℝ) :
    q.scale n = n ^ (-q.exponent) := by
  unfold PowerLogIndex.scale
  rw [hq, pow_zero, mul_one]

namespace BlowUpCube

open WaterFilling SingletonChart NormalisedBox

variable {d : ℕ} (β : Fin d) {p F : (Fin d → ℝ) → ℝ}

/-! ### F0: the observable germs of the pieces -/

section Germs

variable (A : HolomorphicSignedBoxExtension 1 p F) (σ : CoordSign d)

/-- ★ **The observable representative has the germ of `F ∘ φ_β ∘ R_σ`** at every point of the open
real domain (which contains the box, hence every base point of the piece). -/
theorem obsRep_piece_eventuallyEq {z : Fin d → ℝ} (hz : z ∈ (pieceExt β A σ).realDomain) :
    (pieceExt β A σ).obsRep =ᶠ[𝓝 z] fun w => F (φ β (refl σ w)) := by
  filter_upwards [(pieceExt β A σ).isOpen_realDomain.mem_nhds hz] with w hw
  exact (pieceExt β A σ).obsRep_eq_of_mem hw

/-- ★ **The normal differentials entering the piece coefficients are those of `F ∘ φ_β ∘ R_σ`**
(at every stratum point of the real domain, in particular at every base point). -/
theorem normalDifferential_obsRep_piece (h₀ : ℕ) (I : Finset (SingletonChart.G β h₀).Component)
    (s : (SingletonChart.G β h₀).Stratum I)
    (hs : (SingletonChart.G β h₀).π s ∈ (pieceExt β A σ).realDomain) (r : ℕ) :
    (SingletonChart.N β h₀).normalDifferential (pieceExt β A σ).obsRep I s r =
      (SingletonChart.N β h₀).normalDifferential (fun w => F (φ β (refl σ w))) I s r :=
  (SingletonChart.N β h₀).normalDifferential_congr I s (obsRep_piece_eventuallyEq β A σ hs) r

theorem mem_realDomain_piece_of_mem_box {z : Fin d → ℝ} (hz : z ∈ piBox d (Icc 0 1)) :
    z ∈ (pieceExt β A σ).realDomain :=
  (pieceExt β A σ).box_subset_realDomain hz

end Germs

/-! ### F1: the leading remainder from the leading-measure theorem -/

section Leading

variable [NeZero d] (hd : 1 < d) (A : HolomorphicSignedBoxExtension 1 p F)

omit β [NeZero d] in
include A in
/-- A bounded continuous function on `ℝ^d` agreeing with `F · p` on the cube (Tietze extension of
the continuous restriction, clamped to the range of `F · p` on the cube). -/
theorem exists_boundedContinuous_eq :
    ∃ a : (Fin d → ℝ) →ᵇ ℝ, ∀ x ∈ cube d, a x = F x * p x := by
  have hcont : ContinuousOn (fun x => F x * p x) (cube d) :=
    A.continuousOn_obs.mul A.continuousOn_prior
  have hclosed : IsClosed (cube d) := isCompact_cube.isClosed
  obtain ⟨g, hg⟩ := ContinuousMap.exists_restrict_eq (Y := ℝ) hclosed
    ⟨fun x : cube d => F x.1 * p x.1, continuousOn_iff_continuous_domRestrict.1 hcont⟩
  have hg' : ∀ x ∈ cube d, g x = F x * p x := fun x hx => by
    have := congrArg (fun f : C(cube d, ℝ) => f ⟨x, hx⟩) hg
    simp only [ContinuousMap.restrict_apply] at this
    exact this
  obtain ⟨M, hM⟩ := isCompact_cube.exists_bound_of_continuousOn g.continuous.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by
    rw [mem_cube]
    intro j
    simp))
  let g' : C((Fin d → ℝ), ℝ) := ⟨fun x => max (-M) (min M (g x)),
    continuous_const.max (continuous_const.min g.continuous)⟩
  have hg'bd : ∀ x y, dist (g' x) (g' y) ≤ 2 * M := fun x y => by
    have h1 : -M ≤ g' x := le_max_left _ _
    have h2 : g' x ≤ M := max_le (by linarith) (min_le_left _ _)
    have h3 : -M ≤ g' y := le_max_left _ _
    have h4 : g' y ≤ M := max_le (by linarith) (min_le_left _ _)
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith
  refine ⟨BoundedContinuousFunction.mkOfBound g' (2 * M) hg'bd, fun x hx => ?_⟩
  rw [BoundedContinuousFunction.mkOfBound_coe]
  have hbx := hM x hx
  rw [Real.norm_eq_abs, abs_le] at hbx
  change max (-M) (min M (g x)) = F x * p x
  rw [min_eq_right hbx.2, max_eq_right hbx.1, hg' x hx]

omit β in
include hd A in
/-- ★ **The unconditional leading remainder**:
`∫_{cube} F p e^{−n|x|²} − π^{d/2} F(0) p(0) n^{−d/2} = o(n^{−d/2})` (from the leading-measure
theorem CCXCV for `1 < d`, applied to a bounded continuous extension of `F p`). -/
theorem cube_leading_remainder :
    (fun n : ℝ => (∫ x in cube d, F x * p x * Real.exp (-n * K x)) -
      Real.pi ^ (d / 2 : ℝ) * (F 0 * p 0) * n ^ (-(d / 2 : ℝ))) =o[atTop]
      fun n : ℝ => n ^ (-(d / 2 : ℝ)) := by
  obtain ⟨a, ha⟩ := exists_boundedContinuous_eq A
  have h0 : (0 : Fin d → ℝ) ∈ cube d := by
    rw [mem_cube]
    intro j
    simp
  have hint : ∀ n : ℝ, ∫ x in cube d, a x * Real.exp (-n * K x) =
      ∫ x in cube d, F x * p x * Real.exp (-n * K x) := fun n =>
    setIntegral_congr_fun isCompact_cube.isClosed.measurableSet fun x hx => by
      rw [ha x hx]
  have ht := tendsto_cube_laplace hd a
  rw [ha 0 h0] at ht
  have ht' : Tendsto (fun t : ℝ => (∫ x in cube d, a x * Real.exp (-t * K x)) /
      t ^ (-(d / 2 : ℝ)) - Real.pi ^ (d / 2 : ℝ) * (F 0 * p 0)) atTop (𝓝 0) :=
    tendsto_sub_nhds_zero_iff.2 ht
  have hlo : (fun t : ℝ => (∫ x in cube d, a x * Real.exp (-t * K x)) /
      t ^ (-(d / 2 : ℝ)) - Real.pi ^ (d / 2 : ℝ) * (F 0 * p 0)) =o[atTop]
      fun _ : ℝ => (1 : ℝ) := (isLittleO_one_iff ℝ).2 ht'
  have hmul := hlo.mul_isBigO (isBigO_refl (fun t : ℝ => t ^ (-(d / 2 : ℝ))) atTop)
  have heq : ∀ᶠ t in atTop, ((∫ x in cube d, a x * Real.exp (-t * K x)) / t ^ (-(d / 2 : ℝ)) -
      Real.pi ^ (d / 2 : ℝ) * (F 0 * p 0)) * t ^ (-(d / 2 : ℝ)) =
      (∫ x in cube d, F x * p x * Real.exp (-t * K x)) -
        Real.pi ^ (d / 2 : ℝ) * (F 0 * p 0) * t ^ (-(d / 2 : ℝ)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [hint, sub_mul, div_mul_cancel₀ _ (Real.rpow_pos_of_pos ht _).ne']
  exact hmul.congr' heq (Eventually.of_forall fun t => one_mul _)

end Leading

/-! ### F1: vanishing below `d/2` and the leading coefficient -/

/-- The leading index `(d/2, 0)`. -/
noncomputable def leadingIndex (d : ℕ) : PowerLogIndex := ⟨d / 2, 0⟩

omit β in
theorem leadingIndex_mem : leadingIndex d ∈ spectrumLe 2 0 (d / 2 : ℝ) :=
  (mem_spectrumLe_zero_iff two_pos _ _).2 ⟨⟨d, by simp [leadingIndex]⟩, rfl, le_rfl⟩

section Coefficients

variable [NeZero d] (hd : 1 < d) (A : HolomorphicSignedBoxExtension 1 p F)
  (hp0 : ∀ x ∈ piBox d (Icc (-1) 1), 0 ≤ p x)

omit β in
include hd hp0 in
open Classical in
/-- The comparison of the certificate expansion at cutoff `d/2` with the leading remainder: the
coefficients on `spectrumLe 2 0 (d/2)`, corrected by `π^{d/2} F(0)p(0)` at the leading index, all
vanish. -/
theorem corrected_coeff_eq_zero :
    ∀ q ∈ spectrumLe 2 0 (d / 2 : ℝ),
      cubeCoefficient A hp0 q -
        (if q = leadingIndex d then Real.pi ^ (d / 2 : ℝ) * (F 0 * p 0) else 0) = 0 := by
  classical
  have h1 := cube_hasExpansion A hp0 (d / 2 : ℝ)
  have h2 := cube_leading_remainder hd A
  have h3 := h2.sub h1
  refine coeff_eq_zero_of_isLittleO_powSum (e := PowerLogIndex.exponent)
    (exponent_injOn_spectrumLe_zero two_pos _)
    (fun q hq => ((mem_spectrumLe_zero_iff two_pos _ _).1 hq).2.2)
    (h3.congr_left fun n => ?_)
  simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
    if_pos (leadingIndex_mem (d := d))]
  have hsc : ∀ q ∈ spectrumLe 2 0 (d / 2 : ℝ), cubeCoefficient A hp0 q * q.scale n =
      cubeCoefficient A hp0 q * n ^ (-q.exponent) := fun q hq => by
    rw [scale_of_logDegree_zero ((mem_spectrumLe_zero_iff two_pos _ _).1 hq).2.1]
  rw [Finset.sum_congr rfl hsc]
  simp only [leadingIndex]
  ring

omit β in
include hd in
/-- ★★ **Vanishing below the leading exponent**: every coefficient of the cube expansion on the
declared spectrum with exponent `< d/2` is zero. -/
theorem cubeCoefficient_eq_zero_of_lt {B : ℝ} {q : PowerLogIndex} (hq : q ∈ spectrumLe 2 0 B)
    (hlt : q.exponent < d / 2) : cubeCoefficient A hp0 q = 0 := by
  obtain ⟨hm, hj, -⟩ := (mem_spectrumLe_zero_iff two_pos _ _).1 hq
  have hq' : q ∈ spectrumLe 2 0 (d / 2 : ℝ) :=
    (mem_spectrumLe_zero_iff two_pos _ _).2 ⟨hm, hj, hlt.le⟩
  have h := corrected_coeff_eq_zero hd A hp0 q hq'
  have hne : q ≠ leadingIndex d := fun h' => by
    rw [h'] at hlt
    exact lt_irrefl _ hlt
  rwa [if_neg hne, sub_zero] at h

omit β in
include hd in
/-- ★★ **The leading coefficient of the cube expansion is `π^{d/2} F(0) p(0)`** (CCXCV through
the certificates). -/
theorem cubeCoefficient_leading :
    cubeCoefficient A hp0 (leadingIndex d) = Real.pi ^ (d / 2 : ℝ) * (F 0 * p 0) := by
  have h := corrected_coeff_eq_zero hd A hp0 _ leadingIndex_mem
  rwa [if_pos rfl, sub_eq_zero] at h

omit β in
include hd in
/-- ★★ **The paper-facing expansion**: the sum runs only over the exponents `d/2 ≤ α ≤ A` of the
half-integer lattice (the coefficients below `d/2` vanish), with leading coefficient
`π^{d/2} F(0) p(0)`. -/
theorem cube_hasExpansion_from_leading (A' : ℝ) :
    (fun n : ℝ => (∫ x in cube d, F x * p x * Real.exp (-n * K x)) -
      ∑ q ∈ (spectrumLe 2 0 A').filter (fun q => (d / 2 : ℝ) ≤ q.exponent),
        cubeCoefficient A hp0 q * q.scale n) =o[atTop] fun n : ℝ => n ^ (-A') := by
  classical
  refine (cube_hasExpansion A hp0 A').congr_left fun n => ?_
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not (spectrumLe 2 0 A')
    (fun q => (d / 2 : ℝ) ≤ q.exponent),
    Finset.sum_eq_zero (s := (spectrumLe 2 0 A').filter fun q => ¬ (d / 2 : ℝ) ≤ q.exponent)
      fun q hq => ?_, add_zero]
  obtain ⟨hq, hlt⟩ := Finset.mem_filter.1 hq
  rw [cubeCoefficient_eq_zero_of_lt hd A hp0 hq (not_le.1 hlt), zero_mul]

end Coefficients

end BlowUpCube

end Grammar
```

```lean
/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.BlowUpCubeLeadingCoefficient
import Grammar.ChartExpansion
import Grammar.CutoffExpansionUniqueness

/-!
# The exponent support of the cube expansion (CCCXLIX; phase E4F, unit F2 step 1, consult #103)

Consult #103 §2: "singleton support — for normal weight `h₀` the piece coefficient can occur only at
`α = (h₀ + 1 + ℓ)/2`". The assembled canonical coefficients of a certificate vanish off the
candidate exponents of every chart (`gCoeff_eq_zero_of_not_candidate`, from the kernel support
`dataBoxCoeff_eq_zero_of_not_candidate`); the piece certificates of the cube have one normal
coordinate with `k = 1`, `h = d − 1` (`pieceCert_cores_h`), so their candidate exponents are
`(d + ℓ)/2`, `ℓ ∈ ℕ` (`not_candidateExp_piece`). Hence ★★ `pieceCoefficient_eq_zero_of_not_support`,
★★ `cubeCoefficient_eq_zero_of_not_support` and, for EVERY `d ≥ 1` and without the leading-measure
theorem, ★★ `cubeCoefficient_eq_zero_of_lt'` (vanishing below `d/2`) with the paper-facing wrapper
★★ `cube_hasExpansion_support` (the sum runs over `α = (d+ℓ)/2 ≤ A` only), and the packet
independence ★★ `cubeCoefficient_eq_of_packets` (two packets for the same `p, F` give the same
coefficients on the declared spectrum, by uniqueness). This closes the
one-dimensional gap of CCCXLVIII for the vanishing statements (the leading value `C(d/2)` still
uses `1 < d`).

Not included (F2 steps 2–3): the cancellation of odd total prior–observable Taylor orders between
paired normal-sign pieces (support `d/2 + ℕ`, i.e. `ℓ` even) — this needs the transformation of the
convolution of prior coefficients and observable jets under the normal-sign flip, a new bridge
(consult #103 §2), and is deferred.
-/

open MeasureTheory Set Filter Topology Asymptotics

namespace Grammar

/-! ### Assembled canonical coefficients vanish off the candidate exponents of every chart -/

section Assembled

variable {M : ℕ} {K : Fin M → Type*} [∀ I, TopologicalSpace (K I)] [∀ I, MeasurableSpace (K I)]
  {n : Fin M → ℕ} (ν : (I : Fin M) → Measure (K I))
  (h k : (I : Fin M) → Fin (n I + 1) → ℕ) (β : ℝ) (b : Fin M → ℝ) (x : JointData K n)

/-- ★ **Support of the assembled canonical coefficients**: `gCoeff μ j = 0` unless `μ` is a
candidate exponent `(h_i + r + 1)/(2k_i)` of some chart. -/
theorem gCoeff_eq_zero_of_not_candidate (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (hb : ∀ I, 0 < b I)
    {μ : ℝ} (hμ : ∀ I, ¬ candidateExp (h I) (k I) μ) (j : ℕ) : gCoeff ν h k β b x μ j = 0 := by
  unfold gCoeff
  refine Finset.sum_eq_zero fun I _ => ?_
  unfold tanCoeff
  simp [dataBoxCoeff_eq_zero_of_not_candidate (n I) (h I) (k I) (hk I) β hβ (hb I) _ (hμ I) j]

end Assembled

namespace BlowUpCube

open WaterFilling SingletonChart NormalisedBox

variable {d : ℕ} (β : Fin d) {p F : (Fin d → ℝ) → ℝ}

section Pieces

variable [NeZero d] (A : HolomorphicSignedBoxExtension 1 p F) (σ : CoordSign d)
  (hp0 : ∀ x ∈ piBox d (Icc (-1) 1), 0 ≤ p x)

omit [NeZero d] in
/-- The Jacobian order of the piece certificate's normal coordinate is `d − 1`. -/
theorem pieceCert_cores_h (J : Fin (pieceCert β A σ hp0).M)
    (i : Fin ((pieceCert β A σ hp0).n J + 1)) :
    (pieceCert β A σ hp0).cores.h J i = d - 1 := by
  change hS β (d - 1) (σI (Iβ β) i).1 = d - 1
  rw [Finset.mem_singleton.1 (σI (Iβ β) i).2]
  exact hS_self β (d - 1)

/-- The candidate exponents of a piece are `(d + ℓ)/2`. -/
theorem not_candidateExp_piece {μ : ℝ} (hμ : ∀ r : ℕ, μ ≠ ((d : ℝ) + r) / 2)
    (J : Fin (pieceCert β A σ hp0).M) :
    ¬ candidateExp ((pieceCert β A σ hp0).cores.h J) ((pieceCert β A σ hp0).cores.k J) μ := by
  rintro ⟨i, r, hi⟩
  rw [pieceCert_cores_h, pieceCert_cores_k] at hi
  refine hμ r ?_
  have h1 : 1 ≤ d := Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  rw [hi, Nat.cast_sub h1]
  push_cast
  ring

/-- ★★ **Support of a piece coefficient**: it vanishes unless the exponent is `(d + ℓ)/2`. -/
theorem pieceCoefficient_eq_zero_of_not_support {q : PowerLogIndex}
    (hμ : ∀ r : ℕ, q.exponent ≠ ((d : ℝ) + r) / 2) : pieceCoefficient β A σ hp0 q = 0 := by
  unfold pieceCoefficient
  rw [(pieceCoeff β A σ hp0).expansionCoefficient_eq_gCoeff]
  exact gCoeff_eq_zero_of_not_candidate _ _ _ _ _ _ (pieceCert β A σ hp0).cores.k_pos
    (pieceCert β A σ hp0).β_pos (pieceCert β A σ hp0).cores.b_pos
    (fun J => not_candidateExp_piece β A σ hp0 hμ J) _

end Pieces

section Cube

variable [NeZero d] (A : HolomorphicSignedBoxExtension 1 p F)
  (hp0 : ∀ x ∈ piBox d (Icc (-1) 1), 0 ≤ p x)

omit β in
/-- ★★ **Support of the cube expansion**: `C(q) = 0` unless `q.exponent = (d + ℓ)/2`. -/
theorem cubeCoefficient_eq_zero_of_not_support {q : PowerLogIndex}
    (hμ : ∀ r : ℕ, q.exponent ≠ ((d : ℝ) + r) / 2) : cubeCoefficient A hp0 q = 0 :=
  Finset.sum_eq_zero fun β _ => Finset.sum_eq_zero fun σ _ =>
    pieceCoefficient_eq_zero_of_not_support β A σ hp0 hμ

omit β in
/-- ★★ **Vanishing below `d/2` for every `d ≥ 1`** (structural: from the kernel support, with no
leading-measure input). -/
theorem cubeCoefficient_eq_zero_of_lt' {q : PowerLogIndex} (hlt : q.exponent < d / 2) :
    cubeCoefficient A hp0 q = 0 :=
  cubeCoefficient_eq_zero_of_not_support A hp0 fun r hr => by
    have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    linarith

omit β in
open Classical in
/-- ★★ **The paper-facing expansion on the support**: the sum runs over the exponents
`(d + ℓ)/2 ≤ A` only, for every `d ≥ 1`. -/
theorem cube_hasExpansion_support (A' : ℝ) :
    (fun n : ℝ => (∫ x in cube d, F x * p x * Real.exp (-n * K x)) -
      ∑ q ∈ (spectrumLe 2 0 A').filter (fun q => ∃ r : ℕ, q.exponent = ((d : ℝ) + r) / 2),
        cubeCoefficient A hp0 q * q.scale n) =o[atTop] fun n : ℝ => n ^ (-A') := by
  refine (cube_hasExpansion A hp0 A').congr_left fun n => ?_
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not (spectrumLe 2 0 A')
    (fun q => ∃ r : ℕ, q.exponent = ((d : ℝ) + r) / 2),
    Finset.sum_eq_zero (s := (spectrumLe 2 0 A').filter
      fun q => ¬ ∃ r : ℕ, q.exponent = ((d : ℝ) + r) / 2) fun q hq => ?_, add_zero]
  obtain ⟨-, hne⟩ := Finset.mem_filter.1 hq
  push Not at hne
  rw [cubeCoefficient_eq_zero_of_not_support A hp0 hne, zero_mul]

omit β in
/-- ★★ **Packet independence**: two analytic packets representing the same `p, F` give the same
cube coefficients on the declared spectrum (uniqueness of the finite power sum against the same
original integral). -/
theorem cubeCoefficient_eq_of_packets (A' : HolomorphicSignedBoxExtension 1 p F) {B : ℝ}
    {q : PowerLogIndex} (hq : q ∈ spectrumLe 2 0 B) :
    cubeCoefficient A hp0 q = cubeCoefficient A' hp0 q := by
  have h := (cube_hasExpansion A' hp0 B).sub (cube_hasExpansion A hp0 B)
  refine sub_eq_zero.1 (coeff_eq_zero_of_isLittleO_powSum (e := PowerLogIndex.exponent)
    (c := fun q => cubeCoefficient A hp0 q - cubeCoefficient A' hp0 q)
    (exponent_injOn_spectrumLe_zero two_pos _)
    (fun q hq => ((mem_spectrumLe_zero_iff two_pos _ _).1 hq).2.2) (h.congr_left fun n => ?_) q hq)
  have hsc : ∀ q ∈ spectrumLe 2 0 B,
      (cubeCoefficient A hp0 q - cubeCoefficient A' hp0 q) * n ^ (-q.exponent) =
        cubeCoefficient A hp0 q * q.scale n - cubeCoefficient A' hp0 q * q.scale n :=
    fun q hq => by
      rw [scale_of_logDegree_zero ((mem_spectrumLe_zero_iff two_pos _ _).1 hq).2.1]
      ring
  rw [Finset.sum_congr rfl hsc, Finset.sum_sub_distrib]
  ring

end Cube

end BlowUpCube

end Grammar
```
