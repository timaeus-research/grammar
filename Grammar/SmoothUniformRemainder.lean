/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothCoeffJetBound
import Grammar.SmoothPartitionDistribution

/-!
# The uniform remainder of the smooth expansion, engine level (C4s, part 1)

The engine's remainder theorem `smooth_expansion_at_depth_uniform` bounds the truncation error
of `∫_{(0,b]^d} G v^h e^{−Nβ v^{2k}}` by `K · N^{−L} (1 + log N)^{d−1}` for every amplitude `G`
with the rectangular derivative bound `RectBound G p b M`, but the constant `K` is produced after
`M` is fixed. Here the dependence on `M` is made explicit and LINEAR:

* `smooth_expansion_at_depth_linear`: `∃ K, ∀ M ≥ 0, ∀ G, RectBound G p b M → ∀ N ≥ 1,
  |∫ … − absSpectralSum (Qamb k) (d−1) (smoothCoeffAtDepth G …) L N| ≤ K·M·N^{−L}(1+log N)^{d−1}`
  (the face remainder constants `faceRem` are linear in `M`);
* `smooth_uniform_cutoff_linear`: the same for the CANONICAL coefficients `smoothCoeff` and an
  arbitrary real cutoff `L'`, with the rectangular bound taken at the depth
  `depthOf h k (max ⌈L'⌉₊ (L₀ h))`; the coefficients dropped between the cutoffs are controlled by
  the quantitative coefficient bound of CDXIII, which is also linear in `M`;
* `family_uniform_cutoff_linear`: integrated over a compact base with a finite measure.

These are the ingredients of the bridge-level uniform remainder (part 2): the constants depend
only on the engine data `(h, k, β, b, L')`, never on the amplitude.
-/

open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff Distributions

namespace Grammar

namespace SmoothEngine

variable {d : ℕ} {h k p : Fin d → ℕ} {β b : ℝ} {L : ℕ}

/-! ### Linearity of the face remainder constants -/

theorem faceRem_eq_mul (h k p : Fin d → ℕ) (b : ℝ) (L : ℕ) (M : ℝ) (J : Finset (Fin d)) :
    faceRem h k p b L M J = M * faceRem h k p b L 1 J := by
  unfold faceRem
  ring

/-- ★ **The uniform depth expansion, linear in the amplitude bound.** -/
theorem smooth_expansion_at_depth_linear (hk : ∀ i, 0 < k i) (hβ : 0 < β) (hb : 0 < b)
    (hL : 0 < L) (hp : ∀ i, p i + h i = 2 * k i * L) (hp0 : ∀ i, 0 < p i) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ M : ℝ, 0 ≤ M → ∀ G : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ G →
      RectBound G p b M → ∀ N : ℝ, 1 ≤ N →
      |smoothIntegral G h k β b N -
        absSpectralSum (Qamb k) (d - 1) (smoothCoeffAtDepth G h k p β b) L N| ≤
        K * M * (N ^ (-(L : ℝ)) * (1 + log N) ^ (d - 1)) := by
  choose C hC using fun (J : Finset (Fin d)) (e : Fin d → ℕ) =>
    face_two_regime k β b L J hk hβ hb hL e
  have hC0 : ∀ J e, 0 ≤ C J e := fun J e => nonneg_of_two_regime (hC J e)
  refine ⟨∑ x ∈ faceIndex p, faceW x.1 x.2 * (C x.1 (fun i => x.2 i + h i) *
    faceRem h k p b L 1 x.1), ?_, fun M hM0 G hG hM N hN => ?_⟩
  · exact Finset.sum_nonneg fun x _ => mul_nonneg (faceW_nonneg _ _)
      (mul_nonneg (hC0 _ _) (faceRem_nonneg h k p b L zero_le_one _))
  have hlog : 0 ≤ log N := log_nonneg hN
  unfold smoothIntegral
  rw [integral_eq_sum_faceIntegral hG b N, ← sum_faceExpansion_eq hk hβ hb N,
    ← Finset.sum_sub_distrib, Finset.sum_mul, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x hx => ?_)
  have hm : x.2 ∈ idxL p (lJ x.1) := (Finset.mem_sigma.1 hx).2
  have hb' := face_bound hG hk hb hp hp0 hM hm (hC x.1 (fun i => x.2 i + h i)) hN
  have hR0 := faceRem_nonneg h k p b L hM0 x.1
  have hpow : (1 + log N) ^ DJ x.1 ≤ (1 + log N) ^ (d - 1) :=
    pow_le_pow_right₀ (by linarith) (DJ_le x.1)
  have hW := faceW_nonneg x.1 x.2
  rw [← mul_sub, abs_mul, abs_of_nonneg hW]
  calc faceW x.1 x.2 * |faceIntegral G h k p β b x.1 x.2 N - faceExpansion G h k p β b L x.1 x.2 N|
      ≤ faceW x.1 x.2 * (C x.1 (fun i => x.2 i + h i) * faceRem h k p b L M x.1 *
          (1 + log N) ^ DJ x.1 * N ^ (-(L : ℝ))) := mul_le_mul_of_nonneg_left hb' hW
    _ ≤ faceW x.1 x.2 * (C x.1 (fun i => x.2 i + h i) * faceRem h k p b L M x.1 *
          (1 + log N) ^ (d - 1) * N ^ (-(L : ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow (mul_nonneg (hC0 _ _) hR0))
          (rpow_nonneg (by linarith) _)) hW
    _ = _ := by rw [faceRem_eq_mul]; ring

/-! ### Convergence of the coefficient integrals below the cutoff -/

theorem two_k_mul_lt_of_mem_latticeBelow (hk : ∀ i, 0 < k i) (hL : L₀ h ≤ L) {μ : ℝ}
    (hμ : μ ∈ latticeBelow (Qamb k) L) (i : Fin d) :
    2 * (k i : ℝ) * μ < depthOf h k L i + h i + 1 := by
  have hQ := Qamb_pos k hk
  have hμL : μ < L := lt_of_mem_latticeBelow hQ hμ
  have hpk : (depthOf h k L i : ℝ) + h i = 2 * k i * L := by
    exact_mod_cast depthOf_add hk hL i
  have hki : (0 : ℝ) < k i := by exact_mod_cast hk i
  nlinarith

/-- ★★ **The uniform cutoff expansion of the canonical coefficients, linear in the amplitude
bound**: for a real cutoff `L'` and the depth `depthOf h k (max ⌈L'⌉₊ (L₀ h))`. -/
theorem smooth_uniform_cutoff_linear (hk : ∀ i, 0 < k i) (hβ : 0 < β) (hb : 0 < b) (L' : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ M : ℝ, 0 ≤ M → ∀ G : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ G →
      RectBound G (depthOf h k (max ⌈L'⌉₊ (L₀ h))) b M → ∀ N : ℝ, 1 ≤ N →
      |smoothIntegral G h k β b N -
        absSpectralSum (Qamb k) (d - 1) (smoothCoeff G h k β b) L' N| ≤
        K * M * (N ^ (-L') * (1 + log N) ^ (d - 1)) := by
  have hQ := Qamb_pos k hk
  set L : ℕ := max ⌈L'⌉₊ (L₀ h) with hLdef
  have hL : L₀ h ≤ L := le_max_right _ _
  have hL0 : 0 < L := lt_of_lt_of_le (by unfold L₀; omega) hL
  have hLL : L' ≤ (L : ℝ) := by
    have h1 := Nat.le_ceil L'
    have h2 : ((⌈L'⌉₊ : ℕ) : ℝ) ≤ ((max ⌈L'⌉₊ (L₀ h) : ℕ) : ℝ) := by exact_mod_cast le_max_left _ _
    linarith
  obtain ⟨K₁, hK₁0, hK₁⟩ :=
    smooth_expansion_at_depth_linear (h := h) hk hβ hb hL0 (depthOf_add hk hL) (depthOf_pos hk hL)
  set B : ℝ := ∑ μ ∈ latticeBelow (Qamb k) L, ∑ j ∈ range (d - 1 + 1),
    coeffBoundConstant h k (depthOf h k L) β b μ j with hBdef
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun μ _ => Finset.sum_nonneg fun j _ =>
    coeffBoundConstant_nonneg _ _ _ _ _ _ _
  refine ⟨K₁ + B, add_nonneg hK₁0 hB0, fun M hM0 G hG hGM N hN => ?_⟩
  have hlow := bound_lower_cutoff hQ hLL hN (hK₁ M hM0 G hG hGM N hN)
  have hcoef : ∑ μ ∈ latticeBelow (Qamb k) L, ∑ j ∈ range (d - 1 + 1),
      |smoothCoeffAtDepth G h k (depthOf h k L) β b μ j| ≤ B * M := by
    rw [hBdef, Finset.sum_mul]
    refine Finset.sum_le_sum fun μ hμ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    exact abs_smoothCoeffAtDepth_le hG hb (depthOf_pos hk hL)
      (two_k_mul_lt_of_mem_latticeBelow hk hL hμ) hGM j
  have hcan : absSpectralSum (Qamb k) (d - 1) (smoothCoeff G h k β b) L' N =
      absSpectralSum (Qamb k) (d - 1) (smoothCoeffAtDepth G h k (depthOf h k L) β b) L' N := by
    unfold absSpectralSum
    refine Finset.sum_congr rfl fun μ hμ => ?_
    congr 1
    refine Finset.sum_congr rfl fun q hq => ?_
    have hμL : μ ∈ latticeBelow (Qamb k) L := latticeBelow_mono hQ hLL hμ
    rw [smoothCoeff_eq hG hk hβ hb hL hμL (Nat.lt_succ_iff.1 (Finset.mem_range.1 hq))]
  rw [hcan]
  have hω : 0 ≤ N ^ (-L') * (1 + log N) ^ (d - 1) :=
    mul_nonneg (rpow_nonneg (by linarith) _) (pow_nonneg (by linarith [log_nonneg hN]) _)
  refine hlow.trans ?_
  have : K₁ * M + ∑ μ ∈ latticeBelow (Qamb k) L, ∑ j ∈ range (d - 1 + 1),
      |smoothCoeffAtDepth G h k (depthOf h k L) β b μ j| ≤ (K₁ + B) * M := by nlinarith
  exact mul_le_mul_of_nonneg_right this hω

/-! ### The family level -/

variable {S : Type*} [TopologicalSpace S] [CompactSpace S] [FirstCountableTopology S]
  [MeasurableSpace S] [OpensMeasurableSpace S]

/-- ★★ **The integrated uniform cutoff expansion, linear in the amplitude bound.** -/
theorem family_uniform_cutoff_linear (hk : ∀ i, 0 < k i) (hβ : 0 < β) (hb : 0 < b) (L' : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ν : Measure S) [IsFiniteMeasure ν] (F : SmoothAmplitudeFamily S d b)
      (M : ℝ), 0 ≤ M → (∀ s, RectBound (F s) (depthOf h k (max ⌈L'⌉₊ (L₀ h))) b M) →
      ∀ N : ℝ, 1 ≤ N →
      |familyIntegral ν F h k (fun _ => β) b N -
        absSpectralSum (Qamb k) (d - 1) (familyCoeff ν F h k (fun _ => β) b) L' N| ≤
        K * M * ν.real univ * (N ^ (-L') * (1 + log N) ^ (d - 1)) := by
  obtain ⟨K, hK0, hK⟩ := smooth_uniform_cutoff_linear (h := h) hk hβ hb L'
  refine ⟨K, hK0, fun ν _ F M hM0 hFM N hN => ?_⟩
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hc : ∀ μ q, Integrable (fun s => smoothCoeff (F s) h k β b μ q) ν := fun μ q =>
    integrable_of_continuous_compactSpace ν (F.continuous_smoothCoeff hk hb μ q)
  have hZ : Integrable (fun s => smoothIntegral (F s) h k β b N) ν :=
    integrable_of_continuous_compactSpace ν (F.continuous_smoothIntegral hβ.le hN0)
  unfold familyIntegral familyCoeff
  rw [absSpectralSum_integral ν hc, ← integral_sub hZ (integrable_absSpectralSum ν hc L' N),
    ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (C := K * M * (N ^ (-L') * (1 + log N) ^ (d - 1)))
    (ae_of_all _ fun s => ?_)).trans (le_of_eq ?_)
  · rw [Real.norm_eq_abs]
    exact hK M hM0 (F s) (F.smooth s) (hFM s) N hN
  · ring

/-! ### Reindexing of spectral sums -/

theorem absSpectralSum_eq_of_dvd {Q Q' D : ℕ} (hQ : 0 < Q) (hQ' : 0 < Q') (hQQ : Q ∣ Q')
    {c : ℝ → ℕ → ℝ} (hc : ∀ μ, (∀ m : ℕ, μ ≠ (m : ℝ) / Q) → ∀ j, c μ j = 0) (L N : ℝ) :
    absSpectralSum Q' D c L N = absSpectralSum Q D c L N := by
  unfold absSpectralSum
  symm
  refine Finset.sum_subset (latticeBelow_subset_of_dvd hQ hQ' hQQ L) fun μ hμ' hμ => ?_
  have hzero : ∀ j, c μ j = 0 := by
    refine hc μ fun m hm => hμ ?_
    exact (mem_latticeBelow_iff hQ).2 ⟨⟨m, hm⟩, lt_of_mem_latticeBelow hQ' hμ'⟩
  simp [hzero]

theorem absSpectralSum_eq_of_le {Q D D' : ℕ} (hD : D ≤ D') {c : ℝ → ℕ → ℝ}
    (hc : ∀ μ j, D < j → c μ j = 0) (L N : ℝ) :
    absSpectralSum Q D' c L N = absSpectralSum Q D c L N := by
  unfold absSpectralSum
  refine Finset.sum_congr rfl fun μ _ => ?_
  congr 1
  symm
  refine Finset.sum_subset (fun j hj => Finset.mem_range.2
    (lt_of_lt_of_le (Finset.mem_range.1 hj) (by omega))) fun j _ hj => ?_
  have hDj : D < j := by
    by_contra hcon
    exact hj (Finset.mem_range.2 (by omega))
  simp [hc μ j hDj]

theorem absSpectralSum_finset_sum {ι : Type*} (s : Finset ι) (Q D : ℕ) (c : ι → ℝ → ℕ → ℝ)
    (L N : ℝ) :
    absSpectralSum Q D (fun μ q => ∑ i ∈ s, c i μ q) L N =
      ∑ i ∈ s, absSpectralSum Q D (c i) L N := by
  unfold absSpectralSum
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]

/-! ### The exponential tail against a power-log profile -/

theorem exp_neg_mul_le_rpow_profile {δ : ℝ} (hδ : 0 < δ) (L' : ℝ) (D : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, 1 ≤ N →
      exp (-δ * N) ≤ C * (N ^ (-L') * (1 + log N) ^ D) := by
  set n : ℕ := ⌈L'⌉₊ with hn
  refine ⟨(n.factorial : ℝ) / δ ^ n, by positivity, fun N hN => ?_⟩
  have hN0 : 0 < N := by linarith
  have hlog : 1 ≤ 1 + log N := by linarith [log_nonneg hN]
  have hpow1 : 1 ≤ (1 + log N) ^ D := one_le_pow₀ hlog
  -- `N^{L'} ≤ N^n`
  have h1 : N ^ L' ≤ N ^ (n : ℝ) := rpow_le_rpow_of_exponent_le hN (Nat.le_ceil L')
  rw [rpow_natCast] at h1
  -- `(δN)^n / n! ≤ exp(δN)`, so `exp(−δN) N^n ≤ n!/δ^n`
  have h2 := pow_div_factorial_le_exp (δ * N) (mul_nonneg hδ.le hN0.le) n
  have h3 : exp (-δ * N) * N ^ n ≤ (n.factorial : ℝ) / δ ^ n := by
    have hδn : 0 < δ ^ n := pow_pos hδ n
    have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    have hexp := exp_pos (δ * N)
    have hNn : N ^ n = (δ * N) ^ n / δ ^ n := by rw [mul_pow]; field_simp
    have h2' : (δ * N) ^ n ≤ (n.factorial : ℝ) * exp (δ * N) := by
      rw [div_le_iff₀ hfac] at h2
      linarith
    rw [hNn, neg_mul, exp_neg, div_eq_mul_inv, div_eq_mul_inv]
    calc (exp (δ * N))⁻¹ * ((δ * N) ^ n * (δ ^ n)⁻¹)
        ≤ (exp (δ * N))⁻¹ * ((n.factorial : ℝ) * exp (δ * N) * (δ ^ n)⁻¹) := by gcongr
      _ = (n.factorial : ℝ) * (δ ^ n)⁻¹ := by field_simp
  have hL' : N ^ L' * N ^ (-L') = 1 := by
    rw [← rpow_add hN0, add_neg_cancel, rpow_zero]
  have hexp0 : 0 ≤ exp (-δ * N) := (exp_pos _).le
  have hrpow0 : 0 ≤ N ^ (-L') := rpow_nonneg hN0.le _
  calc exp (-δ * N) = exp (-δ * N) * N ^ L' * N ^ (-L') := by rw [mul_assoc, hL', mul_one]
    _ ≤ exp (-δ * N) * N ^ n * N ^ (-L') := by gcongr
    _ ≤ (n.factorial : ℝ) / δ ^ n * N ^ (-L') := mul_le_mul_of_nonneg_right h3 hrpow0
    _ ≤ (n.factorial : ℝ) / δ ^ n * (N ^ (-L') * (1 + log N) ^ D) := by
        rw [← mul_assoc]
        exact le_mul_of_one_le_right (by positivity) hpow1

/-! ### The bridge: piece data at a cutoff -/

namespace BridgeInputs

open Monomialize.VolumeScaling

variable (X : BridgeInputs d)

/-- The engine depth of a piece at the real cutoff `L'`. -/
noncomputable def remDepth (P : X.PIdx) (L' : ℝ) : Fin (X.da P) → ℕ :=
  depthOf (X.hA P) (X.kA P) (max ⌈L'⌉₊ (L₀ (X.hA P)))

/-- ★ **The remainder order** at the cutoff `L'`: the maximum over the pieces of the total depth. -/
noncomputable def remOrder (L' : ℝ) : ℕ := Finset.univ.sup fun P : X.PIdx => ∑ j, X.remDepth P L' j

theorem sum_remDepth_le_remOrder (P : X.PIdx) (L' : ℝ) :
    ∑ j, X.remDepth P L' j ≤ X.remOrder L' :=
  Finset.le_sup (f := fun P : X.PIdx => ∑ j, X.remDepth P L' j) (Finset.mem_univ P)

theorem exists_chartConstL (i : X.T.ι) (L' : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ f → ∀ M : ℝ, 0 ≤ M →
      (∀ r ≤ X.remOrder L', ∀ y ∈ X.T.ψ i '' centeredBox d (X.T.a i),
        ‖iteratedFDeriv ℝ r f y‖ ≤ M) →
      ∀ r ≤ X.remOrder L', ∀ u ∈ centeredBox d (X.T.a i),
        ‖iteratedFDeriv ℝ r (f ∘ X.T.ψ i) u‖ ≤ C * M :=
  exists_chart_jet_bound_centeredBox (X.T.V_open i) (X.T.box_subset_V i) (X.contDiffOn_ψ i)
    (X.remOrder L')

/-- The chain-rule constant of a chart at the remainder order. -/
noncomputable def chartConstL (i : X.T.ι) (L' : ℝ) : ℝ :=
  Classical.choose (X.exists_chartConstL i L')

theorem chartConstL_nonneg (i : X.T.ι) (L' : ℝ) : 0 ≤ X.chartConstL i L' :=
  (Classical.choose_spec (X.exists_chartConstL i L')).1

theorem chartConstL_spec (i : X.T.ι) (L' : ℝ) {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    {M : ℝ} (hM : 0 ≤ M) (hJ : JetBound (X.remOrder L') X.coreImage f M) :
    ∀ r ≤ X.remOrder L', ∀ u ∈ centeredBox d (X.T.a i),
      ‖iteratedFDeriv ℝ r (f ∘ X.T.ψ i) u‖ ≤ X.chartConstL i L' * M :=
  (Classical.choose_spec (X.exists_chartConstL i L')).2 f hf M hM
    fun r hr y hy => hJ r hr y (X.image_box_subset_coreImage i hy)

/-- The rectangular bound of the observable family at the remainder depth. -/
theorem rectBound_obsfam_rem (P : X.PIdx) (L' : ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hJ : JetBound (X.remOrder L') X.coreImage X.obs M) (s : Base (X.act P.1) (X.T.a P.1)) :
    RectBound (X.obsfam P s) (X.remDepth P L') (X.T.a P.1) (X.chartConstL P.1 L' * M) := by
  intro m hm v hv
  have hvbox : ∀ j, v j ∈ Icc 0 (X.T.a P.1) := hv
  have hu : X.Tm P s v ∈ centeredBox d (X.T.a P.1) := X.Tm_mem_box P s hvbox
  have huV : X.Tm P s v ∈ X.T.V P.1 := X.T.box_subset_V P.1 hu
  change |pdMulti m (List.finRange (X.da P))
    (fun v => X.obsExt P.1 (affineMap (X.eqv P) P.2 (X.sc P s) v)) v| ≤ _
  rw [abs_pdMulti_comp_affineMap_finRange (X.eqv P) P.2 (X.sc P s) (X.contDiff_obsExt P.1) m v]
  change |pdMulti (extendIdx (X.eqv P) m) (List.finRange d) (X.obsExt P.1) (X.Tm P s v)| ≤ _
  have hψ : ContDiffOn ℝ ∞ (X.obs ∘ X.T.ψ P.1) (X.T.V P.1) :=
    X.obs_smooth.comp_contDiffOn (X.contDiffOn_ψ P.1)
  rw [pdMulti_eqOn_centeredBox (X.T.V_open P.1) (X.T.a_pos P.1) (X.T.box_subset_V P.1)
    (X.contDiff_obsExt P.1).contDiffOn hψ (fun u hu => X.obsExt_eq P.1 hu) _ _ hu]
  refine (abs_pdMulti_finRange_le_norm_iteratedFDeriv_of_mem (X.T.V_open P.1) hψ _ huV).trans ?_
  refine X.chartConstL_spec P.1 L' X.obs_smooth hM hJ _ ?_ _ hu
  rw [sum_extendIdx]
  exact (Finset.sum_le_sum fun j _ => hm j).trans (X.sum_remDepth_le_remOrder P L')

theorem exists_densityBoundL (P : X.PIdx) (L' : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s, RectBound (X.ρfam P s) (X.remDepth P L') (X.T.a P.1) M :=
  (X.ρfam P).exists_uniform_rect_bound _

/-- The uniform rectangular bound of the density family at the remainder depth. -/
noncomputable def densityBoundL (P : X.PIdx) (L' : ℝ) : ℝ :=
  Classical.choose (X.exists_densityBoundL P L')

theorem densityBoundL_nonneg (P : X.PIdx) (L' : ℝ) : 0 ≤ X.densityBoundL P L' :=
  (Classical.choose_spec (X.exists_densityBoundL P L')).1

theorem rectBound_ρfam_rem (P : X.PIdx) (L' : ℝ) (s : Base (X.act P.1) (X.T.a P.1)) :
    RectBound (X.ρfam P s) (X.remDepth P L') (X.T.a P.1) (X.densityBoundL P L') :=
  (Classical.choose_spec (X.exists_densityBoundL P L')).2 s

/-- The rectangular bound of the product amplitude family at the remainder depth. -/
theorem rectBound_mul_rem (P : X.PIdx) (L' : ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hJ : JetBound (X.remOrder L') X.coreImage X.obs M) (s : Base (X.act P.1) (X.T.a P.1)) :
    RectBound (((X.ρfam P).mul (X.obsfam P)) s) (X.remDepth P L') (X.T.a P.1)
      (2 ^ (∑ j, X.remDepth P L' j) * X.densityBoundL P L' * (X.chartConstL P.1 L' * M)) := by
  rw [SmoothAmplitudeFamily.mul_apply]
  exact RectBound.mul ((X.ρfam P).smooth s) ((X.obsfam P).smooth s) (X.T.a_pos P.1).le
    (X.rectBound_ρfam_rem P L' s) (X.rectBound_obsfam_rem P L' hM hJ s)

/-! ### The piece integrals and coefficients through the product family -/

theorem chartInt_eq_mul (I : Fin (Fintype.card X.PIdx)) (N : ℝ) :
    X.decomp.chartInt I N =
      familyIntegral (baseMeasure (X.act (X.en I).1) (X.T.a (X.en I).1) (X.T.h (X.en I).1))
        ((X.ρfam (X.en I)).mul (X.obsfam (X.en I))) (X.hA (X.en I)) (X.kA (X.en I))
        (fun _ => X.T.phaseConst (X.en I).1) (X.T.a (X.en I).1) N := by
  change familyIntegral (baseMeasure (X.act (X.en I).1) (X.T.a (X.en I).1) (X.T.h (X.en I).1))
    (X.amp (X.en I)) (X.hA (X.en I)) (X.kA (X.en I)) (fun _ => X.T.phaseConst (X.en I).1)
    (X.T.a (X.en I).1) N = _
  unfold familyIntegral
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  unfold smoothIntegral
  refine setIntegral_congr_fun (measurableSet_box _) fun v hv => ?_
  rw [SmoothAmplitudeFamily.mul_apply,
    X.amp_eq_mul (X.en I) s fun j => Ioc_subset_Icc_self (hv j (Set.mem_univ j))]

theorem familyCoeff_amp_eq_mul (P : X.PIdx) (μ : ℝ) (q : ℕ) :
    familyCoeff (baseMeasure (X.act P.1) (X.T.a P.1) (X.T.h P.1)) (X.amp P) (X.hA P) (X.kA P)
        (fun _ => X.T.phaseConst P.1) (X.T.a P.1) μ q =
      familyCoeff (baseMeasure (X.act P.1) (X.T.a P.1) (X.T.h P.1))
        ((X.ρfam P).mul (X.obsfam P)) (X.hA P) (X.kA P) (fun _ => X.T.phaseConst P.1)
        (X.T.a P.1) μ q := by
  unfold familyCoeff
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  refine smoothCoeff_congr_box ((X.amp P).smooth s) (((X.ρfam P).mul (X.obsfam P)).smooth s)
    (X.kA_pos P) (X.T.phaseConst_pos P.1) (X.T.a_pos P.1) (fun v hv => ?_) μ q
  rw [SmoothAmplitudeFamily.mul_apply]
  exact X.amp_eq_mul P s fun j => Ioc_subset_Icc_self (hv j (Set.mem_univ j))

/-! ### The tail -/

instance : IsFiniteMeasure X.T.tail := isFiniteMeasure_of_le X.priorMeasure X.decomp.tail_le

theorem ae_tail_mem_tsupport_prior : ∀ᵐ y ∂X.T.tail, y ∈ tsupport X.prior :=
  (Measure.absolutelyContinuous_of_le X.decomp.tail_le).ae_le X.ae_mem_tsupport_prior

/-- The tail integral is bounded by the supremum of the observable on the support of the prior. -/
theorem abs_tailInt_le {M : ℝ} (hMf : ∀ y ∈ tsupport X.prior, |X.obs y| ≤ M) {N : ℝ}
    (hN : 0 ≤ N) : |X.decomp.tailInt N| ≤ M * X.T.tail.real univ * exp (-X.T.δ * N) := by
  refine (X.decomp.tailInt_bound hN).trans ?_
  have hint : Integrable (fun z => |X.obs z|) X.T.tail :=
    (X.D.obs_integrable.mono_measure X.decomp.tail_le).norm
  have hle : ∫ z, |X.obs z| ∂X.T.tail ≤ M * X.T.tail.real univ := by
    calc ∫ z, |X.obs z| ∂X.T.tail ≤ ∫ _, M ∂X.T.tail :=
          integral_mono_ae hint (integrable_const M)
            (X.ae_tail_mem_tsupport_prior.mono fun y hy => hMf y hy)
      _ = M * X.T.tail.real univ := by rw [integral_const, smul_eq_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right hle (exp_pos _).le

/-! ### The uniform remainder -/

/-- The remainder constant of the bridge at the cutoff `L'`: pieces and tail. -/
noncomputable def remConst (L' : ℝ) (Kp : Fin (Fintype.card X.PIdx) → ℝ) (Ct : ℝ) : ℝ :=
  ∑ I, Kp I * (2 ^ (∑ j, X.remDepth (X.en I) L' j) * X.densityBoundL (X.en I) L' *
    X.chartConstL (X.en I).1 L') *
      (baseMeasure (X.act (X.en I).1) (X.T.a (X.en I).1) (X.T.h (X.en I).1)).real univ +
  X.T.tail.real univ * Ct

/-- The uniform remainder for the bridge's own observable, with the piece and tail constants
supplied. -/
theorem uniform_remainder_cutoff_aux (L' : ℝ) (Kp : Fin (Fintype.card X.PIdx) → ℝ)
    (hKp0 : ∀ I, 0 ≤ Kp I)
    (hKp : ∀ I : Fin (Fintype.card X.PIdx),
      ∀ (ν : Measure (Base (X.act (X.en I).1) (X.T.a (X.en I).1))) [IsFiniteMeasure ν]
        (F : SmoothAmplitudeFamily (Base (X.act (X.en I).1) (X.T.a (X.en I).1)) (X.da (X.en I))
          (X.T.a (X.en I).1)) (M : ℝ), 0 ≤ M →
        (∀ s, RectBound (F s) (X.remDepth (X.en I) L') (X.T.a (X.en I).1) M) → ∀ N : ℝ, 1 ≤ N →
        |familyIntegral ν F (X.hA (X.en I)) (X.kA (X.en I)) (fun _ => X.T.phaseConst (X.en I).1)
            (X.T.a (X.en I).1) N -
          absSpectralSum (Qamb (X.kA (X.en I))) (X.da (X.en I) - 1)
            (familyCoeff ν F (X.hA (X.en I)) (X.kA (X.en I)) (fun _ => X.T.phaseConst (X.en I).1)
              (X.T.a (X.en I).1)) L' N| ≤
          Kp I * M * ν.real univ * (N ^ (-L') * (1 + log N) ^ (X.da (X.en I) - 1)))
    (Ct : ℝ) (hCt : ∀ N : ℝ, 1 ≤ N →
      exp (-X.T.δ * N) ≤ Ct * (N ^ (-L') * (1 + log N) ^ X.decomp.commonD))
    {M : ℝ} (hM : 0 ≤ M)
    (hJ : JetBound (X.remOrder L') (X.coreImage ∪ tsupport X.prior) X.obs M) {N : ℝ}
    (hN : 1 ≤ N) :
    |X.D.Z N - absSpectralSum X.decomp.commonQ X.decomp.commonD X.decomp.coeff L' N| ≤
      X.remConst L' Kp Ct * M * (N ^ (-L') * (1 + log N) ^ X.decomp.commonD) := by
  classical
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hlog : 0 ≤ log N := log_nonneg hN
  have hJc : JetBound (X.remOrder L') X.coreImage X.obs M :=
    hJ.mono le_rfl subset_union_left le_rfl
  have hMf : ∀ y ∈ tsupport X.prior, |X.obs y| ≤ M :=
    jetBound_zero_of_le (hJ.mono (Nat.zero_le _) subset_union_right le_rfl)
  rw [X.decomp.Z_eq hN0]
  -- the coefficient sum, chart by chart, through the product families
  have hcoef : absSpectralSum X.decomp.commonQ X.decomp.commonD X.decomp.coeff L' N =
      ∑ I, absSpectralSum (Qamb (X.kA (X.en I))) (X.da (X.en I) - 1)
        (familyCoeff (baseMeasure (X.act (X.en I).1) (X.T.a (X.en I).1) (X.T.h (X.en I).1))
          ((X.ρfam (X.en I)).mul (X.obsfam (X.en I))) (X.hA (X.en I))
          (X.kA (X.en I)) (fun _ => X.T.phaseConst (X.en I).1) (X.T.a (X.en I).1)) L' N := by
    change absSpectralSum X.decomp.commonQ X.decomp.commonD (fun μ q => ∑ I,
      familyCoeff (baseMeasure (X.act (X.en I).1) (X.T.a (X.en I).1) (X.T.h (X.en I).1))
        (X.amp (X.en I)) (X.hA (X.en I)) (X.kA (X.en I))
        (fun _ => X.T.phaseConst (X.en I).1) (X.T.a (X.en I).1) μ q) L' N = _
    rw [absSpectralSum_finset_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    have hlat : ∀ μ, (∀ m : ℕ, μ ≠ (m : ℝ) / Qamb (X.kA (X.en I))) → ∀ j,
        familyCoeff (baseMeasure (X.act (X.en I).1) (X.T.a (X.en I).1) (X.T.h (X.en I).1))
          (X.amp (X.en I)) (X.hA (X.en I)) (X.kA (X.en I))
          (fun _ => X.T.phaseConst (X.en I).1) (X.T.a (X.en I).1) μ j = 0 := fun μ hμ j =>
      (X.decomp.chart I).familyCoeff_eq_zero_of_not_lattice hμ j
    have hdeg : ∀ μ j, X.da (X.en I) - 1 < j →
        familyCoeff (baseMeasure (X.act (X.en I).1) (X.T.a (X.en I).1) (X.T.h (X.en I).1))
          (X.amp (X.en I)) (X.hA (X.en I)) (X.kA (X.en I))
          (fun _ => X.T.phaseConst (X.en I).1) (X.T.a (X.en I).1) μ j = 0 := fun μ j hj =>
      (X.decomp.chart I).familyCoeff_eq_zero_of_degree_gt hj
    rw [absSpectralSum_eq_of_dvd (Qamb_pos _ (X.kA_pos (X.en I))) X.decomp.commonQ_pos
      (X.decomp.Qamb_dvd_commonQ I) hlat, absSpectralSum_eq_of_le (X.decomp.le_commonD I) hdeg]
    congr 1
    funext μ q
    exact X.familyCoeff_amp_eq_mul (X.en I) μ q
  rw [hcoef, add_sub_right_comm, ← Finset.sum_sub_distrib]
  refine (abs_add_le _ _).trans ?_
  unfold remConst
  rw [add_mul, add_mul]
  refine add_le_add ?_ ?_
  · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun I _ => ?_
    rw [X.chartInt_eq_mul I N]
    have hM' : 0 ≤ 2 ^ (∑ j, X.remDepth (X.en I) L' j) * X.densityBoundL (X.en I) L' *
        (X.chartConstL (X.en I).1 L' * M) :=
      mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) (X.densityBoundL_nonneg _ _))
        (mul_nonneg (X.chartConstL_nonneg _ _) hM)
    have hbound := hKp I (baseMeasure (X.act (X.en I).1) (X.T.a (X.en I).1) (X.T.h (X.en I).1))
      ((X.ρfam (X.en I)).mul (X.obsfam (X.en I))) _ hM'
      (fun s => X.rectBound_mul_rem (X.en I) L' hM hJc s) N hN
    refine hbound.trans ?_
    have hpow : (1 + log N) ^ (X.da (X.en I) - 1) ≤ (1 + log N) ^ X.decomp.commonD :=
      pow_le_pow_right₀ (by linarith) (X.decomp.le_commonD I)
    have hK0 : 0 ≤ Kp I * (2 ^ (∑ j, X.remDepth (X.en I) L' j) * X.densityBoundL (X.en I) L' *
        (X.chartConstL (X.en I).1 L' * M)) *
        (baseMeasure (X.act (X.en I).1) (X.T.a (X.en I).1) (X.T.h (X.en I).1)).real univ :=
      mul_nonneg (mul_nonneg (hKp0 I) hM') measureReal_nonneg
    calc Kp I * (2 ^ (∑ j, X.remDepth (X.en I) L' j) * X.densityBoundL (X.en I) L' *
          (X.chartConstL (X.en I).1 L' * M)) *
          (baseMeasure (X.act (X.en I).1) (X.T.a (X.en I).1) (X.T.h (X.en I).1)).real univ *
          (N ^ (-L') * (1 + log N) ^ (X.da (X.en I) - 1))
        ≤ Kp I * (2 ^ (∑ j, X.remDepth (X.en I) L' j) * X.densityBoundL (X.en I) L' *
          (X.chartConstL (X.en I).1 L' * M)) *
          (baseMeasure (X.act (X.en I).1) (X.T.a (X.en I).1) (X.T.h (X.en I).1)).real univ *
          (N ^ (-L') * (1 + log N) ^ X.decomp.commonD) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (rpow_nonneg hN0 _)) hK0
      _ = _ := by ring
  · refine (X.abs_tailInt_le hMf hN0).trans ?_
    calc M * X.T.tail.real univ * exp (-X.T.δ * N)
        ≤ M * X.T.tail.real univ * (Ct * (N ^ (-L') * (1 + log N) ^ X.decomp.commonD)) :=
          mul_le_mul_of_nonneg_left (hCt N hN) (mul_nonneg hM measureReal_nonneg)
      _ = _ := by ring

/-- ★★★ **The uniform remainder (cutoff form)**: for every cutoff `L'` there are an order `R`
(`remOrder X L'`) and a constant `K`, depending on the bridge data only, such that for every
smooth observable `f` whose derivatives of order `≤ R` are bounded by `M` on the compact set
`coreImage ∪ supp prior`,
`|∫ prior·f·e^{−NK} − Σ_{μ < L'} Σ_{q ≤ D} c_{μ,q}(f) N^{−μ} (log N)^q|`
`  ≤ K · M · N^{−L'}(1+log N)^D` for all `N ≥ 1`. -/
theorem uniform_remainder_cutoff (L' : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ ∞ f) (M : ℝ), 0 ≤ M →
      JetBound (X.remOrder L') (X.coreImage ∪ tsupport X.prior) f M → ∀ N : ℝ, 1 ≤ N →
      |partitionObs X.K X.prior f N - absSpectralSum X.decomp.commonQ X.decomp.commonD
        (fun μ q => X.observableCoeff μ q f hf) L' N| ≤
        K * M * (N ^ (-L') * (1 + log N) ^ X.decomp.commonD) := by
  classical
  have hpiece : ∀ I : Fin (Fintype.card X.PIdx), ∃ K : ℝ, 0 ≤ K ∧
      ∀ (ν : Measure (Base (X.act (X.en I).1) (X.T.a (X.en I).1))) [IsFiniteMeasure ν]
        (F : SmoothAmplitudeFamily (Base (X.act (X.en I).1) (X.T.a (X.en I).1)) (X.da (X.en I))
          (X.T.a (X.en I).1)) (M : ℝ), 0 ≤ M →
        (∀ s, RectBound (F s) (X.remDepth (X.en I) L') (X.T.a (X.en I).1) M) → ∀ N : ℝ, 1 ≤ N →
        |familyIntegral ν F (X.hA (X.en I)) (X.kA (X.en I)) (fun _ => X.T.phaseConst (X.en I).1)
            (X.T.a (X.en I).1) N -
          absSpectralSum (Qamb (X.kA (X.en I))) (X.da (X.en I) - 1)
            (familyCoeff ν F (X.hA (X.en I)) (X.kA (X.en I)) (fun _ => X.T.phaseConst (X.en I).1)
              (X.T.a (X.en I).1)) L' N| ≤
          K * M * ν.real univ * (N ^ (-L') * (1 + log N) ^ (X.da (X.en I) - 1)) := fun I =>
    family_uniform_cutoff_linear (X.kA_pos (X.en I)) (X.T.phaseConst_pos (X.en I).1)
      (X.T.a_pos (X.en I).1) L'
  choose Kp hKp0 hKp using hpiece
  obtain ⟨Ct, hCt0, hCt⟩ := exp_neg_mul_le_rpow_profile X.T.δ_pos L' X.decomp.commonD
  refine ⟨X.remConst L' Kp Ct, ?_, fun f hf M hM hJ N hN => ?_⟩
  · unfold remConst
    exact add_nonneg (Finset.sum_nonneg fun I _ => mul_nonneg (mul_nonneg (hKp0 I)
      (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) (X.densityBoundL_nonneg _ _))
        (X.chartConstL_nonneg _ _))) measureReal_nonneg) (mul_nonneg measureReal_nonneg hCt0)
  rw [← X.withObs_Z hf N]
  exact (X.withObs f hf).uniform_remainder_cutoff_aux L' Kp hKp0 hKp Ct hCt hM hJ hN

/-! ### The little-o form: truncation at `A` with an explicit spectral gap -/

/-- The comparison of the engine order of a coefficient below the cutoff with the remainder
order at that cutoff. -/
theorem engineOrder_le_remOrder {μ L' : ℝ} (hμ : μ < L') (hL' : 1 ≤ L') :
    X.engineOrder μ ≤ X.remOrder L' := by
  refine Finset.sup_le fun P _ => le_trans ?_ (X.sum_remDepth_le_remOrder P L')
  refine Finset.sum_le_sum fun j _ => ?_
  unfold pieceDepth remDepth depthOf cutoffOf
  have hceil : ⌊μ⌋₊ + 1 ≤ ⌈L'⌉₊ := by
    by_cases hμ0 : 0 ≤ μ
    · have h1 : (⌊μ⌋₊ : ℝ) ≤ μ := Nat.floor_le hμ0
      have h2 : L' ≤ (⌈L'⌉₊ : ℝ) := Nat.le_ceil L'
      have : (⌊μ⌋₊ : ℝ) < ⌈L'⌉₊ := by linarith
      exact_mod_cast this
    · rw [Nat.floor_of_nonpos (by linarith)]
      have : (1 : ℝ) ≤ ⌈L'⌉₊ := hL'.trans (Nat.le_ceil L')
      exact_mod_cast this
  have hmax : max (⌊μ⌋₊ + 1) (L₀ (X.hA P)) ≤ max ⌈L'⌉₊ (L₀ (X.hA P)) :=
    max_le_max hceil le_rfl
  exact Nat.sub_le_sub_right (Nat.mul_le_mul_left _ hmax) _

/-- The gap above `A` in the lattice `Q⁻¹ℕ`: the distance from `A` to the smallest lattice point
strictly above it (or to `0` if `A < 0`). -/
noncomputable def latticeGap (Q : ℕ) (A : ℝ) : ℝ :=
  if 0 ≤ A then ((⌊A * Q⌋₊ : ℝ) + 1) / Q - A else -A

theorem latticeGap_pos {Q : ℕ} (hQ : 0 < Q) (A : ℝ) : 0 < latticeGap Q A := by
  unfold latticeGap
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  split_ifs with hA
  · have : A * Q < (⌊A * Q⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [sub_pos, lt_div_iff₀ hQ']
    exact this
  · linarith

theorem add_latticeGap_le_cutoffExponent {Q : ℕ} (hQ : 0 < Q) (A : ℝ) :
    A + latticeGap Q A ≤ cutoffExponent A := by
  unfold latticeGap cutoffExponent
  have hQ' : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  split_ifs with hA
  · have hfl : (⌊A * Q⌋₊ : ℝ) ≤ A * Q := Nat.floor_le (by positivity)
    have : ((⌊A * Q⌋₊ : ℝ) + 1) / Q ≤ A + 1 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    exact le_max_of_le_left (by linarith)
  · exact le_max_of_le_right (by linarith)

theorem add_latticeGap_le_of_lt {Q : ℕ} (hQ : 0 < Q) {A μ : ℝ} (hμ : ∃ m : ℕ, μ = (m : ℝ) / Q)
    (hA : A < μ) : A + latticeGap Q A ≤ μ := by
  obtain ⟨m, rfl⟩ := hμ
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  unfold latticeGap
  split_ifs with hA0
  · have h1 : A * Q < m := by rwa [lt_div_iff₀ hQ'] at hA
    have h2 : ⌊A * Q⌋₊ < m := (Nat.floor_lt (by positivity)).2 h1
    have h3 : (⌊A * Q⌋₊ : ℝ) + 1 ≤ m := by exact_mod_cast h2
    have : ((⌊A * Q⌋₊ : ℝ) + 1) / Q ≤ (m : ℝ) / Q := by gcongr
    linarith
  · have : (0 : ℝ) ≤ (m : ℝ) / Q := by positivity
    linarith

/-- ★★★ **The uniform remainder (little-o form)**: after truncating at `A` (all log powers at
every exponent `≤ A`), the remainder is bounded by `K · M · N^{−(A+γ)} (1 + log N)^D` with a
positive spectral gap `γ = latticeGap Q A`, uniformly over the observables `f` with a jet bound
`M` of order `remOrder X (cutoffExponent A)` on the compact set `coreImage ∪ supp prior`. -/
theorem uniform_remainder_spectrumLe (A : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ ∞ f) (M : ℝ), 0 ≤ M →
      JetBound (X.remOrder (cutoffExponent A)) (X.coreImage ∪ tsupport X.prior) f M →
      ∀ N : ℝ, 1 ≤ N →
      |partitionObs X.K X.prior f N - ∑ q ∈ spectrumLe X.decomp.commonQ X.decomp.commonD A,
          X.observableCoeff q.exponent q.logDegree f hf * q.scale N| ≤
        K * M * (N ^ (-(A + latticeGap X.decomp.commonQ A)) *
          (1 + log N) ^ X.decomp.commonD) := by
  classical
  have hQ := X.decomp.commonQ_pos
  have hcut : 1 ≤ cutoffExponent A := le_max_right _ _
  obtain ⟨K₁, hK₁0, hK₁⟩ := X.uniform_remainder_cutoff (cutoffExponent A)
  set band := (spectrumBelow X.decomp.commonQ X.decomp.commonD A).filter
    (fun q => ¬ q.exponent ≤ A) with hband
  set K₂ : ℝ := ∑ q ∈ band, X.jetConst q.exponent q.logDegree with hK₂
  have hK₂0 : 0 ≤ K₂ := Finset.sum_nonneg fun q _ => X.jetConst_nonneg _ _
  refine ⟨K₁ + K₂, add_nonneg hK₁0 hK₂0, fun f hf M hM hJ N hN => ?_⟩
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hlog : 0 ≤ log N := log_nonneg hN
  set γ := latticeGap X.decomp.commonQ A with hγ
  set prof : ℝ := N ^ (-(A + γ)) * (1 + log N) ^ X.decomp.commonD with hprof
  have hprof0 : 0 ≤ prof := mul_nonneg (rpow_nonneg hN0 _) (pow_nonneg (by linarith) _)
  -- the main remainder at the cutoff, compared with the gap profile
  have hmain := hK₁ f hf M hM hJ N hN
  rw [← sum_spectrumBelow] at hmain
  have hprof : N ^ (-cutoffExponent A) * (1 + log N) ^ X.decomp.commonD ≤ prof :=
    mul_le_mul_of_nonneg_right (rpow_le_rpow_of_exponent_le hN
      (neg_le_neg (add_latticeGap_le_cutoffExponent hQ A))) (pow_nonneg (by linarith) _)
  -- the band: exponents in `(A, cutoffExponent A)`
  have hbandterm : ∀ q ∈ band, |X.observableCoeff q.exponent q.logDegree f hf * q.scale N| ≤
      X.jetConst q.exponent q.logDegree * M * prof := by
    intro q hq
    obtain ⟨hqb, hqA⟩ := Finset.mem_filter.1 hq
    obtain ⟨⟨μ, j⟩, hp, rfl⟩ := Finset.mem_map.1 hqb
    obtain ⟨hμ, hj⟩ := Finset.mem_product.1 hp
    change ¬ μ ≤ A at hqA
    have hμlt : μ < cutoffExponent A := lt_of_mem_latticeBelow hQ hμ
    have hμlat : ∃ m : ℕ, μ = (m : ℝ) / X.decomp.commonQ := ((mem_latticeBelow_iff hQ).1 hμ).1
    have hjD : j ≤ X.decomp.commonD := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have hJμ : JetBound (X.engineOrder μ) X.coreImage f M :=
      hJ.mono (X.engineOrder_le_remOrder hμlt hcut) subset_union_left le_rfl
    have hc : |X.observableCoeff μ j f hf| ≤ X.jetConst μ j * M :=
      X.abs_observableCoeff_le μ j hf hM hJμ
    have hsc : |(PowerLogIndex.ofPair (μ, j)).scale N| ≤ prof := by
      rw [PowerLogIndex.scale_def, abs_of_nonneg (mul_nonneg (rpow_nonneg hN0 _)
        (pow_nonneg hlog _))]
      change N ^ (-μ) * log N ^ j ≤ prof
      refine mul_le_mul (rpow_le_rpow_of_exponent_le hN
        (neg_le_neg (add_latticeGap_le_of_lt hQ hμlat (not_le.1 hqA)))) ?_
        (pow_nonneg hlog _) (rpow_nonneg hN0 _)
      exact (pow_le_pow_left₀ hlog (by linarith) j).trans (pow_le_pow_right₀ (by linarith) hjD)
    change |X.observableCoeff μ j f hf * (PowerLogIndex.ofPair (μ, j)).scale N| ≤
      X.jetConst μ j * M * prof
    rw [abs_mul]
    exact mul_le_mul hc hsc (abs_nonneg _) (mul_nonneg (X.jetConst_nonneg _ _) hM)
  -- split the spectrum below the cutoff into the part `≤ A` and the band
  have hsplit : ∑ q ∈ spectrumBelow X.decomp.commonQ X.decomp.commonD A,
      X.observableCoeff q.exponent q.logDegree f hf * q.scale N =
      ∑ q ∈ spectrumLe X.decomp.commonQ X.decomp.commonD A,
        X.observableCoeff q.exponent q.logDegree f hf * q.scale N +
      ∑ q ∈ band, X.observableCoeff q.exponent q.logDegree f hf * q.scale N :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  rw [hsplit] at hmain
  have hdecomp : partitionObs X.K X.prior f N -
      ∑ q ∈ spectrumLe X.decomp.commonQ X.decomp.commonD A,
        X.observableCoeff q.exponent q.logDegree f hf * q.scale N =
      (partitionObs X.K X.prior f N -
        (∑ q ∈ spectrumLe X.decomp.commonQ X.decomp.commonD A,
          X.observableCoeff q.exponent q.logDegree f hf * q.scale N +
        ∑ q ∈ band, X.observableCoeff q.exponent q.logDegree f hf * q.scale N)) +
      ∑ q ∈ band, X.observableCoeff q.exponent q.logDegree f hf * q.scale N := by ring
  rw [hdecomp]
  refine (abs_add_le _ _).trans ?_
  rw [add_mul, add_mul]
  refine add_le_add (hmain.trans (mul_le_mul_of_nonneg_left hprof (mul_nonneg hK₁0 hM))) ?_
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [hK₂, Finset.sum_mul, Finset.sum_mul]
  exact Finset.sum_le_sum fun q hq => hbandterm q hq

/-- ★★★ **The uniform remainder for the partition-function distribution**: for every `A` there
are an order `R`, a constant `K` and a spectral gap `γ > 0` such that for every test function `f`
with a jet bound `M` of order `R` on `coreImage ∪ supp prior`,
`|Zdist X N f − Σ_{μ ≤ A} coeffDistribution X μ q f · N^{−μ} (log N)^q|`
`  ≤ K · M · N^{−(A+γ)} (1+log N)^D` for all `N ≥ 1`: the weak expansion is uniform on
jet-bounded sets of test functions. -/
theorem uniform_remainder_Zdist (A : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : 𝓓((⊤ : TopologicalSpace.Opens (Fin d → ℝ)), ℝ)) (M : ℝ), 0 ≤ M →
      JetBound (X.remOrder (cutoffExponent A)) (X.coreImage ∪ tsupport X.prior) f M →
      ∀ N : ℝ, ∀ hN : 1 ≤ N,
      |X.Zdist N (zero_le_one.trans hN) f -
          ∑ q ∈ spectrumLe X.decomp.commonQ X.decomp.commonD A,
            X.coeffDistribution q.exponent q.logDegree f * q.scale N| ≤
        K * M * (N ^ (-(A + latticeGap X.decomp.commonQ A)) *
          (1 + log N) ^ X.decomp.commonD) := by
  obtain ⟨K, hK0, hK⟩ := X.uniform_remainder_spectrumLe A
  exact ⟨K, hK0, fun f M hM hJ N hN => hK f f.contDiff M hM hJ N hN⟩

end BridgeInputs

end SmoothEngine

end Grammar
