/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.EmpiricalFaceSumCollapse
import Grammar.EmpiricalBoxScaling

/-!
# The replacement rule on a general cube (§20, consult #143 priority 2a)

The graded empirical formula of `EmpiricalFaceSumCollapse` is stated on the unit box. On the cube
`(0,b]^d` it follows by the exact dilation `v = b u`, without repeating the face analysis: the deep
set of the cube is the dilated deep set of the unit box (`mapsTo_diag_deepSet`,
`eventually_zero_deepSet_diag`), the POPULATION coefficients obey the same scaling law as the
empirical ones (`smoothIntegral_eq_dilation`, ★ `smoothCoeff_eq_scaleCoeff_dilation`, by uniqueness
of cutoff expansions), the coefficients of log degree `≥ c` of a deep-vanishing amplitude vanish on
both sides (`smoothCoeff_eq_zero_of_deep`, from the population support theorem), so at the top
power the log mixing of the dilation disappears and
★★★ `empCoeffRect_top_eq_smoothCoeff`:
`empCoeffRect η ζ h k b μ (c−1) = smoothCoeff (η S_μ(ζ)/Γ(μ)) h k 1 b μ (c−1)`
for `η` vanishing near the deep set of the cube — the replacement rule `∂^α A ↦ ∂^α[A S_μ(ζ)]/Γ(μ)`
on every chart cube.
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff

namespace Grammar

namespace SmoothEngine

variable {d : ℕ}

/-! ### Dilation of the deep set -/

theorem mapsTo_diag_deepSet {b : ℝ} (hb : 0 < b) (c : ℕ) :
    MapsTo (diag (fun _ : Fin d => b)) (deepSet d 1 c) (deepSet d b c) := by
  intro v hv
  obtain ⟨hvbox, hcard⟩ := hv
  refine ⟨?_, ?_⟩
  · rw [mem_closedBox] at hvbox ⊢
    intro i
    have := hvbox i
    simp only [diag]
    exact ⟨mul_nonneg hb.le this.1, by nlinarith [this.2]⟩
  · refine hcard.trans (Finset.card_le_card fun i hi => ?_)
    rw [Finset.mem_filter] at hi ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    simp only [diag, hi.2, mul_zero]

theorem eventually_zero_deepSet_diag {η : (Fin d → ℝ) → ℝ} {b : ℝ} (hb : 0 < b) {c : ℕ}
    (h : ∀ᶠ v in 𝓝ˢ (deepSet d b c), η v = 0) :
    ∀ᶠ v in 𝓝ˢ (deepSet d 1 c), (η ∘ diag (fun _ : Fin d => b)) v = 0 :=
  ((contDiff_diag (fun _ : Fin d => b)).continuous.tendsto_nhdsSet
    (mapsTo_diag_deepSet hb c)).eventually h

/-! ### The population scaling law -/

/-- The population cube integral is the dilated unit-box integral. -/
theorem smoothIntegral_eq_dilation (F : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ) (β : ℝ) {b : ℝ}
    (hb : 0 < b) (N : ℝ) :
    smoothIntegral F h k β b N =
      ((∏ _i : Fin d, b) * mono h (fun _ : Fin d => b)) *
        smoothIntegral (F ∘ diag (fun _ : Fin d => b)) h k β 1
          (mono (fun i => 2 * k i) (fun _ : Fin d => b) * N) := by
  unfold smoothIntegral
  rw [← rect_const, integral_rect_eq _ (fun _ => hb), mul_assoc]
  congr 1
  rw [← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun (measurableSet_box (ι := Fin d) 1) fun u _ => ?_
  rw [mono_diag, mono_diag]
  simp only [Function.comp_apply]
  ring_nf

variable {F : (Fin d → ℝ) → ℝ} {h k : Fin d → ℕ}

/-- ★ **The dilation acts on the canonical population coefficients by the scaling law**:
`smoothCoeff F h k β b = A_b · scaleCoeff (d−1) B_b (smoothCoeff (F ∘ b) h k β 1)`. -/
theorem smoothCoeff_eq_scaleCoeff_dilation (hF : ContDiff ℝ ∞ F) (hk : ∀ i, 0 < k i) {β b : ℝ}
    (hβ : 0 < β) (hb : 0 < b) (μ : ℝ) (q : ℕ) :
    smoothCoeff F h k β b μ q =
      ((∏ _i : Fin d, b) * mono h (fun _ : Fin d => b)) *
        scaleCoeff (d - 1) (mono (fun i => 2 * k i) (fun _ : Fin d => b))
          (smoothCoeff (F ∘ diag (fun _ : Fin d => b)) h k β 1) μ q := by
  have hQ := Qamb_pos k hk
  have hB : 0 < mono (fun i => 2 * k i) (fun _ : Fin d => b) := mono_pos _ fun _ => hb
  have hFD : ContDiff ℝ ∞ (F ∘ diag (fun _ : Fin d => b)) := hF.comp (contDiff_diag _)
  have h1 : CutoffExpansion (Qamb k) (d - 1) (smoothIntegral F h k β b)
      (fun μ j => ((∏ _i : Fin d, b) * mono h (fun _ : Fin d => b)) *
        scaleCoeff (d - 1) (mono (fun i => 2 * k i) (fun _ : Fin d => b))
          (smoothCoeff (F ∘ diag (fun _ : Fin d => b)) h k β 1) μ j) := by
    have hexp := CutoffExpansion.const_mul ((∏ _i : Fin d, b) * mono h (fun _ : Fin d => b))
      (CutoffExpansion.comp_mul_pos (smooth_cutoffExpansion hFD hk hβ one_pos (h := h)) hB)
    have hfun : (fun N => ((∏ _i : Fin d, b) * mono h (fun _ : Fin d => b)) *
        smoothIntegral (F ∘ diag (fun _ : Fin d => b)) h k β 1
          (mono (fun i => 2 * k i) (fun _ : Fin d => b) * N)) = smoothIntegral F h k β b :=
      funext fun N => (smoothIntegral_eq_dilation F h k β hb N).symm
    rwa [hfun] at hexp
  by_cases hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb k
  · by_cases hq : q ≤ d - 1
    · exact CutoffExpansion.coeff_unique hQ (smooth_cutoffExpansion hF hk hβ hb) h1 hμ hq
    · have hq' := not_le.1 hq
      rw [smoothCoeff_eq_zero_of_degree_gt hq', scaleCoeff_eq_zero_of_degree_gt hq', mul_zero]
  · have hμ' : ∀ m : ℕ, μ ≠ (m : ℝ) / Qamb k := fun m hm => hμ ⟨m, hm⟩
    rw [smoothCoeff_eq_zero_of_not_lattice hk hβ hb hμ' q,
      scaleCoeff_eq_zero_of_not_lattice (Q := Qamb k)
        (fun ν hν j => smoothCoeff_eq_zero_of_not_lattice hk hβ one_pos hν j) hμ' q, mul_zero]

/-! ### Upper-degree vanishing for deep-vanishing population amplitudes -/

theorem resonantCount_le_card (k e : Fin d → ℕ) (μ : ℝ) (J : Finset (Fin d)) :
    resonantCount (fun i : {i // inJ J i} => k i) (fun i : {i // inJ J i} => e i) μ ≤ J.card := by
  unfold resonantCount
  exact (Finset.card_le_univ _).trans (card_subtype_inJ J).le

/-- The population coefficients of log degree `≥ c` of an amplitude with vanishing jets on the deep
set `{≥ c+1 vanishing coordinates}` vanish. -/
theorem smoothCoeff_eq_zero_of_deep (hF : ContDiff ℝ ∞ F) (hk : ∀ i, 0 < k i) {β b : ℝ}
    (hβ : 0 < β) (hb : 0 < b) {c : ℕ} (hdeep : JetsZeroOn F (deepSet d b c)) (μ : ℝ) {q : ℕ}
    (hq : c ≤ q) : smoothCoeff F h k β b μ q = 0 := by
  refine smoothCoeff_eq_zero_of_resonant hF h k hk hβ hb μ q fun J hJ v hv hvJ α => ?_
  have hcard : c + 1 ≤ J.card :=
    (Nat.succ_le_succ hq).trans (hJ.trans (resonantCount_le_card _ _ μ J))
  exact hdeep α v (mem_deepSet_of_zeros hv hcard hvJ)

/-! ### The replacement rule on the cube -/

variable {η ζ : (Fin d → ℝ) → ℝ}

/-- ★★★ **The replacement rule on a general cube**: for `η` vanishing near the deep set of
`(0,b]^d`, the empirical top coefficient of the cube integral is the population coefficient, on the
same cube, of the amplitude `η · S_μ(ζ)/Γ(μ)`. -/
theorem empCoeffRect_top_eq_smoothCoeff (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ)
    (hk : ∀ i, 0 < k i) {b : ℝ} (hb : 0 < b) {μ : ℝ} (hμ : 0 < μ) {c : ℕ} (hc : 1 ≤ c)
    (hdeep : ∀ᶠ v in 𝓝ˢ (deepSet d b c), η v = 0) :
    empCoeffRect η ζ h k (fun _ => b) μ (c - 1) =
      smoothCoeff (fun v => η v * fluctuation 1 μ (ζ v) / Real.Gamma μ) h k 1 b μ (c - 1) := by
  have hB : 0 < mono (fun i => 2 * k i) (fun _ : Fin d => b) := mono_pos _ fun _ => hb
  set A : ℝ := (∏ _i : Fin d, b) * mono h (fun _ : Fin d => b) with hA
  set B : ℝ := mono (fun i => 2 * k i) (fun _ : Fin d => b) with hBdef
  have hηD : ContDiff ℝ ∞ (η ∘ diag (fun _ : Fin d => b)) := hη.comp (contDiff_diag _)
  have hζD : ContDiff ℝ ∞ (ζ ∘ diag (fun _ : Fin d => b)) := hζ.comp (contDiff_diag _)
  have hdeep1 := eventually_zero_deepSet_diag hb hdeep
  -- the population amplitude and its dilation
  set G : (Fin d → ℝ) → ℝ := fun v => η v * fluctuation 1 μ (ζ v) / Real.Gamma μ with hG
  have hGc : ContDiff ℝ ∞ G := (contDiff_mul_fluctuation hη hζ hμ).div_const _
  have hGD : G ∘ diag (fun _ : Fin d => b) = fun v => (η ∘ diag (fun _ : Fin d => b)) v *
      fluctuation 1 μ ((ζ ∘ diag (fun _ : Fin d => b)) v) / Real.Gamma μ := rfl
  have hGDdeep : JetsZeroOn (G ∘ diag (fun _ : Fin d => b)) (deepSet d 1 c) :=
    jetsZeroOn_of_eventually_zero (hGc.comp (contDiff_diag _)) one_pos
      (deepSet_subset_closedBox 1 c) (hdeep1.mono fun v hv => by
        rw [hGD]; simp only [hv, zero_mul, zero_div])
  by_cases hcd : c - 1 ≤ d - 1
  · -- the empirical side: only `j = c − 1` survives in the scaling law
    have hL : empCoeffRect η ζ h k (fun _ => b) μ (c - 1) =
        A * (B ^ (-μ) * empCoeff (η ∘ diag (fun _ : Fin d => b)) (ζ ∘ diag (fun _ : Fin d => b))
          h k μ (c - 1)) := by
      unfold empCoeffRect scaleCoeff
      rw [Finset.sum_eq_single (c - 1)]
      · rw [Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, mul_one, mul_one]
      · intro j hj hne
        have hjc : c ≤ j := by
          have := (Finset.mem_Ico.1 hj).1
          omega
        rw [empCoeff_eq_zero_of_deep hηD hζD hdeep1 hjc, zero_mul, zero_mul]
      · intro hnot
        exact absurd (Finset.mem_Ico.2 ⟨le_rfl, by omega⟩) hnot
    -- the population side: the same collapse
    have hR : smoothCoeff G h k 1 b μ (c - 1) =
        A * (B ^ (-μ) * smoothCoeff (G ∘ diag (fun _ : Fin d => b)) h k 1 1 μ (c - 1)) := by
      rw [smoothCoeff_eq_scaleCoeff_dilation hGc hk one_pos hb]
      unfold scaleCoeff
      rw [Finset.sum_eq_single (c - 1)]
      · rw [Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, mul_one, mul_one]
      · intro j hj hne
        have hjc : c ≤ j := by
          have := (Finset.mem_Ico.1 hj).1
          omega
        rw [smoothCoeff_eq_zero_of_deep (hGc.comp (contDiff_diag _)) hk one_pos one_pos hGDdeep μ
          hjc, zero_mul, zero_mul]
      · intro hnot
        exact absurd (Finset.mem_Ico.2 ⟨le_rfl, by omega⟩) hnot
    rw [hL, hR, empCoeff_top_eq_smoothCoeff hηD hζD hk hμ hc hdeep1, hGD]
  · -- log degree beyond the dimension: both sides vanish
    have hgt : d - 1 < c - 1 := not_le.1 hcd
    unfold empCoeffRect
    rw [scaleCoeff_eq_zero_of_degree_gt hgt, mul_zero, smoothCoeff_eq_zero_of_degree_gt hgt]

end SmoothEngine

end Grammar
