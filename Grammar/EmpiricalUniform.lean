/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.EmpiricalGeneral
import Grammar.SmoothCoeffBound

/-!
# The empirical expansion, uniformly in the field data (§20 unit 1 of consult #142)

The constants of the empirical box expansion depend on `(η, ζ)` only through the rectangular jet
bound `FieldJetBound η ζ p 1 C M'` (`|∂^m(η e^{τζ})| ≤ C (1+τ)^{|p|} e^{M'τ}`, `m ≤ p`), and
LINEARLY in `C`. This file records the consequences at the level of the canonical coefficients:
the coefficients themselves are `O(C)` (★ `exists_abs_empCoeffAtDepth_le`, via
`abs_faceCoeffInt_le`),
the expansion through every admissible cutoff is `C · K₀ N^{−L}(1+log N)^{d−1}` with `K₀`
depending only on `(h, k, L, M')` (`emp_expansion_cutoff_uniform`), and
★★★ `emp_cutoffExpansion_uniform`: for every real cutoff `L' > 0` there is `K₀ = K₀(h,k,L',M')`
with `|Z_{η,ζ}(N) − Σ_{μ<L'} N^{−μ} Σ_q empCoeff η ζ μ q (log N)^q| ≤ C K₀ N^{−L'}(1+log N)^{d−1}`
for ALL `N ≥ 1` and ALL smooth `(η, ζ)` satisfying the jet bound at the depth of `L'`. This is the
input for random fields `ζ = ζ_n(ω)` with tight jet bounds. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff

namespace Grammar

namespace SmoothEngine

variable {d : ℕ} (h k p : Fin d → ℕ)

/-- ★ **The coefficients are `O(C)`**: there is `K₁ = K₁(h,k,p,L,M')` such that for every smooth
`(η, ζ)` with jet bound `C`, `Σ_{μ ∈ Λ^Q_L} Σ_{j ≤ d−1} |empCoeffAtDepth η ζ h k p μ j| ≤ C K₁`. -/
theorem exists_abs_empCoeffAtDepth_le (hk : ∀ i, 0 < k i) {L : ℕ}
    (hp : ∀ i, p i + h i = 2 * k i * L) (hp0 : ∀ i, 0 < p i) (M' : ℝ) :
    ∃ K₁ : ℝ, 0 ≤ K₁ ∧ ∀ (η ζ : (Fin d → ℝ) → ℝ), ContDiff ℝ ∞ η → ContDiff ℝ ∞ ζ →
      ∀ C : ℝ, FieldJetBound η ζ p 1 C M' →
        ∑ μ ∈ latticeBelow (Qamb k) L, ∑ j ∈ range (d - 1 + 1),
          |empCoeffAtDepth η ζ h k p μ j| ≤ C * K₁ := by
  have hQ := Qamb_pos k hk
  choose Cc hCc0 hCc using fun (J : Finset (Fin d)) (e : Fin d → ℕ) =>
    exists_abs_empFaceCoef_le k (L : ℝ) J hk (∑ i, p i) M' e
  -- the per-face flatness prefactor
  set P : Finset (Fin d) → ℝ := fun J => ∏ i : {i // ¬ inJ J i}, ((p i - 1).factorial : ℝ)⁻¹
    with hP
  have hP0 : ∀ J, 0 ≤ P J := fun J => Finset.prod_nonneg fun i _ => by positivity
  -- the constant
  set K₁ : ℝ := ∑ μ ∈ latticeBelow (Qamb k) L, ∑ q ∈ range (d - 1 + 1),
    ∑ x ∈ faceIndex p, faceW x.1 x.2 * ∑ j ∈ Finset.Ico q (DJ x.1 + 1), (j.choose q : ℝ) *
      (P x.1 * Cc x.1 (fun i => x.2 i + h i) *
        faceMajorant (fun i : {i // ¬ inJ x.1 i} => p i) (fun i : {i // ¬ inJ x.1 i} => h i)
          (fun i : {i // ¬ inJ x.1 i} => 2 * k i) 1 μ (j - q)) with hK₁
  have hK₁0 : 0 ≤ K₁ := by
    refine Finset.sum_nonneg fun μ _ => Finset.sum_nonneg fun q _ => Finset.sum_nonneg fun x _ =>
      mul_nonneg (faceW_nonneg _ _) (Finset.sum_nonneg fun j _ => ?_)
    have := hP0 x.1
    have := hCc0 x.1 (fun i => x.2 i + h i)
    have := faceMajorant_nonneg (fun i : {i // ¬ inJ x.1 i} => p i)
      (fun i : {i // ¬ inJ x.1 i} => h i) (fun i : {i // ¬ inJ x.1 i} => 2 * k i) 1 μ (j - q)
    positivity
  refine ⟨K₁, hK₁0, fun η ζ hη hζ C hC => ?_⟩
  have hC0 : 0 ≤ C := hC.nonneg zero_le_one
  rw [hK₁, Finset.mul_sum]
  refine Finset.sum_le_sum fun μ hμ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun q _ => ?_
  have hμL : μ < L := ((mem_latticeBelow_iff hQ).1 hμ).2
  have hμ0 : 0 ≤ μ := by
    obtain ⟨m, rfl⟩ := ((mem_latticeBelow_iff hQ).1 hμ).1
    positivity
  -- the per-face coefficient integrals
  unfold empCoeffAtDepth
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x hx => ?_)
  rw [abs_mul, abs_of_nonneg (faceW_nonneg _ _), mul_left_comm, Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun j hj => ?_)) (faceW_nonneg _ _)
  rw [abs_mul, Nat.abs_cast]
  -- flatness of the coefficient function `w ↦ empFaceCoef … μ j`
  have hjD : j ≤ DJ x.1 := Nat.lt_succ_iff.1 (Finset.mem_Ico.1 hj).2
  have hgrow : ∀ w ∈ box {i // ¬ inJ x.1 i} 1,
      GrowthLE (fun τ => faceAmp p x.1 (fieldFam η ζ τ) x.2 w)
        (P x.1 * C * mono (fun i : {i // ¬ inJ x.1 i} => p i) w) (∑ i, p i) M' :=
    fun w hw => growthLE_faceAmp_fieldFam_of_bound hη hζ one_pos hC hp0 x.1 x.2
      (Finset.mem_sigma.1 hx).2 hw
  have hflat : ∀ w ∈ box {i // ¬ inJ x.1 i} 1,
      |empFaceCoef k x.1 (fun i => x.2 i + h i) (fun τ => faceAmp p x.1 (fieldFam η ζ τ) x.2 w)
          μ j| ≤ (C * (P x.1 * Cc x.1 (fun i => x.2 i + h i))) *
            mono (fun i : {i // ¬ inJ x.1 i} => p i) w := by
    intro w hw
    by_cases hμJ : μ ∈ empΛJ k (L : ℝ) x.1 (fun i => x.2 i + h i)
    · calc |empFaceCoef k x.1 (fun i => x.2 i + h i)
            (fun τ => faceAmp p x.1 (fieldFam η ζ τ) x.2 w) μ j|
          ≤ (P x.1 * C * mono (fun i : {i // ¬ inJ x.1 i} => p i) w) *
              Cc x.1 (fun i => x.2 i + h i) :=
            hCc _ _ _ _ (hgrow w hw) μ hμJ j (Finset.mem_range.2 (Nat.lt_succ_of_le hjD))
        _ = _ := by ring
    · rw [empFaceCoef_eq_zero k (L : ℝ) x.1 hk _ _ hμ hμJ j, abs_zero]
      have := hP0 x.1
      have := hCc0 x.1 (fun i => x.2 i + h i)
      have := (mono_pos (fun i : {i // ¬ inJ x.1 i} => p i) (pos_of_mem_box hw)).le
      positivity
  have hconv : ∀ i : {i // ¬ inJ x.1 i}, ((2 * k i : ℕ) : ℝ) * μ < (p i : ℝ) + h i + 1 := by
    intro i
    have h1 : ((2 * k i : ℕ) : ℝ) * L = (p i : ℝ) + h i := by exact_mod_cast (hp i).symm
    have h2 : (0 : ℝ) < (2 * k i : ℕ) := by exact_mod_cast Nat.mul_pos two_pos (hk i)
    nlinarith
  have hface : |faceCoeffInt (fun w => empFaceCoef k x.1 (fun i => x.2 i + h i)
          (fun τ => faceAmp p x.1 (fieldFam η ζ τ) x.2 w) μ j)
        (fun i : {i // ¬ inJ x.1 i} => h i) (fun i : {i // ¬ inJ x.1 i} => 2 * k i) 1 μ (j - q)|
      ≤ (C * (P x.1 * Cc x.1 (fun i => x.2 i + h i))) *
          faceMajorant (fun i : {i // ¬ inJ x.1 i} => p i) (fun i : {i // ¬ inJ x.1 i} => h i)
            (fun i : {i // ¬ inJ x.1 i} => 2 * k i) 1 μ (j - q) :=
    abs_faceCoeffInt_le one_pos (measurable_empFaceCoef_comp k x.1 _
      (measurable_uncurry_faceAmp_fieldFam hη hζ p x.1 x.2) μ j).aestronglyMeasurable hflat
      hconv (j - q)
  exact le_of_le_of_eq (mul_le_mul_of_nonneg_left hface (Nat.cast_nonneg _)) (by ring)

/-! ### The uniform cutoff expansions -/

variable {h k}

/-- ★★ **The expansion through the cutoff `L ≥ L₀`, uniformly in the field data.** -/
theorem emp_expansion_cutoff_uniform (hk : ∀ i, 0 < k i) {L : ℕ} (hL : L₀ h ≤ L) (M' : ℝ) :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ (η ζ : (Fin d → ℝ) → ℝ), ContDiff ℝ ∞ η → ContDiff ℝ ∞ ζ →
      ∀ C : ℝ, FieldJetBound η ζ (depthOf h k L) 1 C M' → ∀ N : ℝ, 1 ≤ N →
        |empIntegral η ζ h k N - absSpectralSum (Qamb k) (d - 1)
          (empCoeffAtDepth η ζ h k (depthOf h k L)) L N| ≤
          C * K₀ * (N ^ (-(L : ℝ)) * (1 + log N) ^ (d - 1)) := by
  have hL0 : 0 < L := lt_of_lt_of_le (by unfold L₀; omega) hL
  exact empirical_expansion_at_depth_uniform h k _ hk hL0 (depthOf_add hk hL) (depthOf_pos hk hL) M'

/-- ★★★ **The canonical cutoff expansion, uniformly in the field data**: for every real cutoff
`L' > 0` there is `K₀ = K₀(h, k, L', M')` such that for every smooth `(η, ζ)` with the jet bound
of constant `C` at the depth of `L'`,
`|Z_{η,ζ}(N) − Σ_{μ ∈ Λ^Q_{L'}} N^{−μ} Σ_{q ≤ d−1} empCoeff η ζ h k μ q (log N)^q|`
`  ≤ C K₀ N^{−L'} (1 + log N)^{d−1}` for ALL `N ≥ 1`. -/
theorem emp_cutoffExpansion_uniform (hk : ∀ i, 0 < k i) (L' M' : ℝ) :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ (η ζ : (Fin d → ℝ) → ℝ), ContDiff ℝ ∞ η → ContDiff ℝ ∞ ζ →
      ∀ C : ℝ, FieldJetBound η ζ (depthOf h k (max ⌈L'⌉₊ (L₀ h))) 1 C M' → ∀ N : ℝ, 1 ≤ N →
        |empIntegral η ζ h k N - absSpectralSum (Qamb k) (d - 1) (empCoeff η ζ h k) L' N| ≤
          C * K₀ * (N ^ (-L') * (1 + log N) ^ (d - 1)) := by
  have hQ := Qamb_pos k hk
  set L : ℕ := max ⌈L'⌉₊ (L₀ h) with hLdef
  have hL : L₀ h ≤ L := le_max_right _ _
  have hL0 : 0 < L := lt_of_lt_of_le (by unfold L₀; omega) hL
  have hLL : L' ≤ (L : ℝ) := by
    have h1 := Nat.le_ceil L'
    have h2 : ((⌈L'⌉₊ : ℕ) : ℝ) ≤ ((max ⌈L'⌉₊ (L₀ h) : ℕ) : ℝ) := by exact_mod_cast le_max_left _ _
    linarith
  obtain ⟨K₀, hK₀0, hK₀⟩ := emp_expansion_cutoff_uniform hk hL M'
  obtain ⟨K₁, hK₁0, hK₁⟩ := exists_abs_empCoeffAtDepth_le h k (depthOf h k L) hk
    (depthOf_add hk hL) (depthOf_pos hk hL) M'
  refine ⟨K₀ + K₁, add_nonneg hK₀0 hK₁0, fun η ζ hη hζ C hC N hN => ?_⟩
  have hC0 : 0 ≤ C := hC.nonneg zero_le_one
  have hlow := bound_lower_cutoff hQ hLL hN (hK₀ η ζ hη hζ C hC N hN)
  have hc : ∀ μ ∈ latticeBelow (Qamb k) L', ∀ q ∈ range (d - 1 + 1),
      empCoeff η ζ h k μ q = empCoeffAtDepth η ζ h k (depthOf h k L) μ q := fun μ hμ q hq =>
    empCoeff_eq hη hζ hk hL (latticeBelow_mono hQ hLL hμ)
      (Nat.lt_succ_iff.1 (Finset.mem_range.1 hq))
  have hcoef : absSpectralSum (Qamb k) (d - 1) (empCoeff η ζ h k) L' N =
      absSpectralSum (Qamb k) (d - 1) (empCoeffAtDepth η ζ h k (depthOf h k L)) L' N := by
    unfold absSpectralSum
    exact Finset.sum_congr rfl fun μ hμ => congrArg (N ^ (-μ) * ·)
      (Finset.sum_congr rfl fun q hq => by rw [hc μ hμ q hq])
  rw [hcoef]
  have hlog : 0 ≤ log N := log_nonneg hN
  refine hlow.trans (mul_le_mul_of_nonneg_right ?_
    (mul_nonneg (rpow_nonneg (by linarith) _) (pow_nonneg (by linarith) _)))
  have := hK₁ η ζ hη hζ C hC
  linarith

end SmoothEngine

end Grammar
