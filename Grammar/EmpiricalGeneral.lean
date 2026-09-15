/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.EmpiricalGeneralDepth
import Grammar.SmoothGeneral

/-!
# The empirical expansion: canonical coefficients (§20 Stage 6)

The depth-`p` empirical expansions of `EmpiricalGeneralDepth` are made DEPTH-FREE exactly as for
the population engine (`SmoothGeneral`): for the cutoff `L ≥ L₀ = ∑hᵢ + 1` the depth
`pᵢ = 2kᵢL − hᵢ` is admissible, the bound `|ζ| ≤ M'` on the closed box exists by compactness, and
two admissible depths give the same coefficients below their common cutoff by finite uniqueness.
The canonical coefficient `empCoeff η ζ h k μ q` uses the deterministic cutoff
`max(⌊μ⌋+1, L₀)`, and ★★★ `emp_cutoffExpansion`: the EMPIRICAL integral
`∫_{(0,1]^d} η(v) v^h e^{−N v^{2k} + √N v^k ζ(v)} dv` is a `CutoffExpansion` on the lattice
`Q⁻¹ℕ`, `Q = 2∏kᵢ`, with logarithmic degree `≤ d − 1` and coefficients `empCoeff` — the same
interface as the population engine, so ★★ `empCoeff_unique` (any cutoff expansion has these
coefficients). Only smoothness of `η, ζ` is assumed. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff

namespace Grammar

namespace SmoothEngine

variable {d : ℕ}

/-- The empirical integral `∫_{(0,1]^d} η(v) e^{√N v^k ζ(v)} v^h e^{−N v^{2k}} dv`. -/
noncomputable def empIntegral (η ζ : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ) (N : ℝ) : ℝ :=
  ∫ v in box (Fin d) 1, fieldFam η ζ (coupling k N v) v * mono h v *
    exp (-N * mono (fun i => 2 * k i) v)

/-- The integrand in the paper's form `η(v) v^h e^{−N v^{2k} + √N v^k ζ(v)}`. -/
theorem empIntegral_eq (η ζ : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ) (N : ℝ) :
    empIntegral η ζ h k N = ∫ v in box (Fin d) 1, η v * mono h v *
      exp (-N * mono (fun i => 2 * k i) v + Real.sqrt N * mono k v * ζ v) := by
  unfold empIntegral fieldFam coupling
  refine setIntegral_congr_fun (measurableSet_box 1) fun v _ => ?_
  rw [Real.exp_add]
  ring

variable {η ζ : (Fin d → ℝ) → ℝ} {h k : Fin d → ℕ}

/-- The bound on the root field on the closed box, from compactness. -/
theorem exists_field_bound (hζ : ContDiff ℝ ∞ ζ) :
    ∃ M' : ℝ, ∀ v ∈ closedBox d 1, |ζ v| ≤ M' := by
  obtain ⟨M', hM'⟩ := (isCompact_closedBox 1).exists_bound_of_continuousOn
    hζ.continuous.continuousOn
  exact ⟨M', fun v hv => by simpa [Real.norm_eq_abs] using hM' v hv⟩

/-- ★★ **The empirical expansion through the cutoff `L ≥ L₀`**, from smoothness alone. -/
theorem emp_expansion_cutoff (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) (hk : ∀ i, 0 < k i)
    {L : ℕ} (hL : L₀ h ≤ L) :
    ∃ K : ℝ, ∀ N : ℝ, 1 ≤ N →
      |empIntegral η ζ h k N - absSpectralSum (Qamb k) (d - 1)
        (empCoeffAtDepth η ζ h k (depthOf h k L)) L N| ≤
        K * (N ^ (-(L : ℝ)) * (1 + log N) ^ (d - 1)) := by
  obtain ⟨M', hM'⟩ := exists_field_bound hζ
  have hL0 : 0 < L := lt_of_lt_of_le (by unfold L₀; omega) hL
  exact empirical_expansion_at_depth h k _ hη hζ hM' hk hL0 (depthOf_add hk hL) (depthOf_pos hk hL)

/-- ★★★ **The canonical empirical coefficients**: the depth-`2kL−h` coefficients at the
deterministic cutoff `L = max(⌊μ⌋₊ + 1, L₀)`. -/
noncomputable def empCoeff (η ζ : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ) (μ : ℝ) (q : ℕ) : ℝ :=
  empCoeffAtDepth η ζ h k (depthOf h k (cutoffOf h μ)) μ q

/-- Two admissible cutoffs give the same coefficients below their common cutoff. -/
theorem empCoeffAtDepth_eq (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) (hk : ∀ i, 0 < k i)
    {L L' : ℕ} (hL : L₀ h ≤ L) (hL' : L₀ h ≤ L') {μ : ℝ}
    (hμ : μ ∈ latticeBelow (Qamb k) L) (hμ' : μ ∈ latticeBelow (Qamb k) L') {q : ℕ}
    (hq : q ≤ d - 1) :
    empCoeffAtDepth η ζ h k (depthOf h k L) μ q =
      empCoeffAtDepth η ζ h k (depthOf h k L') μ q := by
  have hQ := Qamb_pos k hk
  obtain ⟨K₁, hK₁⟩ := emp_expansion_cutoff hη hζ hk hL
  obtain ⟨K₂, hK₂⟩ := emp_expansion_cutoff hη hζ hk hL'
  set L'' : ℝ := min (L : ℝ) (L' : ℝ) with hL''
  have h1 : L'' ≤ L := min_le_left _ _
  have h2 : L'' ≤ L' := min_le_right _ _
  obtain ⟨hm, hlt⟩ := (mem_latticeBelow_iff hQ).1 hμ
  have hlt' := ((mem_latticeBelow_iff hQ).1 hμ').2
  have hμ'' : μ ∈ latticeBelow (Qamb k) L'' :=
    (mem_latticeBelow_iff hQ).2 ⟨hm, lt_min hlt hlt'⟩
  refine finite_coeff_unique hQ (Z := empIntegral η ζ h k) (L := L'')
    (K₁ := K₁ + ∑ ν ∈ latticeBelow (Qamb k) L, ∑ j ∈ range (d - 1 + 1),
      |empCoeffAtDepth η ζ h k (depthOf h k L) ν j|)
    (K₂ := K₂ + ∑ ν ∈ latticeBelow (Qamb k) L', ∑ j ∈ range (d - 1 + 1),
      |empCoeffAtDepth η ζ h k (depthOf h k L') ν j|) ?_ ?_ μ hμ'' q hq
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with N hN
    exact bound_lower_cutoff hQ h1 hN (hK₁ N hN)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with N hN
    exact bound_lower_cutoff hQ h2 hN (hK₂ N hN)

/-- The canonical coefficient agrees with every admissible depth below its cutoff. -/
theorem empCoeff_eq (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) (hk : ∀ i, 0 < k i) {L : ℕ}
    (hL : L₀ h ≤ L) {μ : ℝ} (hμ : μ ∈ latticeBelow (Qamb k) L) {q : ℕ} (hq : q ≤ d - 1) :
    empCoeff η ζ h k μ q = empCoeffAtDepth η ζ h k (depthOf h k L) μ q := by
  have hQ := Qamb_pos k hk
  obtain ⟨hm, _⟩ := (mem_latticeBelow_iff hQ).1 hμ
  have hμc : μ ∈ latticeBelow (Qamb k) (cutoffOf h μ) :=
    (mem_latticeBelow_iff hQ).2 ⟨hm, lt_cutoffOf h μ⟩
  exact empCoeffAtDepth_eq hη hζ hk (L₀_le_cutoffOf h μ) hL hμc hμ hq

/-- ★★★ **The empirical integral is a cutoff expansion** on the lattice `Q⁻¹ℕ`, `Q = 2∏kᵢ`, with
logarithmic degree `≤ d − 1` and the canonical coefficients `empCoeff`: for every `L > 0` there is
`K` with
`|∫_{(0,1]^d} η v^h e^{−N v^{2k} + √N v^k ζ} dv`
`  − ∑_{μ ∈ Λ^Q_L} N^{−μ} ∑_{q ≤ d−1} empCoeff μ q (log N)^q|`
`  ≤ K N^{−L} (1 + log N)^{d−1}` eventually in `N`. -/
theorem emp_cutoffExpansion (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) (hk : ∀ i, 0 < k i) :
    CutoffExpansion (Qamb k) (d - 1) (empIntegral η ζ h k) (empCoeff η ζ h k) := by
  intro L' hL'
  have hQ := Qamb_pos k hk
  set L : ℕ := max ⌈L'⌉₊ (L₀ h) with hLdef
  have hL : L₀ h ≤ L := le_max_right _ _
  have hLL : L' ≤ (L : ℝ) := by
    have h1 := Nat.le_ceil L'
    have h2 : ((⌈L'⌉₊ : ℕ) : ℝ) ≤ ((max ⌈L'⌉₊ (L₀ h) : ℕ) : ℝ) := by exact_mod_cast le_max_left _ _
    linarith
  obtain ⟨K, hK⟩ := emp_expansion_cutoff hη hζ hk hL
  refine ⟨K + ∑ ν ∈ latticeBelow (Qamb k) L, ∑ j ∈ range (d - 1 + 1),
    |empCoeffAtDepth η ζ h k (depthOf h k L) ν j|, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with N hN
  have hlow := bound_lower_cutoff hQ hLL hN (hK N hN)
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
  exact hlow

/-- ★★ **Canonicity**: any cutoff expansion of the empirical integral on the lattice `Q⁻¹ℕ` with
logarithmic degree `≤ d − 1` has the coefficients `empCoeff`. -/
theorem empCoeff_unique (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) (hk : ∀ i, 0 < k i)
    {c : ℝ → ℕ → ℝ} (hc : CutoffExpansion (Qamb k) (d - 1) (empIntegral η ζ h k) c) {μ : ℝ}
    (hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb k) {j : ℕ} (hj : j ≤ d - 1) :
    c μ j = empCoeff η ζ h k μ j :=
  CutoffExpansion.coeff_unique (Qamb_pos k hk) hc (emp_cutoffExpansion hη hζ hk) hμ hj

/-- The population engine is the zero-field case: `empIntegral η 0 h k = smoothIntegral η h k 1 1`
(pointwise `e^{0} = 1`). -/
theorem empIntegral_zero_field (η : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ) (N : ℝ) :
    empIntegral η (fun _ => 0) h k N = smoothIntegral η h k 1 1 N := by
  unfold empIntegral smoothIntegral fieldFam
  refine setIntegral_congr_fun (measurableSet_box 1) fun v _ => ?_
  simp

end SmoothEngine

end Grammar
