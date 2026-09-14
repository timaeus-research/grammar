/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothGeneralDepth
import Grammar.SmoothFiniteUniqueness
import Grammar.CutoffExpansionUniqueness

/-!
# The smooth-amplitude expansion: canonical coefficients (consult #116 §2, U3 closure)

The depth-`p` expansions of `SmoothGeneralDepth` are made DEPTH-FREE: for the cutoff `L` the
depth `pᵢ = 2kᵢL − hᵢ` is admissible once `L ≥ L₀ = ∑hᵢ + 1`, the rectangular mixed-derivative
bound exists by compactness (`exists_rect_bound`), and two admissible depths give the same
coefficients below their common cutoff by finite uniqueness (`smoothCoeffAtDepth_eq`). The
canonical coefficient `smoothCoeff F μ q` uses the deterministic cutoff `max(⌊μ⌋+1, L₀)`, and
★★★ `smooth_cutoffExpansion`: the smooth-amplitude integral `∫_{(0,b]^d} F v^h e^{−Nβ v^{2k}} dv`
is a `CutoffExpansion` on the lattice `Q⁻¹ℕ`, `Q = 2∏kᵢ`, with logarithmic degree `≤ d − 1` and
coefficients `smoothCoeff` — the same interface as the analytic box engine, so the repo's
canonicity theorems (`CutoffExpansion.coeff_unique`) apply: ★★ `smoothCoeff_unique`. Only
smoothness of `F` is assumed (no analyticity, no ℓ¹ coefficient families). Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff

namespace Grammar

namespace SmoothEngine

variable {d : ℕ}

/-! ### Depths and cutoffs -/

/-- The smooth-amplitude integral as a function of the sample size. -/
noncomputable def smoothIntegral (F : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ) (β b N : ℝ) : ℝ :=
  ∫ v in box (Fin d) b, F v * mono h v * exp (-(N * β) * mono (fun i => 2 * k i) v)

/-- The depth for the cutoff `L`: `pᵢ = 2kᵢL − hᵢ`. -/
def depthOf (h k : Fin d → ℕ) (L : ℕ) : Fin d → ℕ := fun i => 2 * k i * L - h i

/-- The first cutoff at which every depth is positive. -/
def L₀ (h : Fin d → ℕ) : ℕ := (∑ i, h i) + 1

theorem h_lt_of_L₀_le {h : Fin d → ℕ} {L : ℕ} (hL : L₀ h ≤ L) (i : Fin d) : h i < L := by
  have := Finset.single_le_sum (fun j _ => Nat.zero_le (h j)) (Finset.mem_univ i)
  unfold L₀ at hL
  omega

theorem depthOf_add {h k : Fin d → ℕ} (hk : ∀ i, 0 < k i) {L : ℕ} (hL : L₀ h ≤ L) (i : Fin d) :
    depthOf h k L i + h i = 2 * k i * L := by
  unfold depthOf
  have h1 := h_lt_of_L₀_le hL i
  have h2 : L ≤ 2 * k i * L := by
    have := hk i
    nlinarith
  omega

theorem depthOf_pos {h k : Fin d → ℕ} (hk : ∀ i, 0 < k i) {L : ℕ} (hL : L₀ h ≤ L) (i : Fin d) :
    0 < depthOf h k L i := by
  unfold depthOf
  have h1 := h_lt_of_L₀_le hL i
  have h2 : L ≤ 2 * k i * L := by
    have := hk i
    nlinarith
  omega

/-! ### The rectangular bound from compactness -/

/-- Every finite rectangle of mixed derivatives of a smooth function is bounded on the closed
box. -/
theorem exists_rect_bound {F : (Fin d → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F) (p : Fin d → ℕ) (b : ℝ) :
    ∃ M : ℝ, ∀ m : Fin d → ℕ, (∀ i, m i ≤ p i) → ∀ v : Fin d → ℝ, (∀ i, v i ∈ Icc 0 b) →
      |pdMulti m (List.finRange d) F v| ≤ M := by
  classical
  set S : Finset (Fin d → ℕ) := Fintype.piFinset fun i => Finset.range (p i + 1) with hS
  have hK : IsCompact (Set.pi univ fun _ : Fin d => Icc (0 : ℝ) b) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hbd : ∀ m : Fin d → ℕ, ∃ C : ℝ, ∀ v ∈ Set.pi univ fun _ : Fin d => Icc (0 : ℝ) b,
      ‖pdMulti m (List.finRange d) F v‖ ≤ C := fun m =>
    hK.exists_bound_of_continuousOn (contDiff_pdMulti hF m _).continuous.continuousOn
  choose C hC using hbd
  refine ⟨∑ m ∈ S, |C m|, fun m hm v hv => ?_⟩
  have hmS : m ∈ S := by
    rw [hS, Fintype.mem_piFinset]
    intro i
    exact Finset.mem_range.2 (Nat.lt_succ_of_le (hm i))
  have hv' : v ∈ Set.pi univ fun _ : Fin d => Icc (0 : ℝ) b := fun i _ => hv i
  calc |pdMulti m (List.finRange d) F v| ≤ C m := by
        have := hC m v hv'; rwa [Real.norm_eq_abs] at this
    _ ≤ |C m| := le_abs_self _
    _ ≤ ∑ m ∈ S, |C m| :=
        Finset.single_le_sum (fun m _ => abs_nonneg (C m)) hmS

/-! ### The expansion through every admissible cutoff -/

variable {F : (Fin d → ℝ) → ℝ} {h k : Fin d → ℕ} {β b : ℝ}

/-- ★★ **The expansion through the cutoff `L ≥ L₀`**, from smoothness alone. -/
theorem smooth_expansion_cutoff (hF : ContDiff ℝ ∞ F) (hk : ∀ i, 0 < k i) (hβ : 0 < β)
    (hb : 0 < b) {L : ℕ} (hL : L₀ h ≤ L) :
    ∃ K : ℝ, ∀ N : ℝ, 1 ≤ N →
      |smoothIntegral F h k β b N - absSpectralSum (Qamb k) (d - 1)
        (smoothCoeffAtDepth F h k (depthOf h k L) β b) L N| ≤
        K * (N ^ (-(L : ℝ)) * (1 + log N) ^ (d - 1)) := by
  obtain ⟨M, hM⟩ := exists_rect_bound hF (depthOf h k L) b
  have hL0 : 0 < L := lt_of_lt_of_le (by unfold L₀; omega) hL
  exact smooth_expansion_at_depth hF hk hβ hb hL0 (depthOf_add hk hL) (depthOf_pos hk hL) hM

/-- The cutoff used to define the coefficient at the exponent `μ`. -/
noncomputable def cutoffOf (h : Fin d → ℕ) (μ : ℝ) : ℕ := max (⌊μ⌋₊ + 1) (L₀ h)

theorem lt_cutoffOf (h : Fin d → ℕ) (μ : ℝ) : μ < cutoffOf h μ := by
  have h1 := Nat.lt_floor_add_one μ
  have h2 : ((⌊μ⌋₊ + 1 : ℕ) : ℝ) ≤ ((cutoffOf h μ : ℕ) : ℝ) := by
    exact_mod_cast (le_max_left _ _ : ⌊μ⌋₊ + 1 ≤ cutoffOf h μ)
  push_cast at h2
  exact lt_of_lt_of_le h1 h2

theorem L₀_le_cutoffOf (h : Fin d → ℕ) (μ : ℝ) : L₀ h ≤ cutoffOf h μ := le_max_right _ _

/-- ★★★ **The canonical smooth coefficients**: the depth-`2kL−h` coefficients at the deterministic
cutoff `L = max(⌊μ⌋₊ + 1, L₀)`. -/
noncomputable def smoothCoeff (F : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ) (β b : ℝ) (μ : ℝ)
    (q : ℕ) : ℝ :=
  smoothCoeffAtDepth F h k (depthOf h k (cutoffOf h μ)) β b μ q

/-- Two admissible cutoffs give the same coefficients below their common cutoff. -/
theorem smoothCoeffAtDepth_eq (hF : ContDiff ℝ ∞ F) (hk : ∀ i, 0 < k i) (hβ : 0 < β)
    (hb : 0 < b) {L L' : ℕ} (hL : L₀ h ≤ L) (hL' : L₀ h ≤ L') {μ : ℝ}
    (hμ : μ ∈ latticeBelow (Qamb k) L) (hμ' : μ ∈ latticeBelow (Qamb k) L') {q : ℕ}
    (hq : q ≤ d - 1) :
    smoothCoeffAtDepth F h k (depthOf h k L) β b μ q =
      smoothCoeffAtDepth F h k (depthOf h k L') β b μ q := by
  have hQ := Qamb_pos k hk
  obtain ⟨K₁, hK₁⟩ := smooth_expansion_cutoff hF hk hβ hb hL
  obtain ⟨K₂, hK₂⟩ := smooth_expansion_cutoff hF hk hβ hb hL'
  set L'' : ℝ := min (L : ℝ) (L' : ℝ) with hL''
  have h1 : L'' ≤ L := min_le_left _ _
  have h2 : L'' ≤ L' := min_le_right _ _
  obtain ⟨hm, hlt⟩ := (mem_latticeBelow_iff hQ).1 hμ
  have hlt' := ((mem_latticeBelow_iff hQ).1 hμ').2
  have hμ'' : μ ∈ latticeBelow (Qamb k) L'' :=
    (mem_latticeBelow_iff hQ).2 ⟨hm, lt_min hlt hlt'⟩
  refine finite_coeff_unique hQ (Z := smoothIntegral F h k β b) (L := L'')
    (K₁ := K₁ + ∑ ν ∈ latticeBelow (Qamb k) L, ∑ j ∈ range (d - 1 + 1),
      |smoothCoeffAtDepth F h k (depthOf h k L) β b ν j|)
    (K₂ := K₂ + ∑ ν ∈ latticeBelow (Qamb k) L', ∑ j ∈ range (d - 1 + 1),
      |smoothCoeffAtDepth F h k (depthOf h k L') β b ν j|) ?_ ?_ μ hμ'' q hq
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with N hN
    exact bound_lower_cutoff hQ h1 hN (hK₁ N hN)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with N hN
    exact bound_lower_cutoff hQ h2 hN (hK₂ N hN)

/-- The canonical coefficient agrees with every admissible depth below its cutoff. -/
theorem smoothCoeff_eq (hF : ContDiff ℝ ∞ F) (hk : ∀ i, 0 < k i) (hβ : 0 < β) (hb : 0 < b)
    {L : ℕ} (hL : L₀ h ≤ L) {μ : ℝ} (hμ : μ ∈ latticeBelow (Qamb k) L) {q : ℕ}
    (hq : q ≤ d - 1) :
    smoothCoeff F h k β b μ q = smoothCoeffAtDepth F h k (depthOf h k L) β b μ q := by
  have hQ := Qamb_pos k hk
  obtain ⟨hm, _⟩ := (mem_latticeBelow_iff hQ).1 hμ
  have hμc : μ ∈ latticeBelow (Qamb k) (cutoffOf h μ) :=
    (mem_latticeBelow_iff hQ).2 ⟨hm, lt_cutoffOf h μ⟩
  exact smoothCoeffAtDepth_eq hF hk hβ hb (L₀_le_cutoffOf h μ) hL hμc hμ hq

/-! ### The cutoff expansion -/

/-- ★★★ **The smooth-amplitude integral is a cutoff expansion** on the lattice `Q⁻¹ℕ`,
`Q = 2∏kᵢ`, with logarithmic degree `≤ d − 1` and the canonical coefficients `smoothCoeff`:
for every `L > 0` there is `K` with
`|∫_{(0,b]^d} F v^h e^{−Nβ v^{2k}} dv − ∑_{μ ∈ Λ^Q_L} N^{−μ} ∑_{q ≤ d−1} smoothCoeff μ q (log N)^q|`
`  ≤ K N^{−L} (1 + log N)^{d−1}` eventually in `N`. -/
theorem smooth_cutoffExpansion (hF : ContDiff ℝ ∞ F) (hk : ∀ i, 0 < k i) (hβ : 0 < β)
    (hb : 0 < b) :
    CutoffExpansion (Qamb k) (d - 1) (smoothIntegral F h k β b) (smoothCoeff F h k β b) := by
  intro L' hL'
  have hQ := Qamb_pos k hk
  set L : ℕ := max ⌈L'⌉₊ (L₀ h) with hLdef
  have hL : L₀ h ≤ L := le_max_right _ _
  have hLL : L' ≤ (L : ℝ) := by
    have h1 := Nat.le_ceil L'
    have h2 : ((⌈L'⌉₊ : ℕ) : ℝ) ≤ ((max ⌈L'⌉₊ (L₀ h) : ℕ) : ℝ) := by exact_mod_cast le_max_left _ _
    linarith
  obtain ⟨K, hK⟩ := smooth_expansion_cutoff hF hk hβ hb hL
  refine ⟨K + ∑ ν ∈ latticeBelow (Qamb k) L, ∑ j ∈ range (d - 1 + 1),
    |smoothCoeffAtDepth F h k (depthOf h k L) β b ν j|, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with N hN
  have hlow := bound_lower_cutoff hQ hLL hN (hK N hN)
  have hcoef : absSpectralSum (Qamb k) (d - 1) (smoothCoeff F h k β b) L' N =
      absSpectralSum (Qamb k) (d - 1) (smoothCoeffAtDepth F h k (depthOf h k L) β b) L' N := by
    unfold absSpectralSum
    refine Finset.sum_congr rfl fun μ hμ => ?_
    congr 1
    refine Finset.sum_congr rfl fun q hq => ?_
    have hμL : μ ∈ latticeBelow (Qamb k) L := latticeBelow_mono hQ hLL hμ
    rw [smoothCoeff_eq hF hk hβ hb hL hμL (Nat.lt_succ_iff.1 (Finset.mem_range.1 hq))]
  rw [hcoef]
  exact hlow

/-- ★★ **Canonicity**: any cutoff expansion of the smooth-amplitude integral on the lattice
`Q⁻¹ℕ` with logarithmic degree `≤ d − 1` has the coefficients `smoothCoeff`. -/
theorem smoothCoeff_unique (hF : ContDiff ℝ ∞ F) (hk : ∀ i, 0 < k i) (hβ : 0 < β) (hb : 0 < b)
    {c : ℝ → ℕ → ℝ} (hc : CutoffExpansion (Qamb k) (d - 1) (smoothIntegral F h k β b) c) {μ : ℝ}
    (hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb k) {j : ℕ} (hj : j ≤ d - 1) :
    c μ j = smoothCoeff F h k β b μ j :=
  CutoffExpansion.coeff_unique (Qamb_pos k hk) hc (smooth_cutoffExpansion hF hk hβ hb) hμ hj

end SmoothEngine

end Grammar
