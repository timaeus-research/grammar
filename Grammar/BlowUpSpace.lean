/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.BlowUpCubeCharts
import Grammar.ResolvedGeometry

/-!
# The blow-up of the origin as a genuine resolved space (B1)

The real blow-up of `ℝ^d` at the origin, presented as the tautological line bundle over the
projector model of `ℝP^{d−1}`:
`U = {(x, P) : P a rank-one orthogonal projector, P x = x}`, `π(x, P) = x`. The exceptional
divisor is `E = {(0, P)}`, a copy of the projector base; off `E` the map `π` is a bijection onto
`ℝ^d ∖ {0}`. The base is compact (the image of the unit sphere under `v ↦ v vᵀ`), so `π` is proper.

`blowUpGeometry d : ResolvedGeometry d (BlowUpSpace d)` has one divisor component with phase order
`k = 1` and Jacobian order `h = d − 1`, and resolves the radial phase `K(x) = |x|²`
(`isResolutionOf_K`). The blow-up charts `Ψ_β y = (φ_β y, P(dir_β y))` (with `dir_β y` the direction
vector `y` with `y_β` replaced by `1`) satisfy `π ∘ Ψ_β = φ_β`, the chart maps of the cube blow-up
(`π_Ψ`), and are continuous; they hit `E` exactly at `y_β = 0` (`Ψ_mem_E_iff`).

This replaces the `π = id` chart model of the cube blow-up (`BlowUpCubeChartModel`) by a genuine
resolved space with a collapsing `π`; the normal data and the transport of the chart certificates
follow in B2–B5.
-/

open Set Topology Filter

namespace Grammar

namespace BlowUpCube

variable {d : ℕ}

/-! ### The projector base -/

/-- The rank-one matrix `v vᵀ`; a projector when `|v| = 1`. -/
def rankOneProj (v : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun i j => v i * v j

theorem continuous_rankOneProj : Continuous (rankOneProj (d := d)) := by
  change Continuous fun v : Fin d → ℝ => (fun i j => v i * v j : Fin d → Fin d → ℝ)
  exact continuous_pi fun i => continuous_pi fun j => (continuous_apply i).mul (continuous_apply j)

theorem rankOneProj_mulVec (v x : Fin d → ℝ) :
    (rankOneProj v).mulVec x = (∑ j, v j * x j) • v := by
  funext i
  simp only [Matrix.mulVec, dotProduct, rankOneProj, Matrix.of_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The unit sphere `∑ v_k² = 1`. -/
def sphereSet (d : ℕ) : Set (Fin d → ℝ) := {v | ∑ k, v k ^ 2 = 1}

theorem isClosed_sphereSet : IsClosed (sphereSet d) :=
  isClosed_eq (continuous_finsetSum _ fun k _ => (continuous_apply k).pow 2) continuous_const

theorem sphereSet_subset_cube : sphereSet d ⊆ cube d := by
  intro v hv
  rw [mem_cube]
  intro j
  have h1 : v j ^ 2 ≤ ∑ k, v k ^ 2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg (v k)) (Finset.mem_univ j)
  rw [hv] at h1
  exact abs_le_one_iff_mul_self_le_one.2 (by nlinarith [h1])

theorem isCompact_sphereSet : IsCompact (sphereSet d) :=
  isCompact_cube.of_isClosed_subset isClosed_sphereSet sphereSet_subset_cube

/-- The projector base: the rank-one orthogonal projectors `v vᵀ`, `|v| = 1` (a model of
`ℝP^{d−1}`). -/
def projBase (d : ℕ) : Set (Matrix (Fin d) (Fin d) ℝ) := rankOneProj '' sphereSet d

theorem isCompact_projBase : IsCompact (projBase d) :=
  isCompact_sphereSet.image continuous_rankOneProj

instance : CompactSpace ↥(projBase d) := isCompact_iff_compactSpace.1 isCompact_projBase

/-! ### The blow-up space -/

/-- **The blow-up of the origin**: the tautological line bundle `{(x, P) : P x = x}` over the
projector base. -/
abbrev BlowUpSpace (d : ℕ) : Type :=
  {p : (Fin d → ℝ) × ↥(projBase d) // (p.2 : Matrix (Fin d) (Fin d) ℝ).mulVec p.1 = p.1}

instance : MeasurableSpace (Matrix (Fin d) (Fin d) ℝ) := borel _
instance : BorelSpace (Matrix (Fin d) (Fin d) ℝ) := ⟨rfl⟩

/-- The resolution map `π(x, P) = x`. -/
def π (p : BlowUpSpace d) : Fin d → ℝ := p.1.1

theorem continuous_π : Continuous (π (d := d)) := continuous_fst.comp continuous_subtype_val

theorem isClosed_blowUpSet : IsClosed {p : (Fin d → ℝ) × ↥(projBase d) |
    (p.2 : Matrix (Fin d) (Fin d) ℝ).mulVec p.1 = p.1} :=
  isClosed_eq ((continuous_subtype_val.comp continuous_snd).matrix_mulVec continuous_fst)
    continuous_fst

theorem isProperMap_π : IsProperMap (π (d := d)) :=
  isProperMap_fst_of_compactSpace.comp isClosed_blowUpSet.isClosedEmbedding_subtypeVal.isProperMap

/-- **The blow-up as a resolved geometry**: one divisor component `E = {x = 0}`, phase order
`k = 1`, Jacobian order `h = d − 1`. -/
noncomputable def blowUpGeometry (d : ℕ) : ResolvedGeometry d (BlowUpSpace d) where
  π := π
  continuous_π := continuous_π
  proper_π := isProperMap_π
  Component := Unit
  E := fun _ => {p | π p = 0}
  isClosed_E := fun _ => isClosed_eq continuous_π continuous_const
  k := fun _ => 1
  h := fun _ => d - 1
  k_pos := fun _ => one_pos

theorem blowUpGeometry_π (p : BlowUpSpace d) : (blowUpGeometry d).π p = π p := rfl

theorem mem_E_iff (p : BlowUpSpace d) (i : Unit) : p ∈ (blowUpGeometry d).E i ↔ π p = 0 := Iff.rfl

theorem K_eq_zero_iff (x : Fin d → ℝ) : K x = 0 ↔ x = 0 := by
  constructor
  · intro h
    funext i
    have := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => sq_nonneg (x k)).1 h i (Finset.mem_univ i)
    exact pow_eq_zero_iff two_ne_zero |>.1 this
  · rintro rfl
    simp [K]

/-- The blow-up resolves the radial phase `K(x) = |x|²`: `K ∘ π` vanishes exactly on `E`. -/
theorem isResolutionOf_K : (blowUpGeometry d).IsResolutionOf K := by
  intro p
  rw [ResolvedGeometry.divisor, mem_iUnion, blowUpGeometry_π, K_eq_zero_iff]
  exact ⟨fun h => ⟨(), h⟩, fun ⟨_, h⟩ => h⟩

/-! ### The blow-up charts -/

/-- The direction vector of the chart `β`: `y` with its `β`-coordinate replaced by `1`. -/
def dir (β : Fin d) (y : Fin d → ℝ) : Fin d → ℝ := Function.update y β 1

theorem dir_self (β : Fin d) (y : Fin d → ℝ) : dir β y β = 1 := Function.update_self _ _ _

theorem dir_other (β : Fin d) (y : Fin d → ℝ) {γ : Fin d} (hγ : γ ≠ β) : dir β y γ = y γ :=
  Function.update_of_ne hγ _ _

theorem continuous_dir (β : Fin d) : Continuous (dir β) :=
  continuous_pi fun γ => by
    by_cases hγ : γ = β
    · subst hγ
      simp only [dir_self]
      exact continuous_const
    · simp only [dir_other β _ hγ]
      exact continuous_apply γ

theorem φ_eq_smul_dir (β : Fin d) (y : Fin d → ℝ) : φ β y = y β • dir β y := by
  funext γ
  by_cases hγ : γ = β
  · subst hγ
    simp [φ_self, dir_self]
  · simp [φ_other β y hγ, dir_other β y hγ]

/-- The squared length of the direction vector, `1 + ∑_{γ≠β} y_γ²` (the chart unit). -/
theorem sum_sq_dir (β : Fin d) (y : Fin d → ℝ) : ∑ k, dir β y k ^ 2 = unit β y := by
  unfold unit
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ β), dir_self, one_pow]
  congr 1
  refine Finset.sum_congr rfl fun γ hγ => ?_
  rw [dir_other β y (Finset.ne_of_mem_erase hγ)]

/-- The normalised direction. -/
noncomputable def udir (β : Fin d) (y : Fin d → ℝ) : Fin d → ℝ :=
  fun k => dir β y k / Real.sqrt (unit β y)

theorem udir_mem_sphereSet (β : Fin d) (y : Fin d → ℝ) : udir β y ∈ sphereSet d := by
  have hu := unit_pos β y
  change ∑ k, (dir β y k / Real.sqrt (unit β y)) ^ 2 = 1
  simp_rw [div_pow, Real.sq_sqrt hu.le, ← Finset.sum_div, sum_sq_dir]
  exact div_self hu.ne'

theorem continuous_udir (β : Fin d) : Continuous (udir β) :=
  continuous_pi fun k => ((continuous_apply k).comp (continuous_dir β)).div
    ((continuous_unit β).sqrt) fun y => (Real.sqrt_pos.2 (unit_pos β y)).ne'

/-- The chart projector `P(dir_β y) = u uᵀ`, `u = dir_β y / |dir_β y|`. -/
noncomputable def chartProj (β : Fin d) (y : Fin d → ℝ) : ↥(projBase d) :=
  ⟨rankOneProj (udir β y), ⟨udir β y, udir_mem_sphereSet β y, rfl⟩⟩

theorem continuous_chartProj (β : Fin d) : Continuous (chartProj β) :=
  Continuous.subtype_mk (continuous_rankOneProj.comp (continuous_udir β)) _

theorem chartProj_mulVec_φ (β : Fin d) (y : Fin d → ℝ) :
    (chartProj β y : Matrix (Fin d) (Fin d) ℝ).mulVec (φ β y) = φ β y := by
  have hu := unit_pos β y
  have hs : Real.sqrt (unit β y) ≠ 0 := (Real.sqrt_pos.2 hu).ne'
  change (rankOneProj (udir β y)).mulVec (φ β y) = φ β y
  rw [rankOneProj_mulVec, φ_eq_smul_dir]
  have h : ∑ j, udir β y j * (y β • dir β y) j = y β * Real.sqrt (unit β y) := by
    simp only [udir, Pi.smul_apply, smul_eq_mul]
    have : ∀ j, dir β y j / Real.sqrt (unit β y) * (y β * dir β y j) =
        y β / Real.sqrt (unit β y) * dir β y j ^ 2 := fun j => by ring
    simp_rw [this, ← Finset.mul_sum, sum_sq_dir]
    field_simp
    rw [Real.sq_sqrt hu.le]
  rw [h]
  funext k
  simp only [udir, Pi.smul_apply, smul_eq_mul]
  field_simp

/-- **The blow-up chart** `Ψ_β y = (φ_β y, P(dir_β y))`. -/
noncomputable def Ψ (β : Fin d) (y : Fin d → ℝ) : BlowUpSpace d :=
  ⟨(φ β y, chartProj β y), chartProj_mulVec_φ β y⟩

@[simp] theorem π_Ψ (β : Fin d) (y : Fin d → ℝ) : π (Ψ β y) = φ β y := rfl

theorem continuous_Ψ (β : Fin d) : Continuous (Ψ β) :=
  Continuous.subtype_mk ((continuous_φ β).prodMk (continuous_chartProj β)) _

theorem measurable_Ψ (β : Fin d) : Measurable (Ψ β) := (continuous_Ψ β).measurable

theorem φ_eq_zero_iff (β : Fin d) (y : Fin d → ℝ) : φ β y = 0 ↔ y β = 0 := by
  constructor
  · intro h
    have := congrFun h β
    rwa [φ_self] at this
  · intro h
    rw [φ_eq_smul_dir, h, zero_smul]

/-- The chart meets the exceptional divisor exactly along `y_β = 0`. -/
theorem Ψ_mem_E_iff (β : Fin d) (y : Fin d → ℝ) (i : Unit) :
    Ψ β y ∈ (blowUpGeometry d).E i ↔ y β = 0 := by
  rw [mem_E_iff, π_Ψ, φ_eq_zero_iff]

/-- Off the divisor `π` is injective: a rank-one projector fixing `x ≠ 0` is `x xᵀ/|x|²`. -/
theorem rankOneProj_eq_of_mulVec_eq {v x : Fin d → ℝ} (hv : v ∈ sphereSet d) (hx : x ≠ 0)
    (hvx : (rankOneProj v).mulVec x = x) :
    rankOneProj v = Matrix.of fun i j => x i * x j / ∑ k, x k ^ 2 := by
  rw [rankOneProj_mulVec] at hvx
  have hc0 : (∑ j, v j * x j) ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hvx
    exact hx hvx.symm
  have hv' : v = (∑ j, v j * x j)⁻¹ • x := by
    calc v = (∑ j, v j * x j)⁻¹ • ((∑ j, v j * x j) • v) := by
          rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
      _ = (∑ j, v j * x j)⁻¹ • x := by rw [hvx]
  have hsum : ∑ k, x k ^ 2 = (∑ j, v j * x j) ^ 2 := by
    have h1 : ∑ k, v k ^ 2 = 1 := hv
    rw [hv'] at h1
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum] at h1
    field_simp at h1
    linarith
  ext i j
  rw [rankOneProj, Matrix.of_apply, Matrix.of_apply, hsum]
  conv_lhs => rw [hv']
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp

theorem π_injective_of_ne_zero {p q : BlowUpSpace d} (hp : π p ≠ 0) (h : π p = π q) : p = q := by
  obtain ⟨⟨x, ⟨P, ⟨u, hu, rfl⟩⟩⟩, hpx⟩ := p
  obtain ⟨⟨x', ⟨P', ⟨u', hu', rfl⟩⟩⟩, hqx⟩ := q
  change x ≠ 0 at hp
  change x = x' at h
  subst h
  have := (rankOneProj_eq_of_mulVec_eq hu hp hpx).trans
    (rankOneProj_eq_of_mulVec_eq hu' hp hqx).symm
  exact Subtype.ext (Prod.ext rfl (Subtype.ext this))

end BlowUpCube

end Grammar
