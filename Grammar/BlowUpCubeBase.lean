/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.BlowUpCubeMeasure
import Grammar.BlowUpNormalData

/-!
# The piece bases on the exceptional divisor and the transported frames (B4b)

Each piece `(β, σ)` of the cube blow-up has its base on the closed chart face `{y_β = 0} ∩ [0,1]^d`.
The piece chart `Ψ_β ∘ R_σ` maps this face injectively into the exceptional divisor
`E = S_{univ}` of the genuine blow-up (`baseMap`, `baseMap_injective`), hence homeomorphically onto
its compact image `baseSet` (`baseHomeo`). At a transported base point the chart's normal
coordinate `t ↦ Ψ_β(R_σ(y + t e_β))` is the fibre translation along the direction
`dir_β(R_σ y)`, which spans the normal line (`dir_mem_normalLine`); the frame
`u ↦ (sgn_σ(β) λ(y) u) • dir_β(R_σ y)` identifies the box normal coordinate with the normal space
(`frame`), and the chart core map is the genuine tubular germ along it (`Ψ_Φ_eq_tubular`).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

namespace BlowUpCube

open WaterFilling SingletonChart NormalisedBox CoordModel

variable {d : ℕ} (β : Fin d) (σ : CoordSign d)

/-! ### The piece base and its image in the divisor -/

/-- The piece base: the closed face `{y_β = 0} ∩ [0,1]^d` of the chart (a compact subtype of the
chart stratum). -/
abbrev PieceBase := SingletonChart.K β 1 (d - 1)

theorem pieceBase_coord (s : PieceBase β) : (s.1 : Fin d → ℝ) β = 0 :=
  stratum_coord_zero β (d - 1) s.1

theorem pieceBase_mem_box (s : PieceBase β) : (s.1 : Fin d → ℝ) ∈ piBox d (Icc 0 1) := s.2.1

instance : CompactSpace (PieceBase β) := isCompact_iff_compactSpace.1 (isCompact_base β 1 (d - 1))

/-- The transported base point `Ψ_β(R_σ y)` on the exceptional divisor. -/
noncomputable def baseMap (s : PieceBase β) : (blowUpGeometry d).Stratum Finset.univ :=
  ⟨Ψ β (refl σ s.1.1), fun i => by
    simp only [Finset.mem_univ, iff_true]
    exact (Ψ_mem_E_iff β _ i).2 (by rw [refl_apply, pieceBase_coord, mul_zero])⟩

theorem baseMap_val (s : PieceBase β) : (baseMap β σ s : BlowUpSpace d) = Ψ β (refl σ s.1.1) := rfl

theorem continuous_baseMap : Continuous (baseMap β σ) :=
  Continuous.subtype_mk ((continuous_Ψ β).comp ((continuous_refl σ).comp
    (continuous_subtype_val.comp continuous_subtype_val))) _

/-- Two direction vectors with the same normalised direction agree. -/
theorem dir_eq_of_udir_eq {v v' : Fin d → ℝ} (h : udir β v = udir β v') : dir β v = dir β v' := by
  have hu : 0 < unit β v := unit_pos β v
  have hu' : 0 < unit β v' := unit_pos β v'
  have hβ := congrFun h β
  simp only [udir, dir_self] at hβ
  have hs : Real.sqrt (unit β v) = Real.sqrt (unit β v') := by
    have h1 : (Real.sqrt (unit β v))⁻¹ = (Real.sqrt (unit β v'))⁻¹ := by
      simpa using hβ
    exact inv_inj.1 h1
  funext j
  have hj := congrFun h j
  simp only [udir] at hj
  rw [hs] at hj
  exact (div_left_inj' (Real.sqrt_pos.2 hu').ne').1 hj

/-- Two unit vectors with positive `β`-coordinate and the same rank-one projector agree. -/
theorem eq_of_rankOneProj_eq {u u' : Fin d → ℝ} (h : rankOneProj u = rankOneProj u')
    (hu : 0 < u β) (hu' : 0 < u' β) : u = u' := by
  have hentry : ∀ i j, u i * u j = u' i * u' j := fun i j => by
    have := congrFun (congrFun h i) j
    simpa [rankOneProj] using this
  have hββ : u β = u' β := by
    have := hentry β β
    nlinarith [this, hu, hu']
  funext j
  have := hentry β j
  rw [hββ] at this
  exact mul_left_cancel₀ hu'.ne' this

theorem udir_β_pos (v : Fin d → ℝ) : 0 < udir β v β := by
  simp only [udir, dir_self]
  exact div_pos one_pos (Real.sqrt_pos.2 (unit_pos β v))

/-- The chart projector determines the direction vector. -/
theorem dir_eq_of_chartProj_eq {v v' : Fin d → ℝ} (h : chartProj β v = chartProj β v') :
    dir β v = dir β v' := by
  have h' : rankOneProj (udir β v) = rankOneProj (udir β v') := congrArg Subtype.val h
  exact dir_eq_of_udir_eq β (eq_of_rankOneProj_eq β h' (udir_β_pos β v) (udir_β_pos β v'))

theorem baseMap_injective : Function.Injective (baseMap β σ) := by
  intro s s' h
  have h2 : chartProj β (refl σ s.1.1) = chartProj β (refl σ s'.1.1) :=
    congrArg (fun q : BlowUpSpace d => q.1.2) (congrArg Subtype.val h)
  have hdir := dir_eq_of_chartProj_eq β h2
  have hy : (s.1 : Fin d → ℝ) = s'.1 := by
    funext j
    by_cases hj : j = β
    · subst hj
      rw [pieceBase_coord, pieceBase_coord]
    · have := congrFun hdir j
      rw [dir_other β _ hj, dir_other β _ hj, refl_apply, refl_apply] at this
      have hsgn : WaterFilling.sgn σ j ≠ 0 := by
        have := WaterFilling.abs_sgn σ j
        intro h0
        rw [h0, abs_zero] at this
        exact zero_ne_one this
      exact mul_left_cancel₀ hsgn this
  exact Subtype.ext (Subtype.ext hy)

/-- The compact image of the piece base on the divisor. -/
def baseSet : Set ((blowUpGeometry d).Stratum Finset.univ) := Set.range (baseMap β σ)

theorem isCompact_baseSet : IsCompact (baseSet β σ) := isCompact_range (continuous_baseMap β σ)

/-- The piece base is homeomorphic to its image on the divisor. -/
noncomputable def baseHomeo : PieceBase β ≃ₜ ↥(baseSet β σ) :=
  ((continuous_baseMap β σ).isClosedEmbedding (baseMap_injective β σ)).isEmbedding.toHomeomorph

theorem baseHomeo_apply_coe (s : PieceBase β) : ((baseHomeo β σ s : ↥(baseSet β σ)) :
    (blowUpGeometry d).Stratum Finset.univ) = baseMap β σ s := rfl

theorem baseHomeo_symm_spec (s : ↥(baseSet β σ)) :
    baseMap β σ ((baseHomeo β σ).symm s) = s.1 := by
  have := baseHomeo_apply_coe β σ ((baseHomeo β σ).symm s)
  rw [Homeomorph.apply_symm_apply] at this
  exact this.symm

/-! ### The direction spans the normal line -/

/-- A vector fixed by the projector of a divisor point lies in its normal line. -/
theorem mem_normalLine_of_mulVec {I : Finset Unit} (hI : I.Nonempty) (s : BlowUpSpace d)
    {w : EuclideanSpace ℝ (Fin d)}
    (hw : (projOf s : Matrix (Fin d) (Fin d) ℝ).mulVec w.ofLp = w.ofLp) : w ∈ normalLine I s := by
  rw [normalLine_of_nonempty hI, Submodule.mem_span_singleton]
  refine ⟨∑ j, dirOf (projOf s) j * w.ofLp j, ?_⟩
  have h := hw
  rw [← rankOneProj_dirOf, rankOneProj_mulVec] at h
  rw [edir, ← WithLp.toLp_smul, h, WithLp.toLp_ofLp]

/-- The chart projector fixes the direction vector. -/
theorem chartProj_mulVec_dir (v : Fin d → ℝ) :
    (chartProj β v : Matrix (Fin d) (Fin d) ℝ).mulVec (dir β v) = dir β v := by
  have hu := unit_pos β v
  have hs : Real.sqrt (unit β v) ≠ 0 := (Real.sqrt_pos.2 hu).ne'
  change (rankOneProj (udir β v)).mulVec (dir β v) = dir β v
  rw [rankOneProj_mulVec]
  have h : ∑ j, udir β v j * dir β v j = Real.sqrt (unit β v) := by
    simp only [udir]
    have : ∀ j, dir β v j / Real.sqrt (unit β v) * dir β v j =
        dir β v j ^ 2 / Real.sqrt (unit β v) := fun j => by ring
    simp_rw [this, ← Finset.sum_div, sum_sq_dir]
    field_simp
    exact (Real.sq_sqrt hu.le).symm
  rw [h]
  funext k
  simp only [udir, Pi.smul_apply, smul_eq_mul]
  field_simp

theorem dir_mem_normalLine (s : PieceBase β) :
    WithLp.toLp 2 (dir β (refl σ s.1.1)) ∈ normalLine Finset.univ (baseMap β σ s).1 :=
  mem_normalLine_of_mulVec Finset.univ_nonempty _ (chartProj_mulVec_dir β _)

/-! ### The frames -/

/-- The direction vector as an element of the normal line. -/
noncomputable def dirVec (s : PieceBase β) : normalLine Finset.univ (baseMap β σ s).1 :=
  ⟨WithLp.toLp 2 (dir β (refl σ s.1.1)), dir_mem_normalLine β σ s⟩

theorem dirVec_ne_zero (s : PieceBase β) : dirVec β σ s ≠ 0 := by
  intro h
  have := congrArg (fun w : normalLine Finset.univ (baseMap β σ s).1 =>
    (w : EuclideanSpace ℝ (Fin d)).ofLp β) h
  simp [dirVec, dir_self] at this

theorem sgn_ne_zero (i : Fin d) : WaterFilling.sgn σ i ≠ 0 := by
  intro h
  have := WaterFilling.abs_sgn σ i
  rw [h, abs_zero] at this
  exact zero_ne_one this

/-- The frame scale `sgn_σ(β) λ(y)`, `λ(y) = (√unit_β(y))⁻¹`. -/
noncomputable def frameScale (s : PieceBase β) : ℝ :=
  WaterFilling.sgn σ β * lamS β (unit β) 1 (d - 1) s

theorem frameScale_ne_zero (s : PieceBase β) : frameScale β σ s ≠ 0 :=
  mul_ne_zero (sgn_ne_zero σ β)
    (lamS_pos β (unit β) 1 (d - 1) one_pos 1 one_pos (fun y _ => one_le_unit β y) s).ne'

/-- The frame linear map `u ↦ (sgn_σ(β) λ(y) u₀) • dir_β(R_σ y)`. -/
noncomputable def frameLin (s : PieceBase β) :
    (Fin (nI (Iβ β) + 1) → ℝ) →ₗ[ℝ] normalLine Finset.univ (baseMap β σ s).1 :=
  frameScale β σ s •
    (LinearMap.proj 0 : (Fin (nI (Iβ β) + 1) → ℝ) →ₗ[ℝ] ℝ).smulRight (dirVec β σ s)

theorem fin_nI_eq_zero (i : Fin (nI (Iβ β) + 1)) : i = 0 :=
  Fin.ext (by have := i.isLt; have := nI_Iβ β; omega)

theorem frameLin_apply (s : PieceBase β) (u : Fin (nI (Iβ β) + 1) → ℝ) :
    frameLin β σ s u = (frameScale β σ s * u 0) • dirVec β σ s := by
  simp [frameLin, LinearMap.smulRight_apply, mul_smul]

theorem frameLin_injective (s : PieceBase β) : Function.Injective (frameLin β σ s) := by
  intro u u' h
  rw [frameLin_apply, frameLin_apply] at h
  have h1 : (frameScale β σ s * u 0 - frameScale β σ s * u' 0) • dirVec β σ s = 0 := by
    rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.1 h1 with h1 | h1
  · have hu := mul_left_cancel₀ (frameScale_ne_zero β σ s) (sub_eq_zero.1 h1)
    funext i
    rw [fin_nI_eq_zero β i]
    exact hu
  · exact absurd h1 (dirVec_ne_zero β σ s)

theorem finrank_normalLine_univ (s : BlowUpSpace d) :
    Module.finrank ℝ (normalLine Finset.univ s) = 1 := by
  rw [finrank_normalLine, Finset.card_univ, Fintype.card_unit]

/-- **The frame** `ℝ ≃L N_s` at a transported piece base point. -/
noncomputable def frame (s : PieceBase β) :
    (Fin (nI (Iβ β) + 1) → ℝ) ≃L[ℝ] normalLine Finset.univ (baseMap β σ s).1 :=
  (LinearEquiv.ofBijective (frameLin β σ s) ⟨frameLin_injective β σ s,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [Module.finrank_fin_fun, finrank_normalLine_univ, nI_Iβ])).1
      (frameLin_injective β σ s)⟩).toContinuousLinearEquiv

theorem frame_apply (s : PieceBase β) (u : Fin (nI (Iβ β) + 1) → ℝ) :
    (frame β σ s u : EuclideanSpace ℝ (Fin d)) =
      WithLp.toLp 2 ((frameScale β σ s * u 0) • dir β (refl σ s.1.1)) := by
  change ((frameLin β σ s u : normalLine Finset.univ (baseMap β σ s).1) :
    EuclideanSpace ℝ (Fin d)) = _
  rw [frameLin_apply, Submodule.coe_smul, WithLp.toLp_smul]
  rfl

/-! ### The chart core map is the tubular germ along the frame -/

theorem dir_update (v : Fin d → ℝ) (t : ℝ) : dir β (Function.update v β t) = dir β v := by
  unfold dir
  rw [Function.update_idem]

theorem unit_update (v : Fin d → ℝ) (t : ℝ) : unit β (Function.update v β t) = unit β v :=
  unit_indep β fun _ hγ => Function.update_of_ne hγ _ _

theorem chartProj_update (v : Fin d → ℝ) (t : ℝ) :
    chartProj β (Function.update v β t) = chartProj β v := by
  apply Subtype.ext
  change rankOneProj (udir β _) = rankOneProj (udir β v)
  congr 1
  funext k
  simp only [udir, dir_update, unit_update]

theorem refl_update (v : Fin d → ℝ) (t : ℝ) :
    refl σ (Function.update v β t) = Function.update (refl σ v) β (WaterFilling.sgn σ β * t) := by
  funext j
  rw [refl_apply]
  by_cases hj : j = β
  · subst hj
    simp
  · rw [Function.update_of_ne hj, Function.update_of_ne hj, refl_apply]

/-- The chart core map in the singleton chart: the face point with normal coordinate `λ(y) u₀`. -/
theorem Φ_eq_update (s : PieceBase β) (u : Fin (nI (Iβ β) + 1) → ℝ) :
    NormalisedBox.Φ (Iβ β).1 (σI (Iβ β)) (e β 1 (d - 1)) (lam β (unit β)) (s, u) =
      Function.update (s.1 : Fin d → ℝ) β (lamS β (unit β) 1 (d - 1) s * u 0) := by
  rw [Φ_eq_orig]
  funext j
  unfold originalNormalMap
  by_cases hj : j ∈ (Iβ β).1
  · have hjβ : j = β := Finset.mem_singleton.1 hj
    subst hjβ
    rw [dif_pos hj, Function.update_self, pieceBase_coord, zero_add,
      fin_nI_eq_zero j ((σI (Iβ j)).symm ⟨j, hj⟩)]
    rfl
  · have hjβ : j ≠ β := fun h => hj (h ▸ Finset.mem_singleton_self β)
    rw [dif_neg hj, Function.update_of_ne hjβ]

/-- ★ **The transported chart core map is the tubular germ along the frame**:
`Ψ_β(R_σ(Φ(s, u))) = Φ_{(baseMap s)}(frame s u)`. -/
theorem Ψ_Φ_eq_tubular (s : PieceBase β) (u : Fin (nI (Iβ β) + 1) → ℝ) :
    Ψ β (WaterFilling.refl σ
      (NormalisedBox.Φ (Iβ β).1 (σI (Iβ β)) (e β 1 (d - 1)) (lam β (unit β)) (s, u))) =
      tubular Finset.univ (baseMap β σ s).1 (frame β σ s u) := by
  rw [Φ_eq_update, refl_update]
  apply Subtype.ext
  apply Prod.ext
  · change φ β (Function.update (refl σ s.1.1) β _) =
      π (baseMap β σ s).1 + (frame β σ s u : EuclideanSpace ℝ (Fin d)).ofLp
    rw [φ_eq_smul_dir, dir_update, Function.update_self, frame_apply, baseMap_val, π_Ψ,
      φ_eq_smul_dir, refl_apply, pieceBase_coord, mul_zero, zero_smul, zero_add,
      WithLp.ofLp_toLp]
    unfold frameScale
    rw [mul_assoc]
  · change chartProj β (Function.update (refl σ s.1.1) β _) = chartProj β (refl σ s.1.1)
    exact chartProj_update β _ _

end BlowUpCube

end Grammar
