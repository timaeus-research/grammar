/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.EmpiricalFaceKernel
import Grammar.SmoothGeneralDepth

/-!
# The empirical inner kernel on a general finite index type (§20 Stage 5, part 1)

`empFaceInner k e G t = ∫_{(0,1]^ι} u^e G(√t u^k) e^{−t u^{2k}} du` on an arbitrary finite index
type `ι` — the inner integral of a face `J` of the box, `ι = {i // i ∈ J}`. On `Fin (n+1)` it is
`empUnitInner` (`empFaceInner_fin`), it is invariant under reindexing (`empFaceInner_reindex`,
transport along `piCongrLeft`), and on the EMPTY index type it is `G(√t) e^{−t}`
(`empFaceInner_isEmpty`). The two-regime estimate of `EmpiricalInnerTwoRegime` transports to every
nonempty `ι` (★ `empFaceInner_two_regime`) with spectrum `faceSpectrum k e L ⊆ (2∏kᵢ)⁻¹ℕ ∩ [0,L)`
and coefficients `faceInnerCoeff k e G` (linear in `G`, bounded by `A` times a constant, vanishing
off the spectrum); on the empty type the estimate holds with EMPTY spectrum
(`empFaceInner_isEmpty_two_regime`, from the master kernel bound `jet_kernel_le`). Measurability in
an outer parameter is transported as well. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Finset

namespace Grammar

namespace SmoothEngine

variable {ι : Type*} [Fintype ι]

/-! ### The kernel on a general index type -/

/-- The empirical inner kernel on the unit box `(0,1]^ι`. -/
noncomputable def empFaceInner (k e : ι → ℕ) (G : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u in box ι 1, mono e u * (G (Real.sqrt t * mono k u) * exp (-t * mono (fun i => 2 * k i) u))

theorem empFaceInner_fin {n : ℕ} (k e : Fin (n + 1) → ℕ) (G : ℝ → ℝ) (t : ℝ) :
    empFaceInner k e G t = empUnitInner k e G t := rfl

/-- Reindexing the kernel along an equivalence of index types. -/
theorem empFaceInner_reindex {κ : Type*} [Fintype κ] (σ : ι ≃ κ) (k e : ι → ℕ) (G : ℝ → ℝ)
    (t : ℝ) : empFaceInner k e G t = empFaceInner (k ∘ σ.symm) (e ∘ σ.symm) G t := by
  have hmp : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : κ => ℝ) σ) volume volume :=
    volume_measurePreserving_piCongrLeft (fun _ : κ => ℝ) σ
  have hpre : MeasurableEquiv.piCongrLeft (fun _ : κ => ℝ) σ ⁻¹' box κ 1 = box ι 1 := by
    rw [box, box, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_preimage_univ_pi]
  have hmono : ∀ (a : κ → ℕ) (x : ι → ℝ),
      mono a (MeasurableEquiv.piCongrLeft (fun _ : κ => ℝ) σ x) = mono (a ∘ σ) x := by
    intro a x
    unfold mono
    rw [← Equiv.prod_comp σ]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Function.comp_apply, MeasurableEquiv.piCongrLeft_apply_apply]
  have he : (e ∘ σ.symm) ∘ σ = e := by funext i; simp
  have hk : (k ∘ σ.symm) ∘ σ = k := by funext i; simp
  have hk2 : (fun j => 2 * (k ∘ σ.symm) j) ∘ σ = fun i => 2 * k i := by funext i; simp
  have h := hmp.setIntegral_preimage_emb
    (MeasurableEquiv.piCongrLeft (fun _ : κ => ℝ) σ).measurableEmbedding
    (fun v => mono (e ∘ σ.symm) v *
      (G (Real.sqrt t * mono (k ∘ σ.symm) v) * exp (-t * mono (fun j => 2 * (k ∘ σ.symm) j) v)))
    (box κ 1)
  rw [hpre] at h
  unfold empFaceInner
  rw [← h]
  refine setIntegral_congr_fun (measurableSet_box 1) fun x _ => ?_
  simp only [hmono, he, hk, hk2]

/-- On the empty index type the kernel is `G(√t) e^{−t}`. -/
theorem empFaceInner_isEmpty [IsEmpty ι] (k e : ι → ℕ) (G : ℝ → ℝ) (t : ℝ) :
    empFaceInner k e G t = G (Real.sqrt t) * exp (-t) := by
  unfold empFaceInner
  rw [box_isEmpty, Measure.restrict_univ]
  simp only [mono_isEmpty, one_mul, mul_one]
  rw [integral_const, smul_eq_mul, Measure.real, volume_pi, Measure.pi_univ]
  simp

/-! ### Spectrum and coefficients on a nonempty index type -/

/-- The face spectrum below the cutoff, through the reindexing `faceEquiv`. -/
noncomputable def faceSpectrum [Nonempty ι] (k e : ι → ℕ) (L : ℝ) : Finset ℝ :=
  innerSpectrumBelow (k ∘ (faceEquiv ι).symm) (e ∘ (faceEquiv ι).symm) L

/-- The face coefficient system, through the reindexing `faceEquiv`. -/
noncomputable def faceInnerCoeff [Nonempty ι] (k e : ι → ℕ) (G : ℝ → ℝ) : ℝ → ℕ → ℝ :=
  empInnerCoeff (k ∘ (faceEquiv ι).symm) (e ∘ (faceEquiv ι).symm) G

/-- ★ The two-regime estimate on a nonempty index type: constant depending on
`(k, e, m, M', L)`, remainder linear in the growth constant. -/
theorem empFaceInner_two_regime [Nonempty ι] (k e : ι → ℕ) (hk : ∀ i, 0 < k i) (m : ℕ) (M' : ℝ)
    {L : ℝ} (hL : 0 < L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (G : ℝ → ℝ), Measurable G → ∀ (A : ℝ), GrowthLE G A m M' →
      ∀ t : ℝ, 0 < t →
        |empFaceInner k e G t -
            powLog (faceSpectrum k e L) (Fintype.card ι - 1) (faceInnerCoeff k e G) t| ≤
          A * C * (t ^ (-L) * (1 + |log t|) ^ (Fintype.card ι - 1)) := by
  obtain ⟨C, hC0, hC⟩ := empUnitInner_two_regime (k ∘ (faceEquiv ι).symm)
    (e ∘ (faceEquiv ι).symm) (fun _ => hk _) m M' hL
  refine ⟨C, hC0, fun G hGm A hG t ht => ?_⟩
  rw [empFaceInner_reindex (faceEquiv ι)]
  exact hC G hGm A hG t ht

theorem mem_faceSpectrum_le [Nonempty ι] (k e : ι → ℕ) {L μ : ℝ} (hμ : μ ∈ faceSpectrum k e L) :
    μ ≤ L :=
  (Finset.mem_filter.1 hμ).2.le

theorem mem_faceSpectrum_pos [Nonempty ι] (k e : ι → ℕ) (hk : ∀ i, 0 < k i) {L μ : ℝ}
    (hμ : μ ∈ faceSpectrum k e L) : 0 < μ :=
  mem_innerSpectrum_pos _ _ (fun _ => hk _) (Finset.mem_filter.1 hμ).1

/-- The face coefficients are bounded by `A` times a constant depending on `(k, e, m, M')`. -/
theorem abs_faceInnerCoeff_le [Nonempty ι] (k e : ι → ℕ) (hk : ∀ i, 0 < k i) {G : ℝ → ℝ}
    {A : ℝ} {m : ℕ} {M' : ℝ} (hG : GrowthLE G A m M') {L μ : ℝ} (hμ : μ ∈ faceSpectrum k e L)
    {q : ℕ} (hq : q ∈ range (Fintype.card ι - 1 + 1)) :
    |faceInnerCoeff k e G μ q| ≤
      A * innerCoeffTotal (k ∘ (faceEquiv ι).symm) (e ∘ (faceEquiv ι).symm) m M' := by
  have hμ' := Finset.mem_filter.1 hμ
  have hμ0 : 0 < μ := mem_innerSpectrum_pos _ _ (fun _ => hk _) hμ'.1
  calc |faceInnerCoeff k e G μ q|
      ≤ A * innerCoeffBound (k ∘ (faceEquiv ι).symm) (e ∘ (faceEquiv ι).symm) m M' μ q :=
        abs_empInnerCoeff_le _ _ hG hμ0 q
    _ ≤ _ := mul_le_mul_of_nonneg_left (innerCoeffBound_le_total _ _ m M' hμ'.1 hq) hG.nonneg

/-- The face coefficients vanish off the face spectrum (among exponents below the cutoff). -/
theorem faceInnerCoeff_eq_zero [Nonempty ι] (k e : ι → ℕ) (G : ℝ → ℝ) {L μ : ℝ} (hμL : μ < L)
    (hμ : μ ∉ faceSpectrum k e L) (q : ℕ) : faceInnerCoeff k e G μ q = 0 := by
  have hnot : μ ∉ innerSpectrum (k ∘ (faceEquiv ι).symm) (e ∘ (faceEquiv ι).symm) := fun h =>
    hμ (Finset.mem_filter.2 ⟨h, hμL⟩)
  unfold faceInnerCoeff empInnerCoeff
  rw [Finset.sum_eq_zero fun j _ => ?_, mul_zero]
  rw [coeffAt_eq_zero_of_not_mem _ hnot j, zero_mul, zero_mul]

/-- The face spectrum lies in the lattice `(2∏ᵢ kᵢ)⁻¹ ℕ` below `L`. -/
theorem faceSpectrum_subset [Nonempty ι] (k e : ι → ℕ) (hk : ∀ i, 0 < k i) (L : ℝ) :
    faceSpectrum k e L ⊆ latticeBelow (2 * ∏ i, k i) L := by
  intro μ hμ
  have hμ' := Finset.mem_filter.1 hμ
  have hQ : 0 < 2 * ∏ i, k i := Nat.mul_pos two_pos (Finset.prod_pos fun i _ => hk i)
  set k' := k ∘ (faceEquiv ι).symm with hk'
  set e' := e ∘ (faceEquiv ι).symm with he'
  -- `μ = (e'_j + 1) / (2 k'_j)` for some `j`
  have hmem := hμ'.1
  unfold innerSpectrum at hmem
  rw [List.mem_toFinset, List.mem_map] at hmem
  obtain ⟨en, hen, rfl⟩ := hmem
  obtain ⟨j, hj⟩ := stateDensityRep_exponent_mem _ (sdWeights k' e') en hen
  rw [hj] at hμ' ⊢
  have hsd : sdWeights k' e' j + 1 = ((e' j : ℝ) + 1) / (2 * (k' j : ℝ)) := by
    unfold sdWeights; ring
  rw [hsd] at hμ' ⊢
  -- the lattice point `((e'_j + 1) ∏_{i ≠ j} k'_i) / (2 ∏ k'_i)`
  have hprod : ∏ i, k i = k' j * ∏ i ∈ Finset.univ.erase j, k' i := by
    rw [Finset.mul_prod_erase _ _ (Finset.mem_univ j), hk']
    exact (Equiv.prod_comp (faceEquiv ι).symm k).symm
  have hkj : (0 : ℝ) < k' j := by exact_mod_cast hk _
  have hP : (0 : ℝ) < ∏ i ∈ Finset.univ.erase j, (k' i : ℝ) :=
    Finset.prod_pos fun i _ => by exact_mod_cast hk _
  have heq : ((e' j : ℝ) + 1) / (2 * (k' j : ℝ)) =
      (((e' j + 1) * ∏ i ∈ Finset.univ.erase j, k' i : ℕ) : ℝ) / ((2 * ∏ i, k i : ℕ) : ℝ) := by
    rw [hprod]
    push_cast
    field_simp
  rw [heq]
  exact mem_latticeBelow hQ (by rw [← heq]; exact hμ'.2)

/-! ### Measurability in an outer parameter -/

theorem measurable_empFaceInner_comp {α : Type*} [MeasurableSpace α] (k e : ι → ℕ)
    {G : α → ℝ → ℝ} (hG : Measurable (Function.uncurry G)) {T : α → ℝ} (hT : Measurable T) :
    Measurable fun w => empFaceInner k e (G w) (T w) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp only [empFaceInner_isEmpty]
    have h1 : Measurable fun w => G w (Real.sqrt (T w)) := by
      have : (fun w => G w (Real.sqrt (T w))) =
          Function.uncurry G ∘ fun w => (w, Real.sqrt (T w)) := rfl
      rw [this]
      exact hG.comp (measurable_id.prodMk hT.sqrt)
    exact h1.mul hT.neg.exp
  · have h : (fun w => empFaceInner k e (G w) (T w)) = fun w =>
        empUnitInner (k ∘ (faceEquiv ι).symm) (e ∘ (faceEquiv ι).symm) (G w) (T w) :=
      funext fun w => empFaceInner_reindex (faceEquiv ι) k e (G w) (T w)
    rw [h]
    exact measurable_empUnitInner_comp _ _ hG hT

theorem measurable_faceInnerCoeff_comp [Nonempty ι] {α : Type*} [MeasurableSpace α]
    (k e : ι → ℕ) {G : α → ℝ → ℝ} (hG : Measurable (Function.uncurry G)) (μ : ℝ) (q : ℕ) :
    Measurable fun w => faceInnerCoeff k e (G w) μ q :=
  measurable_empInnerCoeff_comp _ _ hG μ q

/-! ### The empty face -/

/-- On the empty index type the kernel `G(√t) e^{−t}` is `O(A t^{−L})` for all `t > 0`. -/
theorem empFaceInner_isEmpty_two_regime [IsEmpty ι] (k e : ι → ℕ) (m : ℕ) (M' : ℝ) {L : ℝ}
    (hL : 0 < L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (G : ℝ → ℝ) (A : ℝ), GrowthLE G A m M' → ∀ t : ℝ, 0 < t →
      |empFaceInner k e G t| ≤ A * C * t ^ (-L) := by
  obtain ⟨E, hE0, hE⟩ := exists_exp_neg_half_le_rpow L
  refine ⟨kernelConst m M' * (E + 1), by have := kernelConst_nonneg m M'; positivity,
    fun G A hG t ht => ?_⟩
  have hA := hG.nonneg
  have hK0 := kernelConst_nonneg m M'
  rw [empFaceInner_isEmpty, abs_mul, abs_of_pos (exp_pos _)]
  have hs : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hkernel : (1 + Real.sqrt t) ^ m * exp (M' * Real.sqrt t) * exp (-t) ≤
      kernelConst m M' * exp (-t / 2) := by
    have h := jet_kernel_le 1 m M' hs
    simp only [pow_one, mul_one] at h
    rw [Real.sq_sqrt ht.le] at h
    unfold kernelConst
    linarith [h]
  have hexp : exp (-t / 2) ≤ (E + 1) * t ^ (-L) := by
    rcases le_or_gt 1 t with ht1 | ht1
    · exact (hE t ht1).trans (mul_le_mul_of_nonneg_right (by linarith) (rpow_nonneg ht.le _))
    · have h1 : 1 ≤ t ^ (-L) :=
        one_le_rpow_of_pos_of_le_one_of_nonpos ht ht1.le (by linarith)
      calc exp (-t / 2) ≤ 1 := by rw [exp_le_one_iff]; linarith
        _ ≤ (E + 1) * t ^ (-L) := by nlinarith
  calc |G (Real.sqrt t)| * exp (-t)
      ≤ (A * (1 + Real.sqrt t) ^ m * exp (M' * Real.sqrt t)) * exp (-t) :=
        mul_le_mul_of_nonneg_right (hG _ hs) (exp_pos _).le
    _ = A * ((1 + Real.sqrt t) ^ m * exp (M' * Real.sqrt t) * exp (-t)) := by ring
    _ ≤ A * (kernelConst m M' * exp (-t / 2)) := mul_le_mul_of_nonneg_left hkernel hA
    _ ≤ A * (kernelConst m M' * ((E + 1) * t ^ (-L))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp hK0) hA
    _ = _ := by ring

end SmoothEngine

end Grammar
