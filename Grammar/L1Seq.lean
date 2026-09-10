/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.DataSpaceSeparable
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Probability.Moments.Variance

/-!
# `ℓ¹` over a countable index: coordinates, truncations, and the moment hypothesis

Infrastructure for the central limit theorem in `ℓ¹(ι, ℝ)` (the coefficient space of the
random Taylor data).  Coordinate functionals (`coordCLM`), coordinate embeddings (`singleCLM`),
finite truncations `truncate F` (`‖x − truncate F x‖ = ∑_{j∉F} |x_j|`, `truncate (F k) x → x`
along a finite exhaustion), finite coordinate projections `finiteCoords F : ℓ¹ → ℝ^F`, and
measurability of an `ℓ¹`-valued map from measurability of its coordinates (`measurable_of_coords`).

The moment hypothesis of the `ℓ¹` CLT is `SummableCoordL2 P Y`: coordinates in `L²` with
summable `L²`-norms `r_j = ‖Y_j‖_{L²}`.  It gives Bochner integrability `E‖Y‖ ≤ ∑_j r_j`
(`integrable_of_summableCoordL2`) and the coordinate identity `(∫ Y)_j = ∫ Y_j`.

Non-claim: no type-2 theory; `ℓ¹` is not of type 2, and summability of the coordinate `L²` norms is
the extra hypothesis under which the CLT will be proved.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace Grammar

/-- `ℓ¹(ι, ℝ)`. -/
abbrev L1Seq (ι : Type*) : Type _ := lp (fun _ : ι => ℝ) 1

variable {ι : Type*}

noncomputable instance : MeasurableSpace (L1Seq ι) := borel _
instance : BorelSpace (L1Seq ι) := ⟨rfl⟩

instance [Countable ι] : SecondCountableTopology (L1Seq ι) := secondCountableTopology_lp_one

theorem L1Seq.summable_abs (x : L1Seq ι) : Summable fun j => |x j| := by
  have := Memℓp.summable (p := 1) (by norm_num) (lp.memℓp x)
  simpa using this

theorem L1Seq.norm_eq_tsum (x : L1Seq ι) : ‖x‖ = ∑' j, |x j| := by
  rw [lp.norm_eq_tsum_rpow (by norm_num) x]
  simp [Real.norm_eq_abs]

/-- The coordinate functional `x ↦ x_j`. -/
noncomputable def coordCLM (j : ι) : L1Seq ι →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun x => x j
      map_add' := fun x y => by simp
      map_smul' := fun c x => by simp } 1 fun x => by
    rw [one_mul]; exact lp.norm_apply_le_norm one_ne_zero x j

@[simp] theorem coordCLM_apply (j : ι) (x : L1Seq ι) : coordCLM j x = x j := rfl

theorem measurable_coord (j : ι) : Measurable fun x : L1Seq ι => x j :=
  (coordCLM j).continuous.measurable

/-- A monotone covering exhaustion of a countable type by finite sets. -/
theorem exists_finset_exhaustion [Countable ι] :
    ∃ F : ℕ → Finset ι, Monotone F ∧ ∀ j, ∃ k, j ∈ F k := by
  classical
  obtain ⟨e, he⟩ := Countable.exists_injective_nat ι
  refine ⟨fun k => (Finset.range (k + 1)).preimage e he.injOn, fun a b hab => ?_, fun j =>
    ⟨e j, ?_⟩⟩
  · exact Finset.monotone_preimage he (Finset.range_mono (by omega))
  · simp

/-- The finite coordinate projection `ℓ¹ → ℝ^F`. -/
noncomputable def finiteCoords (F : Finset ι) : L1Seq ι →L[ℝ] EuclideanSpace ℝ F :=
  ((EuclideanSpace.equiv F ℝ).symm.toContinuousLinearEquiv : (F → ℝ) →L[ℝ] EuclideanSpace ℝ F).comp
    (ContinuousLinearMap.pi fun j : F => coordCLM (j : ι))

@[simp] theorem finiteCoords_apply (F : Finset ι) (x : L1Seq ι) (j : F) :
    finiteCoords F x j = x j := rfl

/-! ### The moment hypothesis -/

section Moments

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)

/-- The coordinate `L²` norm `r_j = ‖Y_j‖_{L²(P)}`. -/
noncomputable def coordL2 (Y : Ω → L1Seq ι) (j : ι) : ℝ := Real.sqrt (∫ ω, (Y ω j) ^ 2 ∂P)

/-- The moment hypothesis of the `ℓ¹` CLT: measurable, coordinates in `L²`, summable `L²` norms. -/
structure SummableCoordL2 (Y : Ω → L1Seq ι) : Prop where
  measurable : Measurable Y
  memLp_coord : ∀ j, MemLp (fun ω => Y ω j) 2 P
  summable : Summable (coordL2 P Y)

theorem coordL2_nonneg (Y : Ω → L1Seq ι) (j : ι) : 0 ≤ coordL2 P Y j := Real.sqrt_nonneg _

theorem SummableCoordL2.coord_measurable {Y : Ω → L1Seq ι} (hY : SummableCoordL2 P Y) (j : ι) :
    Measurable fun ω => Y ω j :=
  (Grammar.measurable_coord j).comp hY.measurable

/-- The coordinates of the Bochner integral are the integrals of the coordinates. -/
theorem coord_integral {Y : Ω → L1Seq ι} (hY : Integrable Y P) (j : ι) :
    (∫ ω, Y ω ∂P) j = ∫ ω, Y ω j ∂P := by
  have := (coordCLM j).integral_comp_comm hY
  simpa using this.symm

variable [IsProbabilityMeasure P]

/-- Jensen: `∫ |Y_j| ≤ ‖Y_j‖_{L²}`. -/
theorem integral_abs_coord_le {Y : Ω → L1Seq ι} (hY : ∀ j, MemLp (fun ω => Y ω j) 2 P) (j : ι) :
    ∫ ω, |Y ω j| ∂P ≤ coordL2 P Y j := by
  have h2 : MemLp (fun ω => |Y ω j|) 2 P := (hY j).abs
  have hv := variance_nonneg (fun ω => |Y ω j|) P
  rw [variance_eq_sub h2] at hv
  unfold coordL2
  refine Real.le_sqrt_of_sq_le ?_
  have : ∫ ω, |Y ω j| ^ 2 ∂P = ∫ ω, (Y ω j) ^ 2 ∂P := by simp [sq_abs]
  simp only [Pi.pow_apply] at hv
  linarith

theorem integrable_abs_coord {Y : Ω → L1Seq ι} (hY : ∀ j, MemLp (fun ω => Y ω j) 2 P) (j : ι) :
    Integrable (fun ω => |Y ω j|) P :=
  ((hY j).integrable one_le_two).abs

/-- **Bochner integrability** under the moment hypothesis: `E‖Y‖ ≤ ∑_j r_j`. -/
theorem integrable_of_summableCoordL2 [Countable ι] {Y : Ω → L1Seq ι} (hY : SummableCoordL2 P Y) :
    Integrable Y P := by
  refine ⟨hY.measurable.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have h1 : ∀ ω, ‖Y ω‖ₑ = ∑' j, ENNReal.ofReal |Y ω j| := fun ω => by
    rw [← ofReal_norm, L1Seq.norm_eq_tsum,
      ENNReal.ofReal_tsum_of_nonneg (fun j => abs_nonneg _) (L1Seq.summable_abs (Y ω))]
  simp_rw [h1]
  rw [lintegral_tsum (f := fun j ω => ENNReal.ofReal |Y ω j|) fun j =>
    (SummableCoordL2.coord_measurable P hY j).abs.ennreal_ofReal.aemeasurable]
  calc ∑' j, ∫⁻ ω, ENNReal.ofReal |Y ω j| ∂P ≤ ∑' j, ENNReal.ofReal (coordL2 P Y j) := by
        refine ENNReal.tsum_le_tsum fun j => ?_
        rw [← ofReal_integral_eq_lintegral_ofReal (integrable_abs_coord P hY.memLp_coord j)
          (Eventually.of_forall fun ω => abs_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (integral_abs_coord_le P hY.memLp_coord j)
    _ = ENNReal.ofReal (∑' j, coordL2 P Y j) :=
        (ENNReal.ofReal_tsum_of_nonneg (coordL2_nonneg P Y) hY.summable).symm
    _ < ∞ := ENNReal.ofReal_lt_top

end Moments

/-! ### Coordinate embeddings, truncations, finite coordinate projections -/

variable [DecidableEq ι]

/-- The coordinate embedding `a ↦ a e_j`. -/
noncomputable def singleCLM (j : ι) : ℝ →L[ℝ] L1Seq ι :=
  LinearMap.mkContinuous (lp.lsingle (E := fun _ : ι => ℝ) (𝕜 := ℝ) 1 j) 1 fun a => by
    rw [one_mul]
    exact (lp.norm_single (E := fun _ : ι => ℝ) zero_lt_one j a).le

@[simp] theorem singleCLM_apply (j : ι) (a : ℝ) :
    singleCLM j a = lp.single (E := fun _ : ι => ℝ) 1 j a := rfl

/-- The finite truncation `x ↦ ∑_{j∈F} x_j e_j`. -/
noncomputable def truncate (F : Finset ι) : L1Seq ι →L[ℝ] L1Seq ι :=
  ∑ j ∈ F, (singleCLM j).comp (coordCLM j)

theorem truncate_eq_sum (F : Finset ι) (x : L1Seq ι) :
    truncate F x = ∑ j ∈ F, lp.single (E := fun _ : ι => ℝ) 1 j (x j) := by
  simp [truncate]

theorem truncate_apply (F : Finset ι) (x : L1Seq ι) (i : ι) :
    truncate F x i = if i ∈ F then x i else 0 := by
  rw [truncate_eq_sum]
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.single_apply, Pi.single_apply]
  exact Finset.sum_ite_eq F i fun c => x c

theorem sub_truncate_apply (F : Finset ι) (x : L1Seq ι) (i : ι) :
    (x - truncate F x) i = if i ∈ F then 0 else x i := by
  rw [lp.coeFn_sub, Pi.sub_apply, truncate_apply]
  split_ifs <;> simp

/-- `‖x − truncate F x‖ = ∑_{j ∉ F} |x_j|`. -/
theorem norm_sub_truncate (F : Finset ι) (x : L1Seq ι) :
    ‖x - truncate F x‖ = ∑' j, if j ∈ F then 0 else |x j| := by
  rw [L1Seq.norm_eq_tsum]
  refine tsum_congr fun j => ?_
  rw [sub_truncate_apply]
  split_ifs <;> simp

theorem norm_sub_truncate_le_tsum (F : Finset ι) (x : L1Seq ι) :
    ‖x - truncate F x‖ ≤ ∑' j, |x j| := by
  rw [norm_sub_truncate]
  refine Summable.tsum_le_tsum (fun j => ?_) ?_ (L1Seq.summable_abs x)
  · split_ifs <;> simp
  · exact (L1Seq.summable_abs x).of_nonneg_of_le (fun j => by split_ifs <;> simp)
      (fun j => by split_ifs <;> simp)

theorem norm_truncate_le (F : Finset ι) (x : L1Seq ι) : ‖truncate F x‖ ≤ ‖x‖ := by
  rw [L1Seq.norm_eq_tsum, L1Seq.norm_eq_tsum]
  refine Summable.tsum_le_tsum (fun j => ?_) ?_ (L1Seq.summable_abs x)
  · rw [truncate_apply]; split_ifs <;> simp
  · exact (L1Seq.summable_abs x).of_nonneg_of_le (fun j => abs_nonneg _)
      (fun j => by rw [truncate_apply]; split_ifs <;> simp)

/-- Along a monotone covering exhaustion the truncations converge to `x`. -/
theorem tendsto_truncate {F : ℕ → Finset ι} (hF : Monotone F) (hcov : ∀ j, ∃ k, j ∈ F k)
    (x : L1Seq ι) : Tendsto (fun k => truncate (F k) x) atTop (𝓝 x) := by
  have h := lp.hasSum_single (E := fun _ : ι => ℝ) (p := 1) ENNReal.one_ne_top x
  have h2 := h.comp (tendsto_atTop_finset_of_monotone hF hcov)
  refine h2.congr fun k => ?_
  simp [Function.comp, truncate_eq_sum]

theorem measurable_truncate_comp [Countable ι] {Ω : Type*} [MeasurableSpace Ω] {f : Ω → L1Seq ι}
    (hf : ∀ j, Measurable fun ω => f ω j) (F : Finset ι) :
    Measurable fun ω => truncate F (f ω) := by
  simp_rw [truncate_eq_sum]
  exact Finset.measurable_sum _ fun j _ => (singleCLM j).continuous.measurable.comp (hf j)

omit [DecidableEq ι] in
/-- An `ℓ¹`-valued map with measurable coordinates is measurable. -/
theorem measurable_of_coords [Countable ι] {Ω : Type*} [MeasurableSpace Ω] {f : Ω → L1Seq ι}
    (hf : ∀ j, Measurable fun ω => f ω j) : Measurable f := by
  classical
  obtain ⟨F, hF, hcov⟩ := exists_finset_exhaustion (ι := ι)
  refine measurable_of_tendsto_metrizable (fun k => measurable_truncate_comp hf (F k)) ?_
  rw [tendsto_pi_nhds]
  exact fun ω => tendsto_truncate hF hcov (f ω)

end Grammar
