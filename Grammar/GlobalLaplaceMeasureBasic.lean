/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Grammar.FaceCoefficient
import Grammar.CoefficientLocality

/-!
# The global leading measure of a Laplace integral over the original region (CCXC)

The first unit of the global programme (consult #89): the leading term of the ORIGINAL integral
`∫_W a(w) e^{−tK(w)} dw` over a region `W` of the parameter space is organised around a finite
Borel measure `σ` on `W` (the *leading measure*), concentrated on the zero set `W ∩ {K = 0}`, such
that for every bounded continuous test function `a`
`∫_W a e^{−tK} / (t^{−λ} (log t)^q) → ∫ a dσ` (`HasLeadingMeasure`).

* `globalLaplace W K a t = ∫_W a e^{−tK}` is the target integral with the trivial tube weight
  (`globalLaplace_eq_targetIntegral`), so every target-region certificate of the library applies.
* `LeadingFacePiece`: a finite measure on a Euclidean face space together with a measurable map to
  the parameter space; its pushforward `targetMeasure` is a finite measure on the parameter space,
  and a finite family of such pieces has the leading measure `leadingMeasureOf pieces T`
  (`∫ f dσ = Σ_T ∫ f ∘ toTarget dν_a`, concentration on any set that a.e. contains the images).
  This is the shape of the strata coefficient: `∫_W φ ϕ dσ = Σ_{tied faces} ∫_{face} (φ ϕ)∘q dν`.
* `HasLeadingMeasure W K lam q σ`: scaled limits for all bounded continuous tests. Consequences:
  the coefficient of a test is `∫ a dσ`; equivalence `∫_W a e^{−tK} ~ (∫ a dσ) t^{−λ} (log t)^q`
  when the coefficient is nonzero, positivity when `a ≥ 0` charges `σ`; **canonicality** — two
  finite leading measures at the same pair coincide (`HasLeadingMeasure.unique`, by the separation
  of finite Borel measures by bounded continuous functions), and two NONZERO leading measures force
  the same pair (`HasLeadingMeasure.pair_unique`); **locality** — a leading measure transfers
  between regions of finite volume differing only on a phase-gap set
  (`HasLeadingMeasure.of_locality`).
* The coefficient functional of a leading-term family is linear and positive
  (`coeff_add_of_hasLeadingTerm`, `coeff_smul_of_hasLeadingTerm`, `coeff_nonneg_of_hasLeadingTerm`)
  — by uniqueness of limits, without any structure of the certificates.

Nothing here produces a leading measure from a resolution; the production is the subject of the
following units (source-face measures of certified assemblies).
-/

open MeasureTheory Set Filter Topology Asymptotics BoundedContinuousFunction

namespace Grammar

variable {d : ℕ}

/-! ### The global Laplace integral -/

/-- **The global Laplace integral** of an amplitude `a` over a region `W`: `∫_W a e^{−tK}`. -/
noncomputable def globalLaplace (W : Set (Fin d → ℝ)) (K a : (Fin d → ℝ) → ℝ) (t : ℝ) : ℝ :=
  ∫ w in W, a w * Real.exp (-t * K w)

theorem globalLaplace_eq_targetIntegral (W : Set (Fin d → ℝ)) (K a : (Fin d → ℝ) → ℝ) :
    globalLaplace W K a = targetIntegral W a K (TubeWeight.one d) := by
  funext t
  simp [globalLaplace, targetIntegral]

theorem targetIntegral_eq_globalLaplace (W : Set (Fin d → ℝ)) (F K : (Fin d → ℝ) → ℝ)
    (p : TubeWeight d) : targetIntegral W F K p = globalLaplace W K (fun x => F x * p.w x) := rfl

theorem globalLaplace_smul (W : Set (Fin d → ℝ)) (K a : (Fin d → ℝ) → ℝ) (c t : ℝ) :
    globalLaplace W K (fun x => c * a x) t = c * globalLaplace W K a t := by
  unfold globalLaplace
  rw [← integral_const_mul]
  congr 1; funext x; ring

theorem globalLaplace_nonneg (W : Set (Fin d → ℝ)) (K : (Fin d → ℝ) → ℝ) {a : (Fin d → ℝ) → ℝ}
    (ha : ∀ x, 0 ≤ a x) (t : ℝ) : 0 ≤ globalLaplace W K a t :=
  integral_nonneg fun x => mul_nonneg (ha x) (Real.exp_pos _).le

/-- A bounded measurable amplitude times the Boltzmann factor is integrable on a region of finite
volume for `t ≥ 0` and `K ≥ 0`. -/
theorem integrableOn_mul_exp_of_bounded {W : Set (Fin d → ℝ)} (hW : volume W ≠ ⊤)
    {K : (Fin d → ℝ) → ℝ} (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x) {a : (Fin d → ℝ) → ℝ}
    (ham : Measurable a) {M : ℝ} (haM : ∀ x, |a x| ≤ M) {t : ℝ} (ht : 0 ≤ t) :
    IntegrableOn (fun x => a x * Real.exp (-t * K x)) W := by
  refine (integrableOn_const hW).mono'
    (ham.mul (Real.measurable_exp.comp (measurable_const.mul hK))).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc |a x| * Real.exp (-t * K x) ≤ M * 1 :=
        mul_le_mul (haM x) (by rw [Real.exp_le_one_iff]; nlinarith [hK0 x]) (Real.exp_pos _).le
          ((abs_nonneg _).trans (haM x))
    _ = M := mul_one M

theorem globalLaplace_add {W : Set (Fin d → ℝ)} (hW : volume W ≠ ⊤) {K : (Fin d → ℝ) → ℝ}
    (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x) (a b : (Fin d → ℝ) →ᵇ ℝ) {t : ℝ} (ht : 0 ≤ t) :
    globalLaplace W K (a + b) t = globalLaplace W K a t + globalLaplace W K b t := by
  unfold globalLaplace
  rw [← integral_add
    (integrableOn_mul_exp_of_bounded hW hK hK0 a.continuous.measurable
      (fun x => a.norm_coe_le_norm x) ht)
    (integrableOn_mul_exp_of_bounded hW hK hK0 b.continuous.measurable
      (fun x => b.norm_coe_le_norm x) ht)]
  congr 1; funext x
  simp only [Pi.add_apply]; ring

/-! ### The coefficient functional of a leading-term family is linear and positive -/

variable {W : Set (Fin d → ℝ)} {K : (Fin d → ℝ) → ℝ} {lam : ℝ} {q : ℕ}

/-- **Additivity of the coefficient** by uniqueness of limits. -/
theorem coeff_add_of_hasLeadingTerm (hW : volume W ≠ ⊤) (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x)
    {a b : (Fin d → ℝ) →ᵇ ℝ} {ca cb cab : ℝ} (ha : HasLeadingTerm (globalLaplace W K a) ca lam q)
    (hb : HasLeadingTerm (globalLaplace W K b) cb lam q)
    (hab : HasLeadingTerm (globalLaplace W K (a + b)) cab lam q) : cab = ca + cb := by
  refine hab.coeff_unique ((ha.add hb).congr' ?_)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact (globalLaplace_add hW hK hK0 a b ht).symm

/-- **Homogeneity of the coefficient** by uniqueness of limits. -/
theorem coeff_smul_of_hasLeadingTerm {a : (Fin d → ℝ) → ℝ} {c ca cca : ℝ}
    (ha : HasLeadingTerm (globalLaplace W K a) ca lam q)
    (hca : HasLeadingTerm (globalLaplace W K (fun x => c * a x)) cca lam q) : cca = c * ca :=
  hca.coeff_unique ((ha.const_mul c).congr' (Eventually.of_forall fun t =>
    (globalLaplace_smul W K a c t).symm))

/-- **Positivity of the coefficient** of a nonnegative amplitude. -/
theorem coeff_nonneg_of_hasLeadingTerm {a : (Fin d → ℝ) → ℝ} (ha0 : ∀ x, 0 ≤ a x) {c : ℝ}
    (h : HasLeadingTerm (globalLaplace W K a) c lam q) : 0 ≤ c := by
  refine ge_of_tendsto h ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  exact div_nonneg (globalLaplace_nonneg W K ha0 t) (powLogScale_pos lam q ht).le

/-- **Monotonicity of the coefficient.** -/
theorem coeff_mono_of_hasLeadingTerm (hW : volume W ≠ ⊤) (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x)
    {a b : (Fin d → ℝ) →ᵇ ℝ} (hab : ∀ x, a x ≤ b x) {ca cb : ℝ}
    (ha : HasLeadingTerm (globalLaplace W K a) ca lam q)
    (hb : HasLeadingTerm (globalLaplace W K b) cb lam q) : ca ≤ cb := by
  have hsub : HasLeadingTerm (globalLaplace W K (b - a)) (cb + -1 * ca) lam q := by
    refine (hb.add (ha.const_mul (-1))).congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have h1 := globalLaplace_add hW hK hK0 a (b - a) ht
    rw [coe_sub, add_sub_cancel] at h1
    rw [h1]; ring
  have := coeff_nonneg_of_hasLeadingTerm
    (fun x => by rw [Pi.sub_apply]; exact sub_nonneg.2 (hab x)) hsub
  linarith

/-! ### Face pieces and their pushforwards -/

/-- **A leading face piece**: a finite measure on a Euclidean face space with a measurable map to
the parameter space (the composite of a chart map with the embedding of a face). -/
structure LeadingFacePiece (d : ℕ) where
  /-- The dimension of the face space. -/
  dim : ℕ
  /-- The face measure (all geometric factors of the coefficient). -/
  measure : Measure (Fin dim → ℝ)
  [finite : IsFiniteMeasure measure]
  /-- The map to the parameter space. -/
  toTarget : (Fin dim → ℝ) → (Fin d → ℝ)
  measurable_toTarget : Measurable toTarget

attribute [instance] LeadingFacePiece.finite

namespace LeadingFacePiece

variable (a : LeadingFacePiece d)

/-- The pushforward of the face measure to the parameter space. -/
noncomputable def targetMeasure : Measure (Fin d → ℝ) := a.measure.map a.toTarget

instance : IsFiniteMeasure a.targetMeasure := Measure.isFiniteMeasure_map _ _

theorem targetMeasure_apply {s : Set (Fin d → ℝ)} (hs : MeasurableSet s) :
    a.targetMeasure s = a.measure (a.toTarget ⁻¹' s) :=
  Measure.map_apply a.measurable_toTarget hs

theorem integral_targetMeasure {f : (Fin d → ℝ) → ℝ} (hf : AEStronglyMeasurable f a.targetMeasure) :
    ∫ x, f x ∂a.targetMeasure = ∫ y, f (a.toTarget y) ∂a.measure :=
  integral_map a.measurable_toTarget.aemeasurable hf

/-- A piece whose map lands a.e. in `S` has pushforward concentrated on `S`. -/
theorem targetMeasure_compl_eq_zero {S : Set (Fin d → ℝ)} (hS : MeasurableSet S)
    (h : ∀ᵐ y ∂a.measure, a.toTarget y ∈ S) : a.targetMeasure Sᶜ = 0 := by
  rw [targetMeasure_apply a hS.compl, preimage_compl]
  exact ae_iff.1 h

end LeadingFacePiece

/-- **The leading measure of a finite family of pieces**: the sum of the pushforwards over the tied
index set `T`. -/
noncomputable def leadingMeasureOf {ι : Type*} (pieces : ι → LeadingFacePiece d) (T : Finset ι) :
    Measure (Fin d → ℝ) :=
  ∑ a ∈ T, (pieces a).targetMeasure

instance {ι : Type*} (pieces : ι → LeadingFacePiece d) (T : Finset ι) :
    IsFiniteMeasure (leadingMeasureOf pieces T) := by
  unfold leadingMeasureOf; infer_instance

/-- **The strata-integral form of the coefficient**: `∫ f dσ = Σ_{a ∈ T} ∫ f ∘ q_a dν_a`. -/
theorem integral_leadingMeasureOf {ι : Type*} (pieces : ι → LeadingFacePiece d) (T : Finset ι)
    {f : (Fin d → ℝ) → ℝ} (hf : ∀ a ∈ T, Integrable f (pieces a).targetMeasure) :
    ∫ x, f x ∂leadingMeasureOf pieces T =
      ∑ a ∈ T, ∫ y, f ((pieces a).toTarget y) ∂(pieces a).measure := by
  unfold leadingMeasureOf
  rw [integral_finsetSum_measure hf]
  exact Finset.sum_congr rfl fun a ha =>
    (pieces a).integral_targetMeasure (hf a ha).aestronglyMeasurable

theorem integral_leadingMeasureOf_bcf {ι : Type*} (pieces : ι → LeadingFacePiece d) (T : Finset ι)
    (f : (Fin d → ℝ) →ᵇ ℝ) :
    ∫ x, f x ∂leadingMeasureOf pieces T =
      ∑ a ∈ T, ∫ y, f ((pieces a).toTarget y) ∂(pieces a).measure :=
  integral_leadingMeasureOf pieces T fun _ _ => f.integrable _

/-- **Concentration**: if every piece lands a.e. in `S`, the leading measure vanishes off `S`. -/
theorem leadingMeasureOf_compl_eq_zero {ι : Type*} (pieces : ι → LeadingFacePiece d) (T : Finset ι)
    {S : Set (Fin d → ℝ)} (hS : MeasurableSet S)
    (h : ∀ a ∈ T, ∀ᵐ y ∂(pieces a).measure, (pieces a).toTarget y ∈ S) :
    leadingMeasureOf pieces T Sᶜ = 0 := by
  unfold leadingMeasureOf
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  exact Finset.sum_eq_zero fun a ha => (pieces a).targetMeasure_compl_eq_zero hS (h a ha)

/-! ### Leading measures -/

/-- **A leading measure** of the region `W` at the pair `(λ, q)`: for every bounded continuous test
`a`, `∫_W a e^{−tK} / (t^{−λ} (log t)^q) → ∫ a dσ`. -/
def HasLeadingMeasure (W : Set (Fin d → ℝ)) (K : (Fin d → ℝ) → ℝ) (lam : ℝ) (q : ℕ)
    (σ : Measure (Fin d → ℝ)) : Prop :=
  ∀ a : (Fin d → ℝ) →ᵇ ℝ, HasLeadingTerm (globalLaplace W K a) (∫ w, a w ∂σ) lam q

namespace HasLeadingMeasure

variable {σ τ : Measure (Fin d → ℝ)}

theorem tendsto (h : HasLeadingMeasure W K lam q σ) (a : (Fin d → ℝ) →ᵇ ℝ) :
    Tendsto (fun t => globalLaplace W K a t / powLogScale lam q t) atTop (𝓝 (∫ w, a w ∂σ)) :=
  h a

/-- A leading measure from a coefficient functional represented by `σ`. -/
theorem of_coeff (C : ((Fin d → ℝ) →ᵇ ℝ) → ℝ)
    (hC : ∀ a : (Fin d → ℝ) →ᵇ ℝ, HasLeadingTerm (globalLaplace W K a) (C a) lam q)
    (hσ : ∀ a : (Fin d → ℝ) →ᵇ ℝ, C a = ∫ w, a w ∂σ) : HasLeadingMeasure W K lam q σ :=
  fun a => hσ a ▸ hC a

/-- **Asymptotic equivalence** when the coefficient is nonzero. -/
theorem isEquivalent (h : HasLeadingMeasure W K lam q σ) (a : (Fin d → ℝ) →ᵇ ℝ)
    (hc : ∫ w, a w ∂σ ≠ 0) :
    globalLaplace W K a ~[atTop] fun t => (∫ w, a w ∂σ) * powLogScale lam q t :=
  (h a).isEquivalent hc

/-- **Positivity of the coefficient** of a nonnegative test charging the leading measure. -/
theorem integral_pos_iff [IsFiniteMeasure σ] (a : (Fin d → ℝ) →ᵇ ℝ) (ha0 : ∀ x, 0 ≤ a x) :
    0 < ∫ w, a w ∂σ ↔ 0 < σ (Function.support a) :=
  integral_pos_iff_support_of_nonneg ha0 (a.integrable σ)

theorem isEquivalent_of_pos [IsFiniteMeasure σ] (h : HasLeadingMeasure W K lam q σ)
    (a : (Fin d → ℝ) →ᵇ ℝ) (ha0 : ∀ x, 0 ≤ a x) (hpos : 0 < σ (Function.support a)) :
    0 < ∫ w, a w ∂σ ∧
      globalLaplace W K a ~[atTop] fun t => (∫ w, a w ∂σ) * powLogScale lam q t :=
  ⟨(integral_pos_iff a ha0).2 hpos, h.isEquivalent a ((integral_pos_iff a ha0).2 hpos).ne'⟩

/-- ★ **Canonicality**: two finite leading measures at the same pair coincide. -/
theorem unique [IsFiniteMeasure σ] [IsFiniteMeasure τ] (h₁ : HasLeadingMeasure W K lam q σ)
    (h₂ : HasLeadingMeasure W K lam q τ) : σ = τ :=
  ext_of_forall_integral_eq_of_IsFiniteMeasure fun a => (h₁ a).coeff_unique (h₂ a)

/-- The total mass is the coefficient of the constant test `1`. -/
theorem hasLeadingTerm_one [IsFiniteMeasure σ] (h : HasLeadingMeasure W K lam q σ) :
    HasLeadingTerm (globalLaplace W K (1 : (Fin d → ℝ) →ᵇ ℝ)) (σ.real univ) lam q := by
  have := h 1
  simpa [integral_const] using this

/-- ★ **Nonzero leading measures identify the pair.** -/
theorem pair_unique [IsFiniteMeasure σ] [IsFiniteMeasure τ] {lam' : ℝ} {q' : ℕ}
    (h₁ : HasLeadingMeasure W K lam q σ) (h₂ : HasLeadingMeasure W K lam' q' τ) (hσ : σ ≠ 0)
    (hτ : τ ≠ 0) : lam = lam' ∧ q = q' := by
  have : NeZero σ := ⟨hσ⟩
  have : NeZero τ := ⟨hτ⟩
  exact h₁.hasLeadingTerm_one.pair_unique measureReal_univ_ne_zero h₂.hasLeadingTerm_one
    measureReal_univ_ne_zero

/-- Nonzero leading measures at possibly different pairs coincide, pairs included. -/
theorem eq_of_ne_zero [IsFiniteMeasure σ] [IsFiniteMeasure τ] {lam' : ℝ} {q' : ℕ}
    (h₁ : HasLeadingMeasure W K lam q σ) (h₂ : HasLeadingMeasure W K lam' q' τ) (hσ : σ ≠ 0)
    (hτ : τ ≠ 0) : lam = lam' ∧ q = q' ∧ σ = τ := by
  obtain ⟨hl, hq⟩ := h₁.pair_unique h₂ hσ hτ
  subst hl; subst hq
  exact ⟨rfl, rfl, h₁.unique h₂⟩

/-- **Locality**: a leading measure transfers between regions of finite volume differing only on a
phase-gap set `{K ≥ κ}`. -/
theorem of_locality {A B : Set (Fin d → ℝ)} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : volume (A ∪ B) ≠ ⊤) (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x) {κ : ℝ} (hκ : 0 < κ)
    (hKA : ∀ᵐ x ∂(volume.restrict (A \ B)), κ ≤ K x)
    (hKB : ∀ᵐ x ∂(volume.restrict (B \ A)), κ ≤ K x) (h : HasLeadingMeasure A K lam q σ) :
    HasLeadingMeasure B K lam q σ := by
  intro a
  have ha := h a
  rw [globalLaplace_eq_targetIntegral] at ha ⊢
  refine ha.targetIntegral_of_locality hA hB ?_ hK hK0 hκ hKA hKB
  refine (integrableOn_const (C := ‖a‖) hAB).mono'
    (a.continuous.measurable.mul measurable_const).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  simp only [TubeWeight.one_w, mul_one]
  exact a.norm_coe_le_norm x

/-- **Concentration determines the coefficient**: tests agreeing on a set of full `σ`-measure have
the same coefficient. -/
theorem integral_congr_of_eqOn {S : Set (Fin d → ℝ)} (hS : σ Sᶜ = 0)
    {a b : (Fin d → ℝ) → ℝ} (hab : EqOn a b S) : ∫ w, a w ∂σ = ∫ w, b w ∂σ :=
  integral_congr_ae (by
    rw [Filter.EventuallyEq, ae_iff]
    exact measure_mono_null (fun x hx => fun hxS => hx (hab hxS)) hS)

end HasLeadingMeasure

end Grammar
