import Grammar.CompactBaseKernel
import Grammar.GaussianQuartetGeneral

/-!
# Compact base II (part 1): finite reduction and the Gaussian field record

A finite-range quantisation `q` of the compact base turns every compact-base quantity of
`ρ.map q` into a finite quartet quantity over the atoms of positive mass:

* `posAtoms ρ hfin` are the atoms `a ∈ range q` with `ρ(q⁻¹{a}) > 0`, enumerated by
  `atomPt : Fin m → K` with weights `atomWt : Fin m → ℝ` (positive, summing to `ρ(K)`);
* `∫ f(q x) dρ = ∑ᵢ wᵢ f(xᵢ)` (`integral_comp_finiteRange_atoms`), so `D, M₂, H, Diag, Q, V` of
  `ρ.map q` equal `quartetD, quartetM2, quartetH, quartetDiag, quartetQ, quartetVgen` of the
  evaluation vector `g ∘ atomPt` with the kernel matrix `kernelMatrix 𝒞 atomPt`
  (`compactD_map_eq`, …, `compactV_map_eq`).

A **Gaussian field** (`GaussianField 𝒞 P`) is a random continuous function `G : Ω → C(K,ℝ)`
with measurable evaluations, a finite second sup-norm moment, and finite-dimensional laws given
by the axiom-clean `gaussianVector` construction with covariance `kernelMatrix 𝒞 x` at every
finite family of points (repeated points and singular covariances allowed). Its finite-dimensional
integrals transfer to the Gaussian vector (`GaussianField.integral_eval`), so on every quantised
measure the finite identities hold verbatim:

* **`E H_{ρ∘q⁻¹}(G) = β E V_{ρ∘q⁻¹}(G)`** (`GaussianField.integral_compactH_map_eq`);
* **`E log D_{ρ∘q⁻¹}(G) = log D(0) + (β²/2)∫₀¹ E V_{ρ∘q⁻¹}(√s G) ds`**
  (`GaussianField.integral_log_compactD_map_eq`) and `E log D_{ρ∘q⁻¹}(G) ≥ log D(0)`
  (`GaussianField.log_compactD_zero_le_integral_map`), with `D(0) = ρ(K) β^{−λ}Γ(λ)`
  (`compactD_zero`).

The passage to `ρ` itself (dominated convergence along a quantisation sequence) is the next unit.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

section Atoms

variable {K : Type*} [MeasurableSpace K] [MeasurableSingletonClass K] (ρ : Measure K)
  [IsFiniteMeasure ρ] {q : K → K}

/-- The atoms of positive mass of a finite-range quantisation. -/
noncomputable def posAtoms (hfin : (Set.range q).Finite) : Finset K :=
  hfin.toFinset.filter fun a => 0 < ρ.real (q ⁻¹' {a})

/-- Enumeration of the positive atoms. -/
noncomputable def atomPt (hfin : (Set.range q).Finite) (i : Fin (posAtoms ρ hfin).card) : K :=
  ((posAtoms ρ hfin).equivFin.symm i : K)

/-- The weights of the positive atoms. -/
noncomputable def atomWt (hfin : (Set.range q).Finite) (i : Fin (posAtoms ρ hfin).card) : ℝ :=
  ρ.real (q ⁻¹' {atomPt ρ hfin i})

omit [MeasurableSingletonClass K] [IsFiniteMeasure ρ] in
theorem atomPt_mem (hfin : (Set.range q).Finite) (i : Fin (posAtoms ρ hfin).card) :
    atomPt ρ hfin i ∈ posAtoms ρ hfin := ((posAtoms ρ hfin).equivFin.symm i).2

omit [MeasurableSingletonClass K] [IsFiniteMeasure ρ] in
theorem atomWt_pos (hfin : (Set.range q).Finite) (i : Fin (posAtoms ρ hfin).card) :
    0 < atomWt ρ hfin i :=
  (Finset.mem_filter.1 (atomPt_mem ρ hfin i)).2

omit [MeasurableSingletonClass K] [IsFiniteMeasure ρ] in
/-- Sums over the range weighted by the atom masses reduce to sums over the positive atoms. -/
theorem sum_range_eq_sum_atoms (hfin : (Set.range q).Finite) (F : K → ℝ) :
    ∑ a ∈ hfin.toFinset, ρ.real (q ⁻¹' {a}) * F a = ∑ i, atomWt ρ hfin i * F (atomPt ρ hfin i) := by
  rw [← Finset.sum_filter_of_ne (p := fun a => 0 < ρ.real (q ⁻¹' {a})) (fun a _ h => ?_)]
  · change ∑ a ∈ posAtoms ρ hfin, _ = _
    rw [← Finset.sum_coe_sort (posAtoms ρ hfin)]
    exact ((posAtoms ρ hfin).equivFin.symm.sum_comp
      (fun a : posAtoms ρ hfin => ρ.real (q ⁻¹' {(a : K)}) * F a)).symm
  · rcases (measureReal_nonneg (μ := ρ) (s := q ⁻¹' {a})).lt_or_eq with h' | h'
    · exact h'
    · exact absurd (by rw [← h', zero_mul]) h

theorem integral_comp_finiteRange_atoms (hq : Measurable q) (hfin : (Set.range q).Finite)
    (f : K → ℝ) : ∫ x, f (q x) ∂ρ = ∑ i, atomWt ρ hfin i * f (atomPt ρ hfin i) := by
  rw [integral_comp_finiteRange ρ hq hfin f, sum_range_eq_sum_atoms]

theorem sum_atomWt (hq : Measurable q) (hfin : (Set.range q).Finite) :
    ∑ i, atomWt ρ hfin i = ρ.real univ := by
  have := integral_comp_finiteRange_atoms ρ hq hfin (fun _ => (1 : ℝ))
  simp only [integral_const, smul_eq_mul, mul_one] at this
  exact this.symm

theorem nonempty_atoms (hq : Measurable q) (hfin : (Set.range q).Finite) (hρ : ρ ≠ 0) :
    Nonempty (Fin (posAtoms ρ hfin).card) := by
  by_contra h
  rw [not_nonempty_iff] at h
  have hsum := sum_atomWt ρ hq hfin
  rw [Finset.univ_eq_empty, Finset.sum_empty] at hsum
  have : 0 < ρ.real univ := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (Measure.measure_univ_ne_zero.2 hρ) (measure_ne_top _ _)
  linarith

end Atoms

/-- The kernel matrix `C(xᵢ, xⱼ)` of a finite family of points. -/
def PSDKernel.kernelMatrix {K : Type*} [TopologicalSpace K] (𝒞 : PSDKernel K) {m : ℕ}
    (x : Fin m → K) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j => 𝒞.C (x i) (x j)

section Reduce

variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {β lam : ℝ} (ρ : Measure K) [IsFiniteMeasure ρ] (hβ : 0 < β) (hlam : 0 < lam)
  (𝒞 : PSDKernel K) (g : C(K, ℝ)) {q : K → K} (hq : Measurable q) (hfin : (Set.range q).Finite)
include hβ hlam hq

omit 𝒞 in
theorem compactD_map_eq :
    compactD β lam (ρ.map q) g = quartetD β lam (atomWt ρ hfin) (fun i => g (atomPt ρ hfin i)) := by
  rw [compactD_map ρ hβ hlam g hq,
    integral_comp_finiteRange_atoms ρ hq hfin (fun x => fluctuation β lam (g x))]
  rfl

omit 𝒞 in
theorem compactM2_map_eq :
    compactM2 β lam (ρ.map q) g =
      quartetM2 β lam (atomWt ρ hfin) (fun i => g (atomPt ρ hfin i)) := by
  rw [compactM2_map ρ hβ hlam g hq, integral_comp_finiteRange_atoms ρ hq hfin
    (fun x => fluctuation β (lam + 1) (g x)), compactD_map_eq ρ hβ hlam g hq hfin]
  unfold quartetM2 quartetR
  rw [Finset.sum_div]

omit 𝒞 in
theorem compactH_map_eq :
    compactH β lam (ρ.map q) g =
      quartetH β lam (atomWt ρ hfin) (fun i => g (atomPt ρ hfin i)) := by
  rw [compactH_map ρ hβ hlam g hq, integral_comp_finiteRange_atoms ρ hq hfin
    (fun x => g x * fluctuation β (lam + 1 / 2) (g x)), compactD_map_eq ρ hβ hlam g hq hfin]
  unfold quartetH quartetW quartetN
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem compactDiag_map_eq :
    compactDiag (ρ.map q) β lam 𝒞 g =
      quartetDiag β lam (atomWt ρ hfin) (𝒞.kernelMatrix (atomPt ρ hfin))
        (fun i => g (atomPt ρ hfin i)) := by
  rw [compactDiag_map ρ hβ hlam 𝒞 g hq, integral_comp_finiteRange_atoms ρ hq hfin
    (fun x => 𝒞.C x x * fluctuation β (lam + 1) (g x)), compactD_map_eq ρ hβ hlam g hq hfin]
  unfold quartetDiag quartetR PSDKernel.kernelMatrix
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by simp only [Matrix.of_apply]; ring

theorem compactQnum_map_eq :
    compactQnum (ρ.map q) β lam 𝒞 g =
      ∑ i, ∑ j, 𝒞.C (atomPt ρ hfin i) (atomPt ρ hfin j) *
        (atomWt ρ hfin i * fluctuation β (lam + 1 / 2) (g (atomPt ρ hfin i))) *
        (atomWt ρ hfin j * fluctuation β (lam + 1 / 2) (g (atomPt ρ hfin j))) := by
  set F : C(K × K, ℝ) := ⟨bilocalC β lam 𝒞 g, continuous_bilocalC hβ hlam 𝒞 g⟩ with hF
  have hint : Integrable (fun z : K × K => bilocalC β lam 𝒞 g (q z.1, q z.2)) (ρ.prod ρ) :=
    Integrable.of_bound ((continuous_bilocalC hβ hlam 𝒞 g).measurable.comp
      (((hq.comp measurable_fst).prodMk (hq.comp measurable_snd)))).aestronglyMeasurable ‖F‖
      (Filter.Eventually.of_forall fun z => F.norm_coe_le_norm (q z.1, q z.2))
  rw [compactQnum_map ρ hβ hlam 𝒞 g hq, integral_prod _ hint]
  have hin : ∀ x, ∫ y, bilocalC β lam 𝒞 g (q x, q y) ∂ρ =
      ∑ j, atomWt ρ hfin j * bilocalC β lam 𝒞 g (q x, atomPt ρ hfin j) := fun x =>
    integral_comp_finiteRange_atoms ρ hq hfin (fun b => bilocalC β lam 𝒞 g (q x, b))
  simp_rw [hin]
  have hout := integral_comp_finiteRange_atoms ρ hq hfin
    (fun a => ∑ j, atomWt ρ hfin j * bilocalC β lam 𝒞 g (a, atomPt ρ hfin j))
  beta_reduce at hout
  rw [hout]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [bilocalC]
  ring

theorem compactQ_map_eq (hρ : ρ ≠ 0) :
    compactQ (ρ.map q) β lam 𝒞 g =
      quartetQ β lam (atomWt ρ hfin) (𝒞.kernelMatrix (atomPt ρ hfin))
        (fun i => g (atomPt ρ hfin i)) := by
  have := nonempty_atoms ρ hq hfin hρ
  have hD := quartetD_pos hβ hlam (atomWt_pos ρ hfin) (fun i => g (atomPt ρ hfin i))
  unfold compactQ
  rw [compactQnum_map_eq ρ hβ hlam 𝒞 g hq hfin, compactD_map_eq ρ hβ hlam g hq hfin]
  unfold quartetQ quartetW quartetN PSDKernel.kernelMatrix
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.of_apply]
  field_simp

theorem compactV_map_eq (hρ : ρ ≠ 0) :
    compactV (ρ.map q) β lam 𝒞 g =
      quartetVgen β lam (atomWt ρ hfin) (𝒞.kernelMatrix (atomPt ρ hfin))
        (fun i => g (atomPt ρ hfin i)) := by
  unfold compactV quartetVgen
  rw [compactDiag_map_eq ρ hβ hlam 𝒞 g hq hfin, compactQ_map_eq ρ hβ hlam 𝒞 g hq hfin hρ]

omit [CompactSpace K] [BorelSpace K] [IsFiniteMeasure ρ] hq in
/-- `D_ρ(0) = ρ(K) β^{−λ} Γ(λ)`. -/
theorem compactD_zero :
    compactD β lam ρ (0 : C(K, ℝ)) = ρ.real univ * (β ^ (-lam) * Real.Gamma lam) := by
  unfold compactD
  simp only [ContinuousMap.zero_apply, fluctuation_zero β lam hβ hlam, integral_const, smul_eq_mul]

end Reduce

/-! ### The Gaussian field record -/

/-- A **Gaussian field** on the compact base with covariance kernel `𝒞`: a random continuous
function with measurable evaluations, a finite second sup-norm moment, and finite-dimensional
laws given by the axiom-clean `gaussianVector` construction with covariance `kernelMatrix 𝒞 x`. -/
structure GaussianField {K : Type*} [TopologicalSpace K] [CompactSpace K] (𝒞 : PSDKernel K)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) where
  /-- The random continuous function. -/
  G : Ω → C(K, ℝ)
  measurable_eval : ∀ x, Measurable fun ω => G ω x
  integrable_sq_norm : Integrable (fun ω => ‖G ω‖ ^ 2) P
  law : ∀ (m : ℕ) (x : Fin m → K), ∃ (n : ℕ) (A : Matrix (Fin m) (Fin (n + 1)) ℝ),
    A * A.transpose = 𝒞.kernelMatrix x ∧
      P.map (fun ω => fun i => G ω (x i)) = gaussianVector A

namespace GaussianField

variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {𝒞 : PSDKernel K} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (Γ : GaussianField 𝒞 P)

omit [MeasurableSpace K] [BorelSpace K] in
theorem measurable_evalVec {m : ℕ} (x : Fin m → K) :
    Measurable fun ω => fun i => Γ.G ω (x i) :=
  measurable_pi_lambda _ fun i => Γ.measurable_eval (x i)

omit [MeasurableSpace K] [BorelSpace K] in
/-- Finite-dimensional integrals transfer to the Gaussian vector. -/
theorem integral_eval {m n : ℕ} (x : Fin m → K) (A : Matrix (Fin m) (Fin (n + 1)) ℝ)
    (hA : P.map (fun ω => fun i => Γ.G ω (x i)) = gaussianVector A) {F : (Fin m → ℝ) → ℝ}
    (hF : Measurable F) :
    ∫ ω, F (fun i => Γ.G ω (x i)) ∂P = ∫ v, F v ∂gaussianVector A := by
  rw [← hA, integral_map (Γ.measurable_evalVec x).aemeasurable hF.aestronglyMeasurable]

omit [MeasurableSpace K] [BorelSpace K] in
theorem integrable_eval {m n : ℕ} (x : Fin m → K) (A : Matrix (Fin m) (Fin (n + 1)) ℝ)
    (hA : P.map (fun ω => fun i => Γ.G ω (x i)) = gaussianVector A) {F : (Fin m → ℝ) → ℝ}
    (hF : Measurable F) (hint : Integrable F (gaussianVector A)) :
    Integrable (fun ω => F (fun i => Γ.G ω (x i))) P := by
  rw [← hA] at hint
  exact (integrable_map_measure hF.aestronglyMeasurable
    (Γ.measurable_evalVec x).aemeasurable).1 hint

variable {β lam : ℝ} (ρ : Measure K) [IsFiniteMeasure ρ] (hβ : 0 < β) (hlam : 0 < lam)
  (hρ : ρ ≠ 0) {q : K → K} (hq : Measurable q) (hfin : (Set.range q).Finite)
include hβ hlam hρ hq hfin

/-- **`E H = β E V` on a quantised base.** -/
theorem integral_compactH_map_eq :
    ∫ ω, compactH β lam (ρ.map q) (Γ.G ω) ∂P =
      β * ∫ ω, compactV (ρ.map q) β lam 𝒞 (Γ.G ω) ∂P := by
  have := nonempty_atoms ρ hq hfin hρ
  obtain ⟨n, A, hAB, hA⟩ := Γ.law _ (atomPt ρ hfin)
  have hw := atomWt_pos ρ hfin
  simp_rw [compactH_map_eq ρ hβ hlam (Γ.G _) hq hfin,
    compactV_map_eq ρ hβ hlam 𝒞 (Γ.G _) hq hfin hρ]
  rw [Γ.integral_eval _ A hA (continuous_quartetH hβ hlam hw).measurable,
    Γ.integral_eval _ A hA (continuous_quartetVgen hβ hlam hw _).measurable, ← hAB]
  exact integral_quartetH_eq_gen hβ hlam hw A

/-- **The interpolation identity on a quantised base**:
`E log D_{ρ∘q⁻¹}(G) = log D(0) + (β²/2) ∫₀¹ E V_{ρ∘q⁻¹}(√s G) ds`. -/
theorem integral_log_compactD_map_eq :
    ∫ ω, Real.log (compactD β lam (ρ.map q) (Γ.G ω)) ∂P =
      Real.log (β ^ (-lam) * Real.Gamma lam * ρ.real univ) +
        ∫ s in (0 : ℝ)..1, β ^ 2 / 2 *
          ∫ ω, compactV (ρ.map q) β lam 𝒞 (Real.sqrt s • Γ.G ω : C(K, ℝ)) ∂P := by
  have := nonempty_atoms ρ hq hfin hρ
  obtain ⟨n, A, hAB, hA⟩ := Γ.law _ (atomPt ρ hfin)
  have hw := atomWt_pos ρ hfin
  simp_rw [compactD_map_eq ρ hβ hlam (Γ.G _) hq hfin]
  rw [Γ.integral_eval _ A hA (measurable_log_quartetD hβ hlam), integral_log_quartetD_eq_gen A hβ
    hlam hw, sum_atomWt ρ hq hfin]
  congr 1
  refine intervalIntegral.integral_congr fun s _ => ?_
  congr 1
  have hV : ∀ ω, compactV (ρ.map q) β lam 𝒞 (Real.sqrt s • Γ.G ω : C(K, ℝ)) =
      quartetVgen β lam (atomWt ρ hfin) (A * A.transpose)
        (Real.sqrt s • fun i => Γ.G ω (atomPt ρ hfin i)) := by
    intro ω
    rw [compactV_map_eq ρ hβ hlam 𝒞 (Real.sqrt s • Γ.G ω) hq hfin hρ, hAB]
    rfl
  simp_rw [hV]
  have hsm : Measurable fun v : Fin (posAtoms ρ hfin).card → ℝ =>
      quartetVgen β lam (atomWt ρ hfin) (A * A.transpose) (Real.sqrt s • v) :=
    ((continuous_quartetVgen hβ hlam hw (A * A.transpose)).comp
      ((continuous_const (y := Real.sqrt s)).smul (continuous_id (X := Fin _ → ℝ)))).measurable
  rw [Γ.integral_eval _ A hA hsm, integral_gaussianVector _ _ hsm]
  unfold interpVgen
  rfl

/-- **`E log D_{ρ∘q⁻¹}(G) ≥ log D(0)`**. -/
theorem log_compactD_zero_le_integral_map :
    Real.log (β ^ (-lam) * Real.Gamma lam * ρ.real univ) ≤
      ∫ ω, Real.log (compactD β lam (ρ.map q) (Γ.G ω)) ∂P := by
  have := nonempty_atoms ρ hq hfin hρ
  obtain ⟨n, A, hAB, hA⟩ := Γ.law _ (atomPt ρ hfin)
  have hw := atomWt_pos ρ hfin
  simp_rw [compactD_map_eq ρ hβ hlam (Γ.G _) hq hfin]
  rw [Γ.integral_eval _ A hA (measurable_log_quartetD hβ hlam), ← sum_atomWt ρ hq hfin]
  exact log_quartetD_zero_le_integral_gen A hβ hlam hw

end GaussianField

end Grammar
