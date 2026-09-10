import Grammar.CoverAssembly
import Grammar.ChartAssemblyGlobal

/-!
# The exact-core adapter: certified box data are the pulled-back core integral

The cover assembly (CXXXVIII) leaves the core terms as pulled-back integrals against the weighted
source measures; the stochastic expansion (CXXI–CXXII, CXXXVII) is stated for the model integral
`gInt ν h k β b x N = ∑_I ∫_{K_I} dataBoxIntegral (x_I v) dν_I(v)`. This file closes the
representation gap with a certificate, without removing any analytic unit:

an `ExactBoxCoreCertificate` for chart `i` consists of adapted coordinates
`ψ : K × (Fin (n+1) → ℝ) → (Fin d → ℝ)` on the core together with the **proved** identities

* the weighted source measure restricted to the core is the pushforward of `ν ⊗ dy|_{(0,b]^{n+1}}`
  under `ψ` (the change-of-variables identity — an input, not reproved here);
* the phase is the monomial: `φ(Φ(ψ(v,u))) = ∏ uⱼ^{kⱼ}`;
* the fluctuation is the chart datum's phase: `ξ(Φ(ψ(v,u))) = evalF (toXi b (x v)) u`;
* the amplitude is the chart datum's observable times the monomial weight:
  `F(Φ(ψ(v,u))) = evalF (toEta b (x v)) u · ∏ uⱼ^{hⱼ}`.

Then the pulled-back core integral **is** the model integral (`chartIntegral_eq_tanIntegral`), and
over a cover with certified cores `Z(N) = gInt(x, N) + Rem(N)` with the positive-gap remainder
bound (`coverIntegral_eq_gInt_add`). Substituting into the assembled stochastic expansion attaches
its output to the actual core integrals.

Non-claims: the certificate is supplied, not constructed (its measure identity is a change of
variables about the presentation); a positive phase unit `a(u)` is not removed (the certificate
requires the exact monomial phase); nothing about the analytic partition of unity.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

open CoeffFamily

theorem measurableSet_piBox_Ioc (d : ℕ) (b : ℝ) : MeasurableSet (piBox d (Ioc 0 b)) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioc

/-- The empirical exponent in the shape used throughout: `−βNφ² + β√N φ ξ`. -/
noncomputable def empExponent (φ ξ : (Fin d → ℝ) → ℝ) (β N : ℝ) (x : Fin d → ℝ) : ℝ :=
  -β * N * φ x ^ 2 + β * Real.sqrt N * φ x * ξ x

namespace ResolutionCover

variable {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι)

/-- **An exact box-core certificate** for chart `i`: adapted coordinates on the core in which the
weighted source measure is `ν ⊗ dy|_{(0,b]^{n+1}}`, the phase is the exact monomial, the
fluctuation is the chart datum's phase and the amplitude is the chart datum's observable times the
monomial weight. -/
structure ExactBoxCoreCertificate (i : ι) (core : Set (Fin d → ℝ)) {K : Type*}
    [TopologicalSpace K] [MeasurableSpace K] (ν : Measure K) (n : ℕ) (h k : Fin (n + 1) → ℕ)
    (b : ℝ) (F φ ξ : (Fin d → ℝ) → ℝ) (x : TangentialData K (n + 1)) where
  /-- adapted coordinates on the core -/
  ψ : K × (Fin (n + 1) → ℝ) → (Fin d → ℝ)
  measurable_ψ : Measurable ψ
  /-- the change-of-variables identity (an input) -/
  map_eq : Measure.map ψ (ν.prod ((volume : Measure (Fin (n + 1) → ℝ)).restrict
    (piBox (n + 1) (Ioc 0 b)))) = (R.sourceMeasure i).restrict core
  phase_eq : ∀ v u, u ∈ piBox (n + 1) (Ioc 0 b) → φ ((R.chart i).Φ (ψ (v, u))) = ∏ j, u j ^ k j
  fluct_eq : ∀ v u, u ∈ piBox (n + 1) (Ioc 0 b) →
    ξ ((R.chart i).Φ (ψ (v, u))) = evalF (toXi b (x v)) u
  amp_eq : ∀ v u, u ∈ piBox (n + 1) (Ioc 0 b) →
    F ((R.chart i).Φ (ψ (v, u))) = evalF (toEta b (x v)) u * ∏ j, u j ^ h j

variable {K : Type*} [TopologicalSpace K] [MeasurableSpace K] {ν : Measure K} [SFinite ν]
  {n : ℕ} {h k : Fin (n + 1) → ℕ} {b : ℝ} {F φ ξ : (Fin d → ℝ) → ℝ} {x : TangentialData K (n + 1)}

/-- **The pulled-back core integral is the model integral.** -/
theorem ExactBoxCoreCertificate.chartIntegral_eq_tanIntegral {i : ι} {core : Set (Fin d → ℝ)}
    (C : R.ExactBoxCoreCertificate i core ν n h k b F φ ξ x) (hFm : Measurable F)
    (hφ : Measurable φ) (hξ : Measurable ξ) (β N : ℝ)
    (hint : Integrable (fun y => F ((R.chart i).Φ y) *
      Real.exp (empExponent φ ξ β N ((R.chart i).Φ y))) ((R.sourceMeasure i).restrict core)) :
    R.chartIntegral F (empExponent φ ξ β N) i core = tanIntegral ν n h k β N b x := by
  have hGm : Measurable fun y => F ((R.chart i).Φ y) *
      Real.exp (empExponent φ ξ β N ((R.chart i).Φ y)) := by
    unfold empExponent
    exact (hFm.comp (R.measurable_chart_Φ i)).mul (Measurable.exp
      (((measurable_const.mul ((hφ.comp (R.measurable_chart_Φ i)).pow_const 2))).add
        ((measurable_const.mul (hφ.comp (R.measurable_chart_Φ i))).mul
          (hξ.comp (R.measurable_chart_Φ i)))))
  unfold chartIntegral tanIntegral dataBoxIntegral familyPhaseIntegralBox
  rw [← C.map_eq] at hint ⊢
  have hint' : Integrable (fun p : K × (Fin (n + 1) → ℝ) => F ((R.chart i).Φ (C.ψ p)) *
      Real.exp (empExponent φ ξ β N ((R.chart i).Φ (C.ψ p))))
      (ν.prod ((volume : Measure (Fin (n + 1) → ℝ)).restrict (piBox (n + 1) (Ioc 0 b)))) :=
    (integrable_map_measure hGm.aestronglyMeasurable C.measurable_ψ.aemeasurable).1 hint
  rw [integral_map C.measurable_ψ.aemeasurable hGm.aestronglyMeasurable, integral_prod _ hint']
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  refine setIntegral_congr_fun (measurableSet_piBox_Ioc _ _) fun u hu => ?_
  simp only [empExponent, C.phase_eq v u hu, C.fluct_eq v u hu, C.amp_eq v u hu]
  have hsq : (∏ j, u j ^ k j) ^ 2 = ∏ j, u j ^ (2 * k j) := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun j _ => (pow_mul' _ _ _).symm
  rw [hsq]
  congr 2
  ring

/-! ### The assembled model integral with certified cores -/

variable {M : ℕ} {Kf : Fin M → Type*} [∀ I, TopologicalSpace (Kf I)]
  [∀ I, MeasurableSpace (Kf I)] {nf : Fin M → ℕ}

/-- **Cover assembly with certified cores**: `Z(N) = gInt(x, N) + ∑ᵢ (gap contributions)`, and the
gap contributions are bounded by `e^{−βNκ/2} ∑ᵢ ∫_{gapᵢ} |F∘Φᵢ|` under the fluctuation bound on
the gaps. -/
theorem coverIntegral_eq_gInt_add (R : ResolutionCover d (Fin M))
    (νf : (I : Fin M) → Measure (Kf I))
    [∀ I, IsFiniteMeasure (νf I)] (hf kf : (I : Fin M) → Fin (nf I + 1) → ℕ) (β : ℝ)
    (bf : Fin M → ℝ) (x : JointData Kf nf) (F φ ξ : (Fin d → ℝ) → ℝ) (hFm : Measurable F)
    (hφ : Measurable φ) (hξ : Measurable ξ) {N : ℝ} (hN : 0 < N)
    (hF : Integrable F (volume.restrict (⋃ i, R.image i)))
    (hint : Integrable (fun y => F y * Real.exp (empExponent φ ξ β N y))
      (volume.restrict (⋃ i, R.image i)))
    (core : Fin M → Set (Fin d → ℝ)) (hcore : ∀ I, MeasurableSet (core I))
    (C : ∀ I, R.ExactBoxCoreCertificate I (core I) (νf I) (nf I) (hf I) (kf I) (bf I) F φ ξ
      (x.chart I))
    {κ B : ℝ} (hβ : 0 ≤ β)
    (hgap : ∀ I, ∀ y ∈ (R.chart I).dom \ core I, κ ≤ φ ((R.chart I).Φ y) ^ 2)
    (hfl : ∀ I, ∀ y ∈ (R.chart I).dom \ core I, |ξ ((R.chart I).Φ y)| ≤ B)
    (hB : 2 * B ≤ Real.sqrt (N * κ)) :
    R.coverIntegral F (empExponent φ ξ β N) =
        gInt νf hf kf β bf x N + ∑ I, R.chartIntegral F (empExponent φ ξ β N) I (core I)ᶜ ∧
      ‖∑ I, R.chartIntegral F (empExponent φ ξ β N) I (core I)ᶜ‖ ≤
        Real.exp (-(β * N * (κ / 2))) *
          ∑ I, ∫ y in (R.chart I).dom \ core I, |F ((R.chart I).Φ y)| ∂R.sourceMeasure I := by
  have hEm : Measurable (empExponent φ ξ β N) := by
    unfold empExponent
    exact ((measurable_const.mul (hφ.pow_const 2))).add ((measurable_const.mul hφ).mul hξ)
  have hGm : Measurable fun y => F y * Real.exp (empExponent φ ξ β N y) :=
    hFm.mul (Real.measurable_exp.comp hEm)
  refine ⟨?_, ?_⟩
  · unfold gInt
    rw [R.coverIntegral_eq_sum F _ hFm hEm hint, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [R.chartIntegral_univ_eq_add F _ hFm hEm hint I (hcore I),
      (C I).chartIntegral_eq_tanIntegral R hFm hφ hξ β N
        ((R.integrable_pullback hGm hint I).integrableOn)]
  · refine le_trans (norm_sum_le Finset.univ fun I =>
      R.chartIntegral F (empExponent φ ξ β N) I (core I)ᶜ) ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun I _ => ?_
    rw [R.chartIntegral_compl_eq]
    unfold chartIntegral
    have hS : MeasurableSet ((R.chart I).dom \ core I) :=
      (R.chart I).dom_compact.isClosed.measurableSet.diff (hcore I)
    have hFi := R.integrable_pullback hFm hF I
    have hb := norm_setIntegral_empirical_exp_gap_le (μ := R.sourceMeasure I)
      ((R.chart I).dom \ core I) hS (fun y => F ((R.chart I).Φ y)) (fun y => |F ((R.chart I).Φ y)|)
      (fun y => φ ((R.chart I).Φ y)) (fun y => ξ ((R.chart I).Φ y)) β N κ B hβ hN
      hFi.aestronglyMeasurable.restrict ((hφ.comp (R.measurable_chart_Φ I)).aestronglyMeasurable)
      ((hξ.comp (R.measurable_chart_Φ I)).aestronglyMeasurable) hFi.abs.integrableOn
      (fun y _ => le_of_eq (Real.norm_eq_abs _)) (hgap I) (hfl I) hB
    simpa only [empExponent] using hb

end ResolutionCover

end Grammar
