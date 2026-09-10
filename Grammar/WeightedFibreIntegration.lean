import Grammar.NormalFibreMoment
import Grammar.ChartTaylorMoment
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-!
# Weighted fibre integration and dressed moments (Astra #63 unit 5)

Measure-theoretic versions of the fibre-integration identities of `subsec:tubular_nbhd`:

* **the pushforward characterisation `eq:pushforward_char`**: integrating `f` against the base
  pushforward `τ_*Ω = Ω.map fst` is integrating `f ∘ τ` against `Ω` (`integral_map_fst`), and on a
  metrizable base a finite measure with this property for all bounded continuous `f` is the
  pushforward (`eq_map_fst_of_forall_integral`); the change of variables `eq:tubular_cov` for a
  measurable equivalence (`integral_eq_integral_comp_map_symm`);
* **weighted fibre measures**: the unnormalised fibre measure `η_v = c(v,·) du` of a nonnegative
  density (`fibreMeasure`, `integral_fibreMeasure`), of total mass `C(v)` (`fibreMeasure_univ`);
  the normalised conditional fibre of `MomentFunctional.lean` is `κ_v = C(v)⁻¹ η_v`
  (`condFibre_eq_smul_fibreMeasure`), and the **normalisation/cancellation**
  `∫ H dη_v = C(v) ∫ H dκ_v` (`integral_fibreMeasure_eq_mass_mul`) transfers to the moment pairings
  (`momentFunctional_fibreMeasure_eq`);
* **weighted Fubini `eq:pushforward_local`**: `∫ H dΩ = ∫_v ∫ H(v,u) dη_v dν` for
  `Ω = c(v,u) dν du` (`integral_omega_eq_fibreMeasure`), and for the diagonal evaluations of a
  form family the inner integrals are the normal-fibre moment pairings, unnormalised against `ν`
  or normalised against the base pushforward `τ_*Ω = C(v) dν` (`integral_omega_diag_eq_moment`,
  `integral_omega_diag_eq_condMoment`) — the paper's `∫_{S_I} ⟨D^r_⊥(φ∘π), 𝖬_{I,r}⟩ τ_*|μ_I|`;
* **dressed moments `eq:dressed_moment`**: `M̃_γ(v) = ∫ u^γ c(v,u) du` is the dressed moment of the
  fibre measure (`dressedMoment_fibreMeasure`); the chart measure `u^h e^{-βN u^{2k}} du` on the
  positive box is such a fibre measure (`dressedMeasure_eq_fibreMeasure`); and the
  **density-series interchange**: if `c(v,u) = w(u) c₀(v,u)` with `c₀(v,·) = ∑_δ a_δ u^δ` a.e. and
  `∑_δ |a_δ| ∫ |u^{γ+δ} w| < ∞`, then `M̃_γ(v) = ∑_δ a_δ M_{γ+δ}` with the bare moments
  `M_α = ∫ u^α w(u) du` (`dressedMoment_eq_tsum_bareMoment`).

Non-claims: no smooth-density pushforward on manifolds, no general disintegration theorem — the
fibres are those of a product `V × E`, and the summability of the density series is a hypothesis.
-/

open MeasureTheory Filter Set
open scoped ENNReal BoundedContinuousFunction

namespace Grammar

open MonoRep

/-! ### `eq:pushforward_char` and `eq:tubular_cov` in measure form -/

section Pushforward

variable {V E : Type*} [MeasurableSpace V] [MeasurableSpace E]

/-- **`eq:pushforward_char`, existence**: `∫ f d(τ_*Ω) = ∫ f∘τ dΩ`. -/
theorem integral_map_fst (ω : Measure (V × E)) {f : V → ℝ}
    (hf : AEStronglyMeasurable f (ω.map Prod.fst)) :
    ∫ v, f v ∂ω.map Prod.fst = ∫ p, f p.1 ∂ω :=
  integral_map measurable_fst.aemeasurable hf

/-- **`eq:pushforward_char`, uniqueness**: on a metrizable base a finite measure with the
pushforward property for all bounded continuous test functions is the pushforward. -/
theorem eq_map_fst_of_forall_integral [TopologicalSpace V]
    [TopologicalSpace.PseudoMetrizableSpace V] [BorelSpace V] (ω : Measure (V × E))
    [IsFiniteMeasure ω] (μ : Measure V) [IsFiniteMeasure μ]
    (h : ∀ f : V →ᵇ ℝ, ∫ v, f v ∂μ = ∫ p, f p.1 ∂ω) : μ = ω.map Prod.fst := by
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  rw [h f, integral_map_fst ω f.continuous.measurable.aestronglyMeasurable]

/-- **`eq:tubular_cov`, measure form**: for a measurable equivalence `Φ` onto the tube,
`∫ F dμ = ∫ (F ∘ Φ) d(Φ^*μ)` with `Φ^*μ = μ.map Φ⁻¹`. -/
theorem integral_eq_integral_comp_map_symm {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (Φ : A ≃ᵐ B) (μ : Measure B) (F : B → ℝ) :
    ∫ y, F y ∂μ = ∫ x, F (Φ x) ∂μ.map Φ.symm := by
  rw [integral_map_equiv]
  simp

end Pushforward

/-! ### Weighted fibre measures and the normalisation cancellation -/

section Fibre

variable {V E : Type*} [MeasurableSpace E] (vol : Measure E)

/-- **The unnormalised weighted fibre measure** `η_v = c(v,·) du`. -/
noncomputable def fibreMeasure (c : V × E → ℝ) (v : V) : Measure E :=
  vol.withDensity fun u => ENNReal.ofReal (c (v, u))

variable {c : V × E → ℝ}

theorem integral_fibreMeasure [MeasurableSpace V] (hc : Measurable c) (hc0 : ∀ p, 0 ≤ c p) (v : V)
    (H : E → ℝ) :
    ∫ u, H u ∂fibreMeasure vol c v = ∫ u, c (v, u) * H u ∂vol := by
  unfold fibreMeasure
  have hmv : Measurable fun u : E => ENNReal.ofReal (c (v, u)) :=
    (hc.comp measurable_prodMk_left).ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hmv
    (Eventually.of_forall fun u => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [ENNReal.toReal_ofReal (hc0 (v, u)), smul_eq_mul]

theorem fibreMeasure_univ (v : V) : fibreMeasure vol c v univ = fibreMass vol c v := by
  unfold fibreMeasure fibreMass
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]

/-- The normalised conditional fibre is the mass-normalised fibre measure `κ_v = C(v)⁻¹ η_v`. -/
theorem condFibre_eq_smul_fibreMeasure (v : V) :
    condFibre vol c v = (fibreMass vol c v)⁻¹ • fibreMeasure vol c v := rfl

/-- **Normalisation/cancellation**: `∫ H dη_v = C(v) ∫ H dκ_v` (both sides vanish when `C(v) = 0`).
-/
theorem integral_fibreMeasure_eq_mass_mul (v : V) (hfin : fibreMass vol c v ≠ ∞) (H : E → ℝ) :
    ∫ u, H u ∂fibreMeasure vol c v = (fibreMass vol c v).toReal * ∫ u, H u ∂condFibre vol c v := by
  rw [condFibre_eq_smul_fibreMeasure, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]
  by_cases h0 : fibreMass vol c v = 0
  · have hz : fibreMeasure vol c v = 0 :=
      Measure.measure_univ_eq_zero.1 ((fibreMeasure_univ vol v).trans h0)
    rw [hz, h0]
    simp
  · rw [← mul_assoc, mul_inv_cancel₀ (ENNReal.toReal_ne_zero.2 ⟨h0, hfin⟩), one_mul]

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [OpensMeasurableSpace E] {r : ℕ}

/-- The moment pairings of the unnormalised and the conditional fibre measures differ by the fibre
mass. -/
theorem momentFunctional_fibreMeasure_eq (v : V) (hfin : fibreMass vol c v ≠ ∞)
    (hr : Integrable (fun u => ‖u‖ ^ r) (fibreMeasure vol c v))
    (hr' : Integrable (fun u => ‖u‖ ^ r) (condFibre vol c v)) (α : JetForm E r) :
    momentFunctional (fibreMeasure vol c v) hr α =
      (fibreMass vol c v).toReal * momentFunctional (condFibre vol c v) hr' α := by
  simp only [momentFunctional_apply]
  exact integral_fibreMeasure_eq_mass_mul vol v hfin _

end Fibre

/-! ### Weighted Fubini `eq:pushforward_local` -/

section Fubini

variable {V E : Type*} [MeasurableSpace V] [MeasurableSpace E] (ν : Measure V) (vol : Measure E)
  {c : V × E → ℝ} (hc : Measurable c) (hc0 : ∀ p, 0 ≤ c p) [SFinite vol] [SFinite ν]
include hc hc0

/-- **`eq:pushforward_local`, fibre-measure form**: `∫ H dΩ = ∫_v ∫ H(v,u) dη_v dν`. -/
theorem integral_omega_eq_fibreMeasure {H : V × E → ℝ} (hH : Integrable H (omegaMeasure ν vol c)) :
    ∫ p, H p ∂omegaMeasure ν vol c = ∫ v, ∫ u, H (v, u) ∂fibreMeasure vol c v ∂ν := by
  rw [integral_omega_eq_prod ν vol hc hc0 hH]
  exact integral_congr_ae (Eventually.of_forall fun v =>
    (integral_fibreMeasure vol hc hc0 v _).symm)

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [OpensMeasurableSpace E] {r : ℕ}

/-- **The per-stratum integral as an integral of moment pairings, unnormalised**: for a family of
`r`-forms `A v` on the fibre, `∫ A_v(u,…,u) dΩ = ∫_v ⟨A_v, 𝖬_r(η_v)⟩ dν`. -/
theorem integral_omega_diag_eq_moment (A : V → JetForm E r)
    (hr : ∀ v, Integrable (fun u => ‖u‖ ^ r) (fibreMeasure vol c v))
    (hH : Integrable (fun p : V × E => A p.1 fun _ => p.2) (omegaMeasure ν vol c)) :
    ∫ p, A p.1 (fun _ => p.2) ∂omegaMeasure ν vol c =
      ∫ v, momentFunctional (fibreMeasure vol c v) (hr v) (A v) ∂ν := by
  rw [integral_omega_eq_fibreMeasure ν vol hc hc0 hH]
  rfl

/-- **The per-stratum integral as an integral of moment pairings against the base pushforward**:
`∫ A_v(u,…,u) dΩ = ∫_v ⟨A_v, 𝖬_r(κ_v)⟩ d(τ_*Ω)` with `τ_*Ω = C(v) dν` — the paper's
`∫_{S_I} ⟨D^r_⊥(φ∘π), 𝖬_{I,r}⟩ τ_*|μ_I|`. -/
theorem integral_omega_diag_eq_condMoment (A : V → JetForm E r) (hfin : ∀ v, fibreMass vol c v ≠ ∞)
    (hr : ∀ v, Integrable (fun u => ‖u‖ ^ r) (condFibre vol c v))
    (hH : Integrable (fun p : V × E => A p.1 fun _ => p.2) (omegaMeasure ν vol c)) :
    ∫ p, A p.1 (fun _ => p.2) ∂omegaMeasure ν vol c =
      ∫ v, momentFunctional (condFibre vol c v) (hr v) (A v)
        ∂(omegaMeasure ν vol c).map Prod.fst := by
  rw [map_fst_omega ν vol hc, integral_omega_eq_condFibre ν vol hc hc0 hfin hH]
  rfl

end Fubini

/-! ### Dressed moments `eq:dressed_moment` -/

section Dressed

variable {V : Type*} {d : ℕ} (vol : Measure (Fin d → ℝ))

/-- **`eq:dressed_moment`, first expression**: `M̃_γ(v) = ∫ u^γ c(v,u) du` is the dressed moment of
the weighted fibre measure. -/
theorem dressedMoment_fibreMeasure [MeasurableSpace V] {c : V × (Fin d → ℝ) → ℝ}
    (hc : Measurable c)
    (hc0 : ∀ p, 0 ≤ c p) (v : V) (γ : Fin d → ℕ) :
    dressedMoment (fibreMeasure vol c v) γ = ∫ u, c (v, u) * mono γ u ∂vol := by
  unfold dressedMoment
  exact integral_fibreMeasure vol hc hc0 v _

/-- The chart measure `u^h e^{-βN u^{2k}} du` on the positive box is the weighted fibre measure of
the bare weight (constant along the base). -/
theorem dressedMeasure_eq_fibreMeasure (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N b : ℝ) (v : V) :
    dressedMeasure n h k β N b =
      fibreMeasure (volume.restrict (piBox (n + 1) (Ioc 0 b)))
        (fun p : V × (Fin (n + 1) → ℝ) =>
          (∏ i, p.2 i ^ h i) * Real.exp (-(β * N * ∏ i, p.2 i ^ (2 * k i)))) v := rfl

/-- **The bare moment** `M_α = ∫ u^α w(u) du` of a weight `w`. -/
noncomputable def bareMoment (w : (Fin d → ℝ) → ℝ) (α : Fin d → ℕ) : ℝ := ∫ u, mono α u * w u ∂vol

/-- **`eq:dressed_moment`, density-series interchange**: if the density factor is a monomial series
`c₀(v,u) = ∑_δ a_δ u^δ` a.e. and `∑_δ |a_δ| ∫ |u^{γ+δ} w(u)| du < ∞`, then
`∫ u^γ w(u) c₀(v,u) du = ∑_δ a_δ M_{γ+δ}`. -/
theorem dressedMoment_eq_tsum_bareMoment (w : (Fin d → ℝ) → ℝ) (c₀ : (Fin d → ℝ) → ℝ)
    (a : (Fin d → ℕ) → ℝ) (γ : Fin d → ℕ)
    (hc₀ : ∀ᵐ u ∂vol, HasSum (fun δ => a δ * mono δ u) (c₀ u))
    (hint : ∀ δ, Integrable (fun u => mono (γ + δ) u * w u) vol)
    (hsum : Summable fun δ => |a δ| * ∫ u, |mono (γ + δ) u * w u| ∂vol) :
    ∫ u, mono γ u * w u * c₀ u ∂vol = ∑' δ, a δ * bareMoment vol w (γ + δ) := by
  have hF_int : ∀ δ, Integrable (fun u => a δ * (mono (γ + δ) u * w u)) vol :=
    fun δ => (hint δ).const_mul _
  have hF_sum : Summable fun δ => ∫ u, ‖a δ * (mono (γ + δ) u * w u)‖ ∂vol := by
    refine hsum.congr fun δ => ?_
    simp_rw [norm_mul, Real.norm_eq_abs, integral_const_mul, abs_mul]
  have h := integral_tsum_of_summable_integral_norm hF_int hF_sum
  simp_rw [integral_const_mul] at h
  unfold bareMoment
  rw [h]
  refine integral_congr_ae ?_
  filter_upwards [hc₀] with u hu
  rw [← hu.tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun δ => ?_
  rw [mono_add]
  ring

end Dressed

end Grammar
