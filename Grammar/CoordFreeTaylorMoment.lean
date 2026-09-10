import Grammar.WeightedFibreIntegration

/-!
# The coordinate-free Taylor–moment expansion (Astra #63 unit 6)

Corrected identity versions of `eq:per_stratum_expansion_coordfree` and `eq:tubular_expansion`.
For a chosen normal family `N`, fibre maps `Φ`, weighted fibre measures `η s` and an observable `F`
whose fibre restriction `G_s = F ∘ Φ_s` has a power series at `0` dominating the moments of `η s`:

* **the infinite expansion** `∫ F∘Φ_s dη_s = ∑_r ⟨D^r_⊥F(s), 𝖬_r(s)⟩`
  (`integral_eq_tsum_normalContraction`), with **no** extra `1/r!` — the paper's
  `eq:per_stratum_expansion_coordfree` carries a spurious `1/r!` relative to `defn:normal_diff`
  (the factorial is inside `D^r_⊥ = T_r = J_r/r!`); the terms are bounded by `‖p_r‖ ∫‖ξ‖^r` and
  summable (`abs_normalContraction_le`, `summable_normalContraction`);
* **the finite expansion with exact integrated remainder**:
  `∫ G_s dη_s = ∑_{r<K} ⟨T_r, 𝖬_r⟩ + ∫ R_K dη_s` with `R_K = G_s − ∑_{r<K} T_r(ξ,…,ξ)`, the
  integrated remainder being the tail of the contraction series (`integral_remainder_eq_tail`),
  bounded by the tail of the dominating series and tending to `0`
  (`abs_tail_normalContraction_le`, `tendsto_tail_normalContraction`);
* **the integrated multi-index/factorial bridge**: on `ℝ^d`,
  `∫ G dη = ∑_r ∑_{|b|=r} (∂^bG(0)/b!) M̃_b` (`integral_eq_tsum_multiIndex`), hence in a fibre
  frame `e : ℝ^d ≃L N s`, `∫ F∘Φ_s dη_s = ∑_r ∑_{|b|=r} (∂^b(F∘Φ_s∘e)(0)/b!) M̃_b(s)` with the
  dressed moments of the frame measure (`integral_eq_tsum_multiIndex_frame`) — no global
  regularity of `F∘Φ_s` is needed;
* **`eq:tubular_expansion`, identity version**: for the per-stratum measure `Ω = c(v,u) dν du` on a
  trivialised tube with fibrewise power series and domination,
  `∫ H dΩ = ∫_v ∑_r ∑_{|γ|=r} (1/γ!) ∂^γ_u H(v,0) M̃_γ(v) dν(v)` (`integral_omega_eq_tsum_dressed`);
* **invariance under transported fibre presentations**: `Φ' = Φ∘L`, `η' = L⁻¹_*η` leave the fibre
  integral unchanged (`integral_fibre_reparam`; the terms are invariant by
  `normalContraction_reparam`).

Non-claims: no asymptotic ordering in the normal degree — these are exact convergent identities
under explicit absolute summability; the paper's `∼` in `eq:tubular_expansion` (asymptotics in `n`)
is the quantitative chart theorem, not reproduced here.
-/

open MeasureTheory Filter Topology
open scoped ContDiff ENNReal
open Finset

namespace Grammar

open MonoRep

/-! ### The multi-index bridge on `ℝ^d` -/

section MultiIndex

variable {d : ℕ}

/-- **The integrated multi-index bridge**: `∫ G dη = ∑_r ∑_{|b|=r} (∂^bG(0)/b!) M̃_b` for a power
series dominating the moments. -/
theorem integral_eq_tsum_multiIndex {G : (Fin d → ℝ) → ℝ}
    {q : FormalMultilinearSeries ℝ (Fin d → ℝ) ℝ} {R : ℝ≥0∞} (hq : HasFPowerSeriesOnBall G q 0 R)
    (η : Measure (Fin d → ℝ)) (hη : ∀ᵐ u ∂η, u ∈ Metric.eball (0 : Fin d → ℝ) R)
    (hr : ∀ r, Integrable (fun u => ‖u‖ ^ r) η)
    (hdom : Summable fun r => ‖q r‖ * ∫ u, ‖u‖ ^ r ∂η) :
    ∫ u, G u ∂η = ∑' r, ∑ b ∈ Finset.Nat.antidiagonalTuple d r,
      (∏ i, ((b i).factorial : ℝ))⁻¹ * weightComponent (normalJet G r) b * dressedMoment η b := by
  rw [integral_eq_tsum_moment hq η hη hr hdom]
  refine tsum_congr fun r => ?_
  rw [momentFunctional_apply, ← integral_const_mul]
  have hG : ContDiffAt ℝ ω G 0 := hq.analyticAt.contDiffAt
  have h1 : ∀ u, (r.factorial : ℝ)⁻¹ * normalJet G r (fun _ => u) =
      ∑ b ∈ Finset.Nat.antidiagonalTuple d r,
        (∏ i, ((b i).factorial : ℝ))⁻¹ * weightComponent (normalJet G r) b * mono b u :=
    fun u => homogeneousTaylor_eq_sum_multiIndex hG r u
  simp_rw [h1]
  rw [integral_finsetSum _ fun b hb => (integrable_mono_of_sum_eq (hr r)
    (Finset.Nat.mem_antidiagonalTuple.1 hb)).const_mul _]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_const_mul]
  rfl

end MultiIndex

/-! ### The per-fibre expansion for a chosen normal family -/

section Family

variable {S : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] {M : Type*}

variable (N : S → Submodule ℝ E) (η : ∀ s, Measure (N s))
  (hr : ∀ (r : ℕ) (s : S), Integrable (fun ξ : N s => ‖ξ‖ ^ r) (η s)) (Φ : ∀ s, N s → M) (F : M → ℝ)
  {s : S} {p : FormalMultilinearSeries ℝ (N s) ℝ} {R : ℝ≥0∞}
  (hp : HasFPowerSeriesOnBall (fun ξ : N s => F (Φ s ξ)) p 0 R)

include hp in
/-- Each contraction is a Taylor–moment term of the fibre series. -/
theorem normalContraction_eq_integral_series (r : ℕ) :
    normalContraction N η (hr r) Φ F s = ∫ ξ, p r (fun _ => ξ) ∂η s := by
  rw [normalContraction_eq_integral]
  exact integral_congr_ae (Eventually.of_forall fun ξ => homogeneousTaylor_eq_series hp r ξ)

include hp in
/-- **Term bound**: `|⟨D^r_⊥F(s), 𝖬_r(s)⟩| ≤ ‖p_r‖ ∫‖ξ‖^r dη_s`. -/
theorem abs_normalContraction_le (r : ℕ) :
    |normalContraction N η (hr r) Φ F s| ≤ ‖p r‖ * ∫ ξ, ‖ξ‖ ^ r ∂η s := by
  rw [normalContraction_eq_integral_series N η hr Φ F hp r, ← Real.norm_eq_abs,
    ← integral_const_mul]
  exact norm_integral_le_of_norm_le ((hr r s).const_mul _)
    (Eventually.of_forall fun ξ => norm_diagEval_le (p r) ξ)

include hp in
theorem summable_normalContraction (hdom : Summable fun r => ‖p r‖ * ∫ ξ, ‖ξ‖ ^ r ∂η s) :
    Summable fun r => normalContraction N η (hr r) Φ F s :=
  hdom.of_norm_bounded fun r => by
    rw [Real.norm_eq_abs]
    exact abs_normalContraction_le N η hr Φ F hp r

include hp in
/-- **`eq:per_stratum_expansion_coordfree`, corrected identity version**: for a fibre measure
carried by the ball of convergence with moments dominated by the series,
`∫ F∘Φ_s dη_s = ∑_r ⟨D^r_⊥F(s), 𝖬_r(s)⟩` (no additional `1/r!`: `D^r_⊥ = J_r/r!`). -/
theorem integral_eq_tsum_normalContraction (hη : ∀ᵐ ξ ∂η s, ξ ∈ Metric.eball (0 : N s) R)
    (hdom : Summable fun r => ‖p r‖ * ∫ ξ, ‖ξ‖ ^ r ∂η s) :
    ∫ ξ, F (Φ s ξ) ∂η s = ∑' r, normalContraction N η (hr r) Φ F s := by
  rw [integral_eq_tsum_moment hp (η s) hη (fun r => hr r s) hdom]
  refine tsum_congr fun r => ?_
  rw [normalContraction_eq_integral_series N η hr Φ F hp r, ← moment_contraction hp (η s) (hr r s)]

include hp in
/-- **Finite expansion with exact integrated remainder**: with `R_K = F∘Φ_s − ∑_{r<K} T_r(ξ,…,ξ)`,
`∫ R_K dη_s = ∑_{r ≥ K} ⟨D^r_⊥F(s), 𝖬_r(s)⟩`, the tail of the contraction series. -/
theorem integral_remainder_eq_tail (hη : ∀ᵐ ξ ∂η s, ξ ∈ Metric.eball (0 : N s) R)
    (hdom : Summable fun r => ‖p r‖ * ∫ ξ, ‖ξ‖ ^ r ∂η s)
    (hG : Integrable (fun ξ : N s => F (Φ s ξ)) (η s)) (K : ℕ) :
    ∫ ξ, (F (Φ s ξ) - ∑ r ∈ Finset.range K,
        homogeneousTaylor (fun ξ : N s => F (Φ s ξ)) r ξ) ∂η s =
      ∑' r, normalContraction N η (hr (r + K)) Φ F s := by
  have hint : ∀ r ∈ Finset.range K,
      Integrable (fun ξ : N s => homogeneousTaylor (fun ξ : N s => F (Φ s ξ)) r ξ) (η s) := by
    intro r _
    have := integrable_diagEval (η s) (hr r s)
      ((r.factorial : ℝ)⁻¹ • normalJet (fun ξ : N s => F (Φ s ξ)) r)
    refine this.congr (Eventually.of_forall fun ξ => ?_)
    simp [homogeneousTaylor]
  rw [integral_sub hG (integrable_finsetSum _ hint), integral_finsetSum _ hint,
    integral_eq_tsum_normalContraction N η hr Φ F hp hη hdom,
    ← (summable_normalContraction N η hr Φ F hp hdom).sum_add_tsum_nat_add K,
    Finset.sum_congr rfl fun r _ => (normalContraction_eq_integral N η (hr r) Φ F s).symm,
    add_sub_cancel_left]

include hp in
/-- **Tail bound**: `|∑_{r ≥ K} ⟨D^r_⊥F, 𝖬_r⟩| ≤ ∑_{r ≥ K} ‖p_r‖ ∫‖ξ‖^r dη_s`. -/
theorem abs_tail_normalContraction_le (hdom : Summable fun r => ‖p r‖ * ∫ ξ, ‖ξ‖ ^ r ∂η s) (K : ℕ) :
    |∑' r, normalContraction N η (hr (r + K)) Φ F s| ≤
      ∑' r, ‖p (r + K)‖ * ∫ ξ, ‖ξ‖ ^ (r + K) ∂η s := by
  have hs : Summable fun r => ‖p (r + K)‖ * ∫ ξ, ‖ξ‖ ^ (r + K) ∂η s :=
    (summable_nat_add_iff K).2 hdom
  have hs' : Summable fun r => ‖normalContraction N η (hr (r + K)) Φ F s‖ :=
    hs.of_nonneg_of_le (fun r => norm_nonneg _) fun r => by
      rw [Real.norm_eq_abs]
      exact abs_normalContraction_le N η hr Φ F hp (r + K)
  rw [← Real.norm_eq_abs]
  exact (norm_tsum_le_tsum_norm hs').trans
    (hs'.tsum_le_tsum (fun r => by
      rw [Real.norm_eq_abs]
      exact abs_normalContraction_le N η hr Φ F hp (r + K)) hs)

include hp in
/-- The integrated remainders tend to zero. -/
theorem tendsto_tail_normalContraction (hdom : Summable fun r => ‖p r‖ * ∫ ξ, ‖ξ‖ ^ r ∂η s) :
    Tendsto (fun K => ∑' r, normalContraction N η (hr (r + K)) Φ F s) atTop (𝓝 0) := by
  refine squeeze_zero_norm (fun K => ?_) (tendsto_sum_nat_add fun r => ‖p r‖ * ∫ ξ, ‖ξ‖ ^ r ∂η s)
  rw [Real.norm_eq_abs]
  exact abs_tail_normalContraction_le N η hr Φ F hp hdom K

end Family

/-! ### Fibre frames and transported presentations -/

section Frame

variable {S : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] {M : Type*} {d : ℕ}

variable (N : S → Submodule ℝ E) (η : ∀ s, Measure (N s)) (Φ : ∀ s, N s → M) (F : M → ℝ) (s : S)

/-- Change of variables along a fibre frame `e : V ≃L N s` (no measurability of the integrand
needed: `e⁻¹` is a measurable embedding). -/
theorem integral_fibre_frame {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] (e : V ≃L[ℝ] N s) :
    ∫ u, F (Φ s (e u)) ∂(η s).map (e.symm : N s →L[ℝ] V) = ∫ ξ, F (Φ s ξ) ∂η s := by
  have h := integral_map_equiv (μ := η s) (e.symm.toHomeomorph.toMeasurableEquiv)
    (fun u : V => F (Φ s (e u)))
  simp only [Homeomorph.toMeasurableEquiv_coe, ContinuousLinearEquiv.coe_toHomeomorph,
    ContinuousLinearEquiv.apply_symm_apply] at h
  exact h

/-- **Invariance under transported fibre presentations**: `Φ' = Φ∘L`, `η' = L⁻¹_*η` leave the fibre
integral unchanged. -/
theorem integral_fibre_reparam (L : N s ≃L[ℝ] N s) :
    ∫ ξ, F (Φ s (L ξ)) ∂(η s).map (L.symm : N s →L[ℝ] N s) = ∫ ξ, F (Φ s ξ) ∂η s :=
  integral_fibre_frame N η Φ F s L

/-- **The integrated multi-index bridge in a fibre frame**: with `G_e = F∘Φ_s∘e` having a power
series at `0` dominating the moments of the frame measure `η_s^e = (e⁻¹)_*η_s`,
`∫ F∘Φ_s dη_s = ∑_r ∑_{|b|=r} (∂^bG_e(0)/b!) M̃_b(s)`. -/
theorem integral_eq_tsum_multiIndex_frame (e : (Fin d → ℝ) ≃L[ℝ] N s)
    {q : FormalMultilinearSeries ℝ (Fin d → ℝ) ℝ} {R : ℝ≥0∞}
    (hq : HasFPowerSeriesOnBall (fun u : Fin d → ℝ => F (Φ s (e u))) q 0 R)
    (hη : ∀ᵐ u ∂(η s).map (e.symm : N s →L[ℝ] (Fin d → ℝ)), u ∈ Metric.eball (0 : Fin d → ℝ) R)
    (hr : ∀ r, Integrable (fun u => ‖u‖ ^ r) ((η s).map (e.symm : N s →L[ℝ] (Fin d → ℝ))))
    (hdom : Summable fun r =>
      ‖q r‖ * ∫ u, ‖u‖ ^ r ∂(η s).map (e.symm : N s →L[ℝ] (Fin d → ℝ))) :
    ∫ ξ, F (Φ s ξ) ∂η s = ∑' r, ∑ b ∈ Finset.Nat.antidiagonalTuple d r,
      (∏ i, ((b i).factorial : ℝ))⁻¹ *
        weightComponent (normalJet (fun u : Fin d → ℝ => F (Φ s (e u))) r) b *
          dressedMoment ((η s).map (e.symm : N s →L[ℝ] (Fin d → ℝ))) b := by
  rw [← integral_fibre_frame N η Φ F s e]
  exact integral_eq_tsum_multiIndex hq _ hη hr hdom

end Frame

/-! ### `eq:tubular_expansion` as an identity on a trivialised tube -/

section Tube

variable {V : Type*} [MeasurableSpace V] {d : ℕ} (ν : Measure V) (vol : Measure (Fin d → ℝ))
  {c : V × (Fin d → ℝ) → ℝ} (hc : Measurable c) (hc0 : ∀ p, 0 ≤ c p) [SFinite vol] [SFinite ν]

include hc hc0 in
/-- **`eq:tubular_expansion`, identity version**: for `Ω = c(v,u) dν du` and an observable `H`
whose fibre restrictions `H(v,·)` have power series at `0` dominating the moments of the weighted
fibre measures `η_v = c(v,·)du`,
`∫ H dΩ = ∫_v ∑_r ∑_{|γ|=r} (1/γ!) ∂^γ_u H(v,0) M̃_γ(v) dν(v)`, `M̃_γ(v) = ∫ u^γ c(v,u) du`. -/
theorem integral_omega_eq_tsum_dressed {H : V × (Fin d → ℝ) → ℝ}
    (hH : Integrable H (omegaMeasure ν vol c))
    (q : V → FormalMultilinearSeries ℝ (Fin d → ℝ) ℝ) (R : V → ℝ≥0∞)
    (hq : ∀ v, HasFPowerSeriesOnBall (fun u => H (v, u)) (q v) 0 (R v))
    (hη : ∀ v, ∀ᵐ u ∂fibreMeasure vol c v, u ∈ Metric.eball (0 : Fin d → ℝ) (R v))
    (hr : ∀ v r, Integrable (fun u => ‖u‖ ^ r) (fibreMeasure vol c v))
    (hdom : ∀ v, Summable fun r => ‖q v r‖ * ∫ u, ‖u‖ ^ r ∂fibreMeasure vol c v) :
    ∫ p, H p ∂omegaMeasure ν vol c = ∫ v, ∑' r, ∑ b ∈ Finset.Nat.antidiagonalTuple d r,
      (∏ i, ((b i).factorial : ℝ))⁻¹ * weightComponent (normalJet (fun u => H (v, u)) r) b *
        dressedMoment (fibreMeasure vol c v) b ∂ν := by
  rw [integral_omega_eq_fibreMeasure ν vol hc hc0 hH]
  exact integral_congr_ae (Eventually.of_forall fun v =>
    integral_eq_tsum_multiIndex (hq v) _ (hη v) (hr v) (hdom v))

end Tube

end Grammar
