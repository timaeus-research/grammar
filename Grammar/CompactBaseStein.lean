/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PosteriorWeightStein
import Grammar.CompactBaseGaussian
import Grammar.QuenchedSource

/-!
# Stein's identity for posterior averages on the compact base (§20, replicas)

For a Gaussian field `G` on the compact base `K` with covariance kernel `𝒞` and the limit
posterior `⟨φ⟩_g = ∫ φ S_λ(g) dρ / D_ρ(g)` (`compactAvg`), the Gaussian integration-by-parts
identity for the posterior average of a continuous observable `f` reads

★★★ `GaussianField.integral_eval_mul_compactAvg`:
`E[G(x₀) ⟨f⟩_G] = β E[⟨f · 𝒞(x₀,·)⟩^{½}_G − ⟨f⟩_G ⟨𝒞(x₀,·)⟩^{½}_G]`,

where `⟨φ⟩^{½}_g = ∫ φ S_{λ+1/2}(g) dρ / D_ρ(g)` (`compactHalfAvg`) is the posterior average of
`φ(x)√t` on the joint Gibbs measure `μ_g(dx dt) ∝ t^{λ−1} e^{−βt + βg(x)√t} dρ dt`.  This is
`E[G(x₀) F(G)] = E[DF(G)[𝒞(x₀,·)]]` with the Fréchet derivative
`DF_f(g)[h] = β(⟨f √t h⟩_g − ⟨f⟩_g ⟨√t h⟩_g)` of the posterior average (Astra #162 §5): the
one-covariance-line identity whose two-replica form is
`β E⟨f(x₁)(√t₁ 𝒞(x₀,x₁) − √t₂ 𝒞(x₀,x₂))⟩^{⊗2}_G`.

Route: on a quantised base `ρ ∘ q⁻¹` the identity is the finite-atom Stein identity
`integral_coord_mul_postAvg_tail` for the joint Gaussian vector `(G(x₀), G(atoms))` supplied by
`GaussianField.law` (`integral_eval_mul_compactAvg_map`); the passage to `ρ` is dominated
convergence along a quantisation sequence with the bounds `|⟨f⟩_g| ≤ ‖f‖` and
`|⟨φ⟩^{½}_g| ≤ ‖φ‖(√(2λ/β) + ‖g‖/2)` (`abs_compactHalfAvg_le`).

Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

section Defs

variable {K : Type*} [MeasurableSpace K]

/-- The posterior average of `φ(x) √t`: `⟨φ⟩^{½}_g = ∫ φ S_{λ+1/2}(g) dρ / D_ρ(g)`. -/
noncomputable def compactHalfAvg (β lam : ℝ) (ρ : Measure K) (g φ : K → ℝ) : ℝ :=
  compactWeighted β (lam + 1 / 2) ρ g φ / compactD β lam ρ g

end Defs

section Bounds

variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {β lam : ℝ} (ρ : Measure K) [IsFiniteMeasure ρ] (hβ : 0 < β) (hlam : 0 < lam)
include hβ hlam

/-- `x ↦ φ(x) S_ν(g(x))` as a continuous map. -/
noncomputable def weightedFluctC (ν : ℝ) (hν : 0 < ν) (φ g : C(K, ℝ)) : C(K, ℝ) :=
  ⟨fun x => φ x * fluctuation β ν (g x),
    φ.continuous.mul ((continuous_fluctuation β ν hβ hν).comp g.continuous)⟩

omit [CompactSpace K] [MeasurableSpace K] [BorelSpace K] hlam in
theorem weightedFluctC_apply (ν : ℝ) (hν : 0 < ν) (φ g : C(K, ℝ)) (x : K) :
    weightedFluctC hβ ν hν φ g x = φ x * fluctuation β ν (g x) := rfl

/-- `|⟨f⟩_g| ≤ ‖f‖`. -/
theorem abs_compactAvg_le (hρ : ρ ≠ 0) (g : C(K, ℝ)) (f : C(K, ℝ)) :
    |compactAvg β lam ρ g f| ≤ ‖f‖ := by
  have hD := compactD_pos ρ hβ hlam hρ g
  unfold compactAvg compactWeighted
  rw [abs_div, abs_of_pos hD, div_le_iff₀ hD]
  refine abs_integral_le_integral_abs.trans ?_
  unfold compactD
  rw [← integral_const_mul]
  refine integral_mono ((integrable_mul_fluctuation_comp ρ hβ hlam g f.continuous.measurable
    (C := ‖f‖) fun x => by
      have := f.norm_coe_le_norm x
      rwa [Real.norm_eq_abs] at this).abs)
    ((integrable_fluctuation_comp ρ hβ hlam g).const_mul _) fun x => ?_
  have hS := fluctuation_pos β lam (g x) hβ hlam
  rw [abs_mul, abs_of_pos hS]
  refine mul_le_mul_of_nonneg_right ?_ hS.le
  have := f.norm_coe_le_norm x
  rwa [Real.norm_eq_abs] at this

/-- `|⟨φ⟩^{½}_g| ≤ ‖φ‖ (√(2λ/β) + ‖g‖/2)`. -/
theorem abs_compactHalfAvg_le (hρ : ρ ≠ 0) (g : C(K, ℝ)) (φ : C(K, ℝ)) :
    |compactHalfAvg β lam ρ g φ| ≤ ‖φ‖ * (Real.sqrt (2 * lam / β) + ‖g‖ / 2) := by
  have hD := compactD_pos ρ hβ hlam hρ g
  have hB : 0 ≤ Real.sqrt (2 * lam / β) + ‖g‖ / 2 := by positivity
  unfold compactHalfAvg compactWeighted
  rw [abs_div, abs_of_pos hD, div_le_iff₀ hD]
  refine abs_integral_le_integral_abs.trans ?_
  unfold compactD
  rw [← integral_const_mul]
  refine integral_mono ((integrable_mul_fluctuation_comp ρ hβ (by linarith) g
    φ.continuous.measurable (C := ‖φ‖) fun x => by
      have := φ.norm_coe_le_norm x
      rwa [Real.norm_eq_abs] at this).abs)
    ((integrable_fluctuation_comp ρ hβ hlam g).const_mul _) fun x => ?_
  have hS := fluctuation_pos β lam (g x) hβ hlam
  have hS' := fluctuation_pos β (lam + 1 / 2) (g x) hβ (by linarith)
  rw [abs_mul, abs_of_pos hS']
  have hφx : |φ x| ≤ ‖φ‖ := by
    have := φ.norm_coe_le_norm x
    rwa [Real.norm_eq_abs] at this
  have hgx : |g x| ≤ ‖g‖ := by
    have := g.norm_coe_le_norm x
    rwa [Real.norm_eq_abs] at this
  have h1 := fluctuation_half_le hβ hlam (g x)
  have h2 : Real.sqrt (2 * lam / β + max (g x) 0 ^ 2 / 4) ≤
      Real.sqrt (2 * lam / β) + ‖g‖ / 2 := by
    refine (sqrt_le_sqrt_add (2 * lam / β) (max (g x) 0) (by positivity)).trans ?_
    have : |max (g x) 0| ≤ ‖g‖ := by
      rw [abs_of_nonneg (le_max_right _ _)]
      exact max_le ((le_abs_self _).trans hgx) (norm_nonneg g)
    linarith
  calc |φ x| * fluctuation β (lam + 1 / 2) (g x) ≤
        ‖φ‖ * (Real.sqrt (2 * lam / β + max (g x) 0 ^ 2 / 4) * fluctuation β lam (g x)) :=
        mul_le_mul hφx h1 hS'.le (norm_nonneg _)
    _ ≤ ‖φ‖ * ((Real.sqrt (2 * lam / β) + ‖g‖ / 2) * fluctuation β lam (g x)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 hS.le) (norm_nonneg _)
    _ = ‖φ‖ * (Real.sqrt (2 * lam / β) + ‖g‖ / 2) * fluctuation β lam (g x) := by ring

/-! ### Quantised bases -/

variable (g : C(K, ℝ)) {q : K → K} (hq : Measurable q)
include hq

omit [CompactSpace K] [IsFiniteMeasure ρ] hlam in
theorem compactWeighted_map (ν : ℝ) (hν : 0 < ν) (φ : C(K, ℝ)) :
    compactWeighted β ν (ρ.map q) g φ = ∫ x, φ (q x) * fluctuation β ν (g (q x)) ∂ρ := by
  unfold compactWeighted
  exact integral_map hq.aemeasurable
    (weightedFluctC hβ ν hν φ g).continuous.measurable.aestronglyMeasurable

omit [CompactSpace K] [IsFiniteMeasure ρ] in
theorem compactAvg_map (f : C(K, ℝ)) :
    compactAvg β lam (ρ.map q) g f =
      (∫ x, f (q x) * fluctuation β lam (g (q x)) ∂ρ) / compactD β lam (ρ.map q) g := by
  unfold compactAvg
  rw [compactWeighted_map ρ hβ g hq lam hlam]

omit [CompactSpace K] [IsFiniteMeasure ρ] in
theorem compactHalfAvg_map (φ : C(K, ℝ)) :
    compactHalfAvg β lam (ρ.map q) g φ =
      (∫ x, φ (q x) * fluctuation β (lam + 1 / 2) (g (q x)) ∂ρ) / compactD β lam (ρ.map q) g := by
  unfold compactHalfAvg
  rw [compactWeighted_map ρ hβ g hq (lam + 1 / 2) (by linarith)]

variable (hfin : (Set.range q).Finite)
include hfin

theorem compactAvg_map_eq (f : C(K, ℝ)) :
    compactAvg β lam (ρ.map q) g f =
      postAvg β lam (atomWt ρ hfin) (fun i => f (atomPt ρ hfin i))
        (fun i => g (atomPt ρ hfin i)) := by
  rw [compactAvg_map ρ hβ hlam g hq, integral_comp_finiteRange_atoms ρ hq hfin
    (fun x => f x * fluctuation β lam (g x)), compactD_map_eq ρ hβ hlam g hq hfin]
  unfold postAvg postWt
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem compactHalfAvg_map_eq (φ : C(K, ℝ)) :
    compactHalfAvg β lam (ρ.map q) g φ =
      ∑ i, φ (atomPt ρ hfin i) *
        quartetW β lam (atomWt ρ hfin) i (fun i => g (atomPt ρ hfin i)) := by
  rw [compactHalfAvg_map ρ hβ hlam g hq, integral_comp_finiteRange_atoms ρ hq hfin
    (fun x => φ x * fluctuation β (lam + 1 / 2) (g x)), compactD_map_eq ρ hβ hlam g hq hfin]
  unfold quartetW quartetN
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ### Convergence along a quantisation sequence -/

omit hq hfin in
theorem tendsto_compactAvg_map (hρ : ρ ≠ 0) (f : C(K, ℝ)) {q : ℕ → K → K}
    (hq : ∀ n, Measurable (q n)) {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hqε : ∀ n x, dist x (q n x) < ε n) :
    Tendsto (fun n => compactAvg β lam (ρ.map (q n)) g f) atTop (𝓝 (compactAvg β lam ρ g f)) := by
  simp_rw [compactAvg_map ρ hβ hlam g (hq _)]
  exact (tendsto_integral_comp_quantise ρ (weightedFluctC hβ lam hlam f g) hq hε hqε).div
    (tendsto_compactD_map ρ hβ hlam g hq hε hqε) (compactD_pos ρ hβ hlam hρ g).ne'

omit hq hfin in
theorem tendsto_compactHalfAvg_map (hρ : ρ ≠ 0) (φ : C(K, ℝ)) {q : ℕ → K → K}
    (hq : ∀ n, Measurable (q n)) {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hqε : ∀ n x, dist x (q n x) < ε n) :
    Tendsto (fun n => compactHalfAvg β lam (ρ.map (q n)) g φ) atTop
      (𝓝 (compactHalfAvg β lam ρ g φ)) := by
  simp_rw [compactHalfAvg_map ρ hβ hlam g (hq _)]
  exact (tendsto_integral_comp_quantise ρ (weightedFluctC hβ (lam + 1 / 2) (by linarith) φ g)
    hq hε hqε).div (tendsto_compactD_map ρ hβ hlam g hq hε hqε) (compactD_pos ρ hβ hlam hρ g).ne'

end Bounds

section Aux

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

theorem norm_le_one_add_sq_norm (g : C(K, ℝ)) : ‖g‖ ≤ 1 + ‖g‖ ^ 2 := by
  nlinarith [norm_nonneg g, sq_nonneg (‖g‖ - 1)]

end Aux

namespace GaussianField

variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {𝒞 : PSDKernel K} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (Γ : GaussianField 𝒞 P)
  {β lam : ℝ} (ρ : Measure K) [IsFiniteMeasure ρ] (hβ : 0 < β) (hlam : 0 < lam) (hρ : ρ ≠ 0)
include hβ hlam hρ

omit [MeasurableSpace K] [BorelSpace K] hβ hlam hρ in
/-- The kernel section `x ↦ 𝒞(x₀, x)` as a continuous map. -/
noncomputable def kernelSection (𝒞 : PSDKernel K) (x₀ : K) : C(K, ℝ) :=
  ⟨fun x => 𝒞.C x₀ x, 𝒞.continuous.comp (Continuous.prodMk_right x₀)⟩

omit [CompactSpace K] [MeasurableSpace K] [BorelSpace K] hβ hlam hρ in
theorem kernelSection_apply (x₀ x : K) : kernelSection 𝒞 x₀ x = 𝒞.C x₀ x := rfl

section Quantised

variable {q : K → K} (hq : Measurable q) (hfin : (Set.range q).Finite)
include hq hfin

/-- The joint points `(x₀, atoms)`. -/
noncomputable def steinPts (x₀ : K) : Fin ((posAtoms ρ hfin).card + 1) → K :=
  Fin.cases x₀ (atomPt ρ hfin)

omit [MetricSpace K] [CompactSpace K] [BorelSpace K] [IsFiniteMeasure ρ] hβ hlam hρ hq in
theorem steinPts_zero (x₀ : K) : steinPts ρ hfin x₀ 0 = x₀ := rfl

omit [MetricSpace K] [CompactSpace K] [BorelSpace K] [IsFiniteMeasure ρ] hβ hlam hρ hq in
theorem steinPts_succ (x₀ : K) (i : Fin (posAtoms ρ hfin).card) :
    steinPts ρ hfin x₀ i.succ = atomPt ρ hfin i := by
  simp [steinPts]

omit [BorelSpace K] [IsFiniteMeasure ρ] hβ hlam hρ hq in
theorem tailCLM_steinPts (x₀ : K) (ω : Ω) :
    tailCLM _ (fun i => Γ.G ω (steinPts ρ hfin x₀ i)) = fun i => Γ.G ω (atomPt ρ hfin i) := by
  funext i
  simp [tailCLM_apply, steinPts]

/-- **Stein's identity on a quantised base**:
`E[G(x₀) ⟨f⟩_{G}] = β E[⟨f 𝒞(x₀,·)⟩^{½} − ⟨f⟩ ⟨𝒞(x₀,·)⟩^{½}]` for `ρ ∘ q⁻¹`. -/
theorem integral_eval_mul_compactAvg_map (f : C(K, ℝ)) (x₀ : K) :
    ∫ ω, Γ.G ω x₀ * compactAvg β lam (ρ.map q) (Γ.G ω) f ∂P =
      β * ∫ ω, (compactHalfAvg β lam (ρ.map q) (Γ.G ω) (f * kernelSection 𝒞 x₀ : C(K, ℝ)) -
        compactAvg β lam (ρ.map q) (Γ.G ω) f *
          compactHalfAvg β lam (ρ.map q) (Γ.G ω) (kernelSection 𝒞 x₀)) ∂P := by
  have := nonempty_atoms ρ hq hfin hρ
  have hw := atomWt_pos ρ hfin
  set m := (posAtoms ρ hfin).card
  obtain ⟨n, A, hAB, hA⟩ := Γ.law _ (steinPts ρ hfin x₀)
  -- the finite-atom form of both sides
  have hL : ∀ ω, Γ.G ω x₀ * compactAvg β lam (ρ.map q) (Γ.G ω) f =
      (fun i => Γ.G ω (steinPts ρ hfin x₀ i)) 0 *
        postAvg β lam (atomWt ρ hfin) (fun i => f (atomPt ρ hfin i))
          (tailCLM m fun i => Γ.G ω (steinPts ρ hfin x₀ i)) := by
    intro ω
    rw [compactAvg_map_eq ρ hβ hlam (Γ.G ω) hq hfin f, Γ.tailCLM_steinPts ρ hfin x₀ ω]
    rfl
  have hR : ∀ ω, compactHalfAvg β lam (ρ.map q) (Γ.G ω) (f * kernelSection 𝒞 x₀ : C(K, ℝ)) -
      compactAvg β lam (ρ.map q) (Γ.G ω) f *
        compactHalfAvg β lam (ρ.map q) (Γ.G ω) (kernelSection 𝒞 x₀) =
      ∑ i, 𝒞.C x₀ (atomPt ρ hfin i) *
        (quartetW β lam (atomWt ρ hfin) i (tailCLM m fun i => Γ.G ω (steinPts ρ hfin x₀ i)) *
          (f (atomPt ρ hfin i) - postAvg β lam (atomWt ρ hfin) (fun i => f (atomPt ρ hfin i))
            (tailCLM m fun i => Γ.G ω (steinPts ρ hfin x₀ i)))) := by
    intro ω
    rw [compactHalfAvg_map_eq ρ hβ hlam (Γ.G ω) hq hfin (f * kernelSection 𝒞 x₀),
      compactHalfAvg_map_eq ρ hβ hlam (Γ.G ω) hq hfin (kernelSection 𝒞 x₀),
      compactAvg_map_eq ρ hβ hlam (Γ.G ω) hq hfin, Γ.tailCLM_steinPts ρ hfin x₀ ω,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ContinuousMap.mul_apply, kernelSection_apply]
    ring
  simp_rw [hL, hR]
  -- transfer to the Gaussian vector
  set w := atomWt ρ hfin with hwdef
  set fv : Fin m → ℝ := fun i => f (atomPt ρ hfin i) with hfvdef
  have hFm : Measurable fun v : Fin (m + 1) → ℝ => v 0 * postAvg β lam w fv (tailCLM m v) :=
    (measurable_pi_apply 0).mul
      ((continuous_postAvg hβ hlam hw fv).comp (tailCLM m).continuous).measurable
  have hGm : ∀ i, Measurable fun v : Fin (m + 1) → ℝ =>
      quartetW β lam w i (tailCLM m v) * (fv i - postAvg β lam w fv (tailCLM m v)) := fun i =>
    (((continuous_quartetW hβ hlam hw i).comp (tailCLM m).continuous).mul
      (continuous_const.sub ((continuous_postAvg hβ hlam hw fv).comp
        (tailCLM m).continuous))).measurable
  have hGb : ∀ i, PolyBoundedPi fun v : Fin (m + 1) → ℝ =>
      quartetW β lam w i (tailCLM m v) * (fv i - postAvg β lam w fv (tailCLM m v)) := fun i =>
    (polyBoundedPi_quartetW hβ hlam hw i).comp_tail.mul
      ((PolyBoundedPi.const (fv i)).sub (polyBoundedPi_postAvg hβ hlam hw fv).comp_tail)
  rw [Γ.integral_eval _ A hA hFm, integral_coord_mul_postAvg_tail hβ hlam hw A fv]
  congr 1
  rw [integral_finsetSum _ fun i _ => (Γ.integrable_eval _ A hA (hGm i)
    (integrable_gaussianVector_of_polyBoundedPi A (hGm i) (hGb i))).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, Γ.integral_eval _ A hA (hGm i), hAB]
  congr 1

end Quantised

section Limit

variable [Nonempty K]

/-! ### Measurability and dominated convergence along a quantisation sequence -/

omit hρ [Nonempty K] in
theorem measurable_compactAvg_comp (f : C(K, ℝ)) :
    Measurable fun ω => compactAvg β lam ρ (Γ.G ω) f :=
  (measurable_compactWeighted_comp ρ hβ hlam Γ.G Γ.measurable_uncurry_G
    f.continuous.measurable).div (measurable_compactD_comp ρ hβ hlam Γ.G Γ.measurable_uncurry_G)

omit hρ [Nonempty K] in
theorem measurable_compactHalfAvg_comp (φ : C(K, ℝ)) :
    Measurable fun ω => compactHalfAvg β lam ρ (Γ.G ω) φ :=
  (measurable_compactWeighted_comp ρ hβ (by linarith : (0 : ℝ) < lam + 1 / 2) Γ.G
    Γ.measurable_uncurry_G φ.continuous.measurable).div
    (measurable_compactD_comp ρ hβ hlam Γ.G Γ.measurable_uncurry_G)

omit [Nonempty K] in
theorem measurable_compactAvg_map_comp {q : K → K} (hq : Measurable q)
    (hfin : (Set.range q).Finite) (f : C(K, ℝ)) :
    Measurable fun ω => compactAvg β lam (ρ.map q) (Γ.G ω) f := by
  have := nonempty_atoms ρ hq hfin hρ
  have : (fun ω => compactAvg β lam (ρ.map q) (Γ.G ω) f) = fun ω =>
      postAvg β lam (atomWt ρ hfin) (fun i => f (atomPt ρ hfin i))
        (fun i => Γ.G ω (atomPt ρ hfin i)) :=
    funext fun ω => compactAvg_map_eq ρ hβ hlam (Γ.G ω) hq hfin f
  rw [this]
  exact (continuous_postAvg hβ hlam (atomWt_pos ρ hfin) _).measurable.comp
    (measurable_pi_lambda _ fun i => Γ.measurable_eval _)

omit [Nonempty K] in
theorem measurable_compactHalfAvg_map_comp {q : K → K} (hq : Measurable q)
    (hfin : (Set.range q).Finite) (φ : C(K, ℝ)) :
    Measurable fun ω => compactHalfAvg β lam (ρ.map q) (Γ.G ω) φ := by
  have := nonempty_atoms ρ hq hfin hρ
  have : (fun ω => compactHalfAvg β lam (ρ.map q) (Γ.G ω) φ) = fun ω =>
      ∑ i, φ (atomPt ρ hfin i) *
        quartetW β lam (atomWt ρ hfin) i (fun i => Γ.G ω (atomPt ρ hfin i)) :=
    funext fun ω => compactHalfAvg_map_eq ρ hβ hlam (Γ.G ω) hq hfin φ
  rw [this]
  exact (continuous_finsetSum _ fun i _ => continuous_const.mul
    (continuous_quartetW hβ hlam (atomWt_pos ρ hfin) i)).measurable.comp
    (measurable_pi_lambda _ fun i => Γ.measurable_eval _)

omit [IsFiniteMeasure ρ] hρ [Nonempty K] in
/-- The Stein right-hand side is dominated by `C (1 + ‖g‖²)`. -/
theorem abs_stein_rhs_le (ρ' : Measure K) [IsFiniteMeasure ρ'] (hρ' : ρ' ≠ 0) (g : C(K, ℝ))
    (f φ : C(K, ℝ)) :
    |compactHalfAvg β lam ρ' g (f * φ : C(K, ℝ)) -
        compactAvg β lam ρ' g f * compactHalfAvg β lam ρ' g φ| ≤
      (‖(f * φ : C(K, ℝ))‖ + ‖f‖ * ‖φ‖) * (Real.sqrt (2 * lam / β) + 1 / 2) *
        (1 + ‖g‖ ^ 2) := by
  have hB : 0 ≤ Real.sqrt (2 * lam / β) := Real.sqrt_nonneg _
  have h1 := abs_compactHalfAvg_le ρ' hβ hlam hρ' g (f * φ)
  have h2 := abs_compactAvg_le ρ' hβ hlam hρ' g f
  have h3 := abs_compactHalfAvg_le ρ' hβ hlam hρ' g φ
  have h4 : Real.sqrt (2 * lam / β) + ‖g‖ / 2 ≤
      (Real.sqrt (2 * lam / β) + 1 / 2) * (1 + ‖g‖ ^ 2) := by
    nlinarith [norm_nonneg g, sq_nonneg (‖g‖ - 1), mul_nonneg hB (sq_nonneg ‖g‖)]
  have h5 : 0 ≤ Real.sqrt (2 * lam / β) + ‖g‖ / 2 := by positivity
  calc |compactHalfAvg β lam ρ' g (f * φ : C(K, ℝ)) -
        compactAvg β lam ρ' g f * compactHalfAvg β lam ρ' g φ| ≤
        |compactHalfAvg β lam ρ' g (f * φ : C(K, ℝ))| +
          |compactAvg β lam ρ' g f| * |compactHalfAvg β lam ρ' g φ| := by
        rw [← abs_mul]; exact abs_sub _ _
    _ ≤ ‖(f * φ : C(K, ℝ))‖ * (Real.sqrt (2 * lam / β) + ‖g‖ / 2) +
          ‖f‖ * (‖φ‖ * (Real.sqrt (2 * lam / β) + ‖g‖ / 2)) :=
        add_le_add h1 (mul_le_mul h2 h3 (abs_nonneg _) (norm_nonneg _))
    _ = (‖(f * φ : C(K, ℝ))‖ + ‖f‖ * ‖φ‖) * (Real.sqrt (2 * lam / β) + ‖g‖ / 2) := by ring
    _ ≤ (‖(f * φ : C(K, ℝ))‖ + ‖f‖ * ‖φ‖) * ((Real.sqrt (2 * lam / β) + 1 / 2) * (1 + ‖g‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = (‖(f * φ : C(K, ℝ))‖ + ‖f‖ * ‖φ‖) * (Real.sqrt (2 * lam / β) + 1 / 2) *
          (1 + ‖g‖ ^ 2) := by ring

variable [IsProbabilityMeasure P] {q : ℕ → K → K} (hq : ∀ n, Measurable (q n))
  (hfin : ∀ n, (Set.range (q n)).Finite) {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
  (hqε : ∀ n x, dist x (q n x) < ε n)
include hq hfin hε hqε

omit [Nonempty K] in
/-- `E[G(x₀)⟨f⟩_{ρₙ}] → E[G(x₀)⟨f⟩_ρ]`. -/
theorem tendsto_integral_eval_mul_compactAvg_map (f : C(K, ℝ)) (x₀ : K) :
    Tendsto (fun n => ∫ ω, Γ.G ω x₀ * compactAvg β lam (ρ.map (q n)) (Γ.G ω) f ∂P) atTop
      (𝓝 (∫ ω, Γ.G ω x₀ * compactAvg β lam ρ (Γ.G ω) f ∂P)) := by
  refine tendsto_integral_of_dominated_convergence (fun ω => ‖f‖ * (1 + ‖Γ.G ω‖ ^ 2))
    (fun n => ((Γ.measurable_eval x₀).mul
      (Γ.measurable_compactAvg_map_comp ρ hβ hlam hρ (hq n) (hfin n) f)).aestronglyMeasurable)
    (integrable_const_mul_one_add_sq P Γ.G Γ.integrable_sq_norm _)
    (fun n => Eventually.of_forall fun ω => ?_)
    (Eventually.of_forall fun ω => tendsto_const_nhds.mul
      (tendsto_compactAvg_map ρ hβ hlam (Γ.G ω) hρ f hq hε hqε))
  rw [Real.norm_eq_abs, abs_mul]
  have h1 : |Γ.G ω x₀| ≤ ‖Γ.G ω‖ := by
    have := (Γ.G ω).norm_coe_le_norm x₀
    rwa [Real.norm_eq_abs] at this
  have h2 := abs_compactAvg_le (ρ.map (q n)) hβ hlam (map_quantise_ne_zero ρ (hq n) hρ) (Γ.G ω) f
  calc |Γ.G ω x₀| * |compactAvg β lam (ρ.map (q n)) (Γ.G ω) f| ≤ ‖Γ.G ω‖ * ‖f‖ :=
        mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
    _ ≤ ‖f‖ * (1 + ‖Γ.G ω‖ ^ 2) := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left (norm_le_one_add_sq_norm _) (norm_nonneg _)

omit [Nonempty K] in
/-- The Stein right-hand sides converge along the quantisation sequence. -/
theorem tendsto_integral_stein_rhs_map (f : C(K, ℝ)) (x₀ : K) :
    Tendsto (fun n => ∫ ω, (compactHalfAvg β lam (ρ.map (q n)) (Γ.G ω)
        (f * kernelSection 𝒞 x₀ : C(K, ℝ)) - compactAvg β lam (ρ.map (q n)) (Γ.G ω) f *
          compactHalfAvg β lam (ρ.map (q n)) (Γ.G ω) (kernelSection 𝒞 x₀)) ∂P) atTop
      (𝓝 (∫ ω, (compactHalfAvg β lam ρ (Γ.G ω) (f * kernelSection 𝒞 x₀ : C(K, ℝ)) -
        compactAvg β lam ρ (Γ.G ω) f *
          compactHalfAvg β lam ρ (Γ.G ω) (kernelSection 𝒞 x₀)) ∂P)) := by
  refine tendsto_integral_of_dominated_convergence
    (fun ω => (‖(f * kernelSection 𝒞 x₀ : C(K, ℝ))‖ + ‖f‖ * ‖kernelSection 𝒞 x₀‖) *
      (Real.sqrt (2 * lam / β) + 1 / 2) * (1 + ‖Γ.G ω‖ ^ 2))
    (fun n => ((Γ.measurable_compactHalfAvg_map_comp ρ hβ hlam hρ (hq n) (hfin n) _).sub
      ((Γ.measurable_compactAvg_map_comp ρ hβ hlam hρ (hq n) (hfin n) f).mul
        (Γ.measurable_compactHalfAvg_map_comp ρ hβ hlam hρ (hq n) (hfin n) _)))
      |>.aestronglyMeasurable)
    (integrable_const_mul_one_add_sq P Γ.G Γ.integrable_sq_norm _)
    (fun n => Eventually.of_forall fun ω => ?_)
    (Eventually.of_forall fun ω =>
      (tendsto_compactHalfAvg_map ρ hβ hlam (Γ.G ω) hρ _ hq hε hqε).sub
        ((tendsto_compactAvg_map ρ hβ hlam (Γ.G ω) hρ f hq hε hqε).mul
          (tendsto_compactHalfAvg_map ρ hβ hlam (Γ.G ω) hρ _ hq hε hqε)))
  rw [Real.norm_eq_abs]
  exact abs_stein_rhs_le hβ hlam (ρ.map (q n)) (map_quantise_ne_zero ρ (hq n) hρ) (Γ.G ω) f _

omit hq hfin hε hqε in
/-- ★★★ **Stein's identity for posterior averages on the compact base**:
`E[G(x₀) ⟨f⟩_G] = β E[⟨f 𝒞(x₀,·)⟩^{½}_G − ⟨f⟩_G ⟨𝒞(x₀,·)⟩^{½}_G]`, i.e.
`E[G(x₀) F_f(G)] = E[DF_f(G)[𝒞(x₀,·)]]` with `DF_f(g)[h] = β(⟨f√t h⟩_g − ⟨f⟩_g⟨√t h⟩_g)`. -/
theorem integral_eval_mul_compactAvg (f : C(K, ℝ)) (x₀ : K) :
    ∫ ω, Γ.G ω x₀ * compactAvg β lam ρ (Γ.G ω) f ∂P =
      β * ∫ ω, (compactHalfAvg β lam ρ (Γ.G ω) (f * kernelSection 𝒞 x₀ : C(K, ℝ)) -
        compactAvg β lam ρ (Γ.G ω) f * compactHalfAvg β lam ρ (Γ.G ω) (kernelSection 𝒞 x₀)) ∂P := by
  obtain ⟨q, hq, hfin, hqε⟩ := exists_quantisation_seq (K := K)
  have h1 := Γ.tendsto_integral_eval_mul_compactAvg_map ρ hβ hlam hρ hq hfin
    tendsto_one_div_add_atTop_nhds_zero_nat hqε f x₀
  have h2 := (Γ.tendsto_integral_stein_rhs_map ρ hβ hlam hρ hq hfin
    tendsto_one_div_add_atTop_nhds_zero_nat hqε f x₀).const_mul β
  refine tendsto_nhds_unique h1 (h2.congr fun n => ?_)
  exact (Γ.integral_eval_mul_compactAvg_map ρ hβ hlam hρ (hq n) (hfin n) f x₀).symm

end Limit

end GaussianField

end Grammar
