/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.ZeroFluctSpectralKernel
import Grammar.SymmetricWeights
import Grammar.ResolvedNormalData

/-!
# Chart coefficient tensors and the termwise identity (CCCII)

Unit 6 of the coordinate-free programme (`tide-log/plan_coordinate_free_expansion.md`). For a
chart with normal exponents `h, k`, box side `b` and a density factor with `b`-weighted ℓ¹ Taylor
family `cc`, the **shifted kernel** `K^{cc}_{μ,j}(δ) = ∑'_γ cc_γ K^b_{μ,j}(γ+δ)` is the `(μ,j)`
canonical coefficient of the dressed monomial moment `∫ u^δ c(u) u^h e^{−βN u^{2k}} du`
(`shiftedKernel`), and the **chart coefficient tensor**
`B_{r,μ,j} = ∑_{|b|=r} (r!/b!) K^{cc}_{μ,j}(b) ∂^b : Sym^r(ℝ^{n+1})^* → ℝ`
(`chartMomentCoeff`) is the `(μ,j)` coefficient of the exact fibre moment tensor
`M̂_r(N) : T ↦ ∫ T(u,…,u) c u^h e^{−βN u^{2k}} du` (its value on `D^rF(0)` is
`r! ∑_{|b|=r} (∂^bF(0)/b!) K^{cc}(b)`, `inv_factorial_mul_chartMomentCoeff_apply`).

★★ **The termwise identity** (`boxCoeff_conv_jetFamily_eq_tsum`): for an observable `F` whose
Taylor family `jetFamily F = (∂^bF(0)/b!)_b` is `b`-weighted ℓ¹,
`boxCoeff 0 (cc ⋆ jetFamily F) μ j = ∑'_r (1/r!) ⟨D^rF(0), B_{r,μ,j}⟩` —
the paper's canonical coefficient of the chart integral `∫ F c u^h e^{−βN u^{2k}} du` (whose
amplitude family is the Cauchy product `cc ⋆ jetFamily F`) is the absolutely convergent sum over
the normal degree of the pairings of the normal jets with the coefficient tensors. The proof is
a pure rearrangement: `boxCoeff_zero_eq_tsum` (CCCI), regrouping of the double series along
`γ = α + δ` (`pairEquiv`), Fubini for absolutely summable double families, and the degree
fibration (`degreeEquiv`) with the multinomial bridge `multinomial_div_factorial`.

Also: `MomentTensor.pushFrame`, the transport of a moment tensor along a linear frame
`e : V →L N` (pairing `⟨T, e_*M⟩ = ⟨T ∘ e, M⟩`), used to place the chart tensors on the strata.

Non-claims: no asymptotics are proved here; the identification of the coefficient tensors with
the paper's `B_{I,r,α,j}` on the strata and the final expansion theorem are the next units.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

open CoeffFamily MonoRep

/-! ### Frame transport of moment tensors -/

/-- The transport of a moment tensor along a linear frame `e : V →L N`:
`⟨T, e_*M⟩ = ⟨T ∘ (e,…,e), M⟩`. -/
noncomputable def MomentTensor.pushFrame {V N : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup N] [NormedSpace ℝ N] {r : ℕ} (M : MomentTensor V r) (e : V →L[ℝ] N) :
    MomentTensor N r :=
  M.comp (ContinuousMultilinearMap.compContinuousLinearMapL fun _ : Fin r => e)

theorem MomentTensor.pushFrame_pair {V N : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup N] [NormedSpace ℝ N] {r : ℕ} (M : MomentTensor V r) (e : V →L[ℝ] N)
    (T : JetForm N r) :
    (M.pushFrame e).pair T = M.pair (T.compContinuousLinearMap fun _ => e) := rfl

/-! ### The shifted kernel and the chart coefficient tensors -/

variable (n : ℕ) (h k : Fin (n + 1) → ℕ) (β b μ : ℝ) (j : ℕ)

/-- The shifted kernel `K^{cc}_{μ,j}(δ) = ∑'_γ cc_γ K^b_{μ,j}(γ + δ)`: the `(μ,j)` canonical
coefficient of the dressed monomial moment `∫ u^δ c(u) u^h e^{−βN u^{2k}} du` for a density with
Taylor family `cc`. -/
noncomputable def shiftedKernel (cc : CoeffFamily (n + 1)) (δ : Fin (n + 1) → ℕ) : ℝ :=
  ∑' γ, cc γ * boxSpectralKernel n h k β b μ j (γ + δ)

omit n in
theorem sum_add_apply {d : ℕ} (γ δ : Fin d → ℕ) : ∑ i, (γ + δ) i = ∑ i, γ i + ∑ i, δ i := by
  simp only [Pi.add_apply, Finset.sum_add_distrib]

theorem summable_shiftedKernel_term (hk : ∀ i, 0 < k i) (hβ : 0 < β) (hb : 0 < b)
    {cc : CoeffFamily (n + 1)} (hcc : AbsSummableAt cc b) (δ : Fin (n + 1) → ℕ) :
    Summable fun γ => cc γ * boxSpectralKernel n h k β b μ j (γ + δ) := by
  refine Summable.of_norm_bounded
    (hcc.mul_right (boxSpectralKernelBound n h k β b μ j * b ^ (∑ i, δ i))) fun γ => ?_
  rw [Real.norm_eq_abs, abs_mul]
  have hK := abs_boxSpectralKernel_le n h k β μ j hk hβ hb.le (γ + δ)
  rw [sum_add_apply, pow_add] at hK
  calc |cc γ| * |boxSpectralKernel n h k β b μ j (γ + δ)|
      ≤ |cc γ| * (boxSpectralKernelBound n h k β b μ j * (b ^ (∑ i, γ i) * b ^ (∑ i, δ i))) :=
        mul_le_mul_of_nonneg_left hK (abs_nonneg _)
    _ = _ := by ring

/-- **The chart coefficient tensor** `B_{r,μ,j} = ∑_{|b|=r} (r!/b!) K^{cc}_{μ,j}(b) ∂^b`, the
`(μ,j)` coefficient of the exact fibre moment tensor `T ↦ ∫ T(u,…,u) c u^h e^{−βN u^{2k}} du`. -/
noncomputable def chartMomentCoeff (cc : CoeffFamily (n + 1)) (r : ℕ) :
    MomentTensor (Fin (n + 1) → ℝ) r :=
  ∑ bb ∈ Finset.Nat.antidiagonalTuple (n + 1) r,
    ((Nat.multinomial Finset.univ bb : ℝ) * shiftedKernel n h k β b μ j cc bb) •
      weightComponentL bb

theorem chartMomentCoeff_apply (cc : CoeffFamily (n + 1)) (r : ℕ)
    (T : JetForm (Fin (n + 1) → ℝ) r) :
    chartMomentCoeff n h k β b μ j cc r T = ∑ bb ∈ Finset.Nat.antidiagonalTuple (n + 1) r,
      (Nat.multinomial Finset.univ bb : ℝ) * shiftedKernel n h k β b μ j cc bb *
        weightComponent T bb := by
  unfold chartMomentCoeff
  rw [sum_apply]
  refine Finset.sum_congr rfl fun bb _ => ?_
  rw [smul_apply, smul_eq_mul]
  rfl

/-! ### The Taylor family of an observable -/

/-- The Taylor family `(∂^bF(0)/b!)_b` of an observable on the box. -/
noncomputable def jetFamily (F : (Fin (n + 1) → ℝ) → ℝ) : CoeffFamily (n + 1) :=
  fun bb => (∏ i, ((bb i).factorial : ℝ))⁻¹ * weightComponent (normalJet F (∑ i, bb i)) bb

theorem jetFamily_eq (F : (Fin (n + 1) → ℝ) → ℝ) {bb : Fin (n + 1) → ℕ} {r : ℕ}
    (hb : ∑ i, bb i = r) :
    jetFamily n F bb = (∏ i, ((bb i).factorial : ℝ))⁻¹ * weightComponent (normalJet F r) bb := by
  subst hb
  rfl

/-- `(1/r!) ⟨D^rF(0), B_{r,μ,j}⟩ = ∑_{|b|=r} (∂^bF(0)/b!) K^{cc}_{μ,j}(b)`. -/
theorem inv_factorial_mul_chartMomentCoeff_apply (cc : CoeffFamily (n + 1))
    (F : (Fin (n + 1) → ℝ) → ℝ) (r : ℕ) :
    (r.factorial : ℝ)⁻¹ * chartMomentCoeff n h k β b μ j cc r (normalJet F r) =
      ∑ bb ∈ Finset.Nat.antidiagonalTuple (n + 1) r,
        jetFamily n F bb * shiftedKernel n h k β b μ j cc bb := by
  rw [chartMomentCoeff_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun bb hb => ?_
  have hb' := Finset.Nat.mem_antidiagonalTuple.1 hb
  rw [jetFamily_eq n F hb', ← multinomial_div_factorial bb hb']
  ring

/-! ### The termwise identity -/

/-- ★★ **The termwise identity**: the canonical `(μ,j)` coefficient of the chart integral with
amplitude family `cc ⋆ jetFamily F` is the absolutely convergent sum over the normal degree of the
pairings of the normal jets with the chart coefficient tensors,
`boxCoeff 0 (cc ⋆ jetFamily F) μ j = ∑'_r (1/r!) ⟨D^rF(0), B_{r,μ,j}⟩`. -/
theorem boxCoeff_conv_jetFamily_eq_tsum (hk : ∀ i, 0 < k i) (hβ : 0 < β) (hb : 0 < b)
    {cc : CoeffFamily (n + 1)} (hcc : AbsSummableAt cc b) {F : (Fin (n + 1) → ℝ) → ℝ}
    (hF : AbsSummableAt (jetFamily n F) b) :
    boxCoeff n h k β b 0 (CoeffFamily.conv cc (jetFamily n F)) μ j =
      ∑' r, (r.factorial : ℝ)⁻¹ * chartMomentCoeff n h k β b μ j cc r (normalJet F r) := by
  set K := boxSpectralKernel n h k β b μ j with hKdef
  set jf := jetFamily n F with hjf
  set S := shiftedKernel n h k β b μ j cc with hS
  have hK := abs_boxSpectralKernel_le n h k β μ j hk hβ hb.le
  -- the absolutely summable pair family `(δ, α) ↦ jf δ · cc α · K(α + δ)`
  have hpair : Summable fun p : (Fin (n + 1) → ℕ) × (Fin (n + 1) → ℕ) =>
      jf p.1 * cc p.2 * K (p.2 + p.1) := by
    have hs := summable_mul_of_summable_norm hF.norm hcc.norm
    refine Summable.of_norm_bounded (hs.mul_right (boxSpectralKernelBound n h k β b μ j))
      fun p => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have hKp := hK (p.2 + p.1)
    rw [sum_add_apply, pow_add] at hKp
    have h1 : 0 ≤ |jf p.1| := abs_nonneg _
    have h2 : 0 ≤ |cc p.2| := abs_nonneg _
    have hb1 : 0 ≤ b ^ (∑ i, p.1 i) := pow_nonneg hb.le _
    have hb2 : 0 ≤ b ^ (∑ i, p.2 i) := pow_nonneg hb.le _
    calc |jf p.1| * |cc p.2| * |K (p.2 + p.1)|
        ≤ |jf p.1| * |cc p.2| *
          (boxSpectralKernelBound n h k β b μ j * (b ^ (∑ i, p.2 i) * b ^ (∑ i, p.1 i))) :=
          mul_le_mul_of_nonneg_left hKp (mul_nonneg h1 h2)
      _ = |jf p.1| * b ^ (∑ i, p.1 i) * (|cc p.2| * b ^ (∑ i, p.2 i)) *
          boxSpectralKernelBound n h k β b μ j := by ring
  -- the fibres over `δ`
  have hinner : ∀ δ, Summable fun α => jf δ * cc α * K (α + δ) := fun δ => by
    have := (summable_shiftedKernel_term n h k β b μ j hk hβ hb hcc δ).mul_left (jf δ)
    refine this.congr fun α => ?_
    ring
  have hin : ∀ δ, ∑' α, jf δ * cc α * K (α + δ) = jf δ * S δ := fun δ => by
    rw [hS]
    unfold shiftedKernel
    rw [← tsum_mul_left]
    exact tsum_congr fun α => by ring
  -- Step 1: the box coefficient as the pair sum, regrouped along `γ = α + δ`
  have hconv : AbsSummableAt (CoeffFamily.conv cc jf) b := AbsSummableAt.conv hb.le hcc hF
  rw [boxCoeff_zero_eq_tsum n h k β μ j hk hβ hb hconv]
  have hp' : HasSum (fun q : (Fin (n + 1) → ℕ) × (Fin (n + 1) → ℕ) =>
      cc q.1 * jf q.2 * K (q.1 + q.2)) (∑' p : (Fin (n + 1) → ℕ) × (Fin (n + 1) → ℕ), jf p.1 *
        cc p.2 * K (p.2 + p.1)) := by
    have := (Equiv.prodComm (Fin (n + 1) → ℕ) (Fin (n + 1) → ℕ)).hasSum_iff.2 hpair.hasSum
    refine this.congr_fun fun q => ?_
    simp only [Function.comp, Equiv.prodComm_apply, Prod.swap]
    ring
  set G : (Σ γ : Fin (n + 1) → ℕ, ↥(Finset.Iic γ)) → ℝ :=
    fun s => cc s.2.1 * jf (s.1 - s.2.1) * K s.1 with hG
  have hGe : ∀ q, G (pairEquiv (n + 1) q) = cc q.1 * jf q.2 * K (q.1 + q.2) := by
    intro q
    simp only [hG, pairEquiv, Equiv.coe_fn_mk, add_tsub_cancel_left]
  have hGsum : HasSum G (∑' p : (Fin (n + 1) → ℕ) × (Fin (n + 1) → ℕ), jf p.1 * cc p.2 * K (p.2
    + p.1)) := by
    rw [← (pairEquiv (n + 1)).hasSum_iff]
    exact hp'.congr_fun fun q => (hGe q).symm ▸ rfl
  have hsig : HasSum (fun γ => CoeffFamily.conv cc jf γ * K γ)
      (∑' p : (Fin (n + 1) → ℕ) × (Fin (n + 1) → ℕ), jf p.1 * cc p.2 * K (p.2 + p.1)) := by
    refine hGsum.sigma fun γ => ?_
    have : ∑ α : ↥(Finset.Iic γ), G ⟨γ, α⟩ = CoeffFamily.conv cc jf γ * K γ := by
      unfold CoeffFamily.conv
      rw [Finset.sum_mul, ← Finset.sum_coe_sort (Finset.Iic γ) (fun α => cc α * jf (γ - α) * K γ)]
    rw [← this]
    exact hasSum_fintype _
  rw [hsig.tsum_eq]
  -- Step 2: Fubini over the pairs and the fibre sums
  rw [hpair.tsum_prod' hinner]
  simp_rw [hin]
  -- Step 3: the degree fibration
  have hδsum : Summable fun δ => jf δ * S δ :=
    (hpair.hasSum.prod_fiberwise fun δ => (hin δ) ▸ (hinner δ).hasSum).summable
  have hdeg : HasSum (fun x : Σ r : ℕ, {δ : Fin (n + 1) → ℕ // ∑ i, δ i = r} =>
      jf x.2.1 * S x.2.1) (∑' δ, jf δ * S δ) := by
    have := (degreeEquiv (Fin (n + 1))).hasSum_iff.2 hδsum.hasSum
    exact this.congr_fun fun x => rfl
  have hfib : ∀ r : ℕ, HasSum (fun δ : {δ : Fin (n + 1) → ℕ // ∑ i, δ i = r} =>
      jf δ.1 * S δ.1) ((r.factorial : ℝ)⁻¹ * chartMomentCoeff n h k β b μ j cc r (normalJet F
        r)) := by
    intro r
    rw [inv_factorial_mul_chartMomentCoeff_apply]
    have hs : HasSum (fun δ : {δ : Fin (n + 1) → ℕ // ∑ i, δ i = r} => jf δ.1 * S δ.1)
        (∑ δ ∈ (Finset.Nat.antidiagonalTuple (n + 1) r).subtype (fun δ => ∑ i, δ i = r),
          jf δ.1 * S δ.1) :=
      hasSum_sum_of_ne_finset_zero fun δ hδ =>
        absurd (Finset.mem_subtype.2 (Finset.Nat.mem_antidiagonalTuple.2 δ.2)) hδ
    convert hs using 1
    rw [Finset.sum_subtype_eq_sum_filter (f := fun δ => jf δ * S δ),
      Finset.filter_true_of_mem fun δ hδ => Finset.Nat.mem_antidiagonalTuple.1 hδ]
  exact (hdeg.sigma hfib).tsum_eq.symm

end Grammar
