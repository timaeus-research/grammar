/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.StochasticData

/-!
# The spectral coefficients at zero fluctuation are linear in the amplitude (CCCI)

Unit 5 of the coordinate-free programme (`tide-log/plan_coordinate_free_expansion.md`). In the
population (zero-fluctuation) case the paper's canonical box coefficients are **linear
functionals of the amplitude family**: with the monomial spectral kernel
`monoKernel_{μ,j}(γ) = (∏ 1/(2kᵢ)) ∑_{q=j}^{n} coeffAt(ρ_{h+γ,k}; μ, q) C(q,j) fluctMoment(μ, q−j)`
one has `spectralCoeff (0) η μ j = ∑_{(γ,c) ∈ η} c · monoKernel_{μ,j}(γ)`
(`spectralCoeff_truncList_zero`), hence for an ℓ¹ amplitude family
`familySpectralCoeff 0 cη μ j = ∑'_γ cη_γ monoKernel_{μ,j}(γ)`
(★ `familySpectralCoeff_zero_eq_tsum`) and, with the box kernel `boxSpectralKernel` absorbing the
box-side rescaling,
`boxCoeff 0 cη μ j = ∑'_γ cη_γ boxKernel_{μ,j}(γ)` (★ `boxCoeff_zero_eq_tsum`). The kernels are
bounded uniformly in the multi-index (`abs_monoKernel_le`, `abs_boxSpectralKernel_le`:
`|boxSpectralKernel(γ)| ≤ C b^{|γ|}`), which is exactly the continuity of the coefficients on the
`b`-weighted ℓ¹ space `AbsSummableAt · b` (closed under the Cauchy product,
`AbsSummableAt.conv`).

This is the algebraic input for the stratum coefficient tensors of the next unit: the
`(μ,j)`-coefficient of the fibre integral `∫ F(u) c(u) u^h e^{−βN u^{2k}} du` is the pairing of the
Taylor family of `F` with the kernel shifted by the density family.

Non-claims: nothing about the fluctuation (stochastic) case; no asymptotic statement is made
here — the identities are exact rearrangements of the paper's coefficient formulas.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

open CoeffFamily MonoRep

/-! ### The monomial spectral kernel -/

/-- The monomial spectral kernel at zero fluctuation: the `(μ, j)` canonical coefficient of the
unit-box monomial integral `∫ u^{γ+h} e^{−βN u^{2k}} du`. -/
noncomputable def monoKernel (n : ℕ) (h k : Fin (n + 1) → ℕ) (β μ : ℝ) (j : ℕ)
    (γ : Fin (n + 1) → ℕ) : ℝ :=
  (∏ i, 1 / (2 * (k i : ℝ))) * ∑ q ∈ Finset.Ico j (n + 1),
    PowLogRep.coeffAt (stateDensityRep n (monoWeights (h + γ) k)) μ q * (q.choose j : ℝ) *
      fluctMoment β 0 0 μ (q - j)

variable (n : ℕ) (h k : Fin (n + 1) → ℕ) (β μ : ℝ) (j : ℕ)

theorem coeffTerm_zero_zero (P : MonoRep (n + 1)) :
    coeffTerm n h k β 0 0 μ j P = (P.map fun s => s.2 * monoKernel n h k β μ j s.1).sum := by
  unfold coeffTerm monoKernel
  rw [← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun s _ => ?_
  ring

theorem coeffTerm_eq_zero_of_forall_snd (a : ℝ) (p : ℕ) (P : MonoRep (n + 1))
    (hP : ∀ s ∈ P, s.2 = 0) : coeffTerm n h k β a p μ j P = 0 := by
  unfold coeffTerm
  rw [mul_eq_zero]
  right
  refine List.sum_eq_zero fun x hx => ?_
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
  rw [hP s hs, zero_mul]

omit n h k β μ j in
theorem mul_snd_eq_zero_left {d : ℕ} {P Q : MonoRep d} (hP : ∀ s ∈ P, s.2 = 0) :
    ∀ s ∈ mul P Q, s.2 = 0 := by
  intro s hs
  obtain ⟨a, ha, hs'⟩ := List.mem_flatMap.1 hs
  obtain ⟨t, -, rfl⟩ := List.mem_map.1 hs'
  change a.2 * t.2 = 0
  rw [hP a ha, zero_mul]

omit n h k β μ j in
theorem mul_snd_eq_zero_right {d : ℕ} {P Q : MonoRep d} (hQ : ∀ t ∈ Q, t.2 = 0) :
    ∀ s ∈ mul P Q, s.2 = 0 := by
  intro s hs
  obtain ⟨a, -, hs'⟩ := List.mem_flatMap.1 hs
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hs'
  change a.2 * t.2 = 0
  rw [hQ t ht, mul_zero]

omit n h k β μ j in
theorem pow_succ_snd_eq_zero {d : ℕ} {P : MonoRep d} (hP : ∀ s ∈ P, s.2 = 0) (p : ℕ) :
    ∀ s ∈ pow P (p + 1), s.2 = 0 :=
  mul_snd_eq_zero_left hP

omit n h k β μ j in
theorem fluct_truncList_zero_snd {d : ℕ} (m : ℕ) :
    ∀ s ∈ fluct (truncList (0 : CoeffFamily d) m), s.2 = 0 := by
  intro s hs
  have hs' : s ∈ truncList (0 : CoeffFamily d) m := (List.mem_filter.1 hs).1
  obtain ⟨γ, -, rfl⟩ := List.mem_map.1 hs'
  rfl

omit n h k β μ j in
theorem mul_single_zero_one {d : ℕ} (P : MonoRep d) :
    mul P [((0 : Fin d → ℕ), (1 : ℝ))] = P.map fun s => (s.1 + 0, s.2 * 1) := by
  unfold mul
  induction P with
  | nil => rfl
  | cons s P ih => rw [List.flatMap_cons, List.map_cons, ih]; rfl

/-- **The zero-fluctuation spectral coefficient is the kernel pairing** with the amplitude. -/
theorem spectralCoeff_truncList_zero (m : ℕ) (η : MonoRep (n + 1)) :
    spectralCoeff n h k β (truncList 0 m) η μ j =
      (η.map fun s => s.2 * monoKernel n h k β μ j s.1).sum := by
  unfold spectralCoeff
  rw [eval_truncList_zero, Pi.zero_apply, tsum_eq_single 0]
  · rw [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul, coeffTerm_zero_zero]
    rw [show pow (fluct (truncList (0 : CoeffFamily (n + 1)) m)) 0 =
      [((0 : Fin (n + 1) → ℕ), (1 : ℝ))] from rfl, mul_single_zero_one, List.map_map]
    congr 1
    refine List.map_congr_left fun s _ => ?_
    simp only [Function.comp, add_zero, mul_one]
  · intro p hp
    obtain ⟨p', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp
    rw [coeffTerm_eq_zero_of_forall_snd n h k β μ j _ _ _
      (mul_snd_eq_zero_right (pow_succ_snd_eq_zero (fluct_truncList_zero_snd m) p')), mul_zero]

/-- The truncation coefficients at zero fluctuation are the finite kernel sums. -/
theorem truncCoeff_zero_eq (cη : CoeffFamily (n + 1)) (m : ℕ) :
    truncCoeff n h k β 0 cη μ j m =
      ∑ γ ∈ boxSet (n + 1) m, cη γ * monoKernel n h k β μ j γ := by
  unfold truncCoeff
  rw [spectralCoeff_truncList_zero]
  unfold truncList
  rw [List.map_map, sum_map_toList]
  rfl

/-! ### Uniform bounds -/

/-- The kernel bound `(∏ 1/(2kᵢ)) (n+1) (n+1)! Q^n 2^n · phaseLogMoment β 0 μ n 0`. -/
noncomputable def kernelBound (n : ℕ) (k : Fin (n + 1) → ℕ) (β μ : ℝ) : ℝ :=
  (∏ i, 1 / (2 * (k i : ℝ))) *
    ((n + 1 : ℝ) * (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) * 2 ^ n) *
    phaseLogMoment β 0 μ n 0

omit h j in
theorem kernelBound_nonneg : 0 ≤ kernelBound n k β μ := by
  unfold kernelBound
  have := phaseLogMoment_nonneg β 0 μ n 0
  have hK : 0 ≤ ∏ i, 1 / (2 * (k i : ℝ)) := Finset.prod_nonneg fun i _ => by positivity
  positivity

theorem monoKernel_eq_zero_of_not_candidate (hμ : ¬ candidateExp h k μ) (γ : Fin (n + 1) → ℕ) :
    monoKernel n h k β μ j γ = 0 := by
  unfold monoKernel
  rw [Finset.sum_eq_zero fun q _ => by rw [coeffAt_monoWeights_eq_zero n h k γ hμ q]; ring,
    mul_zero]

/-- **The kernel is bounded uniformly in the multi-index.** -/
theorem abs_monoKernel_le (hk : ∀ i, 0 < k i) (hβ : 0 < β) (γ : Fin (n + 1) → ℕ) :
    |monoKernel n h k β μ j γ| ≤ kernelBound n k β μ := by
  by_cases hμ : 0 < μ
  · have hK : 0 ≤ ∏ i, 1 / (2 * (k i : ℝ)) := Finset.prod_nonneg fun i _ => by positivity
    set M := phaseLogMoment β 0 μ n 0 with hM
    have hM0 : 0 ≤ M := phaseLogMoment_nonneg β 0 μ n 0
    have hterm : ∀ q ∈ Finset.Ico j (n + 1),
        |PowLogRep.coeffAt (stateDensityRep n (monoWeights (h + γ) k)) μ q * (q.choose j : ℝ) *
          fluctMoment β 0 0 μ (q - j)| ≤
        (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) * 2 ^ n * M := by
      intro q hq
      have hqn : q ≤ n := Nat.lt_succ_iff.1 (Finset.mem_Ico.1 hq).2
      rw [abs_mul, abs_mul, Nat.abs_cast]
      refine mul_le_mul (mul_le_mul (abs_coeffAt_stateDensityRep_le n (h + γ) k hk μ q) ?_
        (by positivity) (by positivity)) (abs_fluctMoment_le β 0 hβ 0 hμ (by omega))
        (abs_nonneg _) (by positivity)
      calc (q.choose j : ℝ) ≤ (2 ^ q : ℕ) := by exact_mod_cast Nat.choose_le_two_pow q j
        _ ≤ 2 ^ n := by exact_mod_cast Nat.pow_le_pow_right two_pos hqn
    unfold monoKernel kernelBound
    rw [abs_mul, abs_of_nonneg hK, mul_assoc]
    refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans ?_) hK
    refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
    rw [nsmul_eq_mul, Nat.card_Ico]
    have hcard : ((n + 1 - j : ℕ) : ℝ) ≤ n + 1 := by exact_mod_cast Nat.sub_le (n + 1) j
    calc ((n + 1 - j : ℕ) : ℝ) * ((((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) * 2 ^ n * M)
        ≤ (n + 1 : ℝ) * ((((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) * 2 ^ n * M) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := by ring
  · rw [monoKernel_eq_zero_of_not_candidate n h k β μ j
      (fun hc => hμ (candidateExp_pos hk hc)) γ, abs_zero]
    exact kernelBound_nonneg n k β μ

/-! ### The ℓ¹ limit -/

omit n h k β μ j in
theorem tendsto_boxSet_atTop (d : ℕ) : Tendsto (boxSet d) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro S
  refine ⟨S.sup fun γ : Fin d → ℕ => Finset.univ.sup γ, fun m hm γ hγ => ?_⟩
  rw [mem_boxSet]
  intro i
  exact ((Finset.le_sup (f := fun γ : Fin d → ℕ => Finset.univ.sup γ) hγ).trans' 
    (Finset.le_sup (f := γ) (Finset.mem_univ i))).trans hm

omit n h k β μ j in
theorem tendsto_sum_boxSet {d : ℕ} {f : (Fin d → ℕ) → ℝ} (hf : Summable f) :
    Tendsto (fun m => ∑ γ ∈ boxSet d m, f γ) atTop (𝓝 (∑' γ, f γ)) :=
  hf.hasSum.comp (tendsto_boxSet_atTop d)

omit n h k β μ j in
theorem absSummable_zero (d : ℕ) : AbsSummable (0 : CoeffFamily d) := by
  unfold AbsSummable
  simp only [Pi.zero_apply, abs_zero]
  exact summable_zero

theorem summable_mul_monoKernel (hk : ∀ i, 0 < k i) (hβ : 0 < β) {cη : CoeffFamily (n + 1)}
    (hη : AbsSummable cη) : Summable fun γ => cη γ * monoKernel n h k β μ j γ := by
  refine Summable.of_norm_bounded (hη.mul_right (kernelBound n k β μ)) fun γ => ?_
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_monoKernel_le n h k β μ j hk hβ γ) (abs_nonneg _)

/-- ★ **The family spectral coefficient at zero fluctuation is the ℓ¹ kernel pairing**
`A_{μ,j}(0, cη) = ∑'_γ cη_γ monoKernel_{μ,j}(γ)`. -/
theorem familySpectralCoeff_zero_eq_tsum (hk : ∀ i, 0 < k i) (hβ : 0 < β)
    {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη) :
    familySpectralCoeff n h k β 0 cη μ j = ∑' γ, cη γ * monoKernel n h k β μ j γ := by
  refine tendsto_nhds_unique (tendsto_truncCoeff n h k hk β hβ (absSummable_zero (n + 1)) hη μ j)
    ?_
  have heq : truncCoeff n h k β 0 cη μ j =
      fun m => ∑ γ ∈ boxSet (n + 1) m, cη γ * monoKernel n h k β μ j γ :=
    funext (truncCoeff_zero_eq n h k β μ j cη)
  rw [heq]
  exact tendsto_sum_boxSet (summable_mul_monoKernel n h k β μ j hk hβ hη)

/-! ### The box kernel -/

/-- The box kernel `K^b_{μ,j}(γ) = b^{|h|+d} c^{−μ} ∑_{q ≥ j} b^{|γ|} monoKernel_{μ,q}(γ) C(q,j)
(log c)^{q−j}`, `c = b^{2|k|}`: the `(μ,j)` canonical coefficient of `∫_{(0,b]^d} u^{γ+h}
e^{−βN u^{2k}} du`. -/
noncomputable def boxSpectralKernel (n : ℕ) (h k : Fin (n + 1) → ℕ) (β b μ : ℝ) (j : ℕ)
    (γ : Fin (n + 1) → ℕ) : ℝ :=
  b ^ (∑ i, h i + (n + 1)) * (b ^ (2 * ∑ i, k i)) ^ (-μ) *
    ∑ q ∈ Finset.Ico j (n + 1), b ^ (∑ i, γ i) * monoKernel n h k β μ q γ * (q.choose j : ℝ) *
      (Real.log (b ^ (2 * ∑ i, k i))) ^ (q - j)

/-- ★ **The box coefficient at zero fluctuation is the ℓ¹ box-kernel pairing.** -/
theorem boxCoeff_zero_eq_tsum (hk : ∀ i, 0 < k i) (hβ : 0 < β) {b : ℝ} (hb : 0 < b)
    {cη : CoeffFamily (n + 1)} (hη : AbsSummableAt cη b) :
    boxCoeff n h k β b 0 cη μ j = ∑' γ, cη γ * boxSpectralKernel n h k β b μ j γ := by
  have hηs : AbsSummable (scale cη b) := AbsSummable.of_scale hb.le hη
  have hs0 : scale (0 : CoeffFamily (n + 1)) b = 0 := by
    funext γ
    change (0 : CoeffFamily (n + 1)) γ * b ^ (∑ i, γ i) = 0
    rw [Pi.zero_apply, zero_mul]
  unfold boxCoeff boxSpectralKernel
  rw [hs0]
  simp_rw [familySpectralCoeff_zero_eq_tsum n h k β _ _ hk hβ hηs]
  have hsum : ∀ q ∈ Finset.Ico j (n + 1), Summable fun γ =>
      scale cη b γ * monoKernel n h k β μ q γ * (q.choose j : ℝ) *
        (Real.log (b ^ (2 * ∑ i, k i))) ^ (q - j) := fun q _ =>
    ((summable_mul_monoKernel n h k β μ q hk hβ hηs).mul_right _).mul_right _
  have hq : ∀ q ∈ Finset.Ico j (n + 1),
      (∑' γ, scale cη b γ * monoKernel n h k β μ q γ) * (q.choose j : ℝ) *
        (Real.log (b ^ (2 * ∑ i, k i))) ^ (q - j) =
      ∑' γ, scale cη b γ * monoKernel n h k β μ q γ * (q.choose j : ℝ) *
        (Real.log (b ^ (2 * ∑ i, k i))) ^ (q - j) := fun q _ => by
    rw [← tsum_mul_right, ← tsum_mul_right]
  rw [Finset.sum_congr rfl hq, ← Summable.tsum_finsetSum hsum, ← tsum_mul_left]
  refine tsum_congr fun γ => ?_
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  unfold scale
  ring

/-- The box-kernel bound constant. -/
noncomputable def boxSpectralKernelBound (n : ℕ) (h k : Fin (n + 1) → ℕ) (β b μ : ℝ) (j : ℕ) : ℝ :=
  |b ^ (∑ i, h i + (n + 1)) * (b ^ (2 * ∑ i, k i)) ^ (-μ)| *
    ∑ q ∈ Finset.Ico j (n + 1), kernelBound n k β μ * (q.choose j : ℝ) *
      |Real.log (b ^ (2 * ∑ i, k i))| ^ (q - j)

theorem boxSpectralKernelBound_nonneg (b : ℝ) : 0 ≤ boxSpectralKernelBound n h k β b μ j := by
  unfold boxSpectralKernelBound
  apply mul_nonneg (abs_nonneg _)
  exact Finset.sum_nonneg fun q _ =>
    mul_nonneg (mul_nonneg (kernelBound_nonneg n k β μ) (by positivity)) (by positivity)

/-- **The box kernel is bounded by `C b^{|γ|}`**, uniformly in the multi-index. -/
theorem abs_boxSpectralKernel_le (hk : ∀ i, 0 < k i) (hβ : 0 < β) {b : ℝ} (hb : 0 ≤ b)
    (γ : Fin (n + 1) → ℕ) :
    |boxSpectralKernel n h k β b μ j γ| ≤
      boxSpectralKernelBound n h k β b μ j * b ^ (∑ i, γ i) := by
  unfold boxSpectralKernel boxSpectralKernelBound
  rw [abs_mul, mul_assoc, Finset.sum_mul]
  refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun q _ => ?_)) (abs_nonneg _)
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hb _), Nat.abs_cast, abs_pow]
  have h1 : |monoKernel n h k β μ q γ| ≤ kernelBound n k β μ :=
    abs_monoKernel_le n h k β μ q hk hβ γ
  have h2 : (0 : ℝ) ≤ (q.choose j : ℝ) := by positivity
  have h3 : (0 : ℝ) ≤ |Real.log (b ^ (2 * ∑ i, k i))| ^ (q - j) := by positivity
  have h4 : (0 : ℝ) ≤ b ^ (∑ i, γ i) := pow_nonneg hb _
  calc b ^ (∑ i, γ i) * |monoKernel n h k β μ q γ| * (q.choose j : ℝ) *
        |Real.log (b ^ (2 * ∑ i, k i))| ^ (q - j)
      ≤ b ^ (∑ i, γ i) * kernelBound n k β μ * (q.choose j : ℝ) *
        |Real.log (b ^ (2 * ∑ i, k i))| ^ (q - j) := by gcongr
    _ = _ := by ring

/-! ### The weighted ℓ¹ space is closed under the Cauchy product -/

omit n h k β μ j in
theorem absSummableAt_iff_absSummable_scale {d : ℕ} {c : CoeffFamily d} {b : ℝ} (hb : 0 ≤ b) :
    AbsSummableAt c b ↔ AbsSummable (scale c b) := by
  unfold AbsSummableAt AbsSummable scale
  refine summable_congr fun γ => ?_
  rw [abs_mul, abs_of_nonneg (pow_nonneg hb _)]

omit n h k β μ j in
theorem scale_conv {d : ℕ} (c e : CoeffFamily d) (b : ℝ) :
    scale (CoeffFamily.conv c e) b = CoeffFamily.conv (scale c b) (scale e b) := by
  funext γ
  unfold scale CoeffFamily.conv
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hle : α ≤ γ := Finset.mem_Iic.1 hα
  have hsum : ∑ i, γ i = ∑ i, α i + ∑ i, (γ - α) i := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.sub_apply]
    exact (add_tsub_cancel_of_le (hle i)).symm
  rw [hsum, pow_add]
  ring

omit n h k β μ j in
theorem AbsSummableAt.conv {d : ℕ} {c e : CoeffFamily d} {b : ℝ} (hb : 0 ≤ b)
    (hc : AbsSummableAt c b) (he : AbsSummableAt e b) : AbsSummableAt (CoeffFamily.conv c e) b := by
  rw [absSummableAt_iff_absSummable_scale hb] at hc he ⊢
  rw [scale_conv]
  exact hc.conv he

end Grammar
