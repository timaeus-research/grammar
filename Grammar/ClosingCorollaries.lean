/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PosteriorLeading

/-!
# Closing corollaries: different leading scales; the deterministic normal-form bridge (Stage S19)

Unit 289 (Astra #36, the optional two-unit closing tranche, done as one unit). (i) **Different
leading scales**: if `(U_ℓ/a_ℓ, V_ℓ/b_ℓ) ⇒ (A, B)` with deterministic nonzero normalisations and
`P(B = 0) = 0`, then `(b_ℓ/a_ℓ)·(U_ℓ/V_ℓ) ⇒ A/B` (`tendstoInDistribution_div_of_scaled'`); the
assembled form (`tendstoInDistribution_posterior_scales`): with numerator target `(μ_φ, j_φ)` and
denominator target `(μ₁, j₁)`, residuals and predecessor sums at their respective targets,
`N_ℓ^{μ_φ − μ₁} (log N_ℓ)^{j₁ − j_φ} · Z^0_ℓ[φ]/Z^0_ℓ[1] ⇒ C^φ_{μ_φ,j_φ}(Y)/C¹_{μ₁,j₁}(X)` (real
exponents, integer difference of log powers as a real). (ii) **Conditional deterministic
finite-chart normal-form expansion**: for a FIXED joint datum `x` (in particular zero phase and
deterministic amplitudes), `Z_nf(N) = 𝒵^{glob}(N; x)` satisfies
`(Z_nf(N) − S_{≺(μ,j)}(N)) / (N^{-μ}(log N)^j) → C^{glob}_{μ,j}(x)` (`tendsto_gRemainder_fixed`);
with an external deterministic decomposition `Z_pop = Z_nf + E`, `E = o(N^{-μ}(log N)^j)`, the
same holds for `Z_pop` (`tendsto_normalForm_pop`), and if the predecessor sum vanishes and the
coefficient
is nonzero, `Z_pop(N) ∼ C^{glob}_{μ,j}(x) N^{-μ}(log N)^j` (`isEquivalent_normalForm_pop`). This is
a
deterministic corollary of the assembly machinery, **not** the paper's (unrevised) §3 theorem
`thm:expectation_expansion`: no resolution atlas, adapted partition of unity or fibre integration is
constructed, and nothing is claimed about which coefficients are nonzero.
-/

open MeasureTheory Set Real Filter Topology Asymptotics

namespace Grammar

open scoped Classical

variable {ι Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {l : Filter ι}
  [l.IsCountablyGenerated]

/-- **Different leading scales**: `(U_ℓ/a_ℓ, V_ℓ/b_ℓ) ⇒ (A, B)`, `P(B = 0) = 0`, `a_ℓ, b_ℓ ≠ 0` ⇒
`(b_ℓ/a_ℓ)·(U_ℓ/V_ℓ) ⇒ A/B`. -/
theorem tendstoInDistribution_div_of_scaled' (U V : ι → Ω → ℝ) (a b : ι → ℝ) (ha : ∀ i, a i ≠ 0)
    (hb : ∀ i, b i ≠ 0) (hUm : ∀ i, Measurable (U i)) (hVm : ∀ i, Measurable (V i))
    (A B : Ω' → ℝ) (hAm : Measurable A) (hBm : Measurable B)
    (hUV : TendstoInDistribution (fun i ω => (U i ω / a i, V i ω / b i)) l (fun ω => (A ω, B ω))
      (fun _ => μ) μ')
    (hB : μ' {ω | B ω = 0} = 0) :
    TendstoInDistribution (fun i ω => b i / a i * (U i ω / V i ω)) l (fun ω => A ω / B ω)
      (fun _ => μ) μ' := by
  have h := tendstoInDistribution_div (fun i ω => U i ω / a i) (fun i ω => V i ω / b i)
    (fun i => (hUm i).div_const _) (fun i => (hVm i).div_const _) A B hAm hBm hUV hB
  have heq : (fun i ω => U i ω / a i / (V i ω / b i)) = fun i ω => b i / a i * (U i ω / V i ω) := by
    funext i ω
    have := ha i; have := hb i
    field_simp
  rw [heq] at h
  exact h

variable {M : ℕ} {K : Fin M → Type*} [∀ I, TopologicalSpace (K I)] [∀ I, CompactSpace (K I)]
  [∀ I, T2Space (K I)] [∀ I, MeasurableSpace (K I)] [∀ I, OpensMeasurableSpace (K I)]
  {n : Fin M → ℕ} (ν : (I : Fin M) → Measure (K I)) [∀ I, IsFiniteMeasure (ν I)]
  (h k : (I : Fin M) → Fin (n I + 1) → ℕ) (β : ℝ) (b : Fin M → ℝ)

/-- The pair of coefficients at two different targets. -/
noncomputable def pairCoeff₂ (p : PairData K n) (μφ : ℝ) (jφ : ℕ) (μ₁ : ℝ) (j₁ : ℕ) : ℝ × ℝ :=
  (gCoeff ν h k β b p.num μφ jφ, gCoeff ν h k β b p.den μ₁ j₁)

/-- The pair of remainders at two different targets minus the coefficients tends to zero in
probability. -/
theorem tendstoInMeasure_pairRemainder₂_sub (hk : ∀ I i, 0 < k I i) (hβ : 0 < β)
    (hb : ∀ I, 0 < b I) {μφ : ℝ} (hμφ : ∃ m : ℕ, μφ = (m : ℝ) / commonQ k) {jφ : ℕ}
    (hjφ : jφ ≤ commonD n) {μ₁ : ℝ} (hμ₁ : ∃ m : ℕ, μ₁ = (m : ℝ) / commonQ k) {j₁ : ℕ}
    (hj₁ : j₁ ≤ commonD n) (XY : ι → Ω → PairData K n) (Z : Ω' → PairData K n)
    (hXY : TendstoInDistribution XY l Z (fun _ => μ) μ') (Nseq : ι → ℝ)
    (hN : Tendsto Nseq l atTop) :
    TendstoInMeasure μ (fun i ω =>
      (gRemainder ν h k β b (XY i ω).num μφ jφ (Nseq i) - gCoeff ν h k β b (XY i ω).num μφ jφ,
       gRemainder ν h k β b (XY i ω).den μ₁ j₁ (Nseq i) - gCoeff ν h k β b (XY i ω).den μ₁ j₁))
      l (fun _ => (0 : ℝ × ℝ)) := by
  refine tendstoInMeasure_zero_of_uniform_on_balls'' _ XY (fun R hR ε hε => ?_)
    (normBounded_of_tendstoInDistribution' XY Z hXY)
  have huφ := Metric.tendstoUniformlyOn_iff.1
    (tendstoUniformlyOn_gRemainder ν h k β b hk hβ hb hμφ hjφ R) ε hε
  have hu₁ := Metric.tendstoUniformlyOn_iff.1
    (tendstoUniformlyOn_gRemainder ν h k β b hk hβ hb hμ₁ hj₁ R) ε hε
  filter_upwards [hN.eventually huφ, hN.eventually hu₁] with i hiφ hi₁ ω hω
  have h1 := hiφ (XY i ω).num (by simpa using (norm_num_le (XY i ω)).trans hω)
  have h2 := hi₁ (XY i ω).den (by simpa using (norm_den_le (XY i ω)).trans hω)
  rw [Real.dist_eq, abs_sub_comm] at h1 h2
  rw [Prod.norm_def]
  exact max_le (by simpa [Real.norm_eq_abs] using h1.le) (by simpa [Real.norm_eq_abs] using h2.le)

/-- **The different-scale leading posterior quotient (assembled).** With numerator target
`(μ_φ, j_φ)` and denominator target `(μ₁, j₁)` (residuals and predecessor sums at their respective
scales), `N_ℓ^{μ_φ−μ₁} (log N_ℓ)^{j₁−j_φ} · Z^0_ℓ[φ]/Z^0_ℓ[1] ⇒ C^φ_{μ_φ,j_φ}(Y)/C¹_{μ₁,j₁}(X)`. -/
theorem tendstoInDistribution_posterior_scales (hk : ∀ I i, 0 < k I i) (hβ : 0 < β)
    (hb : ∀ I, 0 < b I) {μφ : ℝ} (hμφ : ∃ m : ℕ, μφ = (m : ℝ) / commonQ k) {jφ : ℕ}
    (hjφ : jφ ≤ commonD n) {μ₁ : ℝ} (hμ₁ : ∃ m : ℕ, μ₁ = (m : ℝ) / commonQ k) {j₁ : ℕ}
    (hj₁ : j₁ ≤ commonD n) (XY : ι → Ω → PairData K n) (hXYm : ∀ i, Measurable (XY i))
    (Z : Ω' → PairData K n) (hZm : Measurable Z)
    (hXY : TendstoInDistribution XY l Z (fun _ => μ) μ') (Nseq : ι → ℝ)
    (hN1 : ∀ i, 1 < Nseq i) (hN : Tendsto Nseq l atTop) (Zφ Z1 Eφ E1 : ι → Ω → ℝ)
    (hZφm : ∀ i, Measurable (Zφ i)) (hZ1m : ∀ i, Measurable (Z1 i))
    (hdφ : ∀ i, ∀ᵐ ω ∂μ, Zφ i ω = gInt ν h k β b (XY i ω).num (Nseq i) + Eφ i ω)
    (hd1 : ∀ i, ∀ᵐ ω ∂μ, Z1 i ω = gInt ν h k β b (XY i ω).den (Nseq i) + E1 i ω)
    (hEφ : TendstoInMeasure μ (fun i ω => Eφ i ω / (Nseq i ^ (-μφ) * Real.log (Nseq i) ^ jφ)) l
      (fun _ => 0))
    (hE1 : TendstoInMeasure μ (fun i ω => E1 i ω / (Nseq i ^ (-μ₁) * Real.log (Nseq i) ^ j₁)) l
      (fun _ => 0))
    (hpφ : ∀ i, ∀ᵐ ω ∂μ,
      absPredSum (commonQ k) (commonD n) (gCoeff ν h k β b (XY i ω).num) μφ jφ (Nseq i) = 0)
    (hp1 : ∀ i, ∀ᵐ ω ∂μ,
      absPredSum (commonQ k) (commonD n) (gCoeff ν h k β b (XY i ω).den) μ₁ j₁ (Nseq i) = 0)
    (hB : μ' {ω | gCoeff ν h k β b (Z ω).den μ₁ j₁ = 0} = 0) :
    TendstoInDistribution (fun i ω =>
        (Nseq i ^ (-μ₁) * Real.log (Nseq i) ^ j₁) / (Nseq i ^ (-μφ) * Real.log (Nseq i) ^ jφ) *
          (Zφ i ω / Z1 i ω)) l
      (fun ω => gCoeff ν h k β b (Z ω).num μφ jφ / gCoeff ν h k β b (Z ω).den μ₁ j₁)
      (fun _ => μ) μ' := by
  -- joint convergence of the two differently normalised integrals
  have hC : TendstoInDistribution (fun i ω => pairCoeff₂ ν h k β b (XY i ω) μφ jφ μ₁ j₁) l
      (fun ω => pairCoeff₂ ν h k β b (Z ω) μφ jφ μ₁ j₁) (fun _ => μ) μ' :=
    hXY.continuous_comp (g := fun p => pairCoeff₂ ν h k β b p μφ jφ μ₁ j₁)
      (((continuous_gCoeff ν h k β b hk hβ hb μφ jφ).comp continuous_num).prodMk
        ((continuous_gCoeff ν h k β b hk hβ hb μ₁ j₁).comp continuous_den))
  have hpair : TendstoInDistribution (fun i ω =>
      (Zφ i ω / (Nseq i ^ (-μφ) * Real.log (Nseq i) ^ jφ),
       Z1 i ω / (Nseq i ^ (-μ₁) * Real.log (Nseq i) ^ j₁))) l
      (fun ω => pairCoeff₂ ν h k β b (Z ω) μφ jφ μ₁ j₁) (fun _ => μ) μ' := by
    refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hC ?_ fun i => ?_
    · have hsum := tendstoInMeasure_add_zero
        (tendstoInMeasure_pairRemainder₂_sub ν h k β b hk hβ hb hμφ hjφ hμ₁ hj₁ XY Z hXY Nseq hN)
        (tendstoInMeasure_prodMk_zero' hEφ hE1)
      refine TendstoInMeasure.congr (fun i => ?_) (Eventually.of_forall fun _ => rfl) hsum
      filter_upwards [hdφ i, hd1 i, hpφ i, hp1 i] with ω hφ h1 hpφ' hp1'
      simp only [Pi.sub_apply, pairCoeff₂, Prod.mk_add_mk, Prod.mk_sub_mk]
      unfold gRemainder abstractRemainder
      rw [hφ, h1, hpφ', hp1']
      ext <;> simp only <;> ring
    · exact ((hZφm i).div_const _).prodMk ((hZ1m i).div_const _) |>.aemeasurable
  have haφ : ∀ i, Nseq i ^ (-μφ) * Real.log (Nseq i) ^ jφ ≠ 0 := fun i => by
    have h0 : 0 < Nseq i := lt_trans one_pos (hN1 i)
    have hl : 0 < Real.log (Nseq i) := Real.log_pos (hN1 i)
    positivity
  have ha₁ : ∀ i, Nseq i ^ (-μ₁) * Real.log (Nseq i) ^ j₁ ≠ 0 := fun i => by
    have h0 : 0 < Nseq i := lt_trans one_pos (hN1 i)
    have hl : 0 < Real.log (Nseq i) := Real.log_pos (hN1 i)
    positivity
  have hAm : Measurable fun ω => gCoeff ν h k β b (Z ω).num μφ jφ :=
    ((continuous_gCoeff ν h k β b hk hβ hb μφ jφ).comp continuous_num).measurable.comp hZm
  have hBm : Measurable fun ω => gCoeff ν h k β b (Z ω).den μ₁ j₁ :=
    ((continuous_gCoeff ν h k β b hk hβ hb μ₁ j₁).comp continuous_den).measurable.comp hZm
  exact tendstoInDistribution_div_of_scaled' Zφ Z1 _ _ haφ ha₁ hZφm hZ1m _ _ hAm hBm hpair hB

/-! ### The conditional deterministic normal-form expansion -/

/-- For a fixed joint datum the global ordered remainder converges to the global coefficient. -/
theorem tendsto_gRemainder_fixed (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (hb : ∀ I, 0 < b I)
    (x : JointData K n) {μ₀ : ℝ} (hμ : ∃ m : ℕ, μ₀ = (m : ℝ) / commonQ k) {j : ℕ}
    (hj : j ≤ commonD n) :
    Tendsto (fun N => gRemainder ν h k β b x μ₀ j N) atTop (𝓝 (gCoeff ν h k β b x μ₀ j)) :=
  (tendstoUniformlyOn_gRemainder ν h k β b hk hβ hb hμ hj ‖x‖).tendsto_at (by simp)

/-- **Conditional deterministic finite-chart normal-form expansion**: if `Z_pop = Z_nf + E` with
`Z_nf(N) = 𝒵^{glob}(N; x)` for a fixed joint datum `x` and `E(N) = o(N^{-μ}(log N)^j)`, then
`(Z_pop(N) − S_{≺(μ,j)}(N)) / (N^{-μ}(log N)^j) → C^{glob}_{μ,j}(x)`. -/
theorem tendsto_normalForm_pop (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (hb : ∀ I, 0 < b I)
    (x : JointData K n) {μ₀ : ℝ} (hμ : ∃ m : ℕ, μ₀ = (m : ℝ) / commonQ k) {j : ℕ}
    (hj : j ≤ commonD n) (Zpop E : ℝ → ℝ) (hdecomp : ∀ N, Zpop N = gInt ν h k β b x N + E N)
    (hE : Tendsto (fun N => E N / (N ^ (-μ₀) * Real.log N ^ j)) atTop (𝓝 0)) :
    Tendsto (fun N => (Zpop N - absPredSum (commonQ k) (commonD n) (gCoeff ν h k β b x) μ₀ j N) /
        (N ^ (-μ₀) * Real.log N ^ j)) atTop (𝓝 (gCoeff ν h k β b x μ₀ j)) := by
  have ht := (tendsto_gRemainder_fixed ν h k β b hk hβ hb x hμ hj).add hE
  rw [add_zero] at ht
  refine ht.congr fun N => ?_
  unfold gRemainder abstractRemainder
  rw [hdecomp N]
  ring

/-- **Leading-term asymptotic equivalence**: if moreover the predecessor sum vanishes and the
coefficient `c = C^{glob}_{μ,j}(x)` is nonzero, then `Z_pop(N) ∼ c N^{-μ}(log N)^j`. -/
theorem isEquivalent_normalForm_pop (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (hb : ∀ I, 0 < b I)
    (x : JointData K n) {μ₀ : ℝ} (hμ : ∃ m : ℕ, μ₀ = (m : ℝ) / commonQ k) {j : ℕ}
    (hj : j ≤ commonD n) (Zpop E : ℝ → ℝ) (hdecomp : ∀ N, Zpop N = gInt ν h k β b x N + E N)
    (hE : Tendsto (fun N => E N / (N ^ (-μ₀) * Real.log N ^ j)) atTop (𝓝 0))
    (hpred : ∀ N, absPredSum (commonQ k) (commonD n) (gCoeff ν h k β b x) μ₀ j N = 0)
    (hc : gCoeff ν h k β b x μ₀ j ≠ 0) :
    Zpop ~[atTop] fun N => gCoeff ν h k β b x μ₀ j * (N ^ (-μ₀) * Real.log N ^ j) := by
  have ht := tendsto_normalForm_pop ν h k β b hk hβ hb x hμ hj Zpop E hdecomp hE
  simp only [hpred, sub_zero] at ht
  set c := gCoeff ν h k β b x μ₀ j with hcdef
  refine isEquivalent_of_tendsto_one ?_
  have h' := ht.div_const c
  rw [div_self hc] at h'
  refine h'.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  have h0 : 0 < N := by linarith
  have hl : 0 < Real.log N := Real.log_pos hN
  have hD : N ^ (-μ₀) * Real.log N ^ j ≠ 0 := by positivity
  simp only [Pi.div_apply]
  field_simp

end Grammar
