/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PosteriorLeading
import Grammar.QuotientInDistribution
import Grammar.ApproxInDistribution
import Grammar.StochasticAssemblyInfra

/-!
# The stochastic second-order posterior quotient (unit 328; Astra #39 units 1–3)

Random joint data `(X_ℓ, Y_ℓ) ⇒ (X, Y)` (denominator, numerator) with sample sizes `N_ℓ → ∞`,
a.e. external decompositions `Z^1_ℓ = 𝒵(N_ℓ; X_ℓ) + E¹_ℓ`, `Z^φ_ℓ = 𝒵(N_ℓ; Y_ℓ) + E^φ_ℓ` with
residuals negligible at the NEXT-log scales `N^{-μ₀}L^{s}`, `N^{-μ₀'}L^{s'}` (targets `(μ₀, s+1)`,
`(μ₀', s'+1)`), and a.e. vanishing of all predecessors of the targets for the approximating data.
Then, centring at the leading quotient of the CURRENT data `A'_ℓ/A_ℓ` (not at the limit `A'/A`:
weak convergence does not control `log N (A'_ℓ/A_ℓ − A'/A)`),
```
log N_ℓ ( Z^φ_ℓ/Z^1_ℓ · N_ℓ^{μ₀'−μ₀} L^{s+1}/L^{s'+1} − A'_ℓ/A_ℓ ) ⇒ (A B' − A' B)/A²
```
whenever `P(A = 0) = 0` (`tendstoInDistribution_posterior_second_order`), with `A, B` (resp.
`A', B'`) the limit coefficients of `N^{-μ₀}L^{s+1}`, `N^{-μ₀}L^{s}` (resp. primed). Route: the
ordered remainder at `(μ₀, s)` is the two-term remainder centred at the current leading coefficient
(`absPredSum_succ`, `tendstoInMeasure_randomTwoTerm_sub`); the four statistics converge jointly with
a deterministic `1/log N → 0` coordinate (Slutsky); numerator and denominator of the algebraic
identity are continuous images and their quotient converges (`tendstoInDistribution_div`); the
identity fails only on `{A_ℓ = 0} ∪ {A_ℓ + R_ℓ/L = 0}`, whose probability tends to zero (closed-set
Portmanteau and `P(A = 0) = 0`), so the approximation lemma transfers the limit. Not claimed: the
multiplicity-one case (leading log degree `0`, needing log-weighted remainders), or centring at
`A'/A`. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

/-- The predecessor set of `(μ, j)` is that of `(μ, j+1)` together with `(μ, j+1)`. -/
theorem predSet_succ {D Q : ℕ} (hQ : 0 < Q) {μ : ℝ} (hμ : ∃ m : ℕ, μ = (m : ℝ) / Q) {j : ℕ}
    (hj : j + 1 ≤ D) : predSet D Q μ j = insert (μ, j + 1) (predSet D Q μ (j + 1)) := by
  ext p
  simp only [mem_predSet_iff, Finset.mem_insert, precedes]
  constructor
  · rintro ⟨hp, hprec⟩
    rcases hprec with hlt | ⟨heq, hgt⟩
    · exact Or.inr ⟨hp, Or.inl hlt⟩
    · rcases Nat.lt_or_ge (j + 1) p.2 with h1 | h1
      · exact Or.inr ⟨hp, Or.inr ⟨heq, h1⟩⟩
      · left
        have : p.2 = j + 1 := by omega
        exact Prod.ext heq this
  · rintro (rfl | ⟨hp, hprec⟩)
    · refine ⟨?_, Or.inr ⟨rfl, Nat.lt_succ_self j⟩⟩
      rw [mem_indexSet_iff]
      obtain ⟨m, hm⟩ := hμ
      refine ⟨?_, by omega⟩
      show μ ∈ latticeBelow Q (μ + 1)
      rw [hm]
      exact mem_latticeBelow hQ (by linarith)
    · refine ⟨hp, ?_⟩
      rcases hprec with hlt | ⟨heq, hgt⟩
      · exact Or.inl hlt
      · exact Or.inr ⟨heq, by omega⟩

/-- **Predecessor-sum split**: `∑_{≺(μ,j)} = c_{μ,j+1} N^{-μ} L^{j+1} + ∑_{≺(μ,j+1)}`. -/
theorem absPredSum_succ {D Q : ℕ} (hQ : 0 < Q) (c : ℝ → ℕ → ℝ) {μ : ℝ}
    (hμ : ∃ m : ℕ, μ = (m : ℝ) / Q) {j : ℕ} (hj : j + 1 ≤ D) (N : ℝ) :
    absPredSum Q D c μ j N =
      c μ (j + 1) * (N ^ (-μ) * Real.log N ^ (j + 1)) + absPredSum Q D c μ (j + 1) N := by
  unfold absPredSum
  rw [predSet_succ hQ hμ hj, Finset.sum_insert]
  · rfl
  · rw [mem_predSet_iff]
    rintro ⟨-, h⟩
    simp [precedes] at h

variable {M : ℕ} {K : Fin M → Type*} [∀ I, TopologicalSpace (K I)] [∀ I, CompactSpace (K I)]
  [∀ I, T2Space (K I)] [∀ I, MeasurableSpace (K I)] [∀ I, OpensMeasurableSpace (K I)]
  {n : Fin M → ℕ} (ν : (I : Fin M) → Measure (K I)) [∀ I, IsFiniteMeasure (ν I)]
  (h k : (I : Fin M) → Fin (n I + 1) → ℕ) (β : ℝ) (b : Fin M → ℝ)

variable {ι Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {l : Filter ι}
  [l.IsCountablyGenerated]

/-- **Random two-term remainder centred at the current leading coefficient**: with a.e. vanishing
predecessors of `(μ₀, s+1)` and a residual negligible at the scale `N^{-μ₀}L^{s}`,
`(Z_ℓ − A_ℓ N^{-μ₀}L^{s+1})/(N^{-μ₀}L^{s}) − B_ℓ → 0` in probability, where `A_ℓ, B_ℓ` are the
coefficients of the CURRENT data. -/
theorem tendstoInMeasure_randomTwoTerm_sub (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (hb : ∀ I, 0 < b I)
    {μ₀ : ℝ} (hμ : ∃ m : ℕ, μ₀ = (m : ℝ) / commonQ k) {s : ℕ} (hs : s + 1 ≤ commonD n)
    (X : ι → Ω → JointData K n) (Z : Ω' → JointData K n)
    (hX : TendstoInDistribution X l Z (fun _ => μ) μ') (Nseq : ι → ℝ) (hN : Tendsto Nseq l atTop)
    (Zg E : ι → Ω → ℝ)
    (hdecomp : ∀ i, ∀ᵐ ω ∂μ, Zg i ω = gInt ν h k β b (X i ω) (Nseq i) + E i ω)
    (hE : TendstoInMeasure μ (fun i ω => E i ω / (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ s)) l
      (fun _ => 0))
    (hp : ∀ i, ∀ᵐ ω ∂μ,
      absPredSum (commonQ k) (commonD n) (gCoeff ν h k β b (X i ω)) μ₀ (s + 1) (Nseq i) = 0) :
    TendstoInMeasure μ (fun i ω => (Zg i ω - gCoeff ν h k β b (X i ω) μ₀ (s + 1) *
      (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ (s + 1))) / (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ s) -
      gCoeff ν h k β b (X i ω) μ₀ s) l (fun _ => 0) := by
  have h1 := tendstoInMeasure_gRemainder_sub ν h k β b hk hβ hb hμ (by omega : s ≤ commonD n) X Z
    hX Nseq hN
  have h2 := tendstoInMeasure_add_zero h1 hE
  refine h2.congr' (Eventually.of_forall fun i => ?_) (Eventually.of_forall fun _ => rfl)
  filter_upwards [hdecomp i, hp i] with ω hd hp'
  unfold gRemainder abstractRemainder
  rw [absPredSum_succ (commonQ_pos k hk) _ hμ hs, hp', add_zero, hd]
  ring

theorem continuous_vec4 {X : Type*} [TopologicalSpace X] {f₀ f₁ f₂ f₃ : X → ℝ}
    (h₀ : Continuous f₀) (h₁ : Continuous f₁) (h₂ : Continuous f₂) (h₃ : Continuous f₃) :
    Continuous fun x => (![f₀ x, f₁ x, f₂ x, f₃ x] : Fin 4 → ℝ) := by
  refine continuous_pi fun a => ?_
  fin_cases a <;> simpa

theorem measurable_vec4 {X : Type*} [MeasurableSpace X] {f₀ f₁ f₂ f₃ : X → ℝ}
    (h₀ : Measurable f₀) (h₁ : Measurable f₁) (h₂ : Measurable f₂) (h₃ : Measurable f₃) :
    Measurable fun x => (![f₀ x, f₁ x, f₂ x, f₃ x] : Fin 4 → ℝ) := by
  refine measurable_pi_lambda _ fun a => ?_
  fin_cases a <;> simpa

/-- The algebraic core: numerator `A R' − A' R` and denominator `A (A + R c)` of the second-order
quotient, as a continuous map of the statistics `v = (R, A, R', A')` and `c = 1/log N`. -/
def secondOrderPair (q : (Fin 4 → ℝ) × ℝ) : ℝ × ℝ :=
  (q.1 1 * q.1 2 - q.1 3 * q.1 0, q.1 1 * (q.1 1 + q.1 0 * q.2))

theorem continuous_secondOrderPair : Continuous secondOrderPair := by
  unfold secondOrderPair
  fun_prop

/-- **The stochastic second-order posterior quotient.** -/
theorem tendstoInDistribution_posterior_second_order (hk : ∀ I i, 0 < k I i) (hβ : 0 < β)
    (hb : ∀ I, 0 < b I) {μ₀ : ℝ} (hμ : ∃ m : ℕ, μ₀ = (m : ℝ) / commonQ k) {s : ℕ}
    (hs : s + 1 ≤ commonD n) {μ₀' : ℝ} (hμ' : ∃ m : ℕ, μ₀' = (m : ℝ) / commonQ k) {s' : ℕ}
    (hs' : s' + 1 ≤ commonD n) (XY : ι → Ω → PairData K n) (hXYm : ∀ i, Measurable (XY i))
    (Z : Ω' → PairData K n) (hZm : Measurable Z)
    (hXY : TendstoInDistribution XY l Z (fun _ => μ) μ') (Nseq : ι → ℝ)
    (hN1 : ∀ i, 1 < Nseq i) (hN : Tendsto Nseq l atTop) (Zφ Z1 Eφ E1 : ι → Ω → ℝ)
    (hZφm : ∀ i, Measurable (Zφ i)) (hZ1m : ∀ i, Measurable (Z1 i))
    (hdφ : ∀ i, ∀ᵐ ω ∂μ, Zφ i ω = gInt ν h k β b (XY i ω).num (Nseq i) + Eφ i ω)
    (hd1 : ∀ i, ∀ᵐ ω ∂μ, Z1 i ω = gInt ν h k β b (XY i ω).den (Nseq i) + E1 i ω)
    (hEφ : TendstoInMeasure μ (fun i ω => Eφ i ω / (Nseq i ^ (-μ₀') * Real.log (Nseq i) ^ s')) l
      (fun _ => 0))
    (hE1 : TendstoInMeasure μ (fun i ω => E1 i ω / (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ s)) l
      (fun _ => 0))
    (hpφ : ∀ i, ∀ᵐ ω ∂μ, absPredSum (commonQ k) (commonD n) (gCoeff ν h k β b (XY i ω).num) μ₀'
      (s' + 1) (Nseq i) = 0)
    (hp1 : ∀ i, ∀ᵐ ω ∂μ, absPredSum (commonQ k) (commonD n) (gCoeff ν h k β b (XY i ω).den) μ₀
      (s + 1) (Nseq i) = 0)
    (hB : μ' {ω | gCoeff ν h k β b (Z ω).den μ₀ (s + 1) = 0} = 0) :
    TendstoInDistribution (fun i ω => Real.log (Nseq i) * (Zφ i ω / Z1 i ω *
        (Nseq i ^ (μ₀' - μ₀) * Real.log (Nseq i) ^ (s + 1) / Real.log (Nseq i) ^ (s' + 1)) -
        gCoeff ν h k β b (XY i ω).num μ₀' (s' + 1) / gCoeff ν h k β b (XY i ω).den μ₀ (s + 1))) l
      (fun ω => (gCoeff ν h k β b (Z ω).den μ₀ (s + 1) * gCoeff ν h k β b (Z ω).num μ₀' s' -
        gCoeff ν h k β b (Z ω).num μ₀' (s' + 1) * gCoeff ν h k β b (Z ω).den μ₀ s) /
        gCoeff ν h k β b (Z ω).den μ₀ (s + 1) ^ 2) (fun _ => μ) μ' := by
  -- the four statistics of the current data and the coefficients of the limit
  obtain ⟨A, hA⟩ : ∃ A : ι → Ω → ℝ, ∀ i ω, A i ω = gCoeff ν h k β b (XY i ω).den μ₀ (s + 1) :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨A', hA'⟩ : ∃ A' : ι → Ω → ℝ, ∀ i ω, A' i ω = gCoeff ν h k β b (XY i ω).num μ₀' (s' + 1) :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ι → Ω → ℝ, ∀ i ω, R i ω = (Z1 i ω - A i ω *
      (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ (s + 1))) / (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ s) :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨R', hR'⟩ : ∃ R' : ι → Ω → ℝ, ∀ i ω, R' i ω = (Zφ i ω - A' i ω *
      (Nseq i ^ (-μ₀') * Real.log (Nseq i) ^ (s' + 1))) /
      (Nseq i ^ (-μ₀') * Real.log (Nseq i) ^ s') := ⟨_, fun _ _ => rfl⟩
  have hden : TendstoInDistribution (fun i ω => (XY i ω).den) l (fun ω => (Z ω).den)
      (fun _ => μ) μ' := hXY.continuous_comp continuous_den
  have hnum : TendstoInDistribution (fun i ω => (XY i ω).num) l (fun ω => (Z ω).num)
      (fun _ => μ) μ' := hXY.continuous_comp continuous_num
  -- the two random two-term remainders
  have hRm : TendstoInMeasure μ (fun i ω => R i ω - gCoeff ν h k β b (XY i ω).den μ₀ s) l
      (fun _ => 0) := by
    have := tendstoInMeasure_randomTwoTerm_sub ν h k β b hk hβ hb hμ hs _ _ hden Nseq hN Z1 E1 hd1
      hE1 hp1
    refine this.congr' (Eventually.of_forall fun i => Eventually.of_forall fun ω => ?_)
      (Eventually.of_forall fun _ => rfl)
    dsimp only
    rw [hR, hA]
  have hR'm : TendstoInMeasure μ (fun i ω => R' i ω - gCoeff ν h k β b (XY i ω).num μ₀' s') l
      (fun _ => 0) := by
    have := tendstoInMeasure_randomTwoTerm_sub ν h k β b hk hβ hb hμ' hs' _ _ hnum Nseq hN Zφ Eφ
      hdφ hEφ hpφ
    refine this.congr' (Eventually.of_forall fun i => Eventually.of_forall fun ω => ?_)
      (Eventually.of_forall fun _ => rfl)
    dsimp only
    rw [hR', hA']
  -- measurability of the statistics
  have hAm : ∀ i, Measurable (A i) := fun i => by
    have : A i = fun ω => gCoeff ν h k β b (XY i ω).den μ₀ (s + 1) := funext (hA i)
    rw [this]
    exact (continuous_gCoeff ν h k β b hk hβ hb μ₀ (s + 1)).measurable.comp
      (continuous_den.measurable.comp (hXYm i))
  have hA'm : ∀ i, Measurable (A' i) := fun i => by
    have : A' i = fun ω => gCoeff ν h k β b (XY i ω).num μ₀' (s' + 1) := funext (hA' i)
    rw [this]
    exact (continuous_gCoeff ν h k β b hk hβ hb μ₀' (s' + 1)).measurable.comp
      (continuous_num.measurable.comp (hXYm i))
  have hRmeas : ∀ i, Measurable (R i) := fun i => by
    have : R i = fun ω => (Z1 i ω - A i ω * (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ (s + 1))) /
        (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ s) := funext (hR i)
    rw [this]
    exact ((hZ1m i).sub ((hAm i).mul_const _)).div_const _
  have hR'meas : ∀ i, Measurable (R' i) := fun i => by
    have : R' i = fun ω => (Zφ i ω - A' i ω * (Nseq i ^ (-μ₀') * Real.log (Nseq i) ^ (s' + 1))) /
        (Nseq i ^ (-μ₀') * Real.log (Nseq i) ^ s') := funext (hR' i)
    rw [this]
    exact ((hZφm i).sub ((hA'm i).mul_const _)).div_const _
  -- joint convergence of the coefficient vector `(B, A, B', A')`
  obtain ⟨Cz, hCz⟩ : ∃ Cz : Ω' → Fin 4 → ℝ, ∀ ω, Cz ω = ![gCoeff ν h k β b (Z ω).den μ₀ s,
      gCoeff ν h k β b (Z ω).den μ₀ (s + 1), gCoeff ν h k β b (Z ω).num μ₀' s',
      gCoeff ν h k β b (Z ω).num μ₀' (s' + 1)] := ⟨_, fun _ => rfl⟩
  have hCzfun : Cz = fun ω => ![gCoeff ν h k β b (Z ω).den μ₀ s,
      gCoeff ν h k β b (Z ω).den μ₀ (s + 1), gCoeff ν h k β b (Z ω).num μ₀' s',
      gCoeff ν h k β b (Z ω).num μ₀' (s' + 1)] := funext hCz
  have hgcont : Continuous fun p : PairData K n => (![gCoeff ν h k β b p.den μ₀ s,
      gCoeff ν h k β b p.den μ₀ (s + 1), gCoeff ν h k β b p.num μ₀' s',
      gCoeff ν h k β b p.num μ₀' (s' + 1)] : Fin 4 → ℝ) :=
    continuous_vec4 ((continuous_gCoeff ν h k β b hk hβ hb μ₀ s).comp continuous_den)
      ((continuous_gCoeff ν h k β b hk hβ hb μ₀ (s + 1)).comp continuous_den)
      ((continuous_gCoeff ν h k β b hk hβ hb μ₀' s').comp continuous_num)
      ((continuous_gCoeff ν h k β b hk hβ hb μ₀' (s' + 1)).comp continuous_num)
  have hC : TendstoInDistribution (fun i ω => (![gCoeff ν h k β b (XY i ω).den μ₀ s,
      gCoeff ν h k β b (XY i ω).den μ₀ (s + 1), gCoeff ν h k β b (XY i ω).num μ₀' s',
      gCoeff ν h k β b (XY i ω).num μ₀' (s' + 1)] : Fin 4 → ℝ)) l Cz (fun _ => μ) μ' := by
    rw [hCzfun]
    exact hXY.continuous_comp hgcont
  -- the statistics vector `V = (R, A, R', A')` converges to the same limit (Slutsky)
  obtain ⟨V, hV⟩ : ∃ V : ι → Ω → Fin 4 → ℝ, ∀ i ω, V i ω = ![R i ω, A i ω, R' i ω, A' i ω] :=
    ⟨_, fun _ _ => rfl⟩
  have hVm : ∀ i, Measurable (V i) := fun i => by
    have : V i = fun ω => ![R i ω, A i ω, R' i ω, A' i ω] := funext (hV i)
    rw [this]
    exact measurable_vec4 (hRmeas i) (hAm i) (hR'meas i) (hA'm i)
  have hVdist : TendstoInDistribution V l Cz (fun _ => μ) μ' := by
    refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hC ?_ fun i => (hVm i).aemeasurable
    have hzero : TendstoInMeasure μ (fun i ω => (0 : ℝ)) l (fun _ => 0) :=
      tendstoInMeasure_const_of_tendsto (fun _ => (0 : ℝ)) 0 tendsto_const_nhds
    have hpi := tendstoInMeasure_pi_zero (μ := μ) (L := l) (κ := Fin 4) (E := ℝ)
      ![fun i ω => R i ω - gCoeff ν h k β b (XY i ω).den μ₀ s, fun _ _ => (0 : ℝ),
        fun i ω => R' i ω - gCoeff ν h k β b (XY i ω).num μ₀' s', fun _ _ => (0 : ℝ)]
      (fun a => by fin_cases a <;> simp <;> first | exact hRm | exact hR'm | exact hzero)
    refine hpi.congr' (Eventually.of_forall fun i => Eventually.of_forall fun ω => ?_)
      (Eventually.of_forall fun _ => rfl)
    funext a
    simp only [Pi.sub_apply, hV]
    fin_cases a <;> simp [hA, hA']
  -- the deterministic coordinate `1/log N → 0`
  have hVc : TendstoInDistribution (fun i ω => (V i ω, (Real.log (Nseq i))⁻¹)) l
      (fun ω => (Cz ω, (0 : ℝ))) (fun _ => μ) μ' :=
    hVdist.prodMk_of_tendstoInMeasure_const V (fun i _ => (Real.log (Nseq i))⁻¹) Cz
      (tendstoInMeasure_const_of_tendsto (fun i => (Real.log (Nseq i))⁻¹) 0
        (tendsto_inv_log.comp hN))
      (fun _ => aemeasurable_const)
  -- numerator and denominator of the algebraic identity
  have hUW := hVc.continuous_comp continuous_secondOrderPair
  have hAz : Measurable fun ω => gCoeff ν h k β b (Z ω).den μ₀ (s + 1) :=
    (continuous_gCoeff ν h k β b hk hβ hb μ₀ (s + 1)).measurable.comp
      (continuous_den.measurable.comp hZm)
  have hCzm : Measurable Cz := by
    rw [hCzfun]
    exact measurable_vec4
      ((continuous_gCoeff ν h k β b hk hβ hb μ₀ s).measurable.comp
        (continuous_den.measurable.comp hZm)) hAz
      ((continuous_gCoeff ν h k β b hk hβ hb μ₀' s').measurable.comp
        (continuous_num.measurable.comp hZm))
      ((continuous_gCoeff ν h k β b hk hβ hb μ₀' (s' + 1)).measurable.comp
        (continuous_num.measurable.comp hZm))
  have hpairm : ∀ i, Measurable fun ω => secondOrderPair (V i ω, (Real.log (Nseq i))⁻¹) :=
    fun i => continuous_secondOrderPair.measurable.comp ((hVm i).prodMk measurable_const)
  have hpairzm : Measurable fun ω => secondOrderPair (Cz ω, (0 : ℝ)) :=
    continuous_secondOrderPair.measurable.comp (hCzm.prodMk measurable_const)
  have hW0 : μ' {ω | (secondOrderPair (Cz ω, 0)).2 = 0} = 0 := by
    convert hB using 2
    ext ω
    simp [secondOrderPair, hCz]
  have hdiv0 := tendstoInDistribution_div
    (fun i ω => (secondOrderPair (V i ω, (Real.log (Nseq i))⁻¹)).1)
    (fun i ω => (secondOrderPair (V i ω, (Real.log (Nseq i))⁻¹)).2)
    (fun i => measurable_fst.comp (hpairm i)) (fun i => measurable_snd.comp (hpairm i))
    (fun ω => (secondOrderPair (Cz ω, 0)).1) (fun ω => (secondOrderPair (Cz ω, 0)).2)
    (measurable_fst.comp hpairzm) (measurable_snd.comp hpairzm) hUW hW0
  -- the limit is the stated one
  have hdiv : TendstoInDistribution (fun i ω => (secondOrderPair (V i ω, (Real.log (Nseq i))⁻¹)).1 /
      (secondOrderPair (V i ω, (Real.log (Nseq i))⁻¹)).2) l
      (fun ω => (gCoeff ν h k β b (Z ω).den μ₀ (s + 1) * gCoeff ν h k β b (Z ω).num μ₀' s' -
        gCoeff ν h k β b (Z ω).num μ₀' (s' + 1) * gCoeff ν h k β b (Z ω).den μ₀ s) /
        gCoeff ν h k β b (Z ω).den μ₀ (s + 1) ^ 2) (fun _ => μ) μ' := by
    convert hdiv0 using 2
    simp only [secondOrderPair, hCz]
    simp
    try ring
  -- transfer through the exceptional events `A_ℓ = 0`, `A_ℓ + R_ℓ/log N = 0`
  have hAzc : Continuous fun p : PairData K n => gCoeff ν h k β b p.den μ₀ (s + 1) :=
    (continuous_gCoeff ν h k β b hk hβ hb μ₀ (s + 1)).comp continuous_den
  have hA'zc : Continuous fun p : PairData K n => gCoeff ν h k β b p.num μ₀' (s' + 1) :=
    (continuous_gCoeff ν h k β b hk hβ hb μ₀' (s' + 1)).comp continuous_num
  have hTm : ∀ i, Measurable fun ω => Real.log (Nseq i) * (Zφ i ω / Z1 i ω *
      (Nseq i ^ (μ₀' - μ₀) * Real.log (Nseq i) ^ (s + 1) / Real.log (Nseq i) ^ (s' + 1)) -
      gCoeff ν h k β b (XY i ω).num μ₀' (s' + 1) / gCoeff ν h k β b (XY i ω).den μ₀ (s + 1)) :=
    fun i => (((((hZφm i).div (hZ1m i)).mul_const _).sub
      ((hA'zc.measurable.comp (hXYm i)).div (hAzc.measurable.comp (hXYm i)))).const_mul _)
  have hlimm : Measurable fun ω => (gCoeff ν h k β b (Z ω).den μ₀ (s + 1) *
      gCoeff ν h k β b (Z ω).num μ₀' s' - gCoeff ν h k β b (Z ω).num μ₀' (s' + 1) *
      gCoeff ν h k β b (Z ω).den μ₀ s) / gCoeff ν h k β b (Z ω).den μ₀ (s + 1) ^ 2 := by
    have hB0 : Measurable fun ω => gCoeff ν h k β b (Z ω).den μ₀ s :=
      (continuous_gCoeff ν h k β b hk hβ hb μ₀ s).measurable.comp
        (continuous_den.measurable.comp hZm)
    have hB' : Measurable fun ω => gCoeff ν h k β b (Z ω).num μ₀' s' :=
      (continuous_gCoeff ν h k β b hk hβ hb μ₀' s').measurable.comp
        (continuous_num.measurable.comp hZm)
    have hA'z : Measurable fun ω => gCoeff ν h k β b (Z ω).num μ₀' (s' + 1) :=
      hA'zc.measurable.comp hZm
    exact ((hAz.mul hB').sub (hA'z.mul hB0)).div (hAz.pow_const 2)
  -- the current leading coefficient and `A_ℓ + R_ℓ/log N` converge in distribution to `A`
  have hAdist : TendstoInDistribution A l (fun ω => gCoeff ν h k β b (Z ω).den μ₀ (s + 1))
      (fun _ => μ) μ' := by
    have : A = fun i ω => gCoeff ν h k β b (XY i ω).den μ₀ (s + 1) :=
      funext fun i => funext (hA i)
    rw [this]
    exact hXY.continuous_comp (g := fun p : PairData K n => gCoeff ν h k β b p.den μ₀ (s + 1)) hAzc
  have hARdist : TendstoInDistribution (fun i ω => A i ω + R i ω * (Real.log (Nseq i))⁻¹) l
      (fun ω => gCoeff ν h k β b (Z ω).den μ₀ (s + 1)) (fun _ => μ) μ' := by
    have := hVc.continuous_comp (g := fun q : (Fin 4 → ℝ) × ℝ => q.1 1 + q.1 0 * q.2)
      (by fun_prop)
    convert this using 2
    · simp [Function.comp_def, hV]
    · simp [Function.comp_def, hCz]
  have hARm : ∀ i, Measurable fun ω => A i ω + R i ω * (Real.log (Nseq i))⁻¹ := fun i =>
    (hAm i).add ((hRmeas i).mul_const _)
  -- the approximation step
  refine tendstoInDistribution_of_approx _ _ hTm hlimm fun η hη => ?_
  refine ⟨fun i ω => (secondOrderPair (V i ω, (Real.log (Nseq i))⁻¹)).1 /
    (secondOrderPair (V i ω, (Real.log (Nseq i))⁻¹)).2, _,
    fun i => (measurable_fst.comp (hpairm i)).div (measurable_snd.comp (hpairm i)), hlimm, hdiv,
    ?_, by simp⟩
  -- choose `δ` with `P(|A| ≤ δ) < η/2`
  obtain ⟨m, hm⟩ := ((tendsto_measure_abs_le_of_ae_ne_zero _ hAz hB).eventually
    (gt_mem_nhds (ENNReal.ofReal_pos.2 (half_pos hη)))).exists
  set δ : ℝ := 1 / ((m : ℝ) + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  have hF : IsClosed {x : ℝ | |x| ≤ δ} := isClosed_le continuous_abs continuous_const
  have hmapz : (μ'.map fun ω => gCoeff ν h k β b (Z ω).den μ₀ (s + 1)) {x | |x| ≤ δ} =
      μ' {ω | |gCoeff ν h k β b (Z ω).den μ₀ (s + 1)| ≤ δ} := Measure.map_apply hAz hF.measurableSet
  have hev1 : ∀ᶠ i in l, μ {ω | |A i ω| ≤ δ} < ENNReal.ofReal (η / 2) := by
    have hport := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hAdist.tendsto hF
    simp only [ProbabilityMeasure.coe_mk] at hport
    have hmap : ∀ i, (μ.map (A i)) {x | |x| ≤ δ} = μ {ω | |A i ω| ≤ δ} := fun i =>
      Measure.map_apply (hAm i) hF.measurableSet
    simp only [hmap, hmapz] at hport
    exact eventually_lt_of_limsup_lt (lt_of_le_of_lt hport hm)
  have hev2 : ∀ᶠ i in l, μ {ω | |A i ω + R i ω * (Real.log (Nseq i))⁻¹| ≤ δ} <
      ENNReal.ofReal (η / 2) := by
    have hport := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hARdist.tendsto hF
    simp only [ProbabilityMeasure.coe_mk] at hport
    have hmap : ∀ i, (μ.map fun ω => A i ω + R i ω * (Real.log (Nseq i))⁻¹) {x | |x| ≤ δ} =
        μ {ω | |A i ω + R i ω * (Real.log (Nseq i))⁻¹| ≤ δ} := fun i =>
      Measure.map_apply (hARm i) hF.measurableSet
    simp only [hmap, hmapz] at hport
    exact eventually_lt_of_limsup_lt (lt_of_le_of_lt hport hm)
  filter_upwards [hev1, hev2] with i hi1 hi2
  have hN0 : 0 < Nseq i := by linarith [hN1 i]
  have hL : 0 < Real.log (Nseq i) := Real.log_pos (hN1 i)
  have hsub : {ω | Real.log (Nseq i) * (Zφ i ω / Z1 i ω *
      (Nseq i ^ (μ₀' - μ₀) * Real.log (Nseq i) ^ (s + 1) / Real.log (Nseq i) ^ (s' + 1)) -
      gCoeff ν h k β b (XY i ω).num μ₀' (s' + 1) / gCoeff ν h k β b (XY i ω).den μ₀ (s + 1)) ≠
      (secondOrderPair (V i ω, (Real.log (Nseq i))⁻¹)).1 /
        (secondOrderPair (V i ω, (Real.log (Nseq i))⁻¹)).2} ⊆
      {ω | |A i ω| ≤ δ} ∪ {ω | |A i ω + R i ω * (Real.log (Nseq i))⁻¹| ≤ δ} := by
    intro ω hω
    simp only [mem_setOf_eq, mem_union]
    by_contra hcon
    push_neg at hcon
    apply hω
    have hA0 : A i ω ≠ 0 := by
      intro h0
      have := hcon.1
      rw [h0, abs_zero] at this
      linarith
    have hAR0 : A i ω + R i ω * (Real.log (Nseq i))⁻¹ ≠ 0 := by
      intro h0
      have := hcon.2
      rw [h0, abs_zero] at this
      linarith
    have hAR' : A i ω * Real.log (Nseq i) + R i ω ≠ 0 := by
      intro h0
      apply hAR0
      field_simp
      linear_combination h0
    have hPμ : Nseq i ^ (-μ₀) ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
    have hPμ' : Nseq i ^ (-μ₀') ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
    have hLs : Real.log (Nseq i) ^ s ≠ 0 := pow_ne_zero _ hL.ne'
    have hLs' : Real.log (Nseq i) ^ s' ≠ 0 := pow_ne_zero _ hL.ne'
    have hZ1 : Z1 i ω = R i ω * (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ s) +
        A i ω * (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ (s + 1)) := by
      rw [hR]
      field_simp
      ring
    have hZφ : Zφ i ω = R' i ω * (Nseq i ^ (-μ₀') * Real.log (Nseq i) ^ s') +
        A' i ω * (Nseq i ^ (-μ₀') * Real.log (Nseq i) ^ (s' + 1)) := by
      rw [hR']
      field_simp
      ring
    have hrpow : Nseq i ^ (μ₀' - μ₀) = Nseq i ^ (-μ₀) / Nseq i ^ (-μ₀') := by
      rw [← Real.rpow_sub hN0]
      congr 1
      ring
    have hRA : R i ω + A i ω * Real.log (Nseq i) ≠ 0 := by
      intro h0
      apply hAR'
      linear_combination h0
    have hden : R i ω * (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ s) +
        A i ω * (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ (s + 1)) ≠ 0 := by
      have e : R i ω * (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ s) +
          A i ω * (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ (s + 1)) =
          Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ s * (R i ω + A i ω * Real.log (Nseq i)) := by
        ring
      rw [e]
      exact mul_ne_zero (mul_ne_zero hPμ hLs) hRA
    have hq : (R' i ω * (Nseq i ^ (-μ₀') * Real.log (Nseq i) ^ s') +
        A' i ω * (Nseq i ^ (-μ₀') * Real.log (Nseq i) ^ (s' + 1))) /
        (R i ω * (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ s) +
          A i ω * (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ (s + 1))) *
        (Nseq i ^ (-μ₀) / Nseq i ^ (-μ₀') * Real.log (Nseq i) ^ (s + 1) /
          Real.log (Nseq i) ^ (s' + 1)) =
        (R' i ω + A' i ω * Real.log (Nseq i)) / (R i ω + A i ω * Real.log (Nseq i)) := by
      rw [div_mul_div_comm, div_eq_div_iff (mul_ne_zero hden (pow_ne_zero _ hL.ne')) hRA]
      field_simp
      ring
    have hRA2 : Real.log (Nseq i) * A i ω + R i ω ≠ 0 := by
      intro h0
      apply hRA
      linear_combination h0
    have hinv : (Real.log (Nseq i) * A i ω + R i ω) * (Real.log (Nseq i) * A i ω + R i ω)⁻¹ = 1 :=
      mul_inv_cancel₀ hRA2
    rw [hZ1, hZφ, hrpow, ← hA, ← hA', hq]
    simp only [secondOrderPair, hV]
    simp
    field_simp
    linear_combination (R' i ω * A i ω + Real.log (Nseq i) * A' i ω * A i ω) * hinv
  calc μ {ω | Real.log (Nseq i) * (Zφ i ω / Z1 i ω *
      (Nseq i ^ (μ₀' - μ₀) * Real.log (Nseq i) ^ (s + 1) / Real.log (Nseq i) ^ (s' + 1)) -
      gCoeff ν h k β b (XY i ω).num μ₀' (s' + 1) / gCoeff ν h k β b (XY i ω).den μ₀ (s + 1)) ≠
      (secondOrderPair (V i ω, (Real.log (Nseq i))⁻¹)).1 /
        (secondOrderPair (V i ω, (Real.log (Nseq i))⁻¹)).2}
      ≤ μ ({ω | |A i ω| ≤ δ} ∪ {ω | |A i ω + R i ω * (Real.log (Nseq i))⁻¹| ≤ δ}) :=
        measure_mono hsub
    _ ≤ μ {ω | |A i ω| ≤ δ} + μ {ω | |A i ω + R i ω * (Real.log (Nseq i))⁻¹| ≤ δ} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) := add_le_add hi1.le hi2.le
    _ = ENNReal.ofReal η := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

end Grammar
