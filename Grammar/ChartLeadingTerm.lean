/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.ChartOrthantTiling
import Grammar.PopulationPositivity
import Grammar.PhasePosterior
import Grammar.PopulationTangential

/-!
# The identified leading term of the local chart theorem (Astra #70, route C)

The local chart theorem (CCIV) produces the full power–log cutoff expansion of `∫_Ω F e^{−NK}` with
the assembled canonical coefficients. Here the **leading term is identified**: with the normal
exponents `h_{n_j}` (Jacobian) and `2k_j` (phase) of the centred chart, the exponent is the minimal
Mellin ratio `λ = min_j (h_{n_j}+1)/(2k_j)` and the log degree is `m − 1` with `m` the number of
minimisers (`minRatio`, `multCount`), and for a positive observable the coefficient is positive
(`chart_local_leading_term`, `IsMonomialChart.local_leading_term`).

The route is the one prescribed in consult #70: the population coefficient theory at box side one
(`dataBoxCoeff_population_leading`) is transported to a general box side `b` through the exact
scaling law of `boxCoeff` (`dataBoxCoeff_population_leading_b`: the coefficient at `(λ, m−1)` is
`b^{Σh+n+1} (b^{2Σk})^{−λ}` times the face functional `amplitudeCoeff` of the datum's amplitude,
and the coefficients at `(λ, j)`, `j > m−1`, vanish); all `2^{n+1}` orthant pieces share the same
exponents, so the assembled coefficient at `(λ, m−1)` is a sum of positive face integrals
(`amplitudeCoeff_pos` on each orthant amplitude `orthantJac · F ∘ Ψ_s > 0`), every preceding
canonical coefficient vanishes, and the first-nonzero theorem of the analytic core decomposition
(`AnalyticCoreDecomposition.first_nonzero`) identifies the asymptotic.

Non-claims: the coefficient is exhibited as the assembled canonical coefficient `gCoeff` and shown
positive; its closed form as a sum of face integrals is `gCoeff_uniform_leading`, not further
simplified; for a signed observable the canonical coefficient at `(λ, m−1)` may vanish and then
`(λ, m)` is only a candidate pair.
-/

open MeasureTheory Set Filter Topology Asymptotics Monomialize.Analytic
  Monomialize.VolumeScaling
open scoped ENNReal NNReal

namespace Grammar

open CoeffFamily

/-! ### The population coefficients at a general box side -/

section BoxSide

variable (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ) (hβ : 0 < β) {b : ℝ}
  (hb : 0 < b) (x : DataSpace (n + 1)) (hx : xiCoord x = 0) {l : ℝ}
  (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)

include hk hβ hb hx hmin hatt in
/-- The box coefficients at `λ` vanish above log degree `m − 1`, at every box side. -/
theorem dataBoxCoeff_population_gt {j : ℕ} (hj : multCount (ratioExp h k) l - 1 < j) :
    dataBoxCoeff n h k β b x l j = 0 := by
  unfold dataBoxCoeff boxCoeff
  rw [scale_toXi hb.ne', scale_toEta hb.ne', hx]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun q hq => ?_)
  have hq' := Finset.mem_Ico.1 hq
  rw [← dataBoxCoeff_population n h k β x hx l (by omega),
    (dataBoxCoeff_population_leading n h k hk β hβ x hx hmin hatt).1 q (by omega), zero_mul,
    zero_mul]

include hk hβ hb hx hmin hatt in
/-- **The box coefficient at `(λ, m − 1)` at a general box side** is the scaling factor
`b^{Σh+n+1} (b^{2Σk})^{−λ}` times the face functional of the datum's amplitude. -/
theorem dataBoxCoeff_population_leading_b :
    dataBoxCoeff n h k β b x l (multCount (ratioExp h k) l - 1) =
      b ^ (∑ i, h i + (n + 1)) * (b ^ (2 * ∑ i, k i)) ^ (-l) *
        amplitudeCoeff h k l β (dataAmplitude x) := by
  unfold dataBoxCoeff boxCoeff
  rw [scale_toXi hb.ne', scale_toEta hb.ne', hx]
  have hm : multCount (ratioExp h k) l - 1 < n + 1 := by
    have := multCount_le_card (ratioExp h k) l
    omega
  rw [Finset.sum_eq_single (multCount (ratioExp h k) l - 1)]
  · rw [Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, mul_one, mul_one,
      ← dataBoxCoeff_population n h k β x hx l (by omega),
      (dataBoxCoeff_population_leading n h k hk β hβ x hx hmin hatt).2]
  · intro q hq hne
    have hq' := Finset.mem_Ico.1 hq
    rw [← dataBoxCoeff_population n h k β x hx l (by omega),
      (dataBoxCoeff_population_leading n h k hk β hβ x hx hmin hatt).1 q
        (lt_of_le_of_ne hq'.1 (Ne.symm hne)), zero_mul, zero_mul]
  · intro hnot
    exact absurd (Finset.mem_Ico.2 ⟨le_rfl, hm⟩) hnot

end BoxSide

section Tangential

variable {K : Type*} [TopologicalSpace K] [MeasurableSpace K] (ν : Measure K)
  (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ) (hβ : 0 < β) {b : ℝ}
  (hb : 0 < b) (x : TangentialData K (n + 1)) (hx : ∀ v, xiCoord (x v) = 0) {l : ℝ}
  (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)

include hk hβ hb hx hmin hatt in
theorem tanCoeff_population_gt {j : ℕ} (hj : multCount (ratioExp h k) l - 1 < j) :
    tanCoeff ν n h k β b x l j = 0 := by
  unfold tanCoeff
  simp [fun v => dataBoxCoeff_population_gt n h k hk β hβ hb (x v) (hx v) hmin hatt hj]

include hk hβ hb hx hmin hatt in
/-- The integrated coefficient at `(λ, m − 1)` at a general box side. -/
theorem tanCoeff_population_leading_b :
    tanCoeff ν n h k β b x l (multCount (ratioExp h k) l - 1) =
      b ^ (∑ i, h i + (n + 1)) * (b ^ (2 * ∑ i, k i)) ^ (-l) *
        ∫ v, amplitudeCoeff h k l β (dataAmplitude (x v)) ∂ν := by
  unfold tanCoeff
  rw [← integral_const_mul]
  congr 1
  funext v
  exact dataBoxCoeff_population_leading_b n h k hk β hβ hb (x v) (hx v) hmin hatt

end Tangential

/-! ### The first nonzero coefficient of a uniform analytic core decomposition -/

section Uniform

variable {U : Type*} [MeasurableSpace U] {D : LocalisationData U} {M : ℕ} {K : Fin M → Type*}
  [∀ I, TopologicalSpace (K I)] [∀ I, MeasurableSpace (K I)] {n : Fin M → ℕ} {β : ℝ}
  (A : AnalyticCoreDecomposition D M K n β) (hβ : 0 < β) {l : ℝ} {m : ℕ}
  (hmin : ∀ I i, l ≤ ratioExp (A.h I) (A.k I) i) (hatt : ∀ I, ∃ i, ratioExp (A.h I) (A.k I) i = l)
  (hm : ∀ I, multCount (ratioExp (A.h I) (A.k I)) l = m)

include hβ hmin in
/-- The assembled coefficients vanish below the common minimal ratio. -/
theorem gCoeff_uniform_eq_zero_of_lt {μ : ℝ} (hμ : μ < l) (j : ℕ) :
    gCoeff A.ν A.h A.k β A.b A.x μ j = 0 := by
  unfold gCoeff
  exact Finset.sum_eq_zero fun I _ =>
    tanCoeff_eq_zero_of_lt_min (A.ν I) (n I) (A.h I) (A.k I) (A.k_pos I) β hβ (A.b_pos I) (A.x I)
      (hmin I) hμ j

include hβ hmin hatt hm in
/-- The assembled coefficients at `λ` vanish above log degree `m − 1`. -/
theorem gCoeff_uniform_eq_zero_of_gt {j : ℕ} (hj : m - 1 < j) :
    gCoeff A.ν A.h A.k β A.b A.x l j = 0 := by
  unfold gCoeff
  refine Finset.sum_eq_zero fun I _ => ?_
  have hx : ∀ v, xiCoord (A.x I v) = 0 := (A.chart I).fluct_zero
  exact tanCoeff_population_gt (A.ν I) (n I) (A.h I) (A.k I) (A.k_pos I) β hβ (A.b_pos I) (A.x I)
    hx (hmin I) (hatt I) (by rw [hm I]; exact hj)

include hβ hmin hatt hm in
/-- **The assembled coefficient at `(λ, m − 1)`** is the sum over the pieces of the scaled face
integrals. -/
theorem gCoeff_uniform_leading :
    gCoeff A.ν A.h A.k β A.b A.x l (m - 1) =
      ∑ I, A.b I ^ (∑ i, A.h I i + (n I + 1)) * (A.b I ^ (2 * ∑ i, A.k I i)) ^ (-l) *
        ∫ v, amplitudeCoeff (A.h I) (A.k I) l β (dataAmplitude (A.x I v)) ∂(A.ν I) := by
  unfold gCoeff
  refine Finset.sum_congr rfl fun I _ => ?_
  have hx : ∀ v, xiCoord (A.x I v) = 0 := (A.chart I).fluct_zero
  rw [← hm I]
  exact tanCoeff_population_leading_b (A.ν I) (n I) (A.h I) (A.k I) (A.k_pos I) β hβ (A.b_pos I)
    (A.x I) hx (hmin I) (hatt I)

variable [∀ I, CompactSpace (K I)] [∀ I, T2Space (K I)] [∀ I, OpensMeasurableSpace (K I)]

include hβ hmin hatt hm in
/-- **The identified asymptotic of a uniform analytic core decomposition**: if the assembled
coefficient at `(λ, m − 1)` is nonzero, `Z(N) ~ gCoeff_{λ,m−1} N^{−λ} (log N)^{m−1}`. -/
theorem AnalyticCoreDecomposition.isEquivalent_uniform
    (hne : gCoeff A.ν A.h A.k β A.b A.x l (m - 1) ≠ 0) :
    D.Z ~[atTop] fun N => gCoeff A.ν A.h A.k β A.b A.x l (m - 1) *
      (N ^ (-l) * Real.log N ^ (m - 1)) := by
  classical
  -- a piece exists
  have hM : 0 < M := by
    by_contra hM
    apply hne
    unfold gCoeff
    exact Finset.sum_eq_zero fun I _ => absurd I.2 (by omega)
  set I₀ : Fin M := ⟨0, hM⟩ with hI₀
  -- `λ` lies in the common lattice
  have hQ : 0 < commonQ A.k := commonQ_pos A.k A.k_pos
  have hlat : ∃ m' : ℕ, l = (m' : ℝ) / commonQ A.k := by
    obtain ⟨i, hi⟩ := hatt I₀
    obtain ⟨m', -, hm'⟩ := ratio_mem_lattice (A.k I₀) (A.k_pos I₀) i (A.h I₀ i)
    obtain ⟨c, hc⟩ := latticeQ_dvd_commonQ (k := A.k) I₀
    have hQI : (0 : ℝ) < latticeQ (A.k I₀) := by exact_mod_cast latticeQ_pos _ (A.k_pos I₀)
    have hc0 : (0 : ℝ) < c := by
      have : (0 : ℝ) < commonQ A.k := by exact_mod_cast hQ
      rw [hc, Nat.cast_mul] at this
      exact pos_of_mul_pos_right this hQI.le
    refine ⟨m' * c, ?_⟩
    rw [← hi, hc]
    unfold ratioExp
    rw [hm', Nat.cast_mul, Nat.cast_mul]
    field_simp
  have hmn : m - 1 ≤ commonD n := by
    have h1 := multCount_le_card (ratioExp (A.h I₀) (A.k I₀)) l
    rw [hm I₀] at h1
    have h2 := le_commonD (n := n) I₀
    omega
  -- the target pair is admissible and first
  have hadm : ((l, m - 1) : ℝ × ℕ) ∈ admissible (commonD n) (commonQ A.k) := ⟨hlat, hmn⟩
  have hfirst : ∀ q ∈ admissible (commonD n) (commonQ A.k), precedes q (l, m - 1) →
      gCoeff A.ν A.h A.k β A.b A.x q.1 q.2 = 0 := by
    intro q _ hq
    rcases hq with hlt | ⟨heq, hgt⟩
    · exact gCoeff_uniform_eq_zero_of_lt A hβ hmin hlt q.2
    · have heq' : q.1 = l := heq
      rw [heq']
      exact gCoeff_uniform_eq_zero_of_gt A hβ hmin hatt hm hgt
  have hne' : ∃ p ∈ indexSet (commonD n) (commonQ A.k) (l + 1),
      gCoeff A.ν A.h A.k β A.b A.x p.1 p.2 ≠ 0 := by
    refine ⟨(l, m - 1), ?_, hne⟩
    unfold indexSet
    rw [Finset.mem_product]
    refine ⟨?_, Finset.mem_range.2 (by omega)⟩
    obtain ⟨m', hm'⟩ := hlat
    rw [hm']
    exact mem_latticeBelow hQ (by rw [← hm']; linarith)
  obtain ⟨p, ⟨hpadm, hpne, hpfirst, hequiv⟩, -⟩ := A.first_nonzero hβ hne'
  have hp : p = (l, m - 1) :=
    first_nonzero_unique (gCoeff A.ν A.h A.k β A.b A.x) hpadm hpne hpfirst hadm hne hfirst
  rw [hp] at hequiv
  exact hequiv

end Uniform

/-! ### The identified leading term at a divisor point -/

variable {d : ℕ} {K : (Fin d → ℝ) → ℝ} {φ : (Fin d → ℝ) → (Fin d → ℝ)} {h : Fin d →₀ ℕ}
  {y₀ : Fin d → ℝ} (C : CentredChartData K φ h y₀) {β : ℝ} {j₀ : Fin (C.n + 1)}
  {A : Set (Fin C.t → ℝ)} {b₁ : ℝ}
  (SD : StripData (nIdx C.σ j₀) C.V₀ (unitRoot β (2 * C.k j₀) C.unit₀) (stripBase C.σ A j₀ b₁))

/-- The normal Jacobian exponents of the centred chart. -/
def CentredChartData.hN : Fin (C.n + 1) → ℕ := fun j => h (nIdx C.σ j)

/-- The exponent of the centred chart: the minimal Mellin ratio `min_j (h_{n_j}+1)/(2k_j)`. -/
noncomputable def CentredChartData.lam : ℝ := minRatio C.hN C.k

/-- The multiplicity of the centred chart: the number of minimisers. -/
noncomputable def CentredChartData.mult : ℕ := multCount (ratioExp C.hN C.k) C.lam

theorem CentredChartData.lam_le (j : Fin (C.n + 1)) : C.lam ≤ ratioExp C.hN C.k j :=
  minRatio_le _ _ j

theorem CentredChartData.exists_ratioExp_eq_lam : ∃ j, ratioExp C.hN C.k j = C.lam :=
  exists_ratioExp_eq_minRatio _ _

theorem CentredChartData.lam_pos : 0 < C.lam := minRatio_pos _ _ C.k_pos

/-- The orthant chart maps the closed strip box into the local region. -/
theorem orthantChart_mem_localRegion (s : Fin (C.n + 1) → Bool) {A' : Set (Fin C.t → ℝ)} {b' : ℝ}
    {v : Fin C.t → ℝ} (hv : v ∈ A') {u : Fin (C.n + 1) → ℝ} (hu : ∀ j, |u j| ≤ b') :
    orthantChart C SD s (prodToPi C.σ (v, u)) ∈ localRegion C SD A' b' := by
  rw [orthantChart_eq, Function.comp_apply, splitReflect_prodToPi]
  refine ⟨_, ⟨reflectChart s (v, u), ⟨hv, fun j _ => ?_⟩, rfl⟩, rfl⟩
  rw [reflectChart_apply]
  simp only [reflectEquiv_apply]
  rw [mem_Icc, ← abs_le, abs_mul, abs_boolSgn, one_mul]
  exact hu j

/-- The orthant amplitude is positive on the closed strip box when `F > 0` on the local region. -/
theorem orthantAmp_pos (hβ : 0 < β) {F : (Fin d → ℝ) → ℝ} (s : Fin (C.n + 1) → Bool)
    {A' : Set (Fin C.t → ℝ)} (hA'A : A' ⊆ A) {b' : ℝ} (hb'b₁ : b' ≤ b₁) (hb'SD : b' ≤ SD.b)
    (hF : ∀ x ∈ localRegion C SD A' b', 0 < F x) {v : Fin C.t → ℝ} (hv : v ∈ A')
    {u : Fin (C.n + 1) → ℝ} (hu : ∀ j, |u j| ≤ b') : 0 < orthantAmp C SD s F (v, u) := by
  have hdom : prodToPi C.σ (v, u) ∈ orthantDomain C SD s := by
    rw [mem_orthantDomain_iff', splitReflect_prodToPi]
    refine zBox_subset_stripImage C SD hA'A hb'b₁ hb'SD ⟨reflectChart s (v, u), ⟨hv, fun j _ => ?_⟩,
      rfl⟩
    rw [reflectChart_apply]
    simp only [reflectEquiv_apply]
    rw [mem_Icc, ← abs_le, abs_mul, abs_boolSgn, one_mul]
    exact hu j
  unfold orthantAmp
  rw [orthantJac_eq C SD s hdom]
  exact mul_pos (orthantJacFun_pos C SD hβ s hdom)
    (hF _ (orthantChart_mem_localRegion C SD s hv hu))

/-- **The face integral of the orthant chart `s`**: the tangential integral over `A'` of the face
constant times the integral over the unit box of the orthant amplitude at the scaled face point,
against the residual weight on the nonminimising normal coordinates. -/
noncomputable def orthantFaceIntegral (s : Fin (C.n + 1) → Bool) (F : (Fin d → ℝ) → ℝ)
    (A' : Set (Fin C.t → ℝ)) (b' : ℝ) : ℝ :=
  ∫ v in A', faceLeadConst C.hN C.k C.lam β * ∫ u in unitBox (C.n + 1),
    orthantAmp C SD s F (v, b' • faceProj C.hN C.k C.lam u) * residualWeight C.hN C.k C.lam u

/-- **The local leading coefficient**: the sum over the `2^{n+1}` orthants of the box-side scaling
factor times the orthant face integral. -/
noncomputable def localLeadingCoeff (F : (Fin d → ℝ) → ℝ) (A' : Set (Fin C.t → ℝ)) (b' : ℝ) :
    ℝ :=
  ∑ s : Fin (C.n + 1) → Bool, b' ^ (∑ j, C.hN j + (C.n + 1)) * (b' ^ (2 * ∑ j, C.k j)) ^ (-C.lam) *
    orthantFaceIntegral C SD s F A' b'

/-- **The identified leading term of the local chart theorem.** Under the hypotheses of the local
chart theorem, with `F > 0` on an open `U' ∋ φ y₀` and a tangential base of positive volume near
the origin, the region `Ω` can be taken inside `U'` and
`∫_Ω F e^{−NK} ~ c · N^{−λ} (log N)^{m−1}` with `c > 0`, `λ = min_j (h_{n_j}+1)/(2k_j)` and `m` the
number of minimisers. -/
theorem chart_local_leading_term (hβ : 0 < β) (hφ : ∀ y ∈ C.V₀, AnalyticAt ℝ φ (y + y₀))
    (hinj : ∀ w₁ ∈ C.V₀, ∀ w₂ ∈ C.V₀, monomialEval (w₁ + y₀) h ≠ 0 →
      monomialEval (w₂ + y₀) h ≠ 0 → φ (w₁ + y₀) = φ (w₂ + y₀) → w₁ = w₂)
    (hKm : Measurable K) (hK0 : ∀ w ∈ C.V₀, 0 ≤ K (translated φ y₀ w)) {F : (Fin d → ℝ) → ℝ}
    (hF : ∀ w ∈ C.V₀, AnalyticAt ℝ F (translated φ y₀ w)) (hA : IsCompact A)
    (h0 : (0 : Fin C.t → ℝ) ∈ A) (hAvol : ∀ r : ℝ, 0 < r → 0 < volume (A ∩ Metric.closedBall 0 r))
    (hb₁ : 0 < b₁) {U' : Set (Fin d → ℝ)} (hU' : IsOpen U') (hy₀U' : φ y₀ ∈ U')
    (hFU' : ∀ x ∈ U', 0 < F x) :
    ∃ (B b' : ℝ), 0 < B ∧ 0 < b' ∧ b' ≤ b₁ ∧ b' ≤ SD.b ∧
      IsCompact (localRegion C SD (A ∩ Metric.closedBall 0 B) b') ∧
      φ y₀ ∈ localRegion C SD (A ∩ Metric.closedBall 0 B) b' ∧
      localRegion C SD (A ∩ Metric.closedBall 0 B) b' ⊆ translated φ y₀ '' C.V₀ ∧
      localRegion C SD (A ∩ Metric.closedBall 0 B) b' ⊆ U' ∧
      0 < localLeadingCoeff C SD F (A ∩ Metric.closedBall 0 B) b' ∧
        (fun N => ∫ x in localRegion C SD (A ∩ Metric.closedBall 0 B) b',
          F x * Real.exp (-N * K x)) ~[atTop]
        fun N => localLeadingCoeff C SD F (A ∩ Metric.closedBall 0 B) b' *
          (N ^ (-C.lam) * Real.log N ^ (C.mult - 1)) := by
  classical
  obtain ⟨B, b', hB, hb', hb'b₁, hb'SD, hΩc, hmem, hsub, hΩU', hX⟩ :=
    exists_orthantSplitBoxCharts C SD hβ hφ hinj hF hA h0 hb₁ hU' hy₀U'
  set A' := A ∩ Metric.closedBall (0 : Fin C.t → ℝ) B with hA'
  have hA'c : IsCompact A' := hA.inter_right Metric.isClosed_closedBall
  have hA'A : A' ⊆ A := inter_subset_left
  set Ω := localRegion C SD A' b' with hΩ
  have hΩm : MeasurableSet Ω := hΩc.isClosed.measurableSet
  have hΩmem : ∀ x ∈ Ω, ∃ w ∈ C.V₀, x = translated φ y₀ w := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := hsub hx
    exact ⟨w, hw, rfl⟩
  have hFc : ContinuousOn F Ω := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := hΩmem x hx
    exact (hF w hw).continuousAt.continuousWithinAt
  let D : LocalisationData (Fin d → ℝ) :=
    ⟨volume.restrict Ω, K, F, hKm,
      ae_restrict_of_forall_mem hΩm fun x hx => by
        obtain ⟨w, hw, rfl⟩ := hΩmem x hx
        exact hK0 w hw,
      hFc.integrableOn_compact hΩc, 1, one_pos⟩
  obtain ⟨X, hX⟩ := hX D (fun _ _ => rfl) (fun _ _ => rfl)
  set T := orthantCoreTiling C SD hinj hφ (D := D) rfl hA'c hA'A hb' hb'b₁ hb'SD X
    (fun s => (hX s).1) with hT
  set Ad := T.toAnalyticCoreDecomposition with hAd
  -- the pieces are uniform
  have hAh : ∀ I, Ad.h I = C.hN := fun I => (hX _).2.1
  have hAk : ∀ I, Ad.k I = C.k := fun I => (hX _).2.2.1
  have hAb : ∀ I, Ad.b I = b' := fun _ => rfl
  have hmin : ∀ I i, C.lam ≤ ratioExp (Ad.h I) (Ad.k I) i := fun I i => by
    rw [hAh, hAk]
    exact C.lam_le i
  have hatt : ∀ I, ∃ i, ratioExp (Ad.h I) (Ad.k I) i = C.lam := fun I => by
    rw [hAh, hAk]
    exact C.exists_ratioExp_eq_lam
  have hm : ∀ I, multCount (ratioExp (Ad.h I) (Ad.k I)) C.lam = C.mult := fun I => by
    rw [hAh, hAk]
    rfl
  -- the amplitude of a piece is the orthant amplitude on the closed box
  have hamp : ∀ (s : Fin (C.n + 1) → Bool) (v : A'), ∀ w ∈ closedCube (C.n + 1),
      dataAmplitude ((X s).amp v) w = orthantAmp C SD s F (v.1, b' • w) := by
    intro s v w hw
    rw [dataAmplitude_eq_of_mem _ hw, ← scale_toEta hb'.ne', evalF_scale]
    refine (hX s).2.2.2.2 v (b' • w) fun j => ?_
    rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hb']
    have := hw j (mem_univ j)
    rw [mem_Icc] at this
    rw [abs_of_nonneg this.1]
    exact mul_le_of_le_one_right hb'.le this.2
  -- the assembled coefficient is the local leading coefficient
  have hgeq : gCoeff Ad.ν Ad.h Ad.k β Ad.b Ad.x C.lam (C.mult - 1) =
      localLeadingCoeff C SD F A' b' := by
    rw [gCoeff_uniform_leading Ad hβ hmin hatt hm]
    unfold localLeadingCoeff
    rw [← Equiv.sum_comp (signIdx C).symm]
    refine Finset.sum_congr rfl fun I _ => ?_
    set s := (signIdx C).symm I with hs
    change b' ^ (∑ i, (X s).h i + (C.n + 1)) * (b' ^ (2 * ∑ i, (X s).k i)) ^ (-C.lam) *
      ∫ v : A', amplitudeCoeff (X s).h (X s).k C.lam β (dataAmplitude ((X s).amp v))
        ∂(Measure.comap Subtype.val volume) = _
    have hh : (X s).h = C.hN := (hX s).2.1
    rw [hh, (hX s).2.2.1]
    have hpt : ∀ v : A', amplitudeCoeff C.hN C.k C.lam β (dataAmplitude ((X s).amp v)) =
        faceLeadConst C.hN C.k C.lam β * ∫ u in unitBox (C.n + 1),
          orthantAmp C SD s F (v.1, b' • faceProj C.hN C.k C.lam u) *
            residualWeight C.hN C.k C.lam u := by
      intro v
      unfold amplitudeCoeff
      congr 1
      refine setIntegral_congr_fun (measurableSet_unitBox _) fun u hu => ?_
      rw [hamp s v _ (faceProj_mapsTo _ _ _ hu)]
    have hint : (∫ v : A', amplitudeCoeff C.hN C.k C.lam β (dataAmplitude ((X s).amp v))
        ∂(Measure.comap Subtype.val volume)) = orthantFaceIntegral C SD s F A' b' := by
      unfold orthantFaceIntegral
      rw [← integral_subtype_comap hA'c.isClosed.measurableSet]
      exact integral_congr_ae (Eventually.of_forall fun v => hpt v)
    rw [hint]
  -- positivity of the assembled leading coefficient
  have hFΩ : ∀ x ∈ Ω, 0 < F x := fun x hx => hFU' x (hΩU' hx)
  have hν : ∀ I, Ad.ν I ≠ 0 := by
    intro I
    rw [← Measure.measure_univ_ne_zero]
    change Measure.comap (Subtype.val : A' → Fin C.t → ℝ) volume univ ≠ 0
    rw [(MeasurableEmbedding.subtype_coe hA'c.isClosed.measurableSet).comap_apply, image_univ,
      Subtype.range_coe]
    exact (hAvol B hB).ne'
  have hpos : ∀ I, 0 < Ad.b I ^ (∑ i, Ad.h I i + (C.n + 1)) *
      (Ad.b I ^ (2 * ∑ i, Ad.k I i)) ^ (-C.lam) *
      ∫ v, amplitudeCoeff (Ad.h I) (Ad.k I) C.lam β (dataAmplitude (Ad.x I v)) ∂(Ad.ν I) := by
    intro I
    have hb'I : 0 < Ad.b I := by rw [hAb]; exact hb'
    refine mul_pos (mul_pos (pow_pos hb'I _) (Real.rpow_pos_of_pos (pow_pos hb'I _) _)) ?_
    have hx : ∀ v, xiCoord (Ad.x I v) = 0 := (Ad.chart I).fluct_zero
    refine tanCoeff_population_pos (Ad.ν I) C.n (Ad.h I) (Ad.k I) (Ad.k_pos I) β hβ (Ad.x I) hx
      (hmin I) (hatt I) ?_ (hν I)
    intro v
    -- the amplitude of the piece is positive on the closed box
    set s := (signIdx C).symm I with hs
    have hampos : ∀ w ∈ closedCube (C.n + 1), 0 < dataAmplitude ((X s).amp v) w := by
      intro w hw
      rw [hamp s v w hw]
      refine orthantAmp_pos C SD hβ s hA'A hb'b₁ hb'SD hFΩ v.2 fun j => ?_
      rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hb']
      have := hw j (mem_univ j)
      rw [mem_Icc] at this
      rw [abs_of_nonneg this.1]
      exact mul_le_of_le_one_right hb'.le this.2
    have h0c : (0 : Fin (C.n + 1) → ℝ) ∈ closedCube (C.n + 1) := fun j _ => by
      simp
    have hmin' : ∀ i, C.lam ≤ ratioExp (X s).h (X s).k i := by
      rw [(hX s).2.1, (hX s).2.2.1]
      exact C.lam_le
    change 0 < amplitudeCoeff (X s).h (X s).k C.lam β (dataAmplitude ((X s).amp v))
    refine amplitudeCoeff_pos C.n (X s).h (X s).k (X s).k_pos C.lam β C.lam_pos hβ hmin' _
      (continuous_dataAmplitude _) (fun u hu => (hampos _ (faceProj_mem_closedCube _ _ _ hu)).le)
      0 h0c (hampos _ (faceProj_mem_closedCube _ _ _ h0c))
  have hgpos : 0 < gCoeff Ad.ν Ad.h Ad.k β Ad.b Ad.x C.lam (C.mult - 1) := by
    rw [gCoeff_uniform_leading Ad hβ hmin hatt hm]
    exact Finset.sum_pos (fun I _ => hpos I) ⟨(signIdx C) (fun _ => true), Finset.mem_univ _⟩
  refine ⟨B, b', hB, hb', hb'b₁, hb'SD, hΩc, hmem, hsub, hΩU', hgeq ▸ hgpos, ?_⟩
  rw [← hgeq]
  exact Ad.isEquivalent_uniform hβ hmin hatt hm hgpos.ne'

/-- **The identified leading term at a divisor point of a hironaka chart.** Under the hypotheses of
`IsMonomialChart.local_cutoffExpansion` with `F (φ y₀) > 0`: for the centred chart data `C` at
`y₀`, some compact region `Ω ∋ φ y₀` inside `φ(W) ∩ U` has
`∫_Ω F e^{−NK} ~ c · N^{−λ} (log N)^{m−1}` with `c > 0`, `λ = min_j (h_{n_j}+1)/(2k_j)` the minimal
Mellin ratio of the chart's normal exponents and `m` the number of minimisers. -/
theorem IsMonomialChart.local_leading_term {dom : Set (Fin d → ℝ)} {e : Fin d →₀ ℕ}
    {W : Set (Fin d → ℝ)} (hc : IsMonomialChart K φ dom e h W) {U : Set (Fin d → ℝ)}
    (hU : IsOpen U) (hK : AnalyticOnNhd ℝ K U) (hK0 : ∀ x ∈ U, 0 ≤ K x) (hKm : Measurable K)
    (hhe : ∀ j, 0 < h j → 0 < e j) (hy₀W : y₀ ∈ W) (hy₀U : φ y₀ ∈ U) (hKy₀ : K (φ y₀) = 0)
    {F : (Fin d → ℝ) → ℝ} (hF : AnalyticOnNhd ℝ F U) (hFpos : 0 < F (φ y₀)) :
    ∃ C : CentredChartData K φ h y₀, ∃ Ω : Set (Fin d → ℝ), IsCompact Ω ∧ φ y₀ ∈ Ω ∧
      Ω ⊆ φ '' W ∧ Ω ⊆ U ∧ (∃ V : Set (Fin d → ℝ), IsOpen V ∧ y₀ ∈ V ∧ ∀ y ∈ V, φ y ∈ Ω) ∧
      ∃ c : ℝ, 0 < c ∧
        (fun N => ∫ x in Ω, F x * Real.exp (-N * K x)) ~[atTop]
          fun N => c * (N ^ (-C.lam) * Real.log N ^ (C.mult - 1)) := by
  obtain ⟨C, hC⟩ := exists_centredChartData hc hU hK hK0 hhe hy₀W hy₀U hKy₀
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 C.V₀_open 0 C.zero_mem
  set ε' := ε / 2 with hε'
  have hε'pos : 0 < ε' := half_pos hε
  have hcball : Metric.closedBall (0 : Fin d → ℝ) ε' ⊆ C.V₀ :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball
  set j₀ : Fin (C.n + 1) := 0 with hj₀
  set A : Set (Fin C.t → ℝ) := Metric.closedBall 0 ε' with hA
  have hρ : AnalyticOnNhd ℝ (unitRoot 1 (2 * C.k j₀) C.unit₀) C.V₀ := fun w hw =>
    analyticAt_unitRoot one_pos (by have := C.k_pos j₀; omega) (C.unit₀_analytic w hw)
      (C.unit₀_pos w hw)
  have hQ₀ : IsCompact (stripBase C.σ A j₀ ε') :=
    isCompact_stripBase (isCompact_closedBall _ _) j₀ ε'
  have hQ₀V : stripBase C.σ A j₀ ε' ⊆ C.V₀ :=
    (stripBase_subset_closedBall C.σ j₀ hε'pos.le).trans hcball
  obtain ⟨SD⟩ := exists_stripData C.V₀_open hρ (fun w _ => unitRoot_pos _ _ _ _) hQ₀ hQ₀V
    fun y hy => stripBase_apply_nIdx hy
  have hφ : ∀ y ∈ C.V₀, AnalyticAt ℝ φ (y + y₀) := fun y hy => hc.analyticOnNhd _ (hC y hy).1
  have hinj : ∀ w₁ ∈ C.V₀, ∀ w₂ ∈ C.V₀, monomialEval (w₁ + y₀) h ≠ 0 →
      monomialEval (w₂ + y₀) h ≠ 0 → φ (w₁ + y₀) = φ (w₂ + y₀) → w₁ = w₂ := by
    intro w₁ hw₁ w₂ hw₂ hm₁ hm₂ heq
    have := hc.injOn ⟨(hC w₁ hw₁).1, hm₁⟩ ⟨(hC w₂ hw₂).1, hm₂⟩ heq
    exact add_right_cancel this
  -- the positive set of `F`
  have hU'o : IsOpen (U ∩ F ⁻¹' Ioi 0) := hF.continuousOn.isOpen_inter_preimage hU isOpen_Ioi
  have hAvol : ∀ r : ℝ, 0 < r → 0 < volume (A ∩ Metric.closedBall (0 : Fin C.t → ℝ) r) := by
    intro r hr
    refine lt_of_lt_of_le
      (Metric.measure_closedBall_pos (volume : Measure (Fin C.t → ℝ)) 0 (lt_min hε'pos hr)) ?_
    refine measure_mono fun v hv => ⟨?_, ?_⟩
    · exact Metric.closedBall_subset_closedBall (min_le_left _ _) hv
    · exact Metric.closedBall_subset_closedBall (min_le_right _ _) hv
  obtain ⟨B, b', hB, hb', hb'b₁, hb'SD, hΩc, hmem, hsub, -, hc0, hequiv⟩ :=
    chart_local_leading_term C SD one_pos hφ hinj hKm (fun w hw => hK0 _ (hC w hw).2)
      (fun w hw => hF _ (hC w hw).2) (isCompact_closedBall _ _) (by simp [hA, hε'pos.le]) hAvol
      hε'pos hU'o ⟨hy₀U, hFpos⟩ (fun x hx => hx.2)
  have hrA : Metric.ball (0 : Fin C.t → ℝ) (min ε' B) ⊆ A ∩ Metric.closedBall 0 B := by
    intro v hv
    exact ⟨Metric.ball_subset_closedBall (Metric.ball_subset_ball (min_le_left _ _) hv),
      Metric.ball_subset_closedBall (Metric.ball_subset_ball (min_le_right _ _) hv)⟩
  refine ⟨C, _, hΩc, hmem, ?_, ?_, exists_isOpen_subset_localRegion C SD one_pos
    (lt_min hε'pos hB) hrA inter_subset_left hb' hb'b₁ hb'SD (by simp [hA, hε'pos.le]) hε'pos.le,
    _, hc0, hequiv⟩
  · intro x hx
    obtain ⟨w, hw, rfl⟩ := hsub hx
    exact ⟨w + y₀, (hC w hw).1, rfl⟩
  · intro x hx
    obtain ⟨w, hw, rfl⟩ := hsub hx
    exact (hC w hw).2

end Grammar
