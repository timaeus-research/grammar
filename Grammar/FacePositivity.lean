/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PopulationEnergyAssembled
import Grammar.PopulationPositivity

/-!
# Noncancellation from face witnesses (unit 329; Astra #39 units 7–8)

Global strict positivity of the amplitude is not what the leading coefficient needs: only the
restriction to the principal face matters, and the restriction can vanish identically while the
amplitude is positive elsewhere. This file records the witness form. A face functional is
nonnegative when the amplitude is nonnegative on the (closed) face (`amplitudeCoeff_nonneg`); the
chart face functional `∫_K A(η_v) dν` is nonnegative under the pointwise condition
(`chartFace_nonneg`) and strictly positive as soon as one tangential point has a strictly positive
face functional, for a measure charging open sets (`chartFace_pos`; the integrand is continuous in
`v` by Headline XXXIV). Assembled: if every chart contributing to the global leading pair has a
nonnegative face functional and one of them is positive, `A_* > 0` (`assembledFace_pos`), so the
assembled population integral is asymptotically `A_* N^{-μ_*}(log N)^{m_*−1}` with no further
noncancellation hypothesis (`population_assembled_isEquivalent_of_witness`). Not claimed: that an
arbitrary partition of unity supplies such witnesses (its positive chart may have a different
candidate pair, or all dominant face restrictions may vanish, in which case selection must run
again); compatibility of witness points across charts is external. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Asymptotics

namespace Grammar

/-- **Nonnegativity of the face functional** for an amplitude nonnegative on the closed face. -/
theorem amplitudeCoeff_nonneg {d : ℕ} (h k : Fin (d + 1) → ℕ) (hk : ∀ i, 0 < k i) (l β : ℝ)
    (hl : 0 < l) (hβ : 0 < β) (η : (Fin (d + 1) → ℝ) → ℝ)
    (hnn : ∀ u ∈ closedCube (d + 1), 0 ≤ η (faceProj h k l u)) : 0 ≤ amplitudeCoeff h k l β η := by
  unfold amplitudeCoeff
  refine mul_nonneg (faceLeadConst_pos h k hk l β hl hβ).le ?_
  refine setIntegral_nonneg (measurableSet_unitBox _) fun u hu => ?_
  exact mul_nonneg (hnn u (unitBox_subset_closedCube _ hu)) (residualWeight_nonneg h k l u hu)

variable {M : ℕ} {K : Fin M → Type*} [∀ I, TopologicalSpace (K I)] [∀ I, CompactSpace (K I)]
  [∀ I, T2Space (K I)] [∀ I, MeasurableSpace (K I)] [∀ I, OpensMeasurableSpace (K I)]
  {n : Fin M → ℕ} (ν : (I : Fin M) → Measure (K I)) [∀ I, IsFiniteMeasure (ν I)]
  (h k : (I : Fin M) → Fin (n I + 1) → ℕ) (β : ℝ)

omit [∀ I, CompactSpace (K I)] [∀ I, T2Space (K I)] [∀ I, OpensMeasurableSpace (K I)]
  [∀ I, IsFiniteMeasure (ν I)] in
/-- The chart face functional is nonnegative when every tangential amplitude is nonnegative on the
closed face. -/
theorem chartFace_nonneg (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (x : JointData K n)
    (lam : Fin M → ℝ) (hatt : ∀ I, ∃ i, ratioExp (h I) (k I) i = lam I) (I : Fin M)
    (hnn : ∀ v, ∀ u ∈ closedCube (n I + 1),
      0 ≤ dataAmplitude (x.chart I v) (faceProj (h I) (k I) (lam I) u)) :
    0 ≤ chartFace ν h k β x lam I := by
  unfold chartFace
  have hl : 0 < lam I := by
    obtain ⟨i, hi⟩ := hatt I
    rw [← hi]
    exact ratioExp_pos (h I) (k I) (hk I) i
  exact integral_nonneg fun v => amplitudeCoeff_nonneg (h I) (k I) (hk I) (lam I) β hl hβ _ (hnn v)

/-- **Strict positivity of the chart face functional from one witness**: nonnegative face
restrictions everywhere and a strictly positive face functional at one tangential point, for a
measure charging open sets. -/
theorem chartFace_pos (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (x : JointData K n)
    (hx : ∀ I v, xiCoord (x.chart I v) = 0) (lam : Fin M → ℝ)
    (hmin : ∀ I i, lam I ≤ ratioExp (h I) (k I) i) (hatt : ∀ I, ∃ i, ratioExp (h I) (k I) i = lam I)
    (I : Fin M) [(ν I).IsOpenPosMeasure]
    (hnn : ∀ v, ∀ u ∈ closedCube (n I + 1),
      0 ≤ dataAmplitude (x.chart I v) (faceProj (h I) (k I) (lam I) u))
    (v₀ : K I) (hpos : 0 < amplitudeCoeff (h I) (k I) (lam I) β (dataAmplitude (x.chart I v₀))) :
    0 < chartFace ν h k β x lam I := by
  unfold chartFace
  have hl : 0 < lam I := by
    obtain ⟨i, hi⟩ := hatt I
    rw [← hi]
    exact ratioExp_pos (h I) (k I) (hk I) i
  have hf0 : 0 ≤ fun v => amplitudeCoeff (h I) (k I) (lam I) β (dataAmplitude (x.chart I v)) :=
    fun v => amplitudeCoeff_nonneg (h I) (k I) (hk I) (lam I) β hl hβ _ (hnn v)
  have hint := integrable_tanFace (ν I) (n I) (h I) (k I) (hk I) β hβ (x.chart I) (hx I) (hmin I)
    (hatt I)
  rw [integral_pos_iff_support_of_nonneg hf0 hint]
  have hcont : Continuous fun v =>
      amplitudeCoeff (h I) (k I) (lam I) β (dataAmplitude (x.chart I v)) := by
    have e : (fun v => amplitudeCoeff (h I) (k I) (lam I) β (dataAmplitude (x.chart I v))) =
        fun v => dataBoxCoeff (n I) (h I) (k I) β 1 (x.chart I v) (lam I)
          (multCount (ratioExp (h I) (k I)) (lam I) - 1) := by
      funext v
      exact ((dataBoxCoeff_population_leading (n I) (h I) (k I) (hk I) β hβ (x.chart I v) (hx I v)
        (hmin I) (hatt I)).2).symm
    rw [e]
    exact (continuous_taylorTree_coeff (n I) (h I) (k I) (hk I) β hβ one_pos _ _).comp
      (x.chart I).continuous
  have hopen : IsOpen {v : K I |
      0 < amplitudeCoeff (h I) (k I) (lam I) β (dataAmplitude (x.chart I v))} :=
    isOpen_lt continuous_const hcont
  refine lt_of_lt_of_le (hopen.measure_pos (ν I) ⟨v₀, hpos⟩) (measure_mono fun v hv => ?_)
  exact (show (0 : ℝ) < _ from hv).ne'

omit [∀ I, CompactSpace (K I)] [∀ I, T2Space (K I)] [∀ I, OpensMeasurableSpace (K I)]
  [∀ I, IsFiniteMeasure (ν I)] in
/-- **Assembled noncancellation**: nonnegative face functionals on every chart contributing to the
global leading pair and a positive one on some contributing chart give `A_* > 0`. -/
theorem assembledFace_pos (x : JointData K n) (lam : Fin M → ℝ) (μs : ℝ) (ms : ℕ)
    (hnn : ∀ I, lam I = μs → multCount (ratioExp (h I) (k I)) (lam I) = ms →
      0 ≤ chartFace ν h k β x lam I)
    (hpos : ∃ I, lam I = μs ∧ multCount (ratioExp (h I) (k I)) (lam I) = ms ∧
      0 < chartFace ν h k β x lam I) :
    0 < assembledFace ν h k β x lam μs ms := by
  unfold assembledFace
  refine Finset.sum_pos' (fun I _ => ?_) ?_
  · split_ifs with hI
    · exact hnn I hI.1 hI.2
    · exact le_refl 0
  · obtain ⟨I, h1, h2, h3⟩ := hpos
    exact ⟨I, Finset.mem_univ I, by rw [if_pos ⟨h1, h2⟩]; exact h3⟩

/-- **Unconditional assembled asymptotics from compatible witnesses**: zero-noise joint data whose
amplitudes are nonnegative on the principal faces of the contributing charts, with one contributing
chart carrying a tangential point of strictly positive face functional (and a measure charging open
sets there), have `A_* > 0` and `𝒵_pop ~ A_* N^{-μ_*} (log N)^{m_*−1}`. -/
theorem population_assembled_isEquivalent_of_witness (hk : ∀ I i, 0 < k I i) (hβ : 0 < β)
    (x : JointData K n) (hx : ∀ I v, xiCoord (x.chart I v) = 0) (lam : Fin M → ℝ)
    (hmin : ∀ I i, lam I ≤ ratioExp (h I) (k I) i) (hatt : ∀ I, ∃ i, ratioExp (h I) (k I) i = lam I)
    {μs : ℝ} (hμ : ∀ I, μs ≤ lam I) (hμatt : ∃ I, lam I = μs) {ms : ℕ}
    (hm : ∀ I, lam I = μs → multCount (ratioExp (h I) (k I)) (lam I) ≤ ms)
    (hmatt : ∃ I, lam I = μs ∧ multCount (ratioExp (h I) (k I)) (lam I) = ms) (Zpop E : ℝ → ℝ)
    (hdecomp : ∀ N, Zpop N = gInt ν h k β (fun _ => 1) x N + E N)
    (hE : Tendsto (fun N => E N / (N ^ (-μs) * Real.log N ^ (ms - 1))) atTop (𝓝 0))
    (hnn : ∀ I, lam I = μs → multCount (ratioExp (h I) (k I)) (lam I) = ms →
      ∀ v, ∀ u ∈ closedCube (n I + 1),
        0 ≤ dataAmplitude (x.chart I v) (faceProj (h I) (k I) (lam I) u))
    (I₀ : Fin M) [(ν I₀).IsOpenPosMeasure] (hI₀ : lam I₀ = μs)
    (hmI₀ : multCount (ratioExp (h I₀) (k I₀)) (lam I₀) = ms) (v₀ : K I₀)
    (hpos : 0 < amplitudeCoeff (h I₀) (k I₀) (lam I₀) β (dataAmplitude (x.chart I₀ v₀))) :
    0 < assembledFace ν h k β x lam μs ms ∧
    Zpop ~[atTop] fun N => assembledFace ν h k β x lam μs ms *
      (N ^ (-μs) * Real.log N ^ (ms - 1)) := by
  have hA : 0 < assembledFace ν h k β x lam μs ms :=
    assembledFace_pos ν h k β x lam μs ms
      (fun I h1 h2 => chartFace_nonneg ν h k β hk hβ x lam hatt I (hnn I h1 h2))
      ⟨I₀, hI₀, hmI₀, chartFace_pos ν h k β hk hβ x hx lam hmin hatt I₀ (hnn I₀ hI₀ hmI₀) v₀ hpos⟩
  exact ⟨hA, population_assembled_isEquivalent ν h k β hk hβ x hx lam hmin hatt hμ hμatt hm hmatt
    Zpop E hdecomp hE hA.ne'⟩

end Grammar
