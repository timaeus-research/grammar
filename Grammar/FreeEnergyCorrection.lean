/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.SecondOrderAssembled

/-!
# The population free energy with its first inverse-log correction (unit 325)

From two-term data `log N (Z/(N^{-λ}L^s) − A) → B` with `A > 0` (`L = log N`):
```
−log Z = λ log N − s log log N − log A − (B/A)/log N + o(1/log N)
```
(`neg_log_twoTerm`, stated as `log N · (−log Z − (λ log N − s log log N − log A)) → −B/A`, with
eventual positivity of `Z`). Instantiated for the population chart integral of an analytic
amplitude (`population_free_energy_chart`, `s = m − 1`, `A` the face functional, `B = secondCoeff`)
and for the assembled population integral (`population_free_energy_assembled`). The proof is the
logarithm of the two-term expansion with `|log(1+x) − x| ≤ x²/(1+x)`; nothing is differentiated or
integrated in `β`,
and no moving-temperature (WBIC) regime is claimed. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

/-- `|log(1+x) − x| ≤ x²/(1+x)` for `x > −1`. -/
theorem abs_log_one_add_sub_le {x : ℝ} (hx : -1 < x) :
    |Real.log (1 + x) - x| ≤ x ^ 2 / (1 + x) := by
  have h1 : 0 < 1 + x := by linarith
  have hu : Real.log (1 + x) ≤ x := by
    have := Real.log_le_sub_one_of_pos h1
    linarith
  have hl : x - x ^ 2 / (1 + x) ≤ Real.log (1 + x) := by
    have := Real.log_le_sub_one_of_pos (inv_pos.2 h1)
    rw [Real.log_inv] at this
    have e : 1 - (1 + x)⁻¹ = x - x ^ 2 / (1 + x) := by
      field_simp
      ring
    linarith
  rw [abs_le]
  constructor <;> linarith

/-- **Free energy from two-term data**: `Z = N^{-λ} L^s (A + B/L + o(1/L))` with `A > 0` gives
eventual positivity and `log N · (−log Z − (λ log N − s log log N − log A)) → −B/A`. -/
theorem neg_log_twoTerm {Z : ℝ → ℝ} {A B l : ℝ} {s : ℕ} (hA : 0 < A)
    (hZ : Tendsto (fun N => Real.log N * (Z N / (N ^ (-l) * Real.log N ^ s) - A)) atTop (𝓝 B)) :
    (∀ᶠ N in atTop, 0 < Z N) ∧
    Tendsto (fun N => Real.log N * (-Real.log (Z N) -
      (l * Real.log N - s * Real.log (Real.log N) - Real.log A))) atTop (𝓝 (-B / A)) := by
  -- ε → 0
  have hε : Tendsto (fun N => Z N / (N ^ (-l) * Real.log N ^ s) - A) atTop (𝓝 0) := by
    have := hZ.mul tendsto_inv_log
    rw [mul_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    have hlog : Real.log N ≠ 0 := (Real.log_pos hN).ne'
    rw [mul_comm, ← mul_assoc, inv_mul_cancel₀ hlog, one_mul]
  have hev : ∀ᶠ N in atTop, -(A / 2) < Z N / (N ^ (-l) * Real.log N ^ s) - A :=
    hε.eventually (Ioi_mem_nhds (by linarith))
  have hpos : ∀ᶠ N in atTop, 0 < Z N := by
    filter_upwards [hev, eventually_gt_atTop (1 : ℝ)] with N hN hN1
    have hpow : 0 < N ^ (-l) * Real.log N ^ s :=
      mul_pos (Real.rpow_pos_of_pos (by linarith) _) (pow_pos (Real.log_pos hN1) s)
    have : 0 < Z N / (N ^ (-l) * Real.log N ^ s) := by linarith
    exact (div_pos_iff_of_pos_right hpow).1 this
  refine ⟨hpos, ?_⟩
  -- the main term: L * (−log(1 + ε/A)) = −(L ε)/A − L (log(1+x) − x)
  have hx : Tendsto (fun N => (Z N / (N ^ (-l) * Real.log N ^ s) - A) / A) atTop (𝓝 0) := by
    simpa using hε.div_const A
  have hLx : Tendsto (fun N => Real.log N * ((Z N / (N ^ (-l) * Real.log N ^ s) - A) / A)) atTop
      (𝓝 (B / A)) := by
    have := hZ.div_const A
    refine this.congr' (Eventually.of_forall fun N => ?_)
    ring
  -- the error L (log(1+x) − x) → 0
  have herr : Tendsto (fun N => Real.log N *
      (Real.log (1 + (Z N / (N ^ (-l) * Real.log N ^ s) - A) / A) -
        (Z N / (N ^ (-l) * Real.log N ^ s) - A) / A)) atTop (𝓝 0) := by
    have hden : Tendsto (fun N => 1 + (Z N / (N ^ (-l) * Real.log N ^ s) - A) / A) atTop
        (𝓝 (1 + 0)) := tendsto_const_nhds.add hx
    have hbound := (hLx.mul hx).mul (hden.inv₀ (by norm_num))
    simp only [mul_zero, zero_mul, add_zero, inv_one] at hbound
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [hev, eventually_gt_atTop (1 : ℝ)] with N hN hN1
    have hlog : 0 < Real.log N := Real.log_pos hN1
    set x := (Z N / (N ^ (-l) * Real.log N ^ s) - A) / A with hxdef
    have hx1 : -1 < x := by
      rw [hxdef, lt_div_iff₀ hA]
      linarith
    have h1x : 0 < 1 + x := by linarith
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hlog]
    calc Real.log N * |Real.log (1 + x) - x| ≤ Real.log N * (x ^ 2 / (1 + x)) :=
          mul_le_mul_of_nonneg_left (abs_log_one_add_sub_le hx1) hlog.le
      _ = Real.log N * x * x * (1 + x)⁻¹ := by
          rw [sq, div_eq_mul_inv]
          ring
  have hmain := hLx.neg.sub herr
  rw [sub_zero] at hmain
  rw [show -B / A = -(B / A) by ring]
  refine hmain.congr' ?_
  · filter_upwards [hpos, hev, eventually_gt_atTop (1 : ℝ)] with N hZN hN hN1
    have hN0 : 0 < N := by linarith
    have hlog : 0 < Real.log N := Real.log_pos hN1
    have hpow : 0 < N ^ (-l) := Real.rpow_pos_of_pos hN0 _
    have hlogs : 0 < Real.log N ^ s := pow_pos hlog s
    have hAε : 0 < A + (Z N / (N ^ (-l) * Real.log N ^ s) - A) := by linarith
    have hZeq : Z N =
        N ^ (-l) * Real.log N ^ s * (A + (Z N / (N ^ (-l) * Real.log N ^ s) - A)) := by
      field_simp
      ring
    have hlogZ : Real.log (Z N) = -l * Real.log N + s * Real.log (Real.log N) +
        Real.log (A + (Z N / (N ^ (-l) * Real.log N ^ s) - A)) := by
      conv_lhs => rw [hZeq]
      rw [Real.log_mul (mul_pos hpow hlogs).ne' hAε.ne', Real.log_mul hpow.ne' hlogs.ne',
        Real.log_rpow hN0, Real.log_pow]
    have hlog1 : Real.log (1 + (Z N / (N ^ (-l) * Real.log N ^ s) - A) / A) =
        Real.log (A + (Z N / (N ^ (-l) * Real.log N ^ s) - A)) - Real.log A := by
      rw [← Real.log_div hAε.ne' hA.ne']
      congr 1
      field_simp
    rw [hlogZ, hlog1]
    ring

/-- **Population free energy at chart level**: for an analytic amplitude with positive face
functional `A`, `−log 𝒵_N = λ log N − (m−1) log log N − log A − (B/A)/log N + o(1/log N)`. -/
theorem population_free_energy_chart (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {R : ℝ} (hR : 1 < R) {Fη : (Fin (n + 1) → ℂ) → ℂ}
    {η : (Fin (n + 1) → ℝ) → ℝ} (hFη : DifferentiableOn ℂ Fη (openPolydisc (n + 1) R))
    (hη : ∀ u ∈ piBox (n + 1) (Ioc 0 1), (Fη fun i => (u i : ℂ)).re = η u)
    (hηc : Continuous η) {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i)
    (hatt : ∃ i, ratioExp h k i = l) (hA : 0 < amplitudeCoeff h k l β η) :
    (∀ᶠ N in atTop, 0 < origPhaseIntegral n h k β N 1 (fun _ => 0) η) ∧
    Tendsto (fun N => Real.log N * (-Real.log (origPhaseIntegral n h k β N 1 (fun _ => 0) η) -
      (l * Real.log N - ((multCount (ratioExp h k) l - 1 : ℕ) : ℝ) * Real.log (Real.log N) -
        Real.log (amplitudeCoeff h k l β η)))) atTop
      (𝓝 (-secondCoeff n h k β Fη l / amplitudeCoeff h k l β η)) :=
  neg_log_twoTerm hA (population_twoTerm_chart n h k hk β hβ hR hFη hη hηc hmin hatt)

variable {M : ℕ} {K : Fin M → Type*} [∀ I, TopologicalSpace (K I)] [∀ I, CompactSpace (K I)]
  [∀ I, T2Space (K I)] [∀ I, MeasurableSpace (K I)] [∀ I, OpensMeasurableSpace (K I)]
  {n : Fin M → ℕ} (ν : (I : Fin M) → Measure (K I)) [∀ I, IsFiniteMeasure (ν I)]
  (h k : (I : Fin M) → Fin (n I + 1) → ℕ) (β : ℝ)

/-- **Assembled population free energy**: for `A_* > 0`,
`−log 𝒵_N = μ_* log N − (m_*−1) log log N − log A_* − (B_*/A_*)/log N + o(1/log N)`. -/
theorem population_free_energy_assembled (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (x : JointData K n)
    (hx : ∀ I v, xiCoord (x.chart I v) = 0) (lam : Fin M → ℝ)
    (hmin : ∀ I i, lam I ≤ ratioExp (h I) (k I) i) (hatt : ∀ I, ∃ i, ratioExp (h I) (k I) i = lam I)
    {μs : ℝ} (hμ : ∀ I, μs ≤ lam I) (hμatt : ∃ I, lam I = μs) {ms : ℕ}
    (hm : ∀ I, lam I = μs → multCount (ratioExp (h I) (k I)) (lam I) ≤ ms)
    (hmatt : ∃ I, lam I = μs ∧ multCount (ratioExp (h I) (k I)) (lam I) = ms) (Zpop E : ℝ → ℝ)
    (hdecomp : ∀ N, Zpop N = gInt ν h k β (fun _ => 1) x N + E N)
    (hE : Tendsto (fun N => E N * Real.log N / N ^ (-μs)) atTop (𝓝 0))
    (hA : 0 < assembledFace ν h k β x lam μs ms) :
    (∀ᶠ N in atTop, 0 < Zpop N) ∧
    Tendsto (fun N => Real.log N * (-Real.log (Zpop N) -
      (μs * Real.log N - ((ms - 1 : ℕ) : ℝ) * Real.log (Real.log N) -
        Real.log (assembledFace ν h k β x lam μs ms)))) atTop
      (𝓝 (-assembledSecondCoeff ν h k β x μs ms / assembledFace ν h k β x lam μs ms)) :=
  neg_log_twoTerm hA (population_twoTerm_assembled ν h k β hk hβ x hx lam hmin hatt hμ hμatt hm
    hmatt Zpop E hdecomp hE)

end Grammar
