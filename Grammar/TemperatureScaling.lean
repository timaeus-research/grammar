/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.SpatialNextLogDictionary

/-!
# Temperature scaling of the two-term coefficients

The exact kernel identity `𝒵_N^β[η; ξ] = 𝒵_{βN}^1[η; √β ξ]` (`origPhaseIntegral_temperature_scale`;
note the phase rescaling — it is **not** `𝒵^1_{βN}[η; ξ]`) transports the `β = 1` two-term
expansion along `N ↦ βN`.  Since `log(βN) = log β + log N`, the leading and next-log coefficients
scale as
`F_β[η; ξ] = β^{−λ} F_1[η; √β ξ]`, `B_β[η; ξ] = β^{−λ}(B_1[η; √β ξ] + (m−1) log β · F_1[η; √β ξ])`
(`spatialFace_temperature_scale`, `spatialSecondFace_temperature_scale`), by uniqueness of the
two-term coefficients (`twoTerm_coeff_unique`).  This is an independent check of the normalisation
of `B` by `log N` rather than `log(βN)`: the second coefficient is not temperature-covariant on its
own, the `(m−1) log β` cross term is forced.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open CoeffFamily

/-! ### Uniqueness of two-term coefficients -/

/-- If `log N (f N − F) → B` and `log N (f N − F') → B'` then `F = F'` and `B = B'`. -/
theorem twoTerm_coeff_unique {f : ℝ → ℝ} {F B F' B' : ℝ}
    (h : Tendsto (fun N => Real.log N * (f N - F)) atTop (𝓝 B))
    (h' : Tendsto (fun N => Real.log N * (f N - F')) atTop (𝓝 B')) : F = F' ∧ B = B' := by
  have hsub := h.sub h'
  have heq : (fun N => Real.log N * (f N - F) - Real.log N * (f N - F')) =
      fun N => Real.log N * (F' - F) := funext fun N => by ring
  rw [heq] at hsub
  have hF : F' - F = 0 := eq_zero_of_tendsto_log_mul_const hsub
  have hF' : F' = F := by linarith
  subst hF'
  refine ⟨rfl, ?_⟩
  rw [sub_self, show (fun N : ℝ => Real.log N * 0) = fun _ => 0 from funext fun _ => mul_zero _]
    at hsub
  have := tendsto_nhds_unique hsub tendsto_const_nhds
  linarith

/-! ### The exact kernel identity -/

/-- `𝒵_N^β[η; ξ] = 𝒵_{βN}^1[η; √β ξ]` for every real `N` (`β > 0`). -/
theorem origPhaseIntegral_temperature_scale (n : ℕ) (h k : Fin (n + 1) → ℕ) {β : ℝ} (hβ : 0 < β)
    (N : ℝ) (ξ η : (Fin (n + 1) → ℝ) → ℝ) :
    origPhaseIntegral n h k β N 1 ξ η =
      origPhaseIntegral n h k 1 (β * N) 1 (fun u => Real.sqrt β * ξ u) η := by
  unfold origPhaseIntegral
  refine setIntegral_congr_fun (measurableSet_piBox _ _ measurableSet_Ioc) fun u _ => ?_
  dsimp only
  rw [Real.sqrt_mul hβ.le]
  congr 2
  have := Real.mul_self_sqrt hβ.le
  linear_combination (-(Real.sqrt N * (∏ i, u i ^ k i) * ξ u)) * this

/-! ### Scaling of the two-term coefficients -/

variable (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ} (hβ : 0 < β)
  {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummable cξ) (hη : AbsSummable cη)
  {ξ η : (Fin (n + 1) → ℝ) → ℝ} (hξc : Continuous ξ) (hηc : Continuous η)
  (hevξ : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cξ u = ξ u)
  (hevη : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ}
  (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
  (hm : 2 ≤ multCount (ratioExp h k) l)

include hk hβ hξ hη hξc hηc hevξ hevη hmin hatt hm in
/-- The `β = 1` two-term expansion transported to temperature `β`: with `F₁ = F_1[η; √β ξ]`,
`B₁ = B_1[η; √β ξ]`, `q = m − 1`,
`log N (𝒵_N^β/(N^{−λ} log^q N) − β^{−λ}F₁) → β^{−λ}(B₁ + q log β · F₁)`. -/
theorem spatialPhase_twoTerm_of_temperature_scale :
    Tendsto (fun N => Real.log N * (origPhaseIntegral n h k β N 1 ξ η /
        (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1)) -
        β ^ (-l) * spatialFace h k l 1 (fun u => Real.sqrt β * ξ u) η)) atTop
      (𝓝 (β ^ (-l) * (spatialSecondFace h k l 1 (fun u => Real.sqrt β * ξ u) η +
        ((multCount (ratioExp h k) l - 1 : ℕ) : ℝ) * Real.log β *
          spatialFace h k l 1 (fun u => Real.sqrt β * ξ u) η))) := by
  have hξc' : Continuous fun u => Real.sqrt β * ξ u := continuous_const.mul hξc
  have hevξ' : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF (Real.sqrt β • cξ) u = Real.sqrt β * ξ u :=
    fun u hu => by rw [evalF_const_smul, hevξ u hu]
  have h1 := spatialPhase_twoTerm_explicit n h k hk one_pos (AbsSummable.const_smul hξ _) hη hξc'
    hηc hevξ' hevη hmin hatt hm
  -- opaque names for the coefficients and the log degree
  generalize hq : multCount (ratioExp h k) l - 1 = q at h1 ⊢
  generalize hF : spatialFace h k l 1 (fun u => Real.sqrt β * ξ u) η = F₁ at h1 ⊢
  generalize hB : spatialSecondFace h k l 1 (fun u => Real.sqrt β * ξ u) η = B₁ at h1 ⊢
  -- transport along `N ↦ βN`
  have hG : Tendsto (fun N => Real.log (β * N) *
      (origPhaseIntegral n h k 1 (β * N) 1 (fun u => Real.sqrt β * ξ u) η /
        ((β * N) ^ (-l) * Real.log (β * N) ^ q) - F₁)) atTop (𝓝 B₁) :=
    h1.comp (tendsto_id.const_mul_atTop hβ)
  have hx : Tendsto (fun N : ℝ => Real.log β / Real.log N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have hratio : Tendsto (fun N : ℝ => Real.log N / Real.log (β * N)) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).div (hx.add (tendsto_const_nhds (x := (1 : ℝ))))
      (by norm_num)
    rw [zero_add, div_one] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    have hL : Real.log N ≠ 0 := (Real.log_pos hN).ne'
    rw [Real.log_mul hβ.ne' (by linarith)]
    change (1 : ℝ) / (Real.log β / Real.log N + 1) = Real.log N / (Real.log β + Real.log N)
    field_simp
  have hpow : Tendsto (fun N : ℝ => (1 + Real.log β / Real.log N) ^ q) atTop (𝓝 1) := by
    have := ((tendsto_const_nhds (x := (1 : ℝ))).add hx).pow q
    rwa [add_zero, one_pow] at this
  have hsum : Tendsto (fun N : ℝ => ∑ j ∈ Finset.range q, (1 + Real.log β / Real.log N) ^ j) atTop
      (𝓝 (q : ℝ)) := by
    have := tendsto_finsetSum (Finset.range q) fun j _ =>
      ((tendsto_const_nhds (x := (1 : ℝ))).add hx).pow j
    simpa using this
  -- the limit of the reorganised expression
  have hlim : Tendsto (fun N : ℝ => β ^ (-l) * ((Real.log N / Real.log (β * N)) *
      (Real.log (β * N) * (origPhaseIntegral n h k 1 (β * N) 1 (fun u => Real.sqrt β * ξ u) η /
        ((β * N) ^ (-l) * Real.log (β * N) ^ q) - F₁)) * (1 + Real.log β / Real.log N) ^ q +
      F₁ * (Real.log β * ∑ j ∈ Finset.range q, (1 + Real.log β / Real.log N) ^ j))) atTop
      (𝓝 (β ^ (-l) * (B₁ + (q : ℝ) * Real.log β * F₁))) := by
    have := ((hratio.mul hG).mul hpow).add ((hsum.const_mul (Real.log β)).const_mul F₁)
    have e : β ^ (-l) * (1 * B₁ * 1 + F₁ * (Real.log β * (q : ℝ))) =
        β ^ (-l) * (B₁ + (q : ℝ) * Real.log β * F₁) := by ring
    rw [← e]
    exact this.const_mul _
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (max 1 (1 / β))] with N hN
  have hN1 : 1 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hβN : 1 < β * N := by
    have := lt_of_le_of_lt (le_max_right _ _) hN
    rwa [div_lt_iff₀ hβ, mul_comm] at this
  have hL : Real.log N ≠ 0 := (Real.log_pos hN1).ne'
  have hLq : Real.log N ^ q ≠ 0 := pow_ne_zero _ hL
  have hlogmul : Real.log (β * N) = Real.log β + Real.log N := Real.log_mul hβ.ne' (by linarith)
  have hLβ : Real.log β + Real.log N ≠ 0 := hlogmul ▸ (Real.log_pos hβN).ne'
  have hrpow : (β * N) ^ (-l) = β ^ (-l) * N ^ (-l) := Real.mul_rpow hβ.le (by linarith)
  have hNl : N ^ (-l) ≠ 0 := (Real.rpow_pos_of_pos (by linarith) _).ne'
  have hβl : β ^ (-l) ≠ 0 := (Real.rpow_pos_of_pos hβ _).ne'
  rw [origPhaseIntegral_temperature_scale n h k hβ N ξ η, hrpow, hlogmul]
  -- `x = log β / log N`, `P = (1 + x)^q = 1 + x S`
  obtain ⟨x, hx⟩ : ∃ x, Real.log β / Real.log N = x := ⟨_, rfl⟩
  have hxL : x * Real.log N = Real.log β := by rw [← hx]; field_simp
  have hgeom : (∑ j ∈ Finset.range q, (1 + Real.log β / Real.log N) ^ j) *
      (Real.log β / Real.log N) = (1 + Real.log β / Real.log N) ^ q - 1 := by
    have := geom_sum_mul (1 + Real.log β / Real.log N) q
    rwa [add_sub_cancel_left] at this
  rw [hx] at hgeom ⊢
  generalize hS : (∑ j ∈ Finset.range q, (1 + x) ^ j) = S at hgeom ⊢
  have hP : (1 + x) ^ q = 1 + x * S := by linarith [hgeom]
  have hpowq : (Real.log β + Real.log N) ^ q = Real.log N ^ q * (1 + x * S) := by
    rw [← hP, ← mul_pow]
    congr 1
    rw [← hxL]
    ring
  have h1x : 1 + x ≠ 0 := fun h0 => hLβ (by
    rw [← hxL]
    have : x = -1 := by linarith
    rw [this]; ring)
  have hP0 : 1 + x * S ≠ 0 := by rw [← hP]; exact pow_ne_zero _ h1x
  rw [hpowq, hP, ← hxL]
  generalize origPhaseIntegral n h k 1 (β * N) 1 (fun u => Real.sqrt β * ξ u) η = Z
  generalize hA : β ^ (-l) = A at hβl ⊢
  generalize hNl' : N ^ (-l) = Nl at hNl ⊢
  generalize hLL : Real.log N = L at hL hLq hLβ hxL ⊢
  rw [← hxL] at hLβ
  have e1 : ∀ T : ℝ, L / (x * L + L) * ((x * L + L) * T) = L * T := fun T => by
    rw [div_mul_eq_mul_div, mul_div_assoc, mul_div_cancel_left₀ _ hLβ]
  rw [e1]
  field_simp
  ring

include hk hβ hξ hη hξc hηc hevξ hevη hmin hatt hm in
/-- **Temperature scaling of the leading coefficient**: `F_β[η; ξ] = β^{−λ} F_1[η; √β ξ]`. -/
theorem spatialFace_temperature_scale :
    spatialFace h k l β ξ η = β ^ (-l) * spatialFace h k l 1 (fun u => Real.sqrt β * ξ u) η :=
  (twoTerm_coeff_unique
    (spatialPhase_twoTerm_explicit n h k hk hβ hξ hη hξc hηc hevξ hevη hmin hatt hm)
    (spatialPhase_twoTerm_of_temperature_scale n h k hk hβ hξ hη hξc hηc hevξ hevη hmin hatt
      hm)).1

include hk hβ hξ hη hξc hηc hevξ hevη hmin hatt hm in
/-- **Temperature scaling of the second coefficient**:
`B_β[η; ξ] = β^{−λ} (B_1[η; √β ξ] + (m − 1) log β · F_1[η; √β ξ])` — the cross term is forced by
the normalisation of `B` by `log N` rather than `log(βN)`. -/
theorem spatialSecondFace_temperature_scale :
    spatialSecondFace h k l β ξ η =
      β ^ (-l) * (spatialSecondFace h k l 1 (fun u => Real.sqrt β * ξ u) η +
        ((multCount (ratioExp h k) l - 1 : ℕ) : ℝ) * Real.log β *
          spatialFace h k l 1 (fun u => Real.sqrt β * ξ u) η) :=
  (twoTerm_coeff_unique
    (spatialPhase_twoTerm_explicit n h k hk hβ hξ hη hξc hηc hevξ hevη hmin hatt hm)
    (spatialPhase_twoTerm_of_temperature_scale n h k hk hβ hξ hη hξc hηc hevξ hevη hmin hatt
      hm)).2

end Grammar
