/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Uniform next-log quotients

Uniform algebra for real-valued families on a set `S`: products with bounded limits
(`tendstoUniformlyOn_mul_of_bounded`), reciprocals above a positive floor
(`tendstoUniformlyOn_inv_of_floor`), and the **uniform next-log quotient theorem**
(`tendstoUniformlyOn_nextLog_div`): if `log N (a_N − A) → B_A` and `log N (z_N − F) → B_Z`
uniformly on `S`, the limits are bounded on `S`, and `F ≥ δ > 0` on `S`, then
`log N (a_N/z_N − A/F) → (B_A F − A B_Z)/F²` uniformly on `S`, with `z_N ≥ δ/2` eventually
uniformly (`eventually_floor_of_nextLog`).
-/

open Filter Topology

namespace Grammar

variable {ι : Type*} {S : Set ι}

/-- A family constant in `N` converges uniformly to itself. -/
theorem tendstoUniformlyOn_const' (f : ι → ℝ) :
    TendstoUniformlyOn (fun _ : ℝ => f) f atTop S :=
  fun _ hu => Eventually.of_forall fun _ _ _ => refl_mem_uniformity hu

/-- Products of uniformly convergent real families with bounded limits converge uniformly. -/
theorem tendstoUniformlyOn_mul_of_bounded {F G : ℝ → ι → ℝ} {f g : ι → ℝ}
    (hF : TendstoUniformlyOn F f atTop S) (hG : TendstoUniformlyOn G g atTop S) {Mf Mg : ℝ}
    (hf : ∀ x ∈ S, |f x| ≤ Mf) (hg : ∀ x ∈ S, |g x| ≤ Mg) :
    TendstoUniformlyOn (fun N x => F N x * G N x) (fun x => f x * g x) atTop S := by
  rw [Metric.tendstoUniformlyOn_iff] at hF hG ⊢
  intro ε hε
  have hMf : 0 ≤ Mf ∨ S = ∅ := by
    by_cases hS : S = ∅
    · exact Or.inr hS
    · obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 hS
      exact Or.inl ((abs_nonneg _).trans (hf x hx))
  rcases hMf with hMf | hS
  · have hMg : 0 ≤ Mg ∨ S = ∅ := by
      by_cases hS : S = ∅
      · exact Or.inr hS
      · obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 hS
        exact Or.inl ((abs_nonneg _).trans (hg x hx))
    rcases hMg with hMg | hS
    · set η := min 1 (ε / (Mf + Mg + 2)) with hη
      have hη0 : 0 < η := lt_min one_pos (by positivity)
      have hη1 : η ≤ 1 := min_le_left _ _
      have hη2 : η ≤ ε / (Mf + Mg + 2) := min_le_right _ _
      filter_upwards [hF η hη0, hG η hη0] with N hFN hGN x hx
      have h1 := hFN x hx
      have h2 := hGN x hx
      rw [Real.dist_eq] at h1 h2 ⊢
      have hGb : |G N x| ≤ Mg + 1 := by
        have := abs_sub_abs_le_abs_sub (G N x) (g x)
        rw [abs_sub_comm] at this
        linarith [hg x hx]
      -- `f g − F G = f (g − G) + (f − F) G`
      have hid : f x * g x - F N x * G N x = f x * (g x - G N x) + (f x - F N x) * G N x := by ring
      rw [hid]
      calc |f x * (g x - G N x) + (f x - F N x) * G N x|
          ≤ |f x| * |g x - G N x| + |f x - F N x| * |G N x| := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_mul]
        _ ≤ Mf * η + η * (Mg + 1) :=
            add_le_add (mul_le_mul (hf x hx) h2.le (abs_nonneg _) hMf)
              (mul_le_mul h1.le hGb (abs_nonneg _) hη0.le)
        _ = η * (Mf + Mg + 1) := by ring
        _ < η * (Mf + Mg + 2) := by
            have : 0 < η := hη0
            nlinarith
        _ ≤ ε := by
            calc η * (Mf + Mg + 2) ≤ ε / (Mf + Mg + 2) * (Mf + Mg + 2) := by gcongr
              _ = ε := by field_simp
    · subst hS
      simp
  · subst hS
    simp

/-- Above a positive floor, reciprocals of a uniformly convergent family converge uniformly. -/
theorem tendstoUniformlyOn_inv_of_floor {Z : ℝ → ι → ℝ} {F : ι → ℝ}
    (hZ : TendstoUniformlyOn Z F atTop S) {δ : ℝ} (hδ : 0 < δ) (hfloor : ∀ x ∈ S, δ ≤ F x) :
    TendstoUniformlyOn (fun N x => (Z N x)⁻¹) (fun x => (F x)⁻¹) atTop S := by
  rw [Metric.tendstoUniformlyOn_iff] at hZ ⊢
  intro ε hε
  set η := min (δ / 2) (ε * (δ * (δ / 2))) with hη
  have hη0 : 0 < η := lt_min (by positivity) (by positivity)
  filter_upwards [hZ η hη0] with N hN x hx
  have h1 := hN x hx
  rw [Real.dist_eq] at h1 ⊢
  have hFx := hfloor x hx
  have hηle : η ≤ δ / 2 := min_le_left _ _
  have hZx : δ / 2 ≤ Z N x := by
    have := (abs_lt.1 h1).2
    linarith
  have hZ0 : Z N x ≠ 0 := by linarith
  have hF0 : F x ≠ 0 := by linarith
  rw [abs_sub_comm] at h1
  rw [inv_sub_inv hF0 hZ0, abs_div, abs_mul, abs_of_pos (by linarith : 0 < F x),
    abs_of_pos (by linarith : 0 < Z N x), div_lt_iff₀ (mul_pos (by linarith) (by linarith))]
  calc |Z N x - F x| < η := h1
    _ ≤ ε * (δ * (δ / 2)) := min_le_right _ _
    _ ≤ ε * (F x * Z N x) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hFx hZx (by positivity) (by linarith)) hε.le

/-- If `log N (z_N − F) → B_Z` uniformly on `S` with `B_Z` bounded, then `z_N → F` uniformly. -/
theorem tendstoUniformlyOn_of_nextLog {z : ℝ → ι → ℝ} {F BZ : ι → ℝ}
    (hZ : TendstoUniformlyOn (fun N x => Real.log N * (z N x - F x)) BZ atTop S) {MB : ℝ}
    (hMB : ∀ x ∈ S, |BZ x| ≤ MB) : TendstoUniformlyOn z F atTop S := by
  rw [Metric.tendstoUniformlyOn_iff] at hZ ⊢
  intro ε hε
  have hMB0 : 0 ≤ MB ∨ S = ∅ := by
    by_cases hS : S = ∅
    · exact Or.inr hS
    · obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 hS
      exact Or.inl ((abs_nonneg _).trans (hMB x hx))
  rcases hMB0 with hMB0 | hS
  · have hlim : Tendsto (fun N : ℝ => (MB + 1) / Real.log N) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
    filter_upwards [hZ 1 one_pos, hlim.eventually (gt_mem_nhds hε), eventually_gt_atTop (1 : ℝ)]
      with N h1 h2 hN x hx
    have hL : 0 < Real.log N := Real.log_pos hN
    have hd := h1 x hx
    rw [Real.dist_eq] at hd ⊢
    have hb : |Real.log N * (z N x - F x)| ≤ MB + 1 := by
      have := abs_sub_abs_le_abs_sub (Real.log N * (z N x - F x)) (BZ x)
      rw [abs_sub_comm] at this
      linarith [hMB x hx]
    rw [abs_mul, abs_of_pos hL] at hb
    rw [abs_sub_comm, ← le_div_iff₀' hL] at hb
    exact hb.trans_lt h2
  · subst hS
    simp

/-- Eventual uniform floor for the denominator: `z_N ≥ δ/2` on `S` for large `N`. -/
theorem eventually_floor_of_nextLog {z : ℝ → ι → ℝ} {F BZ : ι → ℝ}
    (hZ : TendstoUniformlyOn (fun N x => Real.log N * (z N x - F x)) BZ atTop S) {MB : ℝ}
    (hMB : ∀ x ∈ S, |BZ x| ≤ MB) {δ : ℝ} (hδ : 0 < δ) (hfloor : ∀ x ∈ S, δ ≤ F x) :
    ∀ᶠ N in atTop, ∀ x ∈ S, δ / 2 ≤ z N x := by
  have h := Metric.tendstoUniformlyOn_iff.1 (tendstoUniformlyOn_of_nextLog hZ hMB) (δ / 2)
    (by positivity)
  filter_upwards [h] with N hN x hx
  have := hN x hx
  rw [Real.dist_eq] at this
  have := (abs_lt.1 this).2
  linarith [hfloor x hx]

/-- **The uniform next-log quotient theorem**: `log N (a_N − A) → B_A`, `log N (z_N − F) → B_Z`
uniformly on `S`, bounded limits, `F ≥ δ > 0` on `S` ⇒
`log N (a_N/z_N − A/F) → (B_A F − A B_Z)/F²` uniformly on `S`. -/
theorem tendstoUniformlyOn_nextLog_div {a z : ℝ → ι → ℝ} {A F BA BZ : ι → ℝ}
    (hA : TendstoUniformlyOn (fun N x => Real.log N * (a N x - A x)) BA atTop S)
    (hZ : TendstoUniformlyOn (fun N x => Real.log N * (z N x - F x)) BZ atTop S)
    {MA MB : ℝ} (hMA : ∀ x ∈ S, |A x| ≤ MA) (hMF : ∀ x ∈ S, |F x| ≤ MA)
    (hMBA : ∀ x ∈ S, |BA x| ≤ MB) (hMBZ : ∀ x ∈ S, |BZ x| ≤ MB) {δ : ℝ} (hδ : 0 < δ)
    (hfloor : ∀ x ∈ S, δ ≤ F x) :
    TendstoUniformlyOn (fun N x => Real.log N * (a N x / z N x - A x / F x))
      (fun x => (BA x * F x - A x * BZ x) / F x ^ 2) atTop S := by
  -- `u F − A v` with `u = log N (a − A)`, `v = log N (z − F)`
  have h1 : TendstoUniformlyOn (fun N x => Real.log N * (a N x - A x) * F x)
      (fun x => BA x * F x) atTop S :=
    tendstoUniformlyOn_mul_of_bounded hA (tendstoUniformlyOn_const' F) hMBA hMF
  have h2 : TendstoUniformlyOn (fun N x => A x * (Real.log N * (z N x - F x)))
      (fun x => A x * BZ x) atTop S :=
    tendstoUniformlyOn_mul_of_bounded (tendstoUniformlyOn_const' A) hZ hMA hMBZ
  have h3 := h1.sub h2
  -- `1/z → 1/F`
  have hinv : TendstoUniformlyOn (fun N x => (z N x)⁻¹) (fun x => (F x)⁻¹) atTop S :=
    tendstoUniformlyOn_inv_of_floor (tendstoUniformlyOn_of_nextLog hZ hMBZ) hδ hfloor
  have hnum_bd : ∀ x ∈ S, |BA x * F x - A x * BZ x| ≤ 2 * (MB * MA) := fun x hx => by
    have := abs_sub (BA x * F x) (A x * BZ x)
    rw [abs_mul, abs_mul] at this
    have h1 := mul_le_mul (hMBA x hx) (hMF x hx) (abs_nonneg _) ((abs_nonneg _).trans (hMBA x hx))
    have h2 := mul_le_mul (hMA x hx) (hMBZ x hx) (abs_nonneg _) ((abs_nonneg _).trans (hMA x hx))
    linarith
  have hinv_bd : ∀ x ∈ S, |(F x)⁻¹| ≤ δ⁻¹ := fun x hx => by
    rw [abs_inv, abs_of_pos (by linarith [hfloor x hx])]
    exact inv_anti₀ hδ (hfloor x hx)
  have h4 := tendstoUniformlyOn_mul_of_bounded
    (tendstoUniformlyOn_mul_of_bounded h3 hinv hnum_bd hinv_bd)
    (tendstoUniformlyOn_const' fun x => (F x)⁻¹) (Mf := 2 * (MB * MA) * δ⁻¹)
    (fun x hx => by
      rw [abs_mul]
      exact mul_le_mul (hnum_bd x hx) (hinv_bd x hx) (abs_nonneg _)
        ((abs_nonneg _).trans (hnum_bd x hx))) hinv_bd
  refine (h4.congr ?_).congr_right fun x hx => ?_
  · filter_upwards [eventually_floor_of_nextLog hZ hMBZ hδ hfloor, eventually_gt_atTop (1 : ℝ)]
      with N hN hN1 x hx
    have hL : Real.log N ≠ 0 := (Real.log_pos hN1).ne'
    have hz : z N x ≠ 0 := by linarith [hN x hx]
    have hF : F x ≠ 0 := by linarith [hfloor x hx]
    simp only [Pi.sub_apply]
    field_simp
    ring
  · have hF : F x ≠ 0 := by linarith [hfloor x hx]
    simp only [Pi.sub_apply]
    field_simp

end Grammar
