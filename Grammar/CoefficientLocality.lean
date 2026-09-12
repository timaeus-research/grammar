/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SourceDecompositionAssembly

/-!
# Coefficient locality (CCLXXXV)

The coefficient of a leading term depends on the integration region — but only through the part
of the region where the phase vanishes (consult #86, B):

* `targetIntegral_sub_hasExponentialBound`: if two regions differ only on a set where
  `K ≥ κ > 0` (a.e.) and the amplitude is integrable there, their target integrals differ by an
  exponentially small remainder;
* ★ `HasLeadingTerm.targetIntegral_of_locality`: a leading-term certificate of one region
  transfers to the other with the SAME pair and coefficient (CCLXXIII); with positive coefficients
  the pairs and coefficients of any two certificates agree
  (`targetIntegral_pair_coeff_eq_of_locality`);
* ★ `hasLeadingTerm_closedBall_iff_of_isolatedZero`: **small-ball radius independence around an
  isolated zero** — for a phase continuous on a compact neighbourhood with a unique zero `w`, the
  closed balls `closedBall w r` inside it all carry the same leading term (their symmetric
  difference is an annular region with a positive phase gap).

Radius independence fails for a positive-dimensional zero set (`K(x,y) = x²` on a disk of radius
`r`: the coefficient `2r√π` grows with `r`); the general final form of the theory is the
coefficient of a region.
-/

open MeasureTheory Set Filter Topology Asymptotics

namespace Grammar

section Locality

variable {d : ℕ} {F K : (Fin d → ℝ) → ℝ} {p : TubeWeight d}

/-- The Boltzmann integrand is integrable on a set on which the amplitude is. -/
theorem integrableOn_boltzmann_of_integrableOn {S : Set (Fin d → ℝ)}
    (hint : IntegrableOn (fun x => F x * p.w x) S) (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x)
    {N : ℝ} (hN : 0 ≤ N) :
    IntegrableOn (fun x => F x * p.w x * Real.exp (-N * K x)) S := by
  have h := hint.bdd_mul (c := 1) (f := fun x => Real.exp (-N * K x))
    (Real.measurable_exp.comp (measurable_const.mul hK)).aestronglyMeasurable
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_mul]
      exact neg_nonpos.2 (mul_nonneg hN (hK0 x)))
  exact h.congr (Eventually.of_forall fun x => by beta_reduce; ring)

/-- **Two regions differing on a phase-gap set have exponentially close target integrals.** -/
theorem targetIntegral_sub_hasExponentialBound {A B : Set (Fin d → ℝ)} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hint : IntegrableOn (fun x => F x * p.w x) (A ∪ B))
    (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x) {κ : ℝ} (hκ : 0 < κ)
    (hKA : ∀ᵐ x ∂(volume.restrict (A \ B)), κ ≤ K x)
    (hKB : ∀ᵐ x ∂(volume.restrict (B \ A)), κ ≤ K x) :
    HasExponentialBound fun N => targetIntegral A F K p N - targetIntegral B F K p N := by
  have h1 := hasExponentialBound_setIntegral (μ := volume) (S := A \ B)
    (g := fun x => F x * p.w x) (K := K) (hint.mono_set (diff_subset.trans subset_union_left)) hκ
    hKA
  have h2 := hasExponentialBound_setIntegral (μ := volume) (S := B \ A)
    (g := fun x => F x * p.w x) (K := K) (hint.mono_set (diff_subset.trans subset_union_right)) hκ
    hKB
  obtain ⟨C₁, hC₁, κ₁, hκ₁, hb₁⟩ := h1
  obtain ⟨C₂, hC₂, κ₂, hκ₂, hb₂⟩ := h2.neg
  refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, min κ₁ κ₂, lt_min hκ₁ hκ₂, fun N hN => ?_⟩
  have hsplit : targetIntegral A F K p N - targetIntegral B F K p N =
      (∫ x in A \ B, F x * p.w x * Real.exp (-N * K x)) +
        -(∫ x in B \ A, F x * p.w x * Real.exp (-N * K x)) := by
    have hg := integrableOn_boltzmann_of_integrableOn hint hK hK0 hN
    have hAeq : targetIntegral A F K p N =
        (∫ x in A ∩ B, F x * p.w x * Real.exp (-N * K x)) +
          ∫ x in A \ B, F x * p.w x * Real.exp (-N * K x) := by
      unfold targetIntegral
      rw [← setIntegral_union disjoint_sdiff_inter.symm (hA.diff hB)
        (hg.mono_set (inter_subset_left.trans subset_union_left))
        (hg.mono_set (diff_subset.trans subset_union_left)), inter_union_diff]
    have hBeq : targetIntegral B F K p N =
        (∫ x in A ∩ B, F x * p.w x * Real.exp (-N * K x)) +
          ∫ x in B \ A, F x * p.w x * Real.exp (-N * K x) := by
      unfold targetIntegral
      rw [← setIntegral_union (inter_comm A B ▸ disjoint_sdiff_inter.symm) (hB.diff hA)
        (hg.mono_set (inter_subset_left.trans subset_union_left))
        (hg.mono_set (diff_subset.trans subset_union_right)), inter_comm, inter_union_diff]
    rw [hAeq, hBeq]
    ring
  beta_reduce
  rw [hsplit]
  have e1 : Real.exp (-κ₁ * N) ≤ Real.exp (-min κ₁ κ₂ * N) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_left κ₁ κ₂])
  have e2 : Real.exp (-κ₂ * N) ≤ Real.exp (-min κ₁ κ₂ * N) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_right κ₁ κ₂])
  calc |(∫ x in A \ B, F x * p.w x * Real.exp (-N * K x)) +
        -(∫ x in B \ A, F x * p.w x * Real.exp (-N * K x))|
      ≤ |∫ x in A \ B, F x * p.w x * Real.exp (-N * K x)| +
          |-(∫ x in B \ A, F x * p.w x * Real.exp (-N * K x))| := abs_add_le _ _
    _ ≤ C₁ * Real.exp (-κ₁ * N) + C₂ * Real.exp (-κ₂ * N) := add_le_add (hb₁ N hN) (hb₂ N hN)
    _ ≤ C₁ * Real.exp (-min κ₁ κ₂ * N) + C₂ * Real.exp (-min κ₁ κ₂ * N) :=
      add_le_add (mul_le_mul_of_nonneg_left e1 hC₁) (mul_le_mul_of_nonneg_left e2 hC₂)
    _ = (C₁ + C₂) * Real.exp (-min κ₁ κ₂ * N) := by ring

/-- ★ **Coefficient locality**: a leading-term certificate transfers between regions differing only
on a phase-gap set, with the same pair and coefficient. -/
theorem HasLeadingTerm.targetIntegral_of_locality {A B : Set (Fin d → ℝ)} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hint : IntegrableOn (fun x => F x * p.w x) (A ∪ B))
    (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x) {κ : ℝ} (hκ : 0 < κ)
    (hKA : ∀ᵐ x ∂(volume.restrict (A \ B)), κ ≤ K x)
    (hKB : ∀ᵐ x ∂(volume.restrict (B \ A)), κ ≤ K x) {c lam : ℝ} {k : ℕ}
    (h : HasLeadingTerm (targetIntegral A F K p) c lam k) :
    HasLeadingTerm (targetIntegral B F K p) c lam k :=
  (h.add_exponential (targetIntegral_sub_hasExponentialBound hB hA
    (union_comm A B ▸ hint) hK hK0 hκ hKB hKA)).congr' (Eventually.of_forall fun N => by
      simp only
      ring)

/-- Two positive certificates of two regions differing on a phase-gap set have the same pair and
coefficient. -/
theorem targetIntegral_pair_coeff_eq_of_locality {A B : Set (Fin d → ℝ)} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hint : IntegrableOn (fun x => F x * p.w x) (A ∪ B))
    (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x) {κ : ℝ} (hκ : 0 < κ)
    (hKA : ∀ᵐ x ∂(volume.restrict (A \ B)), κ ≤ K x)
    (hKB : ∀ᵐ x ∂(volume.restrict (B \ A)), κ ≤ K x) {c₁ c₂ lam₁ lam₂ : ℝ} {k₁ k₂ : ℕ}
    (h₁ : HasLeadingTerm (targetIntegral A F K p) c₁ lam₁ k₁) (hc₁ : c₁ ≠ 0)
    (h₂ : HasLeadingTerm (targetIntegral B F K p) c₂ lam₂ k₂) (hc₂ : c₂ ≠ 0) :
    lam₁ = lam₂ ∧ k₁ = k₂ ∧ c₁ = c₂ := by
  have h₁' := h₁.targetIntegral_of_locality hA hB hint hK hK0 hκ hKA hKB
  obtain ⟨hl, hk⟩ := h₁'.pair_unique hc₁ h₂ hc₂
  subst hl hk
  exact ⟨rfl, rfl, h₁'.coeff_unique h₂⟩

end Locality

/-! ### Small-ball radius independence around an isolated zero -/

section IsolatedZero

variable {d : ℕ} {F K : (Fin d → ℝ) → ℝ} {p : TubeWeight d} {S : Set (Fin d → ℝ)}
  (hS : IsCompact S) (hKc : ContinuousOn K S) (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x)
  {w : Fin d → ℝ} (hzero : ∀ x ∈ S, K x = 0 → x = w)

include hS hKc hK0 hzero in
/-- The phase has a positive gap on the compact part of `S` at distance at least `r > 0` from the
isolated zero. -/
theorem exists_gap_of_isolatedZero {r : ℝ} (hr : 0 < r) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ x ∈ S \ Metric.ball w r, κ ≤ K x := by
  refine exists_pos_le_of_isCompact (hS.diff Metric.isOpen_ball) (hKc.mono diff_subset)
    fun x hx => lt_of_le_of_ne (hK0 x) fun h0 => ?_
  have := hzero x hx.1 h0.symm
  exact hx.2 (this ▸ Metric.mem_ball_self hr)

include hS hKc hK hK0 hzero in
/-- ★ **Small-ball radius independence around an isolated zero**: closed balls around `w` inside the
compact neighbourhood carry the same leading term. -/
theorem hasLeadingTerm_closedBall_iff_of_isolatedZero
    (hint : IntegrableOn (fun x => F x * p.w x) S) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hB₁ : Metric.closedBall w r₁ ⊆ S) (hB₂ : Metric.closedBall w r₂ ⊆ S) {c lam : ℝ} {k : ℕ} :
    HasLeadingTerm (targetIntegral (Metric.closedBall w r₁) F K p) c lam k ↔
      HasLeadingTerm (targetIntegral (Metric.closedBall w r₂) F K p) c lam k := by
  obtain ⟨κ, hκ, hgap⟩ := exists_gap_of_isolatedZero hS hKc hK0 hzero (lt_min hr₁ hr₂)
  have hunion : Metric.closedBall w r₁ ∪ Metric.closedBall w r₂ ⊆ S := union_subset hB₁ hB₂
  have hgap₁ : ∀ᵐ x ∂(volume.restrict (Metric.closedBall w r₁ \ Metric.closedBall w r₂)),
      κ ≤ K x :=
    ae_restrict_of_forall_mem (Metric.isClosed_closedBall.measurableSet.diff
      Metric.isClosed_closedBall.measurableSet) fun x hx =>
      hgap x ⟨hB₁ hx.1, fun hb => hx.2 (Metric.ball_subset_closedBall
        (Metric.ball_subset_ball (min_le_right r₁ r₂) hb))⟩
  have hgap₂ : ∀ᵐ x ∂(volume.restrict (Metric.closedBall w r₂ \ Metric.closedBall w r₁)),
      κ ≤ K x :=
    ae_restrict_of_forall_mem (Metric.isClosed_closedBall.measurableSet.diff
      Metric.isClosed_closedBall.measurableSet) fun x hx =>
      hgap x ⟨hB₂ hx.1, fun hb => hx.2 (Metric.ball_subset_closedBall
        (Metric.ball_subset_ball (min_le_left r₁ r₂) hb))⟩
  constructor
  · intro h
    exact h.targetIntegral_of_locality Metric.isClosed_closedBall.measurableSet
      Metric.isClosed_closedBall.measurableSet (hint.mono_set hunion) hK hK0 hκ hgap₁ hgap₂
  · intro h
    exact h.targetIntegral_of_locality Metric.isClosed_closedBall.measurableSet
      Metric.isClosed_closedBall.measurableSet (hint.mono_set (union_comm _ _ ▸ hunion)) hK hK0 hκ
      hgap₂ hgap₁

end IsolatedZero

end Grammar
