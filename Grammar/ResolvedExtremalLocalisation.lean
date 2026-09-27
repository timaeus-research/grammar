/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.ResolvedLeadingMeasure
import Grammar.SmoothStratumMeasureExtremal

/-!
# Extremal localisation of the leading measure (polar-distribution plan, unit 20)

Consult #169 (`tide-log/gpt6_leading_v169.md`).  The population leading theorem of unit 19
(`hasLeadingTerm_Z_eq_integral_leadingResidueMeasureU`) is stated at a CHART-leading pair: every
piece box of the transport has all wall ratios `≥ λ` and at most `m` walls of ratio `λ`.  The
intrinsic notion is the EXTREMAL data `(λ*, m*)` of the zero fibre (`IsExtremalData`): every wall
through a point of `Z₀` has ratio `≥ λ*` and at most `m*` walls through any point of `Z₀` resonate
with `λ*`.  The two differ exactly on the pieces whose walls do not all pass through a point of the
zero fibre, so the bridge is a CERTIFICATE (`ExtremalCertificate`): every piece's wall multiset
`pieceWalls p = {(k_i, h_i)}` sits inside the intrinsic pair data of some point of the zero fibre.
The certificate holds whenever the chart centres lie in the zero fibre
(`extremalCertificate_of_divPt_zero`, via `pairs_divPt_zero`), and

  `IsExtremalData λ m ∧ ExtremalCertificate ⟹ ChartLeading λ m`

(★★ `chartLeading_of_extremalData`: the ratio bound is clause 1 of the extremal data and the
multiplicity count is bounded by the resonance count of clause 2, since a wall of ratio exactly `λ`
resonates with `λ`).

With the bridge `hasLeadingTerm_iff_tendsto_normalised` between the two normalisation conventions
of the library, uniqueness of limits identifies the population coefficient functional at the
extremal pair with the raw leading measure for EVERY smooth observable, with no test hypothesis:

  `𝒯^U_{λ*,m*−1}[G] = Γ(λ*)/(m*−1)! · ∫_U G dρ^{λ*}_{m*}`

(★★★ `coeff_withF_eq_integral_leadingResidueMeasureU`).  Downstairs this gives the leading
asymptotic of `∫ prior · f · e^{−NK}` for every smooth `f` against the pull-back of the raw
measure (★★★ `tendsto_normalised_partitionObs_extremal_all`,
`partitionObs_isEquivalent_extremal_all`), and the leading coefficient of the partition function
is the total mass `Γ(λ*)/(m*−1)! · ρ^{λ*}_{m*}(U)` (`coeff_one_eq_mass_leadingResidueMeasureU`).
-/

open MeasureTheory Set Filter Topology Asymptotics
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing Grammar.NormalCrossing.EvenChartBoxDepth

namespace Grammar

namespace SmoothEngine

/-! ### The two normalisation conventions -/

/-- `Z(N)/(N^{−λ} (log N)^k) → c` iff `N^λ (log N)^{−k} Z(N) → c`. -/
theorem hasLeadingTerm_iff_tendsto_normalised {Z : ℝ → ℝ} {c lam : ℝ} {k : ℕ} :
    HasLeadingTerm Z c lam k ↔ Tendsto (normalised lam k Z) atTop (𝓝 c) := by
  unfold HasLeadingTerm
  refine tendsto_congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  unfold normalised powLogScale
  rw [Real.rpow_neg hN.le, div_eq_mul_inv, mul_inv, inv_inv, div_eq_mul_inv]
  ring

namespace ResolvedData

variable {d : ℕ} (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-! ### The wall multiset of a piece and the certificate -/

/-- The wall multiset `{(k_i, h_i) : i}` of a piece of the transport. -/
noncomputable def pieceWalls (p : (Ξ.X Y).PIdx) : Multiset (ℕ × ℕ) :=
  (Finset.univ : Finset (Fin ((Ξ.X Y).da p))).val.map fun i => ((Ξ.X Y).kA p i, (Ξ.X Y).hA p i)

/-- The intrinsic pair data of the divisor point at the origin of the box is the wall multiset of
the piece. -/
theorem pairs_divPt_zero (p : (Ξ.X Y).PIdx) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1)) :
    pairs Ξ.R Ξ.hK0 (Ξ.divPt Y p s 0) = Ξ.pieceWalls Y p := by
  have h0 : (0 : Fin ((Ξ.X Y).da p) → ℝ) ∈ closedBox _ (Y.T.a p.1) :=
    mem_closedBox.2 fun i => ⟨le_rfl, (Y.T.a_pos p.1).le⟩
  rw [pairs_eq_of_mem_source Ξ.R Ξ.hK0 (Y.evenChartBox p.1) (Ξ.divPt_mem_source Y p s h0),
    Y.evenChartBox_φ, Ξ.φ_divPt Y p s h0,
    Ξ.wallsAt_facePt_eq Y p s (J := Finset.univ) (fun i => by simp), Finset.map_val,
    Multiset.map_map]
  rfl

/-- **The extremal certificate**: the wall multiset of every piece sits inside the intrinsic pair
data of some point of the zero fibre. -/
def ExtremalCertificate : Prop :=
  ∀ p : (Ξ.X Y).PIdx, ∃ P ∈ Ξ.zeroFibre, Ξ.pieceWalls Y p ≤ pairs Ξ.R Ξ.hK0 P

/-- The certificate holds when every piece has a box origin in the zero fibre. -/
theorem extremalCertificate_of_divPt_zero
    (h : ∀ p : (Ξ.X Y).PIdx, ∃ s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1),
      Ξ.divPt Y p s 0 ∈ Ξ.zeroFibre) :
    Ξ.ExtremalCertificate Y := fun p => by
  obtain ⟨s, hs⟩ := h p
  exact ⟨_, hs, (Ξ.pairs_divPt_zero Y p s).symm ▸ le_rfl⟩

/-- A wall of ratio exactly `λ` resonates with `λ`. -/
theorem resonates_of_ratioExp_eq {h k : Fin d → ℕ} {lam : ℝ} {i : Fin d} (hk : 0 < k i)
    (hi : ratioExp h k i = lam) : Resonates lam (k i, h i) := by
  refine ⟨0, ?_⟩
  unfold ratioExp at hi
  have hk' : (0 : ℝ) < k i := by exact_mod_cast hk
  rw [← hi]
  push_cast
  field_simp
  ring

open Classical in
/-- ★★ **Extremal data plus the certificate give the chart-leading condition**. -/
theorem chartLeading_of_extremalData {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    (hc : Ξ.ExtremalCertificate Y) : Ξ.ChartLeading Y lam m := by
  intro p
  obtain ⟨P, hP, hle⟩ := hc p
  have hmem : ∀ i, ((Ξ.X Y).kA p i, (Ξ.X Y).hA p i) ∈ pairs Ξ.R Ξ.hK0 P := fun i =>
    Multiset.mem_of_le hle (Multiset.mem_map.2 ⟨i, Finset.mem_univ_val _, rfl⟩)
  refine ⟨fun i => ?_, ?_⟩
  · have hi := h.1 P hP _ (hmem i)
    have hk : (0 : ℝ) < (Ξ.X Y).kA p i := by exact_mod_cast (Ξ.X Y).kA_pos p i
    unfold ratioExp
    rw [le_div_iff₀ (by positivity)]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hi
  · calc multCount (ratioExp ((Ξ.X Y).hA p) ((Ξ.X Y).kA p)) lam
        = ((Finset.univ.filter fun i =>
            ratioExp ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) i = lam).val).card := by
          rw [multCount, ← Finset.card_filter, Finset.card_def]
      _ ≤ ((Ξ.pieceWalls Y p).filter (Resonates lam)).card := by
          unfold pieceWalls
          rw [Multiset.filter_map, Multiset.card_map, Finset.filter_val]
          exact Multiset.card_le_card (Multiset.monotone_filter_right _ fun i hi =>
            resonates_of_ratioExp_eq ((Ξ.X Y).kA_pos p i) hi)
      _ ≤ ((pairs Ξ.R Ξ.hK0 P).filter (Resonates lam)).card :=
          Multiset.card_le_card (Multiset.filter_le_filter _ hle)
      _ = resonanceCount Ξ.R Ξ.hK0 lam P := rfl
      _ ≤ m := h.2 P hP

/-! ### The population coefficient functional at the extremal pair -/

/-- ★★★ **The extremal coefficient functional is the raw leading measure** for every smooth
observable: `𝒯^U_{λ*,m*−1}[G] = Γ(λ*)/(m*−1)! · ∫_U G dρ^{λ*}_{m*}`. -/
theorem coeff_withF_eq_integral_leadingResidueMeasureU {lam : ℝ} {m : ℕ}
    (h : Ξ.IsExtremalData lam m) (hc : Ξ.ExtremalCertificate Y) (hμ : 0 < lam) (hm : 1 ≤ m)
    {G : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) :
    (Ξ.withF G hG).coeff Y lam (m - 1) =
      residueConst lam m * ∫ x, G x ∂(Ξ.leadingResidueMeasureU Y lam m) :=
  tendsto_nhds_unique (Ξ.tendsto_normalised_Z_of_extremalData Y h hG)
    (hasLeadingTerm_iff_tendsto_normalised.1
      ((Ξ.withF G hG).hasLeadingTerm_Z_eq_integral_leadingResidueMeasureU Y hμ hm
        (Ξ.chartLeading_of_extremalData Y h hc)))

/-- The leading coefficient of the partition function is the total mass
`Γ(λ*)/(m*−1)! · ρ^{λ*}_{m*}(U)` of the raw leading measure. -/
theorem coeff_one_eq_mass_leadingResidueMeasureU {lam : ℝ} {m : ℕ}
    (h : Ξ.IsExtremalData lam m) (hc : Ξ.ExtremalCertificate Y) (hμ : 0 < lam) (hm : 1 ≤ m) :
    (Ξ.withF (fun _ => (1 : ℝ)) contMDiff_const).coeff Y lam (m - 1) =
      residueConst lam m * (Ξ.leadingResidueMeasureU Y lam m).real univ := by
  rw [Ξ.coeff_withF_eq_integral_leadingResidueMeasureU Y h hc hμ hm contMDiff_const,
    integral_const, smul_eq_mul, mul_one]

/-! ### Downstairs: every smooth observable -/

/-- ★★★ **The leading asymptotic downstairs for every smooth observable**:
`N^{λ*} (log N)^{−(m*−1)} ∫ prior · f · e^{−NK} → Γ(λ*)/(m*−1)! · ∫_U f ∘ π dρ^{λ*}_{m*}`. -/
theorem tendsto_normalised_partitionObs_extremal_all {f : (Fin d → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    (hc : Ξ.ExtremalCertificate Y) (hμ : 0 < lam) (hm : 1 ≤ m) :
    Tendsto (normalised lam (m - 1) (partitionObs Ξ.K Ξ.prior f)) atTop
      (𝓝 (residueConst lam m *
        ∫ x, f (Ξ.R.gv x) ∂(Ξ.leadingResidueMeasureU Y lam m))) := by
  have key := Ξ.tendsto_normalised_Z_of_extremalData Y h (Ξ.contMDiff_comp_gv hf)
  rw [Ξ.coeff_withF_eq_integral_leadingResidueMeasureU Y h hc hμ hm] at key
  refine key.congr fun N => ?_
  unfold normalised
  rw [Ξ.Z_withF_comp_gv hf N]

/-- ★★★ **The leading asymptotic with insertion, for every smooth observable**: when
`∫ f ∘ π dρ^{λ*}_{m*} ≠ 0`,
`∫ prior · f · e^{−NK} ∼ Γ(λ*)/(m*−1)! (∫ f ∘ π dρ^{λ*}_{m*}) N^{−λ*} (log N)^{m*−1}`. -/
theorem partitionObs_isEquivalent_extremal_all {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m) (hc : Ξ.ExtremalCertificate Y)
    (hμ : 0 < lam) (hm : 1 ≤ m)
    (hne : ∫ x, f (Ξ.R.gv x) ∂(Ξ.leadingResidueMeasureU Y lam m) ≠ 0) :
    (fun N => partitionObs Ξ.K Ξ.prior f N) ~[atTop]
      fun N => (residueConst lam m * ∫ x, f (Ξ.R.gv x) ∂(Ξ.leadingResidueMeasureU Y lam m)) *
        (N ^ (-lam) * Real.log N ^ (m - 1)) := by
  set I := residueConst lam m * ∫ x, f (Ξ.R.gv x) ∂(Ξ.leadingResidueMeasureU Y lam m) with hI
  have hIne : I ≠ 0 := mul_ne_zero (residueConst_pos hμ m).ne' hne
  have hv : ∀ᶠ N : ℝ in atTop, I * (N ^ (-lam) * Real.log N ^ (m - 1)) ≠ 0 := by
    filter_upwards [eventually_gt_atTop 1] with N hN
    exact mul_ne_zero hIne (mul_pos (Real.rpow_pos_of_pos (by linarith) _)
      (pow_pos (Real.log_pos hN) _)).ne'
  refine (Asymptotics.isEquivalent_iff_tendsto_one hv).2 ?_
  have hlim := (Ξ.tendsto_normalised_partitionObs_extremal_all Y hf h hc hμ hm).div_const I
  rw [div_self hIne] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with N hN
  have hN0 : 0 ≤ N := by linarith
  have hA : (N ^ lam : ℝ) ≠ 0 := (Real.rpow_pos_of_pos (by linarith) _).ne'
  have hL : (Real.log N ^ (m - 1) : ℝ) ≠ 0 := (pow_pos (Real.log_pos hN) _).ne'
  simp only [Pi.div_apply]
  unfold normalised
  rw [Real.rpow_neg hN0]
  field_simp

end ResolvedData

end SmoothEngine

end Grammar
