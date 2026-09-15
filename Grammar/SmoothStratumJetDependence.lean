/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothStratumTest
import Grammar.SmoothRenormalisedStrata

/-!
# Jet dependence of the stratum coefficients (chart-free)

The `(μ, c−1)` coefficient of an observable `F` vanishing near the deep zero fibre depends on `F`
only through a finite transverse jet along the exact stratum `S^μ_c`, and the order of that jet
is intrinsic. Both halves of the statement are chart-free:

* `VanishesToOrderAt n H P`: near `P`, `H` is a finite sum of smooth multiples of products of `n`
  smooth functions each vanishing at `P` (equivalently, the `(n−1)`-jet of `H` at `P` is zero);
  `MemIdealPowNear S n H P` is the ideal-theoretic form `H ∈ 𝓘_S^n` near `P` (the factors vanish
  on `S`). Exponent `0` imposes nothing.
* `stratumJetOrder μ P = Σ_{(k,h)} (⌊2kμ⌋₊ − h − 1)` over the intrinsic wall pairs through `P`;
  at a point of the exact stratum it is the total resonant Taylor order `|α|` of the face formula
  (`stratumJetOrder_divPt_eq`), and it vanishes under the zero-order condition.

Main results: `coeff_eq_zero_of_vanishesToOrder` (an observable vanishing near `D_{c+1}` and
to order `stratumJetOrder μ P + 1` at every `P ∈ S^μ_c` has zero coefficient),
`coeff_eq_of_vanishesToOrder` / `coeff_eq_of_memIdealPow` (two observables whose difference lies
in `𝓘_{S^μ_c}^{|α|+1}` near the stratum have the same coefficient), and the test-functional form
`T_eq_of_memIdealPow`. No zero-order hypothesis is needed. The calculus input is the Leibniz
rule: derivatives of order `< n` of a product of `n` functions vanishing at a point vanish there
(`pdMulti_prod_eq_zero_of_forall_eq_zero`). Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing Grammar.NormalCrossing.EvenChartBoxDepth

namespace Grammar

namespace SmoothEngine

variable {d : ℕ}

/-! ### Calculus: coordinate derivatives of differences and of vanishing products -/

theorem pdMulti_sub {F F' : (Fin d → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F) (hF' : ContDiff ℝ ∞ F')
    (m : Fin d → ℕ) (l : List (Fin d)) :
    pdMulti m l (fun v => F v - F' v) = fun v => pdMulti m l F v - pdMulti m l F' v := by
  have h := pdMulti_finset_sum (s := (Finset.univ : Finset (Fin 2))) (![1, -1] : Fin 2 → ℝ)
    (G := ![F, F']) (fun b _ => by fin_cases b <;> simp [hF, hF']) m l
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul,
    neg_one_mul] at h
  have e : (fun v => F v - F' v) = fun v => F v + -F' v := by
    funext v
    ring
  rw [e, h]
  funext v
  ring

/-- Two smooth functions agreeing on `O ∩ closedBox` (`O` open) have the same coordinate
derivatives at every point of `O ∩ closedBox`. -/
theorem pdMulti_eq_of_eqOn_inter_closedBox {F F' : (Fin d → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F)
    (hF' : ContDiff ℝ ∞ F') {b : ℝ} (hb : 0 < b) {O : Set (Fin d → ℝ)} (hO : IsOpen O)
    (h : ∀ v ∈ O ∩ closedBox d b, F v = F' v) {v₀ : Fin d → ℝ} (hv₀ : v₀ ∈ O ∩ closedBox d b)
    (α : Fin d → ℕ) : pdMulti α (List.finRange d) F v₀ = pdMulti α (List.finRange d) F' v₀ := by
  have h0 := pdMulti_eq_zero_of_eqOn_inter_closedBox (hF.sub hF') hb hO
    (fun v hv => sub_eq_zero.2 (h v hv)) hv₀ α
  rw [pdMulti_sub hF hF'] at h0
  exact sub_eq_zero.1 h0

/-- ★ **Vanishing products**: a coordinate derivative of total order `< n` of a product of `n`
smooth functions all vanishing at `v₀` vanishes at `v₀` (Leibniz: some factor is left
undifferentiated). -/
theorem pdMulti_prod_eq_zero_of_forall_eq_zero {n : ℕ} :
    ∀ {G : Fin n → (Fin d → ℝ) → ℝ}, (∀ l, ContDiff ℝ ∞ (G l)) → ∀ {v₀ : Fin d → ℝ},
      (∀ l, G l v₀ = 0) → ∀ {α : Fin d → ℕ}, ∑ i, α i < n →
      pdMulti α (List.finRange d) (fun v => ∏ l, G l v) v₀ = 0 := by
  induction n with
  | zero =>
    intro G _ v₀ _ α hα
    exact absurd hα (Nat.not_lt_zero _)
  | succ n ih =>
    intro G hG v₀ h0 α hα
    have hprod : ContDiff ℝ ∞ fun v => ∏ l : Fin n, G l.succ v :=
      contDiff_prod fun l _ => hG l.succ
    have e : (fun v => ∏ l, G l v) = fun v => G 0 v * ∏ l : Fin n, G l.succ v := by
      funext v
      exact Fin.prod_univ_succ _
    rw [e, pdMulti_mul (hG 0) hprod α (List.nodup_finRange d)]
    beta_reduce
    refine Finset.sum_eq_zero fun β hβ => ?_
    by_cases hβ0 : β = 0
    · subst hβ0
      rw [pdMulti_zero, h0 0, zero_mul, mul_zero]
    · have hle : ∀ i, β i ≤ α i := fun i => by
        have := (mem_idxL_iff.1 hβ) i
        simp only [List.mem_finRange, if_true, Finset.mem_range] at this
        omega
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hβ0
      have hsum : ∑ j, (α - β) j < n := by
        have h1 : ∑ j, (α - β) j + ∑ j, β j = ∑ j, α j := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun j _ => by
            rw [Pi.sub_apply, Nat.sub_add_cancel (hle j)]
        have h2 : 1 ≤ ∑ j, β j :=
          le_trans (Nat.one_le_iff_ne_zero.2 hi)
            (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
        omega
      rw [ih (fun l => hG l.succ) (fun l => h0 l.succ) hsum, mul_zero, mul_zero]

namespace ResolvedData

variable (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-! ### Chart-free vanishing orders -/

/-- **Vanishing to order `n` at `P`**: near `P`, `H` is a finite sum of smooth multiples of
products of `n` smooth functions each vanishing at `P` (`H ∈ 𝔪_P^n` near `P`; the `(n−1)`-jet of `H`
at `P` is zero). For `n = 0` every smooth `H` qualifies. -/
def VanishesToOrderAt (n : ℕ) (H : Ξ.R.U → ℝ) (P : Ξ.R.U) : Prop :=
  ∃ N ∈ 𝓝 P, ∃ (ι : Type) (_ : Fintype ι) (a : ι → Ξ.R.U → ℝ) (g : ι → Fin n → Ξ.R.U → ℝ),
    (∀ i, ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ (a i)) ∧
    (∀ i l, ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ (g i l)) ∧ (∀ i l, g i l P = 0) ∧
    ∀ Q ∈ N, H Q = ∑ i, a i Q * ∏ l, g i l Q

/-- **`H ∈ 𝓘_S^n` near `P`**: near `P`, `H` is a finite sum of smooth multiples of products of `n`
smooth functions each vanishing on `S`. For `n = 0` every smooth `H` qualifies. -/
def MemIdealPowNear (S : Set Ξ.R.U) (n : ℕ) (H : Ξ.R.U → ℝ) (P : Ξ.R.U) : Prop :=
  ∃ N ∈ 𝓝 P, ∃ (ι : Type) (_ : Fintype ι) (a : ι → Ξ.R.U → ℝ) (g : ι → Fin n → Ξ.R.U → ℝ),
    (∀ i, ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ (a i)) ∧
    (∀ i l, ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ (g i l)) ∧ (∀ i l, ∀ Q ∈ S, g i l Q = 0) ∧
    ∀ Q ∈ N, H Q = ∑ i, a i Q * ∏ l, g i l Q

variable {Ξ} in
theorem MemIdealPowNear.vanishesToOrderAt {S : Set Ξ.R.U} {n : ℕ} {H : Ξ.R.U → ℝ} {P : Ξ.R.U}
    (h : Ξ.MemIdealPowNear S n H P) (hP : P ∈ S) : Ξ.VanishesToOrderAt n H P := by
  obtain ⟨N, hN, ι, _, a, g, ha, hg, hg0, hH⟩ := h
  exact ⟨N, hN, ι, inferInstance, a, g, ha, hg, fun i l => hg0 i l P hP, hH⟩

variable {Ξ} in
theorem VanishesToOrderAt.congr {n : ℕ} {H H' : Ξ.R.U → ℝ} {P : Ξ.R.U}
    (h : Ξ.VanishesToOrderAt n H P) (hHH' : ∀ Q, H Q = H' Q) : Ξ.VanishesToOrderAt n H' P := by
  obtain ⟨N, hN, ι, _, a, g, ha, hg, hg0, hH⟩ := h
  exact ⟨N, hN, ι, inferInstance, a, g, ha, hg, hg0, fun Q hQ => (hHH' Q).symm.trans (hH Q hQ)⟩

/-- Exponent zero imposes nothing on a smooth function. -/
theorem memIdealPowNear_zero (S : Set Ξ.R.U) {H : Ξ.R.U → ℝ}
    (hH : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ H) (P : Ξ.R.U) : Ξ.MemIdealPowNear S 0 H P :=
  ⟨univ, univ_mem, Unit, inferInstance, fun _ => H, fun _ => Fin.elim0, fun _ => hH,
    fun _ l => Fin.elim0 l, fun _ l => Fin.elim0 l, fun Q _ => by simp⟩

/-- Order one is plain vanishing at the point. -/
theorem vanishesToOrderAt_one_of_eq_zero {H : Ξ.R.U → ℝ}
    (hH : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ H) {P : Ξ.R.U} (h0 : H P = 0) :
    Ξ.VanishesToOrderAt 1 H P :=
  ⟨univ, univ_mem, Unit, inferInstance, fun _ _ => 1, fun _ _ => H, fun _ => contMDiff_const,
    fun _ _ => hH, fun _ _ => h0, fun Q _ => by simp⟩

/-- Order one on `S` is plain vanishing on `S`. -/
theorem memIdealPowNear_one_of_eqOn_zero (S : Set Ξ.R.U) {H : Ξ.R.U → ℝ}
    (hH : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ H) (h0 : ∀ Q ∈ S, H Q = 0) (P : Ξ.R.U) :
    Ξ.MemIdealPowNear S 1 H P :=
  ⟨univ, univ_mem, Unit, inferInstance, fun _ _ => 1, fun _ _ => H, fun _ => contMDiff_const,
    fun _ _ => hH, fun _ _ => h0, fun Q _ => by simp⟩

/-! ### The intrinsic transverse jet order -/

/-- The intrinsic transverse jet order at `P`: `Σ_{(k,h)} (⌊2kμ⌋₊ − h − 1)` over the wall pairs
through `P`. At a point of the exact stratum this is the total resonant Taylor order `|α|`. -/
noncomputable def stratumJetOrder (μ : ℝ) (P : Ξ.R.U) : ℕ :=
  ((pairs Ξ.R Ξ.hK0 P).map fun q => ⌊2 * (q.1 : ℝ) * μ⌋₊ - q.2 - 1).sum

theorem stratumJetOrder_eq_zero_of_zeroOrder {μ : ℝ} {c : ℕ} (hzero : Ξ.ZeroOrder μ c)
    {P : Ξ.R.U} (hP : P ∈ Ξ.exactStratum μ c) : Ξ.stratumJetOrder μ P = 0 := by
  unfold stratumJetOrder
  refine Multiset.sum_eq_zero fun x hx => ?_
  obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.1 hx
  have h : ⌊2 * (q.1 : ℝ) * μ⌋₊ = q.2 + 1 := by
    rw [hzero P hP q hq, ← Nat.cast_succ, Nat.floor_natCast]
  omega

/-- At a face point of a piece the intrinsic jet order is the total resonant Taylor order of the
face. -/
theorem stratumJetOrder_divPt_eq (p : (Ξ.X Y).PIdx) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1))
    {J : Finset (Fin ((Ξ.X Y).da p))} {w : {i // ¬ inJ J i} → ℝ}
    (hw : w ∈ box {i // ¬ inJ J i} (Y.T.a p.1)) (μ : ℝ) :
    Ξ.stratumJetOrder μ (Ξ.divPt Y p s (glue J 0 w)) =
      ∑ i, resOrder ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) μ J i := by
  have hv : glue J 0 w ∈ closedBox _ (Y.T.a p.1) := Ξ.glue_zero_mem_closedBox Y p J hw
  have hJ : ∀ i, glue J 0 w i = 0 ↔ i ∈ J := Ξ.glue_zero_eq_zero_iff Y p J hw
  unfold stratumJetOrder
  rw [pairs_eq_of_mem_source Ξ.R Ξ.hK0 (Y.evenChartBox p.1) (Ξ.divPt_mem_source Y p s hv),
    Y.evenChartBox_φ, Ξ.φ_divPt Y p s hv, Ξ.wallsAt_facePt_eq Y p s hJ, Finset.map_val,
    Multiset.map_map, Multiset.map_map, ← Finset.sum_eq_multiset_sum,
    ← Finset.sum_subset (Finset.subset_univ J) fun i _ hi => resOrder_of_not_mem hi]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Function.comp, resOrder, if_pos hi]
  rfl

/-! ### Jets of the piece amplitude at a face point -/

theorem exists_contDiff_eqOn_comp_chartInv {H : Ξ.R.U → ℝ}
    (hH : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ H) (i : Y.T.ι) :
    ∃ g : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ g ∧
      EqOn g (fun u => H (Y.chartInv i u)) (centeredBox d (Y.T.a i)) := by
  obtain ⟨g, hg, heq, -⟩ := exists_contDiff_eqOn_of_contDiffOn (Y.φ i).open_target
    (isCompact_centeredBox d (Y.T.a i)).isClosed (Y.box_subset_target i)
    (Y.contDiffOn_comp_chartInv hH i)
  exact ⟨g, hg, heq⟩

theorem contDiff_facePt (p : (Ξ.X Y).PIdx) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1)) :
    ContDiff ℝ ∞ (Ξ.facePt Y p s) :=
  contDiff_affineMap _ _ _

/-- ★★ **Vanishing jets from vanishing order**: if `F` vanishes to order `|α| + 1` at the divisor
point of a chart point `v₀` of the box, the `α`-th coordinate derivative of the piece amplitude
vanishes at `v₀`. -/
theorem pdMulti_amp_eq_zero_of_vanishesToOrder (p : (Ξ.X Y).PIdx)
    (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1)) {v₀ : Fin ((Ξ.X Y).da p) → ℝ}
    (hv : v₀ ∈ closedBox _ (Y.T.a p.1)) {α : Fin ((Ξ.X Y).da p) → ℕ}
    (hF : Ξ.VanishesToOrderAt (∑ i, α i + 1) Ξ.F (Ξ.divPt Y p s v₀)) :
    pdMulti α (List.finRange _) ((Ξ.amp Y p).amp s) v₀ = 0 := by
  obtain ⟨N, hN, ι, _, a, g, ha, hg, hg0, hFg⟩ := hF
  obtain ⟨N', hN'N, hN'o, hPN'⟩ := mem_nhds_iff.1 hN
  have hbox : IsClosed (centeredBox d (Y.T.a p.1)) := (isCompact_centeredBox d _).isClosed
  choose gt hgt hgteq using fun (i : ι) (l : Fin (∑ i, α i + 1)) =>
    Ξ.exists_contDiff_eqOn_comp_chartInv Y (hg i l) p.1
  choose aT hat hateq using fun (i : ι) => Ξ.exists_contDiff_eqOn_comp_chartInv Y (ha i) p.1
  obtain ⟨ρt, hρt, hρteq, -⟩ := exists_contDiff_eqOn_of_contDiffOn (Y.T.V_open p.1) hbox
    (Y.T.box_subset_V p.1) ((Ξ.X Y).contDiffOn_ρloc p.1)
  have hfp := Ξ.contDiff_facePt Y p s
  have hDi : ∀ i : ι, ContDiff ℝ ∞ fun v => ρt (Ξ.facePt Y p s v) * aT i (Ξ.facePt Y p s v) :=
    fun i => (hρt.comp hfp).mul ((hat i).comp hfp)
  have hAi : ∀ i : ι, ContDiff ℝ ∞ fun v =>
      ρt (Ξ.facePt Y p s v) * aT i (Ξ.facePt Y p s v) * ∏ l, gt i l (Ξ.facePt Y p s v) :=
    fun i => (hDi i).mul (contDiff_prod fun l _ => (hgt i l).comp hfp)
  have hAs : ContDiff ℝ ∞ fun v => ∑ i, (1 : ℝ) *
      (ρt (Ξ.facePt Y p s v) * aT i (Ξ.facePt Y p s v) * ∏ l, gt i l (Ξ.facePt Y p s v)) :=
    ContDiff.sum fun i _ => contDiff_const.mul (hAi i)
  have hO : IsOpen (Ξ.facePt Y p s ⁻¹' ((Y.φ p.1).target ∩ (Y.φ p.1).symm ⁻¹' N')) :=
    ((Y.φ p.1).continuousOn_symm.isOpen_inter_preimage (Y.φ p.1).open_target hN'o).preimage
      (Ξ.continuous_facePt Y p s)
  have hv₀O : v₀ ∈ Ξ.facePt Y p s ⁻¹' ((Y.φ p.1).target ∩ (Y.φ p.1).symm ⁻¹' N') :=
    ⟨Ξ.facePt_mem_target Y p s hv, hPN'⟩
  have heq : ∀ v ∈ Ξ.facePt Y p s ⁻¹' ((Y.φ p.1).target ∩ (Y.φ p.1).symm ⁻¹' N') ∩
      closedBox _ (Y.T.a p.1), (Ξ.amp Y p).amp s v = ∑ i, (1 : ℝ) *
        (ρt (Ξ.facePt Y p s v) * aT i (Ξ.facePt Y p s v) * ∏ l, gt i l (Ξ.facePt Y p s v)) := by
    intro v hv'
    have hub := Ξ.facePt_mem_box Y p s hv'.2
    have hut := Ξ.facePt_mem_target Y p s hv'.2
    rw [Ξ.amp_apply, Ξ.G_eq Y p.1 hub]
    unfold Gloc
    rw [Y.chartInv_eq p.1 hut]
    change (Ξ.X Y).ρloc p.1 _ * Ξ.F (Ξ.divPt Y p s v) = _
    rw [hFg (Ξ.divPt Y p s v) (hN'N hv'.1.2), ← hρteq hub, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [one_mul, ← mul_assoc]
    congr 1
    · rw [hateq i hub]
      change ρt _ * a i (Ξ.divPt Y p s v) = ρt _ * a i (Y.chartInv p.1 (Ξ.facePt Y p s v))
      rw [Y.chartInv_eq p.1 hut]
      rfl
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [hgteq i l hub]
    change g i l (Ξ.divPt Y p s v) = g i l (Y.chartInv p.1 (Ξ.facePt Y p s v))
    rw [Y.chartInv_eq p.1 hut]
    rfl
  rw [pdMulti_eq_of_eqOn_inter_closedBox ((Ξ.amp Y p).smooth s) hAs (Y.T.a_pos p.1) hO heq
    ⟨hv₀O, hv⟩ α, pdMulti_finset_sum (fun _ => (1 : ℝ)) (fun i _ => hAi i)]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [one_mul, pdMulti_mul (D := fun v => ρt (Ξ.facePt Y p s v) * aT i (Ξ.facePt Y p s v))
    (f := fun v => ∏ l, gt i l (Ξ.facePt Y p s v)) (hDi i)
    (contDiff_prod fun l _ => (hgt i l).comp hfp) α (List.nodup_finRange _)]
  beta_reduce
  refine Finset.sum_eq_zero fun β _ => ?_
  have hg0' : ∀ l, gt i l (Ξ.facePt Y p s v₀) = 0 := fun l => by
    rw [hgteq i l (Ξ.facePt_mem_box Y p s hv)]
    change g i l (Y.chartInv p.1 (Ξ.facePt Y p s v₀)) = 0
    rw [Y.chartInv_eq p.1 (Ξ.facePt_mem_target Y p s hv)]
    exact hg0 i l
  have hlt : ∑ j, (α - β) j < ∑ j, α j + 1 :=
    calc ∑ j, (α - β) j ≤ ∑ j, α j := Finset.sum_le_sum fun j _ => Nat.sub_le _ _
      _ < ∑ j, α j + 1 := Nat.lt_succ_self _
  rw [pdMulti_prod_eq_zero_of_forall_eq_zero (G := fun l v => gt i l (Ξ.facePt Y p s v))
    (fun l => (hgt i l).comp hfp) hg0' hlt, mul_zero, mul_zero]

/-- At an exactly resonant face of size `c`, the resonant derivative of the amplitude vanishes
when `F` vanishes to order `stratumJetOrder + 1` along the exact stratum. -/
theorem pdMulti_amp_glue_eq_zero_of_vanishesToOrder {μ : ℝ} {c : ℕ} (hc : 1 ≤ c)
    (hF : ∀ P ∈ Ξ.exactStratum μ c, Ξ.VanishesToOrderAt (Ξ.stratumJetOrder μ P + 1) Ξ.F P)
    (p : (Ξ.X Y).PIdx) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1))
    {J : Finset (Fin ((Ξ.X Y).da p))} (hJc : J.card = c)
    (hex : ∀ i ∈ J, 2 * ((Ξ.X Y).kA p i : ℝ) * μ =
      resOrder ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) μ J i + (Ξ.X Y).hA p i + 1)
    {w : {i // ¬ inJ J i} → ℝ} (hw : w ∈ box {i // ¬ inJ J i} (Y.T.a p.1)) :
    pdMulti (resOrder ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) μ J) (List.finRange _)
      ((Ξ.amp Y p).amp s) (glue J 0 w) = 0 := by
  have hv : glue J 0 w ∈ closedBox _ (Y.T.a p.1) := Ξ.glue_zero_mem_closedBox Y p J hw
  have hJ : ∀ i, glue J 0 w i = 0 ↔ i ∈ J := Ξ.glue_zero_eq_zero_iff Y p J hw
  have hJne : J.Nonempty := Finset.card_pos.1 (by omega)
  by_cases hsupp : Ξ.R.gv (Ξ.divPt Y p s (glue J 0 w)) ∈ tsupport Ξ.prior
  · have hres : ∀ i ∈ J, Resonates μ ((Ξ.X Y).kA p i, (Ξ.X Y).hA p i) := fun i hi =>
      ⟨resOrder ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) μ J i, by
        have := hex i hi
        simp only
        linarith⟩
    have hmem : Ξ.divPt Y p s (glue J 0 w) ∈ Ξ.exactStratum μ c :=
      ⟨⟨hsupp, Ξ.phase_divPt_eq_zero Y p s hv hJne fun i hi => (hJ i).2 hi⟩,
        by rw [Ξ.depth_divPt_eq Y p s hv hJ, hJc],
        by rw [Ξ.resonanceCount_divPt_eq Y p s hv hJ hres, hJc]⟩
    have hF' := hF _ hmem
    rw [Ξ.stratumJetOrder_divPt_eq Y p s hw μ] at hF'
    exact Ξ.pdMulti_amp_eq_zero_of_vanishesToOrder Y p s hv hF'
  · exact Ξ.pdMulti_amp_eq_zero_of_not_mem_tsupport Y p s hv hsupp _

/-! ### The coefficient theorems -/

theorem pieceStratumSum_eq_zero_of_vanishesToOrder {μ : ℝ} {c : ℕ} (hc : 1 ≤ c)
    (hF : ∀ P ∈ Ξ.exactStratum μ c, Ξ.VanishesToOrderAt (Ξ.stratumJetOrder μ P + 1) Ξ.F P)
    (I : Fin (Fintype.card (Ξ.X Y).PIdx))
    (s : Base ((Ξ.X Y).act ((Ξ.X Y).en I).1) (Y.T.a ((Ξ.X Y).en I).1)) :
    Ξ.pieceStratumSum Y I s μ c = 0 := by
  unfold pieceStratumSum
  simp only [Ξ.chart_k Y, Ξ.chart_h Y, Ξ.chart_b Y, Ξ.chart_βf Y, Ξ.chart_amp Y]
  refine Finset.sum_eq_zero fun J hJ => ?_
  have hJc : J.card = c := (Finset.mem_filter.1 hJ).2
  have hDJ : DJ J = c - 1 := by rw [DJ_eq, hJc]
  by_cases hex : ∀ i ∈ J, 2 * ((Ξ.X Y).kA ((Ξ.X Y).en I) i : ℝ) * μ =
      resOrder ((Ξ.X Y).hA ((Ξ.X Y).en I)) ((Ξ.X Y).kA ((Ξ.X Y).en I)) μ J i +
        (Ξ.X Y).hA ((Ξ.X Y).en I) i + 1
  · rw [faceCoeffInt_eq_zero_of_forall _ _ _ _ _ fun w hw => ?_, mul_zero, mul_zero]
    rw [pdMulti_lJ_eq_finRange_of_zero_off ((Ξ.amp Y _).smooth s) J _
      fun i hi => resOrder_of_not_mem hi]
    exact Ξ.pdMulti_amp_glue_eq_zero_of_vanishesToOrder Y hc hF _ s hJc hex hw
  · obtain ⟨i, hi, hne⟩ : ∃ i ∈ J, 2 * ((Ξ.X Y).kA ((Ξ.X Y).en I) i : ℝ) * μ ≠
        resOrder ((Ξ.X Y).hA ((Ξ.X Y).en I)) ((Ξ.X Y).kA ((Ξ.X Y).en I)) μ J i +
          (Ξ.X Y).hA ((Ξ.X Y).en I) i + 1 := by
      by_contra h
      exact hex fun i hi => by_contra fun hne => h ⟨i, hi, hne⟩
    rw [← hDJ, faceCoef_top_eq_zero_of_not_exact _ ((Ξ.X Y).kA_pos _) (Y.T.phaseConst_pos _)
      (Y.T.a_pos _) J _ hi (by push_cast; exact hne), zero_mul, mul_zero]

theorem stratumSum_eq_zero_of_vanishesToOrder {μ : ℝ} {c : ℕ} (hc : 1 ≤ c)
    (hF : ∀ P ∈ Ξ.exactStratum μ c, Ξ.VanishesToOrderAt (Ξ.stratumJetOrder μ P + 1) Ξ.F P) :
    Ξ.stratumSum Y μ c = 0 :=
  Finset.sum_eq_zero fun I _ => integral_eq_zero_of_ae (Eventually.of_forall fun s =>
    Ξ.pieceStratumSum_eq_zero_of_vanishesToOrder Y hc hF I s)

/-- ★★★ **Vanishing coefficient from vanishing transverse jets**: an observable vanishing near the
deep zero fibre and to order `stratumJetOrder μ P + 1` at every point `P` of the exact stratum
has zero `(μ, c−1)` coefficient. No zero-order hypothesis. -/
theorem coeff_eq_zero_of_vanishesToOrder {μ : ℝ} {c : ℕ} (hc : 1 ≤ c)
    (hF0 : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0)
    (hF : ∀ P ∈ Ξ.exactStratum μ c, Ξ.VanishesToOrderAt (Ξ.stratumJetOrder μ P + 1) Ξ.F P) :
    Ξ.coeff Y μ (c - 1) = 0 := by
  rw [Ξ.coeff_eq_stratumSum Y hc hF0 μ]
  exact Ξ.stratumSum_eq_zero_of_vanishesToOrder Y hc hF

/-- ★★★ **Jet dependence of the stratum coefficient** (chart-free): two observables vanishing near
the deep zero fibre whose difference vanishes to order `stratumJetOrder μ P + 1` at every point
`P` of the exact stratum `S^μ_c` have the same `(μ, c−1)` coefficient. -/
theorem coeff_eq_of_vanishesToOrder {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) {G G' : Ξ.R.U → ℝ}
    (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) (hG' : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G')
    (hG0 : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), G P = 0)
    (hG0' : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), G' P = 0)
    (hjet : ∀ P ∈ Ξ.exactStratum μ c,
      Ξ.VanishesToOrderAt (Ξ.stratumJetOrder μ P + 1) (fun P => G P - G' P) P) :
    (Ξ.withF G hG).coeff Y μ (c - 1) = (Ξ.withF G' hG').coeff Y μ (c - 1) := by
  have hG'' : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ (fun P => (-1 : ℝ) * G' P) :=
    contMDiff_const.mul hG'
  have hsum : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ (fun P => G P + (-1 : ℝ) * G' P) :=
    hG.add hG''
  have hev : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), G P + (-1 : ℝ) * G' P = 0 := by
    filter_upwards [hG0, hG0'] with P h1 h2
    rw [h1, h2]
    ring
  have hjet' : ∀ P ∈ (Ξ.withF (fun P => G P + (-1 : ℝ) * G' P) hsum).exactStratum μ c,
      (Ξ.withF (fun P => G P + (-1 : ℝ) * G' P) hsum).VanishesToOrderAt
        ((Ξ.withF (fun P => G P + (-1 : ℝ) * G' P) hsum).stratumJetOrder μ P + 1)
        (fun P => G P + (-1 : ℝ) * G' P) P :=
    fun P hP => (hjet P hP).congr fun Q => by ring
  have hdiff := (Ξ.withF (fun P => G P + (-1 : ℝ) * G' P)
    hsum).coeff_eq_zero_of_vanishesToOrder Y hc hev hjet'
  have h1 := Ξ.coeff_add Y hG hG'' μ (c - 1)
  have h2 := Ξ.coeff_smul Y hG' (-1) μ (c - 1)
  linarith

/-- ★★★ **Ideal-power form**: if `G − G' ∈ 𝓘_{S^μ_c}^{stratumJetOrder μ P + 1}` near every point
`P` of the exact stratum, the two `(μ, c−1)` coefficients agree. -/
theorem coeff_eq_of_memIdealPow {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) {G G' : Ξ.R.U → ℝ}
    (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) (hG' : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G')
    (hG0 : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), G P = 0)
    (hG0' : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), G' P = 0)
    (hjet : ∀ P ∈ Ξ.exactStratum μ c, Ξ.MemIdealPowNear (Ξ.exactStratum μ c)
      (Ξ.stratumJetOrder μ P + 1) (fun P => G P - G' P) P) :
    (Ξ.withF G hG).coeff Y μ (c - 1) = (Ξ.withF G' hG').coeff Y μ (c - 1) :=
  Ξ.coeff_eq_of_vanishesToOrder Y hc hG hG' hG0 hG0' fun P hP =>
    (hjet P hP).vanishesToOrderAt hP

/-- The test-functional form: `𝒯[G] = 𝒯[G']` for tests with
`G − G' ∈ 𝓘_{S^μ_c}^{stratumJetOrder + 1}` near the exact stratum. -/
theorem T_eq_of_memIdealPow {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) {G G' : Ξ.R.U → ℝ}
    (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) (hG' : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G')
    (hGt : Ξ.IsTest c G) (hGt' : Ξ.IsTest c G')
    (hjet : ∀ P ∈ Ξ.exactStratum μ c, Ξ.MemIdealPowNear (Ξ.exactStratum μ c)
      (Ξ.stratumJetOrder μ P + 1) (fun P => G P - G' P) P) :
    Ξ.T Y μ c G hG = Ξ.T Y μ c G' hG' :=
  Ξ.coeff_eq_of_memIdealPow Y hc hG hG' hGt.eventually_zero hGt'.eventually_zero hjet

/-- Under the zero-order condition the jet order is zero and the jet hypothesis reduces to
agreement on the exact stratum, recovering `coeff_eq_of_eqOn_exactStratum`. -/
theorem coeff_eq_of_eqOn_exactStratum' {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c)
    {G G' : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G)
    (hG' : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G')
    (hG0 : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), G P = 0)
    (hG0' : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), G' P = 0) (heq : EqOn G G' (Ξ.exactStratum μ c)) :
    (Ξ.withF G hG).coeff Y μ (c - 1) = (Ξ.withF G' hG').coeff Y μ (c - 1) :=
  Ξ.coeff_eq_of_vanishesToOrder Y hc hG hG' hG0 hG0' fun P hP => by
    rw [Ξ.stratumJetOrder_eq_zero_of_zeroOrder hzero hP]
    exact Ξ.vanishesToOrderAt_one_of_eq_zero (hG.sub hG') (sub_eq_zero.2 (heq hP))

end ResolvedData

end SmoothEngine

end Grammar
