/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothStratumMeasurePositive
import Grammar.SmoothStratumMeasureFinite
import Monomialize.Transport.MonomialModification

/-!
# Regression: the monomial phase `∏ x_i^{2k_i}` through the resolved machinery

The identity is a Watanabe modification of the monomial phase (hironaka
`WatanabeModificationOn.ofMonomial`), so a monomial phase with any compactly supported smooth
prior on `W` is an instance of the resolved data (`monomialData`). Its intrinsic wall data are
computed from the centred even chart boxes of the identity modification: at a zero `P` the walls
are the coordinates `i` with `P_i = 0` and `k_i > 0`, each with pair `(k_i, 0)`
(`pairs_monomialData`, `depth_monomialData`, `resonanceCount_monomialData`). The extremal data are
`λ* = 1/(2 k_max)` and `m* = #{i : k_i = k_max}`, realised at the origin
(`isExtremalData_monomial`, `resonanceCount_monomial_zero`), and the abstract RLCT theorem
reproduces the classical monomial asymptotic
`∫ φ e^{−N ∏ x^{2k}} ∼ c N^{−1/(2k_max)} (log N)^{m*−1}`, `c > 0`, for `φ(0) > 0`
(`monomial_rlct_asymptotic`). Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology Asymptotics
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing Grammar.NormalCrossing.EvenChartBoxDepth

namespace Grammar

namespace SmoothEngine

section Monomial

variable {d : ℕ} (k : Fin d → ℕ) (W : TopologicalSpace.Opens (Fin d → ℝ))

theorem continuous_monoPhase : Continuous (monoPhase k) := by
  unfold monoPhase
  fun_prop

/-- ★★ **The monomial resolved data**: the phase `∏ x_i^{2k_i}` on `W`, the identity modification,
a compactly supported smooth nonnegative prior, and the unit observable. -/
noncomputable def monomialData {prior : (Fin d → ℝ) → ℝ} (hps : ContDiff ℝ ∞ prior)
    (hp0 : ∀ y, 0 ≤ prior y) (hpc : HasCompactSupport prior)
    (hpW : tsupport prior ⊆ (W : Set (Fin d → ℝ))) : ResolvedData d where
  K := monoPhase k
  W := W
  R := WatanabeModificationOn.ofMonomial k W
  hKc := (continuous_monoPhase k).continuousOn
  hK0 := fun x _ => monoPhase_nonneg k x
  K_m := (continuous_monoPhase k).measurable
  prior := prior
  prior_smooth := hps
  prior_nonneg := hp0
  prior_compact := hpc
  prior_W := hpW
  F := fun _ => 1
  F_smooth := contMDiff_const

variable {prior : (Fin d → ℝ) → ℝ} (hps : ContDiff ℝ ∞ prior) (hp0 : ∀ y, 0 ≤ prior y)
  (hpc : HasCompactSupport prior) (hpW : tsupport prior ⊆ (W : Set (Fin d → ℝ)))

/-- The active zero coordinates at `P`: `P_i = 0` and `k_i > 0`. -/
noncomputable def zeroActive (P : Fin d → ℝ) : Finset (Fin d) :=
  Finset.univ.filter fun i => P i = 0 ∧ 0 < k i

theorem mem_zeroActive {P : Fin d → ℝ} {i : Fin d} : i ∈ zeroActive k P ↔ P i = 0 ∧ 0 < k i := by
  simp [zeroActive]

theorem monoK0 : ∀ x ∈ (W : Set (Fin d → ℝ)), 0 ≤ monoPhase k x := fun x _ => monoPhase_nonneg k x

/-- ★★ **The intrinsic pair data of the monomial phase**: at a zero `P`, one wall `(k_i, 0)` for
each active zero coordinate. -/
theorem pairs_ofMonomial (P : (WatanabeModificationOn.ofMonomial k W).U)
    (hP : monoPhase k P.1 = 0) :
    pairs (WatanabeModificationOn.ofMonomial k W) (monoK0 k W) P =
      (zeroActive k P.1).val.map fun i => (k i, 0) := by
  obtain ⟨E, hPs, hP0, hk, hh⟩ := exists_evenChartBox_ofMonomial W k P hP
  rw [pairs_eq_pairData _ _ E hPs hP0, pairData, active, hk, hh]
  have hfilt : (Finset.univ.filter fun j => 0 < activeExp k P.1 j) = zeroActive k P.1 := by
    ext i
    rw [Finset.mem_filter, mem_zeroActive]
    by_cases hi : P.1 i = 0 <;> simp [activeExp, hi]
  rw [hfilt]
  refine Multiset.map_congr rfl fun j hj => ?_
  rw [Finset.mem_val, mem_zeroActive] at hj
  simp [activeExp, hj.1]

theorem depth_ofMonomial (P : (WatanabeModificationOn.ofMonomial k W).U)
    (hP : monoPhase k P.1 = 0) :
    depth (WatanabeModificationOn.ofMonomial k W) (monoK0 k W) P = (zeroActive k P.1).card := by
  unfold depth
  rw [pairs_ofMonomial k W P hP, Multiset.card_map, Finset.card_val]

open Classical in
theorem resonanceCount_ofMonomial (μ : ℝ) (P : (WatanabeModificationOn.ofMonomial k W).U)
    (hP : monoPhase k P.1 = 0) :
    resonanceCount (WatanabeModificationOn.ofMonomial k W) (monoK0 k W) μ P =
      ((zeroActive k P.1).filter fun i => Resonates μ (k i, 0)).card := by
  unfold resonanceCount
  rw [pairs_ofMonomial k W P hP, Multiset.filter_map, Multiset.card_map, Finset.card_def,
    Finset.filter_val]
  rfl

theorem monomialData_R :
    (monomialData k W hps hp0 hpc hpW).R = WatanabeModificationOn.ofMonomial k W := rfl

/-! ### The extremal data -/

/-- The maximal exponent `k_max`. -/
noncomputable def kmax : ℕ := Finset.univ.sup k

/-- The multiplicity `m* = #{i : k_i = k_max}`. -/
noncomputable def mstar : ℕ := (Finset.univ.filter fun i => k i = kmax k).card

theorem le_kmax (i : Fin d) : k i ≤ kmax k := Finset.le_sup (Finset.mem_univ i)

theorem kmax_pos (hk : ∃ i, 0 < k i) : 0 < kmax k := by
  obtain ⟨i, hi⟩ := hk
  exact hi.trans_le (le_kmax k i)

theorem exists_eq_kmax [Nonempty (Fin d)] : ∃ i, k i = kmax k := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty k
  exact ⟨i, hi.symm⟩

theorem one_le_mstar (hk : ∃ i, 0 < k i) : 1 ≤ mstar k := by
  obtain ⟨i₀, -⟩ := hk
  have : Nonempty (Fin d) := ⟨i₀⟩
  obtain ⟨i, hi⟩ := exists_eq_kmax k
  exact Finset.card_pos.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩

/-- The extremal exponent `λ* = 1/(2 k_max)`. -/
noncomputable def lamStar : ℝ := 1 / (2 * (kmax k : ℝ))

/-- Resonance of `λ*` with the wall `(k_i, 0)` means `k_i = k_max`. -/
theorem resonates_lamStar_iff (hk : ∃ i, 0 < k i) (i : Fin d) :
    Resonates (lamStar k) (k i, 0) ↔ k i = kmax k := by
  have hpos : (0 : ℝ) < kmax k := Nat.cast_pos.2 (kmax_pos k hk)
  have hle : (k i : ℝ) ≤ kmax k := Nat.cast_le.2 (le_kmax k i)
  constructor
  · rintro ⟨n, hn⟩
    simp only [lamStar, Nat.cast_zero, zero_add] at hn
    have h1 : (k i : ℝ) / kmax k = 1 + n := by
      rw [← hn]
      field_simp
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h2 : (k i : ℝ) = kmax k * (1 + n) := by
      rw [← h1]
      field_simp
    have h3 : (kmax k : ℝ) ≤ k i := by nlinarith
    exact_mod_cast le_antisymm hle h3
  · intro h
    refine ⟨0, ?_⟩
    simp only [lamStar, h, Nat.cast_zero, zero_add, add_zero]
    field_simp

/-- ★★★ **The monomial phase has extremal data `(λ*, m*)`.** -/
theorem isExtremalData_monomial (hk : ∃ i, 0 < k i) :
    (monomialData k W hps hp0 hpc hpW).IsExtremalData (lamStar k) (mstar k) := by
  classical
  have hpos : (0 : ℝ) < kmax k := Nat.cast_pos.2 (kmax_pos k hk)
  refine ⟨fun P hP p hp => ?_, fun P hP => ?_⟩
  · have hp' : p ∈ pairs (WatanabeModificationOn.ofMonomial k W) (monoK0 k W) P := hp
    rw [pairs_ofMonomial k W P hP.2] at hp'
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hp'
    simp only [lamStar, Nat.cast_zero, zero_add]
    have hle : (k i : ℝ) ≤ kmax k := Nat.cast_le.2 (le_kmax k i)
    rw [show 2 * (k i : ℝ) * (1 / (2 * (kmax k : ℝ))) = k i / kmax k by field_simp,
      div_le_one hpos]
    exact hle
  · change resonanceCount (WatanabeModificationOn.ofMonomial k W) (monoK0 k W) (lamStar k) P ≤
      mstar k
    rw [resonanceCount_ofMonomial k W _ P hP.2]
    refine Finset.card_le_card fun i hi => ?_
    rw [Finset.mem_filter] at hi
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (resonates_lamStar_iff k hk i).1 hi.2⟩

/-- The origin of `W` as a point of the resolved manifold. -/
def originPt (h0W : (0 : Fin d → ℝ) ∈ W) : (monomialData k W hps hp0 hpc hpW).R.U := ⟨0, h0W⟩

theorem monoPhase_zero (hk : ∃ i, 0 < k i) : monoPhase k 0 = 0 := by
  obtain ⟨i, hi⟩ := hk
  unfold monoPhase
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by
    rw [Pi.zero_apply]
    exact zero_pow (by omega))

/-- The origin realises the multiplicity: exactly `m*` walls through it resonate with `λ*`. -/
theorem resonanceCount_monomial_zero (hk : ∃ i, 0 < k i) (h0W : (0 : Fin d → ℝ) ∈ W) :
    resonanceCount (monomialData k W hps hp0 hpc hpW).R (monomialData k W hps hp0 hpc hpW).hK0
      (lamStar k) (originPt k W hps hp0 hpc hpW h0W) = mstar k := by
  classical
  change resonanceCount (WatanabeModificationOn.ofMonomial k W) (monoK0 k W) (lamStar k)
    (originPt k W hps hp0 hpc hpW h0W) = mstar k
  rw [resonanceCount_ofMonomial k W _ (originPt k W hps hp0 hpc hpW h0W) (monoPhase_zero k hk)]
  unfold mstar
  congr 1
  ext i
  have h0 : ∀ i, (originPt k W hps hp0 hpc hpW h0W).1 i = 0 := fun i => rfl
  simp only [Finset.mem_filter, mem_zeroActive, h0, true_and, Finset.mem_univ,
    resonates_lamStar_iff k hk]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · intro h
    exact ⟨h ▸ kmax_pos k hk, h⟩

theorem originPt_mem_zeroFibre (hk : ∃ i, 0 < k i) (h0W : (0 : Fin d → ℝ) ∈ W)
    (hp : 0 < prior 0) :
    originPt k W hps hp0 hpc hpW h0W ∈ (monomialData k W hps hp0 hpc hpW).zeroFibre := by
  refine ⟨subset_tsupport _ ?_, monoPhase_zero k hk⟩
  exact hp.ne'

include hps hp0 hpc hpW in
/-- ★★★ **The classical monomial RLCT from the resolved machinery**: for `∏ x_i^{2k_i}` with a
compactly supported smooth prior positive at the origin,
`∫ φ e^{−N ∏ x^{2k}} ∼ c N^{−1/(2 k_max)} (log N)^{m*−1}` with `c > 0`,
`m* = #{i : k_i = k_max}`. -/
theorem monomial_rlct_asymptotic (hk : ∃ i, 0 < k i) (h0W : (0 : Fin d → ℝ) ∈ W)
    (hp : 0 < prior 0) :
    ∃ c : ℝ, 0 < c ∧ (fun N => partitionObs (monoPhase k) prior (fun _ => (1 : ℝ)) N) ~[atTop]
      fun N => c * (N ^ (-lamStar k) * Real.log N ^ (mstar k - 1)) := by
  set Ξ := monomialData k W hps hp0 hpc hpW with hΞ
  obtain ⟨Y⟩ := WatanabeModificationOn.exists_resolvedCoreTransport_of_modification Ξ.R Ξ.hK0
    Ξ.hKc Ξ.prior_smooth.continuous.measurable Ξ.prior_nonneg Ξ.prior_compact Ξ.prior_W
  obtain ⟨-, -, hc, hequiv⟩ := Ξ.rlct_asymptotic_of_realised Y
    (isExtremalData_monomial k W hps hp0 hpc hpW hk)
    (originPt_mem_zeroFibre k W hps hp0 hpc hpW hk h0W hp) hp
    (resonanceCount_monomial_zero k W hps hp0 hpc hpW hk h0W) (one_le_mstar k hk)
  exact ⟨_, hc, hequiv⟩

end Monomial

end SmoothEngine

end Grammar
