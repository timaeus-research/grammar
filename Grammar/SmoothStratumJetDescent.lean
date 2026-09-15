/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothStratumJetDependence

/-!
# Descent of the stratum coefficient to the transverse-jet quotient

The jet-dependence theorem of `SmoothStratumJetDependence` is packaged as a descent: the
admissible observables of depth `c` (smooth, vanishing near `D_{c+1}`) form a submodule
`admissible c` of `U → ℝ`; the observables lying in `𝓘_{S^μ_c}^{n(P)+1}` near every point `P` of the
exact stratum form a submodule `jetKernel μ c` (the ideal-power condition is closed under sums and
smooth multiples); the coefficient `G ↦ 𝒯^U_{μ,c−1}[G]` is a linear functional `coeffLin` on
`admissible c` that kills `admissible c ∩ jetKernel μ c` (`coeffLin_eq_zero_of_mem_jetKernel`), so
it descends to a linear functional `descendedCoeff` on the transverse-jet quotient
`admissible c ⧸ (admissible c ∩ jetKernel μ c)` with `descendedCoeff (mk G) = 𝒯^U_{μ,c−1}[G]`
(`descendedCoeff_mk`). No zero-order hypothesis; under it the kernel contains every admissible
observable vanishing on the exact stratum (`mem_jetKernel_of_eqOn_zero`). Not constructed here: a
separately defined residue object acting on the quotient. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing Grammar.NormalCrossing.EvenChartBoxDepth

namespace Grammar

namespace SmoothEngine

namespace ResolvedData

variable {d : ℕ} (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-! ### The ideal-power condition is linear -/

variable {Ξ} in
theorem MemIdealPowNear.add {S : Set Ξ.R.U} {n : ℕ} {H H' : Ξ.R.U → ℝ} {P : Ξ.R.U}
    (h : Ξ.MemIdealPowNear S n H P) (h' : Ξ.MemIdealPowNear S n H' P) :
    Ξ.MemIdealPowNear S n (H + H') P := by
  obtain ⟨N, hN, ι, _, a, g, ha, hg, hg0, hH⟩ := h
  obtain ⟨N', hN', ι', _, a', g', ha', hg', hg0', hH'⟩ := h'
  refine ⟨N ∩ N', inter_mem hN hN', ι ⊕ ι', inferInstance, Sum.elim a a', Sum.elim g g',
    ?_, ?_, ?_, ?_⟩
  · intro i
    cases i with
    | inl i => exact ha i
    | inr i => exact ha' i
  · intro i l
    cases i with
    | inl i => exact hg i l
    | inr i => exact hg' i l
  · intro i l Q hQ
    cases i with
    | inl i => exact hg0 i l Q hQ
    | inr i => exact hg0' i l Q hQ
  · intro Q hQ
    rw [Pi.add_apply, hH Q hQ.1, hH' Q hQ.2, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]

variable {Ξ} in
theorem MemIdealPowNear.smul {S : Set Ξ.R.U} {n : ℕ} {H : Ξ.R.U → ℝ} {P : Ξ.R.U} (r : ℝ)
    (h : Ξ.MemIdealPowNear S n H P) : Ξ.MemIdealPowNear S n (r • H) P := by
  obtain ⟨N, hN, ι, _, a, g, ha, hg, hg0, hH⟩ := h
  refine ⟨N, hN, ι, inferInstance, fun i Q => r * a i Q, g, fun i => contMDiff_const.mul (ha i),
    hg, hg0, fun Q hQ => ?_⟩
  rw [Pi.smul_apply, smul_eq_mul, hH Q hQ, Finset.mul_sum]
  simp only [mul_assoc]

theorem memIdealPowNear_zero_fun (S : Set Ξ.R.U) (n : ℕ) (P : Ξ.R.U) :
    Ξ.MemIdealPowNear S n 0 P :=
  ⟨univ, univ_mem, Empty, inferInstance, Empty.elim, Empty.elim, fun i => i.elim, fun i => i.elim,
    fun i => i.elim, fun Q _ => by simp⟩

/-! ### The submodules -/

/-- The admissible observables of depth `c`: smooth and vanishing near the deep zero fibre
`D_{c+1}`. -/
def admissible (c : ℕ) : Submodule ℝ (Ξ.R.U → ℝ) where
  carrier := {G | ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G ∧ ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), G P = 0}
  add_mem' {G G'} hG hG' := ⟨hG.1.add hG'.1, by
    filter_upwards [hG.2, hG'.2] with P h1 h2
    rw [Pi.add_apply, h1, h2, add_zero]⟩
  zero_mem' := ⟨contMDiff_const, Eventually.of_forall fun _ => rfl⟩
  smul_mem' r {G} hG := ⟨contMDiff_const.mul hG.1, by
    filter_upwards [hG.2] with P h1
    rw [Pi.smul_apply, h1, smul_zero]⟩

theorem mem_admissible {c : ℕ} {G : Ξ.R.U → ℝ} : G ∈ Ξ.admissible c ↔
    ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G ∧ ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), G P = 0 := Iff.rfl

/-- The transverse-jet kernel: observables lying in `𝓘_{S^μ_c}^{n(P)+1}` near every point `P` of
the exact stratum, `n(P) = stratumJetOrder μ P`. -/
def jetKernel (μ : ℝ) (c : ℕ) : Submodule ℝ (Ξ.R.U → ℝ) where
  carrier := {H | ∀ P ∈ Ξ.exactStratum μ c,
    Ξ.MemIdealPowNear (Ξ.exactStratum μ c) (Ξ.stratumJetOrder μ P + 1) H P}
  add_mem' hH hH' P hP := (hH P hP).add (hH' P hP)
  zero_mem' P _ := Ξ.memIdealPowNear_zero_fun _ _ P
  smul_mem' r _ hH P hP := (hH P hP).smul r

theorem mem_jetKernel {μ : ℝ} {c : ℕ} {H : Ξ.R.U → ℝ} : H ∈ Ξ.jetKernel μ c ↔
    ∀ P ∈ Ξ.exactStratum μ c,
      Ξ.MemIdealPowNear (Ξ.exactStratum μ c) (Ξ.stratumJetOrder μ P + 1) H P := Iff.rfl

/-- Under the zero-order condition the kernel contains every smooth observable vanishing on the
exact stratum. -/
theorem mem_jetKernel_of_eqOn_zero {μ : ℝ} {c : ℕ} (hzero : Ξ.ZeroOrder μ c) {H : Ξ.R.U → ℝ}
    (hH : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ H) (h0 : ∀ P ∈ Ξ.exactStratum μ c, H P = 0) :
    H ∈ Ξ.jetKernel μ c := fun P hP => by
  rw [Ξ.stratumJetOrder_eq_zero_of_zeroOrder hzero hP]
  exact Ξ.memIdealPowNear_one_of_eqOn_zero _ hH h0 P

/-! ### The coefficient as a linear functional and its descent -/

/-- The `(μ, c−1)` coefficient on admissible observables, as a linear functional. -/
noncomputable def coeffLin (μ : ℝ) (c : ℕ) : Ξ.admissible c →ₗ[ℝ] ℝ where
  toFun G := (Ξ.withF G.1 G.2.1).coeff Y μ (c - 1)
  map_add' G G' := Ξ.coeff_add Y G.2.1 G'.2.1 μ (c - 1)
  map_smul' r G := Ξ.coeff_smul Y G.2.1 r μ (c - 1)

theorem coeffLin_apply (μ : ℝ) (c : ℕ) (G : Ξ.admissible c) :
    Ξ.coeffLin Y μ c G = (Ξ.withF G.1 G.2.1).coeff Y μ (c - 1) := rfl

/-- ★★ The coefficient functional kills the transverse-jet kernel. -/
theorem coeffLin_eq_zero_of_mem_jetKernel {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (G : Ξ.admissible c)
    (hG : (G : Ξ.R.U → ℝ) ∈ Ξ.jetKernel μ c) : Ξ.coeffLin Y μ c G = 0 :=
  (Ξ.withF G.1 G.2.1).coeff_eq_zero_of_vanishesToOrder Y hc G.2.2 fun P hP =>
    (hG P hP).vanishesToOrderAt hP

/-- The transverse-jet kernel inside the admissible observables. -/
def jetKernelAdm (μ : ℝ) (c : ℕ) : Submodule ℝ (Ξ.admissible c) :=
  (Ξ.jetKernel μ c).comap (Ξ.admissible c).subtype

theorem jetKernelAdm_le_ker {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) :
    Ξ.jetKernelAdm μ c ≤ LinearMap.ker (Ξ.coeffLin Y μ c) := fun G hG =>
  Ξ.coeffLin_eq_zero_of_mem_jetKernel Y hc G hG

/-- ★★★ **The descended coefficient functional** on the transverse-jet quotient of admissible
observables: `𝒯^U_{μ,c−1}` factors through `admissible c ⧸ (admissible c ∩ 𝓘_{S^μ_c}^{n(·)+1})`. -/
noncomputable def descendedCoeff (μ : ℝ) (c : ℕ) (hc : 1 ≤ c) :
    (Ξ.admissible c ⧸ Ξ.jetKernelAdm μ c) →ₗ[ℝ] ℝ :=
  (Ξ.jetKernelAdm μ c).liftQ (Ξ.coeffLin Y μ c) (Ξ.jetKernelAdm_le_ker Y hc)

theorem descendedCoeff_mk (μ : ℝ) {c : ℕ} (hc : 1 ≤ c) (G : Ξ.admissible c) :
    Ξ.descendedCoeff Y μ c hc (Submodule.Quotient.mk G) = (Ξ.withF G.1 G.2.1).coeff Y μ (c - 1) :=
  Submodule.liftQ_apply _ _ _

/-- Two admissible observables with the same transverse-jet class have the same coefficient. -/
theorem coeff_eq_of_quotient_mk_eq (μ : ℝ) {c : ℕ} (hc : 1 ≤ c) {G G' : Ξ.admissible c}
    (h : (Submodule.Quotient.mk G : Ξ.admissible c ⧸ Ξ.jetKernelAdm μ c) =
      Submodule.Quotient.mk G') :
    (Ξ.withF G.1 G.2.1).coeff Y μ (c - 1) = (Ξ.withF G'.1 G'.2.1).coeff Y μ (c - 1) := by
  rw [← Ξ.descendedCoeff_mk Y μ hc, h, Ξ.descendedCoeff_mk Y μ hc]

end ResolvedData

end SmoothEngine

end Grammar
