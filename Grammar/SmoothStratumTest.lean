/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothResolvedResidue
import Grammar.SmoothResolvedStratumExtremal
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# The stratum test functional

Residue programme (consult #132), unit 1. Fix `(μ, c)` with the zero-order condition. On the open
set `X = U ∖ D_{c+1}` (`stratumOpen`) the TEST FUNCTIONS are the smooth observables with compact
support inside `X` (`IsTest`); every test vanishes near the deep zero fibre, so the resolved
coefficient functional `T[G] := 𝒯^U_{μ,c−1}[G]` (`T`) is defined on them and is linear
(`T_add`, `T_smul`), positive (`T_nonneg`), monotone (`T_mono`), local on the exact stratum
(`T_eq_zero_of_eqOn_zero`), and locally bounded: `|T[G]| ≤ M · T[χ]` whenever `|G| ≤ M` and the
cutoff `χ ≥ 1` on the support of `G` (`abs_T_le`). Cutoffs equal to `1` on a compact subset of
`X` exist (`exists_cutoff`, smooth bump functions on the σ-compact Hausdorff manifold `U`). These
are the inputs of the Riesz construction of the stratum measure. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing

namespace Grammar

namespace SmoothEngine

variable {d : ℕ}

/-! ### Topological instances on the resolved manifold -/

instance {K : (Fin d → ℝ) → ℝ} {W : TopologicalSpace.Opens (Fin d → ℝ)}
    (R : WatanabeModificationOn K W) : LocallyCompactSpace R.U :=
  locallyCompactSpace_of_chartedSpace (Fin d → ℝ) R.U

instance {K : (Fin d → ℝ) → ℝ} {W : TopologicalSpace.Opens (Fin d → ℝ)}
    (R : WatanabeModificationOn K W) : SigmaCompactSpace R.U :=
  sigmaCompactSpace_of_chartedSpace (Fin d → ℝ) R.U

namespace ResolvedData

variable (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-- The open set `X = U ∖ D_{c+1}` carrying the stratum measure. -/
def stratumOpen (c : ℕ) : Set Ξ.R.U := (Ξ.deepZeroFibre c)ᶜ

theorem isOpen_stratumOpen (c : ℕ) : IsOpen (Ξ.stratumOpen c) :=
  (Ξ.isCompact_deepZeroFibre c).isClosed.isOpen_compl

/-- **Test functions**: compactly supported inside `X = U ∖ D_{c+1}`. -/
def IsTest (c : ℕ) (G : Ξ.R.U → ℝ) : Prop :=
  HasCompactSupport G ∧ tsupport G ⊆ Ξ.stratumOpen c

theorem IsTest.eventually_zero {c : ℕ} {G : Ξ.R.U → ℝ} (hG : Ξ.IsTest c G) :
    ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), G P = 0 := by
  have hopen : IsOpen (tsupport G)ᶜ := (isClosed_tsupport G).isOpen_compl
  have hsub : Ξ.deepZeroFibre c ⊆ (tsupport G)ᶜ := fun P hP hPt => hG.2 hPt hP
  exact Filter.eventually_of_mem (hopen.mem_nhdsSet.2 hsub) fun P hP =>
    image_eq_zero_of_notMem_tsupport hP

theorem IsTest.add {c : ℕ} {G G' : Ξ.R.U → ℝ} (hG : Ξ.IsTest c G) (hG' : Ξ.IsTest c G') :
    Ξ.IsTest c (fun P => G P + G' P) := by
  have hK : IsCompact (tsupport G ∪ tsupport G') := hG.1.union hG'.1
  have hsub : tsupport (fun P => G P + G' P) ⊆ tsupport G ∪ tsupport G' := by
    refine closure_minimal (fun P hP => ?_) (hG.1.isClosed.union hG'.1.isClosed)
    by_contra h
    rw [Set.mem_union, not_or] at h
    exact hP (by
      change G P + G' P = 0
      rw [image_eq_zero_of_notMem_tsupport h.1, image_eq_zero_of_notMem_tsupport h.2, add_zero])
  exact ⟨hK.of_isClosed_subset (isClosed_tsupport _) hsub,
    hsub.trans (Set.union_subset hG.2 hG'.2)⟩

theorem IsTest.smul {c : ℕ} {G : Ξ.R.U → ℝ} (hG : Ξ.IsTest c G) (r : ℝ) :
    Ξ.IsTest c (fun P => r * G P) := by
  have hsub : tsupport (fun P => r * G P) ⊆ tsupport G := by
    refine closure_minimal (fun P hP => ?_) (isClosed_tsupport G)
    by_contra h
    exact hP (by
      change r * G P = 0
      rw [image_eq_zero_of_notMem_tsupport h, mul_zero])
  exact ⟨hG.1.of_isClosed_subset (isClosed_tsupport _) hsub, hsub.trans hG.2⟩

/-! ### The functional -/

/-- **The stratum test functional** `T[G] = 𝒯^U_{μ,c−1}[G]`. -/
noncomputable def T (μ : ℝ) (c : ℕ) (G : Ξ.R.U → ℝ)
    (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) : ℝ :=
  (Ξ.withF G hG).coeff Y μ (c - 1)

theorem T_add (μ : ℝ) (c : ℕ) {G G' : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G)
    (hG' : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G') :
    Ξ.T Y μ c (fun P => G P + G' P) (hG.add hG') = Ξ.T Y μ c G hG + Ξ.T Y μ c G' hG' :=
  Ξ.coeff_add Y hG hG' μ (c - 1)

theorem T_smul (μ : ℝ) (c : ℕ) {G : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G)
    (r : ℝ) : Ξ.T Y μ c (fun P => r * G P) (contMDiff_const.mul hG) = r * Ξ.T Y μ c G hG :=
  Ξ.coeff_smul Y hG r μ (c - 1)

/-- The functional does not depend on the transport. -/
theorem T_eq_of_transports (Y' : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior) (μ : ℝ) (c : ℕ)
    {G : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) :
    Ξ.T Y μ c G hG = Ξ.T Y' μ c G hG :=
  (Ξ.withF G hG).coeff_eq_of_transports Y Y' μ (c - 1)

theorem T_nonneg {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c) {G : Ξ.R.U → ℝ}
    (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) (hGt : Ξ.IsTest c G) (hG0 : ∀ P, 0 ≤ G P) :
    0 ≤ Ξ.T Y μ c G hG :=
  (Ξ.withF G hG).coeff_nonneg_of_deep Y hc hzero hGt.eventually_zero hG0

theorem T_eq_zero_of_eqOn_zero {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c)
    {G : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) (hGt : Ξ.IsTest c G)
    (h0 : ∀ P ∈ Ξ.exactStratum μ c, G P = 0) : Ξ.T Y μ c G hG = 0 :=
  (Ξ.withF G hG).coeff_eq_zero_of_eqOn_zero_exactStratum Y hc hzero hGt.eventually_zero h0

theorem T_mono {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c) {G G' : Ξ.R.U → ℝ}
    (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) (hG' : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G')
    (hGt : Ξ.IsTest c G) (hG't : Ξ.IsTest c G') (hle : ∀ P, G P ≤ G' P) :
    Ξ.T Y μ c G hG ≤ Ξ.T Y μ c G' hG' := by
  have hG'' : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ (fun P => (-1 : ℝ) * G P) :=
    contMDiff_const.mul hG
  have hdiff := Ξ.T_nonneg Y hc hzero (G := fun P => G' P + (-1 : ℝ) * G P) (hG'.add hG'')
    (IsTest.add Ξ hG't (IsTest.smul Ξ hGt (-1))) fun P => by
      have := hle P
      change 0 ≤ G' P + (-1 : ℝ) * G P
      linarith
  rw [Ξ.T_add Y μ c hG' hG'', Ξ.T_smul Y μ c hG (-1)] at hdiff
  linarith

/-- ★ **The local bound**: `|T[G]| ≤ M · T[χ]` for a cutoff `χ ≥ 1` on the support of `G` and
`|G| ≤ M`. -/
theorem abs_T_le {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c) {G χ : Ξ.R.U → ℝ}
    (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) (hGt : Ξ.IsTest c G)
    (hχ : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ χ) (hχt : Ξ.IsTest c χ) (hχ0 : ∀ P, 0 ≤ χ P)
    (hχ1 : ∀ P ∈ tsupport G, 1 ≤ χ P) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ P, |G P| ≤ M) :
    |Ξ.T Y μ c G hG| ≤ M * Ξ.T Y μ c χ hχ := by
  have hMχ : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ (fun P => M * χ P) := contMDiff_const.mul hχ
  have hbound : ∀ P, |G P| ≤ M * χ P := by
    intro P
    by_cases hP : P ∈ tsupport G
    · exact (hM P).trans (le_mul_of_one_le_right hM0 (hχ1 P hP))
    · rw [image_eq_zero_of_notMem_tsupport hP, abs_zero]
      exact mul_nonneg hM0 (hχ0 P)
  have hplus := Ξ.T_nonneg Y hc hzero (G := fun P => M * χ P + G P) (hMχ.add hG)
    (IsTest.add Ξ (IsTest.smul Ξ hχt M) hGt) fun P => by
      have := (abs_le.1 (hbound P)).1
      change 0 ≤ M * χ P + G P
      linarith
  have hG'' : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ (fun P => (-1 : ℝ) * G P) :=
    contMDiff_const.mul hG
  have hminus := Ξ.T_nonneg Y hc hzero (G := fun P => M * χ P + (-1 : ℝ) * G P) (hMχ.add hG'')
    (IsTest.add Ξ (IsTest.smul Ξ hχt M) (IsTest.smul Ξ hGt (-1))) fun P => by
      have := (abs_le.1 (hbound P)).2
      change 0 ≤ M * χ P + (-1 : ℝ) * G P
      linarith
  rw [Ξ.T_add Y μ c hMχ hG, Ξ.T_smul Y μ c hχ M] at hplus
  rw [Ξ.T_add Y μ c hMχ hG'', Ξ.T_smul Y μ c hχ M, Ξ.T_smul Y μ c hG (-1)] at hminus
  rw [abs_le]
  constructor <;> linarith

/-! ### Cutoffs -/

/-- ★ **Cutoffs**: a smooth test function equal to `1` on a compact subset of `X`, with values in
`[0, 1]`. -/
theorem exists_cutoff (c : ℕ) {K : Set Ξ.R.U} (hK : IsCompact K) (hKX : K ⊆ Ξ.stratumOpen c) :
    ∃ χ : Ξ.R.U → ℝ, ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ χ ∧ Ξ.IsTest c χ ∧
      (∀ P ∈ K, χ P = 1) ∧ ∀ P, χ P ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨L, hLc, hKL, hLX⟩ := exists_compact_between hK (Ξ.isOpen_stratumOpen c) hKX
  obtain ⟨f, hf1, hf0, hf01⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(ℝ, Fin d → ℝ) (n := ⊤) hK.isClosed hKL
  have hsupp : Function.support f ⊆ L := fun P hP => by_contra fun h => hP (hf0 P h)
  have hts : tsupport f ⊆ L := closure_minimal hsupp hLc.isClosed
  refine ⟨f, f.contMDiff, ⟨hLc.of_isClosed_subset (isClosed_tsupport _) hts, hts.trans hLX⟩,
    fun P hP => hf1.self_of_nhdsSet P hP, hf01⟩

end ResolvedData

end SmoothEngine

end Grammar
