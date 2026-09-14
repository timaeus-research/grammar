/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothResolvedRLCTPositive

/-!
# The extremal pair of a compact zero fibre is realised

The wall data occurring on the compact zero fibre `Z₀` is finite: a finite even chart cover
bounds every wall multiset by a chart's data (`exists_finset_pairs_subset`). Hence the minimal
wall ratio `λ* = min (h+1)/(2k)` over the walls through `Z₀` is attained, the maximal resonance
count `m*` at `λ*` is attained, and `(λ*, m*)` is extremal data (CDXXXIX) REALISED at a point
`P₀ ∈ Z₀` with `m* ≥ 1` (★★ `exists_realised_extremalData`). Combined with the positivity
theorem (CDXLI): for every resolved input whose zero fibre is nonempty and whose prior is
positive on the zero set of the phase inside its support, there are `λ*` and `m* ≥ 1` with
`(λ*, m* − 1)` the leading index of `Z^U_N[1]` (★★★ `exists_isLeadingIndexOne`,
`exists_isLeadingIndexOne_of_pos_on_zeroSet`): the partition function has the asymptotics
`c N^{−λ*}(log N)^{m*−1}`, `c > 0`, with `(λ*, m*)` the extremal pair of the intrinsic wall data —
the RLCT identification with no leading-index hypothesis. If the zero fibre is empty every
coefficient vanishes (`coeff_eq_zero_of_zeroFibre_eq_empty`).

Non-claims: the exponent and multiplicity are produced by choice (no closed formula); the
positivity hypothesis on the prior is on the zero set inside the support, not merely at one point.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing Grammar.NormalCrossing.EvenChartBoxDepth

namespace Grammar

namespace SmoothEngine

variable {d : ℕ}

/-- The ratio `(h+1)/(2k)` of a wall `(k, h)`. -/
noncomputable def wallRatio (p : ℕ × ℕ) : ℝ := ((p.2 : ℝ) + 1) / (2 * p.1)

theorem le_wallRatio_iff {p : ℕ × ℕ} (hk : 0 < p.1) {lam : ℝ} :
    lam ≤ wallRatio p ↔ 2 * (p.1 : ℝ) * lam ≤ p.2 + 1 := by
  have hk' : (0 : ℝ) < p.1 := Nat.cast_pos.2 hk
  unfold wallRatio
  rw [le_div_iff₀ (by linarith)]
  constructor <;> intro h <;> linarith

theorem resonates_wallRatio {p : ℕ × ℕ} (hk : 0 < p.1) : Resonates (wallRatio p) p := by
  have hk' : (p.1 : ℝ) ≠ 0 := (Nat.cast_pos.2 hk).ne'
  refine ⟨0, ?_⟩
  rw [Nat.cast_zero, add_zero]
  unfold wallRatio
  field_simp

namespace ResolvedData

variable (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-- **Finiteness of the wall data on the zero fibre**: a finite even chart cover of the compact
zero fibre bounds every wall multiset by the chart data at a centre. -/
theorem exists_finset_pairs_subset :
    ∃ S : Finset (ℕ × ℕ), ∀ P ∈ Ξ.zeroFibre, ∀ p ∈ pairs Ξ.R Ξ.hK0 P, p ∈ S := by
  classical
  obtain ⟨ι, hι, E, hcover⟩ := exists_finite_evenChartBoxes Ξ.R Ξ.hK0 Ξ.isCompact_zeroFibre
    fun P hP => hP.2
  refine ⟨Finset.univ.biUnion fun i => (pairData (E i)).toFinset, fun P hP p hp => ?_⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hcover hP)
  have hc : (E i).φ.symm 0 ∈ (E i).φ.source := (E i).φ.map_target (E i).zero_mem.1
  have hc0 : (E i).φ ((E i).φ.symm 0) = 0 := (E i).φ.right_inv (E i).zero_mem.1
  have hle := pairs_le_of_mem_source Ξ.R Ξ.hK0 (E i) hc hc0 hi.1
  rw [pairs_eq_pairData Ξ.R Ξ.hK0 (E i) hc hc0] at hle
  exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _,
    Multiset.mem_toFinset.2 (Multiset.mem_of_le hle hp)⟩

/-- ★★ **The extremal pair of a nonempty compact zero fibre exists and is realised**: there are
`λ*`, `m* ≥ 1` and `P₀ ∈ Z₀` with `(λ*, m*)` extremal and exactly `m*` walls through `P₀`
resonating with `λ*`. -/
theorem exists_realised_extremalData (hne : Ξ.zeroFibre.Nonempty) :
    ∃ (lam : ℝ) (m : ℕ) (P₀ : Ξ.R.U), Ξ.IsExtremalData lam m ∧ P₀ ∈ Ξ.zeroFibre ∧
      resonanceCount Ξ.R Ξ.hK0 lam P₀ = m ∧ 1 ≤ m := by
  classical
  obtain ⟨S, hS⟩ := Ξ.exists_finset_pairs_subset
  set S' : Finset (ℕ × ℕ) := S.filter fun p => ∃ P ∈ Ξ.zeroFibre, p ∈ pairs Ξ.R Ξ.hK0 P with hS'
  have hmemS' : ∀ P ∈ Ξ.zeroFibre, ∀ p ∈ pairs Ξ.R Ξ.hK0 P, p ∈ S' := fun P hP p hp =>
    Finset.mem_filter.2 ⟨hS P hP p hp, P, hP, hp⟩
  obtain ⟨P₁, hP₁⟩ := hne
  obtain ⟨p₁, hp₁⟩ : ∃ p, p ∈ pairs Ξ.R Ξ.hK0 P₁ := by
    have := (depth_pos_iff Ξ.R Ξ.hK0 P₁).2 hP₁.2
    unfold depth at this
    exact Multiset.card_pos_iff_exists_mem.1 this
  have hS'ne : S'.Nonempty := ⟨p₁, hmemS' P₁ hP₁ p₁ hp₁⟩
  obtain ⟨p₀, hp₀S', hp₀min⟩ := S'.exists_min_image wallRatio hS'ne
  obtain ⟨-, P₂, hP₂, hp₀⟩ := Finset.mem_filter.1 hp₀S'
  set lam := wallRatio p₀ with hlam
  have hext : ∀ P ∈ Ξ.zeroFibre, ∀ p ∈ pairs Ξ.R Ξ.hK0 P, 2 * (p.1 : ℝ) * lam ≤ p.2 + 1 :=
    fun P hP p hp =>
      (le_wallRatio_iff (fst_pos_of_mem_pairs Ξ.R Ξ.hK0 hp)).1 (hp₀min p (hmemS' P hP p hp))
  have hbdd : ∃ m : ℕ, ∀ P ∈ Ξ.zeroFibre, resonanceCount Ξ.R Ξ.hK0 lam P ≤ m :=
    ⟨d, fun P _ => (resonanceCount_le_depth Ξ.R Ξ.hK0 lam P).trans (depth_le_dim Ξ.R Ξ.hK0 P)⟩
  set m := Nat.find hbdd with hm
  have hmspec : ∀ P ∈ Ξ.zeroFibre, resonanceCount Ξ.R Ξ.hK0 lam P ≤ m := Nat.find_spec hbdd
  have hres₂ : 1 ≤ resonanceCount Ξ.R Ξ.hK0 lam P₂ := by
    unfold resonanceCount
    exact Multiset.card_pos_iff_exists_mem.2
      ⟨p₀, Multiset.mem_filter.2 ⟨hp₀, resonates_wallRatio (fst_pos_of_mem_pairs Ξ.R Ξ.hK0 hp₀)⟩⟩
  have hm1 : 1 ≤ m := hres₂.trans (hmspec P₂ hP₂)
  have hattain : ∃ P₀ ∈ Ξ.zeroFibre, resonanceCount Ξ.R Ξ.hK0 lam P₀ = m := by
    by_contra hcon
    have hcon' : ∀ P ∈ Ξ.zeroFibre, resonanceCount Ξ.R Ξ.hK0 lam P ≠ m :=
      fun P hP hPm => hcon ⟨P, hP, hPm⟩
    have hlt : ∀ P ∈ Ξ.zeroFibre, resonanceCount Ξ.R Ξ.hK0 lam P ≤ m - 1 := fun P hP => by
      have h1 := hmspec P hP
      have h2 := hcon' P hP
      omega
    have := Nat.find_min' hbdd hlt
    omega
  obtain ⟨P₀, hP₀, hP₀m⟩ := hattain
  exact ⟨lam, m, P₀, ⟨hext, hmspec⟩, hP₀, hP₀m, hm1⟩

/-- ★★★ **The RLCT identification without a leading-index hypothesis**: for a nonempty zero
fibre and a prior positive on it, some `(λ*, m* − 1)` with `(λ*, m*)` extremal and `m* ≥ 1` is
the leading index of `Z^U_N[1]`. -/
theorem exists_isLeadingIndexOne (hne : Ξ.zeroFibre.Nonempty)
    (hpos : ∀ P ∈ Ξ.zeroFibre, 0 < Ξ.prior (Ξ.R.gv P)) :
    ∃ (lam : ℝ) (m : ℕ), 1 ≤ m ∧ Ξ.IsExtremalData lam m ∧ Ξ.IsLeadingIndexOne Y lam (m - 1) := by
  obtain ⟨lam, m, P₀, hext, hP₀, hres, hm1⟩ := Ξ.exists_realised_extremalData hne
  exact ⟨lam, m, hm1, hext, Ξ.isLeadingIndexOne_of_realised Y hext hP₀ (hpos P₀ hP₀) hres hm1⟩

/-- The Euclidean form of the positivity hypothesis: the prior is positive on the zero set of the
phase inside its support. -/
theorem exists_isLeadingIndexOne_of_pos_on_zeroSet (hne : Ξ.zeroFibre.Nonempty)
    (hpos : ∀ y ∈ tsupport Ξ.prior, Ξ.K y = 0 → 0 < Ξ.prior y) :
    ∃ (lam : ℝ) (m : ℕ), 1 ≤ m ∧ Ξ.IsExtremalData lam m ∧ Ξ.IsLeadingIndexOne Y lam (m - 1) :=
  Ξ.exists_isLeadingIndexOne Y hne fun _ hP => hpos _ hP.1 hP.2

/-- With an empty zero fibre every resolved coefficient vanishes. -/
theorem coeff_eq_zero_of_zeroFibre_eq_empty (h : Ξ.zeroFibre = ∅) (μ : ℝ) (q : ℕ) :
    Ξ.coeff Y μ q = 0 := by
  refine Ξ.coeff_eq_zero_of_eventually_zero_resonant Y ?_
  have : Ξ.resonantZeroFibre μ q = ∅ :=
    Set.eq_empty_of_subset_empty (h ▸ Set.inter_subset_left)
  rw [this, nhdsSet_empty]
  exact Filter.eventually_bot

end ResolvedData

end SmoothEngine

end Grammar
