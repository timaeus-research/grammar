/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.EmpiricalResolvedExpansion
import Grammar.EmpiricalFaceSumCollapse
import Grammar.CoordFreeLeadingTerm

/-!
# Leading consistency: the resolved empirical expansion recovers the empirical leading term
(§20, consult #143 priority 1)

Under the chart-leading hypothesis `ChartLeading λ m` (every piece: `λ ≤ (hᵢ+1)/(2kᵢ)` and at
most `m` coordinates attain `λ`), the empirical coefficients of every piece vanish below `λ`
(`empCoeffAtDepth_eq_zero_of_boxLeading_lt`) and at `λ` in logarithmic degree `≥ m`
(`empCoeffAtDepth_eq_zero_of_boxLeading_deg`): below `λ` the exponent is off the face spectra,
at `λ` the exact-resonance count of any face is at most the multiplicity `m`. Hence the resolved
coefficients vanish on every index preceding `(λ, m−1)` in the asymptotic order, the generic
extraction lemma `CutoffExpansion.hasLeadingTerm_of_first` gives
`Z^emp/(N^{−λ}(log N)^{m−1}) → resolvedCoeff λ (m−1)`, and uniqueness of limits against the
independently proved leading theorem `hasLeadingTerm_empZ` (the spatially varying phase route)
identifies the two: ★★★ `resolvedCoeff_leading`:
`resolvedCoeff λ (m−1) = ∑_p ∫_{Base_p} pieceFaceLimit_p dν_p` — the face formula with
`S_λ(ψ̂)/Γ(λ)`, i.e. the `α = 0` replacement rule at the leading pair WITHOUT any deep-vanishing
hypothesis; for tests vanishing near `D_{m+1}` it is `∫ F dν^λ_m(ψ̂)`
(`resolvedCoeff_leading_eq_integral`).
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Finset
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing Grammar.NormalCrossing.EvenChartBoxDepth

namespace Grammar

namespace SmoothEngine

/-! ### Vanishing of the inner and face coefficients below and at the leading exponent -/

section Inner

variable {n : ℕ} (k e : Fin (n + 1) → ℕ)

/-- Below every exponent of the face spectrum the inner coefficients vanish. -/
theorem empInnerCoeff_eq_zero_of_lt (hk : ∀ i, 0 < k i) {μ : ℝ}
    (hμ : ∀ i, 2 * (k i : ℝ) * μ < e i + 1) (G : ℝ → ℝ) (q : ℕ) : empInnerCoeff k e G μ q = 0 := by
  have hnot : μ ∉ innerSpectrum k e := by
    intro hmem
    unfold innerSpectrum at hmem
    rw [List.mem_toFinset, List.mem_map] at hmem
    obtain ⟨en, hen, hμe⟩ := hmem
    obtain ⟨i, hi⟩ := stateDensityRep_exponent_mem _ (sdWeights k e) en hen
    have h := (sdWeights_add_one_eq_iff k e hk μ i).1 (by rw [← hi, hμe])
    exact (hμ i).ne h
  unfold empInnerCoeff
  rw [Finset.sum_eq_zero fun j _ => ?_, mul_zero]
  rw [coeffAt_eq_zero_of_not_mem _ hnot j, zero_mul, zero_mul]

/-- The exact-resonance count of the face is the multiplicity of the exponent in the state
density. -/
theorem expMult_sdWeights_eq_card (hk : ∀ i, 0 < k i) (μ : ℝ) :
    expMult (sdWeights k e) μ = (Finset.univ.filter fun i => 2 * (k i : ℝ) * μ = e i + 1).card := by
  unfold expMult
  congr 1
  exact Finset.filter_congr fun i _ => sdWeights_add_one_eq_iff k e hk μ i

/-- At log degrees at least the exact-resonance count the inner coefficients vanish. -/
theorem empInnerCoeff_eq_zero_of_count_le (hk : ∀ i, 0 < k i) {μ : ℝ} {q : ℕ}
    (hq : (Finset.univ.filter fun i => 2 * (k i : ℝ) * μ = e i + 1).card ≤ q) (G : ℝ → ℝ) :
    empInnerCoeff k e G μ q = 0 := by
  unfold empInnerCoeff
  rw [Finset.sum_eq_zero fun j _ => ?_, mul_zero]
  rcases lt_or_ge j q with hj | hj
  · rw [Nat.choose_eq_zero_of_lt hj, Nat.cast_zero, mul_zero, zero_mul]
  · rw [stateDensityRep_coeffAt_eq_zero_of_le _ _ _
      (by rw [expMult_sdWeights_eq_card k e hk]; omega), zero_mul, zero_mul]

end Inner

section Face

variable {d : ℕ} (k : Fin d → ℕ) (J : Finset (Fin d)) (e : Fin d → ℕ) (G : ℝ → ℝ)

theorem empFaceCoef_eq_zero_of_lt (hk : ∀ i, 0 < k i) {μ : ℝ}
    (hμ : ∀ i ∈ J, 2 * (k i : ℝ) * μ < e i + 1) (q : ℕ) :
    empFaceCoef k J e G μ q = 0 := by
  unfold empFaceCoef
  split_ifs with hJ
  · have := nonempty_subtype_inJ hJ
    unfold faceInnerCoeff
    exact empInnerCoeff_eq_zero_of_lt _ _ (fun i => hk _)
      (fun i => hμ ((faceEquiv {i // inJ J i}).symm i).1 ((faceEquiv {i // inJ J i}).symm i).2) G q
  · rfl

theorem empFaceCoef_eq_zero_of_count_le (hk : ∀ i, 0 < k i) {μ : ℝ} {q : ℕ}
    (hq : (Finset.univ.filter fun i : {i // inJ J i} => 2 * (k i : ℝ) * μ = e i + 1).card ≤ q) :
    empFaceCoef k J e G μ q = 0 := by
  unfold empFaceCoef
  split_ifs with hJ
  · have := nonempty_subtype_inJ hJ
    unfold faceInnerCoeff
    refine empInnerCoeff_eq_zero_of_count_le _ _ (fun i => hk _) ((le_of_eq ?_).trans hq) G
    refine Finset.card_equiv (faceEquiv {i // inJ J i}).symm fun i => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply]
  · rfl

end Face

/-! ### Chart-leading vanishing at fixed depth -/

section BoxLeading

variable {d : ℕ} {η ζ : (Fin d → ℝ) → ℝ} (h k p : Fin d → ℕ)

theorem two_mul_le_of_boxLeading (hk : ∀ i, 0 < k i) {lam : ℝ} {m : ℕ}
    (hBL : BoxLeading h k lam m) (i : Fin d) :
    2 * (k i : ℝ) * lam ≤ h i + 1 := by
  have h1 := hBL.1 i
  unfold ratioExp at h1
  have hk' : (0 : ℝ) < 2 * (k i : ℝ) := by
    have : (0 : ℝ) < k i := by exact_mod_cast hk i
    positivity
  rw [le_div_iff₀ hk'] at h1
  linarith

/-- Below the leading exponent every depth-`p` coefficient vanishes. -/
theorem empCoeffAtDepth_eq_zero_of_boxLeading_lt (hk : ∀ i, 0 < k i) {lam : ℝ} {m : ℕ}
    (hBL : BoxLeading h k lam m)
    {μ : ℝ} (hμ : μ < lam) (q : ℕ) : empCoeffAtDepth η ζ h k p μ q = 0 := by
  unfold empCoeffAtDepth
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [Finset.sum_eq_zero fun j _ => ?_, mul_zero]
  rw [faceCoeffInt_eq_zero_of_forall _ _ _ _ _ fun w _ => empFaceCoef_eq_zero_of_lt k x.1 _ _ hk
    (fun i _ => ?_) j, mul_zero]
  have h1 := two_mul_le_of_boxLeading h k hk hBL i
  have hk' : (0 : ℝ) < 2 * (k i : ℝ) := by
    have : (0 : ℝ) < k i := by exact_mod_cast hk i
    positivity
  have h2 : 2 * (k i : ℝ) * μ < 2 * (k i : ℝ) * lam := mul_lt_mul_of_pos_left hμ hk'
  have h3 : (0 : ℝ) ≤ x.2 i := Nat.cast_nonneg _
  push_cast
  linarith

/-- At the leading exponent the coefficients of log degree `≥ m` vanish: the exact resonances of a
face are among the coordinates attaining `λ`, of which there are at most `m`. -/
theorem empCoeffAtDepth_eq_zero_of_boxLeading_deg (hk : ∀ i, 0 < k i) {lam : ℝ} {m : ℕ}
    (hBL : BoxLeading h k lam m)
    {q : ℕ} (hq : m ≤ q) : empCoeffAtDepth η ζ h k p lam q = 0 := by
  unfold empCoeffAtDepth
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [Finset.sum_eq_zero fun j hj => ?_, mul_zero]
  have hjq : q ≤ j := (Finset.mem_Ico.1 hj).1
  rw [faceCoeffInt_eq_zero_of_forall _ _ _ _ _ fun w _ =>
    empFaceCoef_eq_zero_of_count_le k x.1 _ _ hk ?_, mul_zero]
  -- the exact resonances of the face inject into the coordinates attaining `λ`
  have hcount : (Finset.univ.filter fun i : {i // inJ x.1 i} =>
      2 * (k i : ℝ) * lam = ((fun i => x.2 i + h i) i : ℕ) + 1).card ≤
      multCount (ratioExp h k) lam := by
    unfold multCount
    rw [← Finset.card_filter]
    refine Finset.card_le_card_of_injOn Subtype.val (fun i hi => ?_)
      (Subtype.val_injective.injOn)
    have hi' := Finset.mem_filter.1 (Finset.mem_coe.1 hi)
    refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩)
    replace hi := hi'
    have h1 := two_mul_le_of_boxLeading h k hk hBL i.1
    have h2 := hi.2
    push_cast at h2
    have h3 : (0 : ℝ) ≤ x.2 i.1 := Nat.cast_nonneg _
    have hk' : (0 : ℝ) < 2 * (k i.1 : ℝ) := by
      have : (0 : ℝ) < k i.1 := by exact_mod_cast hk i.1
      positivity
    unfold ratioExp
    rw [div_eq_iff hk'.ne']
    linarith
  exact hcount.trans (hBL.2.trans (hq.trans hjq))

theorem empCoeff_eq_zero_of_boxLeading_lt (hk : ∀ i, 0 < k i) {lam : ℝ} {m : ℕ}
    (hBL : BoxLeading h k lam m) {μ : ℝ}
    (hμ : μ < lam) (q : ℕ) : empCoeff η ζ h k μ q = 0 :=
  empCoeffAtDepth_eq_zero_of_boxLeading_lt h k _ hk hBL hμ q

theorem empCoeff_eq_zero_of_boxLeading_deg (hk : ∀ i, 0 < k i) {lam : ℝ} {m : ℕ}
    (hBL : BoxLeading h k lam m) {q : ℕ} (hq : m ≤ q) : empCoeff η ζ h k lam q = 0 :=
  empCoeffAtDepth_eq_zero_of_boxLeading_deg h k _ hk hBL hq

theorem empCoeffRect_eq_zero_of_boxLeading_lt (hk : ∀ i, 0 < k i) {lam : ℝ} {m : ℕ}
    (hBL : BoxLeading h k lam m) (b : Fin d → ℝ) {μ : ℝ} (hμ : μ < lam) (q : ℕ) :
    empCoeffRect η ζ h k b μ q = 0 := by
  unfold empCoeffRect scaleCoeff
  rw [Finset.sum_eq_zero fun j _ => by
    rw [empCoeff_eq_zero_of_boxLeading_lt h k hk hBL hμ j, zero_mul, zero_mul], mul_zero, mul_zero]

theorem empCoeffRect_eq_zero_of_boxLeading_deg (hk : ∀ i, 0 < k i) {lam : ℝ} {m : ℕ}
    (hBL : BoxLeading h k lam m) (b : Fin d → ℝ) {q : ℕ} (hq : m ≤ q) :
    empCoeffRect η ζ h k b lam q = 0 := by
  unfold empCoeffRect scaleCoeff
  rw [Finset.sum_eq_zero fun j hj => by
    rw [empCoeff_eq_zero_of_boxLeading_deg h k hk hBL (hq.trans (Finset.mem_Ico.1 hj).1), zero_mul,
      zero_mul], mul_zero, mul_zero]

end BoxLeading

/-! ### Multiplicity counts -/

theorem multCount_le_card {d : ℕ} (ℓ : Fin d → ℝ) (l : ℝ) : multCount ℓ l ≤ d := by
  unfold multCount
  calc ∑ i, (if ℓ i = l then 1 else 0) ≤ ∑ _i : Fin d, 1 :=
        Finset.sum_le_sum fun i _ => by split_ifs <;> simp
    _ = d := by simp

theorem exists_eq_of_multCount_pos {d : ℕ} {ℓ : Fin d → ℝ} {l : ℝ} (h : 0 < multCount ℓ l) :
    ∃ i, ℓ i = l := by
  by_contra hnot
  push Not at hnot
  have : multCount ℓ l = 0 := by
    unfold multCount
    exact Finset.sum_eq_zero fun i _ => if_neg (hnot i)
  omega

/-- The ratio exponents lie on the chart lattice. -/
theorem ratioExp_eq_div_Qamb {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (i : Fin d) :
    ∃ m : ℕ, ratioExp h k i = (m : ℝ) / Qamb k := by
  refine ⟨(h i + 1) * ∏ j ∈ Finset.univ.erase i, k j, ?_⟩
  unfold ratioExp Qamb
  have hprod : ∏ j, k j = k i * ∏ j ∈ Finset.univ.erase i, k j := by
    rw [Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have hki : (0 : ℝ) < k i := by exact_mod_cast hk i
  have hP : (0 : ℝ) < ∏ j ∈ Finset.univ.erase i, (k j : ℝ) :=
    Finset.prod_pos fun j _ => by exact_mod_cast hk _
  rw [hprod]
  push_cast
  field_simp

/-! ### The resolved statements -/

namespace ResolvedData

variable {d : ℕ} {Ξ : ResolvedData d} {Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior}
  (ξ : Ξ.SmoothRootField Y)

namespace SmoothRootField

theorem pieceCoeff_eq_zero_of_chartLeading_lt {lam : ℝ} {m : ℕ} (hCL : Ξ.ChartLeading Y lam m)
    (p : (Ξ.X Y).PIdx) {μ : ℝ} (hμ : μ < lam) (q : ℕ) : ξ.pieceCoeff p μ q = 0 := by
  unfold pieceCoeff
  rw [integral_congr_ae (Eventually.of_forall fun s =>
    empCoeffRect_eq_zero_of_boxLeading_lt _ _ ((Ξ.X Y).kA_pos p) (hCL p) _ hμ q), integral_zero]

theorem pieceCoeff_eq_zero_of_chartLeading_deg {lam : ℝ} {m : ℕ} (hCL : Ξ.ChartLeading Y lam m)
    (p : (Ξ.X Y).PIdx) {q : ℕ} (hq : m ≤ q) : ξ.pieceCoeff p lam q = 0 := by
  unfold pieceCoeff
  rw [integral_congr_ae (Eventually.of_forall fun s =>
    empCoeffRect_eq_zero_of_boxLeading_deg _ _ ((Ξ.X Y).kA_pos p) (hCL p) _ hq), integral_zero]

theorem resolvedCoeff_eq_zero_of_chartLeading_lt {lam : ℝ} {m : ℕ} (hCL : Ξ.ChartLeading Y lam m)
    {μ : ℝ} (hμ : μ < lam) (q : ℕ) : ξ.resolvedCoeff μ q = 0 :=
  Finset.sum_eq_zero fun p _ => ξ.pieceCoeff_eq_zero_of_chartLeading_lt hCL p hμ q

theorem resolvedCoeff_eq_zero_of_chartLeading_deg {lam : ℝ} {m : ℕ} (hCL : Ξ.ChartLeading Y lam m)
    {q : ℕ} (hq : m ≤ q) : ξ.resolvedCoeff lam q = 0 :=
  Finset.sum_eq_zero fun p _ => ξ.pieceCoeff_eq_zero_of_chartLeading_deg hCL p hq

/-- A point of a chart lattice lies on the common lattice. -/
theorem exists_nat_div_commonQ_of_Qamb (p : (Ξ.X Y).PIdx) {μ : ℝ}
    (hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb ((Ξ.X Y).kA p)) :
    ∃ m : ℕ, μ = (m : ℝ) / (Ξ.decomp Y).commonQ := by
  obtain ⟨m, hm⟩ := hμ
  obtain ⟨c, hc⟩ := Qamb_kA_dvd_commonQ (Ξ := Ξ) (Y := Y) p
  have hQ : (0 : ℝ) < Qamb ((Ξ.X Y).kA p) := by exact_mod_cast Qamb_pos _ ((Ξ.X Y).kA_pos p)
  have hc0 : (0 : ℝ) < c := by
    have : 0 < Qamb ((Ξ.X Y).kA p) * c := hc ▸ (Ξ.decomp Y).commonQ_pos
    exact_mod_cast Nat.pos_of_mul_pos_left this
  refine ⟨m * c, ?_⟩
  rw [hm, hc]
  push_cast
  field_simp

theorem resolvedCoeff_eq_zero_of_not_lattice {μ : ℝ}
    (hμ : ∀ m : ℕ, μ ≠ (m : ℝ) / (Ξ.decomp Y).commonQ) (q : ℕ) : ξ.resolvedCoeff μ q = 0 :=
  Finset.sum_eq_zero fun p _ => ξ.pieceCoeff_eq_zero_of_not_lattice p
    (fun m hm => by
      obtain ⟨m', hm'⟩ := exists_nat_div_commonQ_of_Qamb (Ξ := Ξ) (Y := Y) p ⟨m, hm⟩
      exact hμ m' hm') q

/-- If a piece realises the multiplicity `m ≥ 1` at `λ`, then `λ` is a ratio exponent of the piece,
hence a point of the common lattice. -/
theorem exists_nat_div_commonQ_of_multCount_eq (p : (Ξ.X Y).PIdx) {lam : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (h : multCount (ratioExp ((Ξ.X Y).hA p) ((Ξ.X Y).kA p)) lam = m) :
    ∃ m' : ℕ, lam = (m' : ℝ) / (Ξ.decomp Y).commonQ := by
  have hpos : 0 < multCount (ratioExp ((Ξ.X Y).hA p) ((Ξ.X Y).kA p)) lam := by rw [h]; exact hm
  obtain ⟨i, hi⟩ := exists_eq_of_multCount_pos hpos
  refine exists_nat_div_commonQ_of_Qamb (Ξ := Ξ) (Y := Y) p ?_
  rw [← hi]
  exact ratioExp_eq_div_Qamb _ _ ((Ξ.X Y).kA_pos p) i

/-- The piece face limit vanishes unless the piece realises the multiplicity. -/
theorem pieceFaceLimit_eq_zero_of_ne (p : (Ξ.X Y).PIdx) {lam : ℝ} {m : ℕ}
    (h : multCount (ratioExp ((Ξ.X Y).hA p) ((Ξ.X Y).kA p)) lam ≠ m)
    (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1)) : Ξ.pieceFaceLimit Y p ξ.toRootField lam m s = 0 := by
  unfold pieceFaceLimit boxFaceLimit
  rw [if_neg h]

/-- ★★★ **Leading consistency**: under the chart-leading hypothesis the resolved empirical
coefficient at `(λ, m−1)` is the leading face limit of `hasLeadingTerm_empZ`,
`∑_p ∫_{Base_p} pieceFaceLimit_p dν_p` — the face formula with `S_λ(ψ̂)/Γ(λ)`. -/
theorem resolvedCoeff_leading {M : ℝ} (hM : ∀ P, |ξ.ψ P| ≤ M) {lam : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hCL : Ξ.ChartLeading Y lam m) :
    ξ.resolvedCoeff lam (m - 1) =
      ∑ p, ∫ s, Ξ.pieceFaceLimit Y p ξ.toRootField lam m s ∂(Ξ.piecePresentation Y p).ν := by
  have hlead := Ξ.hasLeadingTerm_empZ Y ξ.toRootField hm hCL hM
  -- the two degenerate cases: `λ` off the lattice, or `m − 1` above the common degree
  have hzero_rhs :
      (∀ p : (Ξ.X Y).PIdx, multCount (ratioExp ((Ξ.X Y).hA p) ((Ξ.X Y).kA p)) lam ≠ m) →
      ∑ p, ∫ s, Ξ.pieceFaceLimit Y p ξ.toRootField lam m s ∂(Ξ.piecePresentation Y p).ν = 0 :=
    fun hne => Finset.sum_eq_zero fun p _ => by
      rw [integral_congr_ae (Eventually.of_forall fun s =>
        ξ.pieceFaceLimit_eq_zero_of_ne p (hne p) s), integral_zero]
  by_cases hlat : ∃ m' : ℕ, lam = (m' : ℝ) / (Ξ.decomp Y).commonQ
  · by_cases hdeg : m - 1 ≤ (Ξ.decomp Y).commonD
    · have hfirst : ∀ q ∈ admissible (Ξ.decomp Y).commonD (Ξ.decomp Y).commonQ,
          precedes q (lam, m - 1) → ξ.resolvedCoeff q.1 q.2 = 0 := by
        rintro ⟨ν, j⟩ _ hpre
        rcases hpre with hlt | ⟨heq, hj⟩
        · exact ξ.resolvedCoeff_eq_zero_of_chartLeading_lt hCL hlt j
        · simp only at heq hj
          rw [heq]
          exact ξ.resolvedCoeff_eq_zero_of_chartLeading_deg hCL (by omega)
      have h1 := CutoffExpansion.hasLeadingTerm_of_first (Ξ.decomp Y).commonQ_pos
        (ξ.empZ_cutoffExpansion hM) hlat hdeg hfirst
      exact tendsto_nhds_unique h1 hlead
    · -- `m` exceeds every piece dimension: both sides vanish
      have hne : ∀ p : (Ξ.X Y).PIdx,
          multCount (ratioExp ((Ξ.X Y).hA p) ((Ξ.X Y).kA p)) lam ≠ m := by
        intro p hp
        have h1 := multCount_le_card (ratioExp ((Ξ.X Y).hA p) ((Ξ.X Y).kA p)) lam
        have h2 := da_sub_one_le_commonD (Ξ := Ξ) (Y := Y) p
        omega
      rw [hzero_rhs hne]
      exact Finset.sum_eq_zero fun p _ => ξ.pieceCoeff_eq_zero_of_degree_gt p (by
        have := da_sub_one_le_commonD (Ξ := Ξ) (Y := Y) p
        omega)
  · -- `λ` off the common lattice: no piece realises the multiplicity, and the coefficient vanishes
    have hne : ∀ p : (Ξ.X Y).PIdx, multCount (ratioExp ((Ξ.X Y).hA p) ((Ξ.X Y).kA p)) lam ≠ m :=
      fun p hp => hlat (exists_nat_div_commonQ_of_multCount_eq (Ξ := Ξ) (Y := Y) p hm hp)
    rw [hzero_rhs hne]
    exact ξ.resolvedCoeff_eq_zero_of_not_lattice (fun m' hm' => hlat ⟨m', hm'⟩) _

/-- For a test vanishing near `D_{m+1}` the leading resolved coefficient is the integral against
the empirical stratum measure. -/
theorem resolvedCoeff_leading_eq_integral {M : ℝ} (hM : ∀ P, |ξ.ψ P| ≤ M) {lam : ℝ} (hμ : 0 < lam)
    {m : ℕ} (hm : 1 ≤ m) (hCL : Ξ.ChartLeading Y lam m) (hFt : Ξ.IsTest m Ξ.F) :
    ξ.resolvedCoeff lam (m - 1) =
      ∫ x, Ξ.F x.1 ∂(Ξ.empiricalStratumMeasure Y ξ.toRootField lam m) := by
  rw [ξ.resolvedCoeff_leading hM hm hCL]
  exact Ξ.integral_empiricalStratumMeasure_eq_sum Y ξ.toRootField hμ hCL hFt ▸ rfl

end SmoothRootField

end ResolvedData

end SmoothEngine

end Grammar
