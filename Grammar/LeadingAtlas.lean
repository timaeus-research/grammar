/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SymmetricVariableUnitCells
import Grammar.AdaptedPieceAtlas

/-!
# The abstract leading atlas (CCLVIII)

The chart–stratum assembly consumes a finite atlas of cells only through four quantities and a
certificate: the cell integral `Z_i`, its coefficient, its exponent pair `(λ_i, m_i)` and
`HasLeadingTerm Z_i c_i λ_i (m_i − 1)`, together with the exact decomposition
`Z = ∑ Z_i` for `N ≥ 0`. This module extracts that boundary:

* `LeadingCell` (integral, coeff, lam, mult, hasLeadingTerm) and `FiniteLeadingAtlas Z`, with the
  tied set and the extremal leading-term theorem `hasLeadingTerm_of_extremal` proved once;
* the conversions `ScalarUnitCell.toLeading`, `VarUnitCell.toLeading`,
  `FiniteScalarUnitAtlas.toLeading`; the concrete **variable-unit atlas** `FiniteVarUnitAtlas`
  with `toLeading` and the orthant atlas `VarUnitCell.symAtlas`;
* the generic global theorem `ResolutionCover.hasLeadingTerm_boltzmannIntegral_of_leadingAtlases`
  (a leading atlas per chart–stratum pair, dominated by `(λ₀, k₀)`) with the coefficient selector
  `leadingAtlasPieceCoeff`; the scalar selector is its specialisation
  (`scalarAtlasPieceCoeff'_eq_leading`, by `rfl`), so the landed scalar theorem is the scalar
  instance of the generic one;
* **extension independence** of variable-unit cells: replacing the amplitude and the unit by
  functions agreeing with them on the base times the closed normal ball changes neither the
  orthant integral, nor the coefficient, nor the symmetric integral (`VarUnitCell.withData`,
  `withData_integral`, `withData_coeff`, `withData_symIntegral`).

No downstream scalar statement changes; positivity and residual-face computations stay on the
concrete cells.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-! ### The abstract cell and atlas -/

/-- **An abstract leading cell**: an integral with a leading-term certificate at `(lam, mult − 1)`.
The coefficient may be zero. -/
structure LeadingCell where
  /-- The cell integral. -/
  integral : ℝ → ℝ
  /-- The leading coefficient. -/
  coeff : ℝ
  /-- The exponent. -/
  lam : ℝ
  /-- The multiplicity (the log degree is `mult − 1`). -/
  mult : ℕ
  hasLeadingTerm : HasLeadingTerm integral coeff lam (mult - 1)

/-- **A finite leading atlas** of `Z`: finitely many leading cells summing to `Z` for `N ≥ 0`. -/
structure FiniteLeadingAtlas (Z : ℝ → ℝ) where
  /-- The cell index type. -/
  ι : Type
  [fintype : Fintype ι]
  /-- The cells. -/
  cell : ι → LeadingCell
  /-- The exact decomposition. -/
  eq : ∀ N : ℝ, 0 ≤ N → Z N = ∑ i, (cell i).integral N

namespace FiniteLeadingAtlas

variable {Z : ℝ → ℝ} (At : FiniteLeadingAtlas Z)

attribute [instance] FiniteLeadingAtlas.fintype

/-- The tied cells at a nominated pair. -/
noncomputable def tied (lam₀ : ℝ) (k₀ : ℕ) : Finset At.ι :=
  Finset.univ.filter fun i => (At.cell i).lam = lam₀ ∧ (At.cell i).mult - 1 = k₀

/-- **The leading term of a leading atlas at a pair dominating every cell.** -/
theorem hasLeadingTerm_of_extremal (lam₀ : ℝ) (k₀ : ℕ) (hlam : ∀ i, lam₀ ≤ (At.cell i).lam)
    (hk : ∀ i, (At.cell i).lam = lam₀ → (At.cell i).mult - 1 ≤ k₀) :
    HasLeadingTerm Z (∑ i ∈ At.tied lam₀ k₀, (At.cell i).coeff) lam₀ k₀ := by
  have h := hasLeadingTerm_sum_of_extremal Finset.univ (fun i N => (At.cell i).integral N)
    (fun i => (At.cell i).coeff) (fun i => (At.cell i).lam) (fun i => (At.cell i).mult - 1) lam₀ k₀
    (fun i _ => (At.cell i).hasLeadingTerm) (fun i _ => hlam i) (fun i _ => hk i)
  exact h.congr' ((eventually_ge_atTop 0).mono fun N hN => (At.eq N hN).symm)

end FiniteLeadingAtlas

/-! ### Conversions from the concrete cells -/

/-- A scalar-unit cell as a leading cell. -/
noncomputable def ScalarUnitCell.toLeading {t : ℕ} (c : ScalarUnitCell t) : LeadingCell :=
  ⟨c.integral, c.coeff, c.lam, c.mult, c.hasLeadingTerm⟩

/-- A variable-unit cell as a leading cell. -/
noncomputable def VarUnitCell.toLeading {t : ℕ} (c : VarUnitCell t) : LeadingCell :=
  ⟨c.integral, c.coeff, c.lam, c.mult, c.hasLeadingTerm⟩

/-- A scalar-unit atlas as a leading atlas. -/
noncomputable def FiniteScalarUnitAtlas.toLeading {t : ℕ} {Z : ℝ → ℝ}
    (At : FiniteScalarUnitAtlas t Z) : FiniteLeadingAtlas Z where
  ι := At.ι
  cell := fun i => (At.cell i).toLeading
  eq := At.eq

theorem FiniteScalarUnitAtlas.toLeading_tied {t : ℕ} {Z : ℝ → ℝ} (At : FiniteScalarUnitAtlas t Z)
    (lam₀ : ℝ) (k₀ : ℕ) : At.toLeading.tied lam₀ k₀ = At.tied lam₀ k₀ := rfl

/-! ### The variable-unit atlas -/

/-- **A finite variable-unit atlas** of `Z`. -/
structure FiniteVarUnitAtlas (t : ℕ) (Z : ℝ → ℝ) where
  /-- The cell index type. -/
  ι : Type
  [fintype : Fintype ι]
  /-- The cells. -/
  cell : ι → VarUnitCell t
  /-- The exact decomposition. -/
  eq : ∀ N : ℝ, 0 ≤ N → Z N = ∑ i, (cell i).integral N

namespace FiniteVarUnitAtlas

variable {t : ℕ} {Z : ℝ → ℝ} (At : FiniteVarUnitAtlas t Z)

attribute [instance] FiniteVarUnitAtlas.fintype

/-- The tied cells at a nominated pair. -/
noncomputable def tied (lam₀ : ℝ) (k₀ : ℕ) : Finset At.ι :=
  Finset.univ.filter fun i => (At.cell i).lam = lam₀ ∧ (At.cell i).mult - 1 = k₀

/-- The variable-unit atlas as a leading atlas. -/
noncomputable def toLeading : FiniteLeadingAtlas Z where
  ι := At.ι
  cell := fun i => (At.cell i).toLeading
  eq := At.eq

theorem toLeading_tied (lam₀ : ℝ) (k₀ : ℕ) : At.toLeading.tied lam₀ k₀ = At.tied lam₀ k₀ := rfl

/-- **The leading term of a variable-unit atlas at a pair dominating every cell.** -/
theorem hasLeadingTerm_of_extremal (lam₀ : ℝ) (k₀ : ℕ) (hlam : ∀ i, lam₀ ≤ (At.cell i).lam)
    (hk : ∀ i, (At.cell i).lam = lam₀ → (At.cell i).mult - 1 ≤ k₀) :
    HasLeadingTerm Z (∑ i ∈ At.tied lam₀ k₀, (At.cell i).coeff) lam₀ k₀ :=
  At.toLeading.hasLeadingTerm_of_extremal lam₀ k₀ hlam hk

end FiniteVarUnitAtlas

/-- **The orthant atlas of a symmetric variable-unit cell.** -/
noncomputable def VarUnitCell.symAtlas {t : ℕ} (c : VarUnitCell t) :
    FiniteVarUnitAtlas t c.symIntegral where
  ι := Fin (c.n + 1) → Bool
  cell := c.reflected
  eq := fun _ hN => c.symIntegral_eq_sum hN

/-! ### The generic global theorem -/

namespace ResolutionCover

open Monomialize.Analytic Monomialize.VolumeScaling

variable {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι)

/-- The coefficient of the chart–stratum pair `(i, I)` from its leading atlas. -/
noncomputable def leadingAtlasPieceCoeff {e : ι → Fin d →₀ ℕ} {Z : ι → Finset (Fin d) → ℝ → ℝ}
    (At : ∀ (i : ι) (I : Finset (Fin d)), I ⊆ (e i).support → I.Nonempty →
      FiniteLeadingAtlas (Z i I))
    (lam₀ : ℝ) (k₀ : ℕ) (i : ι) (I : Finset (Fin d)) : ℝ :=
  open scoped Classical in
  if hI : I ⊆ (e i).support ∧ I.Nonempty then
    ∑ j ∈ (At i I hI.1 hI.2).tied lam₀ k₀, ((At i I hI.1 hI.2).cell j).coeff
  else 0

omit [Fintype ι] in
/-- The scalar coefficient selector is the leading selector of the converted atlases. -/
theorem scalarAtlasPieceCoeff'_eq_leading {e : ι → Fin d →₀ ℕ} {Z : ι → Finset (Fin d) → ℝ → ℝ}
    {tdim : ι → Finset (Fin d) → ℕ}
    (At : ∀ (i : ι) (I : Finset (Fin d)), I ⊆ (e i).support → I.Nonempty →
      FiniteScalarUnitAtlas (tdim i I) (Z i I)) (lam₀ : ℝ) (k₀ : ℕ) :
    scalarAtlasPieceCoeff' At lam₀ k₀ =
      leadingAtlasPieceCoeff (fun i I hI hne => (At i I hI hne).toLeading) lam₀ k₀ := rfl

/-- **The conditional global leading coefficient with leading atlases**: a finite leading atlas
of every nonempty chart–stratum piece integral, all cells dominated by `(λ₀, k₀)`, gives the leading
term of the Boltzmann integral at `(λ₀, k₀)` with coefficient the sum of the tied cell
coefficients. -/
theorem hasLeadingTerm_boltzmannIntegral_of_leadingAtlases (e h : ι → Fin d →₀ ℕ)
    (W : ι → Set (Fin d → ℝ)) {K : (Fin d → ℝ) → ℝ}
    (hc : ∀ i, IsMonomialChart K (R.chart i).φ (R.chart i).dom (e i) (h i) (W i)) {ε : ℝ}
    (hε : 0 < ε) {F : (Fin d → ℝ) → ℝ} {p : TubeWeight d} (hFm : Measurable F)
    (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
    (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x)
    (At : ∀ (i : ι) (I : Finset (Fin d)), I ⊆ (e i).support → I.Nonempty →
      FiniteLeadingAtlas (R.pieceIntegral (fun i => (e i).support) ε i I F K p))
    (lam₀ : ℝ) (k₀ : ℕ)
    (hlam : ∀ (i : ι) (I : Finset (Fin d)) (hI : I ⊆ (e i).support) (hne : I.Nonempty)
      (j : (At i I hI hne).ι), lam₀ ≤ ((At i I hI hne).cell j).lam)
    (hk : ∀ (i : ι) (I : Finset (Fin d)) (hI : I ⊆ (e i).support) (hne : I.Nonempty)
      (j : (At i I hI hne).ι),
      ((At i I hI hne).cell j).lam = lam₀ → ((At i I hI hne).cell j).mult - 1 ≤ k₀) :
    HasLeadingTerm (R.boltzmannIntegral F K p)
      (∑ i, ∑ I ∈ (e i).support.powerset.filter (fun I => I.Nonempty),
        leadingAtlasPieceCoeff At lam₀ k₀ i I) lam₀ k₀ := by
  have hmain := R.hasLeadingTerm_boltzmannIntegral_of_monomial e h W hc hε hFm hF hK hK0
    (leadingAtlasPieceCoeff At lam₀ k₀) (fun _ _ => lam₀) (fun _ _ => k₀) lam₀ k₀
    (fun i I hI => by
      obtain ⟨hpow, hne⟩ := Finset.mem_filter.1 hI
      have hsub : I ⊆ (e i).support := Finset.mem_powerset.1 hpow
      unfold leadingAtlasPieceCoeff
      rw [dif_pos ⟨hsub, hne⟩]
      exact (At i I hsub hne).hasLeadingTerm_of_extremal lam₀ k₀ (hlam i I hsub hne)
        (hk i I hsub hne))
    (fun _ _ _ => le_rfl) (fun _ _ _ _ => le_rfl)
  have hcoef : ∀ i : ι, (∑ I ∈ ((e i).support.powerset.filter (fun I => I.Nonempty)).filter
      (fun _ => lam₀ = lam₀ ∧ k₀ = k₀), leadingAtlasPieceCoeff At lam₀ k₀ i I) =
      ∑ I ∈ (e i).support.powerset.filter (fun I => I.Nonempty),
        leadingAtlasPieceCoeff At lam₀ k₀ i I :=
    fun i => by rw [Finset.filter_true_of_mem fun _ _ => ⟨rfl, rfl⟩]
  beta_reduce at hmain
  rw [Finset.sum_congr rfl fun i _ => hcoef i] at hmain
  exact hmain

end ResolutionCover

/-! ### Extension independence of variable-unit cells -/

/-- `(−b,b]^r` lies in the closed ball of radius `b`. -/
theorem piBox_Ioc_neg_subset_closedBall {r : ℕ} {b : ℝ} (hb : 0 ≤ b) :
    piBox r (Ioc (-b) b) ⊆ Metric.closedBall (0 : Fin r → ℝ) b := by
  intro v hv
  rw [mem_closedBall_zero_iff]
  refine (pi_norm_le_iff_of_nonneg hb).2 fun i => ?_
  have := hv i (mem_univ i)
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨this.1.le, this.2⟩

namespace VarUnitCell

variable {t : ℕ} (c : VarUnitCell t)
  (A' u' : (Fin t → ℝ) → (Fin (c.n + 1) → ℝ) → ℝ) (hA' : Continuous (Function.uncurry A'))
  (hu' : Continuous (Function.uncurry u'))
  (hu'_pos : ∀ z ∈ c.base, ∀ v ∈ Metric.closedBall (0 : Fin (c.n + 1) → ℝ) c.b, 0 < u' z v)

/-- **The cell with replaced amplitude and unit** (same exponents, radius, base and weight). -/
def withData : VarUnitCell t where
  n := c.n
  h := c.h
  k := c.k
  k_pos := c.k_pos
  b := c.b
  b_pos := c.b_pos
  A := A'
  A_cont := hA'
  base := c.base
  base_compact := c.base_compact
  βw := c.βw
  βw_int := c.βw_int
  u := u'
  u_cont := hu'
  u_pos := hu'_pos

theorem withData_lam : (c.withData A' u' hA' hu' hu'_pos).lam = c.lam := rfl

theorem withData_mult : (c.withData A' u' hA' hu' hu'_pos).mult = c.mult := rfl

variable (hA : ∀ z ∈ c.base, ∀ v ∈ Metric.closedBall (0 : Fin (c.n + 1) → ℝ) c.b, A' z v = c.A z v)
  (hu : ∀ z ∈ c.base, ∀ v ∈ Metric.closedBall (0 : Fin (c.n + 1) → ℝ) c.b, u' z v = c.u z v)

include hA hu in
/-- **Extension independence of the orthant integral.** -/
theorem withData_integral (N : ℝ) :
    (c.withData A' u' hA' hu' hu'_pos).integral N = c.integral N := by
  unfold integral
  refine setIntegral_congr_fun c.base_compact.isClosed.measurableSet fun z hz => ?_
  congr 1
  change varBoxKernel c.n c.h c.k c.b u' A' z N = _
  unfold varBoxKernel
  refine setIntegral_congr_fun measurableSet_piBox_Ioc_pos fun v hv => ?_
  have hv' := piBox_Ioc_subset_closedBall c.b_pos hv
  rw [hA z hz v hv', hu z hz v hv']

include hA hu in
/-- **Extension independence of the coefficient**: the projected face points lie in the closed
box. -/
theorem withData_coeff : (c.withData A' u' hA' hu' hu'_pos).coeff = c.coeff := by
  unfold coeff
  refine setIntegral_congr_fun c.base_compact.isClosed.measurableSet fun z hz => ?_
  congr 1
  change varBoxFaceCoeff c.n c.h c.k c.b u' A' c.lam z = _
  unfold varBoxFaceCoeff
  refine boxFaceCoeff_congr c.b_pos.le fun v hv => ?_
  have hv' := piBox_Icc_subset_closedBall c.b_pos.le hv
  change A' z v * u' z v ^ (-c.lam) = c.A z v * c.u z v ^ (-c.lam)
  rw [hA z hz v hv', hu z hz v hv']

include hA hu in
/-- **Extension independence of the symmetric integral.** -/
theorem withData_symIntegral (N : ℝ) :
    (c.withData A' u' hA' hu' hu'_pos).symIntegral N = c.symIntegral N := by
  unfold symIntegral
  refine setIntegral_congr_fun c.base_compact.isClosed.measurableSet fun z hz => ?_
  congr 1
  change symVarKernel c.n c.h c.k c.b u' A' z N = _
  unfold symVarKernel
  refine setIntegral_congr_fun (measurableSet_piBox _ _ measurableSet_Ioc) fun v hv => ?_
  have hv' := piBox_Ioc_neg_subset_closedBall c.b_pos.le hv
  rw [hA z hz v hv', hu z hz v hv']

end VarUnitCell

end Grammar
