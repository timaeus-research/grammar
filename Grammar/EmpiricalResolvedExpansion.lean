/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.EmpiricalPieceExpansion
import Grammar.EmpiricalResolvedLeading

/-!
# The resolved empirical expansion: empirical Theorem E on the resolved manifold
(§20 Stage 7, part 3)

A **smooth root field** is a root field whose branch representative on every piece is the pull-back
of a smooth function on the chart coordinate space along the affine chart map of the piece
(`SmoothRootField`: `loc p (s, v) = Lψ p (Tm p s v)`, smooth up to the walls, sector sign absorbed
piece by piece). For a bounded smooth root field the empirical partition function
`Z^emp_N[F; ψ] = ∫_U F e^{−N K∘π + √N √(K∘π) ψ} dμ_U` decomposes into the empirical piece integrals
and an exponentially small tail (`empZ_eq_sum`, `abs_integral_tail_le`); each piece integral is the
base integral of the rectangle kernels of its piece field family and has the cutoff expansion of
`EmpiricalPieceExpansion` on its chart lattice (★ `empPieceInt_cutoffExpansion`); refined to the
common lattice and padded to the common degree of the resolved core decomposition, the pieces sum
and the tail contributes nothing:
★★★ `empZ_cutoffExpansion`: `Z^emp[F; ψ]` is a `CutoffExpansion` on `commonQ⁻¹ℕ` with logarithmic
degree `≤ commonD ≤ d − 1` — the SAME lattice and degree as the population expansion — with the
canonical coefficients `empResolvedCoeff` (★★ `empResolvedCoeff_unique`), and at zero field the
coefficients are the population resolved coefficients `Ξ.coeff Y` (★★ `empResolvedCoeff_zero`).
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Finset
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing Grammar.NormalCrossing.EvenChartBoxDepth

namespace Grammar

namespace SmoothEngine

namespace ResolvedData

variable {d : ℕ} (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-! ### Smooth root fields -/

/-- A **smooth root field**: a root field whose branch representatives are pull-backs of smooth
functions on the chart coordinate spaces along the affine chart maps of the pieces. -/
structure SmoothRootField extends Ξ.RootField Y where
  /-- the smooth chart representative of the field on the piece -/
  Lψ : (Ξ.X Y).PIdx → (Fin d → ℝ) → ℝ
  Lψ_smooth : ∀ p, ContDiff ℝ ∞ (Lψ p)
  loc_eq_Lψ : ∀ (p : (Ξ.X Y).PIdx)
    (z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ)),
    loc p z = Lψ p ((Ξ.X Y).Tm p z.1 z.2)

namespace SmoothRootField

/-- The zero field is a smooth root field. -/
def zero : Ξ.SmoothRootField Y :=
  { RootField.zero Ξ Y with
    Lψ := fun _ _ => 0
    Lψ_smooth := fun _ => contDiff_const
    loc_eq_Lψ := fun _ _ => rfl }

variable {Ξ Y} (ξ : Ξ.SmoothRootField Y)

/-- The chart map of a piece is the affine chart map. -/
theorem Tm_eq (p : (Ξ.X Y).PIdx) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1))
    (v : Fin ((Ξ.X Y).da p) → ℝ) :
    (Ξ.X Y).Tm p s v = affineMap ((Ξ.X Y).eqv p) p.2 ((Ξ.X Y).sc p s) v := rfl

/-- The amplitude of a piece is the pull-back of the extended chart amplitude. -/
theorem amp_eq (p : (Ξ.X Y).PIdx) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1))
    (v : Fin ((Ξ.X Y).da p) → ℝ) :
    (Ξ.amp Y p).amp s v = Ξ.G Y p.1 (affineMap ((Ξ.X Y).eqv p) p.2 ((Ξ.X Y).sc p s) v) := rfl

/-- The empirical piece kernel is the rectangle kernel of the piece field family. -/
theorem empPieceKernel_eq (p : (Ξ.X Y).PIdx) (N : ℝ) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1)) :
    Ξ.empPieceKernel Y p ξ.toRootField N s =
      empIntegralRect (fun v => Ξ.G Y p.1 (affineMap ((Ξ.X Y).eqv p) p.2 ((Ξ.X Y).sc p s) v))
        (fun v => ξ.Lψ p (affineMap ((Ξ.X Y).eqv p) p.2 ((Ξ.X Y).sc p s) v))
        ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) (fun _ => Y.T.a p.1) N := by
  unfold empPieceKernel empBoxIntegral empIntegralRect
  rw [rect_const]
  refine setIntegral_congr_fun (measurableSet_box _) fun v _ => ?_
  beta_reduce
  rw [ξ.loc_eq_Lψ p (s, v)]
  rfl

/-- The empirical piece integral is the base integral of the rectangle kernels. -/
theorem empPieceInt_eq (p : (Ξ.X Y).PIdx) (N : ℝ) :
    Ξ.empPieceInt Y p ξ.toRootField N =
      ∫ s, empIntegralRect (fun v => Ξ.G Y p.1 (affineMap ((Ξ.X Y).eqv p) p.2 ((Ξ.X Y).sc p s) v))
        (fun v => ξ.Lψ p (affineMap ((Ξ.X Y).eqv p) p.2 ((Ξ.X Y).sc p s) v))
        ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) (fun _ => Y.T.a p.1) N ∂(Ξ.piecePresentation Y p).ν := by
  unfold empPieceInt
  exact integral_congr_ae (Eventually.of_forall fun s => ξ.empPieceKernel_eq p N s)

/-- The empirical piece coefficients: the base integrals of the rectangle coefficients. -/
noncomputable def pieceCoeff (p : (Ξ.X Y).PIdx) (μ : ℝ) (q : ℕ) : ℝ :=
  ∫ s, empCoeffRect (fun v => Ξ.G Y p.1 (affineMap ((Ξ.X Y).eqv p) p.2 ((Ξ.X Y).sc p s) v))
    (fun v => ξ.Lψ p (affineMap ((Ξ.X Y).eqv p) p.2 ((Ξ.X Y).sc p s) v))
    ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) (fun _ => Y.T.a p.1) μ q ∂(Ξ.piecePresentation Y p).ν

/-- ★ **The empirical expansion of a piece of the resolved transport.** -/
theorem empPieceInt_cutoffExpansion (p : (Ξ.X Y).PIdx) :
    CutoffExpansion (Qamb ((Ξ.X Y).kA p)) ((Ξ.X Y).da p - 1) (Ξ.empPieceInt Y p ξ.toRootField)
      (ξ.pieceCoeff p) := by
  have := (Ξ.piecePresentation Y p).isFiniteMeasure_ν
  have h := empRect_cutoffExpansion_integral ((Ξ.X Y).eqv p) p.2 (Ξ.G Y p.1) (ξ.Lψ p)
    (Ξ.piecePresentation Y p).ν (Ξ.contDiff_G Y p.1) (ξ.Lψ_smooth p) ((Ξ.X Y).continuous_sc p)
    (Y.T.a_pos p.1) ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) ((Ξ.X Y).kA_pos p)
  have hZ : (fun N => ∫ s, empIntegralRect
      (fun v => Ξ.G Y p.1 (affineMap ((Ξ.X Y).eqv p) p.2 ((Ξ.X Y).sc p s) v))
      (fun v => ξ.Lψ p (affineMap ((Ξ.X Y).eqv p) p.2 ((Ξ.X Y).sc p s) v))
      ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) (fun _ => Y.T.a p.1) N ∂(Ξ.piecePresentation Y p).ν) =
      Ξ.empPieceInt Y p ξ.toRootField := funext fun N => (ξ.empPieceInt_eq p N).symm
  rw [hZ] at h
  exact h

/-! ### The common lattice and degree -/

theorem Qamb_kA_dvd_commonQ (p : (Ξ.X Y).PIdx) :
    Qamb ((Ξ.X Y).kA p) ∣ (Ξ.decomp Y).commonQ := by
  have h := (Ξ.decomp Y).Qamb_dvd_commonQ ((Ξ.X Y).en.symm p)
  have he : (fun q : (Ξ.X Y).PIdx => Qamb ((Ξ.X Y).kA q)) ((Ξ.X Y).en ((Ξ.X Y).en.symm p)) =
      Qamb ((Ξ.X Y).kA p) := by rw [Equiv.apply_symm_apply]
  exact he ▸ h

theorem da_sub_one_le_commonD (p : (Ξ.X Y).PIdx) :
    (Ξ.X Y).da p - 1 ≤ (Ξ.decomp Y).commonD := by
  have h := (Ξ.decomp Y).le_commonD ((Ξ.X Y).en.symm p)
  have he : (fun q : (Ξ.X Y).PIdx => (Ξ.X Y).da q - 1) ((Ξ.X Y).en ((Ξ.X Y).en.symm p)) =
      (Ξ.X Y).da p - 1 := by rw [Equiv.apply_symm_apply]
  exact he ▸ h

theorem pieceCoeff_eq_zero_of_not_lattice (p : (Ξ.X Y).PIdx) {μ : ℝ}
    (hμ : ∀ m : ℕ, μ ≠ (m : ℝ) / Qamb ((Ξ.X Y).kA p)) (j : ℕ) : ξ.pieceCoeff p μ j = 0 := by
  unfold pieceCoeff empCoeffRect
  rw [integral_congr_ae (Eventually.of_forall fun s => ?_), integral_zero]
  rw [scaleCoeff_eq_zero_of_not_lattice (fun μ' hμ' j' =>
    empCoeff_eq_zero_of_not_lattice ((Ξ.X Y).kA_pos p) hμ' j') hμ j, mul_zero]

theorem pieceCoeff_eq_zero_of_degree_gt (p : (Ξ.X Y).PIdx) {μ : ℝ} {j : ℕ}
    (hj : (Ξ.X Y).da p - 1 < j) : ξ.pieceCoeff p μ j = 0 := by
  unfold pieceCoeff empCoeffRect
  rw [integral_congr_ae (Eventually.of_forall fun s => ?_), integral_zero]
  rw [scaleCoeff_eq_zero_of_degree_gt hj, mul_zero]

/-- Each piece's expansion on the common lattice and degree. -/
theorem empPieceInt_cutoffExpansion_common (p : (Ξ.X Y).PIdx) :
    CutoffExpansion (Ξ.decomp Y).commonQ (Ξ.decomp Y).commonD (Ξ.empPieceInt Y p ξ.toRootField)
      (ξ.pieceCoeff p) :=
  ((ξ.empPieceInt_cutoffExpansion p).refine (Qamb_pos _ ((Ξ.X Y).kA_pos p))
    (Ξ.decomp Y).commonQ_pos (Qamb_kA_dvd_commonQ p)
    fun _ hμ j => ξ.pieceCoeff_eq_zero_of_not_lattice p hμ j).pad
    (da_sub_one_le_commonD p) fun _ _ hj => ξ.pieceCoeff_eq_zero_of_degree_gt p hj

/-! ### The tail and the assembly -/

/-- ★ **The resolved empirical coefficients**: the sum over the pieces of the base integrals of the
rectangle coefficients of the piece field families. -/
noncomputable def resolvedCoeff (μ : ℝ) (q : ℕ) : ℝ := ∑ p, ξ.pieceCoeff p μ q

/-- The residual `Z^emp − ∑_p Z^emp_p`, defined for every real `N`. -/
noncomputable def resid (N : ℝ) : ℝ :=
  Ξ.empZ Y ξ.toRootField N - ∑ p, Ξ.empPieceInt Y p ξ.toRootField N

theorem resid_eq {N : ℝ} (hN : 0 ≤ N) {M : ℝ} (hM : ∀ P, |ξ.ψ P| ≤ M) :
    ξ.resid N = ∫ P, Ξ.empIntegrand Y ξ.toRootField N P ∂Y.tailU := by
  rw [resid, Ξ.empZ_eq_sum Y ξ.toRootField hN hM]
  ring

theorem resid_tendsto {M : ℝ} (hM : ∀ P, |ξ.ψ P| ≤ M) :
    Tendsto (fun N => ξ.resid N * Real.exp ((Y.T.δ / 4) * N)) atTop (𝓝 0) :=
  tendsto_mul_exp_of_exp_bound (fun N hN => by
    rw [ξ.resid_eq hN hM]
    exact Ξ.abs_integral_tail_le Y ξ.toRootField hN hM) (by linarith [Y.T.δ_pos])

/-- ★★★ **The resolved empirical expansion** (empirical Theorem E on the resolved manifold, for a
bounded smooth root field): `Z^emp_N[F; ψ]` is a cutoff expansion on the common lattice
`commonQ⁻¹ℕ` with logarithmic degree `≤ commonD`, with the coefficients `resolvedCoeff`. -/
theorem empZ_cutoffExpansion {M : ℝ} (hM : ∀ P, |ξ.ψ P| ≤ M) :
    CutoffExpansion (Ξ.decomp Y).commonQ (Ξ.decomp Y).commonD (Ξ.empZ Y ξ.toRootField)
      ξ.resolvedCoeff := by
  have hsum := CutoffExpansion.sum Finset.univ fun p _ => ξ.empPieceInt_cutoffExpansion_common p
  have htail := cutoffExpansion_of_exp_small (Ξ.decomp Y).commonQ (Ξ.decomp Y).commonD
    (by linarith [Y.T.δ_pos] : (0 : ℝ) < Y.T.δ / 4) (ξ.resid_tendsto hM)
  have h := hsum.add htail
  have hZ : (fun N => ∑ p ∈ Finset.univ, Ξ.empPieceInt Y p ξ.toRootField N + ξ.resid N) =
      Ξ.empZ Y ξ.toRootField := funext fun N => by unfold resid; ring
  have hc : (fun μ j => ∑ p ∈ Finset.univ, ξ.pieceCoeff p μ j + 0) = ξ.resolvedCoeff :=
    funext fun _ => funext fun _ => by simp [resolvedCoeff]
  rw [hZ, hc] at h
  exact h

/-- ★★ **Canonicity**: any cutoff expansion of `Z^emp[F; ψ]` on the common lattice with the common
degree has the coefficients `resolvedCoeff`. -/
theorem resolvedCoeff_unique {M : ℝ} (hM : ∀ P, |ξ.ψ P| ≤ M) {c : ℝ → ℕ → ℝ}
    (hc : CutoffExpansion (Ξ.decomp Y).commonQ (Ξ.decomp Y).commonD (Ξ.empZ Y ξ.toRootField) c)
    {μ : ℝ} (hμ : ∃ m : ℕ, μ = (m : ℝ) / (Ξ.decomp Y).commonQ) {j : ℕ}
    (hj : j ≤ (Ξ.decomp Y).commonD) : c μ j = ξ.resolvedCoeff μ j :=
  CutoffExpansion.coeff_unique (Ξ.decomp Y).commonQ_pos hc (ξ.empZ_cutoffExpansion hM) hμ hj

/-! ### The zero field -/

/-- At zero field the empirical partition function is the population one. -/
theorem empZ_zero (N : ℝ) : Ξ.empZ Y (zero Ξ Y).toRootField N = Ξ.Z N := by
  unfold empZ Z empIntegrand
  refine integral_congr_ae (Eventually.of_forall fun P => ?_)
  change Real.exp (-N * Ξ.phaseU P + Real.sqrt N * Real.sqrt (Ξ.phaseU P) * 0) * Ξ.F P = _
  rw [mul_zero, add_zero, mul_comm]
  rfl

/-- ★★ **Zero-field compatibility**: the resolved empirical coefficients of the zero field are the
population resolved coefficients. -/
theorem resolvedCoeff_zero {μ : ℝ} (hμ : ∃ m : ℕ, μ = (m : ℝ) / (Ξ.decomp Y).commonQ) {j : ℕ}
    (hj : j ≤ (Ξ.decomp Y).commonD) : (zero Ξ Y).resolvedCoeff μ j = Ξ.coeff Y μ j := by
  have hpop : CutoffExpansion (Ξ.decomp Y).commonQ (Ξ.decomp Y).commonD
      (Ξ.empZ Y (zero Ξ Y).toRootField) (Ξ.coeff Y) := by
    have h := (Ξ.decomp Y).cutoffExpansion
    have hZ : (Ξ.D Y).Z = Ξ.empZ Y (zero Ξ Y).toRootField := funext fun N => by
      rw [Ξ.D_Z Y N, empZ_zero]
    rw [hZ] at h
    exact h
  exact ((zero Ξ Y).resolvedCoeff_unique (M := 0) (fun _ => by change |(0 : ℝ)| ≤ 0; simp)
    hpop hμ hj).symm

end SmoothRootField

end ResolvedData

end SmoothEngine

end Grammar
