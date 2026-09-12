/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.ResolvedGeometry
import Grammar.ConormalSplitting
import Grammar.GlobalLaplaceMeasureBasic

/-!
# Resolved normal data, moment tensors and the coordinate-free expansion statement (CCXCIX)

Unit 3 of the coordinate-free programme (`tide-log/plan_coordinate_free_expansion.md`). On top of a
resolved geometry (CCXCVIII) this file carries the chart-free NORMAL data of the strata and defines
every object appearing in the final formula, and then the final formula itself as a predicate:

* `ResolvedNormalData R A`: along each stratum `S_I` the normal spaces `N_s ⊆ A` (dimension `|I|`),
  the labelled conormal differentials `du_i (s)`, `i ∈ I` (linearly independent, so the conormal
  splitting `N^*_s ≅ ⊕_{i∈I} ℝ·du_i` of `ConormalSplitting.lean` applies), and the tubular germs
  `Φ_s : N_s → U` with `Φ_s 0 = s`.
* `normalDifferential φ I s r = D^r((φ∘π)∘Φ_s)(0)`: the paper's `D^r_⊥(φ∘π)` (CCXCVII convention).
* `MomentTensor V r := Dual (JetForm V r)`: elements of `Sym^r N_s` represented by their pairing
  with `r`-forms; `pureMoment v r = v^{⊙r}`, `pair`.
* `stratumCoefficient ν B φ I r = (1/r!) ∫_{S_I} ⟨D^r_⊥(φ∘π), B(s)⟩ dν_I(s)` and
  `expansionCoefficient = Σ_I Σ'_r stratumCoefficient`.
* ★ `HasCoordFreeExpansion R D ν B spec W K ϕ φ`: for every cutoff `A`,
  `∫_W φ ϕ e^{−nK} − Σ_{q ∈ spec A} expansionCoefficient(q) n^{−q.exponent} (log n)^{q.logDegree}
   = o(n^{−A})`.

This predicate is THE target statement of the programme: it mentions the strata, the normal
differentials, the moment-tensor coefficients, the stratum densities and the resolution map only.
Charts do not occur. Its proof (units 5–10) is where the monomial atlas certificate enters.
-/

open MeasureTheory Set Filter Topology Asymptotics Module
open scoped DirectSum

namespace Grammar

/-! ### Moment tensors -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Moment tensors** of degree `r` on `V`: the continuous dual of the `r`-forms (the pairing
representation of `Sym^r V`). -/
abbrev MomentTensor (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] (r : ℕ) : Type _ :=
  JetForm V r →L[ℝ] ℝ

namespace MomentTensor

/-- The pairing `⟨D, M⟩ = M(D)`. -/
noncomputable def pair {r : ℕ} (M : MomentTensor V r) (D : JetForm V r) : ℝ := M D

theorem pair_add {r : ℕ} (M : MomentTensor V r) (D D' : JetForm V r) :
    M.pair (D + D') = M.pair D + M.pair D' := map_add M D D'

theorem pair_smul {r : ℕ} (M : MomentTensor V r) (c : ℝ) (D : JetForm V r) :
    M.pair (c • D) = c * M.pair D := map_smul M c D

theorem add_pair {r : ℕ} (M M' : MomentTensor V r) (D : JetForm V r) :
    (M + M').pair D = M.pair D + M'.pair D := rfl

end MomentTensor

/-- **The pure moment** `v^{⊙ r}`: evaluation of `r`-forms on the diagonal `(v,…,v)`. -/
noncomputable def pureMoment (v : V) (r : ℕ) : MomentTensor V r :=
  ContinuousMultilinearMap.apply ℝ (fun _ : Fin r => V) ℝ fun _ => v

@[simp] theorem pureMoment_pair (v : V) {r : ℕ} (D : JetForm V r) :
    (pureMoment v r).pair D = D fun _ => v := rfl

/-- A power–log index `(α, j)`: the term `n^{−α} (log n)^j`. -/
structure PowerLogIndex where
  /-- The exponent `α`. -/
  exponent : ℝ
  /-- The logarithmic degree `j`. -/
  logDegree : ℕ

/-- The scale `n^{−α} (log n)^j` of a power–log index. -/
noncomputable def PowerLogIndex.scale (q : PowerLogIndex) (n : ℝ) : ℝ :=
  n ^ (-q.exponent) * Real.log n ^ q.logDegree

/-! ### Resolved normal data -/

variable {d : ℕ} {U : Type*} [TopologicalSpace U]

/-- **Resolved normal data** of a resolved geometry: normal spaces, labelled conormal
differentials and tubular germs along every stratum. -/
structure ResolvedNormalData (R : ResolvedGeometry d U) (A : Type*) [NormedAddCommGroup A]
    [InnerProductSpace ℝ A] where
  /-- The normal space at a point of the stratum `S_I`. -/
  N : ∀ I : Finset R.Component, R.Stratum I → Submodule ℝ A
  finrank_N : ∀ (I : Finset R.Component) (s : R.Stratum I), Module.finrank ℝ (N I s) = I.card
  /-- The labelled conormal differentials `du_i(s)`, `i ∈ I`. -/
  du : ∀ (I : Finset R.Component) (s : R.Stratum I), I → Module.Dual ℝ (N I s)
  du_linearIndependent : ∀ (I : Finset R.Component) (s : R.Stratum I), LinearIndependent ℝ (du I s)
  /-- The tubular germs `Φ_s : N_s → U`. -/
  Φ : ∀ (I : Finset R.Component) (s : R.Stratum I), N I s → U
  Φ_zero : ∀ (I : Finset R.Component) (s : R.Stratum I), Φ I s 0 = (s : U)
  continuousAt_Φ : ∀ (I : Finset R.Component) (s : R.Stratum I), ContinuousAt (Φ I s) 0

namespace ResolvedNormalData

variable {R : ResolvedGeometry d U} {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  (D : ResolvedNormalData R A)

/-- The conormal line `ℝ · du_i(s)` of the component `i ∈ I` at `s`. -/
noncomputable def conormalLine (I : Finset R.Component) (s : R.Stratum I) (i : I) :
    Submodule ℝ (Module.Dual ℝ (D.N I s)) :=
  Grammar.conormalLine (D.du I s) i

/-- **The conormal splitting** `⊕_{i∈I} ℝ·du_i(s) ≃ N^*_s` (fibrewise, `ConormalSplitting.lean`). -/
noncomputable def conormalSplitting (I : Finset R.Component) (s : R.Stratum I) :
    (⨁ i : I, D.conormalLine I s i) ≃ₗ[ℝ] Grammar.conormalOf (D.du I s) :=
  Grammar.conormalSplitting (D.du I s) (D.du_linearIndependent I s)

/-- **The normal differential** `D^r_⊥(φ∘π)(s) = D^r((φ∘π)∘Φ_s)(0)` of an observable on the
parameter space, along the stratum `S_I`. -/
noncomputable def normalDifferential (φ : (Fin d → ℝ) → ℝ) (I : Finset R.Component)
    (s : R.Stratum I) (r : ℕ) : JetForm (D.N I s) r :=
  Grammar.normalDifferential (D.N I) (D.Φ I) (φ ∘ R.π) s r

/-- Degree zero is the value of the observable at the image point. -/
theorem normalDifferential_zero (φ : (Fin d → ℝ) → ℝ) (I : Finset R.Component) (s : R.Stratum I)
    (m : Fin 0 → D.N I s) : D.normalDifferential φ I s 0 m = φ (R.π s) := by
  unfold normalDifferential
  rw [normalDifferential_zero_apply, Function.comp_apply, D.Φ_zero]

/-! ### Stratum coefficients and the expansion coefficient -/

variable [MeasurableSpace U]

/-- **A moment coefficient field**: for every stratum, degree and power–log index, a moment tensor
at each point of the stratum. -/
abbrev MomentCoefficientField : Type _ :=
  ∀ (I : Finset R.Component) (r : ℕ), PowerLogIndex → ∀ s : R.Stratum I, MomentTensor (D.N I s) r

/-- **The stratum coefficient** `(1/r!) ∫_{S_I} ⟨D^r_⊥(φ∘π)(s), B(s)⟩ dν_I(s)`. -/
noncomputable def stratumCoefficient (ν : ∀ I : Finset R.Component, Measure (R.Stratum I))
    (φ : (Fin d → ℝ) → ℝ) (I : Finset R.Component) (r : ℕ)
    (B : ∀ s : R.Stratum I, MomentTensor (D.N I s) r) : ℝ :=
  (r.factorial : ℝ)⁻¹ * ∫ s, (B s).pair (D.normalDifferential φ I s r) ∂ν I

/-- **The expansion coefficient of a power–log index**: the sum over the strata and over all normal
orders of the stratum coefficients. -/
noncomputable def expansionCoefficient (ν : ∀ I : Finset R.Component, Measure (R.Stratum I))
    (B : D.MomentCoefficientField) (φ : (Fin d → ℝ) → ℝ) (q : PowerLogIndex) : ℝ :=
  ∑ I : Finset R.Component, ∑' r : ℕ, D.stratumCoefficient ν φ I r (B I r q)

/-- ★ **The coordinate-free expansion** of the original integral `∫_W φ ϕ e^{−nK}`: for every cutoff
`A`, subtracting the terms `expansionCoefficient(q) · n^{−α}(log n)^j` over the finite spectrum
`spec A` (all indices with exponent `≤ A`) leaves `o(n^{−A})`. Only the strata, the normal
differentials, the moment-tensor coefficients, the stratum densities and `π` occur. -/
def HasCoordFreeExpansion (ν : ∀ I : Finset R.Component, Measure (R.Stratum I))
    (B : D.MomentCoefficientField) (spec : ℝ → Finset PowerLogIndex) (W : Set (Fin d → ℝ))
    (K ϕ φ : (Fin d → ℝ) → ℝ) : Prop :=
  ∀ A : ℝ, (fun n : ℝ => globalLaplace W K (fun w => φ w * ϕ w) n -
      ∑ q ∈ spec A, D.expansionCoefficient ν B φ q * q.scale n) =o[atTop]
    fun n : ℝ => n ^ (-A)

/-- The stratum coefficient at degree `0` is an ordinary stratum integral of the observable: the
leading-measure shape. -/
theorem stratumCoefficient_zero (ν : ∀ I : Finset R.Component, Measure (R.Stratum I))
    (φ : (Fin d → ℝ) → ℝ) (I : Finset R.Component)
    (B : ∀ s : R.Stratum I, MomentTensor (D.N I s) 0) :
    D.stratumCoefficient ν φ I 0 B = ∫ s, φ (R.π s) *
      (B s).pair (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => D.N I s) 1) ∂ν I := by
  unfold stratumCoefficient
  rw [Nat.factorial_zero, Nat.cast_one, inv_one, one_mul]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  beta_reduce
  have h : D.normalDifferential φ I s 0 =
      φ (R.π s) • ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => D.N I s) 1 := by
    ext m
    rw [D.normalDifferential_zero, smul_apply, ContinuousMultilinearMap.constOfIsEmpty_apply,
      smul_eq_mul, mul_one]
  rw [h, MomentTensor.pair_smul]

end ResolvedNormalData

end Grammar
