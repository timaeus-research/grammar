/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.BlowUpCubeLeadingCoefficient
import Grammar.ChartExpansion
import Grammar.CutoffExpansionUniqueness

/-!
# The exponent support of the cube expansion (CCCXLIX; phase E4F, unit F2 step 1, consult #103)

Consult #103 §2: "singleton support — for normal weight `h₀` the piece coefficient can occur only at
`α = (h₀ + 1 + ℓ)/2`". The assembled canonical coefficients of a certificate vanish off the
candidate exponents of every chart (`gCoeff_eq_zero_of_not_candidate`, from the kernel support
`dataBoxCoeff_eq_zero_of_not_candidate`); the piece certificates of the cube have one normal
coordinate with `k = 1`, `h = d − 1` (`pieceCert_cores_h`), so their candidate exponents are
`(d + ℓ)/2`, `ℓ ∈ ℕ` (`not_candidateExp_piece`). Hence ★★ `pieceCoefficient_eq_zero_of_not_support`,
★★ `cubeCoefficient_eq_zero_of_not_support` and, for EVERY `d ≥ 1` and without the leading-measure
theorem, ★★ `cubeCoefficient_eq_zero_of_lt'` (vanishing below `d/2`) with the paper-facing wrapper
★★ `cube_hasExpansion_support` (the sum runs over `α = (d+ℓ)/2 ≤ A` only). This closes the
one-dimensional gap of CCCXLVIII for the vanishing statements (the leading value `C(d/2)` still
uses `1 < d`).

Not included (F2 steps 2–3): the cancellation of odd total prior–observable Taylor orders between
paired normal-sign pieces (support `d/2 + ℕ`, i.e. `ℓ` even) — this needs the transformation of the
convolution of prior coefficients and observable jets under the normal-sign flip, a new bridge
(consult #103 §2), and is deferred.
-/

open MeasureTheory Set Filter Topology Asymptotics

namespace Grammar

/-! ### Assembled canonical coefficients vanish off the candidate exponents of every chart -/

section Assembled

variable {M : ℕ} {K : Fin M → Type*} [∀ I, TopologicalSpace (K I)] [∀ I, MeasurableSpace (K I)]
  {n : Fin M → ℕ} (ν : (I : Fin M) → Measure (K I))
  (h k : (I : Fin M) → Fin (n I + 1) → ℕ) (β : ℝ) (b : Fin M → ℝ) (x : JointData K n)

/-- ★ **Support of the assembled canonical coefficients**: `gCoeff μ j = 0` unless `μ` is a
candidate exponent `(h_i + r + 1)/(2k_i)` of some chart. -/
theorem gCoeff_eq_zero_of_not_candidate (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (hb : ∀ I, 0 < b I)
    {μ : ℝ} (hμ : ∀ I, ¬ candidateExp (h I) (k I) μ) (j : ℕ) : gCoeff ν h k β b x μ j = 0 := by
  unfold gCoeff
  refine Finset.sum_eq_zero fun I _ => ?_
  unfold tanCoeff
  simp [dataBoxCoeff_eq_zero_of_not_candidate (n I) (h I) (k I) (hk I) β hβ (hb I) _ (hμ I) j]

end Assembled

namespace BlowUpCube

open WaterFilling SingletonChart NormalisedBox

variable {d : ℕ} (β : Fin d) {p F : (Fin d → ℝ) → ℝ}

section Pieces

variable [NeZero d] (A : HolomorphicSignedBoxExtension 1 p F) (σ : CoordSign d)
  (hp0 : ∀ x ∈ piBox d (Icc (-1) 1), 0 ≤ p x)

omit [NeZero d] in
/-- The Jacobian order of the piece certificate's normal coordinate is `d − 1`. -/
theorem pieceCert_cores_h (J : Fin (pieceCert β A σ hp0).M)
    (i : Fin ((pieceCert β A σ hp0).n J + 1)) :
    (pieceCert β A σ hp0).cores.h J i = d - 1 := by
  change hS β (d - 1) (σI (Iβ β) i).1 = d - 1
  rw [Finset.mem_singleton.1 (σI (Iβ β) i).2]
  exact hS_self β (d - 1)

/-- The candidate exponents of a piece are `(d + ℓ)/2`. -/
theorem not_candidateExp_piece {μ : ℝ} (hμ : ∀ r : ℕ, μ ≠ ((d : ℝ) + r) / 2)
    (J : Fin (pieceCert β A σ hp0).M) :
    ¬ candidateExp ((pieceCert β A σ hp0).cores.h J) ((pieceCert β A σ hp0).cores.k J) μ := by
  rintro ⟨i, r, hi⟩
  rw [pieceCert_cores_h, pieceCert_cores_k] at hi
  refine hμ r ?_
  have h1 : 1 ≤ d := Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  rw [hi, Nat.cast_sub h1]
  push_cast
  ring

/-- ★★ **Support of a piece coefficient**: it vanishes unless the exponent is `(d + ℓ)/2`. -/
theorem pieceCoefficient_eq_zero_of_not_support {q : PowerLogIndex}
    (hμ : ∀ r : ℕ, q.exponent ≠ ((d : ℝ) + r) / 2) : pieceCoefficient β A σ hp0 q = 0 := by
  unfold pieceCoefficient
  rw [(pieceCoeff β A σ hp0).expansionCoefficient_eq_gCoeff]
  exact gCoeff_eq_zero_of_not_candidate _ _ _ _ _ _ (pieceCert β A σ hp0).cores.k_pos
    (pieceCert β A σ hp0).β_pos (pieceCert β A σ hp0).cores.b_pos
    (fun J => not_candidateExp_piece β A σ hp0 hμ J) _

end Pieces

section Cube

variable [NeZero d] (A : HolomorphicSignedBoxExtension 1 p F)
  (hp0 : ∀ x ∈ piBox d (Icc (-1) 1), 0 ≤ p x)

omit β in
/-- ★★ **Support of the cube expansion**: `C(q) = 0` unless `q.exponent = (d + ℓ)/2`. -/
theorem cubeCoefficient_eq_zero_of_not_support {q : PowerLogIndex}
    (hμ : ∀ r : ℕ, q.exponent ≠ ((d : ℝ) + r) / 2) : cubeCoefficient A hp0 q = 0 :=
  Finset.sum_eq_zero fun β _ => Finset.sum_eq_zero fun σ _ =>
    pieceCoefficient_eq_zero_of_not_support β A σ hp0 hμ

omit β in
/-- ★★ **Vanishing below `d/2` for every `d ≥ 1`** (structural: from the kernel support, with no
leading-measure input). -/
theorem cubeCoefficient_eq_zero_of_lt' {q : PowerLogIndex} (hlt : q.exponent < d / 2) :
    cubeCoefficient A hp0 q = 0 :=
  cubeCoefficient_eq_zero_of_not_support A hp0 fun r hr => by
    have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    linarith

omit β in
open Classical in
/-- ★★ **The paper-facing expansion on the support**: the sum runs over the exponents
`(d + ℓ)/2 ≤ A` only, for every `d ≥ 1`. -/
theorem cube_hasExpansion_support (A' : ℝ) :
    (fun n : ℝ => (∫ x in cube d, F x * p x * Real.exp (-n * K x)) -
      ∑ q ∈ (spectrumLe 2 0 A').filter (fun q => ∃ r : ℕ, q.exponent = ((d : ℝ) + r) / 2),
        cubeCoefficient A hp0 q * q.scale n) =o[atTop] fun n : ℝ => n ^ (-A') := by
  refine (cube_hasExpansion A hp0 A').congr_left fun n => ?_
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not (spectrumLe 2 0 A')
    (fun q => ∃ r : ℕ, q.exponent = ((d : ℝ) + r) / 2),
    Finset.sum_eq_zero (s := (spectrumLe 2 0 A').filter
      fun q => ¬ ∃ r : ℕ, q.exponent = ((d : ℝ) + r) / 2) fun q hq => ?_, add_zero]
  obtain ⟨-, hne⟩ := Finset.mem_filter.1 hq
  push Not at hne
  rw [cubeCoefficient_eq_zero_of_not_support A hp0 hne, zero_mul]

end Cube

end BlowUpCube

end Grammar
