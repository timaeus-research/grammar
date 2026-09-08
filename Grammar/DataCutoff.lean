/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.DataCoeffContinuity

/-!
# The canonical cutoff theorem on the data space, uniform on balls (Stage S4)

Unit 273 (Astra #33 / review v27 should-fix 1 and 5a). The Taylor-tree cutoff theorem is restated
with the canonical coefficient map: for a data-space element `x` with `‖x‖ ≤ R`, every cutoff
`L > 0`, and `N > 0` with `N b^{2|k|} ≥ 1`,

`|Z(N; x) − ∑_{μ ∈ Λ_L} N^{-μ} ∑_{j ≤ n} C_{μ,j}(x) (log N)^j|`
`  ≤ b^{|h|+d} · dataCutoffConst n k β L R · (N b^{2|k|})^{-L} (1 + log(N b^{2|k|}))^n`

(`dataTaylorTree_cutoff_bound`), where `Λ_L = latticeBelow (2∏kᵢ) L` is the finite candidate
lattice below `L`, `C_{μ,j} = dataBoxCoeff`, `Z = dataBoxIntegral`, and the constant
`dataCutoffConst n k β L R = cutoffBound n k β L R R R` depends on the data only through the ball
radius `R` (`cutoffBound_mono`: the uniform cutoff constant is monotone in `|ξ(0)|` and the two
masses). This is the deterministic input for the ordered normalised remainders of A2: on a data
ball the cutoff error is `O((N b^{2|k|})^{-L} (log N)^n)` uniformly.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open CoeffFamily

/-- The uniform cutoff constant is monotone in `|ξ(0)|` and the two masses. -/
theorem cutoffBound_mono (n : ℕ) (k : Fin (n + 1) → ℕ) (β : ℝ) (hβ : 0 < β) {L : ℝ} (hL : 0 < L)
    {a E B a' E' B' : ℝ} (ha : |a| ≤ |a'|) (hE0 : 0 ≤ E) (hE : E ≤ E') (hB0 : 0 ≤ B)
    (hB : B ≤ B') :
    cutoffBound n k β L a E B ≤ cutoffBound n k β L a' E' B' := by
  unfold cutoffBound
  have hK : 0 ≤ ∏ i, 1 / (2 * (k i : ℝ)) := Finset.prod_nonneg fun i _ => by positivity
  have hD : (0 : ℝ) ≤ ((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n := by positivity
  have hab : |a| + B ≤ |a'| + B' := add_le_add ha hB
  have habs : |(|a| + B)| ≤ |(|a'| + B')| := by
    rw [abs_of_nonneg (add_nonneg (abs_nonneg _) hB0),
      abs_of_nonneg (add_nonneg (abs_nonneg _) (hB0.trans hB))]
    exact hab
  have hM := phaseLogMoment_mono β hβ hab hL n 0
  have hT := tailConst_mono β hβ habs 0 L n
  have h4 : (0 : ℝ) ≤ 4 / β := by positivity
  have h5 : (0 : ℝ) ≤ (⌈L⌉₊.factorial : ℝ) * (4 / β) ^ ⌈L⌉₊ := by positivity
  have hM0 := phaseLogMoment_nonneg β (|a'| + B') L n 0
  have hT0 := tailConst_nonneg β (|a'| + B') hβ 0 L n
  refine mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE hK) hD) ?_
    (add_nonneg (phaseLogMoment_nonneg _ _ _ _ _)
      (mul_nonneg (mul_nonneg (tailConst_nonneg β _ hβ 0 L n) h4) h5))
    (mul_nonneg (mul_nonneg hK (hE0.trans hE)) hD)
  exact add_le_add hM (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hT h4) h5)

/-- The cutoff constant on the data ball of radius `R`. -/
noncomputable def dataCutoffConst (n : ℕ) (k : Fin (n + 1) → ℕ) (β L R : ℝ) : ℝ :=
  cutoffBound n k β L R R R

theorem dataCutoffConst_nonneg (n : ℕ) (k : Fin (n + 1) → ℕ) (β : ℝ) (hβ : 0 < β) (L : ℝ)
    {R : ℝ} (hR : 0 ≤ R) : 0 ≤ dataCutoffConst n k β L R :=
  cutoffBound_nonneg n k β hβ L R hR R

/-- The cutoff constant of a data-space element is at most the ball constant. -/
theorem cutoffBound_data_le (n : ℕ) (k : Fin (n + 1) → ℕ) (β : ℝ) (hβ : 0 < β) {L : ℝ}
    (hL : 0 < L) {R : ℝ} {x : DataSpace (n + 1)} (hx : ‖x‖ ≤ R) :
    cutoffBound n k β L (constPhase x) (mass (etaCoord x)) (mass (xiCoord x)) ≤
      dataCutoffConst n k β L R := by
  have hR0 : 0 ≤ R := (norm_nonneg x).trans hx
  unfold dataCutoffConst
  refine cutoffBound_mono n k β hβ hL ?_ (mass_nonneg _) ((mass_etaCoord_le x).trans hx)
    (mass_nonneg _) ((mass_xiCoord_le x).trans hx)
  rw [abs_of_nonneg hR0]
  exact (abs_coord_sub_le x 0 (Sum.inl 0)).trans_eq' (by simp [constPhase]) |>.trans
    (by simpa using hx)

/-- **The canonical cutoff theorem on the data space, uniform on balls.** -/
theorem dataTaylorTree_cutoff_bound (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {L b : ℝ} (hL : 0 < L) (hb : 0 < b) {N : ℝ} (hN : 0 < N)
    (hN' : 1 ≤ boxScale k b N) {R : ℝ} {x : DataSpace (n + 1)} (hx : ‖x‖ ≤ R) :
    |dataBoxIntegral n h k β N b x - ∑ μ ∈ latticeBelow (latticeQ k) L, N ^ (-μ) *
        ∑ j ∈ Finset.range (n + 1), dataBoxCoeff n h k β b x μ j * (Real.log N) ^ j| ≤
      b ^ (∑ i, h i + (n + 1)) * dataCutoffConst n k β L R *
        (boxScale k b N ^ (-L) * (1 + Real.log (boxScale k b N)) ^ n) := by
  have hbox := boxTaylorTree_cutoff_bound n h k hk β hβ hL hb hN.le hN' (absSummableAt_toXi hb x)
    (absSummableAt_toEta hb x)
  rw [boxSpectralSum_eq n h k β L hb _ _ hN, scale_toXi hb.ne', scale_toEta hb.ne'] at hbox
  have hc : (xiCoord x) 0 = constPhase x := rfl
  rw [hc] at hbox
  refine hbox.trans ?_
  have hpos : 0 ≤ boxScale k b N ^ (-L) * (1 + Real.log (boxScale k b N)) ^ n := by
    have h1 : 0 ≤ Real.log (boxScale k b N) := Real.log_nonneg hN'
    have h2 : 0 ≤ boxScale k b N ^ (-L) := Real.rpow_nonneg (by linarith) _
    positivity
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (pow_nonneg hb.le _)) hpos
  exact cutoffBound_data_le n k β hβ hL hx

end Grammar
