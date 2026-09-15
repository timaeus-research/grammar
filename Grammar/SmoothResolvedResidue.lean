/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothResolvedStratumPositive
import Grammar.SmoothResolvedStratumEuclidean

/-!
# The graded stratum formula as a residue sum

The twisted prior density `(K∘π)^{−μ} μ_U` behaves along a wall `(k, h)` like `u^{h − 2kμ}`:
its POLE ORDER is `poleOrder k h μ = 2kμ − h`. A wall resonates with `μ` exactly when this pole
order is a positive integer (`resonates_iff_poleOrder`), the exact resonance count of CDXLIV counts
the SIMPLE poles (`exactCount_eq_card_simplePole`), and the resonant Taylor order is the pole order
minus one. On a face all of whose walls carry simple poles the face term of the stratum formula
(CDXLVI) is the residue term
`Γ(μ) β^{−μ}/(c−1)! · (∏_{j∈J} (2k_j)^{−1}) ∫_{face} A(0_J, w) · residueWeight(w) dw`
(★★ `faceTerm_eq_residue_of_simple`): the weight `∏_{i∉J} w_i^{h_i}(∏_{i∉J} w_i^{2k_i})^{−μ}` is the
coordinate expression of the iterated Poincaré residue of the twisted density along the face, and
the factors `(2k_j)^{−1}` normalise the residue against `d log(u_j^{2k_j})`, the logarithmic
differential of the local phase factor, so that the remaining constant is `Γ(μ)/(c−1)!`
(`residueConst`). On the resolved manifold, under the zero-order condition, the `(μ, c−1)`
coefficient of an observable vanishing near the deep zero fibre is the RESIDUE SUM
(★★★ `coeff_eq_residueSum`): faces with a non-simple pole contribute nothing (their amplitude jets
vanish, or their top face coefficient is zero). Euclidean form: `observableCoeff_eq_residueSum`.
This is the coordinate form of
`𝒯^U_{μ,c−1}[F] = Γ(μ)/(c−1)! ∫_{S^μ_c} F · Res_{S^μ_c}[(K∘π)^{−μ} μ_U]`.
Non-claims: the residue is not constructed as an intrinsic object here (that is the residue
programme); the identification is the chart identity above. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology Finset
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing Grammar.NormalCrossing.EvenChartBoxDepth

namespace Grammar

namespace SmoothEngine

variable {d : ℕ}

/-! ### Pole orders -/

/-- The pole order of the twisted density `(K∘π)^{−μ} μ_U` along a wall `(k, h)`:
`u^{h − 2kμ} = u^{−poleOrder}`. -/
noncomputable def poleOrder (k h : ℕ) (μ : ℝ) : ℝ := 2 * k * μ - h

/-- A wall resonates with `μ` exactly when the twisted density has a pole of positive integer order
along it. -/
theorem resonates_iff_poleOrder (μ : ℝ) (p : ℕ × ℕ) :
    Resonates μ p ↔ ∃ n : ℕ, poleOrder p.1 p.2 μ = n + 1 := by
  unfold Resonates poleOrder
  constructor <;> rintro ⟨n, hn⟩ <;> exact ⟨n, by linarith⟩

/-- The exact resonance count is the number of SIMPLE poles of the twisted density. -/
theorem exactCount_eq_card_simplePole {ι : Type*} [Fintype ι] (k e : ι → ℕ) (μ : ℝ) :
    exactCount k e μ = (univ.filter fun i => poleOrder (k i) (e i) μ = 1).card := by
  unfold exactCount poleOrder
  congr 1
  exact Finset.filter_congr fun i _ => by constructor <;> intro h <;> linarith

/-- On an exactly resonant wall the resonant Taylor order is the pole order minus one. -/
theorem poleOrder_eq_of_exact {k h m : ℕ} {μ : ℝ} (hres : 2 * (k : ℝ) * μ = m + h + 1) :
    poleOrder k h μ = m + 1 := by
  unfold poleOrder
  linarith

/-! ### The residue weight and the `d log`-normalised residue integral -/

/-- The residue weight on a face: `∏_{i∉J} w_i^{h_i} (∏_{i∉J} w_i^{2k_i})^{−μ}`, the coordinate
expression of the iterated Poincaré residue of the twisted density along the face. -/
noncomputable def residueWeight {ι : Type*} [Fintype ι] (h k : ι → ℕ) (μ : ℝ) (w : ι → ℝ) : ℝ :=
  mono h w * mono (fun i => 2 * k i) w ^ (-μ)

theorem residueWeight_nonneg {ι : Type*} [Fintype ι] (h k : ι → ℕ) (μ : ℝ) {b : ℝ}
    {w : ι → ℝ} (hw : w ∈ box ι b) : 0 ≤ residueWeight h k μ w :=
  mul_nonneg (mono_nonneg_of_mem_box hw h) (Real.rpow_nonneg (mono_nonneg_of_mem_box hw _) _)

/-- The residue integral of an amplitude on the face `{u_J = 0}`, normalised against
`d log(u_j^{2k_j})` on each wall of the face. -/
noncomputable def dlogResidueInt (k h : Fin d → ℕ) (μ b : ℝ) (J : Finset (Fin d))
    (A : (Fin d → ℝ) → ℝ) : ℝ :=
  (∏ j : {i // inJ J i}, (2 * (k j : ℝ))⁻¹) *
    ∫ w in box {i // ¬ inJ J i} b,
      A (glue J 0 w) * residueWeight (fun i : {i // ¬ inJ J i} => h i) (fun i => k i) μ w

/-- The residue constant `Γ(μ)/(c−1)!`. -/
noncomputable def residueConst (μ : ℝ) (c : ℕ) : ℝ := Real.Gamma μ / ((c - 1).factorial : ℝ)

theorem residueConst_pos {μ : ℝ} (hμ : 0 < μ) (c : ℕ) : 0 < residueConst μ c :=
  div_pos (Real.Gamma_pos_of_pos hμ) (Nat.cast_pos.2 (Nat.factorial_pos _))

/-- A face all of whose walls carry simple poles has resonant Taylor order zero. -/
theorem resOrder_eq_zero_of_simple {h k : Fin d → ℕ} {μ : ℝ} {J : Finset (Fin d)}
    (hsimple : ∀ j ∈ J, 2 * (k j : ℝ) * μ = h j + 1) : resOrder h k μ J = 0 := by
  funext j
  rw [Pi.zero_apply]
  by_cases hj : j ∈ J
  · exact resOrder_eq_of_exact (m := fun _ => 0) hj
      (by rw [Nat.cast_zero, zero_add]; exact hsimple j hj)
  · exact resOrder_of_not_mem hj

/-- ★★ **The face term of the stratum formula is a residue term on a simple-pole face**:
`faceW · faceCoef · faceCoeffInt = Γ(μ) β^{−μ}/(c−1)! · dlogResidueInt`. -/
theorem faceTerm_eq_residue_of_simple {A : (Fin d → ℝ) → ℝ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i)
    {β b : ℝ} (hβ : 0 < β) (hb : 0 < b) {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (J : Finset (Fin d))
    (hJc : J.card = c) (hsimple : ∀ j ∈ J, 2 * (k j : ℝ) * μ = h j + 1) :
    faceW J (resOrder h k μ J) *
      (faceCoef k β b J (fun i => resOrder h k μ J i + h i) μ (c - 1) *
        faceCoeffInt (fun w => pdMulti (resOrder h k μ J) (lJ J) A (glue J 0 w))
          (fun i : {i // ¬ inJ J i} => h i) (fun i => 2 * k i) b μ 0) =
      residueConst μ c * β ^ (-μ) * dlogResidueInt k h μ b J A := by
  have hJne : J.Nonempty := Finset.card_pos.1 (by omega)
  have h0 := resOrder_eq_zero_of_simple hsimple
  have hDJ : DJ J = c - 1 := by rw [DJ_eq, hJc]
  rw [h0]
  have hW : faceW J 0 = 1 := by
    unfold faceW
    simp
  have hres : ∀ j ∈ J, 2 * (k j : ℝ) * μ = ((fun i => (0 : Fin d → ℕ) i + h i) j : ℕ) + 1 := by
    intro j hj
    simp only [Pi.zero_apply, zero_add]
    exact hsimple j hj
  rw [hW, one_mul, ← hDJ, faceCoef_top_eq k hk hβ hb J hJne _ hres, hDJ]
  unfold faceCoeffInt dlogResidueInt residueConst residueWeight
  simp only [pdMulti_zero, pow_zero, mul_one]
  rw [Finset.prod_inv_distrib]
  have hint : ∫ w in box {i // ¬ inJ J i} b, A (glue J 0 w) *
        mono (fun i : {i // ¬ inJ J i} => h i) w *
        mono (fun i : {i // ¬ inJ J i} => 2 * k i) w ^ (-μ) =
      ∫ w in box {i // ¬ inJ J i} b, A (glue J 0 w) *
        (mono (fun i : {i // ¬ inJ J i} => h i) w *
          mono (fun i : {i // ¬ inJ J i} => 2 * k i) w ^ (-μ)) :=
    setIntegral_congr_fun (measurableSet_box _) fun w _ => by ring
  rw [hint]
  have hprod : (∏ i : {i // inJ J i}, 2 * (k i : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => by
      have := Nat.cast_pos (α := ℝ) |>.2 (hk i.1)
      positivity
  have hfac : ((c - 1).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_pos _).ne'
  field_simp

namespace ResolvedData

variable (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-- The simple-pole faces of size `c` of a piece box. -/
noncomputable def simpleFaces (p : (Ξ.X Y).PIdx) (μ : ℝ) (c : ℕ) :
    Finset (Finset (Fin ((Ξ.X Y).da p))) :=
  (univ : Finset (Finset (Fin ((Ξ.X Y).da p)))).filter fun J =>
    J.card = c ∧ ∀ j ∈ J, 2 * ((Ξ.X Y).kA p j : ℝ) * μ = (Ξ.X Y).hA p j + 1

/-- The residue term of a piece at a base point: the sum over its simple-pole faces of the
`d log`-normalised residue integrals of the amplitude. -/
noncomputable def pieceResidueSum (I : Fin (Fintype.card (Ξ.X Y).PIdx))
    (s : Base ((Ξ.X Y).act ((Ξ.X Y).en I).1) (Y.T.a ((Ξ.X Y).en I).1)) (μ : ℝ) (c : ℕ) : ℝ :=
  ∑ J ∈ Ξ.simpleFaces Y ((Ξ.X Y).en I) μ c,
    dlogResidueInt ((Ξ.X Y).kA ((Ξ.X Y).en I)) ((Ξ.X Y).hA ((Ξ.X Y).en I)) μ
      (Y.T.a ((Ξ.X Y).en I).1) J ((Ξ.amp Y ((Ξ.X Y).en I)).amp s)

/-- ★★ **The residue sum** `Γ(μ)/(c−1)! · ∑_{pieces} ∫_{base} ∑_{simple faces} dlogResidueInt`. -/
noncomputable def residueSum (μ : ℝ) (c : ℕ) : ℝ :=
  residueConst μ c * ∑ I, ∫ s, Ξ.pieceResidueSum Y I s μ c ∂((Ξ.decomp Y).chart I).ν

theorem pieceStratumSum_eq_residue {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c)
    (I : Fin (Fintype.card (Ξ.X Y).PIdx))
    (s : Base ((Ξ.X Y).act ((Ξ.X Y).en I).1) (Y.T.a ((Ξ.X Y).en I).1)) :
    Ξ.pieceStratumSum Y I s μ c = residueConst μ c * Ξ.pieceResidueSum Y I s μ c := by
  unfold pieceStratumSum pieceResidueSum simpleFaces
  simp only [Ξ.chart_k Y, Ξ.chart_h Y, Ξ.chart_b Y, Ξ.chart_βf Y, Ξ.chart_amp Y]
  rw [Finset.mul_sum, Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun J _ => ?_
  by_cases hJc : J.card = c
  · rw [if_pos hJc]
    by_cases hsimple : ∀ j ∈ J, 2 * ((Ξ.X Y).kA ((Ξ.X Y).en I) j : ℝ) * μ =
        (Ξ.X Y).hA ((Ξ.X Y).en I) j + 1
    · rw [if_pos ⟨hJc, hsimple⟩, faceTerm_eq_residue_of_simple _ _ ((Ξ.X Y).kA_pos _)
        (Y.T.phaseConst_pos _) (Y.T.a_pos _) hc J hJc hsimple, Y.phaseConst_eq_one,
        Real.one_rpow, mul_one]
    · rw [if_neg fun h => hsimple h.2]
      -- either the face is not exactly resonant (top coefficient zero) or its Taylor order is
      -- nonzero, in which case all amplitude jets vanish on the face (zero-order condition)
      have hDJ : DJ J = c - 1 := by rw [DJ_eq, hJc]
      by_cases hex : ∀ i ∈ J, 2 * ((Ξ.X Y).kA ((Ξ.X Y).en I) i : ℝ) * μ =
          resOrder ((Ξ.X Y).hA ((Ξ.X Y).en I)) ((Ξ.X Y).kA ((Ξ.X Y).en I)) μ J i +
            (Ξ.X Y).hA ((Ξ.X Y).en I) i + 1
      · rw [faceCoeffInt_eq_zero_of_forall _ _ _ _ _ fun w hw => ?_, mul_zero, mul_zero]
        rcases Ξ.stratum_or_jets_zero Y hc hzero ((Ξ.X Y).en I) s hJc hex hw with ⟨-, h0⟩ | hjets
        · exfalso
          refine hsimple fun j hj => ?_
          have := hex j hj
          rw [h0, Pi.zero_apply, Nat.cast_zero, zero_add] at this
          exact this
        · rw [pdMulti_lJ_eq_finRange_of_zero_off ((Ξ.amp Y _).smooth s) J _
            fun i hi => resOrder_of_not_mem hi]
          exact hjets _
      · obtain ⟨i, hi, hne⟩ : ∃ i ∈ J, 2 * ((Ξ.X Y).kA ((Ξ.X Y).en I) i : ℝ) * μ ≠
            resOrder ((Ξ.X Y).hA ((Ξ.X Y).en I)) ((Ξ.X Y).kA ((Ξ.X Y).en I)) μ J i +
              (Ξ.X Y).hA ((Ξ.X Y).en I) i + 1 := by
          by_contra h
          exact hex fun i hi => by_contra fun hne => h ⟨i, hi, hne⟩
        rw [← hDJ, faceCoef_top_eq_zero_of_not_exact _ ((Ξ.X Y).kA_pos _) (Y.T.phaseConst_pos _)
          (Y.T.a_pos _) J _ hi (by push_cast; exact hne), zero_mul, mul_zero]
  · rw [if_neg hJc, if_neg fun h => hJc h.1]

/-- ★★★ **The graded stratum formula as a residue sum**: under the zero-order condition, the
`(μ, c−1)` coefficient of an observable vanishing near the deep zero fibre is
`Γ(μ)/(c−1)! · ∑_{simple-pole faces} (∏_{j∈J}(2k_j)^{−1}) ∫_{face} amplitude · residue weight`. -/
theorem coeff_eq_residueSum {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c)
    (hF : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0) :
    Ξ.coeff Y μ (c - 1) = Ξ.residueSum Y μ c := by
  rw [Ξ.coeff_eq_stratumSum Y hc hF μ]
  unfold stratumSum residueSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [← integral_const_mul]
  exact integral_congr_ae
    (Eventually.of_forall fun s => Ξ.pieceStratumSum_eq_residue Y hc hzero I s)

/-- The Euclidean form of the residue sum. -/
theorem observableCoeff_eq_residueSum {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) {μ : ℝ} {c : ℕ}
    (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c)
    (h0 : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), f (Ξ.R.gv P) = 0) :
    (Ξ.X Y).observableCoeff μ (c - 1) f hf =
      (Ξ.withF (fun P => f (Ξ.R.gv P)) (Ξ.contMDiff_comp_gv hf)).residueSum Y μ c := by
  rw [← Ξ.coeff_comp_gv Y hf μ (c - 1)]
  exact (Ξ.withF (fun P => f (Ξ.R.gv P)) (Ξ.contMDiff_comp_gv hf)).coeff_eq_residueSum Y hc hzero h0

end ResolvedData

end SmoothEngine

end Grammar
