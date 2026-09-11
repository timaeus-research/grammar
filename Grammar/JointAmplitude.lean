/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.MonomialCoefficients
import Grammar.TangentialData
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# The tangential datum of a jointly analytic amplitude (Astra #68 unit 6c)

A jointly real-analytic amplitude `G(v, u)` of tangential variables `v : Fin t → ℝ` and normal
variables `u : Fin m → ℝ`, represented by one power series `P` on `Fin t ⊕ Fin m → ℝ` around
`(0, 0)` with `(t + m) · B < ρ < radius`, has joint monomial coefficients `C_{α,γ'}` with
`∑ |C_{α,γ'}| B^{|α|+|γ'|} < ∞` (unit 6a). For each `v` in the cube `|v_i| ≤ B` the **fibre family**
`jointFibre P v γ' = ∑_α C_{α,γ'} v^α` is the amplitude family of the normal fibre at `v`:

* it is weighted-ℓ¹ summable at every box side `b ≤ B`, uniformly in `v` through the majorant
  `fibreMajorant P B γ' = ∑_α |C_{α,γ'}| B^{|α|}` (`abs_jointFibre_le`,
  `summable_fibreMajorant_mul_pow`);
* on the normal box `|u_j| ≤ b` its monomial series converges to `G(v, u)`
  (`hasSum_jointFibre_mul_mono`, by `HasSum.prod_fiberwise` on the joint series);
* the data-space element `jointDatum v` (zero phase family, amplitude `jointFibre P v`) depends
  **continuously** on `v` in the ℓ¹ norm (`continuous_jointDatum`): the ℓ¹ distance is dominated by
  the continuous majorant `∑_{α,γ'} |C_{α,γ'}| |v'^α − v^α| b^{|γ'|}` which vanishes at `v' = v` —
  the uniform tail control comes from the joint ℓ¹ bound, no Cauchy estimate is needed.

The result is the tangential datum `jointTangentialData : C(K, DataSpace m)` over any compact
`K` inside the tangential cube, with `xiCoord = 0` and `evalF (toEta b (x v)) u = G(v, u)`
(`evalF_toEta_jointTangentialData`) — the amplitude clause of a core presentation.

Non-claims: the joint series is a hypothesis (one centre); covering a compact base by finitely
many such centres is the assembly unit's task.
-/

open Set Filter Topology
open scoped NNReal ENNReal

namespace Grammar

open CoeffFamily

variable {t m : ℕ}

/-! ### Splitting joint multi-indices -/

/-- Joint multi-indices on `Fin t ⊕ Fin m` as pairs (normal part, tangential part). -/
def splitIdx (t m : ℕ) : (Fin t ⊕ Fin m → ℕ) ≃ (Fin m → ℕ) × (Fin t → ℕ) :=
  (Equiv.sumArrowEquivProdArrow (Fin t) (Fin m) ℕ).trans (Equiv.prodComm _ _)

theorem splitIdx_symm_apply (γ' : Fin m → ℕ) (α : Fin t → ℕ) :
    (splitIdx t m).symm (γ', α) = Sum.elim α γ' := rfl

theorem sum_sum_elim (α : Fin t → ℕ) (γ' : Fin m → ℕ) :
    ∑ x, Sum.elim α γ' x = ∑ i, α i + ∑ j, γ' j := by
  rw [Fintype.sum_sum_type]
  simp

theorem prod_pow_sum_elim (v : Fin t → ℝ) (u : Fin m → ℝ) (α : Fin t → ℕ) (γ' : Fin m → ℕ) :
    ∏ x, Sum.elim v u x ^ Sum.elim α γ' x = (∏ i, v i ^ α i) * ∏ j, u j ^ γ' j := by
  rw [Fintype.prod_sum_type]
  simp

theorem abs_sum_elim_le {v : Fin t → ℝ} {u : Fin m → ℝ} {B b : ℝ} (hv : ∀ i, |v i| ≤ B)
    (hu : ∀ j, |u j| ≤ b) (hbB : b ≤ B) : ∀ x, |Sum.elim v u x| ≤ B := by
  rintro (i | j)
  · simpa using hv i
  · exact (hu j).trans hbB

/-! ### The joint weight and the fibre family -/

variable (P : FormalMultilinearSeries ℝ (Fin t ⊕ Fin m → ℝ) ℝ) (B : ℝ)

/-- The joint ℓ¹ weight `|C_{α,γ'}| B^{|α|} B^{|γ'|}` on the product index. -/
noncomputable def jointWeight (p : (Fin m → ℕ) × (Fin t → ℕ)) : ℝ :=
  |monoFamily P (Sum.elim p.2 p.1)| * B ^ (∑ i, p.2 i) * B ^ (∑ j, p.1 j)

theorem jointWeight_nonneg (hB : 0 ≤ B) (p : (Fin m → ℕ) × (Fin t → ℕ)) :
    0 ≤ jointWeight P B p := by
  unfold jointWeight
  positivity

theorem summable_jointWeight
    (hsum : Summable fun γ : Fin t ⊕ Fin m → ℕ => |monoFamily P γ| * B ^ (∑ x, γ x)) :
    Summable (jointWeight P B) := by
  have := ((splitIdx t m).symm.summable_iff
    (f := fun γ : Fin t ⊕ Fin m → ℕ => |monoFamily P γ| * B ^ (∑ x, γ x))).2 hsum
  refine this.congr fun p => ?_
  obtain ⟨γ', α⟩ := p
  simp only [Function.comp, splitIdx_symm_apply, jointWeight, sum_sum_elim, pow_add, mul_assoc]

/-- The fibre family at the tangential point `v`: `γ' ↦ ∑_α C_{α,γ'} v^α`. -/
noncomputable def jointFibre (v : Fin t → ℝ) (γ' : Fin m → ℕ) : ℝ :=
  ∑' α : Fin t → ℕ, monoFamily P (Sum.elim α γ') * ∏ i, v i ^ α i

/-- The fibre majorant `∑_α |C_{α,γ'}| B^{|α|}`. -/
noncomputable def fibreMajorant (γ' : Fin m → ℕ) : ℝ :=
  ∑' α : Fin t → ℕ, |monoFamily P (Sum.elim α γ')| * B ^ (∑ i, α i)

variable {P B}

theorem summable_jointWeight_fibre (hB : 0 < B) (hW : Summable (jointWeight P B))
    (γ' : Fin m → ℕ) :
    Summable fun α : Fin t → ℕ => |monoFamily P (Sum.elim α γ')| * B ^ (∑ i, α i) :=
  (summable_mul_right_iff (pow_pos hB (∑ j, γ' j)).ne').1 (hW.prod_factor γ')

theorem abs_prod_pow_le {v : Fin t → ℝ} (hv : ∀ i, |v i| ≤ B) (α : Fin t → ℕ) :
    |∏ i, v i ^ α i| ≤ B ^ (∑ i, α i) := by
  rw [Finset.abs_prod, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod (fun i _ => by positivity)
    fun i _ => by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hv i) _

theorem summable_fibre_term (hB : 0 < B) (hW : Summable (jointWeight P B)) {v : Fin t → ℝ}
    (hv : ∀ i, |v i| ≤ B) (γ' : Fin m → ℕ) :
    Summable fun α : Fin t → ℕ => monoFamily P (Sum.elim α γ') * ∏ i, v i ^ α i :=
  Summable.of_norm_bounded (summable_jointWeight_fibre hB hW γ') fun α => by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_prod_pow_le hv α) (abs_nonneg _)

theorem abs_jointFibre_le (hB : 0 < B) (hW : Summable (jointWeight P B)) {v : Fin t → ℝ}
    (hv : ∀ i, |v i| ≤ B) (γ' : Fin m → ℕ) : |jointFibre P v γ'| ≤ fibreMajorant P B γ' := by
  unfold jointFibre fibreMajorant
  have hs := summable_fibre_term hB hW hv γ'
  calc |∑' α : Fin t → ℕ, monoFamily P (Sum.elim α γ') * ∏ i, v i ^ α i|
      = ‖∑' α : Fin t → ℕ, monoFamily P (Sum.elim α γ') * ∏ i, v i ^ α i‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∑' α : Fin t → ℕ, ‖monoFamily P (Sum.elim α γ') * ∏ i, v i ^ α i‖ :=
        norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' α : Fin t → ℕ, |monoFamily P (Sum.elim α γ')| * B ^ (∑ i, α i) := by
        refine Summable.tsum_le_tsum (fun α => ?_) hs.norm (summable_jointWeight_fibre hB hW γ')
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left (abs_prod_pow_le hv α) (abs_nonneg _)

theorem summable_fibreMajorant_mul_pow (hB : 0 < B) (hW : Summable (jointWeight P B)) {b : ℝ}
    (hb : 0 ≤ b) (hbB : b ≤ B) :
    Summable fun γ' : Fin m → ℕ => fibreMajorant P B γ' * b ^ (∑ j, γ' j) := by
  have h1 : Summable fun γ' : Fin m → ℕ => ∑' α : Fin t → ℕ, jointWeight P B (γ', α) :=
    ((summable_prod_of_nonneg fun p => jointWeight_nonneg P B hB.le p).1 hW).2
  refine Summable.of_nonneg_of_le (fun γ' => by
    unfold fibreMajorant
    exact mul_nonneg (tsum_nonneg fun α => by positivity) (by positivity)) (fun γ' => ?_) h1
  calc fibreMajorant P B γ' * b ^ (∑ j, γ' j)
      ≤ fibreMajorant P B γ' * B ^ (∑ j, γ' j) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb hbB _)
          (tsum_nonneg fun α => by positivity)
    _ = ∑' α : Fin t → ℕ, jointWeight P B (γ', α) := by
        unfold fibreMajorant
        rw [← (summable_jointWeight_fibre hB hW γ').tsum_mul_right (B ^ (∑ j, γ' j))]
        rfl

/-- **Uniform weighted ℓ¹ summability of the fibre family** on the tangential cube. -/
theorem absSummableAt_jointFibre (hB : 0 < B) (hW : Summable (jointWeight P B)) {v : Fin t → ℝ}
    (hv : ∀ i, |v i| ≤ B) {b : ℝ} (hb : 0 ≤ b) (hbB : b ≤ B) :
    AbsSummableAt (jointFibre P v) b := by
  unfold AbsSummableAt
  refine Summable.of_nonneg_of_le (fun γ' => by positivity) (fun γ' => ?_)
    (summable_fibreMajorant_mul_pow hB hW hb hbB)
  exact mul_le_mul_of_nonneg_right (abs_jointFibre_le hB hW hv γ') (by positivity)

/-- **The fibre series converges to the joint amplitude**: for `|v_i| ≤ B`, `|u_j| ≤ b ≤ B`,
`∑_{γ'} jointFibre P v γ' · u^{γ'} = G(v, u)`. -/
theorem hasSum_jointFibre_mul_mono {G : (Fin t ⊕ Fin m → ℝ) → ℝ} {R : ℝ≥0∞}
    (hG : HasFPowerSeriesOnBall G P 0 R) {ρ : ℝ≥0} (hρ : (ρ : ℝ≥0∞) < R) (hB : 0 < B)
    (hBρ : ((t + m : ℕ) : ℝ) * B < ρ) (hB1 : B < ρ) {v : Fin t → ℝ} (hv : ∀ i, |v i| ≤ B) {b : ℝ}
    (hbB : b ≤ B) {u : Fin m → ℝ} (hu : ∀ j, |u j| ≤ b) :
    HasSum (fun γ' : Fin m → ℕ => jointFibre P v γ' * ∏ j, u j ^ γ' j) (G (Sum.elim v u)) := by
  have hcard : (Fintype.card (Fin t ⊕ Fin m) : ℝ) * B < ρ := by
    simpa [Fintype.card_sum] using hBρ
  have hW : Summable (jointWeight P B) :=
    summable_jointWeight P B (summable_monoFamily_mul_pow P (hρ.trans_le hG.r_le) hB.le hcard)
  have h := hasSum_monoFamily_mul_mono hG hρ hB.le hcard hB1 (abs_sum_elim_le hv hu hbB)
  have h2 := ((splitIdx t m).symm.hasSum_iff
    (f := fun γ : Fin t ⊕ Fin m → ℕ => monoFamily P γ * ∏ x, Sum.elim v u x ^ γ x)).2 h
  refine HasSum.prod_fiberwise h2 fun γ' => ?_
  have h3 := ((summable_fibre_term hB hW hv γ').hasSum).mul_right (∏ j, u j ^ γ' j)
  have hfun : (fun α : Fin t → ℕ => ((fun γ : Fin t ⊕ Fin m → ℕ =>
      monoFamily P γ * ∏ x, Sum.elim v u x ^ γ x) ∘ (splitIdx t m).symm) (γ', α)) =
      fun α : Fin t → ℕ => (monoFamily P (Sum.elim α γ') * ∏ i, v i ^ α i) * ∏ j, u j ^ γ' j := by
    funext α
    simp only [Function.comp, splitIdx_symm_apply, prod_pow_sum_elim]
    ring
  rw [hfun]
  exact h3

/-! ### The tangential datum -/

variable (P B) {b : ℝ} (hb : 0 < b) (hbB : b ≤ B) (hB : 0 < B) (hW : Summable (jointWeight P B))
  (K : Set (Fin t → ℝ)) (hK : ∀ v ∈ K, ∀ i, |v i| ≤ B)

/-- The data-space element of the normal fibre at `v ∈ K`: zero phase family, amplitude family
`jointFibre P v`. -/
noncomputable def jointDatum (v : K) : DataSpace m :=
  ofFamilies b hb 0 (jointFibre P v.1) (by simp [AbsSummableAt])
    (absSummableAt_jointFibre hB hW (hK v.1 v.2) hb.le hbB)

theorem jointDatum_apply_inr (v : K) (γ' : Fin m → ℕ) :
    jointDatum P B hb hbB hB hW K hK v (Sum.inr γ') = jointFibre P v.1 γ' * b ^ (∑ j, γ' j) := rfl

theorem jointDatum_apply_inl (v : K) (γ : Fin m → ℕ) :
    jointDatum P B hb hbB hB hW K hK v (Sum.inl γ) = 0 := by
  change (0 : CoeffFamily m) γ * b ^ (∑ i, γ i) = 0
  simp

theorem xiCoord_jointDatum (v : K) : xiCoord (jointDatum P B hb hbB hB hW K hK v) = 0 := by
  funext γ
  exact jointDatum_apply_inl P B hb hbB hB hW K hK v γ

theorem toEta_jointDatum (v : K) :
    toEta b (jointDatum P B hb hbB hB hW K hK v) = jointFibre P v.1 :=
  toEta_ofFamilies b hb 0 (jointFibre P v.1) _ _

/-- **Continuity of the tangential datum** in the ℓ¹ norm. -/
theorem continuous_jointDatum : Continuous (jointDatum P B hb hbB hB hW K hK) := by
  rw [continuous_iff_continuousAt]
  intro v
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  -- the continuous majorant of the ℓ¹ distance
  set T : (Fin m → ℕ) × (Fin t → ℕ) → K → ℝ := fun p v' =>
    |monoFamily P (Sum.elim p.2 p.1)| * |∏ i, v'.1 i ^ p.2 i - ∏ i, v.1 i ^ p.2 i| *
      b ^ (∑ j, p.1 j) with hT
  have hTnn : ∀ p v', 0 ≤ T p v' := fun p v' => by simp only [hT]; positivity
  have hTle : ∀ p v', T p v' ≤ 2 * jointWeight P B p := by
    intro p v'
    simp only [hT, jointWeight]
    have h1 : |∏ i, v'.1 i ^ p.2 i - ∏ i, v.1 i ^ p.2 i| ≤ 2 * B ^ (∑ i, p.2 i) := by
      calc |∏ i, v'.1 i ^ p.2 i - ∏ i, v.1 i ^ p.2 i|
          ≤ |∏ i, v'.1 i ^ p.2 i| + |∏ i, v.1 i ^ p.2 i| := abs_sub _ _
        _ ≤ B ^ (∑ i, p.2 i) + B ^ (∑ i, p.2 i) :=
            add_le_add (abs_prod_pow_le (hK v'.1 v'.2) _) (abs_prod_pow_le (hK v.1 v.2) _)
        _ = 2 * B ^ (∑ i, p.2 i) := by ring
    have h2 : b ^ (∑ j, p.1 j) ≤ B ^ (∑ j, p.1 j) := pow_le_pow_left₀ hb.le hbB _
    calc |monoFamily P (Sum.elim p.2 p.1)| * |∏ i, v'.1 i ^ p.2 i - ∏ i, v.1 i ^ p.2 i| *
          b ^ (∑ j, p.1 j)
        ≤ |monoFamily P (Sum.elim p.2 p.1)| * (2 * B ^ (∑ i, p.2 i)) * B ^ (∑ j, p.1 j) := by
          gcongr
        _ = 2 * (|monoFamily P (Sum.elim p.2 p.1)| * B ^ (∑ i, p.2 i) * B ^ (∑ j, p.1 j)) := by
          ring
  have hTcont : ∀ p, Continuous (T p) := by
    intro p
    simp only [hT]
    refine (continuous_const.mul (Continuous.abs ((continuous_finsetProd Finset.univ
      fun i _ => ((continuous_apply i).comp continuous_subtype_val).pow (p.2 i)).sub
        continuous_const))).mul continuous_const
  set H : K → ℝ := fun v' => ∑' p, T p v' with hH
  have hHcont : Continuous H := continuous_tsum hTcont (hW.mul_left 2) fun p v' => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hTnn p v')]
    exact hTle p v'
  have hH0 : H v = 0 := by
    simp only [hH, hT]
    simp
  -- summability of the majorant terms at every `v'`
  have hTsum : ∀ v', Summable fun p => T p v' := fun v' =>
    Summable.of_nonneg_of_le (fun p => hTnn p v') (fun p => hTle p v') (hW.mul_left 2)
  -- the ℓ¹ distance is bounded by the majorant
  have hle : ∀ v' : K, ‖jointDatum P B hb hbB hB hW K hK v' - jointDatum P B hb hbB hB hW K hK v‖
      ≤ H v' := by
    intro v'
    set X := jointDatum P B hb hbB hB hW K hK with hX
    rw [norm_eq_mass_add_mass]
    have hxi : xiCoord (X v' - X v) = 0 := by
      funext γ
      simp only [xiCoord, lp.coeFn_sub, Pi.sub_apply, hX, jointDatum_apply_inl, sub_zero,
        Pi.zero_apply]
    have hmass0 : mass (xiCoord (X v' - X v)) = 0 := by
      rw [hxi]
      simp [mass]
    rw [hmass0, zero_add]
    -- the amplitude part
    have heta : ∀ γ', etaCoord (X v' - X v) γ' =
        (jointFibre P v'.1 γ' - jointFibre P v.1 γ') * b ^ (∑ j, γ' j) := by
      intro γ'
      simp only [etaCoord, lp.coeFn_sub, Pi.sub_apply, hX, jointDatum_apply_inr]
      ring
    have hfib : ∀ γ', |jointFibre P v'.1 γ' - jointFibre P v.1 γ'| ≤
        ∑' α : Fin t → ℕ, |monoFamily P (Sum.elim α γ')| *
          |∏ i, v'.1 i ^ α i - ∏ i, v.1 i ^ α i| := by
      intro γ'
      have hs' := summable_fibre_term hB hW (hK v'.1 v'.2) γ'
      have hs := summable_fibre_term hB hW (hK v.1 v.2) γ'
      have hdiff : Summable fun α : Fin t → ℕ => monoFamily P (Sum.elim α γ') *
          (∏ i, v'.1 i ^ α i - ∏ i, v.1 i ^ α i) := by
        refine (hs'.sub hs).congr fun α => ?_
        ring
      unfold jointFibre
      rw [← hs'.tsum_sub hs]
      calc |∑' α : Fin t → ℕ, (monoFamily P (Sum.elim α γ') * ∏ i, v'.1 i ^ α i -
              monoFamily P (Sum.elim α γ') * ∏ i, v.1 i ^ α i)|
          = ‖∑' α : Fin t → ℕ, monoFamily P (Sum.elim α γ') *
              (∏ i, v'.1 i ^ α i - ∏ i, v.1 i ^ α i)‖ := by
            rw [Real.norm_eq_abs]
            congr 1
            exact tsum_congr fun α => by ring
        _ ≤ ∑' α : Fin t → ℕ, ‖monoFamily P (Sum.elim α γ') *
              (∏ i, v'.1 i ^ α i - ∏ i, v.1 i ^ α i)‖ := norm_tsum_le_tsum_norm hdiff.norm
        _ = ∑' α : Fin t → ℕ, |monoFamily P (Sum.elim α γ')| *
              |∏ i, v'.1 i ^ α i - ∏ i, v.1 i ^ α i| :=
            tsum_congr fun α => by rw [Real.norm_eq_abs, abs_mul]
    -- summability of the inner sums and the product rearrangement
    have hTv' := hTsum v'
    have hprod := (summable_prod_of_nonneg fun p => hTnn p v').1 hTv'
    calc mass (etaCoord (X v' - X v))
        = ∑' γ' : Fin m → ℕ, |jointFibre P v'.1 γ' - jointFibre P v.1 γ'| * b ^ (∑ j, γ' j) := by
          unfold mass
          refine tsum_congr fun γ' => ?_
          rw [heta, abs_mul, abs_of_pos (pow_pos hb _)]
      _ ≤ ∑' γ' : Fin m → ℕ, ∑' α : Fin t → ℕ, T (γ', α) v' := by
          refine Summable.tsum_le_tsum (fun γ' => ?_) ?_ hprod.2
          · have hs : Summable fun α : Fin t → ℕ => |monoFamily P (Sum.elim α γ')| *
                |∏ i, v'.1 i ^ α i - ∏ i, v.1 i ^ α i| :=
              (summable_mul_right_iff (pow_pos hb (∑ j, γ' j)).ne').1
                (by simpa only [hT] using hprod.1 γ')
            simp only [hT]
            rw [hs.tsum_mul_right]
            exact mul_le_mul_of_nonneg_right (hfib γ') (by positivity)
          · have := absSummable_etaCoord (X v' - X v)
            refine this.congr fun γ' => ?_
            rw [heta, abs_mul, abs_of_pos (pow_pos hb _)]
      _ = H v' := (hTv'.tsum_prod' hprod.1).symm
  exact squeeze_zero (fun _ => norm_nonneg _) hle (by
    have := hHcont.continuousAt (x := v)
    rw [ContinuousAt, hH0] at this
    exact this)

/-- **The tangential datum of a jointly analytic amplitude** over a compact tangential base. -/
noncomputable def jointTangentialData [CompactSpace K] : TangentialData K m :=
  ⟨jointDatum P B hb hbB hB hW K hK, continuous_jointDatum P B hb hbB hB hW K hK⟩

theorem xiCoord_jointTangentialData [CompactSpace K] (v : K) :
    xiCoord (jointTangentialData P B hb hbB hB hW K hK v) = 0 :=
  xiCoord_jointDatum P B hb hbB hB hW K hK v

/-- **The amplitude clause**: `evalF (toEta b (x v)) u = G(v, u)` on the normal box. -/
theorem evalF_toEta_jointTangentialData [CompactSpace K] {G : (Fin t ⊕ Fin m → ℝ) → ℝ}
    {R : ℝ≥0∞} (hG : HasFPowerSeriesOnBall G P 0 R) {ρ : ℝ≥0} (hρ : (ρ : ℝ≥0∞) < R)
    (hBρ : ((t + m : ℕ) : ℝ) * B < ρ) (hB1 : B < ρ) (v : K) {u : Fin m → ℝ}
    (hu : ∀ j, |u j| ≤ b) :
    evalF (toEta b (jointTangentialData P B hb hbB hB hW K hK v)) u = G (Sum.elim v.1 u) := by
  change evalF (toEta b (jointDatum P B hb hbB hB hW K hK v)) u = _
  rw [toEta_jointDatum]
  exact (hasSum_jointFibre_mul_mono hG hρ hB hBρ hB1 (hK v.1 v.2) hbB hu).tsum_eq

end Grammar
