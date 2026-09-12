/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.CoordinateBoxCoreCertificate
import Grammar.LpContinuity
import Grammar.JointTorusCertificate

/-!
# Parameterised series data: continuity into the data space (CCCXIX)

Astra #95, producer unit 3 ("parameterised series producer"). A `UniformSeriesFamily X d b'` is a
family `x ↦ f x` of coefficient families over a topological parameter space `X` with
coordinatewise continuity and a UNIFORM weighted-ℓ¹ majorant `|f x γ| ≤ M γ`, `Σ M_γ b'^{|γ|} < ∞`
(the real-coefficient form of "a uniform analytic extension with a uniform bound on a larger
normal polydisc": Cauchy estimates on a complex polydisc of radius `b'` produce exactly such an
`M`). We prove

* each fibre is a `b'`-weighted ℓ¹ family (`absSummableAt`), hence analytic on the ball of radius
  `b'` with Taylor family `f x` (CCCXVII/CCCXVIII);
* the Cauchy product of two uniform families is uniform (`conv`), with majorant `M ⋆ M'`;
* ★ the weighted datum `x ↦ ofFamilies b hb 0 (f x)` is CONTINUOUS into `DataSpace d` in the
  actual ℓ¹ topology (`continuous_datum`, ℓ¹ criterion of `LpContinuity` with the majorant
  `M_γ b^{|γ|}`), so it bundles as `datumC : C(X, DataSpace d)` — the `x` field of a
  `CorePresentation` over a compact base with `toEta_datumC`, `toXi_datumC`;
* joint continuity of the evaluated series `(x, u) ↦ evalF (f x) u` on `X × [−r, r]^d` for
  `r ≤ b'` (`continuous_evalF_clamp`, `continuousOn_evalF`, Weierstrass M-test) and the uniform
  bound `|evalF (f x) u| ≤ Σ M_γ r^{|γ|}` (`abs_evalF_le`) — the `cBound` of a normal-moment
  presentation;
* the amplitude identity for the product datum on the positive box (`evalF_conv`).

These are the analytic inputs a compact-base core presentation needs from series data; no
geometry is constructed here. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open CoeffFamily MonoRep

/-- A parameterised coefficient family with a uniform weighted-ℓ¹ majorant at scale `b'`. -/
structure UniformSeriesFamily (X : Type*) [TopologicalSpace X] (d : ℕ) (b' : ℝ) where
  /-- The coefficient family at the parameter `x`. -/
  f : X → CoeffFamily d
  /-- The uniform majorant. -/
  M : CoeffFamily d
  continuous_coeff : ∀ γ, Continuous fun x => f x γ
  abs_le : ∀ x γ, |f x γ| ≤ M γ
  M_abs : AbsSummableAt M b'

namespace UniformSeriesFamily

variable {X : Type*} [TopologicalSpace X] {d : ℕ} {b' : ℝ} (F : UniformSeriesFamily X d b')

theorem M_nonneg [Nonempty X] (γ : Fin d → ℕ) : 0 ≤ F.M γ :=
  (abs_nonneg _).trans (F.abs_le (Classical.arbitrary X) γ)

theorem absSummableAt (hb' : 0 ≤ b') (x : X) : AbsSummableAt (F.f x) b' := by
  have h := F.M_abs
  unfold AbsSummableAt at h ⊢
  refine Summable.of_nonneg_of_le (fun γ => by positivity) (fun γ => ?_) h
  exact mul_le_mul_of_nonneg_right ((F.abs_le x γ).trans (le_abs_self _)) (pow_nonneg hb' _)

theorem absSummableAt_of_le {b : ℝ} (hb : 0 ≤ b) (hbb' : b ≤ b') (x : X) :
    AbsSummableAt (F.f x) b :=
  AbsSummableAt.mono hb hbb' (F.absSummableAt (hb.trans hbb') x)

theorem M_absSummableAt_of_le {b : ℝ} (hb : 0 ≤ b) (hbb' : b ≤ b') : AbsSummableAt F.M b :=
  AbsSummableAt.mono hb hbb' F.M_abs

/-! ### The Cauchy product of uniform families -/

theorem conv_le_conv {c c' e e' : CoeffFamily d} (hc : ∀ γ, 0 ≤ c γ) (he : ∀ γ, 0 ≤ e γ)
    (hcc : ∀ γ, c γ ≤ c' γ) (hee : ∀ γ, e γ ≤ e' γ) (γ : Fin d → ℕ) :
    CoeffFamily.conv c e γ ≤ CoeffFamily.conv c' e' γ :=
  Finset.sum_le_sum fun α _ =>
    mul_le_mul (hcc α) (hee _) (he _) ((hc α).trans (hcc α))

/-- The Cauchy product of two uniform families, with majorant `M ⋆ M'`. -/
noncomputable def conv (hb' : 0 ≤ b') (G : UniformSeriesFamily X d b') :
    UniformSeriesFamily X d b' where
  f := fun x => CoeffFamily.conv (F.f x) (G.f x)
  M := CoeffFamily.conv F.M G.M
  continuous_coeff := fun _ =>
    continuous_finsetSum _ fun α _ => (F.continuous_coeff α).mul (G.continuous_coeff _)
  abs_le := fun x γ =>
    (abs_conv_le _ _ γ).trans (conv_le_conv (fun _ => abs_nonneg _) (fun _ => abs_nonneg _)
      (F.abs_le x) (G.abs_le x) γ)
  M_abs := AbsSummableAt.conv hb' F.M_abs G.M_abs

@[simp]
theorem conv_f (hb' : 0 ≤ b') (G : UniformSeriesFamily X d b') (x : X) :
    (F.conv hb' G).f x = CoeffFamily.conv (F.f x) (G.f x) := rfl

/-! ### The weighted datum -/

variable {b : ℝ} (hb : 0 < b) (hbb' : b ≤ b')

include hb hbb'

/-- The weighted majorant `M_γ b^{|γ|}` is summable (no sign condition on `M` is needed). -/
theorem summable_M_pow : Summable fun γ => F.M γ * b ^ (∑ i, γ i) :=
  Summable.of_norm_bounded (F.M_absSummableAt_of_le hb.le hbb') fun γ => by
    rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hb]

/-- The zero-phase weighted datum of the family at scale `b`. -/
noncomputable def datum (x : X) : DataSpace d :=
  ofFamilies b hb 0 (F.f x) (absSummableAt_zero b) (F.absSummableAt_of_le hb.le hbb' x)

theorem datum_inl (x : X) (γ : Fin d → ℕ) : F.datum hb hbb' x (Sum.inl γ) = 0 := by
  change (0 : CoeffFamily d) γ * b ^ (∑ i, γ i) = 0
  simp

theorem datum_inr (x : X) (γ : Fin d → ℕ) :
    F.datum hb hbb' x (Sum.inr γ) = F.f x γ * b ^ (∑ i, γ i) := rfl

theorem toEta_datum (x : X) : toEta b (F.datum hb hbb' x) = F.f x := toEta_ofFamilies _ _ _ _ _ _

theorem toXi_datum (x : X) : toXi b (F.datum hb hbb' x) = 0 := toXi_ofFamilies _ _ _ _ _ _

/-- The ℓ¹ majorant of the datum on the data index. -/
noncomputable def dataMajorant : DataIdx d → ℝ :=
  Sum.elim (fun _ => 0) fun γ => F.M γ * b ^ (∑ i, γ i)

theorem summable_dataMajorant : Summable (F.dataMajorant (b := b)) := by
  refine Summable.sum _ ?_ ?_
  · simp [dataMajorant]
  · exact F.summable_M_pow hb hbb'

/-- ★ **Continuity of the weighted datum into the data space** (ℓ¹ topology). -/
theorem continuous_datum : Continuous (F.datum hb hbb') := by
  refine continuous_dataSpace_of_majorant _ ?_ (F.dataMajorant (b := b))
    (F.summable_dataMajorant hb hbb') ?_
  · rintro (γ | γ)
    · simp only [datum_inl]
      exact continuous_const
    · simp only [datum_inr]
      exact (F.continuous_coeff γ).mul continuous_const
  · rintro x (γ | γ)
    · simp [datum_inl, dataMajorant]
    · rw [datum_inr]
      simp only [dataMajorant, Sum.elim_inr, abs_mul, abs_of_pos (pow_pos hb _)]
      exact mul_le_mul_of_nonneg_right (F.abs_le x γ) (pow_nonneg hb.le _)

/-- The weighted datum as a continuous map: the `x` field of a core presentation. -/
noncomputable def datumC : C(X, DataSpace d) := ⟨F.datum hb hbb', F.continuous_datum hb hbb'⟩

theorem datumC_apply (x : X) : F.datumC hb hbb' x = F.datum hb hbb' x := rfl

theorem toEta_datumC (x : X) : toEta b (F.datumC hb hbb' x) = F.f x := F.toEta_datum hb hbb' x

theorem toXi_datumC (x : X) : toXi b (F.datumC hb hbb' x) = 0 := F.toXi_datum hb hbb' x

theorem xiCoord_datum (x : X) : xiCoord (F.datum hb hbb' x) = 0 :=
  funext fun γ => F.datum_inl hb hbb' x γ

theorem xiCoord_datumC (x : X) : xiCoord (F.datumC hb hbb' x) = 0 := F.xiCoord_datum hb hbb' x

/-! ### Joint continuity of the evaluated series -/

omit hb hbb'

/-- The majorant at any nonnegative scale `r ≤ b'`. -/
theorem summable_M_pow' {r : ℝ} (hr : 0 ≤ r) (hrb' : r ≤ b') :
    Summable fun γ => F.M γ * r ^ (∑ i, γ i) :=
  Summable.of_norm_bounded (F.M_absSummableAt_of_le hr hrb') fun γ => by
    rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hr]

theorem abs_term_le {r : ℝ} (x : X) (u : Fin d → ℝ) (hu : ∀ i, |u i| ≤ r) (γ : Fin d → ℕ) :
    |F.f x γ * mono γ u| ≤ F.M γ * r ^ (∑ i, γ i) := by
  rw [abs_mul]
  exact mul_le_mul (F.abs_le x γ) (abs_mono_le_pow hu γ) (abs_nonneg _)
    ((abs_nonneg _).trans (F.abs_le x γ))

/-- Joint continuity of `(x, u) ↦ evalF (f x) (clamp r u)` on the whole product space. -/
theorem continuous_evalF_clamp {r : ℝ} (hr : 0 ≤ r) (hrb' : r ≤ b') :
    Continuous fun p : X × (Fin d → ℝ) => evalF (F.f p.1) (clamp r hr p.2) := by
  unfold evalF
  refine continuous_tsum (fun γ => ?_) (F.summable_M_pow' hr hrb') fun γ p => ?_
  · have hcm : Continuous (mono (d := d) γ) := by
      unfold mono
      exact continuous_finsetProd _ fun i _ => (continuous_apply i).pow _
    exact ((F.continuous_coeff γ).comp continuous_fst).mul
      (hcm.comp ((continuous_clamp r hr).comp continuous_snd))
  · rw [Real.norm_eq_abs]
    exact F.abs_term_le p.1 _ (abs_clamp_le hr p.2) γ

/-- Joint continuity of the evaluated series on `X × [−r, r]^d`. -/
theorem continuousOn_evalF {r : ℝ} (hr : 0 ≤ r) (hrb' : r ≤ b') :
    ContinuousOn (fun p : X × (Fin d → ℝ) => evalF (F.f p.1) p.2)
      (univ ×ˢ piBox d (Icc (-r) r)) := by
  refine (F.continuous_evalF_clamp hr hrb').continuousOn.congr fun p hp => ?_
  have hu : ∀ i, |p.2 i| ≤ r := fun i => _root_.abs_le.2 (hp.2 i (Set.mem_univ i))
  simp only
  rw [clamp_eq_self hr hu]

/-- The uniform bound `|evalF (f x) u| ≤ Σ M_γ r^{|γ|}` on `[−r, r]^d`. -/
theorem abs_evalF_le {r : ℝ} (hr : 0 ≤ r) (hrb' : r ≤ b') (x : X) (u : Fin d → ℝ)
    (hu : ∀ i, |u i| ≤ r) :
    |evalF (F.f x) u| ≤ ∑' γ, F.M γ * r ^ (∑ i, γ i) := by
  have hs : Summable fun γ => ‖F.f x γ * mono γ u‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun γ => by rw [Real.norm_eq_abs]; exact F.abs_term_le x u hu γ)
      (F.summable_M_pow' hr hrb')
  unfold evalF
  rw [← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm hs).trans (Summable.tsum_le_tsum (fun γ => ?_) hs
    (F.summable_M_pow' hr hrb'))
  rw [Real.norm_eq_abs]
  exact F.abs_term_le x u hu γ

/-- Each fibre is analytic at `0` on the ball of radius `r < b'`, uniformly in the parameter. -/
theorem hasFPowerSeriesOnBall_evalFClamp {r : ℝ} (hb' : 0 < b') (hr : 0 < r) (hrb' : r < b')
    (x : X) :
    HasFPowerSeriesOnBall (evalFClamp (F.f x) r hr.le) (polySeriesD (F.f x)) 0
      (ENNReal.ofReal r) :=
  Grammar.hasFPowerSeriesOnBall_evalFClamp (F.f x) hb' (F.absSummableAt hb'.le x) hr hrb'

/-- The Taylor family of each clamped fibre is the coefficient family. -/
theorem jetFamily_evalFClamp {n : ℕ} (F : UniformSeriesFamily X (n + 1) b') {r : ℝ}
    (hb' : 0 < b') (hr : 0 < r) (hrb' : r < b') (x : X) :
    jetFamily n (evalFClamp (F.f x) r hr.le) = F.f x :=
  Grammar.jetFamily_evalFClamp (F.f x) hb' (F.absSummableAt hb'.le x) hr hrb'

include hb hbb' in
/-- The amplitude identity of the product datum on the positive box `[0, b]^d`. -/
theorem evalF_conv (G : UniformSeriesFamily X d b') (x : X) {u : Fin d → ℝ}
    (hu : ∀ i, 0 ≤ u i ∧ u i ≤ b) :
    evalF (toEta b ((F.conv (hb.le.trans hbb') G).datum hb hbb' x)) u =
      evalF (F.f x) u * evalF (G.f x) u := by
  rw [toEta_datum, conv_f]
  exact evalF_conv_of_absSummableAt hb (F.absSummableAt_of_le hb.le hbb' x)
    (G.absSummableAt_of_le hb.le hbb' x) hu

end UniformSeriesFamily

end Grammar
