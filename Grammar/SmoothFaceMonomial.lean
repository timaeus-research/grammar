/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothFiniteUniqueness
import Grammar.SmoothTwoDim
import Grammar.BoxTaylorTree
import Grammar.PopulationDataBridge

/-!
# The two-regime estimate for face monomial box integrals (smooth engine, unit 3c)

The inner function of the facewise engine in several variables is the face monomial box integral
`Z_e(t) = ∫_{(0,b]^ι} u^e e^{−β t u^{2k}} du` (`faceMono`). It is continuous in `t`
(`continuous_faceMono`, hence `measurable_faceMono`), nonnegative, and bounded by
`∏ᵢ b^{eᵢ+1}/(eᵢ+1)` for `t ≥ 0` (`faceMono_le`). For `ι = Fin (n+1)` it is the box engine's
`familyPhaseIntegralBox` with `h = 0`, `cξ = 0` and the monomial coefficient family `monoFam e`
(`familyPhaseIntegralBox_monoFam`), so the Taylor tree on the box (`boxTaylorTree_cutoff_bound`)
gives the power–log estimate in the large regime `t b^{2|k|} ≥ 1`; in the small regime both the
integral and the power–log sum are bounded by constants times `t^{−L}(1 + |log t|)^n`. Together
this is the GLOBAL two-regime estimate `|Z_e(t) − powLog(t)| ≤ C t^{−L} (1 + |log t|)^n` for all
`t > 0` (★★ `faceMono_two_regime_fin`), exactly the input `hZ2` of the generic face theorem
`face_expansion`, with spectrum the lattice `Λ^{Q}_L`, `Q = 2 ∏ kᵢ`, and logarithmic degree
`n = |ι| − 1`. Reindexing the box along `ι ≃ Fin (|ι|−1+1)` transports the estimate to any
nonempty finite index type (★★ `faceMono_two_regime`), with the explicit coefficients
`faceMonoCoeff`. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

namespace SmoothEngine

open CoeffFamily

variable {ι : Type*} [Fintype ι]

/-! ### The face monomial integral -/

/-- `Z_e(t) = ∫_{(0,b]^ι} u^e e^{−β t u^{2k}} du`. -/
noncomputable def faceMono (k e : ι → ℕ) (β b t : ℝ) : ℝ :=
  ∫ u in box ι b, mono e u * Real.exp (-(β * t) * mono (fun i => 2 * k i) u)

/-- The open box and the closed box carry the same restricted measure. -/
theorem restrict_box_eq_restrict_Icc (b : ℝ) :
    (volume : Measure (ι → ℝ)).restrict (box ι b) =
      volume.restrict (Set.pi univ fun _ => Icc 0 b) := by
  rw [box, volume_pi, Measure.restrict_pi_pi, Measure.restrict_pi_pi]
  congr 1
  funext _
  exact Measure.restrict_congr_set Ioc_ae_eq_Icc

theorem continuous_faceMono_integrand (k e : ι → ℕ) (β : ℝ) :
    Continuous fun p : ℝ × (ι → ℝ) =>
      mono e p.2 * Real.exp (-(β * p.1) * mono (fun i => 2 * k i) p.2) :=
  ((continuous_mono e).comp continuous_snd).mul (Real.continuous_exp.comp
    ((continuous_const.mul continuous_fst).neg.mul
      ((continuous_mono fun i => 2 * k i).comp continuous_snd)))

theorem continuous_faceMono (k e : ι → ℕ) (β b : ℝ) : Continuous (faceMono k e β b) := by
  unfold faceMono
  simp_rw [restrict_box_eq_restrict_Icc]
  exact continuous_parametric_integral_of_continuous
    (f := fun t u => mono e u * Real.exp (-(β * t) * mono (fun i => 2 * k i) u))
    (continuous_faceMono_integrand k e β) (isCompact_univ_pi fun _ => isCompact_Icc)

theorem measurable_faceMono (k e : ι → ℕ) (β b : ℝ) : Measurable (faceMono k e β b) :=
  (continuous_faceMono k e β b).measurable

theorem faceMono_nonneg (k e : ι → ℕ) (β b t : ℝ) : 0 ≤ faceMono k e β b t :=
  setIntegral_nonneg (measurableSet_box b) fun _ hu =>
    mul_nonneg (mono_pos e (pos_of_mem_box hu)).le (Real.exp_pos _).le

/-- `∫_{(0,b]^ι} u^e du = ∏ᵢ b^{eᵢ+1}/(eᵢ+1)`. -/
theorem integral_box_mono (e : ι → ℕ) {b : ℝ} (hb : 0 ≤ b) :
    ∫ u in box ι b, mono e u = ∏ i, b ^ (e i + 1) / (e i + 1) := by
  unfold mono box
  rw [volume_pi, Measure.restrict_pi_pi, integral_fintype_prod_eq_prod (fun i x => x ^ e i)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← intervalIntegral.integral_of_le hb, integral_pow, zero_pow (Nat.succ_ne_zero _),
    sub_zero]

theorem integrableOn_faceMono_integrand (k e : ι → ℕ) (β b t : ℝ) :
    IntegrableOn (fun u => mono e u * Real.exp (-(β * t) * mono (fun i => 2 * k i) u))
      (box ι b) :=
  integrableOn_box_of_continuous ((continuous_faceMono_integrand k e β).comp
    (Continuous.prodMk continuous_const continuous_id)) b

/-- The trivial bound `Z_e(t) ≤ ∏ᵢ b^{eᵢ+1}/(eᵢ+1)` for `β, t ≥ 0`. -/
theorem faceMono_le (k e : ι → ℕ) {β b t : ℝ} (hβ : 0 ≤ β) (hb : 0 ≤ b) (ht : 0 ≤ t) :
    faceMono k e β b t ≤ ∏ i, b ^ (e i + 1) / (e i + 1) := by
  rw [← integral_box_mono e hb]
  refine setIntegral_mono_on (integrableOn_faceMono_integrand k e β b t)
    (integrableOn_box_of_continuous (continuous_mono e) b) (measurableSet_box b) fun u hu => ?_
  have hpos := pos_of_mem_box hu
  have hexp : Real.exp (-(β * t) * mono (fun i => 2 * k i) u) ≤ 1 := by
    rw [← Real.exp_zero]
    refine Real.exp_le_exp.2 ?_
    rw [neg_mul, neg_nonpos]
    exact mul_nonneg (mul_nonneg hβ ht) (mono_pos _ hpos).le
  calc mono e u * Real.exp (-(β * t) * mono (fun i => 2 * k i) u)
      ≤ mono e u * 1 := mul_le_mul_of_nonneg_left hexp (mono_pos e hpos).le
    _ = mono e u := mul_one _

/-! ### Identification with the box engine -/

/-- The coefficient family of the monomial `u^e`. -/
def monoFam {d : ℕ} (e : Fin d → ℕ) : CoeffFamily d := fun γ => if γ = e then 1 else 0

theorem evalF_monoFam {d : ℕ} (e : Fin d → ℕ) (u : Fin d → ℝ) :
    evalF (monoFam e) u = mono e u := by
  unfold evalF monoFam
  rw [tsum_eq_single e fun γ hγ => by simp [hγ], if_pos rfl, one_mul]
  rfl

theorem absSummableAt_monoFam {d : ℕ} (e : Fin d → ℕ) (b : ℝ) : AbsSummableAt (monoFam e) b :=
  summable_of_ne_finset_zero (s := {e}) fun γ hγ => by
    rw [Finset.mem_singleton] at hγ
    simp [monoFam, hγ]

/-- The face monomial integral is the box engine's standard integral with `h = 0`, `cξ = 0` and
the monomial family `cη = monoFam e`. -/
theorem familyPhaseIntegralBox_monoFam (n : ℕ) (k e : Fin (n + 1) → ℕ) (β b N : ℝ) :
    familyPhaseIntegralBox n 0 k β N b 0 (monoFam e) = faceMono k e β b N := by
  unfold familyPhaseIntegralBox faceMono
  refine setIntegral_congr_fun (measurableSet_box b) fun u _ => ?_
  rw [evalF_monoFam, evalF_zero]
  simp only [Pi.zero_apply, pow_zero, Finset.prod_const_one, mul_one, mul_zero, add_zero]
  unfold mono
  rw [neg_mul]

/-! ### The two regimes -/

/-- `1 + log(t c) ≤ (1 + |log c|)(1 + |log t|)` for `t, c > 0`. -/
theorem one_add_log_mul_le_abs {t c : ℝ} (ht : 0 < t) (hc : 0 < c) :
    1 + Real.log (t * c) ≤ (1 + |Real.log c|) * (1 + |Real.log t|) := by
  rw [Real.log_mul ht.ne' hc.ne']
  have h1 := le_abs_self (Real.log t)
  have h2 := le_abs_self (Real.log c)
  nlinarith [abs_nonneg (Real.log t), abs_nonneg (Real.log c),
    mul_nonneg (abs_nonneg (Real.log t)) (abs_nonneg (Real.log c))]

/-- `|log t|^j ≤ (1 + |log t|)^n` for `j ≤ n`. -/
theorem abs_log_pow_le_one_add_pow {j n : ℕ} (hj : j ≤ n) (t : ℝ) :
    |Real.log t| ^ j ≤ (1 + |Real.log t|) ^ n := by
  have h0 := abs_nonneg (Real.log t)
  calc |Real.log t| ^ j ≤ (1 + |Real.log t|) ^ j := pow_le_pow_left₀ h0 (by linarith) j
    _ ≤ (1 + |Real.log t|) ^ n := pow_le_pow_right₀ (by linarith) hj

/-- In the small regime `0 < t`, `t c < 1`, every `t^{−μ}` with `0 ≤ μ < L` is at most
`(1 + c^{−L}) t^{−L}`. -/
theorem rpow_neg_le_small {μ L c t : ℝ} (hμ0 : 0 ≤ μ) (hμL : μ < L) (hc : 0 < c) (ht : 0 < t)
    (htc : t * c < 1) : t ^ (-μ) ≤ (1 + c ^ (-L)) * t ^ (-L) := by
  have hsplit : t ^ (-μ) = t ^ (L - μ) * t ^ (-L) := by
    rw [← Real.rpow_add ht]; congr 1; ring
  rw [hsplit]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg ht.le _)
  have hcL := Real.rpow_nonneg hc.le (-L)
  rcases le_or_gt t 1 with h1 | h1
  · calc t ^ (L - μ) ≤ 1 := Real.rpow_le_one ht.le h1 (by linarith)
      _ ≤ 1 + c ^ (-L) := by linarith
  · have htc' : t ≤ c⁻¹ := by
      rw [← one_div]; exact (le_div_iff₀ hc).2 htc.le
    calc t ^ (L - μ) ≤ t ^ L := Real.rpow_le_rpow_of_exponent_le h1.le (by linarith)
      _ ≤ c⁻¹ ^ L := Real.rpow_le_rpow ht.le htc' (by linarith)
      _ = c ^ (-L) := by rw [Real.inv_rpow hc.le, ← Real.rpow_neg hc.le]
      _ ≤ 1 + c ^ (-L) := by linarith

/-- The small-regime bound on a power–log sum over the lattice below `L`. -/
theorem abs_powLog_le_small {Q n : ℕ} (hQ : 0 < Q) (cf : ℝ → ℕ → ℝ) {L c t : ℝ} (hc : 0 < c)
    (ht : 0 < t) (htc : t * c < 1) :
    |powLog (latticeBelow Q L) n cf t| ≤
      (∑ μ ∈ latticeBelow Q L, ∑ j ∈ Finset.range (n + 1), |cf μ j|) * (1 + c ^ (-L)) *
        t ^ (-L) * (1 + |Real.log t|) ^ n := by
  unfold powLog
  rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun μ hμ => ?_)
  rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  obtain ⟨⟨m, hm⟩, hμL⟩ := (mem_latticeBelow_iff hQ).1 hμ
  have hμ0 : 0 ≤ μ := by rw [hm]; positivity
  have hjn : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  have hpow := rpow_neg_le_small hμ0 hμL hc ht htc
  rw [abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht _), abs_pow]
  calc |cf μ j| * t ^ (-μ) * |Real.log t| ^ j
      ≤ |cf μ j| * ((1 + c ^ (-L)) * t ^ (-L)) * (1 + |Real.log t|) ^ n :=
        mul_le_mul (mul_le_mul_of_nonneg_left hpow (abs_nonneg _))
          (abs_log_pow_le_one_add_pow hjn t) (by positivity) (by positivity)
    _ = _ := by ring

/-- ★★ **The global two-regime estimate for the face monomial integral on `(0,b]^{n+1}`**:
`|Z_e(t) − ∑_{μ∈Λ^Q_L} ∑_{j≤n} C_{μ,j} t^{−μ} (log t)^j| ≤ C t^{−L} (1 + |log t|)^n` for every
`t > 0`, with `Q = 2 ∏ kᵢ` and the box-engine coefficients `boxCoeff`. -/
theorem faceMono_two_regime_fin (n : ℕ) (k e : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β b : ℝ}
    (hβ : 0 < β) (hb : 0 < b) {L : ℝ} (hL : 0 < L) :
    ∃ C : ℝ, ∀ t : ℝ, 0 < t →
      |faceMono k e β b t -
        powLog (latticeBelow (latticeQ k) L) n (boxCoeff n 0 k β b 0 (monoFam e)) t| ≤
      C * t ^ (-L) * (1 + |Real.log t|) ^ n := by
  have hQ : 0 < latticeQ k := latticeQ_pos k hk
  set c : ℝ := b ^ (2 * ∑ i, k i) with hc
  have hc0 : 0 < c := pow_pos hb _
  set Cb : ℝ := b ^ (∑ i, (0 : Fin (n + 1) → ℕ) i + (n + 1)) *
    cutoffBound n k β L (scale 0 b 0) (mass (scale (monoFam e) b)) (mass (scale 0 b)) with hCb
  have hCb0 : 0 ≤ Cb :=
    mul_nonneg (pow_nonneg hb.le _) (cutoffBound_nonneg n k β hβ L _ (mass_nonneg _) _)
  set B : ℝ := ∏ i, b ^ (e i + 1) / (e i + 1) with hB
  have hB0 : 0 ≤ B := Finset.prod_nonneg fun i _ => by positivity
  set S : ℝ := ∑ μ ∈ latticeBelow (latticeQ k) L, ∑ j ∈ Finset.range (n + 1),
    |boxCoeff n 0 k β b 0 (monoFam e) μ j| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hcL : 0 ≤ c ^ (-L) := Real.rpow_nonneg hc0.le _
  refine ⟨Cb * c ^ (-L) * (1 + |Real.log c|) ^ n + (B * c ^ (-L) + S * (1 + c ^ (-L))),
    fun t ht => ?_⟩
  have htL : 0 ≤ t ^ (-L) := Real.rpow_nonneg ht.le _
  have hlt : 0 ≤ (1 + |Real.log t|) ^ n := by positivity
  have hC1 : 0 ≤ Cb * c ^ (-L) * (1 + |Real.log c|) ^ n := by positivity
  have hC2 : 0 ≤ B * c ^ (-L) + S * (1 + c ^ (-L)) := by positivity
  rcases le_or_gt 1 (t * c) with hreg | hreg
  · -- large regime `t b^{2|k|} ≥ 1`: the Taylor tree on the box
    have hscale : boxScale k b t = t * c := by unfold boxScale; rw [← hc]
    have hbound := boxTaylorTree_cutoff_bound n 0 k hk β hβ hL hb ht.le (hscale ▸ hreg)
      (absSummableAt_zero b) (absSummableAt_monoFam e b)
    rw [familyPhaseIntegralBox_monoFam, boxSpectralSum_eq n 0 k β L hb 0 (monoFam e) ht,
      hscale] at hbound
    rw [powLog_eq_absSpectralSum]
    have hlog0 : 0 ≤ Real.log (t * c) := Real.log_nonneg hreg
    have hlogle : (1 + Real.log (t * c)) ^ n ≤ ((1 + |Real.log c|) * (1 + |Real.log t|)) ^ n :=
      pow_le_pow_left₀ (by linarith) (one_add_log_mul_le_abs ht hc0) n
    have hrp : (t * c) ^ (-L) = t ^ (-L) * c ^ (-L) := Real.mul_rpow ht.le hc0.le
    calc |faceMono k e β b t - absSpectralSum (latticeQ k) n (boxCoeff n 0 k β b 0 (monoFam e)) L t|
        ≤ Cb * ((t * c) ^ (-L) * (1 + Real.log (t * c)) ^ n) := hbound
      _ ≤ Cb * ((t ^ (-L) * c ^ (-L)) * ((1 + |Real.log c|) * (1 + |Real.log t|)) ^ n) := by
          rw [hrp]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlogle (by positivity)) hCb0
      _ = Cb * c ^ (-L) * (1 + |Real.log c|) ^ n * t ^ (-L) * (1 + |Real.log t|) ^ n := by
          rw [mul_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC2) htL) hlt
  · -- small regime `t b^{2|k|} < 1`: trivial bounds on both terms
    have hface : |faceMono k e β b t| ≤ B * c ^ (-L) * t ^ (-L) * (1 + |Real.log t|) ^ n := by
      rw [abs_of_nonneg (faceMono_nonneg k e β b t)]
      have h1 : 1 ≤ c ^ (-L) * t ^ (-L) := by
        rw [← Real.mul_rpow hc0.le ht.le, mul_comm]
        exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by positivity) hreg.le (by linarith)
      have h2 : (1 : ℝ) ≤ (1 + |Real.log t|) ^ n :=
        one_le_pow₀ (by linarith [abs_nonneg (Real.log t)])
      calc faceMono k e β b t ≤ B := faceMono_le k e hβ.le hb.le ht.le
        _ = B * 1 * 1 := by ring
        _ ≤ B * (c ^ (-L) * t ^ (-L)) * (1 + |Real.log t|) ^ n :=
            mul_le_mul (mul_le_mul_of_nonneg_left h1 hB0) h2 zero_le_one (by positivity)
        _ = _ := by ring
    have hpl := abs_powLog_le_small hQ (boxCoeff n 0 k β b 0 (monoFam e))
      (n := n) (L := L) hc0 ht hreg
    have htri := abs_add_le (faceMono k e β b t)
      (-powLog (latticeBelow (latticeQ k) L) n (boxCoeff n 0 k β b 0 (monoFam e)) t)
    rw [abs_neg, ← sub_eq_add_neg] at htri
    calc |faceMono k e β b t -
          powLog (latticeBelow (latticeQ k) L) n (boxCoeff n 0 k β b 0 (monoFam e)) t|
        ≤ |faceMono k e β b t| +
          |powLog (latticeBelow (latticeQ k) L) n (boxCoeff n 0 k β b 0 (monoFam e)) t| := htri
      _ ≤ B * c ^ (-L) * t ^ (-L) * (1 + |Real.log t|) ^ n +
          S * (1 + c ^ (-L)) * t ^ (-L) * (1 + |Real.log t|) ^ n := add_le_add hface hpl
      _ = (B * c ^ (-L) + S * (1 + c ^ (-L))) * t ^ (-L) * (1 + |Real.log t|) ^ n := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC1) htL) hlt

/-! ### Transport to an arbitrary finite index type -/

/-- Reindexing the face monomial integral along an equivalence of index types. -/
theorem faceMono_reindex {κ : Type*} [Fintype κ] (σ : ι ≃ κ) (k e : ι → ℕ) (β b t : ℝ) :
    faceMono k e β b t = faceMono (k ∘ σ.symm) (e ∘ σ.symm) β b t := by
  have hmp : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : κ => ℝ) σ) volume volume :=
    volume_measurePreserving_piCongrLeft (fun _ : κ => ℝ) σ
  have hpre : MeasurableEquiv.piCongrLeft (fun _ : κ => ℝ) σ ⁻¹' box κ b = box ι b := by
    rw [box, box, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_preimage_univ_pi]
  have hmono : ∀ (a : κ → ℕ) (x : ι → ℝ),
      mono a (MeasurableEquiv.piCongrLeft (fun _ : κ => ℝ) σ x) = mono (a ∘ σ) x := by
    intro a x
    unfold mono
    rw [← Equiv.prod_comp σ]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Function.comp_apply, MeasurableEquiv.piCongrLeft_apply_apply]
  have he : (e ∘ σ.symm) ∘ σ = e := by funext i; simp
  have hk : (fun j => 2 * (k ∘ σ.symm) j) ∘ σ = fun i => 2 * k i := by funext i; simp
  have h := hmp.setIntegral_preimage_emb
    (MeasurableEquiv.piCongrLeft (fun _ : κ => ℝ) σ).measurableEmbedding
    (fun v => mono (e ∘ σ.symm) v * Real.exp (-(β * t) * mono (fun j => 2 * (k ∘ σ.symm) j) v))
    (box κ b)
  rw [hpre] at h
  unfold faceMono
  rw [← h]
  refine setIntegral_congr_fun (measurableSet_box b) fun x _ => ?_
  simp only [hmono, he, hk]

/-- The reindexing `ι ≃ Fin (|ι| − 1 + 1)` of a nonempty finite index type. -/
noncomputable def faceEquiv (ι : Type*) [Fintype ι] [Nonempty ι] :
    ι ≃ Fin (Fintype.card ι - 1 + 1) :=
  (Fintype.equivFin ι).trans
    (finCongr (Nat.sub_add_cancel (Nat.one_le_of_lt Fintype.card_pos)).symm)

/-- The face monomial power–log coefficients `C_{μ,j}` on a nonempty finite index type, defined
through the box engine after reindexing. -/
noncomputable def faceMonoCoeff [Nonempty ι] (k e : ι → ℕ) (β b : ℝ) (μ : ℝ) (j : ℕ) : ℝ :=
  boxCoeff (Fintype.card ι - 1) 0 (k ∘ (faceEquiv ι).symm) β b 0
    (monoFam (e ∘ (faceEquiv ι).symm)) μ j

theorem latticeQ_comp_faceEquiv [Nonempty ι] (k : ι → ℕ) :
    latticeQ (k ∘ (faceEquiv ι).symm) = 2 * ∏ i, k i := by
  unfold latticeQ
  exact congrArg (2 * ·) (Equiv.prod_comp (faceEquiv ι).symm k)

/-! ### Support of the box coefficients -/

/-- The box coefficients vanish off the lattice `(2∏kᵢ)⁻¹ℕ`. -/
theorem boxCoeff_eq_zero_of_not_lattice (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) {b : ℝ} (hb : 0 < b) {cξ cη : CoeffFamily (n + 1)}
    (hξ : AbsSummableAt cξ b) (hη : AbsSummableAt cη b) {μ : ℝ}
    (hμ : ∀ m : ℕ, μ ≠ (m : ℝ) / latticeQ k) (j : ℕ) : boxCoeff n h k β b cξ cη μ j = 0 := by
  have hc : ¬ candidateExp h k μ := fun hc => by
    obtain ⟨m, hm⟩ := candidateExp_mem_lattice hk hc
    exact hμ m hm
  have hz : ∀ q, familySpectralCoeff n h k β (scale cξ b) (scale cη b) μ q = 0 := fun q =>
    familySpectralCoeff_eq_zero_of_not_candidate n h k hk β hβ (AbsSummable.of_scale hb.le hξ)
      (AbsSummable.of_scale hb.le hη) hc q
  simp [boxCoeff, hz]

/-- The box coefficients vanish above the logarithmic degree `n`. -/
theorem boxCoeff_eq_zero_of_lt (n : ℕ) (h k : Fin (n + 1) → ℕ) (β b : ℝ)
    (cξ cη : CoeffFamily (n + 1)) (μ : ℝ) {j : ℕ} (hj : n < j) :
    boxCoeff n h k β b cξ cη μ j = 0 := by
  unfold boxCoeff
  rw [Finset.Ico_eq_empty_of_le (by omega), Finset.sum_empty, mul_zero]

theorem faceMonoCoeff_eq_zero_of_not_lattice [Nonempty ι] (k e : ι → ℕ) (hk : ∀ i, 0 < k i)
    {β : ℝ} (hβ : 0 < β) {b : ℝ} (hb : 0 < b) {μ : ℝ}
    (hμ : ∀ m : ℕ, μ ≠ (m : ℝ) / ((2 * ∏ i, k i : ℕ) : ℝ)) (j : ℕ) :
    faceMonoCoeff k e β b μ j = 0 := by
  unfold faceMonoCoeff
  refine boxCoeff_eq_zero_of_not_lattice _ 0 (k ∘ (faceEquiv ι).symm) (fun i => hk _) β hβ hb
    (absSummableAt_zero b) (absSummableAt_monoFam _ b) (fun m => ?_) j
  rw [latticeQ_comp_faceEquiv]
  exact hμ m

theorem faceMonoCoeff_eq_zero_of_lt [Nonempty ι] (k e : ι → ℕ) (β b μ : ℝ) {j : ℕ}
    (hj : Fintype.card ι - 1 < j) : faceMonoCoeff k e β b μ j = 0 :=
  boxCoeff_eq_zero_of_lt _ _ _ β b _ _ μ hj

/-- ★★ **The global two-regime estimate for the face monomial integral on `(0,b]^ι`**: for every
`t > 0`,
`|Z_e(t) − ∑_{μ∈Λ^Q_L} ∑_{j≤|ι|−1} C_{μ,j} t^{−μ} (log t)^j| ≤ C t^{−L} (1 + |log t|)^{|ι|−1}`
with `Q = 2 ∏ᵢ kᵢ` and the coefficients `faceMonoCoeff`. -/
theorem faceMono_two_regime [Nonempty ι] (k e : ι → ℕ) (hk : ∀ i, 0 < k i) {β b : ℝ}
    (hβ : 0 < β) (hb : 0 < b) {L : ℝ} (hL : 0 < L) :
    ∃ C : ℝ, ∀ t : ℝ, 0 < t →
      |faceMono k e β b t - powLog (latticeBelow (2 * ∏ i, k i) L) (Fintype.card ι - 1)
        (faceMonoCoeff k e β b) t| ≤
      C * t ^ (-L) * (1 + |Real.log t|) ^ (Fintype.card ι - 1) := by
  obtain ⟨C, hC⟩ := faceMono_two_regime_fin (Fintype.card ι - 1) (k ∘ (faceEquiv ι).symm)
    (e ∘ (faceEquiv ι).symm) (fun j => hk _) hβ hb hL
  refine ⟨C, fun t ht => ?_⟩
  have h := hC t ht
  rw [latticeQ_comp_faceEquiv, ← faceMono_reindex] at h
  exact h

end SmoothEngine

end Grammar
