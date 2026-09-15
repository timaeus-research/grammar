/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.EmpiricalInnerKernel
import Grammar.SmoothFaceMonomial

/-!
# The empirical inner kernel as a power–log system with a global two-regime estimate

The exact series of `EmpiricalInnerKernel` is regrouped by exponent into the coefficient system
`empInnerCoeff k e G μ q = ∏ 1/(2kᵢ) ∑_j coeffAt(rep) μ j · C(j,q) · mellinMom G μ (j−q)` on the
spectrum `exps = {(eᵢ+1)/(2kᵢ)}` (`empInnerSeries_eq_powLog`). Every moment is bounded by `A` times
a moment of the growth envelope (`abs_mellinMom_le`), so the coefficients are `O(A)`; and for every
cutoff `L > 0` the kernel satisfies the GLOBAL two-regime estimate
`|I_G(t) − powLog (exps ∩ {μ < L}) n (empInnerCoeff k e G) t| ≤ A · C · t^{−L} (1 + |log t|)^n`
for all `t > 0` (★★ `empUnitInner_two_regime`), with `C` depending only on `k, e, m, M, L` — exactly
the inner hypothesis `hZ2` of the generic face theorem `face_expansion`, linear in the growth
constant of the field factor. The kernel is measurable in `t` (`measurable_empUnitInner`).
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology
open scoped ContDiff

namespace Grammar

namespace SmoothEngine

variable {n : ℕ}

/-! ### Moment bounds -/

/-- The moment of the growth envelope: `∫₀^∞ s^{μ−1} |log s|^ℓ (1+√s)^m e^{M√s} e^{−s} ds`. -/
noncomputable def momBound (m : ℕ) (M μ : ℝ) (ℓ : ℕ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), s ^ (μ - 1) * |log s| ^ ℓ *
    ((1 + Real.sqrt s) ^ m * exp (M * Real.sqrt s) * exp (-s))

theorem envelope_measurable (m : ℕ) (M μ : ℝ) (ℓ : ℕ) :
    Measurable fun s : ℝ => s ^ (μ - 1) * |log s| ^ ℓ *
      ((1 + Real.sqrt s) ^ m * exp (M * Real.sqrt s) * exp (-s)) := by
  fun_prop

/-- The envelope is itself the moment kernel of the growth-`(1, m, M)` factor `τ ↦ (1+τ)^m e^{Mτ}`
up to the sign of the log, so its integrability follows from the kernel bounds. -/
theorem integrableOn_envelope (m : ℕ) (M : ℝ) {μ : ℝ} (hμ : 0 < μ) (ℓ : ℕ) :
    IntegrableOn (fun s : ℝ => s ^ (μ - 1) * |log s| ^ ℓ *
      ((1 + Real.sqrt s) ^ m * exp (M * Real.sqrt s) * exp (-s))) (Ioi 0) := by
  have hG : GrowthLE (fun τ => (1 + τ) ^ m * exp (M * τ)) 1 m M := fun τ hτ => by
    rw [abs_of_nonneg (by positivity)]
    ring_nf
    exact le_rfl
  have hGm : Measurable fun τ : ℝ => (1 + τ) ^ m * exp (M * τ) := by fun_prop
  have hI : IntegrableOn (fun s => |momKernel (fun τ => (1 + τ) ^ m * exp (M * τ)) μ ℓ s|)
      (Ioi 0) :=
    (integrableOn_momKernel hGm hG hμ ℓ).abs
  refine hI.congr_fun (fun s hs => ?_) measurableSet_Ioi
  have hs0 : 0 < s := hs
  change |s ^ (μ - 1) * (-log s) ^ ℓ *
    ((1 + Real.sqrt s) ^ m * exp (M * Real.sqrt s) * exp (-s))| = _
  rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hs0.le _), abs_pow, abs_neg,
    abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ (1 + Real.sqrt s) ^ m * exp (M * Real.sqrt s) * exp (-s))]

theorem momBound_nonneg (m : ℕ) (M μ : ℝ) (ℓ : ℕ) : 0 ≤ momBound m M μ ℓ :=
  setIntegral_nonneg measurableSet_Ioi fun s hs => by
    have hs0 : 0 < s := hs
    positivity

/-- `|mellinMom G μ ℓ| ≤ A · momBound m M μ ℓ`. -/
theorem abs_mellinMom_le {G : ℝ → ℝ} {A : ℝ} {m : ℕ} {M : ℝ} (hG : GrowthLE G A m M) {μ : ℝ}
    (hμ : 0 < μ) (ℓ : ℕ) :
    |mellinMom G μ ℓ| ≤ A * momBound m M μ ℓ := by
  unfold mellinMom momBound
  rw [← MeasureTheory.integral_const_mul, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le ((integrableOn_envelope m M hμ ℓ).const_mul A) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => ?_)
  have hs0 : 0 < s := hs
  have hsq : 0 ≤ Real.sqrt s := Real.sqrt_nonneg s
  rw [Real.norm_eq_abs]
  unfold momKernel
  rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hs0.le _), abs_pow, abs_neg, abs_mul,
    abs_of_pos (exp_pos _)]
  have h := hG (Real.sqrt s) hsq
  calc s ^ (μ - 1) * |log s| ^ ℓ * (|G (Real.sqrt s)| * exp (-s))
      ≤ s ^ (μ - 1) * |log s| ^ ℓ *
        (A * (1 + Real.sqrt s) ^ m * exp (M * Real.sqrt s) * exp (-s)) := by
        gcongr
    _ = _ := by ring

/-! ### The coefficient system -/

/-- The spectrum of the inner kernel: the exponents `(eᵢ+1)/(2kᵢ)` of the state density. -/
noncomputable def innerSpectrum (k e : Fin (n + 1) → ℕ) : Finset ℝ :=
  ((stateDensityRep n (sdWeights k e)).map Prod.fst).toFinset

/-- The spectrum below the cutoff `L`. -/
noncomputable def innerSpectrumBelow (k e : Fin (n + 1) → ℕ) (L : ℝ) : Finset ℝ :=
  (innerSpectrum k e).filter (· < L)

/-- The coefficient system of the inner kernel:
`c μ q = ∏ 1/(2kᵢ) ∑_{j ≤ n} coeffAt(rep) μ j · C(j,q) · mellinMom G μ (j−q)`. -/
noncomputable def empInnerCoeff (k e : Fin (n + 1) → ℕ) (G : ℝ → ℝ) (μ : ℝ) (q : ℕ) : ℝ :=
  (∏ i, 1 / (2 * (k i : ℝ))) * ∑ j ∈ Finset.range (n + 1),
    PowLogRep.coeffAt (stateDensityRep n (sdWeights k e)) μ j * (j.choose q : ℝ) *
      mellinMom G μ (j - q)

theorem mem_innerSpectrum_pos (k e : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {μ : ℝ}
    (hμ : μ ∈ innerSpectrum k e) : 0 < μ := by
  unfold innerSpectrum at hμ
  rw [List.mem_toFinset, List.mem_map] at hμ
  obtain ⟨en, hen, rfl⟩ := hμ
  obtain ⟨i, hi⟩ := stateDensityRep_exponent_mem n (sdWeights k e) en hen
  rw [hi]
  exact sdWeights_add_one_pos k e hk i

theorem coeffAt_eq_zero_of_not_mem (c : PowLogRep) {μ : ℝ} (hμ : μ ∉ (c.map Prod.fst).toFinset)
    (j : ℕ) : PowLogRep.coeffAt c μ j = 0 := by
  unfold PowLogRep.coeffAt
  have : c.filter (fun t => t.1 = μ ∧ t.2.1 = j) = [] := by
    rw [List.filter_eq_nil_iff]
    intro en hen h
    have h' : en.1 = μ ∧ en.2.1 = j := by simpa using h
    apply hμ
    rw [List.mem_toFinset, List.mem_map]
    exact ⟨en, hen, h'.1⟩
  rw [this]
  rfl

/-- Regrouping a power–log list sum by `(exponent, degree)` through `coeffAt`. -/
theorem list_sum_eq_sum_coeffAt (F : ℝ → ℕ → ℝ) (D : ℕ) :
    ∀ l : PowLogRep, (∀ en ∈ l, en.2.1 ≤ D) →
      (l.map fun en => en.2.2 * F en.1 en.2.1).sum =
        ∑ μ ∈ (l.map Prod.fst).toFinset, ∑ j ∈ Finset.range (D + 1),
          PowLogRep.coeffAt l μ j * F μ j := by
  intro l
  induction l with
  | nil => intro _; simp [PowLogRep.coeffAt_nil]
  | cons en l ih =>
    intro hD
    have hen : en.2.1 ≤ D := hD en List.mem_cons_self
    have hl : ∀ en' ∈ l, en'.2.1 ≤ D := fun en' hen' => hD en' (List.mem_cons_of_mem _ hen')
    rw [List.map_cons, List.sum_cons, ih hl, List.map_cons, List.toFinset_cons]
    simp only [PowLogRep.coeffAt_cons, add_mul, Finset.sum_add_distrib]
    -- the `ite` part
    have hA : ∑ μ ∈ insert en.1 (l.map Prod.fst).toFinset, ∑ j ∈ Finset.range (D + 1),
        (if en.1 = μ ∧ en.2.1 = j then en.2.2 else 0) * F μ j = en.2.2 * F en.1 en.2.1 := by
      have hinner : ∀ μ, ∑ j ∈ Finset.range (D + 1),
          (if en.1 = μ ∧ en.2.1 = j then en.2.2 else 0) * F μ j =
          if en.1 = μ then en.2.2 * F μ en.2.1 else 0 := by
        intro μ
        by_cases hμ : en.1 = μ
        · simp only [hμ, true_and, if_true]
          rw [Finset.sum_eq_single en.2.1]
          · simp
          · intro j _ hj
            rw [if_neg (Ne.symm hj), zero_mul]
          · intro h
            exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le hen)) h
        · simp only [hμ, false_and, if_false, zero_mul, Finset.sum_const_zero]
      simp_rw [hinner]
      rw [Finset.sum_ite_eq]
      simp
    -- the tail part
    have hB : ∑ μ ∈ insert en.1 (l.map Prod.fst).toFinset, ∑ j ∈ Finset.range (D + 1),
        PowLogRep.coeffAt l μ j * F μ j =
        ∑ μ ∈ (l.map Prod.fst).toFinset, ∑ j ∈ Finset.range (D + 1),
          PowLogRep.coeffAt l μ j * F μ j := by
      by_cases hmem : en.1 ∈ (l.map Prod.fst).toFinset
      · rw [Finset.insert_eq_of_mem hmem]
      · rw [Finset.sum_insert hmem]
        have : ∑ j ∈ Finset.range (D + 1), PowLogRep.coeffAt l en.1 j * F en.1 j = 0 :=
          Finset.sum_eq_zero fun j _ => by rw [coeffAt_eq_zero_of_not_mem l hmem j, zero_mul]
        rw [this, zero_add]
    rw [hA, hB]

/-- The exact series is the power–log system on the full spectrum. -/
theorem empInnerSeries_eq_powLog (k e : Fin (n + 1) → ℕ) (G : ℝ → ℝ) (t : ℝ) :
    empInnerSeries k e G t = powLog (innerSpectrum k e) n (empInnerCoeff k e G) t := by
  unfold empInnerSeries innerSpectrum powLog empInnerCoeff
  have hD : ∀ en ∈ stateDensityRep n (sdWeights k e), en.2.1 ≤ n :=
    fun en hen => stateDensityRep_degree_le k e hen
  have h := list_sum_eq_sum_coeffAt
    (fun μ j => t ^ (-μ) * ∑ q ∈ Finset.range (j + 1),
      (j.choose q : ℝ) * log t ^ q * mellinMom G μ (j - q)) n (stateDensityRep n (sdWeights k e)) hD
  have hterm : ((stateDensityRep n (sdWeights k e)).map (innerTerm G t)) =
      (stateDensityRep n (sdWeights k e)).map fun en => en.2.2 *
      (t ^ (-en.1) * ∑ q ∈ Finset.range (en.2.1 + 1),
        (en.2.1.choose q : ℝ) * log t ^ q * mellinMom G en.1 (en.2.1 - q)) := rfl
  rw [hterm, h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  -- extend every inner `q`-sum to `range (n+1)` (the extra binomial coefficients vanish)
  have hext : ∀ j ∈ Finset.range (n + 1),
      ∑ q ∈ Finset.range (j + 1), (j.choose q : ℝ) * log t ^ q * mellinMom G μ (j - q) =
      ∑ q ∈ Finset.range (n + 1), (j.choose q : ℝ) * log t ^ q * mellinMom G μ (j - q) := by
    intro j hj
    have hjn : j + 1 ≤ n + 1 := Finset.mem_range.1 hj
    refine Finset.sum_subset (Finset.range_subset_range.2 hjn) fun q _ hq => ?_
    have hjq : j < q := by
      have := Finset.mem_range.not.1 hq
      omega
    rw [Nat.choose_eq_zero_of_lt hjq]
    simp
  rw [Finset.sum_congr rfl fun j hj => by rw [hext j hj]]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-! ### Measurability in the sample size -/

theorem measurable_empUnitInner (k e : Fin (n + 1) → ℕ) {G : ℝ → ℝ} (hG : Measurable G) :
    Measurable (empUnitInner k e G) := by
  have hm : Measurable (Function.uncurry fun (t : ℝ) (u : Fin (n + 1) → ℝ) =>
      (∏ i, u i ^ e i) * (G (Real.sqrt t * ∏ i, u i ^ k i) * exp (-t * ∏ i, u i ^ (2 * k i)))) := by
    change Measurable fun p : ℝ × (Fin (n + 1) → ℝ) =>
      (∏ i, p.2 i ^ e i) *
        (G (Real.sqrt p.1 * ∏ i, p.2 i ^ k i) * exp (-p.1 * ∏ i, p.2 i ^ (2 * k i)))
    fun_prop
  exact (hm.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (unitBox (n + 1)))).measurable

/-! ### Bounds on the coefficients -/

/-- The coefficient envelope `∏ 1/(2kᵢ) ∑_j |coeffAt μ j| C(j,q) momBound m M μ (j−q)`. -/
noncomputable def innerCoeffBound (k e : Fin (n + 1) → ℕ) (m : ℕ) (M μ : ℝ) (q : ℕ) : ℝ :=
  (∏ i, 1 / (2 * (k i : ℝ))) * ∑ j ∈ Finset.range (n + 1),
    |PowLogRep.coeffAt (stateDensityRep n (sdWeights k e)) μ j| * (j.choose q : ℝ) *
      momBound m M μ (j - q)

theorem innerCoeffBound_nonneg (k e : Fin (n + 1) → ℕ) (m : ℕ) (M μ : ℝ) (q : ℕ) :
    0 ≤ innerCoeffBound k e m M μ q := by
  unfold innerCoeffBound
  refine mul_nonneg (Finset.prod_nonneg fun i _ => by positivity) (Finset.sum_nonneg fun j _ => ?_)
  have := momBound_nonneg m M μ (j - q)
  positivity

theorem abs_empInnerCoeff_le (k e : Fin (n + 1) → ℕ) {G : ℝ → ℝ} {A : ℝ} {m : ℕ} {M : ℝ}
    (hG : GrowthLE G A m M) {μ : ℝ} (hμ : 0 < μ) (q : ℕ) :
    |empInnerCoeff k e G μ q| ≤ A * innerCoeffBound k e m M μ q := by
  unfold empInnerCoeff innerCoeffBound
  rw [abs_mul, abs_of_nonneg (Finset.prod_nonneg fun i _ => by positivity), mul_left_comm,
    Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun j _ => ?_)) (Finset.prod_nonneg fun i _ => by positivity)
  rw [abs_mul, abs_mul, Nat.abs_cast]
  calc |PowLogRep.coeffAt (stateDensityRep n (sdWeights k e)) μ j| * (j.choose q : ℝ) *
        |mellinMom G μ (j - q)|
      ≤ |PowLogRep.coeffAt (stateDensityRep n (sdWeights k e)) μ j| * (j.choose q : ℝ) *
        (A * momBound m M μ (j - q)) := by
        gcongr
        exact abs_mellinMom_le hG hμ (j - q)
    _ = _ := by ring

/-- The total coefficient envelope over the spectrum and all degrees. -/
noncomputable def innerCoeffTotal (k e : Fin (n + 1) → ℕ) (m : ℕ) (M : ℝ) : ℝ :=
  ∑ μ ∈ innerSpectrum k e, ∑ q ∈ Finset.range (n + 1), innerCoeffBound k e m M μ q

theorem innerCoeffTotal_nonneg (k e : Fin (n + 1) → ℕ) (m : ℕ) (M : ℝ) :
    0 ≤ innerCoeffTotal k e m M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => innerCoeffBound_nonneg _ _ _ _ _ _

/-! ### The global two-regime estimate -/

/-- The unit-box monomial integral `∫_{(0,1]^{n+1}} u^e du = ∏ 1/(eᵢ+1)`. -/
theorem integral_unitBox_prod_pow (e : Fin (n + 1) → ℕ) :
    ∫ u in unitBox (n + 1), ∏ i, u i ^ e i = ∏ i, (1 : ℝ) / (e i + 1) := by
  have := integral_box_mono (ι := Fin (n + 1)) e (b := 1) zero_le_one
  simp only [one_pow] at this
  exact this

/-- The small-regime bound on the kernel: for `0 < t ≤ 1`, `|I_G(t)| ≤ A 2^m e^{|M|} ∏ 1/(eᵢ+1)`. -/
theorem abs_empUnitInner_le_of_le_one (k e : Fin (n + 1) → ℕ) {G : ℝ → ℝ} {A : ℝ} {m : ℕ}
    {M : ℝ} (hG : GrowthLE G A m M) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |empUnitInner k e G t| ≤ A * 2 ^ m * exp |M| * ∏ i, (1 : ℝ) / (e i + 1) := by
  have hA := hG.nonneg
  set B : ℝ := A * 2 ^ m * exp |M| with hB
  have hB0 : 0 ≤ B := by positivity
  have hg : IntegrableOn (fun u : Fin (n + 1) → ℝ => B * ∏ i, u i ^ e i) (unitBox (n + 1)) := by
    have : Continuous fun u : Fin (n + 1) → ℝ => B * ∏ i, u i ^ e i := by fun_prop
    exact (this.continuousOn.integrableOn_compact
      (isCompact_univ_pi fun _ => isCompact_Icc)).mono_set
      (Set.pi_mono fun _ _ => Ioc_subset_Icc_self)
  unfold empUnitInner
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le hg ?_).trans ?_
  · refine (ae_restrict_iff' (measurableSet_unitBox _)).2 (Eventually.of_forall fun u hu => ?_)
    have hu0 : ∀ i, 0 ≤ u i := fun i => (hu i (Set.mem_univ i)).1.le
    have hpe : 0 ≤ ∏ i, u i ^ e i := Finset.prod_nonneg fun i _ => pow_nonneg (hu0 i) _
    have hpk : ∏ i, u i ^ k i ≤ 1 := prod_pow_le_one_of_mem_unitBox k hu
    have hpk0 : 0 ≤ ∏ i, u i ^ k i := Finset.prod_nonneg fun i _ => pow_nonneg (hu0 i) _
    have hτ : Real.sqrt t * ∏ i, u i ^ k i ≤ 1 :=
      (mul_le_mul (Real.sqrt_le_one.2 ht1) hpk hpk0 zero_le_one).trans_eq (one_mul 1)
    have hτ0 : 0 ≤ Real.sqrt t * ∏ i, u i ^ k i := mul_nonneg (Real.sqrt_nonneg _) hpk0
    have hGb := hG.bound_on zero_le_one hτ0 hτ
    have hexp : exp (-t * ∏ i, u i ^ (2 * k i)) ≤ 1 := by
      rw [exp_le_one_iff]
      have : 0 ≤ ∏ i, u i ^ (2 * k i) := Finset.prod_nonneg fun i _ => pow_nonneg (hu0 i) _
      nlinarith
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hpe, abs_mul, abs_of_pos (exp_pos _)]
    calc (∏ i, u i ^ e i) * (|G (Real.sqrt t * ∏ i, u i ^ k i)| * exp (-t * ∏ i, u i ^ (2 * k i)))
        ≤ (∏ i, u i ^ e i) * (A * (1 + 1) ^ m * exp (|M| * 1) * 1) := by gcongr
      _ = B * ∏ i, u i ^ e i := by rw [hB]; norm_num; ring
  · rw [MeasureTheory.integral_const_mul, integral_unitBox_prod_pow]

/-- The tail constant of the exact series, `∏ 1/(2kᵢ) ∑_{entries} innerTailConst`. -/
noncomputable def innerTailTotal (k e : Fin (n + 1) → ℕ) (m : ℕ) (M : ℝ) : ℝ :=
  (∏ i, 1 / (2 * (k i : ℝ))) * ((stateDensityRep n (sdWeights k e)).map (innerTailConst m M)).sum

theorem innerTailTotal_nonneg (k e : Fin (n + 1) → ℕ) (m : ℕ) (M : ℝ) :
    0 ≤ innerTailTotal k e m M :=
  mul_nonneg (Finset.prod_nonneg fun i _ => by positivity)
    (List.sum_nonneg fun x hx => by
      obtain ⟨en, _, rfl⟩ := List.mem_map.1 hx
      exact innerTailConst_nonneg m M en)

/-- The small-regime constant `2^m e^{|M|} ∏ 1/(eᵢ+1)`. -/
noncomputable def innerSmallConst (e : Fin (n + 1) → ℕ) (m : ℕ) (M : ℝ) : ℝ :=
  2 ^ m * exp |M| * ∏ i, (1 : ℝ) / (e i + 1)

theorem innerSmallConst_nonneg (e : Fin (n + 1) → ℕ) (m : ℕ) (M : ℝ) :
    0 ≤ innerSmallConst e m M := by
  unfold innerSmallConst; positivity

/-- `e^{−t/2} ≤ E · t^{−L}` for `t ≥ 1`, with `E = max(1, ⌈L⌉!) 2^{⌈L⌉}`. -/
theorem exists_exp_neg_half_le_rpow (L : ℝ) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ t : ℝ, 1 ≤ t → exp (-t / 2) ≤ E * t ^ (-L) := by
  set L' : ℕ := ⌈L⌉₊ with hL'
  refine ⟨max 1 (L'.factorial : ℝ) * 2 ^ L', by positivity, fun t ht1 => ?_⟩
  have ht : 0 < t := by linarith
  have h := pow_mul_exp_neg_le L' (by linarith : 0 < t / 2)
  have htL' : t ^ (-(L' : ℝ)) ≤ t ^ (-L) :=
    Real.rpow_le_rpow_of_exponent_le ht1 (by linarith [Nat.le_ceil L])
  have hpos' : 0 < t ^ L' := pow_pos ht _
  have h2 : (0 : ℝ) < 2 ^ L' := by positivity
  have hkey : exp (-t / 2) ≤ max 1 (L'.factorial : ℝ) * 2 ^ L' * t ^ (-(L' : ℝ)) := by
    rw [Real.rpow_neg ht.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hpos']
    rw [div_pow] at h
    calc exp (-t / 2) * t ^ L' = (t ^ L' / 2 ^ L' * exp (-(t / 2))) * 2 ^ L' := by
          rw [neg_div]; field_simp
      _ ≤ max 1 (L'.factorial : ℝ) * 2 ^ L' := by gcongr
  exact hkey.trans (mul_le_mul_of_nonneg_left htL' (by positivity))

/-- The dropped part of the spectrum (exponents `μ ≥ L`) is `O(A · t^{−L} (1+|log t|)^n)` for
`t ≥ 1`. -/
theorem abs_powLog_drop_le (k e : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {G : ℝ → ℝ} {A : ℝ}
    {m : ℕ} {M : ℝ} (hG : GrowthLE G A m M) (L : ℝ) {t : ℝ} (ht1 : 1 ≤ t) :
    |powLog (innerSpectrum k e) n (empInnerCoeff k e G) t -
        powLog (innerSpectrumBelow k e L) n (empInnerCoeff k e G) t| ≤
      A * innerCoeffTotal k e m M * (t ^ (-L) * (1 + |log t|) ^ n) := by
  have ht : 0 < t := by linarith
  have hA := hG.nonneg
  unfold powLog innerSpectrumBelow
  have hsplit : ∑ μ ∈ innerSpectrum k e, ∑ j ∈ Finset.range (n + 1),
      empInnerCoeff k e G μ j * t ^ (-μ) * log t ^ j =
      ∑ μ ∈ (innerSpectrum k e).filter (· < L), ∑ j ∈ Finset.range (n + 1),
        empInnerCoeff k e G μ j * t ^ (-μ) * log t ^ j +
      ∑ μ ∈ (innerSpectrum k e).filter (fun μ => ¬ μ < L), ∑ j ∈ Finset.range (n + 1),
        empInnerCoeff k e G μ j * t ^ (-μ) * log t ^ j :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  rw [hsplit, add_sub_cancel_left]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hsub : ∀ μ ∈ (innerSpectrum k e).filter (fun μ => ¬ μ < L),
      |∑ j ∈ Finset.range (n + 1), empInnerCoeff k e G μ j * t ^ (-μ) * log t ^ j| ≤
        A * (∑ q ∈ Finset.range (n + 1), innerCoeffBound k e m M μ q) *
          (t ^ (-L) * (1 + |log t|) ^ n) := by
    intro μ hμ
    rw [Finset.mem_filter, not_lt] at hμ
    have hμ0 : 0 < μ := mem_innerSpectrum_pos k e hk hμ.1
    have htμ : t ^ (-μ) ≤ t ^ (-L) :=
      Real.rpow_le_rpow_of_exponent_le ht1 (by linarith [hμ.2])
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun j hj => ?_
    have hjn : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have hb0 := innerCoeffBound_nonneg k e m M μ j
    rw [abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht _), abs_pow]
    calc |empInnerCoeff k e G μ j| * t ^ (-μ) * |log t| ^ j
        ≤ (A * innerCoeffBound k e m M μ j) * t ^ (-L) * (1 + |log t|) ^ n :=
          mul_le_mul (mul_le_mul (abs_empInnerCoeff_le k e hG hμ0 j) htμ
            (Real.rpow_nonneg ht.le _) (by positivity))
            (abs_log_pow_le_one_add_pow hjn t) (by positivity) (by positivity)
      _ = _ := by ring
  refine (Finset.sum_le_sum hsub).trans ?_
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hA) (by positivity)
  unfold innerCoeffTotal
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    fun μ _ _ => Finset.sum_nonneg fun q _ => innerCoeffBound_nonneg _ _ _ _ _ _

/-- For `0 < t < 1` the truncated power–log system is `O(A · t^{−L} (1+|log t|)^n)`. -/
theorem abs_powLog_below_le_small (k e : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {G : ℝ → ℝ}
    {A : ℝ} {m : ℕ} {M : ℝ} (hG : GrowthLE G A m M) (L : ℝ) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    |powLog (innerSpectrumBelow k e L) n (empInnerCoeff k e G) t| ≤
      A * (2 * innerCoeffTotal k e m M) * (t ^ (-L) * (1 + |log t|) ^ n) := by
  have hA := hG.nonneg
  unfold powLog
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ μ ∈ innerSpectrumBelow k e L,
      |∑ j ∈ Finset.range (n + 1), empInnerCoeff k e G μ j * t ^ (-μ) * log t ^ j| ≤
        A * (2 * ∑ q ∈ Finset.range (n + 1), innerCoeffBound k e m M μ q) *
          (t ^ (-L) * (1 + |log t|) ^ n) := by
    intro μ hμ
    have hμ' := Finset.mem_filter.1 hμ
    have hμ0 : 0 < μ := mem_innerSpectrum_pos k e hk hμ'.1
    have hsmall : t ^ (-μ) ≤ (1 + (1 : ℝ) ^ (-L)) * t ^ (-L) :=
      rpow_neg_le_small hμ0.le hμ'.2 one_pos ht (by linarith)
    rw [Real.one_rpow] at hsmall
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun j hj => ?_
    have hjn : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have hb0 := innerCoeffBound_nonneg k e m M μ j
    rw [abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht _), abs_pow]
    calc |empInnerCoeff k e G μ j| * t ^ (-μ) * |log t| ^ j
        ≤ (A * innerCoeffBound k e m M μ j) * ((1 + 1) * t ^ (-L)) * (1 + |log t|) ^ n :=
          mul_le_mul (mul_le_mul (abs_empInnerCoeff_le k e hG hμ0 j) hsmall
            (Real.rpow_nonneg ht.le _) (by positivity))
            (abs_log_pow_le_one_add_pow hjn t) (by positivity) (by positivity)
      _ = _ := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left ?_ zero_le_two) hA) (by positivity)
  unfold innerCoeffTotal innerSpectrumBelow
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    fun μ _ _ => Finset.sum_nonneg fun q _ => innerCoeffBound_nonneg _ _ _ _ _ _

/-- ★★ **The global two-regime estimate of the empirical inner kernel**: for every cutoff `L > 0`
there is `C = C(k, e, m, M, L)` such that for every growth-`(A, m, M)` field factor `G` and every
`t > 0`,
`|I_G(t) − powLog (innerSpectrumBelow k e L) n (empInnerCoeff k e G) t|
  ≤ A · C · t^{−L} (1+|log t|)^n`.
This is the inner input of the generic face theorem, linear in the growth constant. -/
theorem empUnitInner_two_regime (k e : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (m : ℕ) (M : ℝ)
    {L : ℝ} (hL : 0 < L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (G : ℝ → ℝ), Measurable G → ∀ (A : ℝ), GrowthLE G A m M →
      ∀ t : ℝ, 0 < t →
        |empUnitInner k e G t - powLog (innerSpectrumBelow k e L) n (empInnerCoeff k e G) t| ≤
          A * C * (t ^ (-L) * (1 + |log t|) ^ n) := by
  obtain ⟨E, hE0, hE⟩ := exists_exp_neg_half_le_rpow L
  have hQ0 := innerTailTotal_nonneg k e m M
  have hT0 := innerCoeffTotal_nonneg k e m M
  have hS0 := innerSmallConst_nonneg e m M
  have hQE : 0 ≤ innerTailTotal k e m M * E := mul_nonneg hQ0 hE0
  refine ⟨innerTailTotal k e m M * E + innerCoeffTotal k e m M +
    (innerSmallConst e m M + 2 * innerCoeffTotal k e m M), by linarith,
    fun G hGm A hG t ht => ?_⟩
  have hA := hG.nonneg
  have htL : 0 < t ^ (-L) := Real.rpow_pos_of_pos ht _
  have hlog1 : (1 : ℝ) ≤ (1 + |log t|) ^ n := one_le_pow₀ (by linarith [abs_nonneg (log t)])
  have hw : 0 ≤ t ^ (-L) * (1 + |log t|) ^ n := by positivity
  rcases le_or_gt 1 t with ht1 | ht1
  · -- large regime
    have hlog0 : 0 ≤ log t := Real.log_nonneg ht1
    have h1 : |empUnitInner k e G t - powLog (innerSpectrum k e) n (empInnerCoeff k e G) t| ≤
        A * innerTailTotal k e m M * ((1 + log t) ^ n * exp (-t / 2)) := by
      have := abs_empUnitInner_sub_series_le k e hk hGm hG ht1
      rwa [empInnerSeries_eq_powLog] at this
    have hdrop := abs_powLog_drop_le k e hk hG L ht1
    have hlogeq : |log t| = log t := abs_of_nonneg hlog0
    calc |empUnitInner k e G t - powLog (innerSpectrumBelow k e L) n (empInnerCoeff k e G) t|
        ≤ |empUnitInner k e G t - powLog (innerSpectrum k e) n (empInnerCoeff k e G) t| +
          |powLog (innerSpectrum k e) n (empInnerCoeff k e G) t -
            powLog (innerSpectrumBelow k e L) n (empInnerCoeff k e G) t| :=
          abs_sub_le _ _ _
      _ ≤ A * innerTailTotal k e m M * ((1 + log t) ^ n * exp (-t / 2)) +
          A * innerCoeffTotal k e m M * (t ^ (-L) * (1 + |log t|) ^ n) := add_le_add h1 hdrop
      _ ≤ A * innerTailTotal k e m M * ((1 + |log t|) ^ n * (E * t ^ (-L))) +
          A * innerCoeffTotal k e m M * (t ^ (-L) * (1 + |log t|) ^ n) := by
          rw [hlogeq]
          gcongr
          exact hE t ht1
      _ = A * (innerTailTotal k e m M * E + innerCoeffTotal k e m M) *
          (t ^ (-L) * (1 + |log t|) ^ n) := by ring
      _ ≤ A * (innerTailTotal k e m M * E + innerCoeffTotal k e m M +
          (innerSmallConst e m M + 2 * innerCoeffTotal k e m M)) *
          (t ^ (-L) * (1 + |log t|) ^ n) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hA) hw
  · -- small regime `t < 1`
    have htL1 : 1 ≤ t ^ (-L) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht ht1.le (by linarith)
    have h1 : |empUnitInner k e G t| ≤
        A * innerSmallConst e m M * (t ^ (-L) * (1 + |log t|) ^ n) := by
      refine (abs_empUnitInner_le_of_le_one k e hG ht.le ht1.le).trans ?_
      have hone : (1 : ℝ) ≤ t ^ (-L) * (1 + |log t|) ^ n :=
        (mul_one 1).symm.le.trans (mul_le_mul htL1 hlog1 zero_le_one htL.le)
      unfold innerSmallConst
      calc A * 2 ^ m * exp |M| * ∏ i, (1 : ℝ) / (e i + 1)
          = A * (2 ^ m * exp |M| * ∏ i, (1 : ℝ) / (e i + 1)) * 1 := by ring
        _ ≤ A * (2 ^ m * exp |M| * ∏ i, (1 : ℝ) / (e i + 1)) *
            (t ^ (-L) * (1 + |log t|) ^ n) := by gcongr
    have h2 := abs_powLog_below_le_small k e hk hG L ht ht1
    calc |empUnitInner k e G t - powLog (innerSpectrumBelow k e L) n (empInnerCoeff k e G) t|
        ≤ |empUnitInner k e G t| +
          |powLog (innerSpectrumBelow k e L) n (empInnerCoeff k e G) t| := abs_sub _ _
      _ ≤ A * innerSmallConst e m M * (t ^ (-L) * (1 + |log t|) ^ n) +
          A * (2 * innerCoeffTotal k e m M) * (t ^ (-L) * (1 + |log t|) ^ n) := add_le_add h1 h2
      _ = A * (innerSmallConst e m M + 2 * innerCoeffTotal k e m M) *
          (t ^ (-L) * (1 + |log t|) ^ n) := by ring
      _ ≤ A * (innerTailTotal k e m M * E + innerCoeffTotal k e m M +
          (innerSmallConst e m M + 2 * innerCoeffTotal k e m M)) *
          (t ^ (-L) * (1 + |log t|) ^ n) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hA) hw

end SmoothEngine

end Grammar
