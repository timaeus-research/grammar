/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Integrability of power–log weights on a box (consult #116 §1.3)

The remainders of the facewise smooth engine are bounded by
`∏ᵢ wᵢ^{cᵢ} · (1 + |∑ᵢ aᵢ log wᵢ|)^D` on `(0,b]^ι` with every `cᵢ > −1`. We prove once that such
weights are integrable (★ `integrableOn_prod_rpow_mul_log_pow`). The proof is elementary: for
`0 < ε` and every `t > 0`, `|log t| ≤ (t^{−ε} + t^{ε})/ε` (`abs_log_le_rpow_add`), so the
logarithmic factor is dominated by a sum of two powers; `1 + ∑ xᵢ ≤ ∏ (1 + xᵢ)` for `xᵢ ≥ 0`
(`one_add_sum_le_prod_one_add`) separates the coordinates, and Mathlib's
`Integrable.fintype_prod` finishes on the product measure. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

namespace SmoothEngine

/-! ### The one-variable logarithm bound -/

/-- `|log t| ≤ (t^{−ε} + t^{ε})/ε` for every `t > 0` and `ε > 0`. -/
theorem abs_log_le_rpow_add {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t) :
    |log t| ≤ (t ^ (-ε) + t ^ ε) / ε := by
  have h0 : 0 ≤ t ^ (-ε) := rpow_nonneg ht.le _
  have h1 : 0 ≤ t ^ ε := rpow_nonneg ht.le _
  rcases le_or_gt t 1 with hle | hgt
  · have key := Real.abs_log_mul_self_rpow_lt t ε ht hle hε
    rw [abs_mul, abs_of_pos (rpow_pos_of_pos ht ε)] at key
    have hpos : 0 < t ^ ε := rpow_pos_of_pos ht ε
    have : |log t| ≤ t ^ (-ε) / ε := by
      rw [rpow_neg ht.le, div_eq_mul_inv, ← mul_inv, ← one_div, le_div_iff₀ (by positivity),
        ← mul_assoc]
      exact ((lt_div_iff₀ hε).1 key).le
    calc |log t| ≤ t ^ (-ε) / ε := this
      _ ≤ (t ^ (-ε) + t ^ ε) / ε := by gcongr; linarith
  · have hlog : 0 ≤ log t := log_nonneg hgt.le
    rw [abs_of_nonneg hlog]
    have key := log_le_sub_one_of_pos (rpow_pos_of_pos ht ε)
    rw [log_rpow ht] at key
    have : log t ≤ t ^ ε / ε := by
      rw [le_div_iff₀ hε]; linarith
    calc log t ≤ t ^ ε / ε := this
      _ ≤ (t ^ (-ε) + t ^ ε) / ε := by gcongr; linarith

/-- `1 ≤ t^{−ε} + t^{ε}` for `t > 0`, `ε ≥ 0`. -/
theorem one_le_rpow_neg_add_rpow {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 < t) :
    1 ≤ t ^ (-ε) + t ^ ε := by
  rcases le_or_gt t 1 with hle | hgt
  · have := one_le_rpow_of_pos_of_le_one_of_nonpos ht hle (neg_nonpos.2 hε)
    linarith [rpow_nonneg ht.le ε]
  · have := one_le_rpow hgt.le hε
    linarith [rpow_nonneg ht.le (-ε)]

/-- `1 + |a| |log t| ≤ (1 + |a|/ε)(t^{−ε} + t^{ε})`. -/
theorem one_add_abs_log_le {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t) (a : ℝ) :
    1 + |a| * |log t| ≤ (1 + |a| / ε) * (t ^ (-ε) + t ^ ε) := by
  have h1 := one_le_rpow_neg_add_rpow hε.le ht
  have h2 := abs_log_le_rpow_add hε ht
  have h3 : |a| * |log t| ≤ |a| * ((t ^ (-ε) + t ^ ε) / ε) :=
    mul_le_mul_of_nonneg_left h2 (abs_nonneg a)
  have h4 : |a| * ((t ^ (-ε) + t ^ ε) / ε) = |a| / ε * (t ^ (-ε) + t ^ ε) := by ring
  nlinarith [abs_nonneg a, div_nonneg (abs_nonneg a) hε.le]

/-- `(x + y)^D ≤ 2^D (x^D + y^D)` for `x, y ≥ 0`. -/
theorem add_pow_le_two_pow_mul {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (D : ℕ) :
    (x + y) ^ D ≤ 2 ^ D * (x ^ D + y ^ D) := by
  have hmax : x + y ≤ 2 * max x y := by
    rcases le_total x y with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  calc (x + y) ^ D ≤ (2 * max x y) ^ D := by
        gcongr
      _ = 2 ^ D * max x y ^ D := mul_pow _ _ _
      _ ≤ 2 ^ D * (x ^ D + y ^ D) := by
        gcongr
        rcases le_total x y with h | h
        · rw [max_eq_right h]; linarith [pow_nonneg hx D]
        · rw [max_eq_left h]; linarith [pow_nonneg hy D]

/-! ### One-variable integrability -/

/-- `t^c` is integrable on `(0,b]` for `c > −1`. -/
theorem integrableOn_rpow_Ioc {c : ℝ} (hc : -1 < c) {b : ℝ} (hb : 0 ≤ b) :
    IntegrableOn (fun t : ℝ => t ^ c) (Ioc 0 b) :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hb).1
    (intervalIntegral.intervalIntegrable_rpow' hc)

/-- The majorant `(2(1 + |a|/ε))^D (t^{c−εD} + t^{c+εD})` of `t^c (1 + |a||log t|)^D`. -/
noncomputable def logMajorant (a c ε : ℝ) (D : ℕ) (t : ℝ) : ℝ :=
  (2 * (1 + |a| / ε)) ^ D * (t ^ (c - ε * D) + t ^ (c + ε * D))

theorem integrableOn_logMajorant {a c ε : ℝ} (D : ℕ) (hlo : -1 < c - ε * D)
    (hhi : -1 < c + ε * D) {b : ℝ} (hb : 0 ≤ b) :
    IntegrableOn (logMajorant a c ε D) (Ioc 0 b) := by
  unfold logMajorant
  exact ((integrableOn_rpow_Ioc hlo hb).add (integrableOn_rpow_Ioc hhi hb)).const_mul _

/-- The pointwise domination `t^c (1 + |a||log t|)^D ≤ logMajorant a c ε D t` for `t > 0`. -/
theorem rpow_mul_one_add_abs_log_pow_le {a c ε t : ℝ} (hε : 0 < ε) (ht : 0 < t) (D : ℕ) :
    t ^ c * (1 + |a| * |log t|) ^ D ≤ logMajorant a c ε D t := by
  have hK : 0 ≤ 1 + |a| / ε := by positivity
  have h0 : 0 ≤ t ^ (-ε) := rpow_nonneg ht.le _
  have h1 : 0 ≤ t ^ ε := rpow_nonneg ht.le _
  have hbase : 1 + |a| * |log t| ≤ (1 + |a| / ε) * (t ^ (-ε) + t ^ ε) :=
    one_add_abs_log_le hε ht a
  have hpow : (1 + |a| * |log t|) ^ D ≤ ((1 + |a| / ε) * (t ^ (-ε) + t ^ ε)) ^ D :=
    pow_le_pow_left₀ (by positivity) hbase D
  have hsplit : ((1 + |a| / ε) * (t ^ (-ε) + t ^ ε)) ^ D
      ≤ (1 + |a| / ε) ^ D * (2 ^ D * ((t ^ (-ε)) ^ D + (t ^ ε) ^ D)) := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left (add_pow_le_two_pow_mul h0 h1 D) (pow_nonneg hK D)
  have hneg : t ^ c * (t ^ (-ε)) ^ D = t ^ (c - ε * D) := by
    rw [← rpow_natCast, ← rpow_mul ht.le, ← rpow_add ht]; ring_nf
  have hpos : t ^ c * (t ^ ε) ^ D = t ^ (c + ε * D) := by
    rw [← rpow_natCast, ← rpow_mul ht.le, ← rpow_add ht]
  have htc : 0 ≤ t ^ c := rpow_nonneg ht.le c
  calc t ^ c * (1 + |a| * |log t|) ^ D
      ≤ t ^ c * ((1 + |a| / ε) ^ D * (2 ^ D * ((t ^ (-ε)) ^ D + (t ^ ε) ^ D))) :=
        mul_le_mul_of_nonneg_left (hpow.trans hsplit) htc
    _ = (2 * (1 + |a| / ε)) ^ D * (t ^ c * (t ^ (-ε)) ^ D + t ^ c * (t ^ ε) ^ D) := by
        rw [mul_pow]; ring
    _ = logMajorant a c ε D t := by rw [logMajorant, hneg, hpos]

/-- Measurability of the one-variable weight. -/
theorem measurable_rpow_mul_log_pow (a c : ℝ) (D : ℕ) :
    Measurable (fun t : ℝ => t ^ c * (1 + |a| * |log t|) ^ D) := by
  refine (measurable_id.pow_const c).mul ?_
  have habs : Measurable fun t : ℝ => |log t| := by
    simpa only [Real.norm_eq_abs] using measurable_log.norm
  exact (measurable_const.add (measurable_const.mul habs)).pow_const D

/-- ★ `t^c (1 + |a||log t|)^D` is integrable on `(0,b]` for `c > −1`. -/
theorem integrableOn_rpow_mul_log_pow {c : ℝ} (hc : -1 < c) (a : ℝ) (D : ℕ) {b : ℝ}
    (hb : 0 ≤ b) :
    IntegrableOn (fun t : ℝ => t ^ c * (1 + |a| * |log t|) ^ D) (Ioc 0 b) := by
  set ε : ℝ := (c + 1) / (2 * (D + 1)) with hεdef
  have hε : 0 < ε := by rw [hεdef]; exact div_pos (by linarith) (by positivity)
  have hεD : ε * D ≤ (c + 1) / 2 := by
    rw [hεdef, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [(Nat.cast_nonneg D : (0 : ℝ) ≤ D)]
  have hlo : -1 < c - ε * D := by linarith
  have hhi : -1 < c + ε * D := by nlinarith [(Nat.cast_nonneg D : (0 : ℝ) ≤ D)]
  refine Integrable.mono' (integrableOn_logMajorant (a := a) D hlo hhi hb)
    (measurable_rpow_mul_log_pow a c D).aestronglyMeasurable ?_
  refine (ae_restrict_mem measurableSet_Ioc).mono fun t ht => ?_
  have htc : 0 ≤ t ^ c := rpow_nonneg ht.1.le c
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg htc (pow_nonneg (by positivity) D))]
  exact rpow_mul_one_add_abs_log_pow_le hε ht.1 D

/-! ### The product bound -/

/-- `1 + ∑ᵢ xᵢ ≤ ∏ᵢ (1 + xᵢ)` for nonnegative `xᵢ`. -/
theorem one_add_sum_le_prod_one_add {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) : 1 + ∑ i ∈ s, x i ≤ ∏ i ∈ s, (1 + x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    have hxj : 0 ≤ x j := hx j (Finset.mem_insert_self j s)
    have ih' := ih fun i hi => hx i (Finset.mem_insert_of_mem hi)
    have hs : 0 ≤ ∑ i ∈ s, x i := Finset.sum_nonneg fun i hi => hx i (Finset.mem_insert_of_mem hi)
    nlinarith

/-- Measurability of the box weight. -/
theorem measurable_prod_rpow_mul_log_pow {ι : Type*} [Fintype ι] (c a : ι → ℝ) (D : ℕ) :
    Measurable (fun w : ι → ℝ => (∏ i, w i ^ c i) * (1 + |∑ i, a i * log (w i)|) ^ D) := by
  refine (Finset.measurable_prod _ fun i _ => (measurable_pi_apply i).pow_const (c i)).mul ?_
  refine (measurable_const.add ?_).pow_const D
  have hS : Measurable fun w : ι → ℝ => ∑ i, a i * log (w i) :=
    Finset.measurable_sum _ fun i _ =>
      measurable_const.mul (measurable_log.comp (measurable_pi_apply i))
  simpa only [Real.norm_eq_abs] using hS.norm

/-- ★ **Power–log weights are integrable on a box**: for `cᵢ > −1`,
`∏ᵢ wᵢ^{cᵢ} (1 + |∑ᵢ aᵢ log wᵢ|)^D` is integrable on `(0,b]^ι`. -/
theorem integrableOn_prod_rpow_mul_log_pow {ι : Type*} [Fintype ι] {c : ι → ℝ}
    (hc : ∀ i, -1 < c i) (a : ι → ℝ) (D : ℕ) {b : ℝ} (hb : 0 ≤ b) :
    IntegrableOn (fun w : ι → ℝ => (∏ i, w i ^ c i) * (1 + |∑ i, a i * log (w i)|) ^ D)
      (Set.pi univ fun _ => Ioc 0 b) := by
  have hg : ∀ i, Integrable (fun t : ℝ => t ^ c i * (1 + |a i| * |log t|) ^ D)
      (volume.restrict (Ioc 0 b)) := fun i => integrableOn_rpow_mul_log_pow (hc i) (a i) D hb
  have hprod := Integrable.fintype_prod (μ := fun _ : ι => volume.restrict (Ioc 0 b)) hg
  rw [← Measure.restrict_pi_pi, ← volume_pi] at hprod
  refine Integrable.mono' hprod (measurable_prod_rpow_mul_log_pow c a D).aestronglyMeasurable ?_
  refine (ae_restrict_mem (MeasurableSet.univ_pi fun _ => measurableSet_Ioc)).mono fun w hw => ?_
  have hpos : ∀ i, 0 < w i := fun i => (hw i (mem_univ i)).1
  have hlogs : 1 + |∑ i, a i * log (w i)| ≤ ∏ i, (1 + |a i| * |log (w i)|) := by
    refine le_trans ?_ (one_add_sum_le_prod_one_add _ _ fun i _ => by positivity)
    have := Finset.abs_sum_le_sum_abs (fun i => a i * log (w i)) Finset.univ
    simp only [abs_mul] at this
    linarith
  have hprodnn : 0 ≤ ∏ i, w i ^ c i := Finset.prod_nonneg fun i _ => rpow_nonneg (hpos i).le _
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc (∏ i, w i ^ c i) * (1 + |∑ i, a i * log (w i)|) ^ D
      ≤ (∏ i, w i ^ c i) * ∏ i, (1 + |a i| * |log (w i)|) ^ D := by
        rw [Finset.prod_pow]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hlogs D) hprodnn
    _ = ∏ i, w i ^ c i * (1 + |a i| * |log (w i)|) ^ D := by rw [Finset.prod_mul_distrib]

/-- The variant with the logarithmic factor `|S|^j`, `j ≤ D`. -/
theorem integrableOn_prod_rpow_mul_abs_log_pow {ι : Type*} [Fintype ι] {c : ι → ℝ}
    (hc : ∀ i, -1 < c i) (a : ι → ℝ) {j D : ℕ} (hj : j ≤ D) {b : ℝ} (hb : 0 ≤ b) :
    IntegrableOn (fun w : ι → ℝ => (∏ i, w i ^ c i) * |∑ i, a i * log (w i)| ^ j)
      (Set.pi univ fun _ => Ioc 0 b) := by
  refine Integrable.mono' (integrableOn_prod_rpow_mul_log_pow hc a D hb) ?_ ?_
  · refine ((Finset.measurable_prod _ fun i _ => (measurable_pi_apply i).pow_const (c i)).mul
      ?_).aestronglyMeasurable
    have hS : Measurable fun w : ι → ℝ => ∑ i, a i * log (w i) :=
      Finset.measurable_sum _ fun i _ =>
        measurable_const.mul (measurable_log.comp (measurable_pi_apply i))
    have hS' : Measurable fun w : ι → ℝ => |∑ i, a i * log (w i)| := by
      simpa only [Real.norm_eq_abs] using hS.norm
    exact hS'.pow_const j
  refine (ae_restrict_mem (MeasurableSet.univ_pi fun _ => measurableSet_Ioc)).mono fun w hw => ?_
  have hpos : ∀ i, 0 < w i := fun i => (hw i (mem_univ i)).1
  have hprodnn : 0 ≤ ∏ i, w i ^ c i := Finset.prod_nonneg fun i _ => rpow_nonneg (hpos i).le _
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ hprodnn
  calc |∑ i, a i * log (w i)| ^ j ≤ (1 + |∑ i, a i * log (w i)|) ^ j :=
        pow_le_pow_left₀ (abs_nonneg _) (by linarith [abs_nonneg (∑ i, a i * log (w i))]) j
    _ ≤ (1 + |∑ i, a i * log (w i)|) ^ D :=
        pow_le_pow_right₀ (by linarith [abs_nonneg (∑ i, a i * log (w i))]) hj

end SmoothEngine

end Grammar
