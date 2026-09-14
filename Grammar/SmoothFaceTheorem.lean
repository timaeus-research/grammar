/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothLogIntegrable

/-!
# The generic face theorem of the smooth engine (consult #116 §1.3–1.4, second milestone)

An inner function `Z(t)` with a GLOBAL power–log estimate
`|Z(t) − ∑_{μ∈Λ} ∑_{j≤D} c_{μ,j} t^{−μ} (log t)^j| ≤ C t^{−L} (1 + |log t|)^D` for every `t > 0`
is integrated against an outer amplitude `G` on the box `(0,b]^ι` satisfying the product-flat
bound `|G(w)| ≤ M ∏ᵢ wᵢ^{pᵢ}`, with Jacobian exponents `h` and the effective parameter
`t = N ∏ᵢ wᵢ^{aᵢ}`:
`∫ G(w) w^h Z(N w^a) dw = ∑_{μ∈Λ} N^{−μ} ∑_{j≤D} ∑_{q≤j} c_{μ,j} C(j,q) (log N)^q`
`  · ∫ G(w) w^h (w^a)^{−μ} S(w)^{j−q} dw + Rem`,
`|Rem| ≤ C M (1 + log N)^D N^{−L} ∫ ∏ᵢ wᵢ^{pᵢ+hᵢ−aᵢL} (1 + |S(w)|)^D dw`, `S(w) = ∑ᵢ aᵢ log wᵢ`,
under the convergence condition `aᵢ L < pᵢ + hᵢ + 1` (★★ `face_expansion`). The logarithmic degree
is preserved (`(log N + S)^j = ∑_q C(j,q)(log N)^q S^{j−q}`), the remainder is bounded on the
WHOLE box (`1 + |log(N w^a)| ≤ (1 + log N)(1 + |S(w)|)` for `N ≥ 1`), and all the coefficient
integrals converge by `SmoothLogIntegrable`. This is the analytic heart of the facewise engine:
the inner `Z` will be a face Mellin integral `Z^J_m` and `G` a coordinate Taylor remainder of the
smooth amplitude in the complementary coordinates. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Finset

namespace Grammar

namespace SmoothEngine

/-! ### The box, monomials and the logarithmic sum -/

/-- The half-open box `(0,b]^ι`. -/
def box (ι : Type*) (b : ℝ) : Set (ι → ℝ) := Set.pi univ fun _ => Ioc 0 b

theorem measurableSet_box {ι : Type*} [Countable ι] (b : ℝ) : MeasurableSet (box ι b) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioc

theorem pos_of_mem_box {ι : Type*} {b : ℝ} {w : ι → ℝ} (hw : w ∈ box ι b) (i : ι) : 0 < w i :=
  (hw i (mem_univ i)).1

theorem const_mem_box {ι : Type*} {b : ℝ} (hb : 0 < b) : (fun _ : ι => b) ∈ box ι b :=
  fun _ _ => ⟨hb, le_rfl⟩

variable {ι : Type*} [Fintype ι]

/-- The monomial `∏ᵢ wᵢ^{aᵢ}`. -/
def mono (a : ι → ℕ) (w : ι → ℝ) : ℝ := ∏ i, w i ^ a i

/-- The logarithmic sum `S(w) = ∑ᵢ aᵢ log wᵢ`. -/
noncomputable def logSum (a : ι → ℕ) (w : ι → ℝ) : ℝ := ∑ i, (a i : ℝ) * log (w i)

theorem mono_pos (a : ι → ℕ) {w : ι → ℝ} (hw : ∀ i, 0 < w i) : 0 < mono a w :=
  Finset.prod_pos fun i _ => pow_pos (hw i) _

theorem log_mono (a : ι → ℕ) {w : ι → ℝ} (hw : ∀ i, 0 < w i) : log (mono a w) = logSum a w := by
  unfold mono logSum
  rw [Real.log_prod fun i _ => pow_ne_zero _ (hw i).ne']
  simp only [Real.log_pow]

theorem measurable_mono (a : ι → ℕ) : Measurable (mono a) :=
  Finset.measurable_prod _ fun i _ => (measurable_pi_apply i).pow_const _

theorem measurable_logSum (a : ι → ℕ) : Measurable (logSum a) :=
  Finset.measurable_sum _ fun i _ =>
    measurable_const.mul (measurable_log.comp (measurable_pi_apply i))

/-- `w^p w^h (w^a)^{−μ} = ∏ᵢ wᵢ^{pᵢ+hᵢ−aᵢμ}` on positive `w`. -/
theorem mono_mul_mono_mul_rpow (p h a : ι → ℕ) (μ : ℝ) {w : ι → ℝ} (hw : ∀ i, 0 < w i) :
    mono p w * mono h w * mono a w ^ (-μ) = ∏ i, w i ^ ((p i + h i : ℝ) - a i * μ) := by
  unfold mono
  rw [← Real.finsetProd_rpow _ _ fun i _ => pow_nonneg (hw i).le _, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [← rpow_natCast]
  rw [← rpow_mul (hw i).le, ← rpow_add (hw i), ← rpow_add (hw i)]
  congr 1; ring

/-! ### Power–log sums and the face coefficient integrals -/

/-- The finite power–log sum `∑_{μ∈Λ} ∑_{j≤D} c_{μ,j} t^{−μ} (log t)^j`. -/
noncomputable def powLog (Λ : Finset ℝ) (D : ℕ) (c : ℝ → ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ μ ∈ Λ, ∑ j ∈ range (D + 1), c μ j * t ^ (-μ) * log t ^ j

theorem measurable_powLog (Λ : Finset ℝ) (D : ℕ) (c : ℝ → ℕ → ℝ) : Measurable (powLog Λ D c) :=
  Finset.measurable_sum _ fun _ _ => Finset.measurable_sum _ fun _ _ =>
    (measurable_const.mul (measurable_id'.pow_const _)).mul (measurable_log.pow_const _)

/-- The face coefficient integral `∫_{(0,b]^ι} G(w) w^h (w^a)^{−μ} S(w)^e dw`. -/
noncomputable def faceCoeffInt (G : (ι → ℝ) → ℝ) (h a : ι → ℕ) (b μ : ℝ) (e : ℕ) : ℝ :=
  ∫ w in box ι b, G w * mono h w * mono a w ^ (-μ) * logSum a w ^ e

/-- The remainder weight `∫_{(0,b]^ι} ∏ᵢ wᵢ^{pᵢ+hᵢ−aᵢL} (1 + |S(w)|)^D dw`. -/
noncomputable def faceRemWeight (p h a : ι → ℕ) (b L : ℝ) (D : ℕ) : ℝ :=
  ∫ w in box ι b, (∏ i, w i ^ ((p i + h i : ℝ) - a i * L)) * (1 + |logSum a w|) ^ D

/-- The coefficient integrands converge under `aᵢ μ < pᵢ + hᵢ + 1`. -/
theorem integrable_faceCoeff {G : (ι → ℝ) → ℝ} {p h a : ι → ℕ} {b M : ℝ} (hb : 0 < b)
    (hG : AEStronglyMeasurable G (volume.restrict (box ι b)))
    (hGM : ∀ w ∈ box ι b, |G w| ≤ M * mono p w) {μ : ℝ}
    (hμ : ∀ i, (a i : ℝ) * μ < p i + h i + 1) {e D : ℕ} (he : e ≤ D) :
    IntegrableOn (fun w => G w * mono h w * mono a w ^ (-μ) * logSum a w ^ e) (box ι b) := by
  have hint := (integrableOn_prod_rpow_mul_abs_log_pow
    (c := fun i => (p i + h i : ℝ) - a i * μ) (fun i => by have := hμ i; linarith)
    (fun i => (a i : ℝ)) he hb.le).const_mul M
  refine Integrable.mono' hint ?_ ?_
  · exact ((hG.mul (measurable_mono h).aestronglyMeasurable).mul
      ((measurable_mono a).pow_const _).aestronglyMeasurable).mul
      ((measurable_logSum a).pow_const e).aestronglyMeasurable
  refine (ae_restrict_mem (measurableSet_box b)).mono fun w hw => ?_
  have hpos := pos_of_mem_box hw
  have hGw := hGM w hw
  have h1 : 0 ≤ mono h w * mono a w ^ (-μ) * |logSum a w| ^ e := by
    have := mono_pos h hpos
    have := rpow_pos_of_pos (mono_pos a hpos) (-μ)
    positivity
  change |G w * mono h w * mono a w ^ (-μ) * logSum a w ^ e| ≤
    M * ((∏ i, w i ^ ((p i + h i : ℝ) - a i * μ)) * |logSum a w| ^ e)
  rw [abs_mul, abs_mul, abs_mul, abs_of_pos (mono_pos h hpos),
    abs_of_pos (rpow_pos_of_pos (mono_pos a hpos) _), abs_pow,
    ← mono_mul_mono_mul_rpow p h a μ hpos]
  calc |G w| * mono h w * mono a w ^ (-μ) * |logSum a w| ^ e
      = |G w| * (mono h w * mono a w ^ (-μ) * |logSum a w| ^ e) := by ring
    _ ≤ M * mono p w * (mono h w * mono a w ^ (-μ) * |logSum a w| ^ e) :=
        mul_le_mul_of_nonneg_right hGw h1
    _ = M * (mono p w * mono h w * mono a w ^ (-μ) * |logSum a w| ^ e) := by ring

/-! ### The main term -/

/-- Pointwise: the power–log sum at `t = N w^a` is a triple sum of coefficient integrands
(`t^{−μ} = N^{−μ} (w^a)^{−μ}`, `log t = log N + S(w)`, binomial expansion). -/
theorem mul_powLog_eq {G : (ι → ℝ) → ℝ} (h a : ι → ℕ) (Λ : Finset ℝ) (D : ℕ) (c : ℝ → ℕ → ℝ)
    {N : ℝ} (hN : 1 ≤ N) {w : ι → ℝ} (hpos : ∀ i, 0 < w i) :
    G w * mono h w * powLog Λ D c (N * mono a w) =
      ∑ μ ∈ Λ, ∑ j ∈ range (D + 1), ∑ q ∈ range (j + 1),
        (N ^ (-μ) * c μ j * (j.choose q) * log N ^ q) *
          (G w * mono h w * mono a w ^ (-μ) * logSum a w ^ (j - q)) := by
  unfold powLog
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Real.mul_rpow (by linarith) (mono_pos a hpos).le,
    Real.log_mul (by linarith) (mono_pos a hpos).ne', log_mono a hpos, add_pow, Finset.mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  ring

/-- The integral of the main term. -/
theorem integral_main {G : (ι → ℝ) → ℝ} {p h a : ι → ℕ} {b M : ℝ} (hb : 0 < b)
    (hG : AEStronglyMeasurable G (volume.restrict (box ι b)))
    (hGM : ∀ w ∈ box ι b, |G w| ≤ M * mono p w) {Λ : Finset ℝ} {D : ℕ} (c : ℝ → ℕ → ℝ)
    (hΛ : ∀ μ ∈ Λ, ∀ i, (a i : ℝ) * μ < p i + h i + 1) {N : ℝ} (hN : 1 ≤ N) :
    ∫ w in box ι b, G w * mono h w * powLog Λ D c (N * mono a w) =
      ∑ μ ∈ Λ, N ^ (-μ) * ∑ j ∈ range (D + 1), ∑ q ∈ range (j + 1),
        c μ j * (j.choose q) * log N ^ q * faceCoeffInt G h a b μ (j - q) := by
  have hint : ∀ μ ∈ Λ, ∀ j ∈ range (D + 1), ∀ q ∈ range (j + 1),
      IntegrableOn (fun w => (N ^ (-μ) * c μ j * (j.choose q) * log N ^ q) *
        (G w * mono h w * mono a w ^ (-μ) * logSum a w ^ (j - q))) (box ι b) :=
    fun μ hμ j hj q _ => (integrable_faceCoeff hb hG hGM (hΛ μ hμ)
      (by have := mem_range.1 hj; omega : j - q ≤ D)).const_mul _
  calc ∫ w in box ι b, G w * mono h w * powLog Λ D c (N * mono a w)
      = ∫ w in box ι b, ∑ μ ∈ Λ, ∑ j ∈ range (D + 1), ∑ q ∈ range (j + 1),
          (N ^ (-μ) * c μ j * (j.choose q) * log N ^ q) *
            (G w * mono h w * mono a w ^ (-μ) * logSum a w ^ (j - q)) :=
        setIntegral_congr_fun (measurableSet_box b) fun w hw =>
          mul_powLog_eq h a Λ D c hN (pos_of_mem_box hw)
    _ = ∑ μ ∈ Λ, ∑ j ∈ range (D + 1), ∑ q ∈ range (j + 1),
          (N ^ (-μ) * c μ j * (j.choose q) * log N ^ q) * faceCoeffInt G h a b μ (j - q) := by
        rw [integral_finsetSum _ fun μ hμ => integrable_finsetSum _ fun j hj =>
          integrable_finsetSum _ fun q hq => hint μ hμ j hj q hq]
        refine Finset.sum_congr rfl fun μ hμ => ?_
        rw [integral_finsetSum _ fun j hj =>
          integrable_finsetSum _ fun q hq => hint μ hμ j hj q hq]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [integral_finsetSum _ fun q hq => hint μ hμ j hj q hq]
        refine Finset.sum_congr rfl fun q _ => ?_
        exact MeasureTheory.integral_const_mul _ _
    _ = _ := by
        refine Finset.sum_congr rfl fun μ _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        ring

/-! ### The remainder -/

/-- `1 + |log N + S| ≤ (1 + log N)(1 + |S|)` for `N ≥ 1`. -/
theorem one_add_abs_log_add_le {N S : ℝ} (hN : 1 ≤ N) :
    1 + |log N + S| ≤ (1 + log N) * (1 + |S|) := by
  have h0 : 0 ≤ log N := log_nonneg hN
  have h1 := abs_add_le (log N) S
  rw [abs_of_nonneg h0] at h1
  nlinarith [abs_nonneg S]

/-- The pointwise remainder bound on the box. -/
theorem rem_bound {G : (ι → ℝ) → ℝ} {Z' : ℝ → ℝ} {p h a : ι → ℕ} {b M C L N : ℝ}
    {Λ : Finset ℝ} {D : ℕ} {c : ℝ → ℕ → ℝ} (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hGM : ∀ w ∈ box ι b, |G w| ≤ M * mono p w)
    (hZ2 : ∀ t : ℝ, 0 < t → |Z' t - powLog Λ D c t| ≤ C * t ^ (-L) * (1 + |log t|) ^ D)
    (hN : 1 ≤ N) {w : ι → ℝ} (hw : w ∈ box ι b) :
    |G w * mono h w * (Z' (N * mono a w) - powLog Λ D c (N * mono a w))| ≤
      C * M * (1 + log N) ^ D * N ^ (-L) *
        ((∏ i, w i ^ ((p i + h i : ℝ) - a i * L)) * (1 + |logSum a w|) ^ D) := by
  have hpos := pos_of_mem_box hw
  have hm := mono_pos a hpos
  have ht : 0 < N * mono a w := by positivity
  have hrp : (N * mono a w) ^ (-L) = N ^ (-L) * mono a w ^ (-L) :=
    Real.mul_rpow (by linarith) hm.le
  have hlog : 1 + |log (N * mono a w)| ≤ (1 + log N) * (1 + |logSum a w|) := by
    rw [Real.log_mul (by linarith) hm.ne', log_mono a hpos]
    exact one_add_abs_log_add_le hN
  have hpow : (1 + |log (N * mono a w)|) ^ D ≤ (1 + log N) ^ D * (1 + |logSum a w|) ^ D := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hlog D
  have hZ' : |Z' (N * mono a w) - powLog Λ D c (N * mono a w)| ≤
      C * (N ^ (-L) * mono a w ^ (-L)) * ((1 + log N) ^ D * (1 + |logSum a w|) ^ D) := by
    refine (hZ2 _ ht).trans ?_
    rw [hrp]
    exact mul_le_mul_of_nonneg_left hpow (mul_nonneg hC (by positivity))
  have hmh := mono_pos h hpos
  rw [abs_mul, abs_mul, abs_of_pos hmh]
  calc |G w| * mono h w * |Z' (N * mono a w) - powLog Λ D c (N * mono a w)|
      ≤ (M * mono p w) * mono h w *
          (C * (N ^ (-L) * mono a w ^ (-L)) * ((1 + log N) ^ D * (1 + |logSum a w|) ^ D)) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (hGM w hw) hmh.le) hZ' (abs_nonneg _)
          (mul_nonneg (mul_nonneg hM (mono_pos p hpos).le) hmh.le)
    _ = C * M * (1 + log N) ^ D * N ^ (-L) *
          ((mono p w * mono h w * mono a w ^ (-L)) * (1 + |logSum a w|) ^ D) := by ring
    _ = _ := by rw [mono_mul_mono_mul_rpow p h a L hpos]

/-- Nonnegativity of the two-regime constant (from `t = 1`). -/
theorem nonneg_of_two_regime {Z' : ℝ → ℝ} {Λ : Finset ℝ} {D : ℕ} {c : ℝ → ℕ → ℝ} {C L : ℝ}
    (hZ2 : ∀ t : ℝ, 0 < t → |Z' t - powLog Λ D c t| ≤ C * t ^ (-L) * (1 + |log t|) ^ D) :
    0 ≤ C := by
  have := hZ2 1 one_pos
  simp only [Real.one_rpow, Real.log_one, abs_zero, add_zero, one_pow, mul_one] at this
  exact (abs_nonneg _).trans this

/-- Nonnegativity of the flatness constant (from any point of the box). -/
theorem nonneg_of_flat {G : (ι → ℝ) → ℝ} {p : ι → ℕ} {b M : ℝ} (hb : 0 < b)
    (hGM : ∀ w ∈ box ι b, |G w| ≤ M * mono p w) : 0 ≤ M := by
  have := hGM _ (const_mem_box hb)
  exact (mul_nonneg_iff_of_pos_right (mono_pos p fun _ => hb)).1 ((abs_nonneg _).trans this)

/-! ### The face theorem -/

/-- ★★ **The generic face theorem**: an inner function with a global power–log estimate,
integrated against a product-flat outer amplitude on the box `(0,b]^ι` at the effective parameter
`N w^a`, has the power–log expansion with coefficients the face coefficient integrals
`faceCoeffInt`, the SAME logarithmic degree `D`, and remainder
`≤ C M (1 + log N)^D N^{−L} · faceRemWeight` for `N ≥ 1`, under `aᵢ L < pᵢ + hᵢ + 1`. -/
theorem face_expansion {G : (ι → ℝ) → ℝ} {Z' : ℝ → ℝ} {p h a : ι → ℕ} {b M C L N : ℝ}
    {Λ : Finset ℝ} {D : ℕ} {c : ℝ → ℕ → ℝ} (hb : 0 < b)
    (hG : AEStronglyMeasurable G (volume.restrict (box ι b)))
    (hGM : ∀ w ∈ box ι b, |G w| ≤ M * mono p w) (hZm : Measurable Z')
    (hZ2 : ∀ t : ℝ, 0 < t → |Z' t - powLog Λ D c t| ≤ C * t ^ (-L) * (1 + |log t|) ^ D)
    (hΛ : ∀ μ ∈ Λ, μ ≤ L) (hA : ∀ i, (a i : ℝ) * L < p i + h i + 1) (hN : 1 ≤ N) :
    |(∫ w in box ι b, G w * mono h w * Z' (N * mono a w)) -
      ∑ μ ∈ Λ, N ^ (-μ) * ∑ j ∈ range (D + 1), ∑ q ∈ range (j + 1),
        c μ j * (j.choose q) * log N ^ q * faceCoeffInt G h a b μ (j - q)| ≤
      C * M * (1 + log N) ^ D * N ^ (-L) * faceRemWeight p h a b L D := by
  have hM : 0 ≤ M := nonneg_of_flat hb hGM
  have hC : 0 ≤ C := nonneg_of_two_regime hZ2
  have hΛ' : ∀ μ ∈ Λ, ∀ i, (a i : ℝ) * μ < p i + h i + 1 := fun μ hμ i =>
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hΛ μ hμ) (Nat.cast_nonneg _)) (hA i)
  have hmain : IntegrableOn (fun w => G w * mono h w * powLog Λ D c (N * mono a w)) (box ι b) := by
    have hsum : IntegrableOn (fun w => ∑ μ ∈ Λ, ∑ j ∈ range (D + 1), ∑ q ∈ range (j + 1),
        (N ^ (-μ) * c μ j * (j.choose q) * log N ^ q) *
          (G w * mono h w * mono a w ^ (-μ) * logSum a w ^ (j - q))) (box ι b) :=
      integrable_finsetSum _ fun μ hμ => integrable_finsetSum _ fun j hj =>
        integrable_finsetSum _ fun q _ => (integrable_faceCoeff hb hG hGM (hΛ' μ hμ)
          (by have := mem_range.1 hj; omega : j - q ≤ D)).const_mul _
    exact hsum.congr ((ae_restrict_mem (measurableSet_box b)).mono fun w hw =>
      (mul_powLog_eq h a Λ D c hN (pos_of_mem_box hw)).symm)
  have hremW : IntegrableOn (fun w => C * M * (1 + log N) ^ D * N ^ (-L) *
      ((∏ i, w i ^ ((p i + h i : ℝ) - a i * L)) * (1 + |logSum a w|) ^ D)) (box ι b) :=
    (integrableOn_prod_rpow_mul_log_pow (c := fun i => (p i + h i : ℝ) - a i * L)
      (fun i => by have := hA i; linarith) (fun i => (a i : ℝ)) D hb.le).const_mul _
  have hremb : ∀ᵐ w ∂(volume.restrict (box ι b)),
      ‖G w * mono h w * (Z' (N * mono a w) - powLog Λ D c (N * mono a w))‖ ≤
        C * M * (1 + log N) ^ D * N ^ (-L) *
          ((∏ i, w i ^ ((p i + h i : ℝ) - a i * L)) * (1 + |logSum a w|) ^ D) :=
    (ae_restrict_mem (measurableSet_box b)).mono fun w hw => by
      rw [Real.norm_eq_abs]; exact rem_bound hM hC hGM hZ2 hN hw
  have hrem : IntegrableOn
      (fun w => G w * mono h w * (Z' (N * mono a w) - powLog Λ D c (N * mono a w))) (box ι b) := by
    refine Integrable.mono' hremW ?_ hremb
    have hT : Measurable fun w : ι → ℝ => N * mono a w := measurable_const.mul (measurable_mono a)
    exact ((hG.mul (measurable_mono h).aestronglyMeasurable).mul
      ((hZm.comp hT).sub ((measurable_powLog Λ D c).comp hT)).aestronglyMeasurable)
  have htot : IntegrableOn (fun w => G w * mono h w * Z' (N * mono a w)) (box ι b) := by
    refine (hmain.add hrem).congr (Eventually.of_forall fun w => ?_)
    simp only [Pi.add_apply]; ring
  rw [← integral_main hb hG hGM c hΛ' hN, ← integral_sub htot hmain]
  have heq : (fun w => G w * mono h w * Z' (N * mono a w) -
      G w * mono h w * powLog Λ D c (N * mono a w)) =
      fun w => G w * mono h w * (Z' (N * mono a w) - powLog Λ D c (N * mono a w)) := by
    funext w; ring
  rw [heq, faceRemWeight, ← MeasureTheory.integral_const_mul, ← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le hremW hremb

end SmoothEngine

end Grammar
