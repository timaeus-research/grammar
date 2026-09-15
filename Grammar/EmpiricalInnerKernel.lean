/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.EmpiricalOneDim
import Grammar.SmoothLogIntegrable
import Grammar.StateDensityAPI
import Grammar.MonomialPhaseIdentity

/-!
# The empirical inner kernel on the unit box, through the state density

For a measurable field factor `G : ℝ → ℝ` of at most polynomial-exponential growth
`|G(τ)| ≤ A (1+τ)^m e^{Mτ}` (`GrowthLE`), the **empirical inner kernel**
`I_G(t) = ∫_{(0,1]^{n+1}} u^e G(√t u^k) e^{−t u^{2k}} du`
is, by the exact state density `v` of the monomial `u^{2k}` under the weight `u^e`
(`integral_unitBox_monomial_eq_stateDensity`), the one-dimensional integral
`∏ 1/(2kᵢ) ∫₀¹ v(z) G(√(tz)) e^{−tz} dz`; and since `v(z) = ∑ c z^{μ−1} (−log z)^j` is an explicit
finite power–log sum, the substitution `z = s/t` turns every term into
`c t^{−μ} ∑_{q ≤ j} C(j,q) (log t)^q ∫₀^t s^{μ−1} (−log s)^{j−q} G(√s) e^{−s} ds`
(★★ `empUnitInner_eq_series`): the multivariate inner kernel is a finite combination of the
**log-weighted Mellin moments** `mellinMom G μ ℓ = ∫₀^∞ s^{μ−1}(−log s)^ℓ G(√s) e^{−s} ds` of the
field factor, with exponents `μ = (eᵢ+1)/(2kᵢ)` and log degrees below the multiplicity. The
truncation at `t` costs `O(e^{−t/2})` uniformly in `G` (★ `abs_mellinMom_sub_trunc_le`), which is
the two-regime input of the (parametrised) face theorem. For `G = e^{a·}` these are the
constant-field face kernels; for `G(τ) = τ^r e^{aτ}` the moments are `S_{μ+r/2}(a)` and its
`μ`-derivatives — the ladder. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology
open scoped ContDiff

namespace Grammar

namespace SmoothEngine

/-! ### Growth-bounded field factors -/

/-- `|G(τ)| ≤ A (1+τ)^m e^{Mτ}` for `τ ≥ 0`. -/
def GrowthLE (G : ℝ → ℝ) (A : ℝ) (m : ℕ) (M : ℝ) : Prop :=
  ∀ τ : ℝ, 0 ≤ τ → |G τ| ≤ A * (1 + τ) ^ m * exp (M * τ)

theorem GrowthLE.nonneg {G : ℝ → ℝ} {A : ℝ} {m : ℕ} {M : ℝ} (h : GrowthLE G A m M) : 0 ≤ A := by
  have := h 0 le_rfl
  simp only [add_zero, one_pow, mul_one, mul_zero, exp_zero] at this
  exact (abs_nonneg _).trans this

/-- A growth-bounded factor is bounded on `[0, T]`. -/
theorem GrowthLE.bound_on {G : ℝ → ℝ} {A : ℝ} {m : ℕ} {M : ℝ} (h : GrowthLE G A m M) {T τ : ℝ}
    (hT : 0 ≤ T) (hτ0 : 0 ≤ τ) (hτ : τ ≤ T) :
    |G τ| ≤ A * (1 + T) ^ m * exp (|M| * T) := by
  refine (h τ hτ0).trans ?_
  have hA := h.nonneg
  have hMT : M * τ ≤ |M| * T :=
    calc M * τ ≤ |M| * τ := mul_le_mul_of_nonneg_right (le_abs_self M) hτ0
      _ ≤ |M| * T := mul_le_mul_of_nonneg_left hτ (abs_nonneg M)
  exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) m) hA)
    (exp_le_exp.2 hMT) (exp_pos _).le (mul_nonneg hA (pow_nonneg (by linarith) _))

/-! ### Log-weighted Mellin moments -/

/-- The moment kernel `s^{μ−1} (−log s)^ℓ · G(√s) e^{−s}`. -/
noncomputable def momKernel (G : ℝ → ℝ) (μ : ℝ) (ℓ : ℕ) (s : ℝ) : ℝ :=
  s ^ (μ - 1) * (-log s) ^ ℓ * (G (Real.sqrt s) * exp (-s))

/-- The log-weighted Mellin moment `∫₀^∞ s^{μ−1} (−log s)^ℓ G(√s) e^{−s} ds`. -/
noncomputable def mellinMom (G : ℝ → ℝ) (μ : ℝ) (ℓ : ℕ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), momKernel G μ ℓ s

/-- The truncated moment `∫₀^t`. -/
noncomputable def mellinMomTrunc (G : ℝ → ℝ) (μ : ℝ) (ℓ : ℕ) (t : ℝ) : ℝ :=
  ∫ s in Ioc (0 : ℝ) t, momKernel G μ ℓ s

theorem measurable_momKernel {G : ℝ → ℝ} (hG : Measurable G) (μ : ℝ) (ℓ : ℕ) :
    Measurable (momKernel G μ ℓ) := by
  unfold momKernel
  fun_prop

/-- On `s ≥ 1` the moment kernel is dominated by a half-Gaussian: with
`n' = m + 2⌈μ⌉₊ + 2ℓ`, `|momKernel| ≤ A · kernelConst n' M · e^{−s/2}`. -/
theorem abs_momKernel_le_of_one_le {G : ℝ → ℝ} {A : ℝ} {m : ℕ} {M : ℝ} (hG : GrowthLE G A m M)
    (μ : ℝ) (ℓ : ℕ) {s : ℝ} (hs : 1 ≤ s) :
    |momKernel G μ ℓ s| ≤ A * kernelConst (m + 2 * ⌈μ⌉₊ + 2 * ℓ) M * exp (-s / 2) := by
  have hs0 : 0 < s := by linarith
  have hsq : 0 ≤ Real.sqrt s := Real.sqrt_nonneg s
  have hsq1 : 1 ≤ Real.sqrt s := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hs
  have hA := hG.nonneg
  set y := Real.sqrt s with hy
  have hys : s = y ^ 2 := by rw [hy, Real.sq_sqrt hs0.le]
  -- `s^{μ−1} ≤ (1+y)^{2⌈μ⌉}`
  have h1 : s ^ (μ - 1) ≤ (1 + y) ^ (2 * ⌈μ⌉₊) := by
    calc s ^ (μ - 1) ≤ s ^ ((⌈μ⌉₊ : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hs (by linarith [Nat.le_ceil μ])
      _ = (y ^ 2) ^ ⌈μ⌉₊ := by rw [Real.rpow_natCast, hys]
      _ = y ^ (2 * ⌈μ⌉₊) := by rw [← pow_mul]
      _ ≤ (1 + y) ^ (2 * ⌈μ⌉₊) := pow_le_pow_left₀ (by positivity) (by linarith) _
  -- `|log s|^ℓ ≤ (1+y)^{2ℓ}`
  have h2 : |(-log s) ^ ℓ| ≤ (1 + y) ^ (2 * ℓ) := by
    rw [abs_pow, abs_neg]
    have hlog : |log s| ≤ (1 + y) ^ 2 := by
      rw [abs_of_nonneg (Real.log_nonneg hs)]
      calc log s ≤ s - 1 := Real.log_le_sub_one_of_pos hs0
        _ ≤ s := by linarith
        _ = y ^ 2 := hys
        _ ≤ (1 + y) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) _
    calc |log s| ^ ℓ ≤ ((1 + y) ^ 2) ^ ℓ := pow_le_pow_left₀ (abs_nonneg _) hlog ℓ
      _ = (1 + y) ^ (2 * ℓ) := by rw [← pow_mul]
  have h3 : |G y| ≤ A * (1 + y) ^ m * exp (M * y) := hG y hsq
  have hker := jet_kernel_le 1 (m + 2 * ⌈μ⌉₊ + 2 * ℓ) M hsq
  simp only [pow_one, mul_one] at hker
  rw [show y ^ 2 = s from hys.symm] at hker
  unfold momKernel
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hs0.le _), abs_of_pos (exp_pos _)]
  calc s ^ (μ - 1) * |(-log s) ^ ℓ| * (|G (Real.sqrt s)| * exp (-s))
      ≤ (1 + y) ^ (2 * ⌈μ⌉₊) * (1 + y) ^ (2 * ℓ) * (A * (1 + y) ^ m * exp (M * y) * exp (-s)) := by
        gcongr
    _ = A * ((1 + y) ^ (m + 2 * ⌈μ⌉₊ + 2 * ℓ) * exp (M * y) * exp (-s)) := by
        rw [show m + 2 * ⌈μ⌉₊ + 2 * ℓ = 2 * ⌈μ⌉₊ + 2 * ℓ + m by ring, pow_add, pow_add]
        ring
    _ ≤ A * (kernelConst (m + 2 * ⌈μ⌉₊ + 2 * ℓ) M * exp (-s / 2)) := by
        unfold kernelConst
        exact mul_le_mul_of_nonneg_left hker hA
    _ = _ := by ring

/-- On `0 < s ≤ 1` the moment kernel is dominated by `A 2^m e^{|M|} s^{μ−1} (1 + |log s|)^ℓ`. -/
theorem abs_momKernel_le_of_le_one {G : ℝ → ℝ} {A : ℝ} {m : ℕ} {M : ℝ} (hG : GrowthLE G A m M)
    (μ : ℝ) (ℓ : ℕ) {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    |momKernel G μ ℓ s| ≤ A * 2 ^ m * exp |M| * (s ^ (μ - 1) * (1 + |log s|) ^ ℓ) := by
  have hsq : 0 ≤ Real.sqrt s := Real.sqrt_nonneg s
  have hsq1 : Real.sqrt s ≤ 1 := Real.sqrt_le_one.2 hs1
  have hA := hG.nonneg
  have h3 : |G (Real.sqrt s)| ≤ A * 2 ^ m * exp |M| := by
    refine (hG.bound_on zero_le_one hsq hsq1).trans (le_of_eq ?_)
    norm_num
  unfold momKernel
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hs0.le _), abs_of_pos (exp_pos _),
    abs_pow, abs_neg]
  have h4 : |log s| ^ ℓ ≤ (1 + |log s|) ^ ℓ := pow_le_pow_left₀ (abs_nonneg _) (by linarith) ℓ
  have h5 : exp (-s) ≤ 1 := by rw [exp_le_one_iff]; linarith
  calc s ^ (μ - 1) * |log s| ^ ℓ * (|G (Real.sqrt s)| * exp (-s))
      ≤ s ^ (μ - 1) * (1 + |log s|) ^ ℓ * (A * 2 ^ m * exp |M| * 1) := by gcongr
    _ = _ := by ring

theorem integrableOn_momKernel_Ioc {G : ℝ → ℝ} (hGm : Measurable G) {A : ℝ} {m : ℕ} {M : ℝ}
    (hG : GrowthLE G A m M) {μ : ℝ} (hμ : 0 < μ) (ℓ : ℕ) :
    IntegrableOn (momKernel G μ ℓ) (Ioc 0 1) := by
  have hint := (integrableOn_rpow_mul_log_pow (c := μ - 1) (by linarith [hμ]) 1 ℓ
    zero_le_one).const_mul (A * 2 ^ m * exp |M|)
  refine hint.mono' (measurable_momKernel hGm μ ℓ).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun s hs => ?_)
  rw [Real.norm_eq_abs]
  simp only [abs_one, one_mul]
  exact abs_momKernel_le_of_le_one hG μ ℓ hs.1 hs.2

theorem integrableOn_momKernel_Ioi_one {G : ℝ → ℝ} (hGm : Measurable G) {A : ℝ} {m : ℕ} {M : ℝ}
    (hG : GrowthLE G A m M) (μ : ℝ) (ℓ : ℕ) :
    IntegrableOn (momKernel G μ ℓ) (Ioi 1) := by
  have hint : IntegrableOn (fun s : ℝ => A * kernelConst (m + 2 * ⌈μ⌉₊ + 2 * ℓ) M * exp (-s / 2))
      (Ioi 1) := by
    have h0 : IntegrableOn (fun s : ℝ => A * kernelConst (m + 2 * ⌈μ⌉₊ + 2 * ℓ) M *
        exp (-(1 / 2) * s)) (Ioi 1) :=
      (exp_neg_integrableOn_Ioi (1 : ℝ) (b := 1 / 2) one_half_pos).const_mul _
    exact h0.congr_fun (fun s _ => by ring_nf) measurableSet_Ioi
  refine hint.mono' (measurable_momKernel hGm μ ℓ).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => ?_)
  rw [Real.norm_eq_abs]
  exact abs_momKernel_le_of_one_le hG μ ℓ (le_of_lt hs)

theorem integrableOn_momKernel {G : ℝ → ℝ} (hGm : Measurable G) {A : ℝ} {m : ℕ} {M : ℝ}
    (hG : GrowthLE G A m M) {μ : ℝ} (hμ : 0 < μ) (ℓ : ℕ) :
    IntegrableOn (momKernel G μ ℓ) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  exact (integrableOn_momKernel_Ioc hGm hG hμ ℓ).union (integrableOn_momKernel_Ioi_one hGm hG μ ℓ)

/-- ★ **The truncation error of the Mellin moment**: for `t ≥ 1`,
`|mellinMom − mellinMomTrunc t| ≤ A · kernelConst · 2 e^{−t/2}`. -/
theorem abs_mellinMom_sub_trunc_le {G : ℝ → ℝ} (hGm : Measurable G) {A : ℝ} {m : ℕ} {M : ℝ}
    (hG : GrowthLE G A m M) {μ : ℝ} (hμ : 0 < μ) (ℓ : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    |mellinMom G μ ℓ - mellinMomTrunc G μ ℓ t| ≤
      A * kernelConst (m + 2 * ⌈μ⌉₊ + 2 * ℓ) M * (2 * exp (-t / 2)) := by
  have hI := integrableOn_momKernel hGm hG hμ ℓ
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have hsplit : mellinMom G μ ℓ = mellinMomTrunc G μ ℓ t + ∫ s in Ioi t, momKernel G μ ℓ s := by
    unfold mellinMom mellinMomTrunc
    rw [← Ioc_union_Ioi_eq_Ioi ht0, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hI.mono_set Ioc_subset_Ioi_self) (hI.mono_set (Ioi_subset_Ioi ht0))]
  rw [hsplit, add_sub_cancel_left]
  set K := A * kernelConst (m + 2 * ⌈μ⌉₊ + 2 * ℓ) M with hK
  have hK0 : 0 ≤ K := mul_nonneg hG.nonneg (kernelConst_nonneg _ _)
  have hg : IntegrableOn (fun s : ℝ => K * exp (-s / 2)) (Ioi t) := by
    have h0 : IntegrableOn (fun s : ℝ => K * exp (-(1 / 2) * s)) (Ioi t) :=
      (exp_neg_integrableOn_Ioi t (b := 1 / 2) one_half_pos).const_mul K
    exact h0.congr_fun (fun s _ => by ring_nf) measurableSet_Ioi
  have h1 := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi t)) (f := momKernel G μ ℓ) hg
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => by
      rw [Real.norm_eq_abs]
      exact abs_momKernel_le_of_one_le hG μ ℓ (ht.trans (le_of_lt hs))))
  rw [Real.norm_eq_abs, MeasureTheory.integral_const_mul] at h1
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ hK0)
  have hexp : ∫ s in Ioi t, exp (-s / 2) = 2 * exp (-t / 2) := by
    have := integral_comp_mul_left_Ioi (fun x => exp (-x)) t (b := 1 / 2) one_half_pos
    simp only [smul_eq_mul, integral_exp_neg_Ioi] at this
    rw [show (fun s : ℝ => exp (-s / 2)) = fun s => exp (-(1 / 2 * s)) by
      funext s; ring_nf, this]
    ring_nf
  exact hexp.le

/-! ### The empirical inner kernel on the unit box -/

variable {n : ℕ}

/-- The state-density weights `(eᵢ+1)/(2kᵢ) − 1` of the monomial `u^{2k}` under `u^e`. -/
noncomputable def sdWeights (k e : Fin (n + 1) → ℕ) : Fin (n + 1) → ℝ :=
  fun i => ((e i : ℝ) + 1) / (2 * (k i : ℝ)) - 1

theorem sdWeights_gt (k e : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (i : Fin (n + 1)) :
    -1 < sdWeights k e i := by
  unfold sdWeights
  have : (0 : ℝ) < k i := by exact_mod_cast hk i
  have : 0 < ((e i : ℝ) + 1) / (2 * (k i : ℝ)) := by positivity
  linarith

theorem sdWeights_add_one_pos (k e : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (i : Fin (n + 1)) :
    0 < sdWeights k e i + 1 := by
  have := sdWeights_gt k e hk i
  linarith

/-- The energy factor `G(√(tz)) e^{−tz}` as a function of `z = u^{2k}`. -/
noncomputable def energyFactor (G : ℝ → ℝ) (t z : ℝ) : ℝ := G (Real.sqrt (t * z)) * exp (-t * z)

theorem measurable_energyFactor {G : ℝ → ℝ} (hG : Measurable G) (t : ℝ) :
    Measurable (energyFactor G t) := by
  unfold energyFactor
  fun_prop

/-- The empirical inner kernel `∫_{(0,1]^{n+1}} u^e G(√t u^k) e^{−t u^{2k}} du`. -/
noncomputable def empUnitInner (k e : Fin (n + 1) → ℕ) (G : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u in unitBox (n + 1), (∏ i, u i ^ e i) *
    (G (Real.sqrt t * ∏ i, u i ^ k i) * exp (-t * ∏ i, u i ^ (2 * k i)))

theorem prod_pow_two_mul_eq_sq (k : Fin (n + 1) → ℕ) (u : Fin (n + 1) → ℝ) :
    ∏ i, u i ^ (2 * k i) = (∏ i, u i ^ k i) ^ 2 := by
  rw [← Finset.prod_pow]
  exact Finset.prod_congr rfl fun i _ => by rw [← pow_mul, mul_comm]

/-- On the positive box, `√t u^k = √(t u^{2k})`. -/
theorem sqrt_mul_prod_pow (k : Fin (n + 1) → ℕ) {t : ℝ} (ht : 0 ≤ t) {u : Fin (n + 1) → ℝ}
    (hu : ∀ i, 0 ≤ u i) :
    Real.sqrt t * ∏ i, u i ^ k i = Real.sqrt (t * ∏ i, u i ^ (2 * k i)) := by
  rw [prod_pow_two_mul_eq_sq, Real.sqrt_mul ht,
    Real.sqrt_sq (Finset.prod_nonneg fun i _ => pow_nonneg (hu i) _)]

theorem prod_pow_mem_Ioc_of_mem_unitBox (k : Fin (n + 1) → ℕ) {u : Fin (n + 1) → ℝ}
    (hu : u ∈ unitBox (n + 1)) : ∏ i, u i ^ (2 * k i) ∈ Ioc (0 : ℝ) 1 :=
  ⟨Finset.prod_pos fun i _ => pow_pos (hu i (Set.mem_univ i)).1 _,
    Finset.prod_le_one (fun i _ => pow_nonneg (hu i (Set.mem_univ i)).1.le _)
      fun i _ => pow_le_one₀ (hu i (Set.mem_univ i)).1.le (hu i (Set.mem_univ i)).2⟩

theorem prod_pow_le_one_of_mem_unitBox (e : Fin (n + 1) → ℕ) {u : Fin (n + 1) → ℝ}
    (hu : u ∈ unitBox (n + 1)) : ∏ i, u i ^ e i ≤ 1 :=
  Finset.prod_le_one (fun i _ => pow_nonneg (hu i (Set.mem_univ i)).1.le _)
    fun i _ => pow_le_one₀ (hu i (Set.mem_univ i)).1.le (hu i (Set.mem_univ i)).2

theorem volume_unitBox_lt_top : volume (unitBox (n + 1)) < ⊤ :=
  (measure_mono (Set.pi_mono fun _ _ => Ioc_subset_Icc_self)).trans_lt
    (isCompact_univ_pi fun _ => isCompact_Icc).measure_lt_top

/-- **The signed state-density identity** for a bounded measurable energy factor `f`:
`∫_{(0,1]^{n+1}} u^e f(u^{2k}) du = ∏ 1/(2kᵢ) ∫₀¹ v(z) f(z) dz`. -/
theorem integral_unitBox_monomial_eq_stateDensity_signed (k e : Fin (n + 1) → ℕ)
    (hk : ∀ i, 0 < k i) {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ}
    (hfB : ∀ z ∈ Ioc (0 : ℝ) 1, |f z| ≤ B) :
    ∫ u in unitBox (n + 1), (∏ i, u i ^ e i) * f (∏ i, u i ^ (2 * k i)) =
      (∏ i, 1 / (2 * (k i : ℝ))) *
        ∫ z in Ioc (0 : ℝ) 1, PowLogRep.eval (stateDensityRep n (sdWeights k e)) z * f z := by
  set fp : ℝ → ℝ := fun z => max (f z) 0 with hfp_def
  set fm : ℝ → ℝ := fun z => max (-f z) 0 with hfm_def
  have hfp : Measurable fp := hf.max measurable_const
  have hfm : Measurable fm := hf.neg.max measurable_const
  have hsub : ∀ z, f z = fp z - fm z := fun z => by
    simp only [hfp_def, hfm_def]
    rcases le_total 0 (f z) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  have hfpB : ∀ z ∈ Ioc (0 : ℝ) 1, |fp z| ≤ B := fun z hz => by
    simp only [hfp_def]
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le ((le_abs_self _).trans (hfB z hz)) ((abs_nonneg _).trans (hfB z hz))
  have hfmB : ∀ z ∈ Ioc (0 : ℝ) 1, |fm z| ≤ B := fun z hz => by
    simp only [hfm_def]
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le ((neg_le_abs _).trans (hfB z hz)) ((abs_nonneg _).trans (hfB z hz))
  have hv := stateDensity_integrableOn n (sdWeights k e) (sdWeights_gt k e hk)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hfB 1 ⟨one_pos, le_rfl⟩)
  -- integrability of the box integrands
  have hbox : ∀ g : ℝ → ℝ, Measurable g → (∀ z ∈ Ioc (0 : ℝ) 1, |g z| ≤ B) →
      IntegrableOn (fun u : Fin (n + 1) → ℝ => (∏ i, u i ^ e i) * g (∏ i, u i ^ (2 * k i)))
        (unitBox (n + 1)) := by
    intro g hg hgB
    have hmeas : Measurable fun u : Fin (n + 1) → ℝ =>
        (∏ i, u i ^ e i) * g (∏ i, u i ^ (2 * k i)) :=
      (Finset.measurable_prod _ fun i _ => (measurable_pi_apply i).pow_const _).mul
        (hg.comp (Finset.measurable_prod _ fun i _ => (measurable_pi_apply i).pow_const _))
    refine Measure.integrableOn_of_bounded volume_unitBox_lt_top.ne hmeas.aestronglyMeasurable
      (M := B) ((ae_restrict_iff' (measurableSet_unitBox _)).2
        (Eventually.of_forall fun u hu => ?_))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Finset.prod_nonneg fun i _ =>
      pow_nonneg (hu i (Set.mem_univ i)).1.le _)]
    calc (∏ i, u i ^ e i) * |g (∏ i, u i ^ (2 * k i))| ≤ 1 * B :=
          mul_le_mul (prod_pow_le_one_of_mem_unitBox e hu)
            (hgB _ (prod_pow_mem_Ioc_of_mem_unitBox k hu)) (abs_nonneg _) zero_le_one
      _ = B := one_mul B
  -- integrability of the density integrands
  have hdens : ∀ g : ℝ → ℝ, Measurable g → (∀ z ∈ Ioc (0 : ℝ) 1, |g z| ≤ B) →
      IntegrableOn (fun z => PowLogRep.eval (stateDensityRep n (sdWeights k e)) z * g z)
        (Ioc (0 : ℝ) 1) := by
    intro g hg hgB
    refine (hv.abs.const_mul B).mono'
      ((PowLogRep.measurable_eval _).mul hg).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun z hz => ?_)
    rw [Real.norm_eq_abs, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hgB z hz) (abs_nonneg _)
  have hp := integral_unitBox_monomial_eq_stateDensity n e k hk fp hfp fun z _ => le_max_right _ _
  have hm := integral_unitBox_monomial_eq_stateDensity n e k hk fm hfm fun z _ => le_max_right _ _
  have hL : (fun u : Fin (n + 1) → ℝ => (∏ i, u i ^ e i) * f (∏ i, u i ^ (2 * k i))) =
      fun u => (∏ i, u i ^ e i) * fp (∏ i, u i ^ (2 * k i)) -
        (∏ i, u i ^ e i) * fm (∏ i, u i ^ (2 * k i)) := by
    funext u; rw [hsub]; ring
  have hR : (fun z => PowLogRep.eval (stateDensityRep n (sdWeights k e)) z * f z) =
      fun z => PowLogRep.eval (stateDensityRep n (sdWeights k e)) z * fp z -
        PowLogRep.eval (stateDensityRep n (sdWeights k e)) z * fm z := by
    funext z; rw [hsub]; ring
  rw [hL, integral_sub (hbox fp hfp hfpB) (hbox fm hfm hfmB), hR,
    integral_sub (hdens fp hfp hfpB) (hdens fm hfm hfmB), hp, hm]
  unfold sdWeights
  ring

/-! ### One state-density term against the energy factor -/

/-- `∫₀¹ F(z) dz = t⁻¹ ∫₀^t F(s/t) ds` on the half-open intervals. -/
theorem integral_Ioc_one_eq_scaled (F : ℝ → ℝ) {t : ℝ} (ht : 0 < t) :
    ∫ z in Ioc (0 : ℝ) 1, F z = t⁻¹ * ∫ s in Ioc (0 : ℝ) t, F (s / t) := by
  rw [← intervalIntegral.integral_of_le zero_le_one, ← intervalIntegral.integral_of_le ht.le]
  have h := intervalIntegral.integral_comp_div (a := (0 : ℝ)) (b := t) F ht.ne'
  rw [zero_div, div_self ht.ne', smul_eq_mul] at h
  rw [h]
  field_simp

/-- One power–log term of the state density against the energy factor: with `z = s/t`,
`∫₀¹ z^{μ−1}(−log z)^j G(√(tz)) e^{−tz} dz`
`  = t^{−μ} ∑_{q≤j} C(j,q) (log t)^q ∫₀^t s^{μ−1}(−log s)^{j−q} G(√s) e^{−s} ds`. -/
theorem integral_powLogBasis_mul_energyFactor {G : ℝ → ℝ} (hGm : Measurable G) {A : ℝ} {m : ℕ}
    {M : ℝ} (hG : GrowthLE G A m M) {μ : ℝ} (hμ : 0 < μ) (j : ℕ) {t : ℝ} (ht : 0 < t) :
    ∫ z in Ioc (0 : ℝ) 1, powLogBasis μ j z * energyFactor G t z =
      t ^ (-μ) * ∑ q ∈ Finset.range (j + 1),
        (j.choose q : ℝ) * log t ^ q * mellinMomTrunc G μ (j - q) t := by
  rw [integral_Ioc_one_eq_scaled _ ht]
  have hI : ∀ q, IntegrableOn (momKernel G μ (j - q)) (Ioc 0 t) :=
    fun q => (integrableOn_momKernel hGm hG hμ (j - q)).mono_set Ioc_subset_Ioi_self
  have hpt : ∀ s ∈ Ioc (0 : ℝ) t, powLogBasis μ j (s / t) * energyFactor G t (s / t) =
      ∑ q ∈ Finset.range (j + 1),
        (t ^ (-(μ - 1)) * ((j.choose q : ℝ) * log t ^ q)) * momKernel G μ (j - q) s := by
    intro s hs
    have hs0 : 0 < s := hs.1
    have hts : -t * (s / t) = -s := by field_simp
    unfold powLogBasis energyFactor momKernel
    rw [mul_div_cancel₀ _ ht.ne', Real.div_rpow hs0.le ht.le, Real.log_div hs0.ne' ht.ne',
      show -(log s - log t) = log t + -log s by ring, add_pow, hts, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Real.rpow_neg ht.le, div_eq_mul_inv]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioc hpt,
    integral_finsetSum _ fun q _ => (hI q).const_mul _]
  simp_rw [MeasureTheory.integral_const_mul]
  unfold mellinMomTrunc
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hpow : t⁻¹ * t ^ (-(μ - 1)) = t ^ (-μ) := by
    rw [show -(μ - 1) = -μ + 1 by ring, Real.rpow_add ht, Real.rpow_one]
    field_simp
  calc t⁻¹ * (t ^ (-(μ - 1)) * ((j.choose q : ℝ) * log t ^ q) *
        ∫ s in Ioc (0 : ℝ) t, momKernel G μ (j - q) s)
      = (t⁻¹ * t ^ (-(μ - 1))) * ((j.choose q : ℝ) * log t ^ q *
          ∫ s in Ioc (0 : ℝ) t, momKernel G μ (j - q) s) := by
        ring
    _ = _ := by rw [hpow]

/-! ### The exact series -/

/-- The truncated series term of one state-density entry `(μ, j, c)`. -/
noncomputable def innerTermTrunc (G : ℝ → ℝ) (t : ℝ) (en : ℝ × ℕ × ℝ) : ℝ :=
  en.2.2 * (t ^ (-en.1) * ∑ q ∈ Finset.range (en.2.1 + 1),
    (en.2.1.choose q : ℝ) * log t ^ q * mellinMomTrunc G en.1 (en.2.1 - q) t)

/-- The full series term of one state-density entry. -/
noncomputable def innerTerm (G : ℝ → ℝ) (t : ℝ) (en : ℝ × ℕ × ℝ) : ℝ :=
  en.2.2 * (t ^ (-en.1) * ∑ q ∈ Finset.range (en.2.1 + 1),
    (en.2.1.choose q : ℝ) * log t ^ q * mellinMom G en.1 (en.2.1 - q))

/-- The exact power–log series of the empirical inner kernel (truncated moments). -/
noncomputable def empInnerSeriesTrunc (k e : Fin (n + 1) → ℕ) (G : ℝ → ℝ) (t : ℝ) : ℝ :=
  (∏ i, 1 / (2 * (k i : ℝ))) * ((stateDensityRep n (sdWeights k e)).map (innerTermTrunc G t)).sum

/-- The power–log series of the empirical inner kernel (full moments). -/
noncomputable def empInnerSeries (k e : Fin (n + 1) → ℕ) (G : ℝ → ℝ) (t : ℝ) : ℝ :=
  (∏ i, 1 / (2 * (k i : ℝ))) * ((stateDensityRep n (sdWeights k e)).map (innerTerm G t)).sum

/-- Integrating a power–log representation with positive exponents against a bounded factor,
term by term. -/
theorem integral_eval_mul_eq_sum (c : PowLogRep) (hc : ∀ en ∈ c, 0 < en.1) {f : ℝ → ℝ}
    (hf : Measurable f) {B : ℝ} (hfB : ∀ z ∈ Ioc (0 : ℝ) 1, |f z| ≤ B) :
    ∫ z in Ioc (0 : ℝ) 1, PowLogRep.eval c z * f z =
      (c.map fun en => en.2.2 * ∫ z in Ioc (0 : ℝ) 1, powLogBasis en.1 en.2.1 z * f z).sum := by
  induction c with
  | nil => simp
  | cons en c ih =>
    have hen : 0 < en.1 := hc en List.mem_cons_self
    have hI : IntegrableOn (fun z => powLogBasis en.1 en.2.1 z * f z) (Ioc (0 : ℝ) 1) := by
      refine ((integrableOn_powLogBasis en.1 hen en.2.1).abs.const_mul B).mono'
        ((measurable_powLogBasis _ _).mul hf).aestronglyMeasurable ?_
      refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun z hz => ?_)
      rw [Real.norm_eq_abs, abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hfB z hz) (abs_nonneg _)
    have hIc : IntegrableOn (fun z => PowLogRep.eval c z * f z) (Ioc (0 : ℝ) 1) := by
      have hcv : IntegrableOn (PowLogRep.eval c) (Ioc (0 : ℝ) 1) :=
        integrableOn_rpow_mul_eval c 0 (fun en hen => by
          simpa using hc en (List.mem_cons_of_mem _ hen))
          |>.congr_fun (fun z _ => by simp) measurableSet_Ioc
      refine (hcv.abs.const_mul B).mono'
        ((PowLogRep.measurable_eval _).mul hf).aestronglyMeasurable ?_
      refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun z hz => ?_)
      rw [Real.norm_eq_abs, abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hfB z hz) (abs_nonneg _)
    rw [List.map_cons, List.sum_cons, ← ih (fun en' hen' => hc en' (List.mem_cons_of_mem _ hen')),
      ← MeasureTheory.integral_const_mul, ← integral_add ((hI.const_mul _)) hIc]
    refine setIntegral_congr_fun measurableSet_Ioc fun z _ => ?_
    rw [PowLogRep.eval_cons]
    ring

/-- The energy factor is bounded on `(0, 1]` for `t ≥ 0`. -/
theorem abs_energyFactor_le {G : ℝ → ℝ} {A : ℝ} {m : ℕ} {M : ℝ} (hG : GrowthLE G A m M) {t : ℝ}
    (ht : 0 ≤ t) {z : ℝ} (hz : z ∈ Ioc (0 : ℝ) 1) :
    |energyFactor G t z| ≤ A * (1 + Real.sqrt t) ^ m * exp (|M| * Real.sqrt t) := by
  unfold energyFactor
  rw [abs_mul, abs_of_pos (exp_pos _)]
  have h1 : Real.sqrt (t * z) ≤ Real.sqrt t := by
    refine Real.sqrt_le_sqrt ?_
    nlinarith [hz.1, hz.2]
  have h2 : exp (-t * z) ≤ 1 := by rw [exp_le_one_iff]; nlinarith [hz.1]
  have hb := hG.bound_on (Real.sqrt_nonneg t) (Real.sqrt_nonneg _) h1
  calc |G (Real.sqrt (t * z))| * exp (-t * z)
      ≤ (A * (1 + Real.sqrt t) ^ m * exp (|M| * Real.sqrt t)) * 1 :=
        mul_le_mul hb h2 (exp_pos _).le ((abs_nonneg _).trans hb)
    _ = _ := mul_one _

/-- ★★ **The empirical inner kernel is its truncated series**, exactly, for every `t > 0`. -/
theorem empUnitInner_eq_seriesTrunc (k e : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {G : ℝ → ℝ}
    (hGm : Measurable G) {A : ℝ} {m : ℕ} {M : ℝ} (hG : GrowthLE G A m M) {t : ℝ} (ht : 0 < t) :
    empUnitInner k e G t = empInnerSeriesTrunc k e G t := by
  have hpt : ∀ u ∈ unitBox (n + 1), (∏ i, u i ^ e i) *
      (G (Real.sqrt t * ∏ i, u i ^ k i) * exp (-t * ∏ i, u i ^ (2 * k i))) =
      (∏ i, u i ^ e i) * energyFactor G t (∏ i, u i ^ (2 * k i)) := by
    intro u hu
    unfold energyFactor
    rw [sqrt_mul_prod_pow k ht.le fun i => (hu i (Set.mem_univ i)).1.le]
  unfold empUnitInner
  rw [setIntegral_congr_fun (measurableSet_unitBox _) hpt,
    integral_unitBox_monomial_eq_stateDensity_signed k e hk (measurable_energyFactor hGm t)
      (fun z hz => abs_energyFactor_le hG ht.le hz)]
  unfold empInnerSeriesTrunc
  congr 1
  rw [integral_eval_mul_eq_sum _ (fun en hen => by
      obtain ⟨i, hi⟩ := stateDensityRep_exponent_mem n (sdWeights k e) en hen
      rw [hi]; exact sdWeights_add_one_pos k e hk i)
    (measurable_energyFactor hGm t) (fun z hz => abs_energyFactor_le hG ht.le hz)]
  congr 1
  refine List.map_congr_left fun en hen => ?_
  obtain ⟨i, hi⟩ := stateDensityRep_exponent_mem n (sdWeights k e) en hen
  have hμ : 0 < en.1 := by rw [hi]; exact sdWeights_add_one_pos k e hk i
  unfold innerTermTrunc
  rw [integral_powLogBasis_mul_energyFactor hGm hG hμ en.2.1 ht]

/-! ### The large-regime error -/

theorem list_sum_map_sub {α : Type*} (l : List α) (f g : α → ℝ) :
    (l.map fun x => f x - g x).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [List.map_cons, List.sum_cons, ih]; ring

theorem list_sum_le_of_forall {α : Type*} (l : List α) (f g : α → ℝ) (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h x List.mem_cons_self) (ih fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem abs_list_sum_le {α : Type*} (l : List α) (f : α → ℝ) :
    |(l.map f).sum| ≤ (l.map fun x => |f x|).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (abs_add_le _ _).trans (add_le_add le_rfl ih)

/-- Every log degree of the state density is at most `n`. -/
theorem stateDensityRep_degree_le (k e : Fin (n + 1) → ℕ) {en : ℝ × ℕ × ℝ}
    (hen : en ∈ stateDensityRep n (sdWeights k e)) : en.2.1 ≤ n := by
  have h := stateDensityRep_degree_lt n (sdWeights k e) en hen
  have hle : expMult (sdWeights k e) en.1 ≤ n + 1 := by
    unfold expMult
    exact (Finset.card_filter_le _ _).trans (by simp)
  omega

/-- The truncation constant of one entry `(μ, j, c)`:
`|c| ∑_{q ≤ j} C(j,q) · 2 kernelConst (m + 2⌈μ⌉ + 2(j−q)) M`. -/
noncomputable def innerTailConst (m : ℕ) (M : ℝ) (en : ℝ × ℕ × ℝ) : ℝ :=
  |en.2.2| * ∑ q ∈ Finset.range (en.2.1 + 1),
    (en.2.1.choose q : ℝ) * (2 * kernelConst (m + 2 * ⌈en.1⌉₊ + 2 * (en.2.1 - q)) M)

theorem innerTailConst_nonneg (m : ℕ) (M : ℝ) (en : ℝ × ℕ × ℝ) : 0 ≤ innerTailConst m M en := by
  unfold innerTailConst
  refine mul_nonneg (abs_nonneg _) (Finset.sum_nonneg fun q _ => ?_)
  have := kernelConst_nonneg (m + 2 * ⌈en.1⌉₊ + 2 * (en.2.1 - q)) M
  positivity

/-- The error of one entry for `t ≥ 1`, with `μ > 0` and `j ≤ n`:
`|innerTermTrunc − innerTerm| ≤ A · innerTailConst · (1 + log t)^n e^{−t/2}`. -/
theorem abs_innerTermTrunc_sub_innerTerm_le {G : ℝ → ℝ} (hGm : Measurable G) {A : ℝ} {m : ℕ}
    {M : ℝ} (hG : GrowthLE G A m M) {en : ℝ × ℕ × ℝ} (hμ : 0 < en.1) (hj : en.2.1 ≤ n) {t : ℝ}
    (ht : 1 ≤ t) :
    |innerTermTrunc G t en - innerTerm G t en| ≤
      A * innerTailConst m M en * ((1 + log t) ^ n * exp (-t / 2)) := by
  have hA := hG.nonneg
  have hlog : 0 ≤ log t := Real.log_nonneg ht
  have htμ : t ^ (-en.1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht (by linarith)
  have htμ0 : 0 ≤ t ^ (-en.1) := Real.rpow_nonneg (by linarith) _
  unfold innerTermTrunc innerTerm innerTailConst
  rw [← mul_sub, ← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_mul, abs_of_nonneg htμ0]
  have hterm : ∀ q ∈ Finset.range (en.2.1 + 1),
      |(en.2.1.choose q : ℝ) * log t ^ q * mellinMomTrunc G en.1 (en.2.1 - q) t -
        (en.2.1.choose q : ℝ) * log t ^ q * mellinMom G en.1 (en.2.1 - q)| ≤
      (en.2.1.choose q : ℝ) * (2 * kernelConst (m + 2 * ⌈en.1⌉₊ + 2 * (en.2.1 - q)) M) *
        (A * ((1 + log t) ^ n * exp (-t / 2))) := by
    intro q hq
    have hq' : q ≤ n := (Nat.lt_succ_iff.1 (Finset.mem_range.1 hq)).trans hj
    have hlq : log t ^ q ≤ (1 + log t) ^ n :=
      (pow_le_pow_left₀ hlog (by linarith) q).trans (pow_le_pow_right₀ (by linarith) hq')
    have htail := abs_mellinMom_sub_trunc_le hGm hG hμ (en.2.1 - q) ht
    rw [abs_sub_comm] at htail
    rw [← mul_sub, abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _),
      abs_of_nonneg (pow_nonneg hlog q)]
    calc (en.2.1.choose q : ℝ) * log t ^ q *
          |mellinMomTrunc G en.1 (en.2.1 - q) t - mellinMom G en.1 (en.2.1 - q)|
        ≤ (en.2.1.choose q : ℝ) * (1 + log t) ^ n *
          (A * kernelConst (m + 2 * ⌈en.1⌉₊ + 2 * (en.2.1 - q)) M * (2 * exp (-t / 2))) := by
          gcongr
      _ = _ := by ring
  calc |en.2.2| * (t ^ (-en.1) * |∑ q ∈ Finset.range (en.2.1 + 1),
        ((en.2.1.choose q : ℝ) * log t ^ q * mellinMomTrunc G en.1 (en.2.1 - q) t -
          (en.2.1.choose q : ℝ) * log t ^ q * mellinMom G en.1 (en.2.1 - q))|)
      ≤ |en.2.2| * (1 * ∑ q ∈ Finset.range (en.2.1 + 1),
          (en.2.1.choose q : ℝ) * (2 * kernelConst (m + 2 * ⌈en.1⌉₊ + 2 * (en.2.1 - q)) M) *
            (A * ((1 + log t) ^ n * exp (-t / 2)))) := by
        gcongr
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- ★★ **The large-regime estimate**: for `t ≥ 1`,
`|I_G(t) − empInnerSeries(t)| ≤ A · C_{k,e,m,M} · (1 + log t)^n e^{−t/2}`, the constant being a
finite sum over the state-density entries and linear in the growth constant `A`. -/
theorem abs_empUnitInner_sub_series_le (k e : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {G : ℝ → ℝ}
    (hGm : Measurable G) {A : ℝ} {m : ℕ} {M : ℝ} (hG : GrowthLE G A m M) {t : ℝ} (ht : 1 ≤ t) :
    |empUnitInner k e G t - empInnerSeries k e G t| ≤
      A * ((∏ i, 1 / (2 * (k i : ℝ))) *
        ((stateDensityRep n (sdWeights k e)).map (innerTailConst m M)).sum) *
        ((1 + log t) ^ n * exp (-t / 2)) := by
  rw [empUnitInner_eq_seriesTrunc k e hk hGm hG (by linarith)]
  unfold empInnerSeriesTrunc empInnerSeries
  rw [← mul_sub, abs_mul, abs_of_nonneg (Finset.prod_nonneg fun i _ => by positivity)]
  set rep := stateDensityRep n (sdWeights k e) with hrep
  have hsub : (rep.map (innerTermTrunc G t)).sum - (rep.map (innerTerm G t)).sum =
      (rep.map fun en => innerTermTrunc G t en - innerTerm G t en).sum :=
    (list_sum_map_sub rep _ _).symm
  rw [hsub]
  have hentry : ∀ en ∈ rep, |innerTermTrunc G t en - innerTerm G t en| ≤
      A * innerTailConst m M en * ((1 + log t) ^ n * exp (-t / 2)) := fun en hen => by
    obtain ⟨i, hi⟩ := stateDensityRep_exponent_mem n (sdWeights k e) en hen
    exact abs_innerTermTrunc_sub_innerTerm_le hGm hG
      (by rw [hi]; exact sdWeights_add_one_pos k e hk i) (stateDensityRep_degree_le k e hen) ht
  have hlist : (rep.map fun en => |innerTermTrunc G t en - innerTerm G t en|).sum ≤
      (rep.map fun en => A * innerTailConst m M en * ((1 + log t) ^ n * exp (-t / 2))).sum :=
    list_sum_le_of_forall rep _ _ hentry
  have hfac : (rep.map fun en => A * innerTailConst m M en * ((1 + log t) ^ n * exp (-t / 2))).sum =
      A * (rep.map (innerTailConst m M)).sum * ((1 + log t) ^ n * exp (-t / 2)) := by
    rw [show (fun en => A * innerTailConst m M en * ((1 + log t) ^ n * exp (-t / 2))) =
      fun en => (A * ((1 + log t) ^ n * exp (-t / 2))) * innerTailConst m M en by
        funext en; ring, List.sum_map_mul_left]
    ring
  calc (∏ i, 1 / (2 * (k i : ℝ))) *
        |(rep.map fun en => innerTermTrunc G t en - innerTerm G t en).sum|
      ≤ (∏ i, 1 / (2 * (k i : ℝ))) *
          (rep.map fun en => |innerTermTrunc G t en - innerTerm G t en|).sum :=
        mul_le_mul_of_nonneg_left (abs_list_sum_le _ _)
          (Finset.prod_nonneg fun i _ => by positivity)
    _ ≤ (∏ i, 1 / (2 * (k i : ℝ))) *
          (A * (rep.map (innerTailConst m M)).sum * ((1 + log t) ^ n * exp (-t / 2))) := by
        rw [← hfac]
        exact mul_le_mul_of_nonneg_left hlist (Finset.prod_nonneg fun i _ => by positivity)
    _ = _ := by ring

end SmoothEngine

end Grammar
