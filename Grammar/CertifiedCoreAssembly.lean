import Grammar.BoxMomentBound
import Grammar.ScaledAssembly

/-!
# The expectation assembly for certified sub-Gaussian cores

The expectation assembly of `ScaledAssembly.lean` takes an abstract uniform `p`-th moment bound on
the scaled cores. For finitely many certified box cores
`Z_n^{core}(ω) = ∑_j dataBoxIntegral n (h j) (k j) β (N_n) (b j) (x j n ω)` with Borel-measurable
bounded random data and the full-box exponential-moment bound on their phase fields, that
hypothesis is discharged by `BoxMomentBound.lean`: each core has
`E|A_n Y_{j,n}|^p ≤ (M A_n b_j^{|h_j|+d} Z^pop_{α,j}(N'_n))^p`, the elementary bound
`|∑_j Y_j|^p ≤ J^{p−1}∑_j|Y_j|^p` (`abs_sum_rpow_le`) assembles the cores, and a certified bound on
the scaled population masses at the reduced temperature `α = β(1 − pβc/2)` for `n ≥ n₀` gives a
uniform bound (the finitely many earlier terms being individually bounded,
`exists_uniform_bound_of_eventually`). Hence, with `A_n Z_n^{core} ⇒ L` and `E|A_n Rem_n| → 0`,

**`E[A_n Z_n] → E L`**   (`tendsto_integral_scaled_assembly_of_certified_subgaussian_cores`),

an annealed asymptotic for certified sub-Gaussian cores with the abstract moment hypothesis
removed. Non-claims: the field limit `A_n Z^core_n ⇒ L`, the certified core representation, the
full-box exponential-moment bound and the reduced-temperature population bound remain hypotheses;
`E L` is the limiting empirical coefficient's expectation, not the population coefficient; no
next-order correction.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace Grammar

/-- `|∑_j Y_j|^p ≤ J^{p−1} ∑_j |Y_j|^p` for `p ≥ 1`. -/
theorem abs_sum_rpow_le {J : ℕ} {p : ℝ} (hp : 1 ≤ p) (Y : Fin J → ℝ) :
    |∑ j, Y j| ^ p ≤ (J : ℝ) ^ (p - 1) * ∑ j, |Y j| ^ p := by
  rcases Nat.eq_zero_or_pos J with hJ | hJ
  · subst hJ
    simp [Real.zero_rpow (by linarith : p ≠ 0)]
  have hJ' : (0 : ℝ) < J := by exact_mod_cast hJ
  have hw : ∑ _j : Fin J, (1 / (J : ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hJen := Real.rpow_arith_mean_le_arith_mean_rpow Finset.univ (fun _ => 1 / (J : ℝ))
    (fun j => |Y j|) (fun _ _ => by positivity) hw (fun j _ => abs_nonneg _) hp
  have h1 : |∑ j, Y j| ^ p ≤ (∑ j, |Y j|) ^ p :=
    Real.rpow_le_rpow (abs_nonneg _) (Finset.abs_sum_le_sum_abs _ _) (by linarith)
  have h2 : (∑ j, |Y j|) = (J : ℝ) * ∑ j, 1 / (J : ℝ) * |Y j| := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp
  calc |∑ j, Y j| ^ p ≤ (∑ j, |Y j|) ^ p := h1
    _ = (J : ℝ) ^ p * (∑ j, 1 / (J : ℝ) * |Y j|) ^ p := by
        rw [h2, Real.mul_rpow hJ'.le (Finset.sum_nonneg fun j _ => by positivity)]
    _ ≤ (J : ℝ) ^ p * ∑ j, 1 / (J : ℝ) * |Y j| ^ p :=
        mul_le_mul_of_nonneg_left hJen (Real.rpow_nonneg hJ'.le _)
    _ = (J : ℝ) ^ (p - 1) * ∑ j, |Y j| ^ p := by
        rw [show p = (p - 1) + 1 by ring, Real.rpow_add_one hJ'.ne', Finset.mul_sum, Finset.mul_sum,
          show p - 1 + 1 - 1 = p - 1 by ring]
        refine Finset.sum_congr rfl fun j _ => ?_
        field_simp

/-- An eventually uniform bound and finitely many exceptions give a uniform bound. -/
theorem exists_uniform_bound_of_eventually {f : ℕ → ℝ} {n₀ : ℕ} {M₀ : ℝ}
    (h : ∀ m, n₀ ≤ m → f m ≤ M₀) : ∃ M', ∀ m, f m ≤ M' := by
  obtain ⟨B, hB⟩ := ((Set.finite_Iio n₀).image f).bddAbove
  refine ⟨max M₀ B, fun m => ?_⟩
  rcases le_or_gt n₀ m with hm | hm
  · exact (h m hm).trans (le_max_left _ _)
  · exact (hB ⟨m, hm, rfl⟩).trans (le_max_right _ _)

section Cores

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']

omit [IsProbabilityMeasure P] in
/-- Bochner form of a `p`-th moment bound from its `lintegral` form. -/
theorem integral_rpow_abs_le_of_lintegral_le {Y : Ω → ℝ} (hY : Measurable Y) {p B : ℝ}
    (hp : 0 < p) (hB : 0 ≤ B)
    (h : ∫⁻ ω, ENNReal.ofReal (|Y ω| ^ p) ∂P ≤ ENNReal.ofReal B ^ p) :
    Integrable (fun ω => |Y ω| ^ p) P ∧ ∫ ω, |Y ω| ^ p ∂P ≤ B ^ p := by
  have hmeas : Measurable fun ω => |Y ω| ^ p := (hY.norm).pow_const p
  have hnn : ∀ ω, 0 ≤ |Y ω| ^ p := fun ω => Real.rpow_nonneg (abs_nonneg _) _
  rw [ENNReal.ofReal_rpow_of_nonneg hB hp.le] at h
  have hint : Integrable (fun ω => |Y ω| ^ p) P := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hnn)]
    exact lt_of_le_of_lt h ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hnn)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg hB _)).1 h

variable (n : ℕ) {J : ℕ} (h k : Fin J → Fin (n + 1) → ℕ) (b : Fin J → ℝ)

/-- The assembled certified core: the sum of the box integrals of the chart data. -/
noncomputable def coreSum (β : ℝ) (Nn : ℕ → ℝ) (x : Fin J → ℕ → Ω → DataSpace (n + 1)) (m : ℕ)
    (ω : Ω) : ℝ :=
  ∑ j, dataBoxIntegral n (h j) (k j) β (Nn m) (b j) (x j m ω)

/-- **Uniform `p`-th moments of the assembled certified cores** from the population masses at the
reduced temperature. -/
theorem uniform_moment_coreSum {β c p M : ℝ} (hβ : 0 < β) (hp : 1 ≤ p) (hc : p * β * c < 2)
    (hM : 0 ≤ M) (hb : ∀ j, 0 < b j) {A Nn : ℕ → ℝ} (hA : ∀ m, 0 ≤ A m) (hNn : ∀ m, 0 ≤ Nn m)
    (x : Fin J → ℕ → Ω → DataSpace (n + 1)) (hx : ∀ j m, Measurable (x j m))
    (hxM : ∀ j m ω, ‖x j m ω‖ ≤ M)
    (hmgf : ∀ j m, ∀ u ∈ unitBox (n + 1), ∀ t : ℝ, 0 ≤ t →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (t * CoeffFamily.evalF (xiCoord (x j m ω)) u)) ∂P ≤
        ENNReal.ofReal (Real.exp (c * t ^ 2 / 2)))
    {n₀ : ℕ} {Cα : Fin J → ℝ}
    (hpop : ∀ j m, n₀ ≤ m → A m * popBoxMass n (h j) (k j) (β * (1 - p * β * c / 2))
      (boxScale (k j) (b j) (Nn m)) ≤ Cα j) :
    (∀ m, Integrable (fun ω => |A m * coreSum n h k b β Nn x m ω| ^ p) P) ∧
      ∃ M', ∀ m, ∫ ω, |A m * coreSum n h k b β Nn x m ω| ^ p ∂P ≤ M' := by
  have hp0 : 0 < p := by linarith
  -- each core: Bochner moment bound
  have hcore : ∀ j m, Integrable (fun ω =>
      |A m * dataBoxIntegral n (h j) (k j) β (Nn m) (b j) (x j m ω)| ^ p) P ∧
      ∫ ω, |A m * dataBoxIntegral n (h j) (k j) β (Nn m) (b j) (x j m ω)| ^ p ∂P ≤
        (M * (A m * (b j) ^ (∑ i, h j i + (n + 1)) *
          popBoxMass n (h j) (k j) (β * (1 - p * β * c / 2))
            (boxScale (k j) (b j) (Nn m)))) ^ p := by
    intro j m
    have hpos : 0 ≤ popBoxMass n (h j) (k j) (β * (1 - p * β * c / 2))
        (boxScale (k j) (b j) (Nn m)) :=
      setIntegral_nonneg (measurableSet_unitBox _) fun u hu =>
        mul_nonneg (Finset.prod_nonneg fun i _ => pow_nonneg (hu i (mem_univ i)).1.le _)
          (Real.exp_pos _).le
    refine integral_rpow_abs_le_of_lintegral_le P
      (measurable_const.mul ((measurable_dataBoxIntegral n (h j) (k j) hβ.le (hNn m) (hb j)).comp
        (hx j m))) hp0 (mul_nonneg hM (mul_nonneg (mul_nonneg (hA m) (pow_nonneg (hb j).le _))
          hpos)) ?_
    exact moment_scaled_dataBoxIntegral_le P n (h j) (k j) hβ hp hc (hA m) hM (hNn m) (hb j)
      (x j m) (hx j m) (hxM j m) (hmgf j m)
  -- the assembled core
  have hsum : ∀ m ω, |A m * coreSum n h k b β Nn x m ω| ^ p ≤
      (J : ℝ) ^ (p - 1) *
        ∑ j, |A m * dataBoxIntegral n (h j) (k j) β (Nn m) (b j) (x j m ω)| ^ p := by
    intro m ω
    unfold coreSum
    rw [Finset.mul_sum]
    exact abs_sum_rpow_le hp _
  have hmeas : ∀ m, Measurable fun ω => |A m * coreSum n h k b β Nn x m ω| ^ p := fun m => by
    have hm : Measurable fun ω => A m * coreSum n h k b β Nn x m ω :=
      measurable_const.mul (Finset.measurable_sum _ fun j _ =>
        (measurable_dataBoxIntegral n (h j) (k j) hβ.le (hNn m) (hb j)).comp (hx j m))
    exact hm.norm.pow_const p
  have hint : ∀ m, Integrable (fun ω => |A m * coreSum n h k b β Nn x m ω| ^ p) P := fun m =>
    ((integrable_finsetSum _ fun j _ => (hcore j m).1).const_mul _).mono'
      (hmeas m).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
        exact hsum m ω)
  refine ⟨hint, ?_⟩
  -- the eventual uniform bound
  set f : ℕ → ℝ := fun m => ∫ ω, |A m * coreSum n h k b β Nn x m ω| ^ p ∂P with hf
  refine exists_uniform_bound_of_eventually (f := f) (n₀ := n₀)
    (M₀ := (J : ℝ) ^ (p - 1) * ∑ j, (M * (b j) ^ (∑ i, h j i + (n + 1)) * Cα j) ^ p) fun m hm => ?_
  calc f m ≤ ∫ ω, (J : ℝ) ^ (p - 1) * ∑ j,
        |A m * dataBoxIntegral n (h j) (k j) β (Nn m) (b j) (x j m ω)| ^ p ∂P :=
        integral_mono (hint m) ((integrable_finsetSum _ fun j _ => (hcore j m).1).const_mul _)
          (hsum m)
    _ = (J : ℝ) ^ (p - 1) * ∑ j, ∫ ω,
        |A m * dataBoxIntegral n (h j) (k j) β (Nn m) (b j) (x j m ω)| ^ p ∂P := by
        rw [integral_const_mul, integral_finsetSum _ fun j _ => (hcore j m).1]
    _ ≤ (J : ℝ) ^ (p - 1) * ∑ j, (M * (b j) ^ (∑ i, h j i + (n + 1)) * Cα j) ^ p := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_)
          (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        have hpm := hpop j m hm
        have hbpos := hb j
        have hpos0 : 0 ≤ popBoxMass n (h j) (k j) (β * (1 - p * β * c / 2))
            (boxScale (k j) (b j) (Nn m)) :=
          setIntegral_nonneg (measurableSet_unitBox _) fun u hu =>
            mul_nonneg (Finset.prod_nonneg fun i _ => pow_nonneg (hu i (mem_univ i)).1.le _)
              (Real.exp_pos _).le
        refine (hcore j m).2.trans (Real.rpow_le_rpow
          (mul_nonneg hM (mul_nonneg (mul_nonneg (hA m) (pow_nonneg hbpos.le _)) hpos0)) ?_ hp0.le)
        calc M * (A m * (b j) ^ (∑ i, h j i + (n + 1)) *
              popBoxMass n (h j) (k j) (β * (1 - p * β * c / 2)) (boxScale (k j) (b j) (Nn m)))
            = M * (b j) ^ (∑ i, h j i + (n + 1)) * (A m *
              popBoxMass n (h j) (k j) (β * (1 - p * β * c / 2))
                (boxScale (k j) (b j) (Nn m))) := by
              ring
          _ ≤ M * (b j) ^ (∑ i, h j i + (n + 1)) * Cα j :=
              mul_le_mul_of_nonneg_left hpm (by positivity)

/-- **The expectation assembly for certified sub-Gaussian cores**: with `A_n Z^core_n ⇒ L`,
`E|A_n Rem_n| → 0`, bounded Borel data with full-box exponential moments, and the certified
reduced-temperature population bound, `E[A_n(Z^core_n + Rem_n)] → E L`. -/
theorem tendsto_integral_scaled_assembly_of_certified_subgaussian_cores {β c p M : ℝ}
    (hβ : 0 < β) (hp : 1 < p) (hc : p * β * c < 2) (hM : 0 ≤ M) (hb : ∀ j, 0 < b j)
    {A Nn : ℕ → ℝ} (hA : ∀ m, 0 ≤ A m) (hNn : ∀ m, 0 ≤ Nn m)
    (x : Fin J → ℕ → Ω → DataSpace (n + 1)) (hx : ∀ j m, Measurable (x j m))
    (hxM : ∀ j m ω, ‖x j m ω‖ ≤ M)
    (hmgf : ∀ j m, ∀ u ∈ unitBox (n + 1), ∀ t : ℝ, 0 ≤ t →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (t * CoeffFamily.evalF (xiCoord (x j m ω)) u)) ∂P ≤
        ENNReal.ofReal (Real.exp (c * t ^ 2 / 2)))
    {n₀ : ℕ} {Cα : Fin J → ℝ}
    (hpop : ∀ j m, n₀ ≤ m → A m * popBoxMass n (h j) (k j) (β * (1 - p * β * c / 2))
      (boxScale (k j) (b j) (Nn m)) ≤ Cα j)
    {L : Ω' → ℝ}
    (hcore : TendstoInDistribution (fun m ω => A m * coreSum n h k b β Nn x m ω) atTop L
      (fun _ => P) μ')
    {R : ℕ → Ω → ℝ} (hRint : ∀ m, Integrable (fun ω => A m * R m ω) P)
    (hrem : Tendsto (fun m => ∫ ω, |A m * R m ω| ∂P) atTop (𝓝 0)) :
    Integrable L μ' ∧ Tendsto (fun m => ∫ ω, A m * (coreSum n h k b β Nn x m ω + R m ω) ∂P)
      atTop (𝓝 (∫ ω, L ω ∂μ')) := by
  obtain ⟨hint, M', hM'⟩ := uniform_moment_coreSum P n h k b hβ hp.le hc hM hb hA hNn x hx hxM hmgf
    hpop
  exact tendsto_integral_scaled_assembly hcore hp hint hM' hRint hrem

end Cores

end Grammar
