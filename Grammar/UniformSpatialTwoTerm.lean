/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.OrderedRemainder
import Grammar.PopulationDataBridge
import Grammar.SpatialSecondCoeffExplicit

/-!
# The spatial two-term expansion, uniformly on coefficient balls

For a datum `x` in the weighted-ℓ¹ data space (phase and amplitude Taylor families), the second
ordered normalised remainder at `(λ, m−2)` is exactly `log N (Z_N(x)/(N^{−λ} log^{m−1} N) − F(x))`:
every predecessor coefficient vanishes except the leading one, `F(x) = C_{λ,m−1}(x)`
(`predSum_spatial`).  The uniform convergence of the ordered remainders on data balls (Headline
XXXV-era, `tendstoUniformlyOn_orderedRemainder`) is therefore the **uniform spatial two-term
theorem** (`tendstoUniformlyOn_spatialTwoTerm`): uniformly on `‖x‖ ≤ R`,
`log N (Z_N(x)/(N^{−λ} log^{m−1} N) − F(x)) → B(x) = C_{λ,m−2}(x)`, with `F`, `B` continuous in
the data (`continuous_taylorTree_coeff`) and identified with the face functional and the explicit
finite-part second coefficient of the represented phase and amplitude
(`dataBoxCoeff_spatialFace`, `dataBoxCoeff_spatialSecondFace`).  For `m = 1` the log-amplified
statement `log N (N^λ Z_N(x) − F(x)) → 0` holds uniformly (`tendstoUniformlyOn_spatialTwoTerm_one`,
from the ordered remainder at the next lattice point `λ + 1/Q`), and `B = 0`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open CoeffFamily

variable {d : ℕ}

/-! ### Represented phase and amplitude of a datum -/

/-- The represented phase of a datum, extended continuously by clamping. -/
noncomputable def dataPhase (x : DataSpace d) (u : Fin d → ℝ) : ℝ :=
  evalF (xiCoord x) (cubeClamp u)

theorem continuous_dataPhase (x : DataSpace d) : Continuous (dataPhase x) :=
  (continuousOn_evalF (absSummable_xiCoord x)).comp_continuous continuous_cubeClamp
    cubeClamp_mem_closedCube

theorem dataPhase_eq_of_mem (x : DataSpace d) {u : Fin d → ℝ} (hu : u ∈ closedCube d) :
    dataPhase x u = evalF (xiCoord x) u := by
  unfold dataPhase
  rw [cubeClamp_eq_of_mem hu]

variable (n : ℕ) (h k : Fin (n + 1) → ℕ)

theorem evalF_xiCoord_eq_dataPhase (x : DataSpace (n + 1)) :
    ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF (xiCoord x) u = dataPhase x u := fun u hu =>
  (dataPhase_eq_of_mem x (unitBox_subset_closedCube _ hu)).symm

theorem evalF_etaCoord_eq_dataAmplitude (x : DataSpace (n + 1)) :
    ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF (etaCoord x) u = dataAmplitude x u := fun u hu =>
  (dataAmplitude_eq_of_mem x (unitBox_subset_closedCube _ hu)).symm

/-- At `b = 1` the datum's box integral is the chart integral of its represented phase and
amplitude. -/
theorem dataBoxIntegral_one (β N : ℝ) (x : DataSpace (n + 1)) :
    dataBoxIntegral n h k β N 1 x =
      origPhaseIntegral n h k β N 1 (dataPhase x) (dataAmplitude x) := by
  unfold dataBoxIntegral
  rw [toXi_one, toEta_one]
  exact familyPhaseIntegralBox_eq_orig n h k β N 1 (evalF_xiCoord_eq_dataPhase n x)
    (evalF_etaCoord_eq_dataAmplitude n x)

/-- At `b = 1` the canonical coefficient is the family spectral coefficient (`j ≤ n`). -/
theorem dataBoxCoeff_one (β : ℝ) (x : DataSpace (n + 1)) (μ : ℝ) {j : ℕ} (hj : j ≤ n) :
    dataBoxCoeff n h k β 1 x μ j = familySpectralCoeff n h k β (xiCoord x) (etaCoord x) μ j := by
  unfold dataBoxCoeff
  rw [toXi_one, toEta_one, boxCoeff_one n h k β _ _ μ hj]

variable (hk : ∀ i, 0 < k i) {β : ℝ} (hβ : 0 < β) {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i)
  (hatt : ∃ i, ratioExp h k i = l)

include hk hβ hmin hatt in
/-- The leading canonical coefficient of a datum is the face functional of its represented phase
and amplitude, and the coefficients above degree `m − 1` at exponent `λ` vanish. -/
theorem dataBoxCoeff_spatialFace (x : DataSpace (n + 1)) :
    (∀ j, multCount (ratioExp h k) l - 1 < j → dataBoxCoeff n h k β 1 x l j = 0) ∧
      dataBoxCoeff n h k β 1 x l (multCount (ratioExp h k) l - 1) =
        spatialFace h k l β (dataPhase x) (dataAmplitude x) := by
  have hm_le : multCount (ratioExp h k) l - 1 ≤ n := by
    have := multCount_le_card (ratioExp h k) l
    omega
  have hs := spatial_leadingCoeff n h k hk hβ (absSummable_xiCoord x) (absSummable_etaCoord x)
    (continuous_dataPhase x) (continuous_dataAmplitude x) (evalF_xiCoord_eq_dataPhase n x)
    (evalF_etaCoord_eq_dataAmplitude n x) hmin hatt
  refine ⟨fun j hj => ?_, ?_⟩
  · by_cases hjn : j ≤ n
    · rw [dataBoxCoeff_one n h k β x l hjn]
      exact hs.1 j hj
    · exact dataBoxCoeff_eq_zero_of_gt_degree n h k β 1 x l (not_le.1 hjn)
  · rw [dataBoxCoeff_one n h k β x l hm_le]
    exact hs.2

include hk hβ hmin hatt in
/-- The second canonical coefficient of a datum is the explicit finite-part second coefficient
of its represented phase and amplitude (`m ≥ 2`). -/
theorem dataBoxCoeff_spatialSecondFace (hm : 2 ≤ multCount (ratioExp h k) l)
    (x : DataSpace (n + 1)) :
    dataBoxCoeff n h k β 1 x l (multCount (ratioExp h k) l - 2) =
      spatialSecondFace h k l β (dataPhase x) (dataAmplitude x) := by
  have hm_le : multCount (ratioExp h k) l - 2 ≤ n := by
    have := multCount_le_card (ratioExp h k) l
    omega
  rw [dataBoxCoeff_one n h k β x l hm_le, ← spatialSecondCoeff_eq n h k hk hβ
    (absSummable_xiCoord x) (absSummable_etaCoord x) (continuous_dataPhase x)
    (continuous_dataAmplitude x) (evalF_xiCoord_eq_dataPhase n x)
    (evalF_etaCoord_eq_dataAmplitude n x) hmin hatt hm]
  unfold spatialSecondCoeff
  rw [if_pos hm]

include hk hatt in
/-- The minimal ratio is a lattice point. -/
theorem exists_latticeQ_eq : ∃ m' : ℕ, l = (m' : ℝ) / latticeQ k := by
  obtain ⟨i, hi⟩ := hatt
  obtain ⟨m', -, hm'⟩ := ratio_mem_lattice k hk i (h i)
  exact ⟨m', by rw [← hi]; exact hm'⟩

include hk hβ hmin hatt in
/-- **The predecessor sum at `(λ, m−2)` is the leading term**: all predecessor coefficients vanish
except `C_{λ,m−1}(x) = F(x)`. -/
theorem predSum_spatial (hm : 2 ≤ multCount (ratioExp h k) l) (x : DataSpace (n + 1)) (N : ℝ) :
    predSum n h k β 1 x l (multCount (ratioExp h k) l - 2) N =
      dataBoxCoeff n h k β 1 x l (multCount (ratioExp h k) l - 1) *
        (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1)) := by
  have hm_le : multCount (ratioExp h k) l - 1 ≤ n := by
    have := multCount_le_card (ratioExp h k) l
    omega
  classical
  unfold predSum
  rw [Finset.sum_eq_single (l, multCount (ratioExp h k) l - 1)]
  · rfl
  · intro p hp hne
    unfold predSet at hp
    rw [Finset.mem_filter] at hp
    obtain ⟨-, hprec⟩ := hp
    unfold expTerm
    rcases hprec with hlt | ⟨heq, hgt⟩
    · rw [dataBoxCoeff_eq_zero_of_lt_min n h k hk β hβ one_pos x hmin hlt, zero_mul]
    · have hp2 : multCount (ratioExp h k) l - 1 < p.2 := by
        rcases Nat.lt_or_ge (multCount (ratioExp h k) l - 1) p.2 with hlt' | hge
        · exact hlt'
        · exfalso
          apply hne
          ext
          · exact heq
          · simp only
            omega
      rw [heq, (dataBoxCoeff_spatialFace n h k hk hβ hmin hatt x).1 p.2 hp2, zero_mul]
  · intro hnot
    exfalso
    apply hnot
    unfold predSet
    rw [Finset.mem_filter]
    refine ⟨?_, Or.inr ⟨rfl, by simp only; omega⟩⟩
    unfold indexSet
    rw [Finset.mem_product]
    refine ⟨?_, Finset.mem_range.2 (by simp only; omega)⟩
    obtain ⟨m', hm'⟩ := exists_latticeQ_eq n h k hk hatt
    simp only
    rw [hm']
    exact mem_latticeBelow (latticeQ_pos k hk) (by rw [← hm']; linarith)

include hk hβ hmin hatt in
/-- **The uniform spatial two-term theorem on coefficient balls** (`m ≥ 2`): uniformly on
`‖x‖ ≤ R`, `log N (Z_N(x)/(N^{−λ} log^{m−1} N) − F(x)) → B(x)`, with `F(x) = C_{λ,m−1}(x)` and
`B(x) = C_{λ,m−2}(x)` the canonical coefficients. -/
theorem tendstoUniformlyOn_spatialTwoTerm (hm : 2 ≤ multCount (ratioExp h k) l) (R : ℝ) :
    TendstoUniformlyOn (fun N x => Real.log N * (dataBoxIntegral n h k β N 1 x /
        (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1)) -
        dataBoxCoeff n h k β 1 x l (multCount (ratioExp h k) l - 1)))
      (fun x => dataBoxCoeff n h k β 1 x l (multCount (ratioExp h k) l - 2)) atTop
      (Metric.closedBall 0 R) := by
  have hj : multCount (ratioExp h k) l - 2 ≤ n := by
    have := multCount_le_card (ratioExp h k) l
    omega
  refine (tendstoUniformlyOn_orderedRemainder n h k hk β hβ one_pos
    (exists_latticeQ_eq n h k hk hatt) hj R).congr ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN x _
  change orderedRemainder n h k β 1 x l (multCount (ratioExp h k) l - 2) N = _
  unfold orderedRemainder
  rw [predSum_spatial n h k hk hβ hmin hatt hm x N]
  have hL : Real.log N ≠ 0 := (Real.log_pos hN).ne'
  have hNl : N ^ (-l) ≠ 0 := (Real.rpow_pos_of_pos (by linarith) _).ne'
  obtain ⟨q, hq⟩ : ∃ q, multCount (ratioExp h k) l - 2 = q := ⟨_, rfl⟩
  have hq1 : multCount (ratioExp h k) l - 1 = q + 1 := by omega
  rw [hq, hq1, pow_succ]
  field_simp

include hk hβ hmin hatt in
/-- The uniform spatial two-term theorem on compact sets of data. -/
theorem tendstoUniformlyOn_spatialTwoTerm_compact (hm : 2 ≤ multCount (ratioExp h k) l)
    {K : Set (DataSpace (n + 1))} (hK : IsCompact K) :
    TendstoUniformlyOn (fun N x => Real.log N * (dataBoxIntegral n h k β N 1 x /
        (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1)) -
        dataBoxCoeff n h k β 1 x l (multCount (ratioExp h k) l - 1)))
      (fun x => dataBoxCoeff n h k β 1 x l (multCount (ratioExp h k) l - 2)) atTop K := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  exact (tendstoUniformlyOn_spatialTwoTerm n h k hk hβ hmin hatt hm R).mono hR

include hk hβ in
/-- Continuity of the canonical coefficients in the data (Headline XXXIV, at `b = 1`). -/
theorem continuous_dataBoxCoeff_one (μ : ℝ) (j : ℕ) :
    Continuous fun x : DataSpace (n + 1) => dataBoxCoeff n h k β 1 x μ j :=
  continuous_taylorTree_coeff n h k hk β hβ one_pos μ j

/-! ### The `m = 1` branch: a pure remainder statement -/

include hk hβ hmin hatt in
/-- For `m = 1` the predecessor sum at the next lattice point `(λ + 1/Q, n)` is the leading term
`F(x) N^{−λ}`. -/
theorem predSum_spatial_one (hm : multCount (ratioExp h k) l = 1) (x : DataSpace (n + 1))
    (N : ℝ) :
    predSum n h k β 1 x (l + 1 / latticeQ k) n N = dataBoxCoeff n h k β 1 x l 0 * N ^ (-l) := by
  classical
  have hQ : 0 < latticeQ k := latticeQ_pos k hk
  have hQ' : (0 : ℝ) < latticeQ k := by exact_mod_cast hQ
  obtain ⟨m', hm'⟩ := exists_latticeQ_eq n h k hk hatt
  unfold predSum
  rw [Finset.sum_eq_single (l, 0)]
  · simp [expTerm]
  · intro p hp hne
    unfold predSet at hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hpI, hprec⟩ := hp
    unfold indexSet at hpI
    rw [Finset.mem_product] at hpI
    obtain ⟨hp1, hp2⟩ := hpI
    rw [mem_latticeBelow_iff hQ] at hp1
    obtain ⟨⟨m'', hm''⟩, -⟩ := hp1
    have hp2' : p.2 ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hp2)
    unfold expTerm
    rcases hprec with hlt | ⟨-, hgt⟩
    · have hle : p.1 ≤ l := by
        rw [hm'', hm'] at hlt ⊢
        rw [← add_div, div_lt_div_iff_of_pos_right hQ'] at hlt
        have h1 : m'' < m' + 1 := by exact_mod_cast hlt
        exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.lt_succ_iff.1 h1) hQ'.le
      rcases lt_or_eq_of_le hle with hlt' | heq
      · rw [dataBoxCoeff_eq_zero_of_lt_min n h k hk β hβ one_pos x hmin hlt', zero_mul]
      · have hp2pos : 0 < p.2 := by
          rcases Nat.eq_zero_or_pos p.2 with h0 | hpos
          · exact absurd (Prod.ext heq h0) hne
          · exact hpos
        rw [heq, (dataBoxCoeff_spatialFace n h k hk hβ hmin hatt x).1 p.2 (by omega), zero_mul]
    · exact absurd hgt (not_lt.2 hp2')
  · intro hnot
    exfalso
    apply hnot
    have h1Q : (0 : ℝ) < 1 / latticeQ k := by positivity
    unfold predSet
    rw [Finset.mem_filter]
    refine ⟨?_, Or.inl (by simp only; linarith)⟩
    unfold indexSet
    rw [Finset.mem_product]
    refine ⟨?_, Finset.mem_range.2 (Nat.succ_pos n)⟩
    simp only
    rw [hm']
    exact mem_latticeBelow hQ (by rw [← hm']; linarith)

include hk hβ hmin hatt in
/-- **The `m = 1` uniform statement**: `log N (N^λ Z_N(x) − F(x)) → 0` uniformly on coefficient
balls (the next-log coefficient is zero; the statement is log-amplified, so it does not follow from
the leading `o(1)` theorem alone). -/
theorem tendstoUniformlyOn_spatialTwoTerm_one (hm : multCount (ratioExp h k) l = 1) (R : ℝ) :
    TendstoUniformlyOn (fun N x => Real.log N *
        (dataBoxIntegral n h k β N 1 x / N ^ (-l) - dataBoxCoeff n h k β 1 x l 0))
      (fun _ => (0 : ℝ)) atTop (Metric.closedBall 0 R) := by
  have hQ : 0 < latticeQ k := latticeQ_pos k hk
  have hQ' : (0 : ℝ) < latticeQ k := by exact_mod_cast hQ
  have h1Q : (0 : ℝ) < 1 / latticeQ k := by positivity
  obtain ⟨m', hm'⟩ := exists_latticeQ_eq n h k hk hatt
  have hμ' : ∃ m'' : ℕ, l + 1 / latticeQ k = (m'' : ℝ) / latticeQ k :=
    ⟨m' + 1, by rw [hm']; push_cast; ring⟩
  have hord := tendstoUniformlyOn_orderedRemainder n h k hk β hβ one_pos hμ' le_rfl R
  have hbound : ∀ x ∈ Metric.closedBall (0 : DataSpace (n + 1)) R,
      |dataBoxCoeff n h k β 1 x (l + 1 / latticeQ k) n| ≤
        coeffBallBound n h k β 1 (l + 1 / latticeQ k) n R := fun x hx =>
    abs_dataBoxCoeff_le_ballBound n h k hk β hβ one_pos _ _ (by simpa using hx)
  have hrate : Tendsto (fun N : ℝ => (|coeffBallBound n h k β 1 (l + 1 / latticeQ k) n R| + 1) *
      (N ^ (-(1 / (latticeQ k : ℝ))) * (1 + Real.log N) ^ (n + 1))) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_mul_one_add_log_pow (n + 1) h1Q).const_mul
      (|coeffBallBound n h k β 1 (l + 1 / latticeQ k) n R| + 1)
    rwa [mul_zero] at this
  rw [Metric.tendstoUniformlyOn_iff] at hord ⊢
  intro ε hε
  filter_upwards [hord 1 one_pos, hrate.eventually (gt_mem_nhds hε),
    eventually_ge_atTop (Real.exp 1)] with N h1 hN hNe x hx
  have hN1 : 1 < N := lt_of_lt_of_le (by have := Real.add_one_lt_exp one_ne_zero; linarith) hNe
  have hN0 : 0 < N := by linarith
  have hL1 : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hN0]
    exact hNe
  have hL0 : 0 < Real.log N := by linarith
  have hid : Real.log N * (dataBoxIntegral n h k β N 1 x / N ^ (-l) -
      dataBoxCoeff n h k β 1 x l 0) =
      orderedRemainder n h k β 1 x (l + 1 / latticeQ k) n N *
        (N ^ (-(1 / (latticeQ k : ℝ))) * Real.log N ^ (n + 1)) := by
    unfold orderedRemainder
    rw [predSum_spatial_one n h k hk hβ hmin hatt hm x N]
    have hsplit : N ^ (-(l + 1 / (latticeQ k : ℝ))) = N ^ (-l) * N ^ (-(1 / (latticeQ k : ℝ))) := by
      rw [← Real.rpow_add hN0]
      congr 1
      ring
    rw [hsplit]
    have hNl : N ^ (-l) ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
    have hNq : N ^ (-(1 / (latticeQ k : ℝ))) ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
    have hLn : Real.log N ^ n ≠ 0 := pow_ne_zero _ hL0.ne'
    field_simp
    ring
  have hnn : (0 : ℝ) ≤ N ^ (-(1 / (latticeQ k : ℝ))) * Real.log N ^ (n + 1) :=
    (mul_pos (Real.rpow_pos_of_pos hN0 _) (pow_pos hL0 _)).le
  rw [dist_zero_left, Real.norm_eq_abs, hid, abs_mul, abs_of_nonneg hnn]
  have hor : |orderedRemainder n h k β 1 x (l + 1 / latticeQ k) n N| ≤
      |coeffBallBound n h k β 1 (l + 1 / latticeQ k) n R| + 1 := by
    have hd := h1 x hx
    rw [Real.dist_eq] at hd
    have hb := hbound x hx
    have := abs_sub_abs_le_abs_sub (orderedRemainder n h k β 1 x (l + 1 / latticeQ k) n N)
      (dataBoxCoeff n h k β 1 x (l + 1 / latticeQ k) n)
    rw [abs_sub_comm] at this
    linarith [le_abs_self (coeffBallBound n h k β 1 (l + 1 / latticeQ k) n R)]
  calc |orderedRemainder n h k β 1 x (l + 1 / latticeQ k) n N| *
        (N ^ (-(1 / (latticeQ k : ℝ))) * Real.log N ^ (n + 1))
      ≤ (|coeffBallBound n h k β 1 (l + 1 / latticeQ k) n R| + 1) *
        (N ^ (-(1 / (latticeQ k : ℝ))) * (1 + Real.log N) ^ (n + 1)) :=
        mul_le_mul hor (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hL0.le (by linarith) _) (by positivity)) (by positivity) (by positivity)
    _ < ε := hN


end Grammar
