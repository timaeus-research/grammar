/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.ResolvedChartExpansion
import Grammar.GlobalExponentBound

/-!
# The leading-coefficient interface over chart–stratum pairs

The seventh module of the resolved-space programme (`tide-log/gpt6_bigpicture_v74.md`): a
**leading-term certificate** `HasLeadingTerm Z c λ k` for a function of the inverse temperature
`N` is the statement `Z(N) / (N^{-λ} (log N)^k) → c` (the scale `powLogScale` of
`GlobalExponentBound`) — the identified-leading-term theorems of
`ChartLeadingTerm` (`∫ F e^{-NK} ~ c N^{-λ} (log N)^{m-1}` with `c > 0`) are certificates with
`k = m − 1` (`hasLeadingTerm_of_isEquivalent`), and a certificate with `c ≠ 0` is such an
equivalence (`HasLeadingTerm.isEquivalent`), while `c = 0` records that `Z` is `o` of the scale.
Certificates are linear, and a term whose pair `(λ', k')` is **dominated** by `(λ, k)` (larger
exponent, or the same exponent and smaller log degree) is a certificate with coefficient `0` at
`(λ, k)` (`HasLeadingTerm.of_dominated`). Hence a finite sum of certified terms has the leading
term of the **extremal pair** — the minimal exponent and, among the terms attaining it, the maximal
log degree — with coefficient the sum of the coefficients of the **tied** terms
(`hasLeadingTerm_sum_of_extremal`, `hasLeadingTerm_sum_extremal`); if that sum cancels, the
certificate says only that the total is `o` of the scale.

Applied to the chart–stratum decomposition of CCXXIV: the resolved Boltzmann integral, as a
function of `N`, is the sum of the chart–stratum piece integrals for `N ≥ 0`
(`boltzmannIntegral_eq_sum_pieces`), so leading-term certificates for the pieces of the nonempty
strata, together with the vanishing of the divisor-free pieces at the extremal scale, give the
leading term of the resolved integral with coefficient the sum over the tied chart–stratum pairs
(`hasLeadingTerm_boltzmannIntegral`).

Non-claims: the per-piece certificates are hypotheses here — they are to be discharged from
hironaka's monomial data on each piece — and no positivity of the summed coefficient is inferred
for signed observables.
-/

open MeasureTheory Set Filter Topology Asymptotics
open scoped ENNReal

namespace Grammar

/-! ### Leading-term certificates -/

section Certificates

/-- **A leading-term certificate**: `Z(N) / (N^{-λ} (log N)^k) → c`. -/
def HasLeadingTerm (Z : ℝ → ℝ) (c lam : ℝ) (k : ℕ) : Prop :=
  Tendsto (fun N => Z N / powLogScale lam k N) atTop (𝓝 c)

variable {Z Z' : ℝ → ℝ} {c c' lam lam' : ℝ} {k k' : ℕ}

theorem HasLeadingTerm.congr' (h : HasLeadingTerm Z c lam k) (hZ : Z =ᶠ[atTop] Z') :
    HasLeadingTerm Z' c lam k :=
  Tendsto.congr' (hZ.mono fun N hN => by simp only [hN]) h

theorem HasLeadingTerm.add (h : HasLeadingTerm Z c lam k) (h' : HasLeadingTerm Z' c' lam k) :
    HasLeadingTerm (fun N => Z N + Z' N) (c + c') lam k := by
  refine (Tendsto.add h h').congr' (Eventually.of_forall fun N => ?_)
  simp only [add_div]

theorem HasLeadingTerm.const_mul (h : HasLeadingTerm Z c lam k) (a : ℝ) :
    HasLeadingTerm (fun N => a * Z N) (a * c) lam k := by
  refine (Tendsto.const_mul a h).congr' (Eventually.of_forall fun N => ?_)
  simp only [mul_div_assoc]

theorem HasLeadingTerm.sum {α : Type*} (s : Finset α) {Z : α → ℝ → ℝ} {c : α → ℝ}
    (h : ∀ j ∈ s, HasLeadingTerm (Z j) (c j) lam k) :
    HasLeadingTerm (fun N => ∑ j ∈ s, Z j N) (∑ j ∈ s, c j) lam k := by
  refine (tendsto_finsetSum s h).congr' (Eventually.of_forall fun N => ?_)
  simp only [Finset.sum_div]

theorem hasLeadingTerm_zero (lam : ℝ) (k : ℕ) : HasLeadingTerm (fun _ => 0) 0 lam k := by
  refine tendsto_const_nhds.congr' (Eventually.of_forall fun N => ?_)
  simp only [zero_div]

/-- The identified-leading-term form `Z ~ c · N^{-λ} (log N)^k` is a certificate (for `c = 0` the
equivalence forces `Z = 0` eventually). -/
theorem hasLeadingTerm_of_isEquivalent (h : Z ~[atTop] fun N => c * powLogScale lam k N) :
    HasLeadingTerm Z c lam k := by
  by_cases hc : c = 0
  · subst hc
    have h0 : Z =ᶠ[atTop] 0 := by
      have h' : (fun N : ℝ => (0 : ℝ) * powLogScale lam k N) = (0 : ℝ → ℝ) :=
        funext fun N => by simp
      rw [h'] at h
      exact isEquivalent_zero_iff_eventually_zero.1 h
    refine tendsto_const_nhds.congr' (h0.mono fun N hN => ?_)
    simp only [Pi.zero_apply] at hN
    simp only [hN, zero_div]
  · have hv : ∀ᶠ N in atTop, c * powLogScale lam k N ≠ 0 :=
      (eventually_gt_atTop 1).mono fun N hN => mul_ne_zero hc (powLogScale_pos _ _ hN).ne'
    have h1 := ((isEquivalent_iff_tendsto_one hv).1 h).mul_const c
    rw [one_mul] at h1
    refine h1.congr' ((eventually_gt_atTop 1).mono fun N hN => ?_)
    have hs := (powLogScale_pos lam k hN).ne'
    simp only [Pi.div_apply]
    field_simp

/-- A certificate with nonzero coefficient is the identified-leading-term equivalence. -/
theorem HasLeadingTerm.isEquivalent (h : HasLeadingTerm Z c lam k) (hc : c ≠ 0) :
    Z ~[atTop] fun N => c * powLogScale lam k N := by
  have hv : ∀ᶠ N in atTop, c * powLogScale lam k N ≠ 0 :=
    (eventually_gt_atTop 1).mono fun N hN => mul_ne_zero hc (powLogScale_pos _ _ hN).ne'
  refine (isEquivalent_iff_tendsto_one hv).2 ?_
  have h1 := h.div_const c
  rw [div_self hc] at h1
  refine h1.congr' ((eventually_gt_atTop 1).mono fun N hN => ?_)
  have hs := (powLogScale_pos lam k hN).ne'
  simp only [Pi.div_apply]
  field_simp

/-- A certificate with coefficient `0` is a little-`o` statement against the scale. -/
theorem HasLeadingTerm.isLittleO (h : HasLeadingTerm Z 0 lam k) :
    Z =o[atTop] powLogScale lam k :=
  (isLittleO_iff_tendsto' ((eventually_gt_atTop 1).mono fun _ hN h0 =>
    absurd h0 (powLogScale_pos _ _ hN).ne')).2 h

end Certificates

/-! ### Dominance of exponent pairs -/

section Dominance

/-- `(λ, k)` **dominates** `(λ', k')`: the scale `N^{-λ'} (log N)^{k'}` is `o(N^{-λ} (log N)^k)`. -/
def PairDominates (lam : ℝ) (k : ℕ) (lam' : ℝ) (k' : ℕ) : Prop :=
  lam < lam' ∨ (lam = lam' ∧ k' < k)

variable {lam lam' : ℝ} {k k' : ℕ}

theorem powLogScale_div {N : ℝ} (hN : 1 < N) :
    powLogScale lam' k' N / powLogScale lam k N =
      N ^ (lam - lam') * (Real.log N ^ k' / Real.log N ^ k) := by
  have hN0 : 0 < N := by linarith
  unfold powLogScale
  rw [mul_div_mul_comm, ← Real.rpow_sub hN0, show -lam' - -lam = lam - lam' by ring]

/-- A dominated scale is `o` of the dominating one. -/
theorem tendsto_powLogScale_div (hd : PairDominates lam k lam' k') :
    Tendsto (fun N => powLogScale lam' k' N / powLogScale lam k N) atTop (𝓝 0) := by
  rcases hd with hlt | ⟨heq, hk⟩
  · set δ := lam' - lam with hδ
    have hδpos : 0 < δ := by rw [hδ]; linarith
    have h1 : Tendsto (fun N : ℝ => Real.log N ^ k' / N ^ δ) atTop (𝓝 0) := by
      have := (isLittleO_log_rpow_rpow_atTop (k' : ℝ) hδpos).tendsto_div_nhds_zero
      refine this.congr' (Eventually.of_forall fun N => ?_)
      rw [Real.rpow_natCast]
    have h2 : IsBoundedUnder (· ≤ ·) atTop ((fun x => ‖x‖) ∘ fun N : ℝ => (Real.log N ^ k)⁻¹) := by
      refine isBoundedUnder_of_eventually_le (a := 1)
        ((eventually_ge_atTop (Real.exp 1)).mono fun N hN => ?_)
      have hlog : 1 ≤ Real.log N := by
        rw [Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos 1) hN)]
        exact hN
      have hpow : 1 ≤ Real.log N ^ k := one_le_pow₀ hlog
      simp only [Function.comp_apply, Real.norm_eq_abs]
      rw [abs_of_pos (inv_pos.2 (by linarith))]
      exact inv_le_one_of_one_le₀ hpow
    refine (h1.zero_mul_isBoundedUnder_le h2).congr' ((eventually_gt_atTop 1).mono fun N hN => ?_)
    have hN0 : 0 < N := by linarith
    beta_reduce
    rw [powLogScale_div hN, show lam - lam' = -δ by rw [hδ]; ring, Real.rpow_neg hN0.le]
    ring
  · have h1 : Tendsto (fun N : ℝ => (Real.log N ^ (k - k'))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (n := k - k') (by omega)).comp
        Real.tendsto_log_atTop)
    refine h1.congr' ((eventually_gt_atTop 1).mono fun N hN => ?_)
    beta_reduce
    rw [powLogScale_div hN, heq, sub_self, Real.rpow_zero, one_mul,
      show k = k' + (k - k') by omega, pow_add, Nat.add_sub_cancel_left,
      div_mul_cancel_left₀ (pow_ne_zero _ (Real.log_pos hN).ne')]

/-- A certified term whose pair is dominated is a certificate with coefficient `0` at the
dominating pair. -/
theorem HasLeadingTerm.of_dominated {Z : ℝ → ℝ} {c : ℝ} (h : HasLeadingTerm Z c lam' k')
    (hd : PairDominates lam k lam' k') : HasLeadingTerm Z 0 lam k := by
  have h1 := h.mul (tendsto_powLogScale_div hd)
  rw [mul_zero] at h1
  refine h1.congr' ((eventually_gt_atTop 1).mono fun N hN => ?_)
  have hs := (powLogScale_pos lam' k' hN).ne'
  rw [div_mul_div_comm, mul_comm (Z N), mul_div_mul_left _ _ hs]

end Dominance

/-! ### Finite sums: the extremal pair and the tied coefficients -/

section Sums

variable {α : Type*} (s : Finset α) (Z : α → ℝ → ℝ) (c lam : α → ℝ) (k : α → ℕ)

/-- **Summing certificates**: if `(λ₀, k₀)` is the extremal pair (no exponent below `λ₀`, no log
degree above `k₀` at exponent `λ₀`), the sum has leading term at `(λ₀, k₀)` with coefficient the
sum over the tied terms (possibly zero — cancellation). -/
theorem hasLeadingTerm_sum_of_extremal (lam₀ : ℝ) (k₀ : ℕ)
    (h : ∀ j ∈ s, HasLeadingTerm (Z j) (c j) (lam j) (k j)) (hlam : ∀ j ∈ s, lam₀ ≤ lam j)
    (hk : ∀ j ∈ s, lam j = lam₀ → k j ≤ k₀) :
    HasLeadingTerm (fun N => ∑ j ∈ s, Z j N)
      (∑ j ∈ s.filter (fun j => lam j = lam₀ ∧ k j = k₀), c j) lam₀ k₀ := by
  classical
  rw [Finset.sum_filter]
  refine HasLeadingTerm.sum s fun j hj => ?_
  by_cases htie : lam j = lam₀ ∧ k j = k₀
  · rw [if_pos htie]
    obtain ⟨h1, h2⟩ := htie
    have := h j hj
    rwa [h1, h2] at this
  · rw [if_neg htie]
    refine (h j hj).of_dominated ?_
    rcases lt_or_eq_of_le (hlam j hj) with hlt | heq
    · exact Or.inl hlt
    · refine Or.inr ⟨heq, lt_of_le_of_ne (hk j hj heq.symm) fun hkj => htie ⟨heq.symm, hkj⟩⟩

variable (hs : s.Nonempty)

/-- The extremal exponent of a finite family: the minimum. -/
noncomputable def extremalExponent : ℝ := s.inf' hs lam

theorem extremalExponent_le {j : α} (hj : j ∈ s) : extremalExponent s lam hs ≤ lam j :=
  Finset.inf'_le lam hj

theorem exists_extremalExponent_eq : ∃ j ∈ s, lam j = extremalExponent s lam hs := by
  obtain ⟨j, hj, h⟩ := Finset.exists_mem_eq_inf' hs lam
  exact ⟨j, hj, h.symm⟩

theorem nonempty_filter_extremal : (s.filter fun j => lam j = extremalExponent s lam hs).Nonempty :=
  by
  obtain ⟨j, hj, h⟩ := exists_extremalExponent_eq s lam hs
  exact ⟨j, Finset.mem_filter.2 ⟨hj, h⟩⟩

/-- The extremal log degree: the maximum over the terms attaining the extremal exponent. -/
noncomputable def extremalDegree : ℕ :=
  (s.filter fun j => lam j = extremalExponent s lam hs).sup' (nonempty_filter_extremal s lam hs) k

theorem le_extremalDegree {j : α} (hj : j ∈ s) (h : lam j = extremalExponent s lam hs) :
    k j ≤ extremalDegree s lam k hs :=
  Finset.le_sup' k (Finset.mem_filter.2 ⟨hj, h⟩)

/-- **The leading term of a finite sum of certified terms**, at the extremal pair, with the tied
coefficients summed. -/
theorem hasLeadingTerm_sum_extremal (h : ∀ j ∈ s, HasLeadingTerm (Z j) (c j) (lam j) (k j)) :
    HasLeadingTerm (fun N => ∑ j ∈ s, Z j N)
      (∑ j ∈ s.filter (fun j => lam j = extremalExponent s lam hs ∧
        k j = extremalDegree s lam k hs), c j)
      (extremalExponent s lam hs) (extremalDegree s lam k hs) :=
  hasLeadingTerm_sum_of_extremal s Z c lam k _ _ h (fun _ hj => extremalExponent_le s lam hs hj)
    fun _ hj hj' => le_extremalDegree s lam k hs hj hj'

end Sums

/-! ### The resolved Boltzmann integral as a function of the inverse temperature -/

namespace ResolutionCover

variable {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι)

/-- The chart density of the Boltzmann integrand at inverse temperature `N`:
`1_{dom_i} · |det Dφ_i| · (ρ_i ∘ Φ_i) · (e^{-NK} p) ∘ Φ_i` (the Boltzmann chart weight, without the
sign hypothesis on `N`). -/
noncomputable def boltzmannChartDensity (i : ι) (N : ℝ) (K : (Fin d → ℝ) → ℝ) (p : TubeWeight d)
    (y : Fin d → ℝ) : ℝ :=
  (R.chart i).dom.indicator (fun y => (R.chart i).jac y * (R.weight i ((R.chart i).Φ y) *
    (Real.exp (-N * K ((R.chart i).Φ y)) * p.w ((R.chart i).Φ y)))) y

theorem chartWeight_boltzmann_w (i : ι) (N : ℝ) (hN : 0 ≤ N) (K : (Fin d → ℝ) → ℝ)
    (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x) (p : TubeWeight d) :
    (R.chartWeight i (TubeWeight.boltzmann N hN K hK hK0 p)).w =
      R.boltzmannChartDensity i N K p := rfl

/-- The chart–stratum piece integral `Z_{N; i, I}[F]`. -/
noncomputable def pieceIntegral (D : ι → Finset (Fin d)) (ε : ℝ) (i : ι) (I : Finset (Fin d))
    (F K : (Fin d → ℝ) → ℝ) (p : TubeWeight d) (N : ℝ) : ℝ :=
  ∫ y in sizePiece (D i) ε I, R.boltzmannChartDensity i N K p y * F ((R.chart i).φ y)

/-- The resolved Boltzmann integral `Z_N[F] = ∫_{⋃ φ_i(dom_i)} F e^{-NK} p dx`. -/
noncomputable def boltzmannIntegral (F K : (Fin d → ℝ) → ℝ) (p : TubeWeight d) (N : ℝ) : ℝ :=
  R.coverIntegral (fun x => F x * p.w x) (fun x => -N * K x)

theorem integrable_boltzmann {F K : (Fin d → ℝ) → ℝ} {p : TubeWeight d}
    (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
    (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x) {N : ℝ} (hN : 0 ≤ N) :
    Integrable (fun x => F x * p.w x * Real.exp (-N * K x))
      (volume.restrict (⋃ i, R.image i)) := by
  have h := hF.bdd_mul (c := 1) (f := fun x => Real.exp (-N * K x))
    (Real.measurable_exp.comp (measurable_const.mul hK)).aestronglyMeasurable
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_mul]
      exact neg_nonpos.2 (mul_nonneg hN (hK0 x)))
  refine h.congr (Eventually.of_forall fun x => ?_)
  ring

/-- **The resolved Boltzmann integral is the sum of the chart–stratum piece integrals** for every
`N ≥ 0` (CCXXIV in the form of functions of `N`). -/
theorem boltzmannIntegral_eq_sum_pieces (D : ι → Finset (Fin d)) (ε : ℝ)
    {F K : (Fin d → ℝ) → ℝ} {p : TubeWeight d} (hFm : Measurable F)
    (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
    (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x) {N : ℝ} (hN : 0 ≤ N) :
    R.boltzmannIntegral F K p N =
      ∑ i, ((∑ I ∈ (D i).powerset.filter (fun I => I.Nonempty), R.pieceIntegral D ε i I F K p N) +
        R.pieceIntegral D ε i ∅ F K p N) := by
  unfold boltzmannIntegral pieceIntegral
  rw [R.coverIntegral_eq_sum_chart_pieces N hN K hK hK0 p D ε hFm
    (R.integrable_boltzmann hF hK hK0 hN)]
  rfl

/-- **The leading-coefficient interface**: leading-term certificates for the chart–stratum piece
integrals of the nonempty strata, an extremal pair `(λ₀, k₀)` for them, and the vanishing of the
divisor-free pieces at that scale give the leading term of the resolved Boltzmann integral, with
coefficient the sum over the tied chart–stratum pairs. -/
theorem hasLeadingTerm_boltzmannIntegral (D : ι → Finset (Fin d)) (ε : ℝ)
    {F K : (Fin d → ℝ) → ℝ} {p : TubeWeight d} (hFm : Measurable F)
    (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
    (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x)
    (c lam : ι → Finset (Fin d) → ℝ) (k : ι → Finset (Fin d) → ℕ) (lam₀ : ℝ) (k₀ : ℕ)
    (hpiece : ∀ i, ∀ I ∈ (D i).powerset.filter (fun I => I.Nonempty),
      HasLeadingTerm (R.pieceIntegral D ε i I F K p) (c i I) (lam i I) (k i I))
    (hlam : ∀ i, ∀ I ∈ (D i).powerset.filter (fun I => I.Nonempty), lam₀ ≤ lam i I)
    (hk : ∀ i, ∀ I ∈ (D i).powerset.filter (fun I => I.Nonempty), lam i I = lam₀ → k i I ≤ k₀)
    (hempty : ∀ i, HasLeadingTerm (R.pieceIntegral D ε i ∅ F K p) 0 lam₀ k₀) :
    HasLeadingTerm (R.boltzmannIntegral F K p)
      (∑ i, ∑ I ∈ ((D i).powerset.filter (fun I => I.Nonempty)).filter
        (fun I => lam i I = lam₀ ∧ k i I = k₀), c i I) lam₀ k₀ := by
  have hsum := HasLeadingTerm.sum (lam := lam₀) (k := k₀) Finset.univ
    (Z := fun i N => (∑ I ∈ (D i).powerset.filter (fun I => I.Nonempty),
      R.pieceIntegral D ε i I F K p N) + R.pieceIntegral D ε i ∅ F K p N)
    (c := fun i => (∑ I ∈ ((D i).powerset.filter (fun I => I.Nonempty)).filter
      (fun I => lam i I = lam₀ ∧ k i I = k₀), c i I) + 0)
    fun i _ => (hasLeadingTerm_sum_of_extremal _ (fun I => R.pieceIntegral D ε i I F K p) (c i)
      (lam i) (k i) lam₀ k₀ (hpiece i) (hlam i) (hk i)).add (hempty i)
  simp only [add_zero] at hsum
  exact hsum.congr' ((eventually_ge_atTop 0).mono fun N hN =>
    (R.boltzmannIntegral_eq_sum_pieces D ε hFm hF hK hK0 hN).symm)

end ResolutionCover

end Grammar
