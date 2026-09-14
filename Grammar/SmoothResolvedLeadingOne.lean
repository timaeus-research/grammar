/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothResolvedLeading

/-!
# The leading index of the partition function is a leading index of every observable

Consult #127, Unit D8a (second theorem). The leading-index condition of `SmoothResolvedLeading`
is stated at the level of the coefficient FUNCTIONALS: every `𝒯_{ν,p}` at an index preceding
`(μ₀, q₀)` vanishes identically. Here we show that it follows from the checkable condition on the
constant observable `1`, i.e. on the partition function `Z^U_N[1] = ∫_U e^{−N K∘π} dμ_U` itself:
if `(μ₀, q₀)` is the first nonzero index of the expansion of `Z^U_N[1]`
(`IsLeadingIndexOne`: the preceding coefficients of `1` vanish and `𝒯_{μ₀,q₀}[1] ≠ 0`), then every
coefficient functional at a preceding index vanishes identically (`isLeadingIndex_of_one`).

The argument is domination: `|Z^U_N[G]| ≤ M · Z^U_N[1]` for `|G| ≤ M` on the carrier of `μ_U`
(`abs_Z_le_mul_Z_one`). If some preceding coefficient of `G` were nonzero, the FIRST such index
`(ν, p)` (smallest exponent, then highest log power — extracted from the finite certified
spectrum) would make `N^{ν} (log N)^{−p} Z^U_N[G]` converge to a nonzero limit, while the
dominating `M · N^{ν}(log N)^{−p} Z^U_N[1]`, which equals
`M · N^{ν−μ₀}(log N)^{q₀−p} · N^{μ₀}(log N)^{−q₀} Z^U_N[1]`,
tends to `0` because `(ν, p)` precedes `(μ₀, q₀)` (`tendsto_normalised_scale_of_precedes`).

Consequence (with `SmoothResolvedLeading`): at the leading index of the partition function — the
RLCT index `(λ, m − 1)` of the pair `(K, prior)` when the leading coefficient is nonzero — the
resolved coefficient functional is a positive functional of order zero.
-/

open MeasureTheory Set Filter Topology Asymptotics
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport

namespace Grammar

namespace SmoothEngine

/-- `Precedes` is transitive. -/
theorem Precedes.trans {a c e : ℝ} {b d f : ℕ} (h₁ : Precedes a b c d) (h₂ : Precedes c d e f) :
    Precedes a b e f := by
  unfold Precedes at *
  rcases h₁ with h₁ | ⟨h₁, h₁'⟩ <;> rcases h₂ with h₂ | ⟨h₂, h₂'⟩
  · exact Or.inl (h₁.trans h₂)
  · exact Or.inl (h₂ ▸ h₁)
  · exact Or.inl (h₁ ▸ h₂)
  · exact Or.inr ⟨h₁.trans h₂, h₂'.trans h₁'⟩

theorem Precedes.exponent_le {a c : ℝ} {b d : ℕ} (h : Precedes a b c d) : a ≤ c := by
  unfold Precedes at h
  rcases h with h | ⟨h, -⟩
  · exact h.le
  · exact h.le

/-- A later power–log term, normalised at an EARLIER index, tends to zero. -/
theorem tendsto_normalised_scale_of_precedes {ν μ₀ : ℝ} {p q₀ : ℕ} (h : Precedes ν p μ₀ q₀) :
    Tendsto (fun N : ℝ => N ^ ν / Real.log N ^ p * (N ^ (-μ₀) * Real.log N ^ q₀)) atTop (𝓝 0) := by
  unfold Precedes at h
  rcases h with hlt | ⟨heq, hp⟩
  · -- a smaller exponent: `N^{-(μ₀ - ν)} log^{q₀}` is `o(1)`, times the bounded `(log N)^{-p}`
    have h0 : Tendsto (fun N : ℝ => N ^ (-(μ₀ - ν)) * Real.log N ^ q₀) atTop (𝓝 0) := by
      have h := isLittleO_scale_of_lt (A := 0) (sub_pos.2 hlt) q₀
      have h' : (fun N : ℝ => N ^ (-(μ₀ - ν)) * Real.log N ^ q₀) =o[atTop] fun _ : ℝ => (1 : ℝ) :=
        h.trans_isBigO (IsBigO.of_bound 1 (Eventually.of_forall fun N => by simp))
      exact (isLittleO_one_iff ℝ).1 h'
    have h1 := h0.zero_mul_isBoundedUnder_le (isBoundedUnder_inv_log_pow p)
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 1] with N hN
    have hNpos : 0 < N := by linarith
    rw [Real.rpow_neg hNpos.le, Real.rpow_sub hNpos, Real.rpow_neg hNpos.le]
    have hlog : Real.log N ^ p ≠ 0 := (pow_pos (Real.log_pos hN) _).ne'
    have hexp : N ^ μ₀ ≠ 0 := (Real.rpow_pos_of_pos hNpos _).ne'
    field_simp
  · -- the same exponent, a higher log power in the normalisation: `(log N)^{-(p - q₀)} → 0`
    have h0 : Tendsto (fun N : ℝ => (Real.log N ^ (p - q₀))⁻¹) atTop (𝓝 0) :=
      ((tendsto_pow_atTop (Nat.sub_ne_zero_of_lt hp)).comp Real.tendsto_log_atTop).inv_tendsto_atTop
    refine h0.congr' ?_
    filter_upwards [eventually_gt_atTop 1] with N hN
    have hNpos : 0 < N := by linarith
    rw [heq, Real.rpow_neg hNpos.le]
    have hlog : Real.log N ≠ 0 := (Real.log_pos hN).ne'
    have hexp : N ^ μ₀ ≠ 0 := (Real.rpow_pos_of_pos hNpos _).ne'
    have hsplit : Real.log N ^ p = Real.log N ^ q₀ * Real.log N ^ (p - q₀) := by
      rw [← pow_add, Nat.add_sub_cancel' hp.le]
    rw [hsplit]
    field_simp

variable {d : ℕ}

namespace ResolvedData

variable (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-- **Domination**: `|Z^U_N[G]| ≤ M · Z^U_N[1]` when `|G| ≤ M` on the carrier of `μ_U`. -/
theorem abs_Z_le_mul_Z_one {G : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) {M : ℝ}
    (hM : ∀ P, Ξ.R.gv P ∈ tsupport Ξ.prior → |G P| ≤ M) (N : ℝ) :
    |(Ξ.withF G hG).Z N| ≤ M * (Ξ.withF (fun _ => (1 : ℝ)) contMDiff_const).Z N := by
  change |∫ P, G P * Real.exp (-N * Ξ.K (Ξ.R.gv P)) ∂Ξ.μU| ≤
    M * ∫ P, (1 : ℝ) * Real.exp (-N * Ξ.K (Ξ.R.gv P)) ∂Ξ.μU
  have hint : Integrable (fun P => M * ((1 : ℝ) * Real.exp (-N * Ξ.K (Ξ.R.gv P)))) Ξ.μU :=
    (Ξ.integrable_mul_exp continuous_const N).const_mul M
  have hbound : ∀ᵐ P ∂Ξ.μU, ‖G P * Real.exp (-N * Ξ.K (Ξ.R.gv P))‖ ≤
      M * ((1 : ℝ) * Real.exp (-N * Ξ.K (Ξ.R.gv P))) := by
    filter_upwards [Ξ.ae_μU_mem] with P hP
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs (Real.exp _), abs_of_pos (Real.exp_pos _),
      one_mul]
    exact mul_le_mul_of_nonneg_right (hM P hP) (Real.exp_pos _).le
  have := norm_integral_le_of_norm_le hint hbound
  rw [Real.norm_eq_abs, integral_const_mul] at this
  exact this

/-- `(μ₀, q₀)` is the leading index of the partition function `Z^U_N[1]`: the preceding
coefficients of the constant observable vanish and the `(μ₀, q₀)` coefficient is nonzero. -/
def IsLeadingIndexOne (μ₀ : ℝ) (q₀ : ℕ) : Prop :=
  (∀ ν p, Precedes ν p μ₀ q₀ → (Ξ.withF (fun _ => (1 : ℝ)) contMDiff_const).coeff Y ν p = 0) ∧
    (Ξ.withF (fun _ => (1 : ℝ)) contMDiff_const).coeff Y μ₀ q₀ ≠ 0

variable {μ₀ : ℝ} {q₀ : ℕ}

/-- The normalised partition function converges to its leading coefficient. -/
theorem tendsto_normalised_Z_one (h : Ξ.IsLeadingIndexOne Y μ₀ q₀) :
    Tendsto (normalised μ₀ q₀ (Ξ.withF (fun _ => (1 : ℝ)) contMDiff_const).Z) atTop
      (𝓝 ((Ξ.withF (fun _ => (1 : ℝ)) contMDiff_const).coeff Y μ₀ q₀)) :=
  tendsto_normalised_of_leading
    ((Ξ.withF (fun _ => (1 : ℝ)) contMDiff_const).decomp Y).commonQ_pos
    ((Ξ.withF (fun _ => (1 : ℝ)) contMDiff_const).hasSmoothCoordFreeExpansion Y)
    ((Ξ.withF (fun _ => (1 : ℝ)) contMDiff_const).decomp Y).toCertificate.coeff_support h.1

/-- A smooth function on `U` is bounded on the carrier `π⁻¹(supp prior)` of `μ_U`. -/
theorem exists_bound_on_carrier {G : Ξ.R.U → ℝ} (hG : Continuous G) :
    ∃ M : ℝ, ∀ P, Ξ.R.gv P ∈ tsupport Ξ.prior → |G P| ≤ M := by
  obtain ⟨M, hM⟩ := (Ξ.R.isCompact_gv_preimage_tsupport Ξ.prior Ξ.prior_compact
    Ξ.prior_W).exists_bound_of_continuousOn hG.continuousOn
  exact ⟨M, fun P hP => by simpa using hM P hP⟩

/-- ★★★ **The leading index of the partition function is a leading index of every observable**:
if `(μ₀, q₀)` is the first nonzero index of the expansion of `Z^U_N[1]`, every coefficient
functional at a preceding index vanishes identically. -/
theorem isLeadingIndex_of_one (h : Ξ.IsLeadingIndexOne Y μ₀ q₀) : Ξ.IsLeadingIndex Y μ₀ q₀ := by
  classical
  intro ν p hνp G hG
  by_contra hne
  set Ξ' := Ξ.withF G hG with hΞ'
  set C := Ξ'.certificate Y with hC
  -- the finite set of preceding indices with nonzero coefficient
  set S : Finset PowerLogIndex := (spectrumLe C.Q C.D (μ₀ + 1)).filter fun r =>
    Precedes r.exponent r.logDegree μ₀ q₀ ∧ Ξ'.coeff Y r.exponent r.logDegree ≠ 0 with hS
  have hmemS : ∀ r : PowerLogIndex, Precedes r.exponent r.logDegree μ₀ q₀ →
      Ξ'.coeff Y r.exponent r.logDegree ≠ 0 → r ∈ S := fun r hr hne' => by
    obtain ⟨hlat, hD⟩ := C.coeff_support r.exponent r.logDegree hne'
    refine Finset.mem_filter.2 ⟨(mem_spectrumLe_iff C.Q_pos _ r).2 ⟨hlat, ?_, hD, ?_⟩, hr, hne'⟩
    · change r.exponent < max (μ₀ + 1 + 1) 1
      exact lt_max_of_lt_left (by linarith [hr.exponent_le])
    · linarith [hr.exponent_le]
  have hSne : S.Nonempty := ⟨⟨ν, p⟩, hmemS ⟨ν, p⟩ hνp hne⟩
  -- the first such index: minimal exponent, then maximal log power
  obtain ⟨r₁, hr₁S, hr₁min⟩ := S.exists_min_image (fun r => r.exponent) hSne
  set S₁ := S.filter fun r => r.exponent = r₁.exponent with hS₁
  have hS₁ne : S₁.Nonempty := ⟨r₁, Finset.mem_filter.2 ⟨hr₁S, rfl⟩⟩
  obtain ⟨r₂, hr₂S₁, hr₂max⟩ := S₁.exists_max_image (fun r => r.logDegree) hS₁ne
  obtain ⟨hr₂S, hr₂exp⟩ := Finset.mem_filter.1 hr₂S₁
  obtain ⟨-, hr₂prec, hr₂ne⟩ := Finset.mem_filter.1 hr₂S
  -- no index preceding `r₂` carries a nonzero coefficient
  have hlead₂ : ∀ ν' p', Precedes ν' p' r₂.exponent r₂.logDegree → Ξ'.coeff Y ν' p' = 0 := by
    intro ν' p' hprec
    by_contra hne'
    have hmem : (⟨ν', p'⟩ : PowerLogIndex) ∈ S := hmemS ⟨ν', p'⟩ (hprec.trans hr₂prec) hne'
    have h1 := hr₁min _ hmem
    unfold Precedes at hprec
    rcases hprec with hlt | ⟨heq, hp⟩
    · change r₁.exponent ≤ ν' at h1
      rw [hr₂exp] at hlt
      exact absurd (h1.trans_lt hlt) (lt_irrefl _)
    · have hmem₁ : (⟨ν', p'⟩ : PowerLogIndex) ∈ S₁ :=
        Finset.mem_filter.2 ⟨hmem, by change ν' = r₁.exponent; rw [heq, hr₂exp]⟩
      have := hr₂max _ hmem₁
      change p' ≤ r₂.logDegree at this
      omega
  -- the normalised integral of `G` at `r₂` converges to a nonzero limit …
  have hlimG : Tendsto (normalised r₂.exponent r₂.logDegree Ξ'.Z) atTop
      (𝓝 (Ξ'.coeff Y r₂.exponent r₂.logDegree)) :=
    tendsto_normalised_of_leading (Ξ'.decomp Y).commonQ_pos (Ξ'.hasSmoothCoordFreeExpansion Y)
      (Ξ'.decomp Y).toCertificate.coeff_support hlead₂
  -- … but is dominated by a quantity tending to zero
  obtain ⟨M, hM⟩ := Ξ.exists_bound_on_carrier hG.continuous
  have hdom : Tendsto (fun N : ℝ => M * (N ^ r₂.exponent / Real.log N ^ r₂.logDegree *
      (N ^ (-μ₀) * Real.log N ^ q₀)) *
        normalised μ₀ q₀ (Ξ.withF (fun _ => (1 : ℝ)) contMDiff_const).Z N) atTop (𝓝 0) := by
    have h1 := ((tendsto_normalised_scale_of_precedes hr₂prec).const_mul M).mul
      (Ξ.tendsto_normalised_Z_one Y h)
    rwa [mul_zero, zero_mul] at h1
  have hzero : Tendsto (normalised r₂.exponent r₂.logDegree Ξ'.Z) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hdom
    filter_upwards [eventually_gt_atTop 1] with N hN
    have hNpos : 0 < N := by linarith
    have hpos : 0 < N ^ r₂.exponent / Real.log N ^ r₂.logDegree :=
      div_pos (Real.rpow_pos_of_pos hNpos _) (pow_pos (Real.log_pos hN) _)
    have hZ1 : 0 ≤ (Ξ.withF (fun _ => (1 : ℝ)) contMDiff_const).Z N :=
      Ξ.Z_nonneg contMDiff_const (Eventually.of_forall fun _ => zero_le_one) N
    rw [Real.norm_eq_abs, normalised, abs_mul, abs_of_pos hpos]
    calc N ^ r₂.exponent / Real.log N ^ r₂.logDegree * |Ξ'.Z N|
        ≤ N ^ r₂.exponent / Real.log N ^ r₂.logDegree *
          (M * (Ξ.withF (fun _ => (1 : ℝ)) contMDiff_const).Z N) :=
          mul_le_mul_of_nonneg_left (Ξ.abs_Z_le_mul_Z_one hG hM N) hpos.le
      _ = M * (N ^ r₂.exponent / Real.log N ^ r₂.logDegree * (N ^ (-μ₀) * Real.log N ^ q₀)) *
          normalised μ₀ q₀ (Ξ.withF (fun _ => (1 : ℝ)) contMDiff_const).Z N := by
          unfold normalised
          have hlog : Real.log N ^ q₀ ≠ 0 := (pow_pos (Real.log_pos hN) _).ne'
          have hexp : N ^ μ₀ ≠ 0 := (Real.rpow_pos_of_pos hNpos _).ne'
          rw [Real.rpow_neg hNpos.le]
          field_simp
  exact hr₂ne (tendsto_nhds_unique hlimG hzero)

/-- ★★ At the leading index of the partition function, the coefficient functional is positive. -/
theorem coeff_nonneg_of_leading_one (h : Ξ.IsLeadingIndexOne Y μ₀ q₀) {G : Ξ.R.U → ℝ}
    (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G)
    (hG0 : ∀ P, Ξ.R.gv P ∈ tsupport Ξ.prior → 0 ≤ G P) :
    0 ≤ (Ξ.withF G hG).coeff Y μ₀ q₀ :=
  Ξ.coeff_nonneg_of_leading_of_nonneg_on Y (Ξ.isLeadingIndex_of_one Y h) hG hG0

/-- ★★ At the leading index of the partition function, the coefficient functional has order zero
and positive mass. -/
theorem abs_coeff_le_of_leading_one (h : Ξ.IsLeadingIndexOne Y μ₀ q₀) {G : Ξ.R.U → ℝ}
    (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) {M : ℝ}
    (hM : ∀ P, Ξ.R.gv P ∈ tsupport Ξ.prior → |G P| ≤ M) :
    |(Ξ.withF G hG).coeff Y μ₀ q₀| ≤
      M * (Ξ.withF (fun _ => (1 : ℝ)) contMDiff_const).coeff Y μ₀ q₀ :=
  Ξ.abs_coeff_le_of_leading Y (Ξ.isLeadingIndex_of_one Y h) hG hM

theorem coeff_one_pos_of_leading_one (h : Ξ.IsLeadingIndexOne Y μ₀ q₀) :
    0 < (Ξ.withF (fun _ => (1 : ℝ)) contMDiff_const).coeff Y μ₀ q₀ :=
  lt_of_le_of_ne (Ξ.coeff_one_nonneg_of_leading Y (Ξ.isLeadingIndex_of_one Y h)) h.2.symm

end ResolvedData

end SmoothEngine

end Grammar
