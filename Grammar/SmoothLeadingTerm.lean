/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothExpansionCertificate

/-!
# The leading term of a smooth coordinate-free expansion

Consult #127, Unit D8a (abstract half). For a function `Z` with a smooth coordinate-free
expansion `Z(N) ~ ∑ c_{μ,q} N^{−μ} (log N)^q` (`HasSmoothCoordFreeExpansion`) whose
coefficients vanish at every index PRECEDING `(μ₀, q₀)` in the asymptotic order — smaller
exponent, or the same exponent with a higher logarithmic power (`Precedes`) — the normalised
function `N^{μ₀} (log N)^{−q₀} Z(N)` converges to `c_{μ₀,q₀}`
(`tendsto_normalised_of_leading`). This is the analytic input for the positivity of the
leading coefficient functional of the resolved expansion (`SmoothResolvedLeading`).

Non-claims: no existence of a first nonzero index (conditional on the vanishing hypothesis);
the normalisation is stated for `N → ∞` along the reals.
-/

open Filter Topology Asymptotics

namespace Grammar

namespace SmoothEngine

/-- `(ν, p)` precedes `(μ₀, q₀)` in the asymptotic order: a smaller exponent, or the same
exponent with a higher logarithmic power. -/
def Precedes (ν : ℝ) (p : ℕ) (μ₀ : ℝ) (q₀ : ℕ) : Prop := ν < μ₀ ∨ (ν = μ₀ ∧ q₀ < p)

/-- The normalised function `N^{μ₀} (log N)^{−q₀} Z(N)`. -/
noncomputable def normalised (μ₀ : ℝ) (q₀ : ℕ) (Z : ℝ → ℝ) (N : ℝ) : ℝ :=
  N ^ μ₀ / Real.log N ^ q₀ * Z N

theorem normalised_add (μ₀ : ℝ) (q₀ : ℕ) (Z₁ Z₂ : ℝ → ℝ) (N : ℝ) :
    normalised μ₀ q₀ (fun N => Z₁ N + Z₂ N) N = normalised μ₀ q₀ Z₁ N + normalised μ₀ q₀ Z₂ N := by
  unfold normalised; ring

theorem normalised_sum {ι : Type*} (s : Finset ι) (μ₀ : ℝ) (q₀ : ℕ) (Z : ι → ℝ → ℝ) (N : ℝ) :
    normalised μ₀ q₀ (fun N => ∑ i ∈ s, Z i N) N = ∑ i ∈ s, normalised μ₀ q₀ (Z i) N := by
  unfold normalised; rw [Finset.mul_sum]

theorem normalised_const_mul (μ₀ : ℝ) (q₀ : ℕ) (c : ℝ) (Z : ℝ → ℝ) (N : ℝ) :
    normalised μ₀ q₀ (fun N => c * Z N) N = c * normalised μ₀ q₀ Z N := by
  unfold normalised; ring

theorem normalised_nonneg {μ₀ : ℝ} {q₀ : ℕ} {Z : ℝ → ℝ} {N : ℝ} (hN : 1 < N) (hZ : 0 ≤ Z N) :
    0 ≤ normalised μ₀ q₀ Z N := by
  unfold normalised
  have h1 : 0 < N ^ μ₀ := Real.rpow_pos_of_pos (by linarith) _
  have h2 : 0 < Real.log N ^ q₀ := pow_pos (Real.log_pos hN) _
  positivity

/-- The inverse powers of the logarithm are eventually bounded by one. -/
theorem isBoundedUnder_inv_log_pow (q₀ : ℕ) :
    IsBoundedUnder (· ≤ ·) atTop ((‖·‖) ∘ fun N : ℝ => (Real.log N ^ q₀)⁻¹) := by
  refine ⟨1, ?_⟩
  rw [eventually_map]
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with N hN
  have hlog : 1 ≤ Real.log N := by
    have := Real.log_le_log (Real.exp_pos 1) hN
    rwa [Real.log_exp] at this
  have hpow : 1 ≤ Real.log N ^ q₀ := one_le_pow₀ hlog
  simp only [Function.comp_apply, Real.norm_eq_abs, abs_inv]
  rw [abs_of_pos (by linarith : (0 : ℝ) < Real.log N ^ q₀)]
  exact inv_le_one_of_one_le₀ hpow

/-- The normalised power–log term `N^{μ₀} (log N)^{−q₀} · N^{−α} (log N)^j` converges to `1` at the
leading index and to `0` at every index not preceding it. -/
theorem tendsto_normalised_scale (μ₀ : ℝ) (q₀ : ℕ) (q : PowerLogIndex)
    (hq : ¬ Precedes q.exponent q.logDegree μ₀ q₀) :
    Tendsto (normalised μ₀ q₀ q.scale) atTop
      (𝓝 (if q.exponent = μ₀ ∧ q.logDegree = q₀ then 1 else 0)) := by
  unfold Precedes at hq
  push Not at hq
  obtain ⟨hle, hdeg⟩ := hq
  rcases hle.lt_or_eq with hlt | heq'
  · -- a larger exponent: the term is `o(1)` times a bounded factor
    rw [if_neg (fun h => absurd h.1 hlt.ne')]
    have h0 : Tendsto (fun N : ℝ => N ^ (-(q.exponent - μ₀)) * Real.log N ^ q.logDegree) atTop
        (𝓝 0) := by
      have h := isLittleO_scale_of_lt (A := 0) (sub_pos.2 hlt) q.logDegree
      have h' : (fun N : ℝ => N ^ (-(q.exponent - μ₀)) * Real.log N ^ q.logDegree) =o[atTop]
          fun _ : ℝ => (1 : ℝ) :=
        h.trans_isBigO (IsBigO.of_bound 1 (Eventually.of_forall fun N => by simp))
      exact (isLittleO_one_iff ℝ).1 h'
    have h1 := h0.zero_mul_isBoundedUnder_le (isBoundedUnder_inv_log_pow q₀)
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 1] with N hN
    have hNpos : 0 < N := by linarith
    unfold normalised PowerLogIndex.scale
    rw [Real.rpow_neg hNpos.le, Real.rpow_sub hNpos, Real.rpow_neg hNpos.le]
    have hlog : Real.log N ^ q₀ ≠ 0 := (pow_pos (Real.log_pos hN) _).ne'
    have hexp : N ^ q.exponent ≠ 0 := (Real.rpow_pos_of_pos hNpos _).ne'
    field_simp
  · -- the same exponent
    have heq : q.exponent = μ₀ := heq'.symm
    by_cases hd : q.logDegree = q₀
    · rw [if_pos ⟨heq, hd⟩]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop 1] with N hN
      have hNpos : 0 < N := by linarith
      unfold normalised PowerLogIndex.scale
      rw [heq, hd, Real.rpow_neg hNpos.le]
      have hlog : Real.log N ^ q₀ ≠ 0 := (pow_pos (Real.log_pos hN) _).ne'
      have hexp : N ^ μ₀ ≠ 0 := (Real.rpow_pos_of_pos hNpos _).ne'
      field_simp
    · -- a lower logarithmic power: `(log N)^{−(q₀ − j)} → 0`
      rw [if_neg (fun h => hd h.2)]
      have hdlt : q.logDegree < q₀ := lt_of_le_of_ne (by exact_mod_cast hdeg heq) hd
      have h0 : Tendsto (fun N : ℝ => (Real.log N ^ (q₀ - q.logDegree))⁻¹) atTop (𝓝 0) :=
        ((tendsto_pow_atTop (Nat.sub_ne_zero_of_lt hdlt)).comp
          Real.tendsto_log_atTop).inv_tendsto_atTop
      refine h0.congr' ?_
      filter_upwards [eventually_gt_atTop 1] with N hN
      have hNpos : 0 < N := by linarith
      unfold normalised PowerLogIndex.scale
      rw [heq, Real.rpow_neg hNpos.le]
      have hlog : Real.log N ≠ 0 := (Real.log_pos hN).ne'
      have hexp : N ^ μ₀ ≠ 0 := (Real.rpow_pos_of_pos hNpos _).ne'
      have hsplit : Real.log N ^ q₀ =
          Real.log N ^ q.logDegree * Real.log N ^ (q₀ - q.logDegree) := by
        rw [← pow_add, Nat.add_sub_cancel' hdlt.le]
      rw [hsplit]
      field_simp

/-- Membership in the truncated spectrum. -/
theorem mem_spectrumLe_iff {Q D : ℕ} (hQ : 0 < Q) (A : ℝ) (q : PowerLogIndex) :
    q ∈ spectrumLe Q D A ↔
      (∃ m : ℕ, q.exponent = (m : ℝ) / Q) ∧ q.exponent < cutoffExponent A ∧ q.logDegree ≤ D ∧
        q.exponent ≤ A := by
  unfold spectrumLe spectrumBelow
  rw [Finset.mem_filter, Finset.mem_map]
  constructor
  · rintro ⟨⟨⟨μ, j⟩, hmem, rfl⟩, hle⟩
    obtain ⟨hμ, hj⟩ := Finset.mem_product.1 hmem
    obtain ⟨⟨m, hm⟩, hlt⟩ := (mem_latticeBelow_iff hQ).1 hμ
    exact ⟨⟨m, hm⟩, hlt, Nat.lt_succ_iff.1 (Finset.mem_range.1 hj), hle⟩
  · rintro ⟨⟨m, hm⟩, hlt, hj, hle⟩
    refine ⟨⟨(q.exponent, q.logDegree), Finset.mem_product.2 ⟨?_, ?_⟩, rfl⟩, hle⟩
    · exact (mem_latticeBelow_iff hQ).2 ⟨⟨m, hm⟩, hlt⟩
    · exact Finset.mem_range.2 (Nat.lt_succ_of_le hj)

/-- ★★★ **The leading term**: if all coefficients preceding `(μ₀, q₀)` vanish, the normalised
function `N^{μ₀} (log N)^{−q₀} Z(N)` converges to `c_{μ₀,q₀}`. -/
theorem tendsto_normalised_of_leading {Z : ℝ → ℝ} {c : ℝ → ℕ → ℝ} {Q D : ℕ} (hQ : 0 < Q)
    (h : HasSmoothCoordFreeExpansion Z c Q D)
    (hsupp : ∀ μ q, c μ q ≠ 0 → (∃ m : ℕ, μ = (m : ℝ) / Q) ∧ q ≤ D)
    {μ₀ : ℝ} {q₀ : ℕ} (hlead : ∀ ν p, Precedes ν p μ₀ q₀ → c ν p = 0) :
    Tendsto (normalised μ₀ q₀ Z) atTop (𝓝 (c μ₀ q₀)) := by
  classical
  set A : ℝ := μ₀ + 1 with hA
  set S : ℝ → ℝ := fun N => ∑ q ∈ spectrumLe Q D A, c q.exponent q.logDegree * q.scale N with hS
  -- the remainder
  have hrem : Tendsto (normalised μ₀ q₀ fun N => Z N - S N) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℝ => (Z N - S N) / N ^ (-A)) atTop (𝓝 0) :=
      (h A).tendsto_div_nhds_zero
    have h2 : Tendsto (fun N : ℝ => N ^ (-(1 : ℝ)) * (Real.log N ^ q₀)⁻¹) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop one_pos).zero_mul_isBoundedUnder_le (isBoundedUnder_inv_log_pow q₀)
    have h3 := h1.mul h2
    rw [zero_mul] at h3
    refine h3.congr' ?_
    filter_upwards [eventually_gt_atTop 1] with N hN
    have hNpos : 0 < N := by linarith
    unfold normalised
    have hlog : Real.log N ^ q₀ ≠ 0 := (pow_pos (Real.log_pos hN) _).ne'
    have hμ : N ^ μ₀ ≠ 0 := (Real.rpow_pos_of_pos hNpos _).ne'
    have hA' : N ^ (-A) = (N ^ μ₀ * N)⁻¹ := by
      rw [Real.rpow_neg hNpos.le, hA, Real.rpow_add hNpos, Real.rpow_one]
    have hone : N ^ (-(1 : ℝ)) = N⁻¹ := by rw [Real.rpow_neg hNpos.le, Real.rpow_one]
    rw [hA', hone]
    field_simp
  -- the spectral sum
  have hspec : Tendsto (normalised μ₀ q₀ S) atTop (𝓝 (∑ q ∈ spectrumLe Q D A,
      c q.exponent q.logDegree * if q.exponent = μ₀ ∧ q.logDegree = q₀ then 1 else 0)) := by
    have : normalised μ₀ q₀ S = fun N => ∑ q ∈ spectrumLe Q D A,
        c q.exponent q.logDegree * normalised μ₀ q₀ q.scale N := by
      funext N
      rw [hS, normalised_sum]
      exact Finset.sum_congr rfl fun q _ => normalised_const_mul μ₀ q₀ _ _ N
    rw [this]
    refine tendsto_finsetSum _ fun q _ => ?_
    by_cases hp : Precedes q.exponent q.logDegree μ₀ q₀
    · rw [hlead _ _ hp]
      simp only [zero_mul]
      exact tendsto_const_nhds
    · exact (tendsto_normalised_scale μ₀ q₀ q hp).const_mul _
  -- the limit of the spectral sum is the leading coefficient
  have hval : (∑ q ∈ spectrumLe Q D A,
      c q.exponent q.logDegree * if q.exponent = μ₀ ∧ q.logDegree = q₀ then 1 else 0) =
        c μ₀ q₀ := by
    have hterm : ∀ q ∈ spectrumLe Q D A, (c q.exponent q.logDegree *
        if q.exponent = μ₀ ∧ q.logDegree = q₀ then 1 else 0) =
          if q = ⟨μ₀, q₀⟩ then c μ₀ q₀ else 0 := fun q _ => by
      by_cases hq : q = ⟨μ₀, q₀⟩
      · subst hq; simp
      · have : ¬ (q.exponent = μ₀ ∧ q.logDegree = q₀) := fun h => hq (by
          cases q; simp only [PowerLogIndex.mk.injEq]; exact h)
        rw [if_neg this, if_neg hq, mul_zero]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
    split_ifs with hmem
    · rfl
    · by_contra hne
      obtain ⟨hlat, hD⟩ := hsupp μ₀ q₀ (Ne.symm hne)
      refine hmem ((mem_spectrumLe_iff hQ A ⟨μ₀, q₀⟩).2 ⟨hlat, ?_, hD, by simp [hA]⟩)
      change μ₀ < max (A + 1) 1
      rw [hA]
      exact lt_max_of_lt_left (by linarith)
  rw [hval] at hspec
  have hsum := hrem.add hspec
  rw [zero_add] at hsum
  refine hsum.congr' (Eventually.of_forall fun N => ?_)
  rw [← normalised_add]
  congr 1
  funext N
  ring

end SmoothEngine

end Grammar
