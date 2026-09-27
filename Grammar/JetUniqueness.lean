/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.GammaLogMomentsIteratedDeriv

/-!
# Uniqueness of a finite jet from scaled remainder limits

If `(f(u) − Σ_{j≤n} h_j u^j)/u^n → 0` and `(f(u) − Σ_{j<n} c_j u^j)/u^n → q` as `u → 0⁺`, then
`h_j = c_j` for `j < n` and `h_n = q` (★★ `jet_unique_of_scaled_remainders`): the Taylor jet of
`f` to order `n` is read off from any principal-part limit of order `n`.  Proof by induction on
`n`: multiplying by `u^{n+1}` both unscaled remainders vanish, so `h₀ = c₀`; then
`f ↦ (f − h₀)/u` with the coefficient sequences shifted.  Neither Laurent series nor
l'Hôpital is used (Astra round 24).  This is the reusable replacement for the order-by-order
pole matching of DCLXXI, consumed by the all-depth jet theorem.  Zero `sorry`/`axiom`.
-/

open Filter Topology Finset

namespace Grammar

/-- `Σ_{j<n+1} d_j u^j = d_0 + u Σ_{j<n} d_{j+1} u^j`. -/
theorem sum_range_succ_pow_shift (d : ℕ → ℂ) (n : ℕ) (u : ℂ) :
    ∑ j ∈ range (n + 1), d j * u ^ j = d 0 + u * ∑ j ∈ range n, d (j + 1) * u ^ j := by
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [pow_zero, mul_one, pow_succ]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- A finite polynomial sum in a real variable tends to its constant term at `0⁺`. -/
theorem tendsto_sum_range_pow_nhdsGT (d : ℕ → ℂ) (n : ℕ) :
    Tendsto (fun u : ℝ => ∑ j ∈ range (n + 1), d j * (u : ℂ) ^ j) (𝓝[>] 0) (𝓝 (d 0)) := by
  have hcont : Continuous (fun u : ℝ => ∑ j ∈ range (n + 1), d j * (u : ℂ) ^ j) :=
    continuous_finsetSum _ fun j _ => by fun_prop
  have := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  simpa [Finset.sum_range_succ'] using this

theorem tendsto_ofReal_nhdsGT_zero : Tendsto (fun u : ℝ => (u : ℂ)) (𝓝[>] 0) (𝓝 0) := by
  have := (Complex.continuous_ofReal.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  simpa using this

/-- ★★ **Uniqueness of the order-`n` jet from scaled remainders.** -/
theorem jet_unique_of_scaled_remainders (n : ℕ) (f : ℝ → ℂ) (h c : ℕ → ℂ) (q : ℂ)
    (hh : Tendsto (fun u : ℝ => (f u - ∑ j ∈ range (n + 1), h j * (u : ℂ) ^ j) / (u : ℂ) ^ n)
      (𝓝[>] 0) (𝓝 0))
    (hc : Tendsto (fun u : ℝ => (f u - ∑ j ∈ range n, c j * (u : ℂ) ^ j) / (u : ℂ) ^ n)
      (𝓝[>] 0) (𝓝 q)) :
    (∀ j < n, h j = c j) ∧ h n = q := by
  induction n generalizing f h c q with
  | zero =>
    simp only [zero_add, Finset.sum_range_one, pow_zero, mul_one, Finset.sum_range_zero,
      sub_zero, div_one] at hh hc
    refine ⟨fun j hj => absurd hj (Nat.not_lt_zero _), ?_⟩
    have h1 : Tendsto (fun u : ℝ => f u) (𝓝[>] 0) (𝓝 (h 0)) := by
      have := hh.add_const (h 0)
      simpa using this
    exact tendsto_nhds_unique h1 hc
  | succ n ih =>
    have hu0 : ∀ᶠ u : ℝ in 𝓝[>] 0, (u : ℂ) ≠ 0 := by
      filter_upwards [self_mem_nhdsWithin] with u hu
      exact_mod_cast (ne_of_gt hu)
    have hpow : Tendsto (fun u : ℝ => (u : ℂ) ^ (n + 1)) (𝓝[>] 0) (𝓝 0) := by
      have := tendsto_ofReal_nhdsGT_zero.pow (n + 1)
      rwa [zero_pow (Nat.succ_ne_zero n)] at this
    -- the unscaled remainders vanish
    have hh0 : Tendsto (fun u : ℝ => f u - ∑ j ∈ range (n + 1 + 1), h j * (u : ℂ) ^ j)
        (𝓝[>] 0) (𝓝 0) := by
      have := hh.mul hpow
      rw [zero_mul] at this
      refine this.congr' ?_
      filter_upwards [hu0] with u hu
      field_simp
    have hc0 : Tendsto (fun u : ℝ => f u - ∑ j ∈ range (n + 1), c j * (u : ℂ) ^ j)
        (𝓝[>] 0) (𝓝 0) := by
      have := hc.mul hpow
      rw [mul_zero] at this
      refine this.congr' ?_
      filter_upwards [hu0] with u hu
      field_simp
    have hf_h : Tendsto f (𝓝[>] 0) (𝓝 (h 0)) := by
      have := hh0.add (tendsto_sum_range_pow_nhdsGT h (n + 1))
      rw [zero_add] at this
      refine this.congr' (Eventually.of_forall fun u => ?_)
      ring
    have hf_c : Tendsto f (𝓝[>] 0) (𝓝 (c 0)) := by
      have := hc0.add (tendsto_sum_range_pow_nhdsGT c n)
      rw [zero_add] at this
      refine this.congr' (Eventually.of_forall fun u => ?_)
      ring
    have h0c : h 0 = c 0 := tendsto_nhds_unique hf_h hf_c
    -- shift
    have hh' : Tendsto (fun u : ℝ => ((f u - h 0) / u -
        ∑ j ∈ range (n + 1), h (j + 1) * (u : ℂ) ^ j) / (u : ℂ) ^ n) (𝓝[>] 0) (𝓝 0) := by
      refine hh.congr' ?_
      filter_upwards [hu0] with u hu
      rw [sum_range_succ_pow_shift h (n + 1) u]
      field_simp
      ring
    have hc' : Tendsto (fun u : ℝ => ((f u - h 0) / u -
        ∑ j ∈ range n, c (j + 1) * (u : ℂ) ^ j) / (u : ℂ) ^ n) (𝓝[>] 0) (𝓝 q) := by
      refine hc.congr' ?_
      filter_upwards [hu0] with u hu
      rw [sum_range_succ_pow_shift c n u, h0c]
      field_simp
      ring
    obtain ⟨h1, h2⟩ := ih (fun u => (f u - h 0) / u) (fun j => h (j + 1)) (fun j => c (j + 1))
      q hh' hc'
    refine ⟨fun j hj => ?_, h2⟩
    cases j with
    | zero => exact h0c
    | succ j => exact h1 j (by omega)

end Grammar
