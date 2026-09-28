import Grammar.SmoothFiniteUniqueness

/-!
# Coefficient transfer for polynomially weighted insertion identities

Multiplying an exact insertion identity by a common negative power of the sample size
keeps every exponent on the nonnegative lattice. A single sufficiently high cutoff then
suffices for coefficient comparison. No differentiation of asymptotic remainders is used.
-/

open Filter Topology

namespace Grammar

/-- A natural shift preserves membership in the coefficient lattice. -/
theorem lattice_add_nat {Q : ℕ} (hQ : 0 < Q) {μ : ℝ}
    (hμ : ∃ m : ℕ, μ = (m : ℝ) / Q) (s : ℕ) :
    ∃ m : ℕ, μ + (s : ℝ) = (m : ℝ) / Q := by
  obtain ⟨m, rfl⟩ := hμ
  refine ⟨m + s * Q, ?_⟩
  have hQr : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  push_cast
  field_simp

/-- Shifting the exponent of a spectral sum multiplies it by `N⁻ˢ`. -/
theorem absSpectralSum_shift_nat {Q D : ℕ} (hQ : 0 < Q)
    {c : ℝ → ℕ → ℝ}
    (hc : ∀ μ q, c μ q ≠ 0 → ∃ m : ℕ, μ = (m : ℝ) / Q)
    (s : ℕ) (L : ℝ) {N : ℝ} (hN : 0 < N) :
    absSpectralSum Q D (fun μ q ↦ c (μ - (s : ℝ)) q) L N =
      N ^ (-(s : ℝ)) * absSpectralSum Q D c (L - (s : ℝ)) N := by
  classical
  let A := latticeBelow Q (L - (s : ℝ))
  let B := A.image (fun μ ↦ μ + (s : ℝ))
  have hsub : B ⊆ latticeBelow Q L := by
    intro μ hμ
    obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.1 hμ
    obtain ⟨hνgrid, hνL⟩ := (mem_latticeBelow_iff hQ).1 hν
    exact (mem_latticeBelow_iff hQ).2 ⟨lattice_add_nat hQ hνgrid s, by linarith⟩
  unfold absSpectralSum
  rw [← Finset.sum_subset hsub]
  · change (∑ μ ∈ A.image (fun ν ↦ ν + (s : ℝ)),
        N ^ (-μ) * ∑ q ∈ Finset.range (D + 1), c (μ - (s : ℝ)) q * Real.log N ^ q) = _
    rw [Finset.sum_image]
    · conv_rhs => rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun μ _ ↦ ?_
      simp only [add_sub_cancel_right]
      rw [show -(μ + (s : ℝ)) = -(s : ℝ) + -μ by ring, Real.rpow_add hN]
      ring
    · intro a _ b _ hab
      exact add_right_cancel hab
  · intro μ hμ hnot
    have hzero : ∀ q, c (μ - (s : ℝ)) q = 0 := by
      intro q
      by_contra hne
      have hmem : μ - (s : ℝ) ∈ A :=
        (mem_latticeBelow_iff hQ).2 ⟨hc _ q hne,
          by have := ((mem_latticeBelow_iff hQ).1 hμ).2; linarith⟩
      exact hnot (Finset.mem_image.2 ⟨μ - (s : ℝ), hmem, sub_add_cancel _ _⟩)
    simp only [hzero, zero_mul, Finset.sum_const_zero, mul_zero]

/-- Only cutoffs above the shift are needed for coefficient transfer. -/
theorem CutoffExpansion.shift_nat_bound {Q D : ℕ} (hQ : 0 < Q)
    {Z : ℝ → ℝ} {c : ℝ → ℕ → ℝ} (h : CutoffExpansion Q D Z c)
    (hc : ∀ μ q, c μ q ≠ 0 → ∃ m : ℕ, μ = (m : ℝ) / Q)
    (s : ℕ) {L : ℝ} (hsL : (s : ℝ) < L) :
    ∃ K : ℝ, ∀ᶠ N in atTop,
      |N ^ (-(s : ℝ)) * Z N -
        absSpectralSum Q D (fun μ q ↦ c (μ - (s : ℝ)) q) L N| ≤
          K * (N ^ (-L) * (1 + Real.log N) ^ D) := by
  obtain ⟨K, hK⟩ := h (L - (s : ℝ)) (sub_pos.2 hsL)
  refine ⟨K, ?_⟩
  filter_upwards [hK, eventually_gt_atTop (0 : ℝ)] with N hbound hN
  rw [absSpectralSum_shift_nat hQ hc s L hN, ← mul_sub, abs_mul,
    abs_of_pos (Real.rpow_pos_of_pos hN _)]
  have hm := mul_le_mul_of_nonneg_left hbound (Real.rpow_pos_of_pos hN (-(s : ℝ))).le
  have he : N ^ (-(s : ℝ)) * N ^ (-(L - (s : ℝ))) = N ^ (-L) := by
    rw [← Real.rpow_add hN]
    congr 1
    ring
  calc
    _ ≤ N ^ (-(s : ℝ)) * (K * (N ^ (-(L - (s : ℝ))) *
        (1 + Real.log N) ^ D)) := hm
    _ = K * (N ^ (-L) * (1 + Real.log N) ^ D) := by
      calc
        _ = K * ((N ^ (-(s : ℝ)) * N ^ (-(L - (s : ℝ)))) *
            (1 + Real.log N) ^ D) := by ring
        _ = _ := by rw [he]


/-- Spectral truncation commutes with a finite sum of coefficient systems. -/
theorem absSpectralSum_finset_sum {ι : Type*} (t : Finset ι) (Q D : ℕ)
    (c : ι → ℝ → ℕ → ℝ) (L N : ℝ) :
    absSpectralSum Q D (fun μ q ↦ ∑ i ∈ t, c i μ q) L N =
      ∑ i ∈ t, absSpectralSum Q D (c i) L N := by
  unfold absSpectralSum
  simp only [Finset.sum_mul, Finset.mul_sum]
  calc
    _ = ∑ μ ∈ latticeBelow Q L, ∑ i ∈ t,
        ∑ q ∈ Finset.range (D + 1), N ^ (-μ) * (c i μ q * Real.log N ^ q) := by
      apply Finset.sum_congr rfl
      intro μ _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- Add finitely many remainder bounds at one fixed cutoff. -/
theorem finset_sum_cutoff_bound {ι : Type*} (t : Finset ι) {Q D : ℕ}
    {Z : ι → ℝ → ℝ} {c : ι → ℝ → ℕ → ℝ} {K : ι → ℝ} {L : ℝ}
    (h : ∀ i ∈ t, ∀ᶠ N in atTop,
      |Z i N - absSpectralSum Q D (c i) L N| ≤
        K i * (N ^ (-L) * (1 + Real.log N) ^ D)) :
    ∀ᶠ N in atTop,
      |(∑ i ∈ t, Z i N) -
        absSpectralSum Q D (fun μ q ↦ ∑ i ∈ t, c i μ q) L N| ≤
          (∑ i ∈ t, K i) * (N ^ (-L) * (1 + Real.log N) ^ D) := by
  filter_upwards [(eventually_all_finset t).2 h] with N hN
  rw [absSpectralSum_finset_sum, ← Finset.sum_sub_distrib, Finset.sum_mul]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi ↦ hN i hi)

/-- Compare coefficients of an identity after all powers have been made nonpositive.
Only one cutoff above all shifts and the target exponent is required. -/
theorem shifted_insertion_coeff_eq {ι : Type*} (t : Finset ι) {Q D : ℕ}
    (hQ : 0 < Q) {Z : ι → ℝ → ℝ} {H : ℝ → ℝ}
    {c : ι → ℝ → ℕ → ℝ} {b : ℝ → ℕ → ℝ}
    (hZ : ∀ i, CutoffExpansion Q D (Z i) (c i))
    (hH : CutoffExpansion Q D H b)
    (hc : ∀ i μ q, c i μ q ≠ 0 → ∃ m : ℕ, μ = (m : ℝ) / Q)
    (hb : ∀ μ q, b μ q ≠ 0 → ∃ m : ℕ, μ = (m : ℝ) / Q)
    (s : ι → ℕ) (d : ℕ) {L μ : ℝ} {q : ℕ}
    (hsL : ∀ i, (s i : ℝ) < L) (hdL : (d : ℝ) < L)
    (hμ : μ ∈ latticeBelow Q L) (hq : q ≤ D)
    (heq : ∀ᶠ N in atTop, ∑ i ∈ t, N ^ (-(s i : ℝ)) * Z i N =
      N ^ (-(d : ℝ)) * H N) :
    ∑ i ∈ t, c i (μ - (s i : ℝ)) q = b (μ - (d : ℝ)) q := by
  choose K hK using fun i ↦ (hZ i).shift_nat_bound hQ (hc i) (s i) (hsL i)
  obtain ⟨KH, hKH⟩ := hH.shift_nat_bound hQ hb d hdL
  have hsum := finset_sum_cutoff_bound t (fun i _ ↦ hK i)
  have hleft : ∀ᶠ N in atTop,
      |N ^ (-(d : ℝ)) * H N -
        absSpectralSum Q D (fun ν j ↦ ∑ i ∈ t, c i (ν - (s i : ℝ)) j) L N| ≤
          (∑ i ∈ t, K i) * (N ^ (-L) * (1 + Real.log N) ^ D) := by
    filter_upwards [hsum, heq] with N hN hEq
    rwa [hEq] at hN
  exact finite_coeff_unique hQ hleft hKH μ hμ q hq

/-- Polynomial insertion identities constrain every coefficient on the common shifted grid.
The shifts are bounded by `d`; the coefficient comparison is at `ρ + d`.
A later wrapper handles off-grid coefficients by their support. -/
theorem polynomial_insertion_coeff_eq {ι : Type*} (t : Finset ι) {Q D : ℕ}
    (hQ : 0 < Q) {Z : ι → ℝ → ℝ} {H : ℝ → ℝ}
    {c : ι → ℝ → ℕ → ℝ} {b : ℝ → ℕ → ℝ}
    (hZ : ∀ i, CutoffExpansion Q D (Z i) (c i))
    (hH : CutoffExpansion Q D H b)
    (hc : ∀ i μ q, c i μ q ≠ 0 → ∃ m : ℕ, μ = (m : ℝ) / Q)
    (hb : ∀ μ q, b μ q ≠ 0 → ∃ m : ℕ, μ = (m : ℝ) / Q)
    (j : ι → ℕ) (d : ℕ) (hjd : ∀ i, j i ≤ d) {ρ : ℝ} {q : ℕ}
    (hρ : ∃ m : ℕ, ρ + (d : ℝ) = (m : ℝ) / Q) (hq : q ≤ D)
    (heq : ∀ᶠ N in atTop, ∑ i ∈ t, N ^ j i * Z i N = H N) :
    ∑ i ∈ t, c i (ρ + (j i : ℝ)) q = b ρ q := by
  let L := max ((d : ℝ) + 1) (ρ + (d : ℝ) + 1)
  have hdL : (d : ℝ) < L := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hμL : ρ + (d : ℝ) < L := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hsL : ∀ i, ((d - j i : ℕ) : ℝ) < L := by
    intro i
    exact lt_of_le_of_lt (by exact_mod_cast Nat.sub_le d (j i)) hdL
  have hshift : ∀ᶠ N in atTop,
      ∑ i ∈ t, N ^ (-((d - j i : ℕ) : ℝ)) * Z i N = N ^ (-(d : ℝ)) * H N := by
    filter_upwards [heq, eventually_gt_atTop (0 : ℝ)] with N hEq hN
    rw [← hEq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hN, Nat.cast_sub (hjd i)]
    congr 2
    ring
  have h := shifted_insertion_coeff_eq t hQ hZ hH hc hb (fun i ↦ d - j i) d
    hsL hdL ((mem_latticeBelow_iff hQ).2 ⟨hρ, hμL⟩) hq hshift
  have harg : ∀ i, ρ + (d : ℝ) - ((d - j i : ℕ) : ℝ) = ρ + (j i : ℝ) := by
    intro i
    rw [Nat.cast_sub (hjd i)]
    ring
  simpa only [harg, add_sub_cancel_right] using h


/-- The coefficient identity holds at every real exponent and every log degree.
Off the shifted lattice, or above the degree bound, support makes both sides zero. -/
theorem polynomial_insertion_coeff_eq_all {ι : Type*} (t : Finset ι) {Q D : ℕ}
    (hQ : 0 < Q) {Z : ι → ℝ → ℝ} {H : ℝ → ℝ}
    {c : ι → ℝ → ℕ → ℝ} {b : ℝ → ℕ → ℝ}
    (hZ : ∀ i, CutoffExpansion Q D (Z i) (c i))
    (hH : CutoffExpansion Q D H b)
    (hc : ∀ i μ q, c i μ q ≠ 0 → (∃ m : ℕ, μ = (m : ℝ) / Q) ∧ q ≤ D)
    (hb : ∀ μ q, b μ q ≠ 0 → (∃ m : ℕ, μ = (m : ℝ) / Q) ∧ q ≤ D)
    (j : ι → ℕ) (d : ℕ) (hjd : ∀ i, j i ≤ d)
    (heq : ∀ᶠ N in atTop, ∑ i ∈ t, N ^ j i * Z i N = H N)
    (ρ : ℝ) (q : ℕ) :
    ∑ i ∈ t, c i (ρ + (j i : ℝ)) q = b ρ q := by
  classical
  by_cases hq : q ≤ D
  · by_cases hρ : ∃ m : ℕ, ρ + (d : ℝ) = (m : ℝ) / Q
    · exact polynomial_insertion_coeff_eq t hQ hZ hH
        (fun i μ q hn ↦ (hc i μ q hn).1) (fun μ q hn ↦ (hb μ q hn).1)
        j d hjd hρ hq heq
    · have hc0 : ∀ i, c i (ρ + (j i : ℝ)) q = 0 := by
        intro i
        by_contra hn
        obtain ⟨m, hm⟩ := lattice_add_nat hQ (hc i _ q hn).1 (d - j i)
        apply hρ
        refine ⟨m, ?_⟩
        calc
          ρ + (d : ℝ) = ρ + (j i : ℝ) + ((d - j i : ℕ) : ℝ) := by
            rw [Nat.cast_sub (hjd i)]
            ring
          _ = (m : ℝ) / Q := hm
      have hb0 : b ρ q = 0 := by
        by_contra hn
        exact hρ (lattice_add_nat hQ (hb _ q hn).1 d)
      simp only [hc0, hb0, Finset.sum_const_zero]
  · have hc0 : ∀ i, c i (ρ + (j i : ℝ)) q = 0 := by
      intro i
      by_contra hn
      exact hq (hc i _ q hn).2
    have hb0 : b ρ q = 0 := by
      by_contra hn
      exact hq (hb _ q hn).2
    simp only [hc0, hb0, Finset.sum_const_zero]

end Grammar
