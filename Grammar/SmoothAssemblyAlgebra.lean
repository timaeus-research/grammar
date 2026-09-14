/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothFaceTheorem
import Grammar.AbstractExpansion

/-!
# Assembly algebra of the smooth engine (consult #116 §1.7, §2)

Two pieces of finite bookkeeping used to turn the facewise expansions into ONE coefficient system
on the ambient lattice:
* ★ `reorganise`: a finite family of power–log expansions (weights `w s`, face lattices
  `Λ s ⊆ latticeBelow Q L`, degrees `D s ≤ D`, coefficients vanishing off their own lattice,
  coefficient integrals `I s μ e`) sums to `absSpectralSum Q D c L N` for the coefficient system
  `c μ q = ∑_s w s ∑_{j=q}^{D s} c_s(μ,j) C(j,q) I s μ (j−q)` — the binomial reindexing
  `(log N + S)^j = ∑_q C(j,q) (log N)^q S^{j−q}` collected by powers of `log N`;
* `absSpectralSum_sub_lower` / `bound_lower_cutoff`: an expansion through the cutoff `L` is an
  expansion through every lower cutoff `L' ≤ L` (the dropped terms are `O(N^{−L'}(1+log N)^D)`).
Zero `sorry`/`axiom`.
-/

open Finset Real

namespace Grammar

namespace SmoothEngine

/-! ### Reorganising the face sums by powers of `log N` -/

/-- The triangle `{(j, q) : q ≤ j ≤ D}` summed in either order. -/
theorem sum_triangle (D : ℕ) (f : ℕ → ℕ → ℝ) :
    ∑ j ∈ range (D + 1), ∑ q ∈ range (j + 1), f j q =
      ∑ q ∈ range (D + 1), ∑ j ∈ Finset.Ico q (D + 1), f j q := by
  refine Finset.sum_comm' fun j q => ?_
  simp only [Finset.mem_range, Finset.mem_Ico]
  omega

/-- ★ **Reorganisation**: a finite family of face expansions is one `absSpectralSum`. -/
theorem reorganise {σ : Type*} (S : Finset σ) (w : σ → ℝ) (Λ : σ → Finset ℝ) (Ds : σ → ℕ)
    (c : σ → ℝ → ℕ → ℝ) (I : σ → ℝ → ℕ → ℝ) {Q D : ℕ} {L N : ℝ}
    (hΛ : ∀ s ∈ S, Λ s ⊆ latticeBelow Q L)
    (hc : ∀ s ∈ S, ∀ μ ∈ latticeBelow Q L, μ ∉ Λ s → ∀ j, c s μ j = 0)
    (hD : ∀ s ∈ S, Ds s ≤ D) :
    ∑ s ∈ S, w s * ∑ μ ∈ Λ s, N ^ (-μ) * ∑ j ∈ range (Ds s + 1), ∑ q ∈ range (j + 1),
        c s μ j * (j.choose q) * log N ^ q * I s μ (j - q) =
      absSpectralSum Q D (fun μ q => ∑ s ∈ S, w s * ∑ j ∈ Finset.Ico q (Ds s + 1),
        c s μ j * (j.choose q) * I s μ (j - q)) L N := by
  unfold absSpectralSum
  -- extend each face lattice to the ambient lattice
  have hext : ∀ s ∈ S, ∑ μ ∈ Λ s, N ^ (-μ) * ∑ j ∈ range (Ds s + 1), ∑ q ∈ range (j + 1),
      c s μ j * (j.choose q) * log N ^ q * I s μ (j - q) =
      ∑ μ ∈ latticeBelow Q L, N ^ (-μ) * ∑ j ∈ range (Ds s + 1), ∑ q ∈ range (j + 1),
        c s μ j * (j.choose q) * log N ^ q * I s μ (j - q) := by
    intro s hs
    refine Finset.sum_subset (hΛ s hs) fun μ hμ hμ' => ?_
    simp [hc s hs μ hμ hμ']
  -- reorder each face's triangle and pad the degree
  have htri : ∀ s ∈ S, ∀ μ : ℝ, ∑ j ∈ range (Ds s + 1), ∑ q ∈ range (j + 1),
      c s μ j * (j.choose q) * log N ^ q * I s μ (j - q) =
      ∑ q ∈ range (D + 1), (∑ j ∈ Finset.Ico q (Ds s + 1),
        c s μ j * (j.choose q) * I s μ (j - q)) * log N ^ q := by
    intro s hs μ
    rw [sum_triangle]
    have hsub : range (Ds s + 1) ⊆ range (D + 1) :=
      Finset.range_mono (Nat.succ_le_succ (hD s hs))
    rw [Finset.sum_subset hsub fun q _ hq => ?_]
    · refine Finset.sum_congr rfl fun q _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    · have : Ds s + 1 ≤ q := by simpa using hq
      simp [Finset.Ico_eq_empty_of_le this]
  calc ∑ s ∈ S, w s * ∑ μ ∈ Λ s, N ^ (-μ) * ∑ j ∈ range (Ds s + 1), ∑ q ∈ range (j + 1),
        c s μ j * (j.choose q) * log N ^ q * I s μ (j - q)
      = ∑ s ∈ S, ∑ μ ∈ latticeBelow Q L, w s * (N ^ (-μ) * ∑ q ∈ range (D + 1),
          (∑ j ∈ Finset.Ico q (Ds s + 1), c s μ j * (j.choose q) * I s μ (j - q)) *
            log N ^ q) := by
        refine Finset.sum_congr rfl fun s hs => ?_
        rw [hext s hs, Finset.mul_sum]
        refine Finset.sum_congr rfl fun μ _ => ?_
        rw [htri s hs μ]
    _ = ∑ μ ∈ latticeBelow Q L, N ^ (-μ) * ∑ q ∈ range (D + 1),
          (∑ s ∈ S, w s * ∑ j ∈ Finset.Ico q (Ds s + 1),
            c s μ j * (j.choose q) * I s μ (j - q)) * log N ^ q := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun μ _ => ?_
        have hx : ∀ x ∈ S, w x * (N ^ (-μ) * ∑ q ∈ range (D + 1),
            (∑ j ∈ Finset.Ico q (Ds x + 1), c x μ j * (j.choose q) * I x μ (j - q)) *
              log N ^ q) =
            ∑ q ∈ range (D + 1), N ^ (-μ) * ((w x * ∑ j ∈ Finset.Ico q (Ds x + 1),
              c x μ j * (j.choose q) * I x μ (j - q)) * log N ^ q) := by
          intro x _
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun q _ => ?_
          ring
        rw [Finset.sum_congr rfl hx, Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.sum_mul, Finset.mul_sum]

/-! ### Lowering the cutoff -/

theorem latticeBelow_mono {Q : ℕ} (hQ : 0 < Q) {L' L : ℝ} (hLL : L' ≤ L) :
    latticeBelow Q L' ⊆ latticeBelow Q L := fun μ hμ => by
  obtain ⟨hm, hlt⟩ := (mem_latticeBelow_iff hQ).1 hμ
  exact (mem_latticeBelow_iff hQ).2 ⟨hm, lt_of_lt_of_le hlt hLL⟩

/-- The terms dropped when lowering the cutoff from `L` to `L' ≤ L` are `O(N^{−L'}(1+log N)^D)`. -/
theorem absSpectralSum_sub_lower {Q D : ℕ} (hQ : 0 < Q) (c : ℝ → ℕ → ℝ) {L' L : ℝ}
    (hLL : L' ≤ L) {N : ℝ} (hN : 1 ≤ N) :
    |absSpectralSum Q D c L N - absSpectralSum Q D c L' N| ≤
      (∑ μ ∈ latticeBelow Q L, ∑ j ∈ range (D + 1), |c μ j|) *
        (N ^ (-L') * (1 + log N) ^ D) := by
  have hN0 : 0 < N := by linarith
  have hlog : 0 ≤ log N := log_nonneg hN
  have hsub := latticeBelow_mono hQ hLL
  unfold absSpectralSum
  rw [← Finset.sum_sdiff hsub, add_sub_cancel_right]
  have hterm : ∀ μ ∈ latticeBelow Q L \ latticeBelow Q L',
      |N ^ (-μ) * ∑ j ∈ range (D + 1), c μ j * log N ^ j| ≤
        (∑ j ∈ range (D + 1), |c μ j|) * (N ^ (-L') * (1 + log N) ^ D) := by
    intro μ hμ
    obtain ⟨hμL, hμL'⟩ := Finset.mem_sdiff.1 hμ
    obtain ⟨hm, _⟩ := (mem_latticeBelow_iff hQ).1 hμL
    have hge : L' ≤ μ := by
      by_contra hlt
      exact hμL' ((mem_latticeBelow_iff hQ).2 ⟨hm, lt_of_not_ge hlt⟩)
    have hpow : N ^ (-μ) ≤ N ^ (-L') := rpow_le_rpow_of_exponent_le hN (by linarith)
    have hpow0 : 0 ≤ N ^ (-μ) := rpow_nonneg hN0.le _
    rw [abs_mul, abs_of_nonneg hpow0]
    calc N ^ (-μ) * |∑ j ∈ range (D + 1), c μ j * log N ^ j|
        ≤ N ^ (-L') * ∑ j ∈ range (D + 1), |c μ j| * (1 + log N) ^ D := by
          refine mul_le_mul hpow ?_ (abs_nonneg _) (rpow_nonneg hN0.le _)
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
          rw [abs_mul, abs_pow, abs_of_nonneg hlog]
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          calc log N ^ j ≤ (1 + log N) ^ j := pow_le_pow_left₀ hlog (by linarith) j
            _ ≤ (1 + log N) ^ D :=
                pow_le_pow_right₀ (by linarith) (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))
      _ = (∑ j ∈ range (D + 1), |c μ j|) * (N ^ (-L') * (1 + log N) ^ D) := by
          rw [← Finset.sum_mul]; ring
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
    fun μ _ _ => Finset.sum_nonneg fun j _ => abs_nonneg _) (by positivity)

/-- An expansion through the cutoff `L` is an expansion through every cutoff `L' ≤ L`. -/
theorem bound_lower_cutoff {Q D : ℕ} (hQ : 0 < Q) {Z : ℝ → ℝ} {c : ℝ → ℕ → ℝ} {L' L K : ℝ}
    (hLL : L' ≤ L) {N : ℝ} (hN : 1 ≤ N)
    (h : |Z N - absSpectralSum Q D c L N| ≤ K * (N ^ (-L) * (1 + log N) ^ D)) :
    |Z N - absSpectralSum Q D c L' N| ≤
      (K + ∑ μ ∈ latticeBelow Q L, ∑ j ∈ range (D + 1), |c μ j|) *
        (N ^ (-L') * (1 + log N) ^ D) := by
  have hN0 : 0 < N := by linarith
  have hK : 0 ≤ K := by
    have h0 : 0 < N ^ (-L) * (1 + log N) ^ D := by
      have := log_nonneg hN; positivity
    exact (mul_nonneg_iff_of_pos_right h0).1 ((abs_nonneg _).trans h)
  have hpow : N ^ (-L) ≤ N ^ (-L') := rpow_le_rpow_of_exponent_le hN (by linarith)
  have hlog : 0 ≤ (1 + log N) ^ D := by have := log_nonneg hN; positivity
  calc |Z N - absSpectralSum Q D c L' N|
      = |(Z N - absSpectralSum Q D c L N) +
          (absSpectralSum Q D c L N - absSpectralSum Q D c L' N)| := by ring_nf
    _ ≤ |Z N - absSpectralSum Q D c L N| +
          |absSpectralSum Q D c L N - absSpectralSum Q D c L' N| := abs_add_le _ _
    _ ≤ K * (N ^ (-L') * (1 + log N) ^ D) +
          (∑ μ ∈ latticeBelow Q L, ∑ j ∈ range (D + 1), |c μ j|) *
            (N ^ (-L') * (1 + log N) ^ D) := by
        refine add_le_add (h.trans ?_) (absSpectralSum_sub_lower hQ c hLL hN)
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hlog) hK
    _ = _ := by ring

end SmoothEngine

end Grammar
