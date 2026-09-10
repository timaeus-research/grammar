import Grammar.BilocalGaussian

/-!
# Divergence of the bilocal integral above threshold

For `a, b > 0` and `h > 2√(ab)` the bilocal integral
`∫₀^∞∫₀^∞ t^{λ−1}s^{λ−1} e^{−at − bs + h√(ts)} dt ds` is `+∞`
(`lintegral_bilocalIntegrand_eq_top`), hence so is `E₊[S_λ(G_i) S_λ(G_j)]`
(`lintegral_fluctuation_mul_fluctuation_eq_top`).

Along the ray `s = ut` the exponent is `t ψ(u)` with `ψ(u) = −a − bu + h√u`, and
`ψ(a/b) = √(a/b) (h − 2√(ab)) > 0`. By continuity `ψ ≥ η > 0` on a closed interval
`[a/b − ε, a/b + ε]`, so on the cone `s ∈ [t(a/b − ε), t(a/b + ε)]` the integrand is at least
`c₁ t^{2λ−2} e^{ηt}`; integrating over the cone section (length `2εt`) and then over `t ≥ T` for
a large `T` gives a lower bound `∫_T^∞ 1 dt = ∞`. Together with `lintegral_bilocalIntegrand_lt_top`
this classifies finiteness off the critical line `h = 2√(ab)`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Grammar

/-- The ray profile `ψ(u) = −a − bu + h√u`: `φ(t, tu) = t ψ(u)`. -/
noncomputable def rayProfile (a b h u : ℝ) : ℝ := -a - b * u + h * Real.sqrt u

theorem continuous_rayProfile (a b h : ℝ) : Continuous (rayProfile a b h) := by
  unfold rayProfile
  fun_prop

/-- `ψ(a/b) = √(a/b) (h − 2√(ab))`. -/
theorem rayProfile_div (a b h : ℝ) (ha : 0 < a) (hb : 0 < b) :
    rayProfile a b h (a / b) = Real.sqrt (a / b) * (h - 2 * Real.sqrt (a * b)) := by
  have h1 : Real.sqrt (a / b) * Real.sqrt (a * b) = a := by
    rw [← Real.sqrt_mul (div_pos ha hb).le, show a / b * (a * b) = a * a by field_simp,
      Real.sqrt_mul_self ha.le]
  have h2 : b * (a / b) = a := mul_div_cancel₀ a hb.ne'
  unfold rayProfile
  rw [h2]
  linear_combination 2 * h1

/-- **Divergence above threshold.** For `a, b > 0` and `h > 2√(ab)`, the bilocal integral
is `+∞`. -/
theorem lintegral_bilocalIntegrand_eq_top (lam a b h : ℝ) (hlam : 0 < lam) (ha : 0 < a)
    (hb : 0 < b) (hh : 2 * Real.sqrt (a * b) < h) :
    ∫⁻ t in Ioi (0 : ℝ), ∫⁻ s in Ioi (0 : ℝ),
      ENNReal.ofReal (bilocalIntegrand lam a b h t s) = ⊤ := by
  -- the ray `u = a/b` and the gap `η`
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = a / b := ⟨_, rfl⟩
  have hκ0 : 0 < κ := hκ ▸ div_pos ha hb
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = rayProfile a b h κ / 2 := ⟨_, rfl⟩
  have hη0 : 0 < η := by
    rw [hη, hκ, rayProfile_div a b h ha hb]
    exact half_pos (mul_pos (Real.sqrt_pos.2 (div_pos ha hb)) (sub_pos.2 hh))
  -- a closed interval around the ray on which `ψ ≥ η`
  obtain ⟨δ, hδ0, hδ⟩ :=
    Metric.continuousAt_iff.1 (continuous_rayProfile a b h).continuousAt η hη0
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = min (δ / 2) (κ / 2) := ⟨_, rfl⟩
  have hε0 : 0 < ε := hε ▸ lt_min (half_pos hδ0) (half_pos hκ0)
  have hεδ : ε < δ := hε ▸ (min_le_left _ _).trans_lt (half_lt_self hδ0)
  have hεκ : ε ≤ κ / 2 := hε ▸ min_le_right _ _
  have hlo : 0 < κ - ε := by linarith
  have hψ : ∀ u ∈ Icc (κ - ε) (κ + ε), η ≤ rayProfile a b h u := by
    intro u hu
    have hd : dist u κ < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hu.1, hu.2]
    have := hδ hd
    rw [Real.dist_eq, abs_lt] at this
    linarith [this.1]
  -- the `rpow` constant on the interval
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : ℝ, c₁ = min ((κ - ε) ^ (lam - 1)) ((κ + ε) ^ (lam - 1)) := ⟨_, rfl⟩
  have hc₁0 : 0 < c₁ :=
    hc₁ ▸ lt_min (Real.rpow_pos_of_pos hlo _) (Real.rpow_pos_of_pos (by linarith) _)
  -- pointwise lower bound on the cone
  have hlow : ∀ t : ℝ, 0 < t → ∀ s ∈ Icc (t * (κ - ε)) (t * (κ + ε)),
      c₁ * (t ^ (lam - 1)) ^ 2 * Real.exp (η * t) ≤ bilocalIntegrand lam a b h t s := by
    intro t ht s hs
    obtain ⟨u, hu, rfl⟩ : ∃ u ∈ Icc (κ - ε) (κ + ε), s = t * u := by
      refine ⟨s / t, ⟨?_, ?_⟩, (mul_div_cancel₀ s ht.ne').symm⟩
      · rw [le_div_iff₀ ht]
        linarith [hs.1]
      · rw [div_le_iff₀ ht]
        linarith [hs.2]
    have hu0 : 0 < u := lt_of_lt_of_le hlo hu.1
    have hsqrt : Real.sqrt (t * (t * u)) = t * Real.sqrt u := by
      rw [show t * (t * u) = (t * t) * u by ring, Real.sqrt_mul (mul_self_nonneg t),
        Real.sqrt_mul_self ht.le]
    have hφ : η * t ≤ -a * t - b * (t * u) + h * Real.sqrt (t * (t * u)) := by
      rw [hsqrt, show -a * t - b * (t * u) + h * (t * Real.sqrt u) = t * rayProfile a b h u by
        unfold rayProfile; ring, mul_comm η]
      exact mul_le_mul_of_nonneg_left (hψ u hu) ht.le
    have hru : c₁ ≤ u ^ (lam - 1) := by
      rcases le_or_gt 0 (lam - 1) with h1 | h1
      · exact (hc₁ ▸ min_le_left _ _).trans (Real.rpow_le_rpow hlo.le hu.1 h1)
      · exact (hc₁ ▸ min_le_right _ _).trans (Real.rpow_le_rpow_of_nonpos hu0 hu.2 h1.le)
    have htn : 0 ≤ t ^ (lam - 1) := Real.rpow_nonneg ht.le _
    unfold bilocalIntegrand
    rw [Real.mul_rpow ht.le hu0.le]
    calc c₁ * (t ^ (lam - 1)) ^ 2 * Real.exp (η * t)
        = t ^ (lam - 1) * (t ^ (lam - 1) * c₁) * Real.exp (η * t) := by ring
      _ ≤ t ^ (lam - 1) * (t ^ (lam - 1) * u ^ (lam - 1)) *
          Real.exp (-a * t - b * (t * u) + h * Real.sqrt (t * (t * u))) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hru htn) htn)
          (Real.exp_le_exp.2 hφ) (Real.exp_pos _).le
          (mul_nonneg htn (mul_nonneg htn (Real.rpow_nonneg hu0.le _)))
  -- the inner integral over the cone section
  have hinner : ∀ t : ℝ, 0 < t →
      ENNReal.ofReal (2 * ε * t * (c₁ * (t ^ (lam - 1)) ^ 2 * Real.exp (η * t))) ≤
        ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (bilocalIntegrand lam a b h t s) := by
    intro t ht
    have hsub : Icc (t * (κ - ε)) (t * (κ + ε)) ⊆ Ioi 0 := fun s hs =>
      lt_of_lt_of_le (mul_pos ht hlo) hs.1
    have hL : 0 ≤ c₁ * (t ^ (lam - 1)) ^ 2 * Real.exp (η * t) :=
      mul_nonneg (mul_nonneg hc₁0.le (sq_nonneg _)) (Real.exp_pos _).le
    calc ENNReal.ofReal (2 * ε * t * (c₁ * (t ^ (lam - 1)) ^ 2 * Real.exp (η * t)))
        = ENNReal.ofReal (c₁ * (t ^ (lam - 1)) ^ 2 * Real.exp (η * t)) *
            volume (Icc (t * (κ - ε)) (t * (κ + ε))) := by
          rw [Real.volume_Icc, ← ENNReal.ofReal_mul hL]
          congr 1
          ring
      _ = ∫⁻ s in Icc (t * (κ - ε)) (t * (κ + ε)),
            ENNReal.ofReal (c₁ * (t ^ (lam - 1)) ^ 2 * Real.exp (η * t)) :=
          (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ s in Icc (t * (κ - ε)) (t * (κ + ε)),
            ENNReal.ofReal (bilocalIntegrand lam a b h t s) :=
          setLIntegral_mono' measurableSet_Icc fun s hs => ENNReal.ofReal_le_ofReal (hlow t ht s hs)
      _ ≤ ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (bilocalIntegrand lam a b h t s) :=
          lintegral_mono_set hsub
  -- the lower bound is eventually `≥ 1`
  have hpos : 0 < ε * c₁ * η ^ 2 := mul_pos (mul_pos hε0 hc₁0) (pow_pos hη0 2)
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = max 1 (1 / (ε * c₁ * η ^ 2)) := ⟨_, rfl⟩
  have hT0 : 0 < T := lt_of_lt_of_le one_pos (hT ▸ le_max_left _ _)
  have hone : ∀ t : ℝ, T ≤ t → (1 : ℝ≥0∞) ≤
      ENNReal.ofReal (2 * ε * t * (c₁ * (t ^ (lam - 1)) ^ 2 * Real.exp (η * t))) := by
    intro t htT
    have ht1 : 1 ≤ t := (hT ▸ le_max_left _ _).trans htT
    have ht0 : 0 < t := by linarith
    have h1 : 1 ≤ ε * c₁ * η ^ 2 * t := by
      have h2 : 1 / (ε * c₁ * η ^ 2) ≤ t := (hT ▸ le_max_right _ _).trans htT
      rw [div_le_iff₀ hpos] at h2
      linarith
    have hinv : t⁻¹ ≤ t ^ (lam - 1) := by
      have := Real.rpow_le_rpow_of_exponent_le ht1 (show (-1 : ℝ) ≤ lam - 1 by linarith)
      rwa [Real.rpow_neg_one] at this
    have hsq : (t⁻¹) ^ 2 ≤ (t ^ (lam - 1)) ^ 2 := pow_le_pow_left₀ (inv_nonneg.2 ht0.le) hinv 2
    have hexp : (η * t) ^ 2 / 2 ≤ Real.exp (η * t) := by
      have := Real.pow_div_factorial_le_exp (η * t) (mul_pos hη0 ht0).le 2
      simpa [Nat.factorial] using this
    have htne : t ≠ 0 := ht0.ne'
    rw [ENNReal.one_le_ofReal]
    calc (1 : ℝ) ≤ ε * c₁ * η ^ 2 * t := h1
      _ = 2 * ε * t * (c₁ * (t⁻¹) ^ 2 * ((η * t) ^ 2 / 2)) := by
          field_simp
      _ ≤ 2 * ε * t * (c₁ * (t ^ (lam - 1)) ^ 2 * Real.exp (η * t)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul (mul_le_mul_of_nonneg_left hsq hc₁0.le) hexp
              (div_nonneg (sq_nonneg _) two_pos.le) (mul_nonneg hc₁0.le (sq_nonneg _)))
            (mul_pos (mul_pos two_pos hε0) ht0).le
  -- assemble
  rw [eq_top_iff]
  calc (⊤ : ℝ≥0∞) = ∫⁻ t in Ici T, (1 : ℝ≥0∞) := by
        rw [setLIntegral_const, Real.volume_Ici, one_mul]
    _ ≤ ∫⁻ t in Ici T, ENNReal.ofReal
          (2 * ε * t * (c₁ * (t ^ (lam - 1)) ^ 2 * Real.exp (η * t))) :=
        setLIntegral_mono' measurableSet_Ici fun t ht => hone t ht
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal
          (2 * ε * t * (c₁ * (t ^ (lam - 1)) ^ 2 * Real.exp (η * t))) :=
        lintegral_mono_set fun t ht => lt_of_lt_of_le hT0 ht
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), ∫⁻ s in Ioi (0 : ℝ),
          ENNReal.ofReal (bilocalIntegrand lam a b h t s) :=
        setLIntegral_mono' measurableSet_Ioi fun t ht => hinner t ht

variable {m n : ℕ} (A : Matrix (Fin m) (Fin (n + 1)) ℝ)

/-- **`E₊[S_λ(G_i) S_λ(G_j)] = +∞` above threshold**: for `a, b > 0` and `β²B_ij > 2√(ab)`. -/
theorem lintegral_fluctuation_mul_fluctuation_eq_top (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam)
    (i j : Fin m)
    (hi : 0 < 1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i / 2)
    (hj : 0 < 1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j / 2)
    (hh : 2 * Real.sqrt ((β * (1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i / 2)) *
        (β * (1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j / 2))) <
      β ^ 2 * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i j) :
    ∫⁻ g, ENNReal.ofReal (fluctuation β lam (g i) * fluctuation β lam (g j)) ∂gaussianVector A =
      ⊤ := by
  rw [lintegral_fluctuation_mul_fluctuation A β lam hβ hlam i j]
  exact lintegral_bilocalIntegrand_eq_top lam _ _ _ hlam (mul_pos hβ hi) (mul_pos hβ hj) hh

end Grammar
