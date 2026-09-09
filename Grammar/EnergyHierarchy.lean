/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.SecondOrderAssembled

/-!
# The population energy hierarchy: all moments of `NK` and their first log corrections (unit 326)

Iterating the exact coefficient transport `C_K(μ+1,j) = (μ C(μ,j) − (j+1) C(μ,j+1))/β` (one step of
`transportOp`, the operator `(μ − ∂_L)/β` on the log polynomial `P_μ(L) = ∑_j C(μ,j) L^j`) gives the
coefficients of the `r`-fold energy insertion `K^r`, i.e. the weight shift `h ↦ h + 2rk`:
`C_{K^r}(μ+r, ·) = β^{-r} ∏_{q<r} (μ+q − ∂_L) P_μ` (`iterTransport`, `gCoeff_add_two_mul_k`). On a
two-term polynomial `A L^s + B L^{s-1} + …` the top coefficient becomes `A (μ)_r / β^r` and the next
`((μ)_r B − s A ∂_μ(μ)_r)/β^r`, with `(μ)_r = μ(μ+1)⋯(μ+r−1)` the rising factorial (`poch`) and
`pochD` its derivative (`iterTransport_top`, `iterTransport_next`). Hence, after finite chart
assembly with `A_* ≠ 0` and `s = m_*−1` (`energy_moment_assembled`):
```
N^r 𝒵_{K^r}/𝒵 → (μ_*)_r/β^r,     log N · (N^r 𝒵_{K^r}/𝒵 − (μ_*)_r/β^r) → −s ∂_μ(μ_*)_r/β^r,
```
the moments of a `Gamma(μ_*, β)` law with their first inverse-log corrections; for the posterior
variance of `NK` (`energy_variance_assembled`): `V_N → μ_*/β²` and
`log N (V_N − μ_*/β²) → −s/β²`. Nothing is obtained by differentiating an asymptotic expansion; the
exact transport is iterated. Not claimed: weak convergence to a Gamma law (the Laplace transform
limit is a separate unit); anything when `A_* = 0`; a learning-theoretic "singular fluctuation"
interpretation (this is the posterior variance of `NK`). Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

/-- The rising factorial `(μ)_r = μ(μ+1)⋯(μ+r−1)`. -/
def poch (μ : ℝ) : ℕ → ℝ
  | 0 => 1
  | r + 1 => poch μ r * (μ + r)

/-- The `μ`-derivative of the rising factorial. -/
def pochD (μ : ℝ) : ℕ → ℝ
  | 0 => 0
  | r + 1 => pochD μ r * (μ + r) + poch μ r

theorem hasDerivAt_poch (r : ℕ) (μ : ℝ) : HasDerivAt (fun μ => poch μ r) (pochD μ r) μ := by
  induction r with
  | zero =>
    simp only [poch, pochD]
    exact hasDerivAt_const μ (1 : ℝ)
  | succ r ih =>
    simp only [poch, pochD]
    have := ih.mul ((hasDerivAt_id μ).add_const (r : ℝ))
    exact this.congr_deriv (by simp)

/-- One transport step: the coefficients of `(μ − ∂_L) P / β`. -/
noncomputable def transportOp (β μ : ℝ) (c : ℕ → ℝ) : ℕ → ℝ :=
  fun j => (μ * c j - ((j : ℝ) + 1) * c (j + 1)) / β

/-- `r` transport steps at `μ, μ+1, …, μ+r−1`. -/
noncomputable def iterTransport (β μ : ℝ) : ℕ → (ℕ → ℝ) → ℕ → ℝ
  | 0, c => c
  | r + 1, c => transportOp β (μ + r) (iterTransport β μ r c)

theorem iterTransport_vanish {β μ : ℝ} {c : ℕ → ℝ} {s : ℕ} (hc : ∀ q, s < q → c q = 0) (r : ℕ) :
    ∀ q, s < q → iterTransport β μ r c q = 0 := by
  induction r with
  | zero => exact hc
  | succ r ih =>
    intro q hq
    simp only [iterTransport, transportOp]
    rw [ih q hq, ih (q + 1) (by omega)]
    ring

/-- The top coefficient after `r` steps: `c_s (μ)_r / β^r`. -/
theorem iterTransport_top {β μ : ℝ} (hβ : β ≠ 0) {c : ℕ → ℝ} {s : ℕ}
    (hc : ∀ q, s < q → c q = 0) (r : ℕ) :
    iterTransport β μ r c s = c s * poch μ r / β ^ r := by
  induction r with
  | zero => simp [iterTransport, poch]
  | succ r ih =>
    simp only [iterTransport, transportOp]
    rw [ih, iterTransport_vanish hc r (s + 1) (by omega), poch, pow_succ]
    field_simp
    ring

/-- The next coefficient after `r` steps: `((μ)_r c_s − (s+1) c_{s+1} ∂_μ(μ)_r)/β^r`. -/
theorem iterTransport_next {β μ : ℝ} (hβ : β ≠ 0) {c : ℕ → ℝ} {s : ℕ}
    (hc : ∀ q, s + 1 < q → c q = 0) (r : ℕ) :
    iterTransport β μ r c s =
      (poch μ r * c s - ((s : ℝ) + 1) * c (s + 1) * pochD μ r) / β ^ r := by
  induction r with
  | zero => simp [iterTransport, poch, pochD]
  | succ r ih =>
    simp only [iterTransport, transportOp]
    rw [ih, iterTransport_top hβ hc r, poch, pochD, pow_succ]
    field_simp
    ring

/-- The ratio exponents of the `r`-fold shifted weight. -/
theorem ratioExp_add_two_mul_k {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (r : ℕ) (i : Fin d) :
    ratioExp (fun i => h i + 2 * r * k i) k i = ratioExp h k i + r := by
  induction r with
  | zero => simp
  | succ r ih =>
    have e : (fun i => h i + 2 * (r + 1) * k i) = fun i => (h i + 2 * r * k i) + 2 * k i := by
      funext i
      ring
    rw [e, ratioExp_add_two_k _ k hk i, ih]
    push_cast
    ring

theorem multCount_add_two_mul_k {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (r : ℕ) (l : ℝ) :
    multCount (ratioExp (fun i => h i + 2 * r * k i) k) (l + r) = multCount (ratioExp h k) l := by
  unfold multCount
  congr 1
  ext i
  simp [ratioExp_add_two_mul_k h k hk r i]

variable {M : ℕ} {K : Fin M → Type*} [∀ I, TopologicalSpace (K I)] [∀ I, CompactSpace (K I)]
  [∀ I, T2Space (K I)] [∀ I, MeasurableSpace (K I)] [∀ I, OpensMeasurableSpace (K I)]
  {n : Fin M → ℕ} (ν : (I : Fin M) → Measure (K I)) [∀ I, IsFiniteMeasure (ν I)]
  (h k : (I : Fin M) → Fin (n I + 1) → ℕ) (β : ℝ)

/-- **Iterated assembled coefficient transport**: the coefficients of the `r`-fold energy insertion
are the `r`-fold transport of the original coefficients. -/
theorem gCoeff_add_two_mul_k (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (x : JointData K n)
    (hx : ∀ I v, xiCoord (x.chart I v) = 0) {μ : ℝ} (hμ : 0 < μ) (r : ℕ) (j : ℕ) :
    gCoeff ν (fun I i => h I i + 2 * r * k I i) k β (fun _ => 1) x (μ + r) j =
      iterTransport β μ r (gCoeff ν h k β (fun _ => 1) x μ) j := by
  induction r generalizing j with
  | zero => simp [iterTransport]
  | succ r ih =>
    have e : (fun I i => h I i + 2 * (r + 1) * k I i) =
        fun I i => (h I i + 2 * r * k I i) + 2 * k I i := by
      funext I i
      ring
    have hμr : 0 < μ + r := by positivity
    have hstep := gCoeff_add_two_k ν (fun I i => h I i + 2 * r * k I i) k β hk hβ x hx hμr j
    rw [e, show μ + ((r + 1 : ℕ) : ℝ) = (μ + r) + 1 by push_cast; ring, hstep]
    simp only [iterTransport, transportOp]
    rw [ih j, ih (j + 1)]

/-- **All moments of `NK` after finite chart assembly, with their first log corrections**:
`N^r 𝒵_{K^r}/𝒵 → (μ_*)_r/β^r` and
`log N (N^r 𝒵_{K^r}/𝒵 − (μ_*)_r/β^r) → −(m_*−1) ∂_μ(μ_*)_r/β^r`, for zero-noise joint data,
external decompositions with log-weighted residual control and
`A_* ≠ 0`. -/
theorem energy_moment_assembled (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (x : JointData K n)
    (hx : ∀ I v, xiCoord (x.chart I v) = 0) (lam : Fin M → ℝ)
    (hmin : ∀ I i, lam I ≤ ratioExp (h I) (k I) i) (hatt : ∀ I, ∃ i, ratioExp (h I) (k I) i = lam I)
    {μs : ℝ} (hμ : ∀ I, μs ≤ lam I) (hμatt : ∃ I, lam I = μs) {ms : ℕ}
    (hm : ∀ I, lam I = μs → multCount (ratioExp (h I) (k I)) (lam I) ≤ ms)
    (hmatt : ∃ I, lam I = μs ∧ multCount (ratioExp (h I) (k I)) (lam I) = ms) (Zpop E : ℝ → ℝ)
    (hdecomp : ∀ N, Zpop N = gInt ν h k β (fun _ => 1) x N + E N)
    (hE : Tendsto (fun N => E N * Real.log N / N ^ (-μs)) atTop (𝓝 0)) (r : ℕ) (Zr Er : ℝ → ℝ)
    (hdecompr : ∀ N, Zr N = gInt ν (fun I i => h I i + 2 * r * k I i) k β (fun _ => 1) x N + Er N)
    (hEr : Tendsto (fun N => Er N * Real.log N / N ^ (-(μs + r))) atTop (𝓝 0))
    (hA : assembledFace ν h k β x lam μs ms ≠ 0) :
    Tendsto (fun N => N ^ r * (Zr N / Zpop N)) atTop (𝓝 (poch μs r / β ^ r)) ∧
    Tendsto (fun N => Real.log N * (N ^ r * (Zr N / Zpop N) - poch μs r / β ^ r)) atTop
      (𝓝 (-((ms : ℝ) - 1) * pochD μs r / β ^ r)) := by
  have hlam : ∀ I, 0 < lam I := fun I => by
    obtain ⟨i, hi⟩ := hatt I
    rw [← hi]
    exact ratioExp_pos (h I) (k I) (hk I) i
  have hμs : 0 < μs := by
    obtain ⟨I, hI⟩ := hμatt
    rw [← hI]
    exact hlam I
  have hms1 : 1 ≤ ms := by
    obtain ⟨I, -, hI⟩ := hmatt
    rw [← hI]
    exact multCount_pos _ _ (hatt I)
  -- shifted ordering data
  have hminr : ∀ I i, lam I + r ≤ ratioExp (fun i => h I i + 2 * r * k I i) (k I) i := by
    intro I i
    rw [ratioExp_add_two_mul_k (h I) (k I) (hk I) r i]
    linarith [hmin I i]
  have hattr : ∀ I, ∃ i, ratioExp (fun i => h I i + 2 * r * k I i) (k I) i = lam I + r := by
    intro I
    obtain ⟨i, hi⟩ := hatt I
    exact ⟨i, by rw [ratioExp_add_two_mul_k (h I) (k I) (hk I) r i, hi]⟩
  have hμr : ∀ I, μs + r ≤ lam I + r := fun I => by linarith [hμ I]
  have hμattr : ∃ I, lam I + r = μs + r := by
    obtain ⟨I, hI⟩ := hμatt
    exact ⟨I, by rw [hI]⟩
  have hmr : ∀ I, lam I + r = μs + r →
      multCount (ratioExp (fun i => h I i + 2 * r * k I i) (k I)) (lam I + r) ≤ ms := by
    intro I hI
    rw [multCount_add_two_mul_k (h I) (k I) (hk I)]
    exact hm I ((add_left_inj _).1 hI)
  have hmattr : ∃ I, lam I + r = μs + r ∧
      multCount (ratioExp (fun i => h I i + 2 * r * k I i) (k I)) (lam I + r) = ms := by
    obtain ⟨I, hI1, hI2⟩ := hmatt
    exact ⟨I, by rw [hI1], by rw [multCount_add_two_mul_k (h I) (k I) (hk I)]; exact hI2⟩
  -- two-term data
  have hZ := population_twoTerm_assembled ν h k β hk hβ x hx lam hmin hatt hμ hμatt hm hmatt Zpop E
    hdecomp hE
  have hZr := population_twoTerm_assembled ν _ k β hk hβ x hx (fun I => lam I + r) hminr hattr hμr
    hμattr hmr hmattr Zr Er hdecompr hEr
  -- coefficient identifications
  have hAeq : gCoeff ν h k β (fun _ => 1) x μs (ms - 1) = assembledFace ν h k β x lam μs ms :=
    gCoeff_population_leading ν h k β hk hβ x hx lam hmin hatt hμ hm
  have hzero : ∀ q, ms - 1 < q → gCoeff ν h k β (fun _ => 1) x μs q = 0 := fun q hq =>
    gCoeff_population_pred_eq_zero ν h k β hk hβ x hx lam hmin hatt hμ hm (p := (μs, q))
      (Or.inr ⟨rfl, hq⟩)
  have hAr : assembledFace ν (fun I i => h I i + 2 * r * k I i) k β x (fun I => lam I + r)
      (μs + r) ms = assembledFace ν h k β x lam μs ms * poch μs r / β ^ r := by
    rw [← gCoeff_population_leading ν _ k β hk hβ x hx (fun I => lam I + r) hminr hattr hμr hmr,
      gCoeff_add_two_mul_k ν h k β hk hβ x hx hμs r, iterTransport_top hβ.ne' hzero r, hAeq]
  have hBr : assembledSecondCoeff ν (fun I i => h I i + 2 * r * k I i) k β x (μs + r) ms =
      (poch μs r * assembledSecondCoeff ν h k β x μs ms -
        ((ms : ℝ) - 1) * assembledFace ν h k β x lam μs ms * pochD μs r) / β ^ r := by
    unfold assembledSecondCoeff
    split_ifs with hms
    · obtain ⟨s, hs⟩ : ∃ s, ms = s + 2 := ⟨ms - 2, by omega⟩
      subst hs
      have e1 : s + 2 - 1 = s + 1 := by omega
      have e2 : s + 2 - 2 = s := by omega
      rw [e2, gCoeff_add_two_mul_k ν h k β hk hβ x hx hμs r, ← hAeq, e1]
      rw [iterTransport_next hβ.ne' (fun q hq => hzero q (by omega)) r]
      push_cast
      ring
    · have hms1' : ms = 1 := by omega
      subst hms1'
      simp
  -- the quotient
  have hq := quotient_second_order hA hZ hZr
  rw [hAr, hBr] at hq
  have hlim : (assembledFace ν h k β x lam μs ms *
      ((poch μs r * assembledSecondCoeff ν h k β x μs ms -
        ((ms : ℝ) - 1) * assembledFace ν h k β x lam μs ms * pochD μs r) / β ^ r) -
      assembledFace ν h k β x lam μs ms * poch μs r / β ^ r *
        assembledSecondCoeff ν h k β x μs ms) /
      assembledFace ν h k β x lam μs ms ^ 2 = -((ms : ℝ) - 1) * pochD μs r / β ^ r := by
    field_simp
    ring
  have hAA : assembledFace ν h k β x lam μs ms * poch μs r / β ^ r /
      assembledFace ν h k β x lam μs ms = poch μs r / β ^ r := by
    field_simp
  rw [hlim, hAA] at hq
  have hq' : Tendsto (fun N => Real.log N * (N ^ r * (Zr N / Zpop N) - poch μs r / β ^ r)) atTop
      (𝓝 (-((ms : ℝ) - 1) * pochD μs r / β ^ r)) := by
    refine hq.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    have hN0 : 0 < N := by linarith
    have hlog : Real.log N ^ (ms - 1) ≠ 0 := pow_ne_zero _ (Real.log_pos hN).ne'
    rw [show μs + r - μs = (r : ℝ) by ring, Real.rpow_natCast, mul_div_assoc, div_self hlog,
      mul_one]
    ring
  refine ⟨?_, hq'⟩
  have := hq'.mul tendsto_inv_log
  rw [mul_zero] at this
  have h0 : Tendsto (fun N => N ^ r * (Zr N / Zpop N) - poch μs r / β ^ r) atTop (𝓝 0) := by
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    have hlog : Real.log N ≠ 0 := (Real.log_pos hN).ne'
    rw [mul_comm, ← mul_assoc, inv_mul_cancel₀ hlog, one_mul]
  have := h0.add_const (poch μs r / β ^ r)
  rw [zero_add] at this
  refine this.congr' (Eventually.of_forall fun N => ?_)
  ring

/-- **Posterior variance of `NK` after finite chart assembly**: with
`V_N = N² 𝒵_{K²}/𝒵 − (N 𝒵_K/𝒵)²`, `V_N → μ_*/β²` and `log N (V_N − μ_*/β²) → −(m_*−1)/β²`. -/
theorem energy_variance_assembled (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (x : JointData K n)
    (hx : ∀ I v, xiCoord (x.chart I v) = 0) (lam : Fin M → ℝ)
    (hmin : ∀ I i, lam I ≤ ratioExp (h I) (k I) i) (hatt : ∀ I, ∃ i, ratioExp (h I) (k I) i = lam I)
    {μs : ℝ} (hμ : ∀ I, μs ≤ lam I) (hμatt : ∃ I, lam I = μs) {ms : ℕ}
    (hm : ∀ I, lam I = μs → multCount (ratioExp (h I) (k I)) (lam I) ≤ ms)
    (hmatt : ∃ I, lam I = μs ∧ multCount (ratioExp (h I) (k I)) (lam I) = ms) (Zpop E : ℝ → ℝ)
    (hdecomp : ∀ N, Zpop N = gInt ν h k β (fun _ => 1) x N + E N)
    (hE : Tendsto (fun N => E N * Real.log N / N ^ (-μs)) atTop (𝓝 0)) (Z1 E1 Z2 E2 : ℝ → ℝ)
    (hdecomp1 : ∀ N, Z1 N = gInt ν (fun I i => h I i + 2 * k I i) k β (fun _ => 1) x N + E1 N)
    (hE1 : Tendsto (fun N => E1 N * Real.log N / N ^ (-(μs + 1))) atTop (𝓝 0))
    (hdecomp2 : ∀ N, Z2 N = gInt ν (fun I i => h I i + 4 * k I i) k β (fun _ => 1) x N + E2 N)
    (hE2 : Tendsto (fun N => E2 N * Real.log N / N ^ (-(μs + 2))) atTop (𝓝 0))
    (hA : assembledFace ν h k β x lam μs ms ≠ 0) :
    Tendsto (fun N => N ^ 2 * (Z2 N / Zpop N) - (N * (Z1 N / Zpop N)) ^ 2) atTop
      (𝓝 (μs / β ^ 2)) ∧
    Tendsto (fun N => Real.log N * (N ^ 2 * (Z2 N / Zpop N) - (N * (Z1 N / Zpop N)) ^ 2 -
      μs / β ^ 2)) atTop (𝓝 (-((ms : ℝ) - 1) / β ^ 2)) := by
  have e1 : (fun I i => h I i + 2 * 1 * k I i) = fun I i => h I i + 2 * k I i := by
    funext I i
    ring
  have e2 : (fun I i => h I i + 2 * 2 * k I i) = fun I i => h I i + 4 * k I i := by
    funext I i
    ring
  obtain ⟨h1a, h1b⟩ := energy_moment_assembled ν h k β hk hβ x hx lam hmin hatt hμ hμatt hm hmatt
    Zpop E hdecomp hE 1 Z1 E1 (by rw [e1]; exact hdecomp1) (by simpa using hE1) hA
  obtain ⟨h2a, h2b⟩ := energy_moment_assembled ν h k β hk hβ x hx lam hmin hatt hμ hμatt hm hmatt
    Zpop E hdecomp hE 2 Z2 E2 (by rw [e2]; exact hdecomp2) (by simpa using hE2) hA
  simp only [poch, pochD, pow_one, Nat.cast_zero, Nat.cast_one, add_zero, one_mul, zero_mul,
    zero_add] at h1a h1b h2a h2b
  constructor
  · convert h2a.sub (h1a.pow 2) using 2 <;> ring
  · convert h2b.sub (h1b.mul (h1a.add_const (μs / β))) using 2 <;> ring

end Grammar
