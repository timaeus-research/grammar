You are Astra, design consultant for the Lean 4 formalisation (repo timaeus-research/grammar, namespace Grammar) accompanying the examples note `examples_slop.tex` of the grammar paper (Gerraty–Murfet, "Expectations and the Exceptional Divisor"). In the previous round you reviewed the note and set three day-sized targets: (1) the unequal-wall tie formula for polynomial amplitudes on the blow-up chart h=(1,0), k=(2,1); (2) the naive Bayes quadratic log-square surrogate with c₃ = π√(2π)V; (3) the rank-one normal Gaussian integral with the linear field and the tilt e^{‖PΞ‖²/2}. All three are now theorems (no sorry/axiom). Their statements follow, then the list of what remains derivation-only in the note, then the questions.

## Target 1 — Grammar/TieFormulaPolynomial.lean (DXCVII)
def tieH : Fin 2 → ℕ := ![1, 0]

/-- The blow-up chart data: `k = (2, 1)`. -/
def tieK : Fin 2 → ℕ := ![2, 1]

theorem tieK_pos : ∀ i, 0 < tieK i := by
  intro i; fin_cases i <;> simp [tieK]

/-- A polynomial amplitude `Σ_{γ ∈ S} c_γ u^γ`. -/
noncomputable def polyAmp (S : Finset (Fin 2 → ℕ)) (c : (Fin 2 → ℕ) → ℝ) (u : Fin 2 → ℝ) : ℝ :=
  ∑ γ ∈ S, c γ * mono γ u

theorem contDiff_polyAmp (S : Finset (Fin 2 → ℕ)) (c : (Fin 2 → ℕ) → ℝ) :
    ContDiff ℝ ∞ (polyAmp S c) :=
  ContDiff.sum fun γ _ => contDiff_const.mul (contDiff_mono γ)

/-- The rational term of one monomial: `1/((γ₀ + 2 − 4s)(γ₁ + 1 − 2s))`. -/
noncomputable def monoTerm (γ : Fin 2 → ℕ) (s : ℂ) : ℂ :=
  1 / (((γ 0 : ℂ) + 2 - 4 * s) * ((γ 1 : ℂ) + 1 - 2 * s))

/-- The chart zeta functional of a monomial on the strip. -/
theorem chartZeta_mono (γ : Fin 2 → ℕ) {s : ℂ} (hs : ZetaStrip tieH tieK s) :
    chartZeta (fun u => mono γ u) tieH tieK s = monoTerm γ s := by
  have hs' : ZetaStrip (fun i => γ i + tieH i) tieK s := fun i => by
    have := hs i
    have h0 : (0 : ℝ) ≤ γ i := Nat.cast_nonneg _

/-- The polar data at `½` of one monomial term: a double pole `c/8` for `γ = 0`, a simple pole
`−c/(2γ₀)` on the exceptional wall (`γ₁ = 0`), `−c/(4γ₁)` on the strict transform (`γ₀ = 0`),
nothing otherwise. -/
noncomputable def monoA (γ : Fin 2 → ℕ) (c : ℝ) : ℕ → ℂ := fun q =>
  if q = 1 then (if γ 0 = 0 ∧ γ 1 = 0 then (c : ℂ) / 8 else 0)
  else if q = 0 then
    (if γ 1 = 0 ∧ γ 0 ≠ 0 then -(c : ℂ) / (2 * γ 0)
      else if γ 0 = 0 ∧ γ 1 ≠ 0 then -(c : ℂ) / (4 * γ 1) else 0)
  else 0

/-- The polar part of one monomial term, written out. -/
theorem polarPart_monoA (γ : Fin 2 → ℕ) (c : ℝ) (s : ℂ) :
    polarPart 1 (monoA γ c) ((1 / 2 : ℝ) : ℂ) s =
      monoA γ c 0 / (s - (1 / 2 : ℝ)) + monoA γ c 1 / (s - (1 / 2 : ℝ)) ^ 2 := by
  unfold polarPart
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  simp

/-- Near `½`, the monomial term minus its polar part is bounded. -/
theorem monoTerm_sub_polarPart_isBigO (γ : Fin 2 → ℕ) (c : ℝ) :
    (fun s => (c : ℂ) * monoTerm γ s - polarPart 1 (monoA γ c) ((1 / 2 : ℝ) : ℂ) s)
      =O[𝓝[≠] ((1 / 2 : ℝ) : ℂ)] fun _ => (1 : ℂ) := by
  -- the two non-resonant denominators are nonzero at `½` unless the exponent vanishes
  have hne0 : ∀ᶠ s in 𝓝[≠] ((1 / 2 : ℝ) : ℂ), s ≠ ((1 / 2 : ℝ) : ℂ) := self_mem_nhdsWithin

/-- The tie polar data of a polynomial amplitude: the sum of the monomial data. -/
noncomputable def tieA (S : Finset (Fin 2 → ℕ)) (c : (Fin 2 → ℕ) → ℝ) : ℕ → ℂ :=
  fun q => ∑ γ ∈ S, monoA γ (c γ) q

theorem polarPart_tieA (S : Finset (Fin 2 → ℕ)) (c : (Fin 2 → ℕ) → ℝ) (μ s : ℂ) :
    polarPart 1 (tieA S c) μ s = ∑ γ ∈ S, polarPart 1 (monoA γ (c γ)) μ s := by
  unfold polarPart tieA
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_div]

theorem differentiableOn_polyTerms (S : Finset (Fin 2 → ℕ)) (c : (Fin 2 → ℕ) → ℝ) (U : Set ℂ) :
    DifferentiableOn ℂ (fun s : ℂ => ∑ γ ∈ S, (c γ : ℂ) * monoTerm γ s)
      (U \ (S.image (fun γ => (((γ 0 : ℂ) + 2) / 4)) ∪
/-- ★★★ **The tie formula for polynomial amplitudes on the blow-up chart**: at `μ = ½`, the
polar coefficients of `η = Σ_γ c_γ u^γ` on the chart `h = (1,0)`, `k = (2,1)` are
`C_{½,2}[η] = c_{00}/8` and `C_{½,1}[η] = −Σ_{γ₀≥1} c_{γ₀0}/(2γ₀) − Σ_{γ₁≥1} c_{0γ₁}/(4γ₁)`. -/
theorem chartPolarCoeff_polyAmp_half (p : Fin 2 → ℕ) (hp0 : ∀ i, 0 < p i)
    (hμ : FlatStrip p tieH tieK ((1 / 2 : ℝ) : ℂ)) (S : Finset (Fin 2 → ℕ))
    (c : (Fin 2 → ℕ) → ℝ) :
    ∀ q ≤ 1, chartPolarCoeff p (polyAmp S c) tieH tieK (1 / 2) q = tieA S c q := by
  have hF := contDiff_polyAmp S c
  have hev := chartZetaAtDepth_eventuallyEq_of_eqOn_strip p hF tieH tieK tieK_pos hp0
    (Set.toFinite _) (differentiableOn_polyTerms S c _)
(chartPolarCoeff p η h k μ q is the library's polar coefficient of order q at μ of the chart zeta functional of a smooth amplitude η; FlatStrip p h k μ is the standing strip hypothesis of the polar-coefficient theory; the route is chartZetaAtDepth_eventuallyEq_of_eqOn_strip + chartPolarCoeff_eq_of_eventuallyEq, i.e. the uniqueness of principal parts.)

## Target 2 — Grammar/NaiveBayesSurrogate.lean (DXCVI)
240:theorem nbSurrogate {N v₁ v₂ : ℝ} (hN : 0 < N) (h₁ : 0 < v₁) (h₂ : 0 < v₂) (c u : ℝ) :
241-    ∫ p : ℝ × ℝ × ℝ, Real.exp (-N * p.1 ^ 2 / (2 * v₁)) *
242-        (Real.exp (-N * p.2.1 ^ 2 / (2 * v₂)) *
243-          (Real.exp (-N * p.2.2 ^ 2 / (2 * (v₁ * v₂))) *
244-            (2 * Real.log (Real.sqrt (v₁ * v₂) / |p.2.2|) ^ 2 - c + u * Real.sign p.2.2))) =
245-      2 * Real.pi * Real.sqrt (2 * Real.pi) * (v₁ * v₂) / (N * Real.sqrt N) *
246-        (Real.log N ^ 2 / 2 + (Real.eulerMascheroniConstant + Real.log 2) * Real.log N +
247-          2 * gaussLogSq / Real.sqrt (2 * Real.pi) - c) := by
248-  rw [Measure.volume_eq_prod, integral_prod_mul (f := fun x : ℝ => Real.exp (-N * x ^ 2 / (2 * v₁)))
(gaussLogSq := ∫ e^{−z²/2} log²|z| dz, left as a constant.)

## Target 3 — Grammar/RankOneNormalTilt.lean (DXCVIII)
namespace Grammar

variable {M N : ℕ}

/-- The axis vector `α e₀`. -/
def axisVec (α : ℝ) : Fin (M + 1) → ℝ := Fin.cons α 0

/-- The Gauss–Newton differential `D(ξ, η) = x ηᵀ + ξ yᵀ` at the orbit point
`x = α e₀`, `y = β e₀`. -/
def gnD (α β : ℝ) (ξ : Fin (M + 1) → ℝ) (η : Fin (N + 1) → ℝ) (i : Fin (M + 1))
    (j : Fin (N + 1)) : ℝ :=
  axisVec α i * η j + ξ i * axisVec β j

/-- The squared Frobenius norm. -/
def frobSq (B : Fin (M + 1) → Fin (N + 1) → ℝ) : ℝ := ∑ i, ∑ j, B i j ^ 2

/-- The Frobenius inner product. -/
def frobInner (B Ξ : Fin (M + 1) → Fin (N + 1) → ℝ) : ℝ := ∑ i, ∑ j, B i j * Ξ i j

/-- The squared norm of the restriction of `Ξ` to the cross `{i = 0} ∪ {j = 0}`: `‖PΞ‖²`. -/
def crossNormSq (Ξ : Fin (M + 1) → Fin (N + 1) → ℝ) : ℝ :=
  ∑ i : Fin M, Ξ i.succ 0 ^ 2 + ∑ j : Fin N, Ξ 0 j.succ ^ 2 + Ξ 0 0 ^ 2

/-- The restriction of `Ξ` to the cross: the orthogonal projection `PΞ` onto `T_A`. -/
def cross (Ξ : Fin (M + 1) → Fin (N + 1) → ℝ) (i : Fin (M + 1)) (j : Fin (N + 1)) : ℝ :=
  if i = 0 ∨ j = 0 then Ξ i j else 0

@[simp] theorem axisVec_zero (α : ℝ) : axisVec (M := M) α 0 = α := by simp [axisVec]

@[simp] theorem axisVec_succ (α : ℝ) (i : Fin M) : axisVec α i.succ = 0 := by simp [axisVec]

81:theorem gnD_tangent (α β : ℝ) :
82-    gnD (M := M) (N := N) α β (axisVec α) (axisVec (-β)) = 0 := by
83-  funext i j
84-  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> simp [gnD]
85-
--
88:theorem frobSq_gnD (α β : ℝ) (ξ : Fin (M + 1) → ℝ) (η : Fin (N + 1) → ℝ) :
89-    frobSq (gnD α β ξ η) =
90-      β ^ 2 * ∑ i : Fin M, ξ i.succ ^ 2 + α ^ 2 * ∑ j : Fin N, η j.succ ^ 2 +
91-        (β * ξ 0 + α * η 0) ^ 2 := by
92-  unfold frobSq
--
121:theorem cross_eq_gnD {α β : ℝ} (hα : α ≠ 0) (hβ : β ≠ 0) (Ξ : Fin (M + 1) → Fin (N + 1) → ℝ) :
122-    cross Ξ = gnD α β (fun i => Ξ i 0 / β) (Fin.cons 0 fun j => Ξ 0 j.succ / α) := by
123-  funext i j
124-  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
125-    simp [gnD, cross, Fin.succ_ne_zero]
--
132:theorem frobInner_gnD_sub_cross (α β : ℝ) (ξ : Fin (M + 1) → ℝ) (η : Fin (N + 1) → ℝ)
133-    (Ξ : Fin (M + 1) → Fin (N + 1) → ℝ) :
134-    frobInner (gnD α β ξ η) (fun i j => Ξ i j - cross Ξ i j) = 0 := by
135-  unfold frobInner
136-  simp only [Fin.sum_univ_succ, gnD_zero_succ, gnD_succ_succ, cross, true_or, or_true, if_true,
--
141:noncomputable def normalCoord (α β ρ : ℝ) (v : (Fin M → ℝ) × (Fin N → ℝ) × ℝ) :
142-    (Fin (M + 1) → ℝ) × (Fin (N + 1) → ℝ) :=
143-  (Fin.cons (β * v.2.2 / ρ) v.1, Fin.cons (α * v.2.2 / ρ) v.2.1)
144-
145-/-- The one-dimensional normal integral with a linear field: for `n, c > 0`,
167:theorem integral_rankOne_normal_tilt {n α β ρ : ℝ} (hn : 0 < n) (hα : 0 < α) (hβ : 0 < β)
168-    (hρ : 0 < ρ) (hρ2 : ρ ^ 2 = α ^ 2 + β ^ 2) (Ξ : Fin (M + 1) → Fin (N + 1) → ℝ) :
169-    ∫ v : (Fin M → ℝ) × (Fin N → ℝ) × ℝ,
170-        Real.exp (-n * frobSq (gnD α β (normalCoord α β ρ v).1 (normalCoord α β ρ v).2) / 2 +
171-          Real.sqrt n * frobInner (gnD α β (normalCoord α β ρ v).1 (normalCoord α β ρ v).2) Ξ) =
172-      Real.sqrt (2 * Real.pi / n) ^ (M + N + 1) / (β ^ M * α ^ N * ρ) *
173-        Real.exp (crossNormSq Ξ / 2) := by
174-  have hpt : ∀ v : (Fin M → ℝ) × (Fin N → ℝ) × ℝ,
175-      Real.exp (-n * frobSq (gnD α β (normalCoord α β ρ v).1 (normalCoord α β ρ v).2) / 2 +

Numerics: normal_tilt_check.py — quadrature vs closed form 3e-10; at generic orbit points (ta, b/t), ΞᵀD(DᵀD)⁺DᵀΞ equals the cross norm in the rotated basis and is t-independent to 1e-16; eig(DᵀD) = {|y|², |x|², |x|²+|y|², 0}.

## What is still derivation-only in the note (candidates for the next round)
(a) Cone: the averaged posterior E_ξ[posterior] claim needs a domination argument (integrability of e^{ξ²/2}-type tilts against N(0,1) fails; e^{ξ₂²/2} is not integrable).
(b) Blow-up: the tie formula for SMOOTH amplitudes (Taylor to chart depth + remainder flat on the walls); the identification of the polar chart with the blow-up chart; assembly over the two crossing points.
(c) DLN flat prior, general L: Z_N = √(2π)/(L−1)! · N^{−1/2} Q_{L−1}(log N − log 2) + O(e^{−N/2}) with Q from Γ^{(j)}(½); Gaussian prior A_{L−1} N^{−1/2} P_{L−1}(log N + κ_L). Formal so far: L=2 flat to all orders (crossing_flat_allOrders), x²y⁶ flat to all orders, the frozen-field L=2 identities. Mathlib has Γ'(½) (hasDerivAt_Gamma_one_half) and digamma(½) but NO trigamma / Γ''(½); ψ'(½) = π²/2 would need a series for ψ' (hasSum_zeta_two exists).
(d) The value gaussLogSq = √(2π)(g²/4 + π²/8), g = γ + log 2 — same blocker (Γ''(½)).
(e) Naive Bayes: the passage from the surrogate to the actual KL (nonlinear remainder, Laplace with the log² amplitude); the cubic-phase term d N^{−2} (formula d = (8π/3)√V(1−2λ₁)(1−2λ₂)u₁u₂ derived, numerically confirmed).
(f) Rank-one: the Morse–Bott passage from the normal integral to Z_N[1;Ξ] (noncompact orbit; the truth's cut-off e^{−c/(2|x|²)}); Bessel closed forms C = 2(2π)^{λ} c^{−(M−1)/2} c^{(M−N)/4} K_{(M−N)/2}(√c).
(g) The state-density / population-coefficient dictionary: for each 1D reduction (2 log(1/|t|), |t|^{−2/3} − 1, the naive Bayes ρ(λ,μ)) the note states the polar distributions (Mellin data) as derivations; formal are the densities and the exact Z_N identities.

Library facts you may rely on: the chart polar-coefficient theory (chartPolarCoeff, chartZetaAtDepth, uniqueness of principal parts, IsBigO route) for smooth amplitudes on boxes with monomial phases; monomial Mellin integrals (integral_box_cpowWeight); the resolved/global leading-measure theory; Gaussian quadratic integrals (integral_exp_quadratic_real, integral_cexp_quadratic), Gamma integrals (integral_rpow_mul_exp_neg_mul_rpow), Γ'(½); polar coordinates (lintegral_polar); Fubini on products and Pi types.

## Questions
1. Fidelity check (brief): do the three theorem statements above say what the note claims (tie formula C_{½,2} = c₀₀/8, C_{½,1} = wall finite parts; surrogate with c₃ = π√(2π)V; tilt = e^{‖PΞ‖²/2} independent of orbit position)? Flag any mismatch of convention (C vs A polar conventions, factor 1/(2k), sign of the simple-pole coefficient, normalisation of the normal coordinates) that the note must state.
2. Rank the next three day-sized formal targets from (a)–(g) (or propose others) by value-per-effort for the note, with a concrete Lean statement for each and the proof route through the library facts above. Prefer targets that produce NEW mathematics (a formula or identity not yet formal) over infrastructure. State explicitly which items you would leave as derivations.
3. For (b), is the smooth tie formula worth doing now: give the cleanest statement (which decomposition η = η₀₀ + u g₁(u) + v g₂(v) + uv ρ(u,v), what regularity is needed on g₁, g₂, ρ for the strip-holomorphy step) and estimate the size.
Answer concisely with Lean-facing detail.
