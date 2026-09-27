You are Astra, design consultant for the Lean 4 formalisation (repo timaeus-research/grammar, namespace Grammar, main 4f13a52, 1020 modules, zero sorry/axiom) of the examples note `examples_slop.tex`. Your round-28 route B is FULLY EXECUTED: DCLXXXII (`RealDigammaSeries.lean`, modules 1–2 exactly as you specified, including the two-endpoint decay bound) and DCLXXXIII (`DigammaSeriesComplex.lean`, modules 3–4: the half-ball, `Complex.differentiableOn_tsum_of_summable_norm`, reality of `ψ` on `(0,∞)` via `HasDerivAt.comp_ofReal`/`ofReal_comp` uniqueness, the principle of isolated zeros `AnalyticAt.frequently_eq_iff_eventually_eq` on the points `1/(m+3)` in place of the identity theorem, iterated `Complex.hasSum_deriv_of_summable_norm` with the order-zero series kept separate, `hasSum_psiOneCoeff`, ★★★ `psiOneCoeff_eq_zeta : ψ_j = (−1)^{j+1} riemannZeta (j+1)` for `j ≥ 1`, and `λ₃ = −2 Re ζ(3)`, `λ₄ = 6 Re ζ(4)`, `λ₅ = −24 Re ζ(5)`), plus DCLXXXIV (`DepthZetaClosedForms.lean`: `ζ(3), ζ(5)` real, `ζ(4) = π⁴/90` from Mathlib, and `Q₃, D₄, D₅, E₅, Q₅` in ζ-values — your caveat about the external `(2π)^{−3/2}` factor is respected: `D₄ = (2b³ + 7π²b + 12ζ(3))/(24π√(2π))`). §2 of the note (the Gaussian deep linear network) is now formally closed at every depth with no symbol: every `P_L`, `Q_L` is a polynomial in `log 2, γ, π²` and ζ-values, depths ≤ 5 written out. Numerics to 1e-30 throughout.

## HEADLINES rows DCLXXXII–DCLXXXIV
| **DCLXXXII** | ★★★ **THE REAL DIGAMMA SERIES `ψ(1+x) − ψ(1) = Σ_{n≥0} x/((n+1)(n+1+x))` WITHOUT AN INTEGRAL REPRESENTATION (u1018; the ζ-bridge, modules 1–2; Astra round-28 route B)**: `RealDigammaSeries.lean` — `realDigamma x = (Complex.digamma ↑x).re`; `realGamma_eq_re`, `hasDerivAt_realGamma` (`HasDerivAt.real_of_complex` of DCVIII's `hasDerivAt_Gamma_of_re_pos`), `realDigamma_eq_div` (`Complex.digamma_def`, `logDeriv_apply`, `Complex.Gamma_ofReal`, `Complex.div_ofReal_re`), `hasDerivAt_log_Gamma` / `deriv_log_Gamma_eq_realDigamma` (`(log ∘ Γ)' = ψ` on `x > 0`, `HasDerivAt.log` with `Real.Gamma_pos_of_pos`), ★ `monotoneOn_realDigamma` (Bohr–Mollerup's `Real.convexOn_log_Gamma` + `ConvexOn.monotoneOn_deriv`), `realDigamma_add_one` (Mathlib's `digamma_apply_add_one` with `ne_neg_nat_of_re_pos`, real part via `← Complex.ofReal_inv`), ★★ `abs_realDigamma_nat_shift_sub_le : |ψ(N+1+x) − ψ(N+1)| ≤ 1/N` for `N ≥ 1`, `−1 ≤ x ≤ 1` (monotone between `ψ(N)` and `ψ(N+2)`, the two endpoint differences `1/N`, `1/(N+1)`), `tendsto_realDigamma_nat_shift_sub` (`squeeze_zero_norm'` + `tendsto_one_div_atTop_nhds_zero_nat`), `sum_realDigamma_telescope` (`Σ_{n<N} x/((n+1)(n+1+x)) = [ψ(1+x) − ψ(1)] − [ψ(N+1+x) − ψ(N+1)]`, induction on `N` with the functional equation), `summable_realDigamma_series` (shift by one, envelope `|x|/(n+1)²` — the unshifted envelope fails at `n = 0` for `x` near `−1`), ★★★ `hasSum_realDigamma_sub` (`Summable.hasSum_iff_tendsto_nat` + the decay). Astra round 28 (`tide-log/gpt6_examples_round28_v1.md`): DCLXXX–DCLXXXI fidelity confirmed; route B (convexity replaces the singular Beta limit) chosen over the subtracted Beta integral; modules 3–4 next: `digammaSeries z = Σ' z/((n+1)(n+1+z))` analytic on `‖z‖ < ½` (`differentiableOn_tsum_of_summable_norm`, majorant `1/k²`), equal to `digamma(1+z) − digamma 1` there by the identity theorem on the real points `1/(m+3)`, then coefficients by iterated `hasSum_deriv_of_summable_norm` (order zero kept separate; `(d/dz)^j z/(k(k+z)) = (−1)^{j+1}j!/(k+z)^{j+1}`, bound `j!2^{j+1}/k^{j+1}`), `hasSum_psiOneCoeff`, `psiOneCoeff_eq_zeta : ψ_j = (−1)^{j+1}ζ(j+1)` via `zeta_eq_tsum_one_div_nat_add_one_cpow`; afterwards a depth-≤5 ζ-valued closure module. Lean: `positivity` cannot see `0 < n+2+x` from `−1 < x` — `mul_pos … (by linarith)`; `realDigamma_eq_div` needs no hypothesis (total division). | RealDigammaSeries.lean |
| **DCLXXXIII** | ★★★ **THE ζ-BRIDGE: `ψ_j = (−1)^{j+1}ζ(j+1)`, HENCE `λ₃ = −2ζ(3)`, `λ₄ = 6ζ(4)`, `λ₅ = −24ζ(5)` — §2 CLOSED WITH NO SYMBOLS (u1019; examples_slop §2; Astra round-28 route B, modules 3–4)**: `DigammaSeriesComplex.lean` — `dsTerm n z = z/((n+1)(n+1+z))`, `digammaSeries = Σ'`, `halfBall = ball 0 ½` (`half_le_norm_add : (n+1)/2 ≤ ‖n+1+z‖` via `norm_le_add_norm_add`, `norm_dsTerm_le ≤ 1/(n+1)²`, `differentiableOn_dsTerm`), `analyticOnNhd_digammaSeries` (Mathlib's `Complex.differentiableOn_tsum_of_summable_norm` + `DifferentiableOn.analyticOnNhd`); reality `deriv_Gamma_ofReal` (`HasDerivAt.comp_ofReal` vs `HasDerivAt.ofReal_comp` + `HasDerivAt.unique`), `digamma_ofReal : ψ(↑x) = ↑(realDigamma x)`; `digammaSeries_ofReal` (DCLXXXII's real series through `Complex.hasSum_ofReal`), `analyticAt_digamma_one_add`, ★★ `digammaSeries_eventuallyEq` (`AnalyticAt.frequently_eq_iff_eventually_eq` — the principle of isolated zeros replaces the identity theorem — on the real points `1/(m+3) → 0` in `𝓝[≠] 0`, `Tendsto.frequently`); `analyticAt_iteratedDeriv`, `iteratedDeriv_inv_const_add` (`(d/dw)^j (c+w)⁻¹ = (−1)^j j!(c+w)^{−(j+1)}` on `c + z ≠ 0`, eventual equality on the open set `{c + w ≠ 0}`), `dsTerm_eq` (partial fractions), `iteratedDeriv_dsTerm` (`(−1)^{j+1}j!/(n+1+z)^{j+1}` for `j ≥ 1`), `norm_iteratedDeriv_dsTerm_le ≤ j!2^{j+1}/(n+1)²`, `differentiableOn_iteratedDeriv_dsTerm`, `summable_bound`, ★★ `hasSum_iteratedDeriv_digammaSeries` (`Nat.le_induction` from `j = 1` with `Complex.hasSum_deriv_of_summable_norm` at each step and the eventual equality `iteratedDeriv j S = Σ' iteratedDeriv j (dsTerm n)` on the half-ball), ★★★ `hasSum_psiOneCoeff : Σ_{n≥0}(−1)^{j+1}/(n+1)^{j+1} = ψ_j` (`j ≥ 1`; `digammaSeries_eventuallyEq.iteratedDeriv_eq`, `iteratedDeriv_const_add`, `iteratedDeriv_comp_const_add'`, `gammaLogDeriv_eq_digamma`, `HasSum.div_const`), ★★★ `psiOneCoeff_eq_zeta : ψ_j = (−1)^{j+1} riemannZeta(j+1)` (`zeta_eq_tsum_one_div_nat_add_one_cpow`, `Complex.cpow_natCast`, `tsum_mul_left`), `psiOneCoeff_two/three/four_eq_zeta`, ★★★ `gammaLogThirdOne_eq_zeta : λ₃ = −2 Re ζ(3)`, `gammaLogFourthOne_eq_zeta : λ₄ = 6 Re ζ(4)`, `gammaLogFifthOne_eq_zeta : λ₅ = −24 Re ζ(5)`. With DCLXXV–DCLXXIX every coefficient of every `P_L` and every `Q_L` of the Gaussian DLN is a polynomial in `log 2`, `γ`, `π²` and the ζ-values, with NO symbol left; in particular `Q₃ = [c₁³/6 + c₁π²/2 + (4/3)ζ(3)]/(4π)`, `D₄ = (b³/6 + 7π²b/12 + ζ(3))/(2π)^{3/2}`, `E₅` with `ζ(3)` and `ζ(4)` follow by rewriting. Lean: `Complex.differentiableOn_tsum_of_summable_norm`/`hasSum_deriv_of_summable_norm` live in the `Complex` namespace; `rw [deriv_Gamma_ofReal]` also rewrites inside the `.re` on the other side (finish with `Complex.ofReal_re`); a `funext`-free `fun n => …` with `(n : ℂ)` inside infers `n : ℂ` — annotate the binder. | DigammaSeriesComplex.lean |
| **DCLXXXIV** | ★★★ **THE GAUSSIAN DLN THROUGH DEPTH FIVE IN ζ-VALUES (u1020; examples_slop §2; the reader-facing closure)**: `DepthZetaClosedForms.lean` — `riemannZeta_three_im = 0`, `riemannZeta_five_im = 0` (from the real jets `psiOneCoeff_im`), `riemannZeta_four_re = π⁴/90` (Mathlib's `riemannZeta_four`), regression `psiOneCoeff_one_eq_zeta : ψ₁ = ζ(2)` (Mathlib's `riemannZeta_two`), `gammaLogFourthOne_eq_pi : λ₄ = π⁴/15`; ★★★ `depthThreeJetCubic_eq_zeta : c₃ = c₁³/6 + c₁π²/2 + (4/3)ζ(3)`, ★★★ `residualMass_three_eq_zeta : Q₃ = [c₁³/6 + c₁π²/2 + (4/3)ζ(3)]/(4π)`, ★★★ `depthFourConst_eq_zeta : D₄ = (2b³ + 7π²b + 12ζ(3))/(24π√(2π))` (= `(b³/6 + 7π²b/12 + ζ(3))/(2π)^{3/2}`), ★★★ `depthFiveLinCoeff_eq_zeta : D₅ = [a³/6 + 2π²a/3 + (2/3)ζ(3)]/(4π²)`, ★★★ `depthFiveConst_eq_zeta : E₅ = [a⁴/24 + π²a²/3 + (2/3)aζ(3) + 5π⁴/18]/(4π²)`, ★★★ `residualMass_five_eq_zeta : Q₅ = [a⁵/120 + π²a³/9 + a²ζ(3)/3 + 5π⁴a/18 + 4π²ζ(3)/9 + (26/5)ζ(5)]/(8π²)` (`ζ(k)` as `(riemannZeta k).re`), all by rewriting DCLXXII/DCLXXIII/DCLXXIX with DCLXXXIII and `ring`. Numerics: `Q₃ = 0.8191866`, `D₄ = 0.7654005`, `D₅ = 0.3553669`, `E₅ = 1.0205207`, `Q₅ = 0.8766618` against the Gamma-product jets (`gauss_zeta_closed_forms_check.py`). §2 of the note: every population coefficient of the Gaussian DLN at every depth is a theorem in `log 2, γ, π²` and the ζ-values, depths ≤ 5 written out. | DepthZetaClosedForms.lean |

## Public statements of DCLXXXIII (the ζ-bridge)
```lean
/-- The summand `z/((n+1)(n+1+z))`. -/
noncomputable def dsTerm (n : ℕ) (z : ℂ) : ℂ := z / (((n : ℂ) + 1) * ((n : ℂ) + 1 + z))

/-- `S(z) = Σ_{n≥0} z/((n+1)(n+1+z))`. -/
noncomputable def digammaSeries (z : ℂ) : ℂ := ∑' n : ℕ, dsTerm n z

/-- The half-ball `‖z‖ < ½`. -/
def halfBall : Set ℂ := Metric.ball 0 (1 / 2)

theorem isOpen_halfBall : IsOpen halfBall := Metric.isOpen_ball

theorem zero_mem_halfBall : (0 : ℂ) ∈ halfBall := by simp [halfBall]

theorem norm_lt_half_of_mem_halfBall {z : ℂ} (hz : z ∈ halfBall) : ‖z‖ < 1 / 2

theorem norm_natCast_add_one (n : ℕ) : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1

theorem half_le_norm_add {z : ℂ} (hz : z ∈ halfBall) (n : ℕ) :
    ((n : ℝ) + 1) / 2 ≤ ‖(n : ℂ) + 1 + z‖

theorem add_ne_zero_of_mem_halfBall {z : ℂ} (hz : z ∈ halfBall) (n : ℕ) :
    (n : ℂ) + 1 + z ≠ 0

theorem natCast_add_one_ne_zero (n : ℕ) : (n : ℂ) + 1 ≠ 0

theorem summable_inv_sq : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2)

theorem norm_dsTerm_le {z : ℂ} (hz : z ∈ halfBall) (n : ℕ) :
    ‖dsTerm n z‖ ≤ 1 / ((n : ℝ) + 1) ^ 2

theorem differentiableOn_dsTerm (n : ℕ) : DifferentiableOn ℂ (dsTerm n) halfBall

/-- `S` is analytic on the half-ball. -/
theorem analyticOnNhd_digammaSeries : AnalyticOnNhd ℂ digammaSeries halfBall

theorem deriv_Gamma_ofReal {x : ℝ} (hx : 0 < x) :
    deriv Complex.Gamma (x : ℂ) = (((deriv Complex.Gamma (x : ℂ)).re : ℝ) : ℂ)

/-- `ψ` is real on `(0,∞)`. -/
theorem digamma_ofReal {x : ℝ} (hx : 0 < x) :
    Complex.digamma (x : ℂ) = ((realDigamma x : ℝ) : ℂ)

theorem digammaSeries_ofReal {x : ℝ} (hx0 : -1 < x) (hx1 : x ≤ 1) :
    digammaSeries (x : ℂ) = Complex.digamma (1 + (x : ℂ)) - Complex.digamma 1

theorem analyticAt_digamma_one_add :
    AnalyticAt ℂ (fun z : ℂ => Complex.digamma (1 + z) - Complex.digamma 1) 0

/-- ★★ `S(z) = ψ(1+z) − ψ(1)` near `0` (isolated zeros on the real points `1/(m+3)`). -/
theorem digammaSeries_eventuallyEq :
    digammaSeries =ᶠ[𝓝 (0 : ℂ)] fun z => Complex.digamma (1 + z) - Complex.digamma 1

theorem analyticAt_iteratedDeriv {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (n : ℕ) :
    AnalyticAt ℂ (iteratedDeriv n f) z

/-- `(d/dw)^j (c + w)⁻¹ = (−1)^j j! (c+w)^{−(j+1)}` where `c + z ≠ 0`. -/
theorem iteratedDeriv_inv_const_add (c : ℂ) (j : ℕ) :
    ∀ {z : ℂ}, c + z ≠ 0 →
      iteratedDeriv j (fun w : ℂ => (c + w)⁻¹) z =
        (-1) ^ j * (j.factorial : ℂ) * ((c + z) ^ (j + 1))⁻¹

theorem dsTerm_eq (n : ℕ) {z : ℂ} (hz : (n : ℂ) + 1 + z ≠ 0) :
    dsTerm n z = ((n : ℂ) + 1)⁻¹ + (-1) * ((n : ℂ) + 1 + z)⁻¹

/-- `(d/dz)^j` of the summand for `j ≥ 1`: `(−1)^{j+1} j!/(n+1+z)^{j+1}`. -/
theorem iteratedDeriv_dsTerm (n j : ℕ) (hj : 1 ≤ j) {z : ℂ} (hz : z ∈ halfBall) :
    iteratedDeriv j (dsTerm n) z =
      (-1) ^ (j + 1) * (j.factorial : ℂ) * (((n : ℂ) + 1 + z) ^ (j + 1))⁻¹

theorem norm_iteratedDeriv_dsTerm_le (n j : ℕ) (hj : 1 ≤ j) {z : ℂ} (hz : z ∈ halfBall) :
    ‖iteratedDeriv j (dsTerm n) z‖ ≤ (j.factorial : ℝ) * 2 ^ (j + 1) / ((n : ℝ) + 1) ^ 2

theorem differentiableOn_iteratedDeriv_dsTerm (n j : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv j (dsTerm n)) halfBall := fun z hz =>
  (analyticAt_iteratedDeriv ((differentiableOn_dsTerm n).analyticOnNhd isOpen_halfBall z hz)
    j).differentiableAt.differentiableWithinAt

theorem summable_bound (j : ℕ) :
    Summable (fun n : ℕ => (j.factorial : ℝ) * 2 ^ (j + 1) / ((n : ℝ) + 1) ^ 2)

/-- ★★ Termwise differentiation of `S` at every order `j ≥ 1` on the half-ball. -/
theorem hasSum_iteratedDeriv_digammaSeries (j : ℕ) (hj : 1 ≤ j) :
    ∀ {z : ℂ}, z ∈ halfBall →
      HasSum (fun n : ℕ => iteratedDeriv j (dsTerm n) z) (iteratedDeriv j digammaSeries z)

/-- ★★★ **`Σ_{n≥0} (−1)^{j+1}/(n+1)^{j+1} = ψ_j`** for `j ≥ 1`. -/
theorem hasSum_psiOneCoeff (j : ℕ) (hj : 1 ≤ j) :
    HasSum (fun n : ℕ => (-1 : ℂ) ^ (j + 1) / ((n : ℂ) + 1) ^ (j + 1)) (psiOneCoeff j)

/-- ★★★ **The ζ-bridge**: `ψ_j = (−1)^{j+1} ζ(j+1)` for `j ≥ 1`. -/
theorem psiOneCoeff_eq_zeta (j : ℕ) (hj : 1 ≤ j) :
    psiOneCoeff j = (-1 : ℂ) ^ (j + 1) * riemannZeta ((j : ℂ) + 1)

theorem psiOneCoeff_two_eq_zeta : psiOneCoeff 2 = -riemannZeta 3

theorem psiOneCoeff_three_eq_zeta : psiOneCoeff 3 = riemannZeta 4

theorem psiOneCoeff_four_eq_zeta : psiOneCoeff 4 = -riemannZeta 5

/-- `λ₃ = −2ζ(3)`. -/
theorem gammaLogThirdOne_eq_zeta : gammaLogThirdOne = -2 * (riemannZeta 3).re

/-- `λ₄ = 6ζ(4)`. -/
theorem gammaLogFourthOne_eq_zeta : gammaLogFourthOne = 6 * (riemannZeta 4).re

/-- `λ₅ = −24ζ(5)`. -/
theorem gammaLogFifthOne_eq_zeta : gammaLogFifthOne = -24 * (riemannZeta 5).re
```

## The note's remaining derivations outside §2 (verbatim extracts)

CONE §3 (the population expansion for a general smooth prior is a derivation; the Gaussian prior is closed; the third coefficient is now a theorem): by completing the square on each half-line of the Leray integral; every coefficient of the expansion in $N^{-1/2}$ is a Taylor coefficient of this expression, and at $a=0$ it reads $4\pi^2N^{-1/2}e^{1/(2N)}T(1/\sqrt N)=4\pi^2N^{-1/2}[\sqrt{\pi/2}-N^{-1/2}+\tfrac12\sqrt{\pi/2}\,N^{-1}-\cdots]$, the vertex term $-4\pi^2N^{-1}$ in its place (the script \texttt{cone\_closed\_check.py} confirms the closed form against quadrature to $10^{-16}$ and the three-term expansion); the third coefficient is a theorem as well (\texttt{Grammar/ConeThirdCoefficient.lean}, \texttt{cone\_third\_coefficient}): with $F(x)=e^{x^2/2}T(x)$ one has $T'=-e^{-x^2/2}$, hence $F'=xF-1$, $F(0)=\sqrt{\pi/2}$, $F'(0)=-1$, $F''(0)=\sqrt{\pi/2}$, and one l'H\^opital step gives $(F(x)-\sqrt{\pi/2}+x)/x^2\to\sqrt{\pi/2}/2$, so that $N^{3/2}\big(\Zcal_N[1]-4\pi^2\sqrt{\pi/2}\,N^{-1/2}+4\pi^2N^{-1}\big)\to2\pi^2\sqrt{\pi/2}$, the coefficient $c_{3/2,0}=2\pi^2\sqrt{\pi/2}$ of the cone's population expansion at zero field (\texttt{cone\_third\_coefficient\_check.py}). The averaged first correction of the posterior mean of $u_1^2$ is a theorem as well (\texttt{Grammar/ConeAveragedPosterior.lean}, \texttt{cone\_averaged\_correction}), with the frozen ratio through the Leray densities and the explicit Gaussian-integrable envelope described above. The Leray density of $u_1^2e^{-|u|^2/2}$ is a theorem as well (\texttt{Grammar/ConeLerayWeighted.lean}). The Leray decomposition for a general prior (\cref{prop:cone_leray}), 

BLOW-UP §4: (\texttt{blowupLaplace\_two\_term\_bound}; the $O(N^{-1}\log N)$ form is \texttt{blowupLaplace\_two\_term}), so $c_{1/2,1}=\sqrt{\pi/2}$ and $c_{1/2,0}=\sqrt{\pi/2}\,(5\log2-\gamma_E)$ are theorems and match the Gamma transform of the Laurent data, $\Gamma(\tfrac12)A_{1/2,2}$ and $\Gamma(\tfrac12)A_{1/2,1}-\Gamma'(\tfrac12)A_{1/2,2}$. The route is Bessel-free and the same as for the depth-two Gaussian network: the Gaussian integral in $y$ at fixed $x$ gives $\Zcal_N[1]=\sqrt{2\pi}\int_\R e^{-Nx^4/2}e^{-x^2/2}(1+Nx^2)^{-1/2}dx$ exactly (\texttt{blowupLaplace\_eq\_integral}); with $N=m^4$ and $x=u/m$ this is $\sqrt{2\pi}\,m^{-2}\int_0^\infty2a_m(u)(u^2+m^{-2})^{-1/2}du$ with the amplitude $a_m(u)=e^{-u^4/2}e^{-u^2/2m^2}$ (\texttt{blowupLaplace\_eq\_ampJ}); the expansion $\int_0^\infty2a(u)(u^2+\varepsilon)^{-1/2}du=\log(4/\varepsilon)+R_a+O(\varepsilon\log(1/\varepsilon))$ holds for every amplitude with $0\le a\le1$, $1-a(u)\le Au^2$ near $0$ and $a(u)\le e^{-u/2}$ for $u\ge1$, with the renormalised constant $R_a=\int_0^\infty(a(u)-\mathbf 1_{(0,1]}(u))\,2\,du/u$ and the explicit remainder $A\varepsilon(\log(1/\varepsilon)+1)+4\varepsilon$ (\texttt{Grammar/AmplitudeJ.lean}, \texttt{ampJ\_two\_term}); for $a_\infty(u)=e^{-u^4/2}$ the constant is $R_\infty=\tfrac12(\log2-\gamma_E)$ by the substitutions $y=u^4$ and $y=2v$ in the renormalised exponential integral (\texttt{ampRenorm\_blowAmpInf}), and $|R_{a_m}-R_\infty|\le3/m^2$; more generally $\int_0^\infty(e^{-u^{2k}/2}-\mathbf 

RANK-ONE §5 (what is formal): The column-wise Gaussian integration \eqref{eq:rankone_reduction}, with the field, is a theorem: \texttt{integral\_rankOne\_gauss} in \texttt{Grammar/RankOneGauss.lean} states, for every $M,N$, every $n\ge 0$, every $x$, truth $A$ and field $\Xi$,

NAIVE BAYES §6 (what remains a derivation): exactly, with $m_2=\int e^{-z^2/2}\log^2|z|\,dz$: the coefficient $c_3=\pi\sqrt{2\pi}V$ of $N^{-3/2}\log^2N$, the shift $g=\gamma+\log2$ from $\Gamma'(\tfrac12)$, and the vanishing of the sign jump at this order are theorems (the theorem is an exact identity for the surrogate integral, not an asymptotic statement about the Kullback--Leibler phase); what remains a derivation is the replacement of the exact phase and density by the surrogate (the $O(N^{-2})$ term and the $\log V(\lambda)$ dependence); the value $m_2=\sqrt{2\pi}(g^2/4+\pi^2/8)$ is a theorem (\texttt{Grammar/NaiveBayesLogSqMoment.lean}, \texttt{integral\_gaussian\_log\_abs\_sq}: by evenness and $z=\sqrt{2t}$, $m_2=\tfrac1{2\sqrt2}\int_0^\infty e^{-t}t^{-1/2}(\log2+\log t)^2dt=\tfrac1{2\sqrt2}[\log^22\,\Gamma(\tfrac12)+2\log2\,\Gamma'(\tfrac12)+\Gamma''(\tfrac12)]$ with the Gamma log-moments at $\tfrac12$ already formalised, $\Gamma'(\tfrac12)=-\sqrt\pi(\gamma_E+2\log2)$ and $\Gamma''(\tfrac12)=\sqrt\pi((\gamma_E+2\log2)^2+\pi^2/2)$). The polar distributions of the fibre density itself are theorems (\texttt{Grammar/LogSquareDensityPolar.lean}, \texttt{logSqMellinFull\_polar}): at fixed means, with $\ell=\log\sqrt V$, $0<M\le1$ and a continuous test amplitude $\varphi$ with $|\varphi(\mu)-\varphi(0)|\le L|\mu|$, the Mellin transform $\int_{-M}^{M}\varphi(\mu)\big(2\log^2(\sqrt V/|\mu|)-c+b\operatorname{sgn}\mu\big)|\mu|^{-2s}d\mu$ continues from $\Re s<\tfrac12$ to $\Re s<1$ up to the rational part, with principal 

## Questions
1. Fidelity of DCLXXXIII–DCLXXXIV (brief): the isolated-zeros step (`∃ᶠ` along `1/(m+3)` in `𝓝[≠] 0`); the termwise-derivative bound `j!2^{j+1}/(n+1)²`; the cpow adapter `(n+1)^{(j+1 : ℂ)} = (n+1)^{j+1}`; the reality of `ζ(3)`, `ζ(5)` from the real jets; the five ζ-valued closed forms (please re-derive `Q₅ = [a⁵/120 + π²a³/9 + a²ζ(3)/3 + 5π⁴a/18 + 4π²ζ(3)/9 + (26/5)ζ(5)]/(8π²)` from your `h_{5,5}` with `λ₃ = −2ζ(3)`, `λ₄ = π⁴/15`, `λ₅ = −24ζ(5)` — my first attempt had `5aπ⁴/18` from a slip and the numerics caught it).
2. §2 POST-CLOSURE: is anything left there worth a unit? Candidates: (a) the flat-prior all-depth identity `Z_N[1] = √(2π)/(L−1)! N^{−1/2} Q_{L−1}(log N − log 2) + O(e^{−N/2})` with `Q_{L−1}` in polygamma values at ½ (the note's eq. dln_flat; the volume identity is a qd-seabed theorem, `L = 2` is formal) — now that `Γ^{(j)}(½)` are theorems via DCLXXVI/DCLXXVII, is the all-depth flat identity a day-sized Mellin computation?; (b) the depressed-polynomial form `P_L(t) = Σ …` with `κ_L = q_{L,0}` and the vanishing of the `t^{L−2}` coefficient at every depth (from `depthLogDerivCoeff_zero` + the recurrence — is it a two-line theorem now?); (c) the `1/log N` observable rates (`E[w_1²] ~ 2/(log N + κ_2)`) at every depth as leading-pole ratios; (d) nothing — move on.
3. POST-§2 RANKING with day-sized Lean interfaces: (v) cone with a general smooth prior: the Leray density's corner `B_F(0) = −2π²F(0)` and the `N^{−1}` vertex coefficient `c_{1,0}(f) = −4π²(fφ)(0)` for a general `F` — the formal route (bipolar coordinates + the smoothness of circle averages in `r²`) and the minimal statement; (vi) blow-up: the frozen quartic amplitude's linear coefficient `J_∞(ε) = log(4/ε) + R_∞ + ½√(π/2)ε + O(ε²log(1/ε))` (day-sized per round 27) and then the moving-amplitude cancellation and the `N^{−3/2}log N` coefficient `√(2π)/32`; (vii) naive Bayes: the surrogate replacement — what is the first honest theorem toward the exact-phase statement (a remainder bound `|Z_N − Z_N^{surr}| ≤ C N^{−2}log²N`, or the `log V(λ)` correction)?; (viii) rank-one beyond leading order (the first integer-step correction `c_1(f)`) or the zero-truth singular regime; (ix) a `taylorCoeff_div` quotient-jet tool with a named consumer. Please rank and give the exact statement for the top item.
4. Convention hazards for the ζ-valued forms (`(riemannZeta k).re` vs a real `ζ`; `Complex.cpow` at natural exponents; the sign `(−1)^{j+1}`).
Answer concisely with Lean-facing detail.
