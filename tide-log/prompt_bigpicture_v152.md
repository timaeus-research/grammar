# Consult #152 — from the coefficient law to a stochastic expansion of the chart evidence (the uniform remainder)

Context (your consults #148–#151). Everything up to your M6 is built and axiom-clean in the bridge repo:
- `chartTopCoeffLaw` / `jointChartTopCoeffLaw`: for each chart α (hypotheses `0 < k α i`, `0 < b_α`, smooth unit weight `η_α` with `DeepVanishing η_α b_α c`, `0 < μ₀`, `1 ≤ c`, jet order `R ≥ cubeOrder`), the coefficient `empCoeffRect η_α (−G_α(n,ω)) h_α k_α b_α μ₀ (c−1)` converges in distribution (jointly over α) to a continuous functional of the joint Gaussian jet limit; here `G_α(n,ω) = χ_α · ξ_n^α(ω)` is the cutoff-globalised empirical field of the smooth representative (`C^∞` on `ℝ^d` for every sample), and `chartXi = −ξ_n^α` a.s. on the box.
- `ae_totalEvidence_eq`: a.s. for all n ≥ 1, the grey book's evidence at β = 1 is `∫ e^{−nKₙ} dν = ∑_α empIntegralRect η_α (−G_α(n,ω)) h_α k_α b_α n + T(n,ω)` (smooth tail `T`, `T·n^λ/(log n)^{m−1} → 0` in probability in the grey book's `TailData`).

Grammar's deterministic expansion of the cube integral, for FIXED smooth η, ζ:
```lean
def CutoffExpansion (Q D : ℕ) (Z : ℝ → ℝ) (c : ℝ → ℕ → ℝ) : Prop :=
  ∀ L : ℝ, 0 < L → ∃ K : ℝ, ∀ᶠ N in atTop, |Z N - absSpectralSum Q D c L N| ≤ K * (N ^ (-L) * (1 + Real.log N) ^ D)
-- absSpectralSum Q D c L N = ∑_{μ ∈ latticeBelow Q L} N^{-μ} ∑_{j ≤ D} c μ j (log N)^j
theorem empRect_cutoffExpansion (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) (hk : ∀ i, 0 < k i) (hb : ∀ i, 0 < b i) :
  CutoffExpansion (Qamb k) (d - 1) (empIntegralRect η ζ h k b) (empCoeffRect η ζ h k b)
-- and the UNIFORM version on the unit box (the cube version is by exact dilation):
def FieldJetBound (η ζ : ℝ^d → ℝ) (p : Fin d → ℕ) (b C M' : ℝ) : Prop :=
  ∀ m ≤ p, ∀ τ ≥ 0, ∀ v ∈ closedBox d b, |∂^m (η · e^{τ ζ})(v)| ≤ C * (1 + τ)^{|p|} * exp (M' * τ)
theorem exists_fieldJetBound (hη) (hζ) (hζM : ∀ v ∈ closedBox d b, |ζ v| ≤ M') (p) : ∃ C ≥ 0, FieldJetBound η ζ p b C M'
theorem emp_cutoffExpansion_uniform (hk) (L' M' : ℝ) : ∃ K₀ ≥ 0, ∀ η ζ smooth, ∀ C, FieldJetBound η ζ (depthOf h k (max ⌈L'⌉₊ (L₀ h))) 1 C M' →
  ∀ N ≥ 1, |empIntegral η ζ h k N - absSpectralSum (Qamb k) (d - 1) (empCoeff η ζ h k) L' N| ≤ C * K₀ * (N ^ (-L') * (1 + log N) ^ (d - 1))
```
So the remainder constant is `C · K₀(L', M')` where `M'` bounds `|ζ|` on the box and `C` is the jet bound of the family `η e^{τζ}` (from jets of η and ζ up to order `|p|`, via Faà di Bruno / Leibniz — the dependence on the jets of ζ is polynomial but `exists_fieldJetBound` only exports existence).

The continuity/law machinery covers ONLY the top coefficient at an index (μ₀, c) under `DeepVanishing η b c` (coefficients of log degree ≥ c at μ₀ vanish; the (μ₀, c−1) coefficient is `smoothCoeff (η S_{μ₀}(ζ)/Γ(μ₀))`), Lipschitz in the `C^{cubeOrder}` jets on bounded jet sets. Nothing is proved about the LOWER log degrees `j < c−1` at μ₀, nor about the coefficients at indices `μ < μ₀` (each has its own top-coefficient theory under its own DeepVanishing level, not jointly assembled).

Stochastic inputs available: the joint law of the jets of order ≤ R in `∏_{(α,k,b)} C(box, ℝ)` (hence in `CubeJetSpace` per chart via continuous reconstruction), tightness of these laws (convergent ⇒ tight, Polish), a.s. smoothness of every path, and `TailData` (`T n ≤ A e^{−nβε/2} e^{βM_n²/2}`, `M_n = O_p(1)`).

## Questions

1. **Uniform jet bound.** To turn `emp_cutoffExpansion_uniform` into an `o_P` statement one needs `∀ B, ∃ C, ∀ ζ smooth, JetBoundOn p (closedBox) ζ B → FieldJetBound η ζ p b C B`. Is this the right lemma to add to grammar (statement shape, and the proof route — audit `exists_pdMulti_fieldFam_bound`'s constant vs. a fresh Leibniz/Faà-di-Bruno bound with explicit polynomial dependence), or is there a slicker route (e.g. state the remainder estimate directly with a constant continuous in the jet bound)?

2. **Tightness ⇒ o_P.** Given `Y_n := (jets of ζ_n)` tight in `CubeJetSpace` and the deterministic remainder bound `|Rem_n(ζ)| ≤ C(‖jet ζ‖) · K₀ · n^{−L'}(1+log n)^{d−1}` valid for all smooth ζ, the standard argument gives `n^{L'}(1+log n)^{−(d−1)} Rem_n(ζ_n) = O_P(1)`, hence `o_P` at any slower rate. Grammar has `tendstoInMeasure_zero_of_tight_bound` (|Y n| ≤ c(M n) r n, M n = O_p(1) nonneg, c monotone, r → 0 ⇒ Y → 0 in measure). Confirm this is the right assembly, and how to get the `O_p(1)` of `‖jet ζ_n‖` from tightness in Lean (Mathlib: `IsTightMeasureSet` ⇒ for each ε a compact hence bounded set with mass ≥ 1−ε ⇒ `∀ η > 0, ∃ R, ∀ n, P(‖Y_n‖ > R) ≤ η` — exact statement shape?).

3. **What stochastic expansion can honestly be stated?** Options: (a) the chart-wise statement "for every L', `n^{L'} (1+log n)^{-(d-1)} [empIntegralRect η_α (−G_α(n)) … n − absSpectralSum (Qamb k_α) (d−1) (empCoeffRect η_α (−G_α(n)) …) L' n] → 0` in probability" — an expansion whose RANDOM coefficients are the canonical cube coefficients at the random field (no law claimed for lower coefficients); combined with the joint law of the top coefficients at the admissible indices; (b) the same for the total evidence via `ae_totalEvidence_eq` plus the tail (`TailData.tendstoZero` gives the tail is `o_P(n^{−λ}(log n)^{m−1})` — only at the leading scale, not at deeper `L'`! is a deeper tail bound available from `T n ≤ A e^{−nβε/2} e^{βM_n²/2}` — yes, exponentially small, so `n^{L'} T n → 0` in probability for every L'; which greybook/grammar lemma gives that most cheaply?); (c) a law for the subleading coefficient of the EVIDENCE itself after subtracting the leading term — this needs the lower coefficients' laws (all indices μ < μ₀ and log degrees at μ₀) — is there a principled index set where DeepVanishing at each level is implied by DeepVanishing at the top level c (e.g. deep sets are nested: `deepSet d b c' ⊆ deepSet d b c` for c' ≥ c, so `DeepVanishing η b c` ⇒ `DeepVanishing η b c'` for c' ≥ c; hence at every index μ the coefficients of log degree ≥ c vanish, but the degrees `c' < c` at μ ≠ μ₀ remain uncontrolled)? Please say which of (a)/(b)/(c) to formalise and give the Lean statement shapes.

4. **Lattice alignment across charts** for the joint statement: `empCoeffRect η ζ h k b μ j` at an index μ off the chart's lattice `(Qamb k)⁻¹ℕ` — is it definitionally `0` (via `empCoeff`/`scaleCoeff`) or does `CutoffExpansion` only constrain lattice indices? If not zero by definition, how to state the total coefficient at a common index: sum over charts of `if μ ∈ lattice_α then c_α else 0`?

5. **Leading-constant identification** (candidate (i) from #151, now audited: greybook's `boxGamma` with essential count `q` has prefactor `(∏ 1/(2kᵢ))/(q−1)!` and b-power `Σh + q − 2λΣk = 0` under `h_i + 1 = 2k_i λ`; `scaledBox s b = (0,b)^s` open vs grammar's `Ioc` box; `limitY` uses `yWt h' y = ∏ |y_j|^{h'_j}`, `yK k' y = ∏ y_j^{2k'_j}`, `fluctuationFunction β lam a = ∫ t^{lam−1} e^{−(β t) + β a √t}` vs grammar `fluctuation β lam a = ∫ t^{lam−1} e^{−β t + β a √t}`; grammar's face integral is over `{i // ¬ inJ (resSet h k l) i} → ℝ` with `glue (resSet) 0 w`; greybook's over `Fin s → ℝ` with `splitCoords e (0, y)`, `e : Fin (r+2) ⊕ Fin s ≃ Fin d`). The plan: (1) `fluctuation 1 l = fluctuationFunction 1 l` (integrand `ring`), (2) `residueWeight = yWt · yK^{−l}` on positive points, (3) `resSet h k l = range (e ∘ inl)` from `hess`/`hnon`, (4) change of variables through `MeasurableEquiv.piCongrLeft` along `{i // ¬ inJ J i} ≃ Fin s` (volume preserving: `MeasureTheory.volume_preserving_piCongrLeft`?), (5) `Ioc` vs `Ioo` boxes a.e. Any pitfalls (e.g. `glue`'s `piEquivPiSubtypeProd` conventions, the factor `(multCount − 1)!` vs `r!` with `multCount = r + 2`)? Is it worth doing now, or park it?

Please rank 1–5 with statement shapes and the declarations to consume; flag anything wrong above.
