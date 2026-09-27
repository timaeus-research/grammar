You are Astra, design consultant for the Lean 4 formalisation (repo timaeus-research/grammar, namespace Grammar, main f2054a0, 961 modules, zero sorry/axiom) accompanying the examples note `examples_slop.tex` of the grammar paper (Gerraty–Murfet, "Expectations and the Exceptional Divisor"). Your round-9 targets ALL landed: (1) DCXXV the family `K = x²(x^{2k−2}+y²)/2` for every `k ≥ 2` with the honest remainder `√(2π)(((k−1)/k) log N + 8)/(√N N^{1/k})` (the log-free remainder you sketched is not done); (2) DCXXVI `TwoTermData` and the two-term propagation step, hence the second coefficient at every depth `B_L = ((L+1) log 2 − (L−1)γ)/((L−2)! √(2π)^{L−1})` (numerics: L = 3 residual ratio 0.365 at N = 10⁴ vs B₃ = 0.2575, consistent with the predicted constant 0.9938/log N; L = 4 by Gauss–Hermite at N ≤ 10⁴: 0.071 vs B₄ = 0.0551); (3) DCXXVII the integral-defined `K₀` and the exact depth-two identity `Z_2(N) = e^{1/(4N)} K₀(1/(4N))/√(2πN)` for `N > 0` (mpmath `besselk` agrees to 12 digits). This is round 10.

## HEADLINES rows DCXXV–DCXXVII
| **DCXXV** | ★★★ **THE FAMILY `K = x²(x^{2k−2}+y²)/2`: THE TWO-TERM EXPANSION FOR EVERY `k ≥ 2` (u959; examples_slop §4; Astra round-9 target 1)**: `monomialFamilyZ k N = ∫_{ℝ²} e^{−N x²(x^{2k−2}+y²)/2} e^{−|w|²/2}` (unnormalised prior, as for the blow-up model), `integrable_monomialFamilyZ`; ★★ `monomialFamilyZ_eq_integral` (Gaussian in `y`); ★★ `monomialFamilyZ_eq_ampJ : Z_k(m^{2k}) = √(2π)/m^k · J_{a_m}(m^{2−2k})` with `a_m = e^{−u^{2k}/2}e^{−u²/2m²}` (`famAmp`; the scale is `ε = 1/m^{2k−2}` and the prefactor `m^{−(k−1)}` from `√(1 + m^{2k−2}u²)`); `famAmp_ampData` (`A = 1`); `ampRenorm_famAmp_sub_le` (`|R_{a_m} − (log 2 − γ)/k| ≤ 3/m²`, using `u e^{−u^{2k}/2} ≤ e^{−u/2}` for `u ≥ 1`, `k ≥ 2` via `u⁴ ≤ u^{2k}`); `monomialFamily_two_term_m`; ★★★ `monomialFamily_two_term_bound : |Z_k(N) − √(2π)/√N·[((k−1)/k) log N + 2 log 2 + (log 2 − γ)/k]| ≤ √(2π)(((k−1)/k) log N + 8)/(√N N^{1/k})` for `N ≥ 1` (`m = N^{1/(2k)}`); ★★★ `monomialFamily_two_term` (`O(N^{−1/2−1/k} log N)`). At `k = 2` this is DCXV's `√(π/2)(log N + 5 log 2 − γ)/√N`. The consult's log-free `O(N^{−1/2−1/k})` would need the sharper kernel estimate `|1/√(u²+ε) − 1/u| ≤ ε/(2u³)` with a weighted renormalised integral — not done. Lean gotchas: the scaling factor is `m^{−(k−1)}`, not `m⁻¹` (DCXV's `k = 2` hides it); `Nat.cast_sub` for `((2k−2 : ℕ) : ℝ)`; `abs_of_nonneg` needs its argument's type spelled out when the `by` blocks would otherwise see metavariables; `rw [show 2k−2 = (k−1)·2 by omega, pow_mul]` before `Real.sqrt_sq`. | MonomialFamilyExpansion.lean |
| **DCXXVI** | ★★★ **THE GAUSSIAN DLN AT EVERY DEPTH: THE SECOND COEFFICIENT `B_L = ((L+1) log 2 − (L−1)γ)/((L−2)! √(2π)^{L−1})` (u960; examples_slop §2 eq. dln_gauss, the subleading coefficient of the polynomials `P_{L−1}` at every depth; Astra round-9 target 2)**: the moments `gaussH_log_pow_inner/outer`, `integrableOn_gaussH_log_pow`, `gaussH_log_pow_moment_le` (`|∫_a^∞ h(x)(log x)^j/x| ≤ M_j = (j+1)^j/2 + 16 j!`); ★ `integral_gaussH_pow_expand` (binomial expansion against `h/x` via `add_pow`: `|∫_a^∞ h(ℓ+2log x)^{n+1}/x − ℓ^{n+1}∫_a^∞ h/x| ≤ (1+ℓ)^n K_n`); `TwoTermData f A B C m` (`0 ≤ f ≤ 1`, `|f(t) − (A(log t)^{m+2} + B(log t)^{m+1})/√t| ≤ C(1+log t)^m/√t`); `gaussR₀ = (log 2 − γ)/2`, `integral_gaussH_div_Ioi`; the pieces `twoTerm_inner_le`, `twoTerm_flat_main` (FTC), `twoTerm_h_main` (the `h`-part keeps `A ℓ^{m+2} R₀` at top order), `twoTerm_err_le`; ★★ `twoTermStep_bound` (`A' = A/((m+3)√(2π))`, `B' = (B/(m+2) + 2AR₀)/√(2π)`, explicit `C'`); `twoTermData_three` (from DCXXIII: `A = 1/(4π)`, `B = (2 log 2 − γ)/π`, `C = 12`); ★★★ `gaussLaplaceL_two_term_bound : ∀ m, ∃ C, TwoTermData Z_{m+3} (1/((m+2)!√(2π)^{m+2})) (((m+4) log 2 − (m+2)γ)/((m+1)!√(2π)^{m+2})) C m` (induction on the depth through the scalar recursion; the recursion `B_{L+1} = (B_L/(L−1) + 2A_L R₀)/√(2π)` closes with `2R₀ = log 2 − γ`); ★★★ `gaussLaplaceL_second_coeff : (√N Z_{m+3} − A(log N)^{m+2})/(log N)^{m+1} → B`. The constant term at each depth stays a derivation. Lean gotchas: `Integrable.const_mul` witnesses typed as `IntegrableOn` before `.integrable_indicator`; `mul_assoc C c P` explicitly before `mul_le_mul_of_nonneg_left`; `push_cast at hA' hB' ⊢` to align `↑(m+1)` with `↑m + 1` before rewriting the closed forms; `integral_finsetSum` (not `_finset_sum`). | GaussianDepthAllTwoTerm.lean |
| **DCXXVII** | ★★★ **THE DEPTH-TWO GAUSSIAN DLN IS A BESSEL FUNCTION: `Z_2(N) = e^{1/(4N)} K₀(1/(4N))/√(2πN)` (u961; examples_slop §2, the closed form of eq. dln_gauss at `L = 2`; Astra round-9 target 3)**: `besselK0Integral z = ∫₀^∞ e^{−z cosh t} dt` (the integral representation for `z > 0`; no Bessel API beyond this is claimed), `le_cosh_of_nonneg`, `integrableOn_besselK0Integral` (domination by `e^{−zt}`), `tendsto_sinh_atTop`; ★ `density_comp_sinh` (`g(sinh t/√N)/√(1 + N (sinh t/√N)²) · cosh t/√N = e^{−sinh² t/(2N)}/(√(2π)√N)`, via `cosh² = 1 + sinh²`); ★★★ `gaussLaplace2_eq_besselK0Integral` (`N > 0`): the substitution `y = sinh t/√N` in the conditional reduction `Z_2 = ∫ g(y)/√(1+Ny²)` (`integral_comp_mul_deriv_Ioi` with `f = sinh/√N`, `tendsto_sinh_atTop`), then `sinh² t = (cosh 2t − 1)/2` and the rescaling `u = 2t` (`integral_comp_mul_left_Ioi`); the substituted integrand is integrable by comparison with `e^{−t²/(2N)}` (`t ≤ sinh t` for `t ≥ 0`). Combined with DCXII this is the two-term expansion `e^{z}K₀(z) = log(1/z) + 3 log 2 − γ + O(z log(1/z))` as `z = 1/(4N) → 0`, read off the DLN side. Lean gotchas: `Real.sinh_lt_cosh` takes an explicit argument; `positivity` fails on `gaussDensity y / √(…)` (spell `div_nonneg (gaussDensity_nonneg y) (Real.sqrt_nonneg _)`); `div_mul_eq_mul_div` before `← Real.exp_add` when the constant factor sits outside the product. | BesselK0Bridge.lean |

## Public statements of the three new files (docstrings + signatures, proofs omitted)
### Grammar/MonomialFamilyExpansion.lean
```lean
/-- The family's partition function with the prior `e^{−|w|²/2}`. -/
noncomputable def monomialFamilyZ (k : ℕ) (N : ℝ) : ℝ

/-- The amplitude `a_m(u) = e^{−u^{2k}/2} e^{−u²/2m²}`. -/
noncomputable def famAmp (k : ℕ) (m u : ℝ) : ℝ

theorem integrable_monomialFamilyZ (k : ℕ) (N : ℝ) (hN : 0 ≤ N) :
    Integrable fun w : ℝ × ℝ => Real.exp (-N * (w.1 ^ 2 * (w.1 ^ (2 * k - 2) + w.2 ^ 2)) / 2) *
      Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 2)

/-- ★★ **The exact conditional reduction**:
`Z_k(N) = √(2π) ∫_ℝ e^{−N x^{2k}/2} e^{−x²/2}/√(1 + N x²) dx` for `N ≥ 0`, `k ≥ 1`. -/
theorem monomialFamilyZ_eq_integral {k : ℕ} (hk : 1 ≤ k) {N : ℝ} (hN : 0 ≤ N) :
    monomialFamilyZ k N = Real.sqrt (2 * Real.pi) *
      ∫ x : ℝ, Real.exp (-N * x ^ (2 * k) / 2) * Real.exp (-x ^ 2 / 2) /
        Real.sqrt (1 + N * x ^ 2)

theorem famAmp_eq (k : ℕ) (m u : ℝ) :
    famAmp k m u = Real.exp (-u ^ (2 * k) / 2 + -u ^ 2 / (2 * m ^ 2))

/-- ★★ `Z_k(m^{2k}) = √(2π)/m^k · J_{a_m}(m^{2−2k})` for `m > 0`, `k ≥ 1`
(the scale `ε = 1/m^{2k−2}`). -/
theorem monomialFamilyZ_eq_ampJ {k : ℕ} (hk : 1 ≤ k) {m : ℝ} (hm : 0 < m) :
    monomialFamilyZ k (m ^ (2 * k)) =
      Real.sqrt (2 * Real.pi) / m ^ k * ampJ (famAmp k m) (1 / m ^ (2 * k - 2))

theorem famAmp_ampData {k : ℕ} (hk : 1 ≤ k) {m : ℝ} (hm : 1 ≤ m) : AmpData (famAmp k m) 1

/-- `|R_{a_m} − R_∞| ≤ 3/m²` for `m ≥ 1`, `k ≥ 2`. -/
theorem ampRenorm_famAmp_sub_le {k : ℕ} (hk : 2 ≤ k) {m : ℝ} (hm : 1 ≤ m) :
    |ampRenorm (famAmp k m) - ampRenorm (monoAmp k)| ≤ 3 / m ^ 2

/-- The `m`-form: for `m ≥ 1`, `k ≥ 2`,
`|Z_k(m^{2k}) − √(2π)/m^k · (2(k−1) log m + 2 log 2 + (log 2 − γ)/k)| ≤
  √(2π)/m^k · ((2k−2) log m + 8)/m²`. -/
theorem monomialFamily_two_term_m {k : ℕ} (hk : 2 ≤ k) {m : ℝ} (hm : 1 ≤ m) :
    |monomialFamilyZ k (m ^ (2 * k)) - Real.sqrt (2 * Real.pi) / m ^ k *
      (2 * (k - 1) * Real.log m + 2 * Real.log 2 +
        (Real.log 2 - Real.eulerMascheroniConstant) / k)| ≤
      Real.sqrt (2 * Real.pi) / m ^ k * ((2 * k - 2) * Real.log m + 8) / m ^ 2

def
  set R

def
  set ε

def
  clear_value J R ε
  have hsq : 0 < Real.sqrt (2 * Real.pi)

/-- ★★★ **The two-term expansion of the family**: for `N ≥ 1` and `k ≥ 2`,
`|Z_k(N) − √(2π)/√N · [((k−1)/k) log N + 2 log 2 + (log 2 − γ)/k]| ≤
  √(2π)(((k−1)/k) log N + 8)/(√N · N^{1/k})`. -/
theorem monomialFamily_two_term_bound {k : ℕ} (hk : 2 ≤ k) {N : ℝ} (hN : 1 ≤ N) :
    |monomialFamilyZ k N - Real.sqrt (2 * Real.pi) / Real.sqrt N *
      ((k - 1) / k * Real.log N + 2 * Real.log 2 +
        (Real.log 2 - Real.eulerMascheroniConstant) / k)| ≤
      Real.sqrt (2 * Real.pi) * ((k - 1) / k * Real.log N + 8) /
        (Real.sqrt N * N ^ (1 / (k : ℝ)))

/-- ★★★ `Z_k(N) = √(2π)N^{−1/2}[((k−1)/k) log N + 2 log 2 + (log 2 − γ)/k] + O(N^{−1/2−1/k} log N)`
for every `k ≥ 2`. -/
theorem monomialFamily_two_term {k : ℕ} (hk : 2 ≤ k) :
    (fun N : ℝ => monomialFamilyZ k N - Real.sqrt (2 * Real.pi) / Real.sqrt N *
      ((k - 1) / k * Real.log N + 2 * Real.log 2 +
        (Real.log 2 - Real.eulerMascheroniConstant) / k))
      =O[atTop] fun N => Real.log N / (Real.sqrt N * N ^ (1 / (k : ℝ)))

```

### Grammar/GaussianDepthAllTwoTerm.lean
```lean
/-- `x |log x|^j ≤ (j+1)^j` on `(0, 1]`. -/
theorem mul_abs_log_pow_le {x : ℝ} (j : ℕ) (hx : x ∈ Ioc (0 : ℝ) 1) :
    x * |Real.log x| ^ j ≤ (j + 1) ^ j

/-- On `(0, 1]`: `|h(x)| |log x|^j / x ≤ (j+1)^j / 2`. -/
theorem gaussH_log_pow_inner {x : ℝ} (j : ℕ) (hx : x ∈ Ioc (0 : ℝ) 1) :
    |gaussH x| * |Real.log x| ^ j / x ≤ (j + 1) ^ j / 2

/-- On `(1, ∞)`: `|h(x)| |log x|^j / x ≤ j! e² e^{−x/2}`. -/
theorem gaussH_log_pow_outer {x : ℝ} (j : ℕ) (hx : 1 < x) :
    |gaussH x| * |Real.log x| ^ j / x ≤ (j.factorial : ℝ) * Real.exp 2 * Real.exp (-x / 2)

theorem measurable_gaussH_log_pow (j : ℕ) :
    Measurable fun x : ℝ => gaussH x * (Real.log x) ^ j / x

theorem integrableOn_gaussH_log_pow_Ioc (j : ℕ) {a : ℝ} (ha0 : 0 ≤ a) :
    IntegrableOn (fun x : ℝ => gaussH x * (Real.log x) ^ j / x) (Ioc a 1)

theorem integrableOn_gaussH_log_pow_Ioi_one (j : ℕ) :
    IntegrableOn (fun x : ℝ => gaussH x * (Real.log x) ^ j / x) (Ioi 1)

theorem integrableOn_gaussH_log_pow (j : ℕ) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    IntegrableOn (fun x : ℝ => gaussH x * (Real.log x) ^ j / x) (Ioi a)

/-- The moment constant `M_j = (j+1)^j/2 + 16 j!`. -/
noncomputable def gaussHMoment (j : ℕ) : ℝ

theorem gaussHMoment_nonneg (j : ℕ) : 0 ≤ gaussHMoment j

/-- `|∫_a^∞ h(x) (log x)^j/x dx| ≤ M_j` for `0 ≤ a ≤ 1`. -/
theorem gaussH_log_pow_moment_le (j : ℕ) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    |∫ x in Ioi a, gaussH x * (Real.log x) ^ j / x| ≤ gaussHMoment j

/-- `K_n = Σ_{i ≤ n} C(n+1, i) 2^{n+1−i} M_{n+1−i}`. -/
noncomputable def twoTermK (n : ℕ) : ℝ

theorem twoTermK_nonneg (n : ℕ) : 0 ≤ twoTermK n

/-- ★ **The expansion**: `|∫_a^∞ h (ℓ + 2 log x)^{n+1}/x − ℓ^{n+1} ∫_a^∞ h/x| ≤ (1+ℓ)^n K_n`
for `ℓ ≥ 0`, `0 < a ≤ 1`. -/
theorem integral_gaussH_pow_expand (n : ℕ) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) {a : ℝ} (ha0 : 0 < a)
    (ha1 : a ≤ 1) :
    |(∫ x in Ioi a, gaussH x * (ℓ + 2 * Real.log x) ^ (n + 1) / x) -
      ℓ ^ (n + 1) * ∫ x in Ioi a, gaussH x / x| ≤ (1 + ℓ) ^ n * twoTermK n

/-- The two-term hypotheses: `0 ≤ f ≤ 1` on `t ≥ 0` and
`|f(t) − (A (log t)^{m+2} + B (log t)^{m+1})/√t| ≤ C (1 + log t)^m/√t` for `t ≥ 1`. -/
structure TwoTermData (f : ℝ → ℝ) (A B C : ℝ) (m : ℕ) : Prop where
  A_nonneg : 0 ≤ A
  C_nonneg : 0 ≤ C
  f_nonneg : ∀ t, 0 ≤ t → 0 ≤ f t
  f_le_one : ∀ t, 0 ≤ t → f t ≤ 1
  bound : ∀ t, 1 ≤ t →
    |f t - (A * (Real.log t) ^ (m + 2) + B * (Real.log t) ^ (m + 1)) / Real.sqrt t| ≤
      C * (1 + Real.log t) ^ m / Real.sqrt t

/-- `R₀ = (log 2 − γ)/2`. -/
noncomputable def gaussR₀ : ℝ

/-- The inner piece for two-term data: `|∫₀^a g f(Nx²)| ≤ a/√(2π)`. -/
theorem twoTerm_inner_le (h : TwoTermData f A B C m) {N a : ℝ} (hN : 0 ≤ N) (ha : 0 ≤ a) :
    |∫ x in Ioc (0 : ℝ) a, gaussDensity x * f (N * x ^ 2)| ≤ 1 / Real.sqrt (2 * Real.pi) * a

/-- `∫_a^∞ h/x = R₀ − ∫₀^a h/x` for `0 ≤ a`. -/
theorem integral_gaussH_div_Ioi {a : ℝ} (ha0 : 0 ≤ a) :
    ∫ x in Ioi a, gaussH x / x = gaussR₀ - ∫ x in Ioc (0 : ℝ) a, gaussH x / x

/-- `h(x)(ℓ + 2 log x)^n / x` is integrable on `(a, ∞)` for `0 < a ≤ 1`. -/
theorem integrableOn_gaussH_pow (n : ℕ) (ℓ : ℝ) {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    IntegrableOn (fun x : ℝ => gaussH x * (ℓ + 2 * Real.log x) ^ n / x) (Ioi a)

/-- The flat main term on `(a, 1]`:
`∫_a^1 Q(x)/(√(2π)√N x) = (A ℓ^{m+3}/(2(m+3)) + B ℓ^{m+2}/(2(m+2)))/(√(2π)√N)`. -/
theorem twoTerm_flat_main (A B : ℝ) (m : ℕ) {N : ℝ} (hN : 1 ≤ N) :
    ∫ x in Ioc (1 / Real.sqrt N) 1, 1 / Real.sqrt (2 * Real.pi) *
      ((A * (Real.log N + 2 * Real.log x) ^ (m + 2) +
        B * (Real.log N + 2 * Real.log x) ^ (m + 1)) / (Real.sqrt N * x)) =
      1 / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
        (A * (Real.log N) ^ (m + 3) / (2 * (m + 3)) + B * (Real.log N) ^ (m + 2) / (2 * (m + 2)))

/-- The `h`-part of the main term on `(a, ∞)`: with `I_a = ∫₀^a h/x`,
`∫_a^∞ h Q/(√(2π)√N x) = (A ℓ^{m+2} R₀ + rest)/(√(2π)√N)`,
`|rest| ≤ (1+ℓ)^{m+1} (A (K_{m+1} + 1) + |B| (K_m + R₀ + 1))`. -/
theorem twoTerm_h_main (A B : ℝ) (m : ℕ) {N : ℝ} (hN : 1 ≤ N) (hA : 0 ≤ A) :
    |(∫ x in Ioi (1 / Real.sqrt N), 1 / Real.sqrt (2 * Real.pi) *
      (gaussH x * (A * (Real.log N + 2 * Real.log x) ^ (m + 2) +
        B * (Real.log N + 2 * Real.log x) ^ (m + 1)) / (Real.sqrt N * x))) -
      1 / (Real.sqrt (2 * Real.pi) * Real.sqrt N) * (A * (Real.log N) ^ (m + 2) * gaussR₀)| ≤
      1 / (Real.sqrt (2 * Real.pi) * Real.sqrt N) * ((1 + Real.log N) ^ (m + 1) *
        (A * (twoTermK (m + 1) + 1) + |B| * (twoTermK m + gaussR₀ + 1)))

def
  clear_value ℓ
  set K1

/-- The error piece on `(a, ∞)`: with `Q(x) = A(ℓ+2log x)^{m+2} + B(ℓ+2log x)^{m+1}`,
`|∫_a^∞ (g f(Nx²) − g Q/(√N x))| ≤ C (1/2 + 8·3^m m!) (1+ℓ)^{m+1}/√N`. -/
theorem twoTerm_err_le (h : TwoTermData f A B C m) {N : ℝ} (hN : 1 ≤ N) :
    |∫ x in Ioi (1 / Real.sqrt N), (gaussDensity x * f (N * x ^ 2) - gaussDensity x *
      ((A * (Real.log N + 2 * Real.log x) ^ (m + 2) +
        B * (Real.log N + 2 * Real.log x) ^ (m + 1)) / (Real.sqrt N * x)))| ≤
      C * (1 / 2 + 8 * 3 ^ m * m.factorial) * (1 + Real.log N) ^ (m + 1) / Real.sqrt N

/-- `g(x) = (1_{(0,1]}(x) + h(x))/√(2π)`. -/
theorem gaussDensity_eq_indicator_add (x : ℝ) :
    gaussDensity x = ((Ioc 0 1).indicator 1 x + gaussH x) / Real.sqrt (2 * Real.pi)

/-- ★★ **The two-term propagation step**: for two-term data `(A, B, C, m)` of `f`, the Gaussian step
`F(N) = ∫ g(x) f(N x²) dx` has the two-term data
`A' = A/((m+3)√(2π))`, `B' = (B/(m+2) + 2 A R₀)/√(2π)` with an error constant depending on
`A, B, C, m` only. -/
theorem twoTermStep_bound (h : TwoTermData f A B C m) : ∃ C' : ℝ, 0 ≤ C' ∧ ∀ N : ℝ, 1 ≤ N →
    Integrable (fun x => gaussDensity x * f (N * x ^ 2)) →
    |(∫ x, gaussDensity x * f (N * x ^ 2)) -
      (A / ((m + 3) * Real.sqrt (2 * Real.pi)) * (Real.log N) ^ (m + 3) +
        (B / (m + 2) + 2 * A * gaussR₀) / Real.sqrt (2 * Real.pi) * (Real.log N) ^ (m + 2)) /
          Real.sqrt N| ≤ C' * (1 + Real.log N) ^ (m + 1) / Real.sqrt N

def
  set E

def
  clear_value I₀ P2 E
  clear hI₀ hP2def hEdef hmid hsplit heven hgQint hgQ hQh hQind hQint1
  set ℓ

def
  clear_value ℓ
  set X

def
  set K0

def
  set R

def
  clear_value K1 K0 R
  -- the pieces against `X`
  have h0' : |I₀| ≤ 1 / 2 * X

/-- The depth-three base: two-term data of `Z_3` with `A = 1/(4π)`, `B = (2 log 2 − γ)/π`,
`C = 12`, `m = 0` (from `Grammar.GaussianDepthThreeTwoTerm`). -/
theorem twoTermData_three :
    TwoTermData (gaussLaplaceL 3) (1 / (4 * Real.pi)) ((2 * Real.log 2 -
        Real.eulerMascheroniConstant) / Real.pi)
      12 0

/-- ★★★ **The two-term expansion at every depth**: for every `m`, there is `C_m` with
`|Z_{m+3}(N) − (A (log N)^{m+2} + B (log N)^{m+1})/√N| ≤ C_m (1 + log N)^m/√N` for `N ≥ 1`,
`A = 1/((m+2)! √(2π)^{m+2})`, `B = ((m+4) log 2 − (m+2) γ)/((m+1)! √(2π)^{m+2})`. -/
theorem gaussLaplaceL_two_term_bound (m : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    TwoTermData (gaussLaplaceL (m + 3))
      (1 / ((m + 2).factorial * Real.sqrt (2 * Real.pi) ^ (m + 2)))
      (((m + 4) * Real.log 2 - (m + 2) * Real.eulerMascheroniConstant) /
        ((m + 1).factorial * Real.sqrt (2 * Real.pi) ^ (m + 2))) C m

/-- ★★★ **The second coefficient at every depth**:
`(√N Z_{m+3}(N) − A (log N)^{m+2})/(log N)^{m+1} → B = ((m+4) log 2 − (m+2)γ)/((m+1)!
√(2π)^{m+2})`. -/
theorem gaussLaplaceL_second_coeff (m : ℕ) :
    Tendsto (fun N : ℝ => (Real.sqrt N * gaussLaplaceL (m + 3) N -
      1 / ((m + 2).factorial * Real.sqrt (2 * Real.pi) ^ (m + 2)) * (Real.log N) ^ (m + 2)) /
        (Real.log N) ^ (m + 1)) atTop
      (𝓝 (((m + 4) * Real.log 2 - (m + 2) * Real.eulerMascheroniConstant) /
        ((m + 1).factorial * Real.sqrt (2 * Real.pi) ^ (m + 2))))

```

### Grammar/BesselK0Bridge.lean
```lean
/-- `K₀(z) = ∫₀^∞ e^{−z cosh t} dt` (the integral representation, `z > 0`). -/
noncomputable def besselK0Integral (z : ℝ) : ℝ

/-- `cosh t ≥ t` for `t ≥ 0`. -/
theorem le_cosh_of_nonneg {t : ℝ} (ht : 0 ≤ t) : t ≤ Real.cosh t

theorem integrableOn_besselK0Integral {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun t : ℝ => Real.exp (-z * Real.cosh t)) (Ioi 0)

/-- `sinh t → ∞`. -/
theorem tendsto_sinh_atTop : Tendsto Real.sinh atTop atTop

/-- The substituted integrand:
`g(sinh t/√N)/√(1 + sinh² t) · cosh t/√N = e^{−sinh² t/(2N)}/(√(2π)√N)`. -/
theorem density_comp_sinh {N t : ℝ} (hN : 0 < N) :
    gaussDensity (Real.sinh t / Real.sqrt N) /
      Real.sqrt (1 + N * (Real.sinh t / Real.sqrt N) ^ 2) * (Real.cosh t / Real.sqrt N) =
      Real.exp (-(Real.sinh t) ^ 2 / (2 * N)) / (Real.sqrt (2 * Real.pi) * Real.sqrt N)

/-- ★★★ **The Bessel closed form at depth two**:
`Z_2(N) = e^{1/(4N)} K₀(1/(4N))/√(2πN)`, `N > 0`. -/
theorem gaussLaplace2_eq_besselK0Integral {N : ℝ} (hN : 0 < N) :
    gaussLaplace2 N = Real.exp (1 / (4 * N)) * besselK0Integral (1 / (4 * N)) /
      Real.sqrt (2 * Real.pi * N)

```


## State of the note (pinned to grammar f2054a0)
Formal: §2 DLN flat prior at every depth; 1D polar dictionaries; Gaussian product zeta and pole; the depth-two Gaussian two-term expansion with explicit remainder and the Bessel closed form; the crossing corollary; all-depth conditional reduction, `ζ_K = 2^s ζ_L` and its leading coefficient; depth-three two-term expansion with bounded residual; the all-depth leading asymptotic AND the all-depth second coefficient. §3 cone: exact Leray closed form with Gaussian tails. §4 blow-up: tie formulas (polynomial / smooth / arbitrary smooth), Laurent data, the two-term Laplace expansion of the model, the monomial renormalised constant, the family theorem for every `k ≥ 2`. §5 rank-one: normal integral and tilt at aligned and general orbit points, the invariant tangent projection. §6 naive Bayes: pushforward density, surrogate exactness, fibre polar distributions, averaged theorem on a ball, domination adapter, envelope certificate, basepoint adapter.
Derivation-only (checked numerically): the depth-three constant term `((4 log 2 − 2γ)² + π²)/(4π)` (your round-9 §3: `J = ∫h log x/x = d²/8 + π²/48`, `∫q = (c² + 5π²/6)/(4s)`) and the constant terms for `L ≥ 4`; `H₃`, `ζ(3)`; the naive Bayes envelope `M_±(λ)` facewise integrability and the joint measurability of the fibre family, KL-vs-surrogate remainder, `m₂`; the cone averaged posterior and the exact expansion prefactors; the blow-up higher poles (`α₁ = √(π/2)/16`) and the observable expansions of §4; the Morse–Bott passage for rank-one; the smooth-amplitude tie remainder beyond `O(1)`; the log-free family remainder; an abstract Mellin transfer theorem.

## Note excerpts you asked for (verbatim LaTeX)
### §3 cone: the Leray density, the complete population expansion, and the sample (the averaged-posterior integrands)
\subsection{The Leray density and the complete population expansion}

Globally, and for a general smooth prior and observable, the whole expansion is read off one function of one variable. For $F$ smooth on $\R^4$ define the Leray density of $q$,
\[
\mathcal L_F(v)=\int_{\{q=v\}}F\,\frac{du}{dq}=\int_{\R^4}\delta(q(u)-v)\,F(u)\,du ,
\]
so that $\int_{\R^4}F\,e^{-Nq^2/2+\sqrt N\,q\,a}\,du=\int_\R e^{-Nv^2/2+\sqrt N\,v\,a}\,\mathcal L_F(v)\,dv$. In the bipolar coordinates $u_1+iu_2=re^{i\theta}$, $u_3+iu_4=se^{i\psi}$, with $p=r^2$ and $t=s^2$, $q=\tfrac12(p-t)$ and $du=\tfrac14dp\,dt\,d\theta\,d\psi$, so with $\bar F(p,t)$ the average of $F$ over the two circles,
\begin{equation}\label{eq:cone_leray}
\mathcal L_F(v)=\pi^2\int_0^\infty\!\!\int_0^\infty\delta\big(\tfrac{p-t}2-v\big)\bar F(p,t)\,dp\,dt=2\pi^2\int_{\max(0,2v)}^\infty\bar F(p,\,p-2v)\,dp .
\end{equation}

% Lean: the decomposition below is a derivation from eq:cone_leray; the smoothness of the circle averages in (p, t) is the standard fact that an even smooth function of r is smooth in r^2.
\begin{prop}[The Leray density of a signature $(2,2)$ form]\label{prop:cone_leray}
For $F$ smooth and integrable with its derivatives against the Leray form, $\mathcal L_F$ is piecewise smooth with a corner at $0$: $\mathcal L_F(v)=A_F(v)+B_F(v)|v|$ with $A_F$, $B_F$ smooth, and
\[
A_F(0)=\mathcal L_F(0)=\int_CF\,\frac{du}{dq},\qquad B_F(0)=\tfrac12\big(\mathcal L_F'(0^+)-\mathcal L_F'(0^-)\big)=-2\pi^2F(0) .
\]
In particular $\mathcal L_F$ has no logarithmic singularity at $0$, and the corner is proportional to the value of $F$ at the vertex.
\end{prop}

\begin{proof}
For $v>0$ the right side of \eqref{eq:cone_leray} is $2\pi^2\int_{2v}^\infty\bar F(p,p-2v)\,dp$ and for $v<0$ it is $2\pi^2\int_0^\infty\bar F(p,p-2v)\,dp$; $\bar F$ is smooth in $(p,t)$ on the closed quadrant because the circle average of a smooth function of $(u_1,u_2)$ is a smooth even function of $r$, hence a smooth function of $r^2$. Each one-sided expression extends smoothly across $v=0$, so $\mathcal L_F=G_+$ on $v\ge0$ and $G_-$ on $v\le0$ with $G_\pm$ smooth, $G_+(0)=G_-(0)$, and $A=\tfrac12(G_++G_-)$, $B=\tfrac12(G_+-G_-)/v$ are smooth. Differentiating, $G_+'(0)=2\pi^2\big(-2\bar F(0,0)-2\int_0^\infty\partial_2\bar F(p,p)\,dp\big)$ and $G_-'(0)=2\pi^2\big(-2\int_0^\infty\partial_2\bar F(p,p)\,dp\big)$, so the jump is $-4\pi^2\bar F(0,0)=-4\pi^2F(0)$.
\end{proof}

\begin{thm}[The complete population expansion of the cone model]\label{thm:cone_population}
For $\varphi$ and $f$ smooth with $F=f\varphi$ as above, writing $A_F(v)=\sum_ia_iv^i$ and $B_F(v)=\sum_ib_iv^i$ at $v=0$,
\begin{equation}\label{eq:cone_population}
\Zcal_N[f]\sim\sum_{j\ge0}\sqrt{2\pi}\,(2j-1)!!\,a_{2j}\,N^{-j-1/2}+\sum_{j\ge0}2^{j+1}j!\,b_{2j}\,N^{-j-1} ,
\end{equation}
an expansion on the lattice $\tfrac12\N$ with no logarithms. The exponents $j+\tfrac12$ are carried by the cone and their coefficients are the even normal moments of $F$ along it; the exponents $j+1$ are carried by the vertex, with
\[
c_{1,0}(f)=2b_0=-4\pi^2\,(f\varphi)(0) .
\]
\end{thm}

\begin{proof}
Insert $\mathcal L_F=A_F+B_F|v|$ into $\int e^{-Nv^2/2}\mathcal L_F(v)\,dv$ and use $\int_\R v^{2j}e^{-Nv^2/2}dv=\sqrt{2\pi}(2j-1)!!N^{-j-1/2}$, $\int_\R|v|^{2j+1}e^{-Nv^2/2}dv=2^{j+1}j!\,N^{-j-1}$, and the vanishing of the odd moments; the Taylor remainders of $A_F$ and $B_F$ contribute at the next order. Cutting the integral to $|v|\le\varepsilon$ costs $O(e^{-N\varepsilon^2/2})$.
\end{proof}

In the language of the paper: the Gamma-free zeta distribution pairs with $F$ as $\langle T(s),F\rangle=\int|q|^{-2s}F=\int|v|^{-2s}\mathcal L_F(v)\,dv$ (with the model's $K=q^2/2$ the Mellin variable is scaled by $2^{s}$, which we suppress), whose poles are simple, at $s=j+\tfrac12$ with residue data $a_{2j}$ from the even part of $A_F$ and at $s=j+1$ with residue data $b_{2j}$ from $B_F|v|$: $A_{1/2,1}[F]=\mathcal L_F(0)$ and $A_{1,1}[F]=b_0$. The candidate double poles at the integers and half-integers $\ge1$ are not realised because the two one-sided densities $G_\pm$ are smooth; in chart terms, the resonant $v$-derivatives at the conic are derivatives along $E$ of functions pulled back from $\R^4$, which vanish. The population leading measure is
\[
\nu^{1/2}_1=\sqrt{2\pi}\;\varphi\,\delta(q)\,du ,\qquad \int f\,d\nu^{1/2}_1=\sqrt{2\pi}\,\mathcal L_{f\varphi}(0) ,
\]
the Gelfand--Leray measure of the cone weighted by the prior: a finite measure on all of $\R^4$ giving the vertex measure zero, as in the paper's global leading-measure theorem, with the factor $\sqrt{2\pi}=\Gamma(\tfrac12)\sqrt2$ the radial constant of $e^{-Nv^2/2}$. The vertex term is a signed correction distribution at exponent $1$, $-4\pi^2\varphi(0)\,\delta_0$, not a leading measure in the sense of the paper's (positive) leading-measure theorem: the finite part of the tangential integral across the quadric $E\cap\widetilde C$.

\begin{cor}[The Gaussian prior]\label{cor:cone_gaussian}
For $\varphi=e^{-|u|^2/2}$, $\mathcal L_\varphi(v)=2\pi^2e^{-|v|}$ exactly, so
\[
\Zcal_N[1]=2\pi^2\int_\R e^{-Nv^2/2-|v|}\,dv=2\pi^2\sqrt{\tfrac{2\pi}N}\,e^{1/2N}\operatorname{erfc}\Big(\frac1{\sqrt{2N}}\Big)\sim2\pi^2\sum_{j\ge0}\frac{(-1)^j}{j!}\,m_j\,N^{-(j+1)/2},\qquad m_j=\int_\R|t|^je^{-t^2/2}dt ,
\]
that is $\Zcal_N[1]=2\pi^2\big[\sqrt{2\pi}N^{-1/2}-2N^{-1}+\tfrac{\sqrt{2\pi}}2N^{-3/2}-\tfrac23N^{-2}+\cdots\big]$. For $f=u_1^2$, $\mathcal L_{f\varphi}(v)=\pi^2e^{-|v|}(1+v+|v|)$, so $\Zcal_N[u_1^2]=\pi^2\int e^{-Nv^2/2-|v|}(1+|v|)\,dv$ has no $N^{-1}$ term, and
\[
\E_\infty[u_1^2]=\frac{\Zcal_N[u_1^2]}{\Zcal_N[1]}=\frac12+\frac1{\sqrt{2\pi}}N^{-1/2}+O(N^{-1}) .
\]
\end{cor}

The population posterior at leading order is the prior-weighted Leray measure on the cone, $\langle u_1^2\rangle_C=\tfrac12$; the vertex enters the expectation at order $N^{-1/2}$, with the universal shape
\[
\E_\infty[f]=\langle f\rangle_C+\frac{4\pi^2\varphi(0)}{\sqrt{2\pi}\,\mathcal L_\varphi(0)}\big(\langle f\rangle_C-f(0)\big)N^{-1/2}+O(N^{-1}) ,
\]
which \emph{repels} the expectation from its value at the singular point, because the vertex mass is negative. This is the first correction of the paper's leading posterior theorem for an observable that does not vanish near the deep stratum, and it is not an admissibility artefact: $f=u_1^2$ vanishes at the vertex and still sees it, through the denominator.

\subsection{The sample}

With the field the Leray reduction reads $Z_N[f;a]=\int_\R e^{-Nv^2/2+\sqrt N\,v\,a}\,\mathcal L_{f\varphi}(v)\,dv$, and the tilt $e^{\sqrt Nva}$ is odd in $v$: the odd Taylor coefficients of $A_F$ and $B_F$, invisible at zero field, are restored. With $t=\sqrt Nv$ and the tilted absolute moments $m_j(a)=\int_\R|t|^je^{-t^2/2+at}dt$, $m_j^\pm(a)=\int_\R t^{j}e^{-t^2/2+at}dt$,
\begin{equation}\label{eq:cone_frozen}
Z_N[f;a]\sim\sum_{i\ge0}a_i\,m^\pm_i(a)\,N^{-(i+1)/2}+\sum_{i\ge0}b_i\,m_{i+1}(a)\,N^{-(i+2)/2} ,
\end{equation}
every coefficient a tilted Gaussian moment of the jets of the two Leray functions at the vertex. The tilted moments are the fluctuation functions of the paper at the standardised field $\sqrt2a$: $\int_0^\infty t^ie^{-t^2/2+at}dt=2^{(i-1)/2}S_{(i+1)/2}(\sqrt2a)$, and the two half-lines carry $\pm\sqrt2a$, the two branch traces of the signed root on the two sides of the cone. The leading coefficient is $\mathcal L_{f\varphi}(0)\,[S_{1/2}(\sqrt2a)+S_{1/2}(-\sqrt2a)]/\sqrt2=\sqrt{2\pi}\,e^{a^2/2}\mathcal L_{f\varphi}(0)$: the tilted leading measure is the population one times $e^{a^2/2}$, a constant, so the leading posterior does not move with the data, as the paper's leading posterior theorem says for a field constant on the support of the leading measure. The data enter at the next order, through three terms: the vertex $b_0m_1(a)$, the odd cone term $a_1m_1^\pm(a)$, and nothing else. For the Gaussian prior and $f=u_1^2$ (where $a_1=\pi^2$, $b_0=0$ for the numerator and $a_1=0$, $b_0=-2\pi^2$ for the denominator),
\begin{equation}\label{eq:cone_posterior_field}
\E[u_1^2\mid\xi_n=a]=\frac12+\frac12\Big(a+\frac{m_1(a)}{m_0(a)}\Big)N^{-1/2}+O(N^{-1}),\qquad \frac{m_1(a)}{m_0(a)}=\frac{2e^{-a^2/2}}{\sqrt{2\pi}}+a\operatorname{erf}\Big(\frac a{\sqrt2}\Big) ,
\end{equation}
the first term of the correction being the restored odd part of the cone density and the second the vertex, each an explicit function of the single Gaussian $\xi_n$. The chart coefficients of \cref{prop:cone_chart_coeffs} are the same two mechanisms on the unit box with the flat prior in blow-up coordinates.

\paragraph{The average over the sample.} Since $\E\,e^{\sqrt N\,q\,\xi}=e^{Nq^2/2}$ for $\xi\sim N(0,1)$, the averaged evidence is exactly the prior mass, $\E_\xi Z_N[1;\xi]=\int\varphi\,du=(2\pi)^2$ for the Gaussian prior, for every $N$; but the leading coefficient $2\pi^2\sqrt{2\pi}e^{\xi^2/2}N^{-1/2}$ is not integrable against the law of $\xi$, the standardised field having variance exactly $2$. The average is carried by fields of size $|\xi|\sim\sqrt N$: truncating to $|\xi|<A$ gives $\E_\xi[Z_N[1;\xi]\mathbf 1_{|\xi|<A}]=2\pi^2\int_\R e^{-|v|}\big[\Phi(A-\sqrt Nv)-\Phi(-A-\sqrt Nv)\big]dv\to0$ as $N\to\infty$ for every fixed $A$. The posterior ratios are a different matter: \eqref{eq:cone_posterior_field} grows with $|\xi|$, so averaging its fixed-field expansion over $\xi$ needs a domination argument that we do not give; formally the averaged first correction is $\tfrac12\E[m_1(\xi)/m_0(\xi)]N^{-1/2}$, which, if the interchange is justified, evaluates to $N^{-1/2}/\sqrt\pi$.


### §6 naive Bayes: the pushforward density and the complete population expansion (the envelope quantities)
\subsection{The pushforward of the prior along the moment map}

For fixed $t$ the leaf map $(a_i,b_i)\mapsto(\lambda_i,\eta_i)=((1-t)a_i+tb_i,\,b_i-a_i)$ is a shear of determinant $(1-t)+t=1$, so the map $\theta\mapsto(t,\lambda_1,\eta_1,\lambda_2,\eta_2)$ preserves Lebesgue measure and carries the uniform prior on the cube to Lebesgue measure on the region $\{0\le\lambda_i-t\eta_i\le1,\ 0\le\lambda_i+(1-t)\eta_i\le1\}$; for fixed $(t,\lambda)$ this is the rectangle $\eta\in[-\alpha_1,\beta_1]\times[-\alpha_2,\beta_2]$ with $\alpha_i=\min(\lambda_i/(1-t),(1-\lambda_i)/t)$ and $\beta_i=\min((1-\lambda_i)/(1-t),\lambda_i/t)$, which contains $0$ in its interior. The density of $\eta_1\eta_2$ under Lebesgue measure on the rectangle is elementary, $\log^+(\beta_1\beta_2/z)+\log^+(\alpha_1\alpha_2/z)$ at $z>0$ (one logarithm per sign quadrant) and $\log^+(\beta_1\alpha_2/|z|)+\log^+(\alpha_1\beta_2/|z|)$ at $z<0$, so the pushforward density of the prior under $y=(\lambda_1,\lambda_2,\mu)$ is the one-dimensional integral
\begin{equation}\label{eq:nb_rho_integral}
\rho(\lambda,\mu)=\int_0^1\frac{dt}{t(1-t)}\,h_t\Big(\frac{\mu}{t(1-t)}\Big),
\end{equation}
and this integral is exactly computable. In the variable $r=t/(1-t)$, $dt/(t(1-t))=dr/r$, and for the quadrant $\eta_1,\eta_2>0$ the product $t(1-t)\beta_1\beta_2=\min((1-\lambda_1)r,\lambda_1)\min((1-\lambda_2)r,\lambda_2)/r$ is $Ar$ for $r\le r_{\rm lo}$, the constant $M$ for $r_{\rm lo}\le r\le r_{\rm hi}$, and $D/r$ for $r\ge r_{\rm hi}$, with $A=(1-\lambda_1)(1-\lambda_2)$, $D=\lambda_1\lambda_2$, $r_{\rm lo},r_{\rm hi}$ the ordered pair $\lambda_i/(1-\lambda_i)$, and $M=\min(\lambda_1(1-\lambda_2),\lambda_2(1-\lambda_1))$; the three pieces integrate against $dr/r$ to $\tfrac12\log^2(M/\mu)+\log(r_{\rm hi}/r_{\rm lo})\log(M/\mu)+\tfrac12\log^2(M/\mu)$ for $0<\mu<M$, and $M^2r_{\rm hi}/r_{\rm lo}=AD=V$. The other quadrant with $\mu>0$ gives the same, and the two mixed quadrants give the same expression with $M_-=\min(\lambda_1\lambda_2,(1-\lambda_1)(1-\lambda_2))$ in place of $M_+=M$:
\begin{prop}[the exact pushforward density; formal, \texttt{nbFibreDensity\_closed\_pos/neg}]\label{prop:nb_rho}
For $0<|\mu|<M_\pm$ (the Fr\'echet bounds, $\pm=\operatorname{sgn}\mu$) and $\lambda\in(0,1)^2$,
\begin{equation}\label{eq:nb_rho}
\rho(\lambda,\mu)=2\log\frac{M_\pm}{|\mu|}\,\log\frac{V}{M_\pm|\mu|}
=2\log^2\frac{\sqrt V}{|\mu|}-\frac{u_1^2+u_2^2}2+u_1u_2\operatorname{sgn}\mu ,
\end{equation}
with $V=\lambda_1\lambda_2(1-\lambda_1)(1-\lambda_2)$ and $u_i=\log(\lambda_i/(1-\lambda_i))$ evaluated at $\lambda$; $\rho=0$ outside these intervals.
\end{prop}
The density is \emph{exactly} a quadratic polynomial in $\log|\mu|$ on each side of $\mu=0$, with no power corrections; it vanishes continuously at the Fr\'echet bounds; its $\log^2$ coefficient is the universal $2$ and its $\log$ coefficient $2\log V$ is the same on both sides, while the constant term jumps by $2u_1u_2$ across $\mu=0$. Its $\lambda$-marginal is $2M_+(2+\log(V/M_+^2))+2M_-(2+\log(V/M_-^2))$, the area of the $(t,\eta)$-region, which integrates to $1$ over the unit square.

This is the whole example in one formula. The multiplicity $m=3$ is the $\log^2|\mu|$ singularity of the fibre volume; the two deepest points $P_0,P_1$ are where the fibre volume near $\mu=0$ accumulates (the ends $t\to0,1$ of the $r$-integral, each contributing $\tfrac12\log^2$ per sign quadrant); the leading measure of the paper, pushed down to parameter space, is
\[
\nu_{\rm lead}=\frac{c_3}2\,(\delta_{P_0}+\delta_{P_1}),\qquad \Zcal_N[f]\sim N^{-3/2}\log^2N\int f\,d\nu_{\rm lead}=\frac{c_3}2\,(f(P_0)+f(P_1))\,N^{-3/2}\log^2N
\]
for continuous $f$, with $c_3$ the constant of \eqref{eq:nb_Z} below, and the label symmetry forces the two weights to agree (the formal chain of \cref{sec:nb} controls insertions that factor through the moments; the concentration at $P_0,P_1$ for general parameter observables is a derivation). In the language of the paper, $T_f(s)=\int K^{-s}f\,d\theta=\int G^{-s}\rho_f\,dy$ with $\rho_f$ the pushforward of $f\,d\theta$, and $\Gamma(s)T_f(s)=\int_0^\infty N^{s-1}\Zcal_N[f]\,dN$ has its leading pole $2c_3[f]/(\tfrac32-s)^3$, so that $T_f(s)\sim2c_3[f]/(\Gamma(\tfrac32)(\tfrac32-s)^3)$: the polar distribution of order three at $\tfrac32$ is the Mellin image of the $\log^2$ term.

\subsection{The complete population expansion}

With $\rho$ exact, $\Zcal_N[1]=\int e^{-NG(y)}\rho(y)\,dy$ is a three-dimensional Laplace integral with a logarithmic amplitude. In the standardised coordinates $\lambda_i=\lambda_i^*+\sqrt{v_i/N}\,x_i$, $\mu=\sqrt{V/N}\,z$ the $\log V$ terms cancel at leading order (at higher orders the density carries $V(\lambda)$ while the scaling uses $V(\lambda^*)$, leaving $\tfrac12\log(V(\lambda)/V(\lambda^*))$), $2\log^2(\sqrt V/|\mu|)=2(\tfrac12L-\log|z|)^2$ with $L=\log N$, and the Gaussian logarithmic moments $\int e^{-z^2/2}\log|z|\,dz=-\sqrt{2\pi}\,g/2$, $\int e^{-z^2/2}\log^2|z|\,dz=\sqrt{2\pi}(g^2/4+\pi^2/8)$ with $g=\gamma+\log2$ give
\begin{equation}\label{eq:nb_Z}
\Zcal_N[1]=(2\pi)^{3/2}V\,N^{-3/2}\Big[\frac{L^2}2+gL+\frac{g^2}2+\frac{\pi^2}4-\frac{u_1^2+u_2^2}2\Big]+d\,N^{-2}+O(N^{-5/2}\log^2N),
\end{equation}
so $c_3=\pi\sqrt{2\pi}\,V$, $c_2=(2\pi)^{3/2}Vg$, $c_1=(2\pi)^{3/2}V(g^2/2+\pi^2/4-(u_1^2+u_2^2)/2)$. The three coefficients at the leading exponent are the paper's polar data of orders $3,2,1$ at $s=\tfrac32$: the top one universal, the middle one the Gamma-derivative shift $g$, the bottom one carrying the geometry of the truth through $u_1^2+u_2^2$, the constant term of the fibre volume.

The first correction is not what a generic example would suggest. Since $\rho$ has no $|\mu|^k$ terms, there is no $N^{-2}\log^jN$ with $j>0$; and the even part of $\rho$ against the odd cubic phase integrates to zero. What survives at $N^{-2}$ is the \emph{sign jump} $u_1u_2\operatorname{sgn}\mu$ paired with the cubic term of the phase: in standardised coordinates $G_3=-\tfrac13(\kappa_1x_1^3+\kappa_2x_2^3+\kappa_1\kappa_2z^3)-x_1x_2z-\kappa_1x_1z^2-\kappa_2x_2z^2$ with $\kappa_i=(1-2\lambda_i^*)/\sqrt{v_i}$, only $z^3$ survives the $x$-integrations, and $\int e^{-z^2/2}|z|^3dz=4$ gives
\begin{equation}\label{eq:nb_d}
d=\frac{8\pi}3\sqrt V\,(1-2\lambda_1^*)(1-2\lambda_2^*)\,u_1u_2 ,
\end{equation}
which vanishes when either mean is $\tfrac12$. The structure to all orders, for $f=1$, is $\sum_kN^{-3/2-k}P_k(\log N)+\sum_kN^{-2-k}d_k$ with $\deg P_k\le2$: the logarithmic amplitude feeds the first series, the jump the second. This is a case where the paper's finite parts at the \emph{same} exponent, the $\log N$ and constant coefficients at $\tfrac32$, are the informative corrections, and the next power is a parity effect.

\subsection{The sample}

The empirical loss is exact in the empirical table $\hat p$: $K_N(\theta)=D(\hat p\|p_\theta)-D(\hat p\|p^*)$, so
\[
Z_N[f;\text{sample}]=e^{ND(\hat p\|p^*)}\int e^{-ND(\hat p\|p_y)}\rho_f(y)\,dy ,
\]
a Laplace integral about the empirical moments $\hat y=y(\hat p)=y^*+\xi/\sqrt N$, where $\xi=\sqrt N(\hat y-y^*)$ is asymptotically $N(0,I^{-1})$ in the moment coordinates. The prefactor is the paper's tilt, $e^{ND(\hat p\|p^*)}=e^{\xi^{\mathsf T}I\xi/2}(1+O(N^{-1/2}))$, with the projector the identity on the three-dimensional observable tangent space because the model saturates. Behind the tilt, the $\lambda$-directions are regular and the $\mu$-Gaussian is centred at $\hat\mu=\xi_\mu/\sqrt N$, i.e.\ at $z=a:=\xi_\mu/\sqrt V$ in the standardised coordinate: the field enters through the shifted logarithmic moments
\[
m_j(a)=\int e^{-(z-a)^2/2}\log^j|z|\,dz,\qquad q(a)=\int e^{-(z-a)^2/2}\operatorname{sgn}z\,dz=\sqrt{2\pi}\,(2\Phi(a)-1),
\]
the fluctuation functions of this example, and
\begin{equation}\label{eq:nb_frozen}
e^{-ND(\hat p\|p^*)}\,N^{3/2}Z_N[1;\text{sample}]=2\pi V\Big[\sqrt{2\pi}\Big(\frac{L^2}2-\frac{u_1^2+u_2^2}2\Big)-2L\,m_1(a)+2m_2(a)+u_1u_2\,q(a)\Big]+o(1)
\end{equation}
The $\log^2N$ coefficient is field-independent once the tilt is divided out ($m_0(a)=\sqrt{2\pi}$ for every shift), the $\log N$ coefficient sees the field through $m_1(a)$, and the constant through $m_2(a)$ and, via the jump, through $q(a)$. For the posterior mean of the covariance parameter,
\begin{equation}\label{eq:nb_postmu}
\E[\mu\mid\text{sample}]=\hat\mu-\frac{4\sqrt V}{\sqrt N\log N}\,\frac{m_1'(a)}{\sqrt{2\pi}}+O\Big(\frac1{\sqrt N\log^2N}\Big),
\end{equation}
the posterior tracks the empirical covariance with a relative correction of order $1/\log N$, while at the population truth ($a=0$) the logarithmic terms are even and only the jump contributes, $\E_N[\mu]\sim4\sqrt V\,u_1u_2/(\sqrt{2\pi}\sqrt N\log^2N)$, a partially vanishing observable with a $1/\log^2N$ rate on top of $N^{-1/2}$. This last limit is approached slowly: the cubic term of the phase against the even part of the amplitude contributes to $\E_N[\mu]$ at relative order $(1-2\lambda_1^*)(1-2\lambda_2^*)\log^2N/\sqrt N$, which exceeds the jump term below $N\approx10^5$, and including it together with the full $\log N$ and constant terms of the denominator gives the posterior covariance to four digits (\cref{sec:nb_numerics}).

Finally an exact statement at every $N$ and for every sample: the label involution $\sigma$ fixes the cell probabilities \eqref{eq:nb_cells} and preserves the prior, so every label-antisymmetric observable has posterior mean zero, and in particular
\[
\E[t\mid\text{sample}]=\tfrac12 ,
\]
the posterior weight of $P_0$ and $P_1$ is equal, the leading measure is not moved by the data (the three regimes of the paper: $t-\tfrac12$ has exactly zero posterior mean by symmetry, $\mu$ is fully vanishing, and $t(1-t)$ is partially vanishing, vanishing at $P_0$ and $P_1$ but not on the whole fibre).



## Library facts
Everything of rounds 1–9: the general-amplitude engine `ampJ_two_term`, the monomial constants, `gaussLaplace2_bounds`, `LeadingData`/`gaussianStep_bound`, `TwoTermData`/`twoTermStep_bound`, the moments `gaussH_log_pow_moment_le` (bounds only, no exact values beyond `R₀`), the scalar recursion at every depth, Bochner peels in both orders, `integral_comp_mul_deriv_Ioi`, `integral_comp_rpow_Ioi_of_pos`, `volume_preserving_finTwoArrow`, the Mellin engine (`hasDerivAt_mellinIoc`, `logMellinFull_eq`, `logSqMellinFull`), `Convex.norm_image_sub_le_of_norm_deriv_le`, matrix trace identities, Gamma values at ½ and 1, `Γ''(½)` (DCVIII). Mathlib pin v4.33.1 (no Bessel functions, no polygamma; `Real.eulerMascheroniConstant` with `Γ'(1) = −γ` available through DCXI).

## Questions
1. Fidelity check (brief) of DCXXV–DCXXVII against the note's claims and your round-9 specifications; in particular (a) DCXXVI's `B` recursion `B' = (B/(m+2) + 2AR₀)/s` and the closed form `B_L` (does it match the subleading coefficient of the note's `P_{L−1}`, i.e. the jet of `Γ(½−ε)Γ(1+ε)^L` — please state the predicted `B_L/A_L` and compare with `(L−1)((L+1) log 2 − (L−1)γ)`); (b) DCXXV's remainder shape and whether the `k = 1` exclusion is right; (c) DCXXVII's `besselK0Integral` as a definition (should we also export the `e^z K₀(z) = log(1/z) + 3 log 2 − γ + O(z log(1/z))` corollary read off DCXII, and is the `1/(4N)` argument the standard normalisation).
2. Rank the next three day-sized formal targets by value-per-effort (concrete Lean statements + routes). Candidates: (a) the depth-three constant, in the honest intermediate form you described (integrability of `q(v) = Z_2(v²) − 1_{(1,∞)}(v)(2 log v + c)/s`, and the residual limit `√N·(Z_3 − two-term) → (cR₀ + 2J)/π + (2/s)∫q` with `J` and `∫q` left as constants) — give the precise route from `gaussLaplace2_bounds` and the DCXXIII pieces; (b) the exact `J = ∫₀^∞ h(x) log x/x dx = d²/8 + π²/48` (what is the cleanest Lean route with `Γ''(½)`/`Γ''(1)` data — do we need `Γ''(1) = γ² + π²/6`, and is that derivable on our pin from the reflection formula as in DCVIII); (c) the naive Bayes envelope on one face, now that the density is supplied above: state the face patch, the envelope `E(λ) ≤ C λ₁^{−a}(1+|log λ₁|)^b`, and which of `M_±, ℓ_λ, c_λ, b_λ, L_λ, φ_λ(0)` are needed; (d) the cone averaged posterior, now that the integrand is supplied: is it an average of ratios or a ratio of averages in the note, and what is the honest day-sized domination statement; (e) the blow-up observable numerators (`x²` and `y²`, unnormalised) as leading-numerator theorems with the amplitude engine; (f) the constant terms for `L ≥ 4` by a `ThreeTermData` propagation (what new moment is needed at each step — is it only `J` and `R₀`, or does `∫ h log² x/x` enter); (g) the log-free family remainder. Say which are honest day-sized targets and give the Lean-facing interface for the top three.
3. Convention hazards in the three new files (`famAmp` and the raw Gaussian mass; `TwoTermData`'s `m` = leading degree `m+2`; `besselK0Integral` only for `z > 0`; the `8` in the family remainder).
Answer concisely with Lean-facing detail.
