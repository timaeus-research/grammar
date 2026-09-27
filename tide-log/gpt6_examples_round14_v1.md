## 1. Fidelity: mathematically consistent

**DCXL–DCXLV match the supplied round-13 specifications.** This is a check of the supplied statements and mathematics, not an independent repository/build audit.

- **Reflection and sign.** At fixed \(a\), the quotient derivative is
  \[
  G(a)=-\operatorname{Cov}_a(T_+,|T|).
  \]
  Reflection sends \(T_+\) to \((-T)_+\), so
  \[
  G(a)+G(-a)=-\operatorname{Var}_a(|T|)
  =-(a^2+1-m(a)^2).
  \]
  Averaging against even \(\gamma\) gives precisely the **negative** half in `coneSecondCoeff_eq_symmetric`.

- **Absolute mean and IBP.** With \(b=2\int_0^a\gamma\), \(b'=2\gamma\) and \(b(\pm\infty)=\pm1\), the normalization \(m=ab+2\gamma\) is correct. The identities follow respectively from
  \[
  (b^3)'=6b^2\gamma,\qquad
  (\gamma^2)'=-2a\gamma^2,\qquad
  (a\gamma)'=(1-a^2)\gamma.
  \]
  Also
  \[
  \int\gamma^3=(2\pi)^{-3/2}\sqrt{2\pi/3}
  =\frac1{2\pi\sqrt3}.
  \]
  Thus \(\int m^2\gamma=1/3+12\int\gamma^3=1/3+2\sqrt3/\pi\), giving the stated \(c_2\).

- **Bridge.** The tail subtraction is \((2\log v+c)/(sv)\), with \(s=\sqrt{2\pi}\). Its Mellin transform is
  \[
  \frac2{s(1-z)^2}+\frac c{s(1-z)}.
  \]
  The limit must be \(z\to1^-\); the supplied filter is correct.

- **Jet normalization and assembly.** Here \(F(u)=B(2u)\), hence
  \[
  F''(0)=4B''(0)=c^2+5\pi^2/6.
  \]
  Directly,
  \[
  M(1-2u)=\frac{F(u)}{2su^2},\qquad
  \operatorname{poles}(1-2u)=\frac{1+cu}{2su^2}.
  \]
  This verifies `depthThreeMellin_sub_poles_eq` and \(Q=F''(0)/(4s)\).

- **Mellin powers of two.** Multiplying
  \[
  A(z)=\frac{\Gamma(z/2)\Gamma((1-z)/2)}{2\sqrt\pi}
  \]
  by the negative Gaussian moment
  \[
  \frac{2^{-z/2}\Gamma((1-z)/2)}{\sqrt\pi}
  \]
  gives exactly \(2^{-1-z/2}/\pi\). No missing factor of two.

- **Independent \(C_3\) calculation.** Since \(s^2=2\pi\),
  \[
  \begin{aligned}
  C_3
  &=\frac{cR_0+R_0^2+\pi^2/24}{\pi}
    +\frac{c^2+5\pi^2/6}{4\pi}\\
  &=\frac{(c+2R_0)^2+\pi^2}{4\pi}.
  \end{aligned}
  \]
  Finally \(2R_0=\log2-\gamma\), so \(c+2R_0=4\log2-2\gamma\). **The assembly is correct.**

## 2. Next three targets, ranked

### 1. Closed form of `thirdCoeff`: highest priority, genuinely day-sized

This is algebraic closure of an existing analytic theorem, not another asymptotics project.

Put
\[
T_L=(L-3)!\,s^{L-1}C_L,\qquad
D_L=(L+1)\log2-(L-1)\gamma.
\]
The recurrence becomes
\[
\boxed{T_{L+1}-T_L=2D_LR_0+4J.}
\]
Since \(D_{L+1}=D_L+2R_0\) and \(4J=2R_0^2+\pi^2/12\),
\[
\frac{D_{L+1}^2+(L+4)\pi^2/6}{2}
-\frac{D_L^2+(L+3)\pi^2/6}{2}
=2D_LR_0+4J.
\]
The formula also holds at \(L=3\), directly from exact \(C_3\).

Proposed public statement, using the supplied indexing:
```lean
theorem thirdCoeff_eq_closed (m : ℕ) :
    thirdCoeff m =
      ((((m + 5 : ℕ) : ℝ) * Real.log 2 -
          ((m + 3 : ℕ) : ℝ) * Real.eulerMascheroniConstant) ^ 2 +
        ((m + 7 : ℕ) : ℝ) * Real.pi ^ 2 / 6) /
      (2 * (Nat.factorial (m + 1) : ℝ) *
        Real.sqrt (2 * Real.pi) ^ (m + 3))
```

**Route:** establish the scaled step first; prove the base from the special \(C_4\) recurrence; then `induction m`. Isolate cast/factorial identities using `Nat.factorial_succ`, `Nat.cast_mul`, and `pow_succ`; discharge nonzero denominators before `field_simp; ring`.

The mathematical step is routine. The only likely friction is matching the actual indexing of the existing `A`, `B`, and recurrence API.

### 2. Abstract forward Mellin finite-part lemma: day-sized if scoped narrowly

Generalize DCXLII’s mechanism—not an inverse Mellin theorem, and not yet a complex meromorphic-continuation theorem.

A useful independent core is:

```lean
theorem tendsto_mellin_residual
    {q : ℝ → ℝ} {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1)
    (hsmall :
      IntegrableOn (fun v => v ^ (a - 1) * q v) (Ioc 0 1))
    (hlarge : IntegrableOn q (Ioi 1)) :
    Tendsto
      (fun z => ∫ v in Ioi (0 : ℝ), v ^ (z - 1) * q v)
      (𝓝[<] (1 : ℝ))
      (𝓝 (∫ v in Ioi (0 : ℝ), q v))
```

**Route:** eventually \(a<z<1\); on \((0,1]\), dominate by \(v^{a-1}|q(v)|\); on \((1,\infty)\), dominate by \(|q(v)|\). Prove residual integrability once, then dominated convergence.

For
\[
Z(v)=q(v)+1_{v>1}\frac{P(\log v)}v,
\]
the resulting polar part is
\[
\sum_{k=0}^d\frac{p_k\,k!}{(1-z)^{k+1}}.
\]
Add the monomial transform
```lean
∫ v in Ioi (1 : ℝ), v ^ (z - 2) * Real.log v ^ k
  = (Nat.factorial k : ℝ) / (1 - z) ^ (k + 1)
```
for \(z<1\), by repeated IBP.

**Scope discipline:** the residual core plus affine \(P\) is comfortably day-sized using existing lemmas. Arbitrary polynomial degree is a sensible extension, not a prerequisite for landing the reusable core.

### 3. Generic power/log face certificate: day-sized analytic building block

This has good reuse value for NB, provided its deliverable is **integrability of a certified envelope**, not certification of the whole fibre construction.

Start with:
```lean
theorem integrableOn_rpow_mul_logWeight
    {a : ℝ} (ha : -1 < a) (k : ℕ) :
    IntegrableOn
      (fun x : ℝ => x ^ a * (1 + |Real.log x|) ^ k)
      (Ioo 0 1)
```

Then finite products:
```lean
theorem integrable_faceWeight
    {d : ℕ} (a : Fin d → ℝ) (k : Fin d → ℕ)
    (ha : ∀ i, -1 < a i) :
    Integrable
      (fun x : Fin d → ℝ =>
        ∏ i, (x i) ^ (a i) * (1 + |Real.log (x i)|) ^ (k i))
      (Measure.pi
        (fun _ : Fin d => volume.restrict (Ioo (0 : ℝ) 1)))
```

**Route:** absorb logarithms into a small negative power, retaining exponent \(>-1\); then use finite-product integrability. A domination adapter takes an a.e.-strongly-measurable \(f\) and a bound \(\|f\|\le C\,W\).

**Not included:** proving that the actual NB envelope has these exponents, handling chart Jacobians, or establishing joint measurability of the fibre family.

### Assessment of the other candidates

| Candidate | Honest scope |
|---|---|
| **Depth-four constant** | A plausible next analytic project, but not automatically day-sized. First prove the `log²` kernel moment/integrability and a cubic-log convolution estimate. An integral-defined `depthFourConst` with a quantitative remainder is a coherent target; its rate must be derived, not borrowed unchanged from depth three. |
| **All higher-depth constants** | Not a single fourth-order propagation task: a fourth term is the constant only at depth four. Constants at increasing depth require increasing jet order. |
| **\(\Gamma'''(1)\), \(\zeta(3)\)** | Do not budget this as a lookup. I cannot verify the pinned Mathlib API here; absent an identified theorem, treat the derivative evaluation as a separate substantial task. |
| **Blow-up \(\alpha_1\)** | Potentially day-sized **if** DCXV already supplies the weighted integrability needed for a second-order remainder. Otherwise the uniform remainder is the real project. Distinguish the pole coefficient from the Laplace coefficient and record the Gamma conversion explicitly. |
| **Cone \(c_3\)** | Plausible but less predictable: Gaussian domination of the quotient remainder, uniformly in \(a\), is the hard part—not the scalar exponential inequality. |

For the cone, fix a normalization hazard before starting: if \(H(\delta,a)=\texttt{coneScaledCorrection}\), and the posterior contribution is \(\delta H(\delta,a)\), then
\[
c_3=\frac12\int \partial_\delta^2H(0,a)\,\gamma(a)\,da.
\]
Thus `G₂` must denote the **second Taylor coefficient**, not the unhalved second derivative.

## 3. Convention and presentation hazards

1. **Keep `u` explicit:** \(u=(1-z)/2=\varepsilon/2\). Reserve \(B(\varepsilon)=F(\varepsilon/2)\); its second derivative is one quarter of \(F''(0)\).

2. **Unify the subtraction constant:** add a rewriting lemma expressing `depthThreeQ` using `depthThreeC`. No need to alter the definition and disturb downstream proofs.

3. **Document `coneB` as \(2\Phi-1\):** it is not \(\Phi\), nor \(\int_0^a\gamma\). The factor two drives both the absolute-mean formula and every IBP constant.

4. **`mellinHalfBeta` is harmless:** explain that it is the half-line integral \(A(z)\), evaluated through Gamma representation and Tonelli. Its name should not suggest a dependency on a Beta API.

5. **Retain the integral definition of `depthThreeMellin`.** In the note, state
   \[
   M(z):=\int_0^\infty v^{z-1}Z_2(v^2)\,dv
   =\frac{2^{-1-z/2}}{\pi}\Gamma(z/2)\Gamma((1-z)/2)^2,
   \quad 0<z<1.
   \]
   The closed form is a theorem on the convergence strip, not a replacement definition outside it.

6. Minor bookkeeping: there are **six headline rows but seven listed files**, because DCXLI contains two modules.