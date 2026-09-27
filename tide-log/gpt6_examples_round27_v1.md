## 1. Fidelity

**(a) Signs are correct.** For
\[
H_{D+1}(z)=2^{Dz}\Gamma(\tfrac12-z)\Gamma(1+z)^{D+1}/\sqrt\pi,
\]
the logarithmic derivative is
\[
D\log2-\psi(\tfrac12-z)+(D+1)\psi(1+z).
\]
The minus comes from differentiating `½ - z`. Separately,
\[
[z^j]\psi(\tfrac12-z)=(-1)^j\psi^\frac12_j.
\]
Thus the contribution to \(q_{D,j}\) is **\(-(-1)^j\psi^\frac12_j\)**.

**(b) Correct.** Substituting
\[
\psi^\frac12_j=(2^{j+1}-1)\psi_j-2\log2\,[j=0]
\]
gives exactly `depthLogDerivCoeff_eq_one`, including the exceptional \((D+1)\log2\) term.

**(c) All displayed depth-five instances agree with the recurrence**, including \(2\pi^4/9\), \(5\lambda_4/6\), and \(-13\lambda_5/60\).

Defining `gammaLogFourthOne := (6 * psiOneCoeff 3).re` is entirely honest. Your real-valued conclusions need only real-part extraction, not reality of the complex coefficient. However:

- “the real part of the fourth logarithmic Gamma derivative” is justified immediately;
- identifying the **complex** derivative with its real cast needs a reality theorem.

Adding
```lean
theorem psiOneCoeff_im (j : ℕ) : (psiOneCoeff j).im = 0
```
from the one-point recurrence and real Gamma jets is worthwhile bookkeeping, not a prerequisite for the current results.

## 2. The ζ-bridge

### First, a sign correction

The first new case is
\[
\boxed{\psi_2=-\zeta(3)},\qquad \lambda_3=2\psi_2=-2\zeta(3).
\]
Your question’s `ψ₂ = ζ(3)` is a typo. These are **Taylor coefficients**, not unnormalised derivatives:
\[
\psi^{(j)}(1)=j!\psi_j=(-1)^{j+1}j!\zeta(j+1).
\]

### Recommendation: a subtracted Beta integral

I would not start with large-argument polygamma decay or the unsubtracted Gauss integral. Target the locally sufficient identity
\[
\boxed{\psi(1+z)+\gamma
=\int_0^1\frac{1-t^z}{1-t}\,dt},
\qquad |z|<\tfrac12.
\]

This is a smaller analytic task than a global Gauss representation and avoids both Stirling and locally uniform convergence of `GammaSeq`.

**Derivation:** for real \(b>0\), subtract the two Beta integrals:
\[
B(1+z,b)-B(1,b)
=\int_0^1(t^z-1)(1-t)^{b-1}\,dt.
\]
Using \(B(1,b)=1/b\), the Gamma side becomes
\[
\frac{\Gamma(1+z)\Gamma(1+b)/\Gamma(1+z+b)-1}{b}.
\]
As \(b\downarrow0\), its limit is \(-\gamma-\psi(1+z)\).

For the integral limit, on \(|z|\le r<1\), use
\[
|t^z-1|\le |z|\,|\log t|\,t^{-r}.
\]
Consequently the common envelope
\[
t^{-r}\frac{|\log t|}{1-t}
\]
is integrable. Subtraction is essential: the two unsubtracted limiting integrals diverge.

**Proposed first analytic interface**—schematic, not a claim about existing API:
```lean
theorem gammaLogDeriv_one_add_eq_integral
    {z : ℂ} (hz : ‖z‖ < (1 / 2 : ℝ)) :
    gammaLogDeriv (1 + z) =
      -(Real.eulerMascheroniConstant : ℂ) +
        ∫ t in (0 : ℝ)..1,
          (1 - (t : ℂ) ^ z) / (1 - (t : ℂ))
```
Endpoint values do not matter.

Then extract jets under the integral:
\[
\psi_j=-\frac1{j!}\int_0^1\frac{\log^j t}{1-t}\,dt
\quad(j\ge1).
\]
For the evaluation, work first with the nonnegative real integrand
\((-\log t)^j/(1-t)\), expand the geometric series, and use
\[
\int_0^1t^n(-\log t)^j\,dt=\frac{j!}{(n+1)^{j+1}}.
\]
The substitution \(t=e^{-u}\) reduces this last integral to an ordinary Gamma integral.

### Exact first acceptance target

```lean
theorem psiOneCoeff_two_eq_neg_zeta_three :
    psiOneCoeff 2 = -riemannZeta (3 : ℂ)
```

Internally, first prove
```lean
HasSum (fun n : ℕ => ((n + 1 : ℂ) ^ 3)⁻¹) (-psiOneCoeff 2)
```
so the special-functions proof is separated from the zeta API.

**Scout one additional item:** the ordinary Dirichlet-series characterization of `riemannZeta` on `1 < re s`. The reported even-zeta lemmas are not themselves the general bridge.

**Honest size:** several focused days, not a reliable one-day task; roughly three modules: subtracted Beta limit, integral jets, zeta identification. Exact cost depends on Beta and parameter-integral APIs. Once the integral representation is established, proving all \(j\ge1\) is preferable to stopping at \(j=2\).

- **A:** valid, but the decay lemma is the substantive missing theorem.
- **B:** use the subtracted local version above.
- **C:** no independent shortcut; the proposed log-Gamma expansion is precisely the missing result.
- **D:** evaluates even zeta values but does not identify Gamma jets.

## 3. Alternatives

### (v) Cone third coefficient — best day-sized mathematical target

Put
\[
A=\sqrt{\pi/2},\qquad F(x)=e^{x^2/2}T(x).
\]
For the Gaussian tail normalization in the displayed formula,
\[
F'(x)=xF(x)-1,\qquad F(0)=A.
\]
Hence
\[
F(x)=A-x+\frac A2x^2+O(x^3).
\]

Thus **\(A/2\) is the third coefficient inside the bracket**; the population coefficient is
\[
\boxed{c_3=2\pi^2\sqrt{\pi/2}}
\]
multiplying \(N^{-3/2}\).

A clean interface is
```lean
theorem coneClosedFactor_taylorCoeff_two :
    taylorCoeff coneClosedFactor 0 2 = Real.sqrt (Real.pi / 2) / 2
```
followed by
\[
Z_N=4\pi^2A\,N^{-1/2}-4\pi^2N^{-1}
     +2\pi^2A\,N^{-3/2}+O(N^{-2}).
\]

Use the ODE to get the jet, then reuse the jet/asymptotic uniqueness machinery. **Important scope boundary:** if the equality between the actual population integral and the closed expression is still only a derivation, this first proves the coefficient of the **closed expression**, not yet of the population integral. The latter needs that exact identification or an adequate remainder theorem.

**Size:** one day if the closed-form identification and tail derivative are available; otherwise split those obligations explicitly.

### (vi) Blow-up — the scaling changes the target

Here
\[
\varepsilon=N^{-1/2},\qquad
Z_N=\sqrt{2\pi}\,\varepsilon J(\varepsilon),
\]
and the actual amplitude is
\[
a_\varepsilon(u)=e^{-u^4/2}e^{-\varepsilon u^2/2}.
\]

For the **frozen** quartic amplitude, there is **no**
\(\varepsilon\log(1/\varepsilon)\) term:
\[
J_\infty(\varepsilon)
=\log(4/\varepsilon)+R_\infty
+\frac12\sqrt{\pi/2}\,\varepsilon
+O(\varepsilon^2\log(1/\varepsilon)).
\]
Indeed, the linear coefficient is
\[
\int_0^\infty\frac{1-e^{-u^4/2}}{u^3}\,du
=\frac12\sqrt{\pi/2}.
\]

For the **moving** amplitude, its first correction contributes the negative of this coefficient. Thus the order-\(\varepsilon\) term cancels.

The next logarithm requires order **\(\varepsilon^2\log(1/\varepsilon)\) in \(J\)**. The elementary expansion predicts
\[
J(\varepsilon)
=\log(4/\varepsilon)+R_\infty
+\frac1{16}\varepsilon^2\log(1/\varepsilon)
+O(\varepsilon^2).
\]
Therefore the target population coefficient is
\[
\boxed{\frac{\sqrt{2\pi}}{32}
       \quad\text{for }N^{-3/2}\log N.}
\]

The \(1/16\) comes from two contributions:
\[
-\frac{3}{16}\quad\text{(quartic amplitude/kernel)},\qquad
+\frac14\quad\text{(moving quadratic amplitude/kernel)}.
\]
These are derived targets, not claims of a checked Lean proof.

**Route:** elementary subtracted-kernel estimates, splitting at \(u=\sqrt\varepsilon\) and \(u=1\); integrate the singular Taylor terms exactly. Do not apply the kernel expansion down to zero without subtraction.

**Size:** the frozen linear coefficient is plausibly day-sized; the moving-amplitude cancellation plus next logarithm is a multi-day project. Existing `ampJ_two_term` bounds cannot identify this logarithmic coefficient.

### (vii) Quotient jets — useful tool, but not the NB phase bridge

Yes. Assuming analytic \(U,V\) at \(a\) and \(V(a)\ne0\), set \(W=U/V\). The useful first interface is the division-free recurrence:
```lean
taylorCoeff V a 0 * taylorCoeff (fun z => U z / V z) a (n + 1) =
  taylorCoeff U a (n + 1) -
    ∑ k ∈ range (n + 1),
      taylorCoeff (fun z => U z / V z) a k *
        taylorCoeff V a (n + 1 - k)
```
Prove local analyticity of the quotient, the eventual identity `W * V = U`, apply `taylorCoeff_mul`, and isolate the final summand.

A legitimate NB consumer is a **normalized surrogate observable**, once numerator and denominator have a common prefactor and analytic residual factors:
\[
U(x)=u_0+u_1x+\cdots,\quad V(x)=v_0+v_1x+\cdots,
\]
giving
\[
[ x ](U/V)=\frac{u_1v_0-u_0v_1}{v_0^2}.
\]
But the supplied NB extract does not specify such an observable. Do not manufacture an application: this tool neither proves exact-phase replacement nor its \(O(N^{-2})\) error. Logarithmic asymptotic expansions also need an appropriate asymptotic algebra, not automatically ordinary Taylor jets.

**Ranking:** cone \(c_3\) first, subject to the identification caveat; quotient jets next if there is a concrete consumer; frozen blow-up refinement next; ζ first-new-case as a dedicated multi-day sprint. The full next blow-up logarithm belongs in that multi-day tier too.

## 4. Convention safeguards

1. Add an explicit compatibility lemma:
   ```lean
   theorem gammaLogDeriv_eq_digamma :
       gammaLogDeriv = Complex.digamma
   ```
   Prove via unfolding/`logDeriv_apply`; avoid relying downstream on accidental reducibility.

2. Keep the normalization visible:
   \[
   \psi_j=[z^j]\psi(1+z),\qquad
   \lambda_k=(k-1)!\psi_{k-1}.
   \]
   Therefore
   \[
   \lambda_k=(-1)^k(k-1)!\zeta(k)\quad(k\ge2).
   \]

3. Real-part definitions are unconditional. Export complex-cast equalities only after a reality lemma.

4. Continue using **logarithmic derivatives**, not an unspecified complex `log Γ`. This preserves the branch-free character of the completed recurrence.