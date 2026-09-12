## Recommendation

**Do R2 next, but use a strengthened version of (B): partition the range of the unit, rather than localising the normal coordinates.** This reuses the existing continuous-amplitude scalar-kernel theorem directly and avoids both the negligible-complement lemma and a separate theorem for a unit depending on residual coordinates.

The landed \(x^2y^4\) and posterior calculations are excellent regression anchors. The constants stated in the appendix are mathematically consistent.

---

## Q1. Ranking and mathematical assessment

### Ranking

1. **(B), modified to unit-range comparison.** Best mathematical/API fit: continuous data, original product region, explicit original-data face coefficient, signed observables after an elementary extension.
2. **(D), supplied regular weights.** Natural next interface step; regular normal-dependent weights enter exactly the continuous amplitude used by R2.
3. **(E), selectively:** a variable-unit regression, a genuine residual/log example, and then the one-theorem paper-facing statement. Defer subleading terms and empirical transfer.
4. **(A), strip normalisation.** Valuable for the analytic expansion programme, but unnecessarily expensive for this leading-order product-box objective.
5. **(C).** Useful only for special cases; not a general R2 route.

I would allocate **three units to the standalone R2 analytic certificate, one to its product-piece bridge, and one to a regression**. Do not make completion of the entire atlas refactor a prerequisite for landing the analytic theorem.

### Is the proposed localisation argument sound?

**Yes, with two important qualifications.**

Write
\[
r_a=\frac{h_a+1}{2k_a},\qquad
\lambda=\min_a r_a,\qquad
M=\{a:r_a=\lambda\},\quad L=M^c,\quad m=|M|.
\]

1. **Only localise the \(M\)-coordinates.**  
   The complement of a small box in *all* normal coordinates is generally not negligible: a residual coordinate bounded away from zero can still carry leading-order mass.

2. **The frozen unit is \(u(z,(0_M,v_L))\), and the current scalar-unit theorem does not immediately handle it.**  
   Treating \(v_L\) as extra base coordinates makes the scalar phase factor
   \[
   u(z,(0_M,v_L))\prod_{a\in L}v_a^{2k_a},
   \]
   which vanishes on residual coordinate hyperplanes. That violates the current compact-base strict-positivity hypothesis. Truncation plus an integrable domination argument would repair this, but it is additional analysis.

The corrected complement
\[
\{n:\exists a\in M,\ |n_a|\geq\eta\}
\]
**is negligible at scale \(N^{-\lambda}(\log N)^{m-1}\)**:

- if some minimal coordinates remain, its contribution has at most log degree \(m-2\);
- if none remain, the remaining phase coordinates have strictly larger ratios;
- if no phase coordinates remain at all, the contribution is exponentially small.

For \(m=1\), do not formulate this as a natural-number “log degree \(m-2\)” statement. The proof must use the improved power or exponential case. A uniform positive lower bound for \(u\), boundedness of \(A\), and integrability of \(|\beta|\) suffice for the domination.

Thus your sketch is sound after correction, but there is a cleaner proof.

---

## The cleaner proof: compare on the range of \(u\)

On the compact base-times-box, obtain
\[
0<a\leq u(z,n)\leq B.
\]

For any \(\delta>0\), choose a finite continuous nonnegative partition of unity
\[
\sum_j\chi_j(s)=1\quad(s\in[a,B]),
\]
with each \(\chi_j\) supported in an interval \([\ell_j,r_j]\subset(0,\infty)\) satisfying
\[
r_j/\ell_j\leq 1+\delta.
\]

First suppose \(\beta\geq0\) and \(A\geq0\). Set
\[
A_j(z,n)=A(z,n)\chi_j(u(z,n)).
\]
These are continuous amplitudes. On their supports, for \(N\geq0\),
\[
A_j e^{-Nr_jP(n)}
\;\leq\;
A_j e^{-Nu(z,n)P(n)}
\;\leq\;
A_j e^{-N\ell_jP(n)},
\qquad P(n)=\prod_a n_a^{2k_a}.
\]

**Every bounding integral is already covered by**
`hasLeadingTerm_integral_scalarBoxKernel`, with **constant** `q` and amplitude `A_j`.

Their face coefficients evaluate the partition functions at
\[
u_F(z,v)=u(z,(0_M,v_L)).
\]
Consequently the lower and upper coefficients bound the desired coefficient \(C\) by
\[
(1+\delta)^{-\lambda}C
\;\leq C^-_\delta\leq C
\leq C^+_\delta
\;\leq(1+\delta)^\lambda C.
\]
Let \(\delta\to0\).

This proves the variable-unit theorem:

- without normal localisation;
- without complement estimates;
- without a residual-dependent scalar-unit theorem;
- without analytic amplitudes;
- and without changing the integration region.

For signed data, split both
\[
\beta=\beta^+-\beta^-,
\qquad A=A^+-A^-.
\]
The amplitude parts remain continuous; the weight parts remain integrable. Apply the nonnegative result four times and use linearity of `HasLeadingTerm`.

**This should be the public theorem: no sign assumption on either amplitude or base weight.**

---

## Clean certificate and coefficient

Let
\[
\alpha_a=h_a-2k_a\lambda\quad(a\in L).
\]
Then \(\alpha_a>-1\). Define
\[
D(h,k,\lambda)
=
\frac{\Gamma(\lambda)}{(m-1)!}
\prod_{a\in M}\frac1{2k_a}.
\]

For the **symmetric** normal box, the coefficient is
\[
\boxed{
C=
2^mD(h,k,\lambda)
\int_T\beta(z)
\int_{[-b,b]^L}
 A(z,(0_M,v_L))\,u(z,(0_M,v_L))^{-\lambda}
 \prod_{a\in L}|v_a|^{\alpha_a}\,dv\,dz .
}
\]

The factor \(2^m\) accounts only for the minimal signs; residual signs are already included in the symmetric residual integral.

### Suggested Lean API

The following is a proposed signature, not a claim about existing identifiers:

```lean
theorem hasLeadingTerm_integral_symmetricVariableBoxKernel
    (hk : ∀ i, 0 < k i) (hb : 0 < b) {l : ℝ}
    (hl : 0 < l)
    (hmin : ∀ i, l ≤ ratioExp h k i)
    (hatt : ∃ i, ratioExp h k i = l)
    (hA : Continuous (Function.uncurry A))
    {T : Set (Fin t → ℝ)} (hT : IsCompact T)
    (hu : Continuous (Function.uncurry u))
    (hu_pos : ∀ z ∈ T, ∀ v ∈ symmetricBox b, 0 < u z v)
    {βw : (Fin t → ℝ) → ℝ}
    (hβw : IntegrableOn βw T) :
    HasLeadingTerm
      (fun N =>
        ∫ z in T, βw z *
          symmetricVariableBoxKernel n h k b u A z N)
      (∫ z in T, βw z *
        symmetricVariableBoxFaceCoeff n h k b u A l z)
      l
      (multCount (ratioExp h k) l - 1)
```

For the first implementation, match the existing kernel’s orthant convention, then derive the symmetric theorem by finite reflection summation.

For `symmetricVariableBoxFaceCoeff`, initially use the existing full-dimensional projected-unit-box representation:
\[
b^{\sum_{a\in L}(\alpha_a+1)}D
\sum_\sigma\int_{\mathrm{unitBox}}
 A(z,x_\sigma(w))u(z,x_\sigma(w))^{-\lambda}
 \operatorname{residualWeight}(w)\,dw,
\]
where
\[
x_\sigma(w)=\operatorname{reflect}_\sigma(b\,\operatorname{faceProj}(w)).
\]

That keeps the implementation close to CCL and avoids introducing subtype-coordinate integration during the analytic proof. The compact residual-integral formula above can be an interpretation theorem.

**Prefer `HasLeadingTerm`, not asymptotic equivalence:** a signed observable can have zero coefficient. Positivity/nonvanishing is a separate corollary.

Global continuity is a reasonable first low-level signature matching CCXXXI. For the chart bridge, add a `ContinuousOn` compact-domain wrapper; product-chart hypotheses only supply continuity on `W`.

---

## Q2. Proposed module contracts

### Unit 1 — `PositiveUnitRangePartition`

**Contracts**

1. A positive continuous function on a nonempty compact domain has bounds \(0<a\leq u\leq B\).
2. A finite continuous partition of unity on \([a,B]\), subordinate to positive intervals of arbitrarily small multiplicative width.
3. A real-valued approximate-squeeze lemma:
   if normalized lower and upper bounds converge to coefficients within factors tending to \(1\) of \(C\geq0\), then the normalized target converges to \(C\).

**Implementation advice**

- Handle an empty base separately.
- Piecewise-linear hats are enough; no smooth partition-of-unity machinery is needed.
- Avoid `limsup`/`liminf` unless that API is already established. An eventual-\(\varepsilon\) squeeze is likely lighter.
- Only require partition identities on the compact range.
- If a globally continuous positive extension is convenient, use `max a u`. Avoid taking negative real powers of an arbitrary globally signed extension.

### Unit 2 — `ContinuousUnitKernel`

**Contracts**

1. Kernel comparison for nonnegative amplitudes and weights, eventually for \(N\geq0\).
2. Variable-unit `HasLeadingTerm` on the existing orthant.
3. Signed extension by positive and negative parts.
4. Integrability of the face coefficient against any integrable base weight.

**Reuse**

- `hasLeadingTerm_integral_scalarBoxKernel`, with constant `q`;
- scaling of its coefficient by `q ^ (-l)`;
- finite-sum and scalar/additive closure of `HasLeadingTerm`;
- the residual coefficient representation from CCL.

**Pitfalls**

- All integral inequalities need integrability established, not merely pointwise inequalities.
- Partition functions must be evaluated on the **full unit** before invoking the scalar theorem. The scalar theorem itself then restricts them to the minimal face.
- The zero-coefficient case must work without dividing by \(C\).

### Unit 3 — `SymmetricVariableUnitCells`

**Contracts**

1. A variable-unit cell structure carrying the same geometric/density data as `ScalarUnitCell`, with `u z n` instead of `q z`.
2. Reflection compatibility for both amplitude and unit.
3. Symmetric `HasLeadingTerm`.
4. Explicit residual-face coefficient.
5. Specialisation to normal-independent units agrees with the current scalar-cell coefficient.
6. Dependence only on face restrictions:
   equality of \(A\) and \(u\) on the minimal face implies equality of coefficients.

**Reuse**

- the existing reflection decomposition;
- `sum_reduce_of_indep`;
- `faceLeadConst_one_eq`;
- the residual scaling identity.

Do not force this structure to extend `ScalarUnitCell` by supplying an artificial `q`. Keep the old interface as a specialisation, or factor out common data later.

The reflection reduction still works: **both \(A\) and \(u\), once evaluated on the minimal face, are independent of minimal signs.**

### Unit 4 — `VariableUnitProductPieces`

**Contracts**

1. Replace the scalar normal form on a piece by
   \[
   K\circ\Phi\circ\Psi(z,n)
   =q_{\mathrm{var}}(z,n)\prod_a n_a^{2k_a}.
   \]
2. Establish continuity and positivity of `q_var` on the compact piece.
3. Obtain the piece certificate from Unit 3.
4. Show compatibility with the old certificate under `unit_indep`.

Here `q_var` includes the original unit and the phase factors of coordinates assigned to the piece’s base. Those active base coordinates are bounded away from zero by the fixed positive cutoff.

**Important scope boundary:** this lands the replacement analytical input. Removing `unit_indep` from the top-level product-chart theorem still requires propagating the new coefficient through tied-piece summation, cutoff independence, and posterior assembly. Do not silently present that refactor as automatic.

### Unit 5 — regression

My first choice is a normal-dependent \(x^2y^4\) test:
\[
K(x,y)=(1+y^2)x^2y^4.
\]
On the minimal face \(y=0\), the unit is \(1\), so the coefficient remains
\[
2\Gamma(1/4).
\]

Then test residual dependence, for example
\[
K(x,y)=(1+x^2+y^2)x^2y^4,
\]
whose coefficient is
\[
\Gamma(1/4)\int_0^1
x^{-1/2}(1+x^2)^{-1/4}\,dx.
\]
No closed-form evaluation is needed: this is a sharp regression against incorrectly freezing at the origin.

If the product-piece bridge takes longer, landing this regression directly from Unit 3 still demonstrates that R2’s analytic gap is closed.

---

## Q3. Audit of CCL–CCLII

### Residual scaling and minimal-coordinate product

The stated formulas are correct.

For each residual coordinate, scaling \(v_a=bw_a\) gives
\[
v_a^{\alpha_a}\,dv_a=b^{\alpha_a+1}w_a^{\alpha_a}\,dw_a.
\]
Thus the factor is exactly
\[
b^{\sum_{a\notin M}(\alpha_a+1)}.
\]

There is no corresponding leading power of \(b\) from minimal coordinates. Their endpoint dependence affects lower logarithmic orders, not this leading coefficient.

The face constant at radius \(1\) is
\[
\frac{\Gamma(\lambda)}{(m-1)!}
\prod_{a\in M}\frac1{2k_a}.
\]
The product is over **minimal coordinates only**. Residual coordinate factors are represented by the residual integral. This is precisely the distinction tested by \(x^2y^4\).

### \(x^2y^4\)

Here
\[
M=\{y\},\quad \lambda=1/4,\quad m=1,\quad \alpha_x=-1/2.
\]
The symmetric coefficient is
\[
2\cdot\frac{\Gamma(1/4)}4
\int_{-1}^1|x|^{-1/2}\,dx
=
2\Gamma(1/4).
\]

For \(F=x^2\), the numerator coefficient is
\[
2\cdot\frac{\Gamma(1/4)}4
\int_{-1}^1|x|^{3/2}\,dx
=
\frac{2}{5}\Gamma(1/4),
\]
giving the posterior limit \(1/5\).

No mathematical inconsistency is visible in the displayed CCLI–CCLII statements.

### Cutoff consistency

**Yes:** given the applicable hypotheses, `productCoeffD_eq_of_cutoff` is sufficient to transfer the computed total coefficient from \(\varepsilon=1\) to any admissible \(0<\varepsilon<1\). It does not make the individual piece coefficients invariant.

For the fixed outer square \([-1,1]^2\), the two tied contributions should be
\[
\begin{aligned}
\{0,1\}\text{-piece}:&\quad
2\Gamma(1/4)\sqrt{\varepsilon},\\
\{1\}\text{-piece}:&\quad
2\Gamma(1/4)(1-\sqrt{\varepsilon}).
\end{aligned}
\]
Their sum is constant.

At \(\varepsilon=1\), the latter base has zero Lebesgue mass; whether it is literally empty or consists of endpoint sets depends on boundary conventions.

For the \(x^2\) numerator, the corresponding check is
\[
\frac{2\Gamma(1/4)}5\varepsilon^{5/2}
+
\frac{2\Gamma(1/4)}5(1-\varepsilon^{5/2}).
\]

Be precise about `b`: the full tied piece has **local normal radius \(\varepsilon\)**, whereas the original square has outer radius \(1\).

### One correction to candidate (E)

\[
K=x^2y^2z^4
\]
does **not** test a leading log: its unique minimum ratio is \(1/4\), attained at \(z\), so \(k^*=0\).

Use
\[
\boxed{K=x^2y^4z^4}
\]
with unit density on \([-1,1]^3\). Then
\[
\lambda^*=1/4,\qquad m=2,\qquad k^*=1,
\]
and \(x\) is residual with exponent \(-1/2\). Its coefficient is
\[
2^2\frac{\Gamma(1/4)}{4\cdot4}
\int_{-1}^1|x|^{-1/2}\,dx
=\Gamma(1/4).
\]
Thus the target regression is
\[
\int_{[-1,1]^3}e^{-Nx^2y^4z^4}
\sim
\Gamma(1/4)N^{-1/4}\log N.
\]

**Bottom line:** R2 need not reopen the strip machinery or build a new internal stratum decomposition. The existing theorem’s freedom to accept an arbitrary continuous amplitude is enough to remove a positive continuous phase unit by finite range comparison, while retaining exactly the minimal-face coefficient you now have in CCL.
