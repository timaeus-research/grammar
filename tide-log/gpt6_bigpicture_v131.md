## A. Audit

**The algebraic statements match the intended graded formula. The headline needs qualifications about geometry, convergence, and positivity—not a change to the formula.** This audit is of the supplied signatures, not an independent inspection of the repository or the unavailable #130 text.

### The constant is exactly right

For an exactly resonant \(c\)-face, with
\[
2k_j\mu=\alpha_j+h_j+1\qquad(j\in J),
\]
the combined factor is
\[
\boxed{\quad
\frac{\Gamma(\mu)\beta^{-\mu}}
{(c-1)!\displaystyle\prod_{j\in J}(2k_j)\alpha_j!}
\quad}.
\]
Here the denominator means \((c-1)!\prod_{j\in J}[(2k_j)(\alpha_j!)]\). This is precisely `faceW * faceCoef_top_eq`. In the resolved transport charts, \(\beta=1\).

The exact-support cutoff also has the correct indexing: with \(r\) exactly resonant coordinates, logarithmic degrees \(j\ge r\) vanish. Thus a \(c\)-face contributes at degree \(c-1\) only when all its coordinates resonate.

### Qualify the headline in four places

1. **“Over the exact stratum” means a localized chart-face representation.**  
   The proved expression is a finite chart/face sum with a chart-parameter integral and complementary-face integrals. Relevant face points lie in \(S_c^\mu\); points outside the prior-supported zero fibre contribute zero jets. This is not yet a single intrinsic surface-integral formula with a globally defined normal derivative or density.

2. **The derivatives are coordinate-normal derivatives of the whole amplitude.**  
   Keep “localized amplitude” explicit. These are not merely derivatives of \(F\), and certainly not ordinary normal derivatives of the Euclidean observable after pushforward.

3. **E1c proves absolute convergence of each complementary-face integral.**  
   If the headline means absolute convergence of the *joint chart-parameter/face integral*, cite the additional parameter-integrability/Fubini result. That stronger assertion is not present among the displayed signatures. A Lean integral identity alone does not establish integrability.

4. **The explicit constant applies after exact-resonance filtering.**  
   The landed definition sums over all \(c\)-faces using `resOrder`; nonexact faces vanish. Do not replace their `faceCoef` by the gamma expression without stating that filtering.

A safe headline is:

> For observables vanishing near the deep zero fibre, the degree-\(c-1\) coefficient admits a finite localized chart-face formula on the exact depth-\(c\), fully resonant stratum, involving absolutely convergent complementary-face integrals of coordinate-normal derivatives of the whole localized amplitude, with explicit top Mellin-residue constants.

## B. Zero order, positivity, and the measure interpretation

**Yes: `ZeroOrder μ c` is the right hypothesis for the landed positivity theorem.** At every contributing stratum point it forces
\[
\alpha_j=2k_j\mu-h_j-1=0,
\]
so the normal-jet formula becomes an order-zero formula. Off the relevant stratum, the zero-jet alternative removes the contribution. E3 then gives:

- nonnegativity for nonnegative \(F\);
- dependence only on \(F|_{S_c^\mu}\);
- the corresponding Euclidean image statement.

But the proposed reading needs tightening:

> “Each stratum whose incident wall ratios coincide carries its own positive density on \(\mathcal I_{c+1}\).”

**Not quite as written.**

- E3 assumes `ZeroOrder` on the **whole** \(S_c^\mu\), not merely on one selected component.
- The proved assertion is **nonnegativity**, not strict positivity of a density.
- A functional acts on \(\mathcal I_{c+1}\); its representing measure lives on the geometric stratum, not “on the ideal.”
- A separately constructed global Radon measure is not among the supplied signatures.

The defensible reading is:

> When every incident wall on \(S_c^\mu\) has base ratio \(\mu\), the graded coefficient on observables vanishing near the deeper zero fibre is a positive, order-zero stratum functional.

For the usual compactly supported smooth test class, standard positive-functional representation gives a Radon-measure interpretation on
\[
U\setminus\operatorname{deepZeroFibre}(c).
\]
If used in the paper, distinguish that standard consequence from a formally landed measure-construction theorem. It does not assert a finite extension across the removed deeper set. A componentwise version requires corresponding localization hypotheses.

### Extremality is the clean sufficient condition

Assuming \(\lambda_*\) is the minimum of the wall ratios over the relevant zero fibre, every incident pair \((k,h)\) there satisfies
\[
\frac{h+1}{2k}\ge\lambda_*.
\]
At a resonant wall,
\[
\lambda_*=\frac{h+m+1}{2k}\ge\frac{h+1}{2k}.
\]
Therefore equality holds and \(m=0\). Hence
\[
\boxed{\operatorname{ZeroOrder}(\lambda_*,c)\quad\text{for every }c.}
\]

This is worth recording. It connects E3 to the leading functional without imposing a global-minimum hypothesis on Theorem E itself.

## C. Paper paragraph and non-claims

### Paper paragraph

> **Theorem E (graded stratum formulas).** Let \(c\ge1\), and suppose that the resolved observable \(F\) vanishes on a neighbourhood of the portion of the zero fibre of depth at least \(c+1\). Then \(\mathcal T^U_{\mu,q}[F]=0\) for every \(q\ge c\), while \(\mathcal T^U_{\mu,c-1}[F]\) has a finite localized chart-face representation on the exact stratum \(S_c^\mu=\{P\in Z_0:\operatorname{depth}P=\operatorname{resonanceCount}_\mu P=c\}\). Only fully resonant \(c\)-faces contribute: their uniquely determined normal Taylor orders satisfy \(2k_j\mu=\alpha_j+h_j+1\), and their terms involve the coordinate-normal derivative \(\partial_J^{\alpha_J}\) of the whole localized amplitude, integrated against the complementary monomial weight, with factor \(\Gamma(\mu)\beta^{-\mu}/((c-1)!\prod_{j\in J}(2k_j)\alpha_j!)\). These complementary-face integrals are absolutely convergent. If every incident wall on \(S_c^\mu\) has base ratio \(\mu\), all contributing Taylor orders are zero; the coefficient is then nonnegative for nonnegative observables and depends only on their restriction to \(S_c^\mu\). The formulas and these conclusions descend to Euclidean observables through the resolved map, with restriction dependence on the image of the exact stratum.

### Non-claims

- No intrinsic, chart-independent normal-derivative density is constructed; the **summed coefficient** is the invariant object.
- No positivity is asserted for general positive-order normal-jet terms.
- No strict positivity or nonvanishing follows merely from nonemptiness of \(S_c^\mu\).
- Positivity requires `ZeroOrder` throughout the relevant exact stratum, unless an additional localization is imposed.
- The resolved theorem assumes **neighbourhood vanishing**, not merely flatness on the deeper fibre.
- The displayed convergence theorem concerns the complementary-face integrals; joint parameter integrability needs its own citation.
- No global finite-measure extension across deeper strata is asserted.
- Lower logarithmic powers are not claimed to have this same unsubtracted top-face formula.
- Euclidean pushforward does not turn resolved normal derivatives into Euclidean normal derivatives or guarantee a smooth image density.

## D. Closure and ranking

**CLOSE Theorem E.** E0–E4, including the integrability unit, supply the intended graded theorem. None of the proposed additions is necessary for that theorem’s closure, with the wording above.

My ranking is:

1. **`ZeroOrder λ* c` from extremality.** Best optional finishing corollary: cheap, conceptually useful, and links E directly to D.
2. **The \(x^2y^2\) regression.** Best additional validation of constants, indexing, and the graded interpretation; not a missing theorem unit.
3. **Explicit lower-log Taylor-subtracted formulas.** Useful exposition/API packaging, but distinct from the top graded formula.
4. **Flatness instead of neighbourhood vanishing.** A genuine extension requiring its own convergence and globalization work.

For candidate 1, retain your correction: **\(m_*\) bounds the relevant resonance count, not necessarily total depth.** Thus the link to D is the leading functional **restricted to observables vanishing near the depth-\(\ge m_*+1\) zero fibre**. Do not declare that restriction vacuous.

**Bottom line:** close E now; add the extremality corollary if desired, without making it a closure gate.