## Verdict

**C5 realises the substantive chart-face design.** You now have finite-order, compactly supported distributions on the chart-face parameter spaces, together with an exact reconstruction of every coefficient through normal jets of the observable.

My recommendation is **(i) close the project after a small interface tidy-up**: state smooth germ-locality explicitly and, preferably, identify `faceFunctional` with the canonical smooth-function pairing of `faceDistribution`. Representative independence is worth recording, but its proof needs one distinction discussed below. **Neither C4s nor C5f is required for the present paper-facing claim.**

This is an audit of the supplied statements and their mathematical implications, not an independent inspection of the Lean files.

## 1. Audit of CDXXII–CDXXIV

### What is genuinely established

The reconstruction has the form
\[
C_{\mu,q}(f)
 =\sum_{P,J,a} w_{J,a}\,
 B_{P,J,a,\mu,q}\bigl(j^\perp_{P,J,a}f\bigr),
\]
where:

- the sum is finite for each fixed coefficient;
- \(j^\perp_{P,J,a}f\) is the specified normal coordinate jet, restricted to the face;
- \(B\) is linear on smooth functions;
- \(B\) satisfies a finite tangential-jet estimate on `faceBox`;
- its restriction to test functions is a distribution supported in that compact box.

That is the core C5 claim. Importantly, the coefficient distribution is reconstructed **termwise from fixed functionals independent of the test observable**, not merely by attaching a different functional to each observable.

The route through `renormFunctional_congr` is completely satisfactory. The operator identity from CDXVIII is a useful additional theorem, but it is not an obligation of the reconstruction proof.

### The apparent weakenings

**Ambient base space versus compact integration subtype: fine.**  
A distribution should live on the ambient finite-dimensional vector space. Integrating over the compact `Base` subtype produces a distribution on that ambient space with support confined to `baseBox ×ˢ tangBox`. It does not require extending the integration measure with a smooth density across the boundary.

Indeed, the estimate is stronger than an ordinary full-jet bound in one respect: **no base derivatives are charged**. This does not imply that the resulting distribution has a smooth density in the base variable, and the paper should not say that.

**`faceOrder = Σ_j pieceDepth j`: valid, not sharp.**  
This is an upper bound on tangential order, not an assertion of minimal order. A paper statement saying “finite tangential order” is fully supported. A statement giving specifically \(\sum_{k\in K}p_k\) would need the sharper theorem.

Also distinguish:

- the order of the face distribution acting on its input \(u\);
- the order needed to control its composite action on \(f\), which includes the normal derivatives already taken in `faceJetObs`.

**`s ∈ baseBox` versus integration over `Base`: fine**, provided the indicated identification is the actual one used in the declarations. The stronger ambient formulation is natural and useful.

**Smooth pairing versus test-function pairing: correct, but expose the bridge.**  
You have not literally proved
```lean
faceDistribution ... (faceJetObs ... f ...)
```
because that expression need not be well-typed. You have proved the correct smooth-functional version. Compact support permits a canonical extension of a distribution’s action to all smooth functions, but that identification should be stated if the paper writes the reconstruction using distribution-pairing notation.

**Dependence on `obsExt`: currently a presentation choice, not yet a stated invariance theorem.**  
The landed result supports a fixed-extension formulation without qualification. It does not, merely by existing, support arbitrary changes of representative term by term.

## 2. The cheap interface theorems—and the representative-independence distinction

### A. Add smooth germ-locality: **S, recommended**

For smooth \(u,u'\), state:
\[
u=u'\text{ on an open neighbourhood of faceBox}
\quad\Longrightarrow\quad
\operatorname{faceFunctional}(u)
=\operatorname{faceFunctional}(u').
\]

This follows directly from linearity and `faceFunctional_eq_zero_of_eqOn_zero`, applied to \(u-u'\). It is worth a named corollary: it exposes precisely the locality that a reader expects from a compactly supported distribution.

An even more analytic formulation, if convenient, is congruence under equality of the required tangential jets on `faceBox`; neighbourhood equality is the clean public interface.

### B. Add the cutoff pairing identity: **S with cutoff infrastructure**

Choose a smooth compactly supported \(\chi\) equal to \(1\) on an open neighbourhood of `faceBox`. Then
\[
\operatorname{faceFunctional}(u)
=
\operatorname{faceDistribution}(\chi u).
\]

Here \(\chi u\) is bundled as a test function. Independence of the cutoff follows from germ-locality.

This identifies the existing smooth functional with the **canonical smooth-function action of the compactly supported distribution**. It is the most useful final bridge for the paper’s notation.

You do not need a new reconstruction proof: rewrite the existing reconstruction through this identity.

### C. Representative independence: **worth writing, but not equivalent to A**

There are two different assertions:

1. two *face inputs* \(u,u'\) agree near `faceBox`;
2. two *observable extensions* agree on the centered full box before normal differentiation.

A proves invariance in situation 1. To deduce situation 2, you must first show that the normal jets—and the further tangential jets used by the functional—agree where required.

**Agreement of observables merely on the face is insufficient.** For example, \(g(x)=x\) and \(g'(x)=0\) agree at the face \(x=0\), but their first normal derivatives differ.

Agreement on the **full-dimensional closed centered box** does suffice for smooth extensions when that box is the closure of its interior: derivatives agree in the interior and then on the boundary by continuity. If degenerate boxes are admitted, this argument requires an additional hypothesis or a separate treatment.

Thus I recommend the following order:

- add A;
- add B if convenient;
- add C using the existing “extensions agree in all relevant box jets” infrastructure, if available.

If C is not immediately cheap, a neighbourhood-agreement version is cleaner than silently treating closed-box agreement as germ agreement. The paper may meanwhile retain the fixed-extension convention.

## 3. Paper-facing chart-face paragraph — eight sentences

> The chart-face form of Theorem C resolves each coefficient distribution into a finite sum of normal-jet contributions associated with the chosen chart decomposition. For each piece, coordinate face, and normal multi-index, it constructs a distribution on the product of the ambient base-coordinate space and the tangential face-coordinate space. This distribution is supported in the corresponding compact face box and satisfies an explicit bound involving only finitely many tangential derivatives of its input. The coefficient is reconstructed by applying the associated smooth functional to the normal jet of the test observable and summing with the prescribed face weights. Because these normal-jet inputs need not be compactly supported, the formal reconstruction uses the smooth functional whose restriction to test functions is the stated distribution. The construction uses the fixed charts and smooth extensions supplied by the bridge data, rather than asserting a canonical intrinsic decomposition along a global stratification. Its order bounds are finite upper bounds, not claims of optimal tangential order or of a minimal normal-jet presentation. Together with the first form of Theorem C, this gives the testwise asymptotic expansion and a chart-face description of its coefficient distributions, but not a remainder estimate uniform on bounded sets of test functions.

After B lands, sentence five can instead explain that the pairing is the canonical smooth-function action of a compactly supported distribution. After C lands, sentence six can distinguish chart dependence from proved extension independence.

## 4. C4s: cheaper now, but not automatically M

**The analytic ingredients have improved substantially; the supplied inventory does not by itself justify reclassifying the whole task as M.** I would call it **M if the remaining work is only a uniformity wrapper; otherwise M–L**, with no reason here to assume the earlier L–XL estimate still applies.

The decisive missing audit is not coefficient boundedness. It is whether the *remainder proof* can be run with:

1. one depth choice depending only on geometry and truncation;
2. one finite test-function jet order;
3. one compact set in the original test-function domain;
4. constants and a large-\(N\) threshold independent of \(f\);
5. uniform control of every chart amplitude and every extension used by the remainder estimates.

`jetConst` and `faceConst` do not alone establish these five facts. In particular, continuity of each coefficient and testwise smallness of the remainder do not automatically supply the desired explicit uniform rate.

A future target should be the estimate
\[
\left|Z_N(f)-S_T(N;f)\right|
\le
C_T\,\omega_T(N)\,
\max_{0\le r\le R_T}\sup_{y\in L_T}
\bigl\|D^r f(y)\bigr\|,
\qquad N\ge N_T,
\]
where \(S_T\) is **exactly the existing truncation**, and \(\omega_T\) is the remainder profile justified by the existing engine theorem. The quantifier order must be
\[
\forall T\;\exists R_T,L_T,C_T,N_T\;\forall f\;\forall N\ge N_T.
\]
If the current claim is little-\(o\) at a specified scale, the selected profile must also have that little-\(o\) property; a borderline big-\(O\) estimate is not an interchangeable substitute.

For Lean, the most convenient first theorem would likely use a supplied \(M\) and a hypothesis bounding all derivatives through \(R_T\) on \(L_T\), rather than immediately packaging the maximum as a seminorm. That matches the landed bound interfaces.

**Recommendation: stop rather than add C4s now.** Nothing about C5 makes a seminorm-uniform remainder necessary for the current theorem. If the paper needs a distribution-topology asymptotic expansion, reopen C4s as a separately scoped strengthening.

## 5. Closing decision and record

### Decision

**Close after the small C5 interface tidy-up. Do not do C5f as a closing requirement.**

Regrouping by \(|a|=r\) is finite-sum bookkeeping. It can improve notation, but it neither supplies a missing analytic property nor upgrades the meaning of the theorem. Do it only if the final displayed paper formula genuinely needs that indexing.

### Suggested final checklist

1. **S:** named smooth neighbourhood-congruence theorem for `faceFunctional`.
2. **S, infrastructure permitting:** cutoff pairing identity and cutoff independence.
3. **S if the required box-jet lemma already exists:** extension independence; otherwise retain the fixed-extension wording.
4. **S:** one public documentation block linking reconstruction, continuity, compact support, and the order estimate.

If you want the exact phrase “the coefficients are pairings of compactly supported face distributions with normal jets,” item 2 is the appropriate formal bridge. If you say “associated smooth functionals,” the landed statements already suffice.

### Non-claims for the closure record

- No seminorm-uniform remainder or asymptotic expansion in a specified distribution topology.
- No canonical intrinsic global stratification or chart-independent individual face summands.
- No minimal tangential order, minimal normal-jet representation, or uniqueness of the face decomposition.
- No regularity of a density in the base variable inferred merely from the absence of base derivatives in the bound.
- No claim that `faceJetObs f` is itself compactly supported.
- No arbitrary representative independence unless explicitly proved; face-value agreement alone does not preserve normal jets.
- No sharp support equality: the support statements are inclusions.
- No single finite face-jet list asserted to work simultaneously for every asymptotic coefficient.

**Bottom line:** the analytic C5 deliverable is complete on the supplied statements; the remaining paper-facing work is chiefly making the smooth-pairing and representative conventions explicit, not adding another asymptotic theorem.
