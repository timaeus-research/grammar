## Verdict

**CDLXVII establishes intrinsic finite-jet dependence, but not a separately constructed residue–jet pairing.** Its main invariance theorem justifies describing the coefficient as a functional on an **ideal-theoretic transverse-jet quotient**. It does not, from these signatures, construct that quotient, an intrinsic residue object acting on it, or the displayed pairing as a Lean definition and identity.

There are two concrete corrections: the definitions mishandle exponent zero, and the paper’s list of determining data must include the prior.

## (a) Signature audit

### 1. The ideal-power definition is appropriate for the exponents used

For **\(n\geq1\)**, `MemIdealPowNear S n H P` expresses membership of the germ of \(H\) in \(\mathcal I_{S,P}^{\,n}\), subject to the distinction that Lean asks for **globally defined** smooth factors vanishing on all of \(S\).

For a locally closed embedded smooth submanifold, that distinction does not change the germ condition: choose a submanifold neighbourhood of \(P\), shrink it, and use smooth cutoffs to extend the local factors globally while preserving vanishing on \(S\). This uses the usual smooth-manifold bump-function machinery; it is **not itself established by the listed signatures**.

Finite `m` is not a restriction. Algebraic ideal powers consist, by definition, of finite sums of products. In normal coordinates, the relevant Taylor/Hadamard factorisation uses finitely many monomials.

**However, exponent zero is wrong as currently defined.** With `n = 0`, every empty product is \(1\), so the displayed sum is the natural number `m`. Thus both definitions require \(H\) to be locally a nonnegative integer constant, whereas
\[
\mathcal I_S^0=C^\infty,\qquad \mathfrak m_P^0=C^\infty.
\]
This does **not** affect the coefficient theorems, which use `stratumJetOrder + 1`. Fix it by special-casing zero, restricting the definitions to positive exponents, or allowing smooth coefficients multiplying the products.

### 2. The order formula is correct on the exact stratum

At an exact-stratum point, resonance gives, for every wall,
\[
2k_j\mu=h_j+1+\alpha_j,\qquad \alpha_j\in\mathbb N.
\]
Consequently the natural floor and truncated natural subtraction give precisely \(\alpha_j\), and
\[
n(P)=\sum_j\alpha_j=|\alpha|.
\]

Thus this is the **total resonant derivative order** of the face formula. It is an order bound, not necessarily the minimal order of the resulting functional: cancellations or the prior can lower the actual order.

Away from the exact stratum, the natural-floor/truncated-subtraction expression should not silently be replaced by an ordinary integer-valued expression.

### 3. “Depends only on the transverse jet” is justified—with a scope distinction

There are two legitimate meanings:

* **Ideal-theoretic definition:** the transverse \(n\)-jet along \(S\) is the class modulo \(\mathcal I_S^{n+1}\). Under this definition, the invariance theorem establishes exactly the necessary kernel statement.
* **Derivative-based definition:** equality of normal Taylor coefficients through order \(n\) along \(S\). Its equivalence with the ideal-theoretic definition follows from Taylor/Hadamard factorisation in submanifold coordinates, but that equivalence is **not among the listed Lean results**.

For a locally closed smooth submanifold, the factorisation hypothesis is not mathematically stronger at the germ level. It is, however, the hypothesis actually formalised. The paper should define its jet ideal-theoretically, or distinguish the standard geometric identification from the Lean theorem.

This equivalence is specific to the submanifold situation; one should not invoke a blanket statement for arbitrary closed sets.

### 4. Terminology and canonicity

Use **“transverse \(n\)-jet along \(S\), understood modulo \(\mathcal I_S^{n+1}\)”** or **“normal \(n\)-jet along \(S\)”**. Both are reasonable.

The quotient is canonical. A decomposition into normal Taylor coefficients generally is not: the associated graded pieces are canonically
\[
\mathcal I_S^r/\mathcal I_S^{r+1}\cong
\operatorname{Sym}^r(N^*S),
\]
but identifying the entire higher-order quotient with a direct sum requires choices.

Do not explain this by saying tangential derivatives “are absorbed in density integration.” The ideal-theoretic quotient retains coefficient functions along \(S\), hence their tangential variation; its intrinsic meaning does not depend on integration by parts.

## (b) Paper wording

The current sentence has three overclaims or ambiguities:

1. **It omits the prior \(\varphi\).**
2. It may suggest that an explicit residue–jet pairing has been constructed in Lean.
3. “Finite jet” means a finite bound **at each point** here; the signatures alone do not assert a uniform global bound.

A replacement is:

> Without the zero-order condition, the coefficient functional has intrinsic finite transverse-jet dependence. At \(P\in S^\mu_c\), put
> \[
> n(P)=\sum_{(k,h)\in\operatorname{pairs}(P)}
> \bigl(\lfloor2k\mu\rfloor_{\mathbb N}-h-1\bigr),
> \]
> where each summand is the nonnegative resonant Taylor order of the corresponding wall. If \(F,F'\in\mathcal I_{c+1}\) and the germ of \(F-F'\) at every \(P\in S^\mu_c\) belongs to \(\mathcal I_{S^\mu_c,P}^{\,n(P)+1}\), then
> \(\mathcal T^U_{\mu,c-1}[F]=\mathcal T^U_{\mu,c-1}[F']\).
> Here ideal-power membership means local expressibility as a finite sum of products of \(n(P)+1\) smooth functions vanishing on the stratum. Thus the functional descends to the corresponding transverse-jet quotient of admissible observables. Both this quotient condition and the order bound are coordinate-free; the induced functional depends on the resolved data, including \(K,\pi\), the prior density \(\varphi\), and \(\mu,c\), rather than on the chart transport. The face formula presents its action using normal derivatives and weighted face integrals in normal-crossings coordinates, but that presentation is not canonical.

For the Lean annotation, add something like:

> **Formalised:** invariance under the stated ideal-power equivalence. An explicit quotient construction and residue–jet pairing are not constructed in this unit.

Mathematically, once linearity is available, the descended functional is a dual element and its evaluation can be called a pairing. **That abstract observation should not be conflated with formalisation of**
\[
\big\langle\operatorname{Res}^{\alpha}_{S^\mu_c}[\cdots],
j^\alpha_S(F)\big\rangle
\]
**as separately defined objects.** In particular, a coordinate derivative multi-index is not itself the canonical replacement for the jet quotient.

## (c) Direction: ranked recommendations

1. **Fix exponent zero and align the paper/Lean scope.**  
   State the jet convention explicitly and include the prior. If derivative-language equivalence matters, formalise the local submanifold factorisation/global-factor extension lemma. This closes the main interpretation gap.

2. **Package the actual descent before adding another residue theorem.**  
   Let \(A=\mathcal I_{c+1}\) be the admissible observable space and define
   \[
   J=\{H:\ H_P\in\mathcal I_{S,P}^{\,n(P)+1}
                \text{ for every }P\in S\}.
   \]
   The natural quotient is
   \[
   A/(A\cap J).
   \]
   Establish the required subspace properties and descended linear functional. Do not write
   \(A/(\mathcal I_c+\mathcal I_S^{n+1})\) without checking domain inclusion and interpreting the variable exponent. If \(\mathcal I_c\) consists of observables vanishing near \(S\), it is already contained in the jet kernel and adds nothing.

3. **Treat the per-wall version as an optional sharpening.**  
   Locally, with \(\mathcal I_{E_j}=(x_j)\),
   \[
   \mathcal I_S^{|\alpha|+1}
   \subseteq \sum_j\mathcal I_{E_j}^{\alpha_j+1}.
   \]
   Therefore the per-wall statement would annihilate a **larger ideal**, giving a sharper dependence result under a weaker equality hypothesis. It is intrinsically expressible through wall ideals and is useful if the paper wants the specific anisotropic \(j^\alpha\) notation. The total-order result is sufficient—and cleaner—for the current paper-level coordinate-free claim.

4. **Do not yet assert “conormal distribution of order \(n\).”**  
   These signatures establish annihilation and invariance, not test-function continuity, distributional order estimates, or a microlocal conormal statement. Those require additional definitions and results; normal derivative order and conormal-distribution order are not interchangeable terminology.