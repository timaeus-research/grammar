# Direction consult #63 — "let's give the differential geometry a shot"

The user has asked us to attempt the **coordinate-free differential geometry** of the original grammar paper (Gerraty–Murfet, *Grammar (Expectations and the Exceptional Divisor)*): the conormal-bundle presentation of the normal Taylor coefficients (`subsec:normal_crossing`: exact sequence `0 → TX → TM|_X → NX → 0`, canonical splitting `N*X ≅ ⊕ L_i` for a transverse intersection of divisors, `lem:normal_deriv`, `defn:normal_diff` with values in `Γ(X, Sym^r N*X)`), the tubular-neighbourhood / integration-along-fibres presentation (`subsec:tubular_nbhd`: `Φ : NX → M`, pushforward of densities `τ_*`, the dressed moments, `eq:tubular_expansion`), and the moment tensors with the coordinate-free contraction (`subsec:moment_tensors`: `eq:moment_tensor_defn`, `eq:per_stratum_expansion_coordfree`, `rem:reduce_to_box`). Currently these subsections carry essentially no Lean dots for the coordinate-free statements (the tubular subsection has measure-theoretic dots for the box split and the fibre pushforward; the moment-tensor subsection has three dots pointing at population-box results). The paper text is appended below.

We want a **bounded, honest programme** whose output is a formalisation of the *mathematical content* of these subsections that can be dotted, not a formalisation of the exposition's vocabulary for its own sake. Please choose the formulation.

## What exists in Lean already

### A. `timaeus-research/strucdual`, `StrucDual/Geometry/*` (Lean 4.29.0, Mathlib v4.29.0 — a DIFFERENT pin from grammar's v4.33.1)
An ambient-Euclidean tubular-neighbourhood library (the paper's `rem:analytic_tubular` cites it; the mirror carries six `\leanref{StrucDual/...}` dots pinned at `f51a798`):
- `tangentSpaceOf J := ker J.mulVecLin`, `normalSpaceOf J := range Jᵀ.mulVecLin`, `FullRowRank J := Injective Jᵀ.mulVec`; `normalSpaceOf_eq_orthogonalSubmodule_tangent` (normal space = dotProduct annihilator of the tangent space).
- `structure CompatibleAnalyticLCIAtlas (r) (S : Set (Fin d → ℝ))`: open cover `V i`, analytic local defining maps `G i : ℝ^d → ℝ^r` with Jacobian fields `J i` (`HasFDerivAt`), `zero_iff` (each chart cuts out `S`), `fullRank` on `S`, and ONE ambient tangent field `tangent : ℝ^d → Submodule ℝ ℝ^d` with `tangent_eq : tangent s = tangentSpaceOf (J i s)` on every chart (compatibility); `normal := orthogonalSubmodule ∘ tangent`; `normal_eq_chart`, `normal_mem_iff_exists_multiplier` (`n ∈ normal s ↔ ∃ y, n = (J i s)ᵀ y`).
- `tangentSpaceOf_eq_of_eventually_zeroSet_eq`: two defining systems with the same zero set near `s` have the same tangent space (so `tangent` is well defined; proved by the local IFT, no partition of unity).
- `structure NormalTubularChart (N : ℝ^d → Submodule ℝ ℝ^d) (S)`: radius `eps`, open tube `U = {s + n : s ∈ S, n ∈ N s, ‖n‖ < eps}`, base-point coordinate `proj` with `x = proj x + (x − proj x)`, `x − proj x ∈ N (proj x)`, uniqueness of the decomposition inside radius `eps`, `proj` smooth on the tube; `AnalyticNormalTubularChart` adds `AnalyticAt ℝ proj`.
- Existence theorems: `exists_analyticNormalTubularChart_of_atlas (hS : IsCompact S) (A : CompatibleAnalyticLCIAtlas r S) : Nonempty (AnalyticNormalTubularChart A.normal S)`; the smooth projection; level-set and polynomial corollaries; chart-local: `stratum_analyticTubularChart m k ε` (a coordinate subspace `{u = 0} ⊆ ℝ^{m+k}` is an analytic tube at every radius).
- Chart-local normal derivatives on `(Fin m → ℝ) × (Fin k → ℝ)`: `normalDir`, `normalPDeriv j g p := fderiv ℝ g p (0, e_j)`, `normalDeriv γ g` (iterated over the multi-index), `normalCoeff F γ v := normalDeriv γ F (v, 0)` (no `1/γ!`), analyticity in `v` for analytic `F` (`analyticAt_normalCoeff`), `normalCoeff_zero_of_vanishing`, `normalCoeff_single_eq_mixedPDeriv`.

### B. `timaeus-research/grammar` (Mathlib v4.33.1), the geometric bridge CVII–CXIII, CXXXVI (all conditional on a certified chart presentation)
- `normalJet F r := iteratedFDeriv ℝ r F 0 : JetForm E r` (continuous `r`-linear form), `homogeneousTaylor F r u := D^rF(0)[u,…,u]/r!`; **fibre-linear covariance** `normalJet_comp_linear : D^r(F∘L)(0) = D^rF(0) ∘ (L,…,L)` for a continuous linear `L : E →L E` and its parametrised version `normalJet_comp_linear_family`.
- `momentFunctional η hr : JetForm E r →L ℝ`, `A ↦ ∫ A(u,…,u) dη`, norm `≤ ∫‖u‖^r dη`; the moment–jet pairing is invariant under a linear change of fibre variable (pull the form back, push the measure forward); `moment_contraction : (1/r!)⟨Moment_{η,r}, D^rF(0)⟩ = ∫ p_r(u,…,u) dη` for an analytic `F`.
- `dressedMeasure η_N = u^h e^{−βNu^{2k}} du` on the normal box; `dataBoxIntegral_eq_integral_dressed`; the chart integral as a Taylor–moment series (CXII).
- `structure LocalisationData U` (resolved measure `μ`, phase `K`, observable, level `δ`); `structure ChartPresentation D ρ K n β`: compact base `K` with finite `ν`, normal box `(0,b]^{n+1}`, measurable chart map `Φ : K × ℝ^{n+1} → U`, density factor `c ≥ 0`, tangential datum `x : C(K, DataSpace)`, and three certificates — measure transport `((ν ⊗ box).withDensity (u^h c)).map Φ = (μ|sublevel).withDensity ρ`, phase normal form `K(Φ(v,u)) = β u^{2k}` a.e., amplitude `evalF (η_x(v)) u = c(v,u) · F(Φ(v,u))` a.e., zero phase datum; `AdaptedStrataData` (finitely many presentations summing to the sublevel set); the conditional geometric main theorem `AdaptedStrataData.cutoffExpansion` (CXIII).
- CXXXVI: the tangential/normal splitting of the weighted box measure along `piEquivPiSubtypeProd`, the monomial phase depending only on normal coordinates, tangential weights integrating to explicit constants.
- Non-claims currently recorded: global tubular neighbourhoods; canonical normal derivatives beyond fibre-linear covariance; an asymptotic ordering by normal Taylor degree; the certified presentation is a hypothesis.

### C. Mathlib (v4.33.1) inventory relevant here
HAS: `IsManifold`, `ChartedSpace`, `ModelWithCorners`; `Diffeomorph`, `PartialDiffeomorph`, `IsLocalDiffeomorph`; **immersions with normal-form charts** (`IsImmersionAt I J n f x`: charts in which `f` looks like `u ↦ (u, 0)` w.r.t. `equiv : E × complement ≃L E''`, `writtenInCharts`), `IsSubmersionAt` likewise, `IsSmoothEmbedding`, Whitney embedding; `TangentBundle`, `mfderiv`; `ContMDiffVectorBundle` for `Hom`, `pullback`, `prod`, trivial bundles; local frames (`IsLocalFrameOn`), the tensoriality criterion (`TensorialAt.mkHom`), the bundle of continuous alternating maps; smooth partitions of unity (`SmoothPartitionOfUnity`); Faà di Bruno (`HasFTaylorSeriesUpToOn.comp`, `compAlongOrderedFinpartition`, `taylorComp_*`); `iteratedFDeriv_comp_right` (composition with linear maps); `Real` analytic inverse function theorem (used by StrucDual).
LACKS: quotient vector bundles / the normal bundle `TM|_X / TX` of a submanifold; symmetric-power bundles `Sym^r` (only the algebraic `TensorPower/Symmetric`); the tubular neighbourhood theorem on manifolds; densities and integration on manifolds (`Geometry/Manifold` has no `MeasureTheory` beyond Riemannian basics); the conormal splitting for transverse divisors.

## Formulations we see
(A) **Bundle-level on Mathlib manifolds**: define `NX` (as a quotient or via immersion complements), `N*X`, its splitting for transverse divisors, `Sym^r N*X` (or use `r`-linear forms on `NX` instead of `Sym^r`), a tubular neighbourhood as a hypothesis (`Φ : NX ⊇ 𝒩 → M` diffeomorphism onto a neighbourhood, identity on the zero section), `D^r_⊥ F` as a section, moment tensors as sections of the dual, densities and `τ_*`. Faithful to the text but most of the infrastructure is missing from Mathlib; likely a multi-month library project.
(B) **Local model with transformation laws**: work on `(v,u) ∈ ℝ^m × ℝ^k` with the stratum `{u = 0}`; a change of fibre frame `u' = g(v)·u` (diagonal units, the normal-crossing case) or `u' = A(v)u` with `A(v)` invertible, or a general diffeomorphism preserving `{u=0}` with linear part along the zero section; prove that the normal jets `normalCoeff F γ v / γ!` (StrucDual) / `normalJet` (grammar) transform tensorially by the linear part (this IS `lem:normal_deriv` and the "non-linear changes introduce lower-order terms" caveat: for a general diffeomorphism the leading nonvanishing jet is intrinsic, the full jet is not), and that the moment functional transforms contragrediently so `⟨D^r_⊥ F, M_r⟩` is invariant (this IS the content of `subsec:moment_tensors`); `τ_*` is Fubini (already CXXXVI/CXII).
(C) **Ambient-invariant ("embedded coordinate-free") formulation on top of StrucDual**: `S ⊆ ℝ^d` with a compatible analytic LCI atlas; `N_s := A.normal s ⊆ ℝ^d` is an honest subspace (the paper's own remark embeds the resolved space analytically); the tubular map is literally `(s, n) ↦ s + n` on `{(s,n) : n ∈ N_s}` (a `NormalTubularChart`); the normal `r`-th differential at `s` is the `r`-th Fréchet derivative of `n ↦ F(s + n)` restricted to `N_s` — canonical, no choice of fibre coordinates; the conormal lines `L_i(s) = span(∇u_i(s))` for a transverse system of divisors are independent of the choice of defining equations because `∇u'_i = g ∇u_i` on `S` (provable from `zero_iff`/compatibility); the moment tensor at `s` is the moment functional of the fibre measure on `N_s`; the pairing is invariant by construction; `eq:per_stratum_expansion_coordfree` becomes an identity of integrals over `S` with the fibre integrals over `N_s ∩ tube`. This gives the coordinate-free statements as theorems about subspaces of `ℝ^d`, dottable against the paper's text if the mirror states the embedded convention.

## Questions
1. Which formulation should we pursue, and why, given the Mathlib inventory? If (C), how do we handle the two Mathlib pins (strucdual at v4.29.0, grammar at v4.33.1): depend on strucdual as a lake package (bump it to v4.33.1 first?), port the ~17 Geometry files into grammar, or state the grammar side against an abstract interface (`NormalTubularChart`-shaped structure) and connect later?
2. What is the exact list of statements that would make `lem:normal_deriv`, `defn:normal_diff`, `eq:decomp_nx`, `eq:decomp_sym_nx`, `eq:pushforward_char`/`eq:pushforward_local`, `eq:dressed_moment`, `eq:tubular_expansion`, `eq:moment_tensor_defn`, `eq:per_stratum_expansion_coordfree` and `rem:reduce_to_box` honestly dottable? For each, say what the Lean statement would be, what it does NOT capture (e.g. `Sym^r` replaced by `r`-linear forms; global sections replaced by pointwise statements plus compatibility), and whether the mirror needs an "embedded convention" sentence.
3. Traps you foresee (universes; `Fin d → ℝ` vs `EuclideanSpace`; `Submodule`-valued fields with no regularity; analyticity vs smoothness; the `1/γ!` conventions; two-sided intervals `(−b,b)` vs the positive box `(0,b]` and `rem:parity`; the cutoff `χ`; the "absorb the unit `ε`" step in `K_I = u^{2k}`; densities vs measures).
4. A ranked programme of ≤ 8 units with precise Lean-level statements, Mathlib inputs (names where confident), non-claims, and a stop rule. Which unit is the first honest dot?

### Paper text: subsec:normal_crossing
\subsection{Normal crossing divisors and normal bundles}\label{subsec:normal_crossing}

A canonical splitting of the conormal bundle of strata $S_I$ of the exceptional divisor underlies the coordinate-free formulation of the per-stratum expansion in \cref{subsec:moment_tensors}; it ensures that the normal Taylor coefficients of the observable are well-defined global sections.

Let $M$ be a smooth manifold and $X$ a submanifold. There is a short exact sequence
\begin{equation}\label{eq:conormal_sequence}
\xymatrix{
0 \ar[r] & TX \ar[r] & TM|_X \ar[r] & NX \ar[r] & 0
}
\end{equation}
of vector bundles on $X$ where $NX$ denotes the normal bundle. It is well-known that there is a natural splitting of the dual bundle $N^*X$ in the case where $X$ is defined by the transverse intersection of smooth divisors, which is the main case of interest in this paper. Let $Y_i$ be such divisors, and suppose $X = \bigcap_{i=1}^k Y_i$. In our application, $M$ is the resolved space $U$, the divisors $Y_i$ are the irreducible components $E_i$ of the exceptional divisor, and $X = E_I = \bigcap_{i \in I} E_i$ for a subset $I \subseteq \{1,\ldots,r\}$; the stratum $S_I \subseteq E_I$ is the open subset where no additional components meet.

In a neighbourhood of $p \in X$ choose defining equations $u_1, \ldots, u_k$ for $Y_1,\ldots,Y_k$ respectively, so that $X$ is locally the simultaneous vanishing locus of $u_1, \ldots, u_k$. Then
\[
T_p X = \bigcap_{i=1}^k \ker( du_i )_p
\]
and hence using the dual of \eqref{eq:conormal_sequence}, $N^*_p X$ is spanned by $(du_1)_p, \ldots, (du_k)_p$. If we choose different defining equations $u'_i$ then $du_i$ and $du'_i$ are related by an invertible smooth function in a neighbourhood of $p$, and so span the same line bundle $\mathcal{L}_i \subseteq N^*X$. It follows that there is a canonical isomorphism
\begin{equation}\label{eq:decomp_nx}
\xymatrix{
\bigoplus_{i=1}^k \mathcal{L}_i \ar[r]^-{\cong} & N^*X
}\,.
\end{equation}
In particular, the $r$-th symmetric power of the conormal bundle decomposes as
\begin{equation}\label{eq:decomp_sym_nx}
\operatorname{Sym}^r(N^*X) \cong \bigoplus_{|b| = r} \bigotimes_{i=1}^k \operatorname{Sym}^{b_i}( \mathcal{L}_i )
\end{equation}
where $b \in \mathbb{N}^k$ is a multi-index and $|b| = b_1 + \cdots + b_k$.

The right-hand side may be thought of as ``polynomials in the $du_i$ with coefficients in smooth functions on $X$''. However, for an arbitrary smooth function $F$ on $M$, taking normal partial derivatives directly in local coordinates is not coordinate-independent: the derivatives depend on the choice of complementary coordinates along $X$, and non-linear changes of defining equations introduce lower-order derivative terms.

To obtain globally well-defined Taylor coefficients, one must pull functions back to the normal bundle via a tubular neighbourhood. On the normal bundle itself, the situation is rigidly structured: because transition functions between local frames of a vector bundle are strictly linear on fibres, the fibrewise Taylor expansion of a function defined on the normal bundle produces globally well-defined tensors in the precise sense of the next lemma.

\begin{lem}\label{lem:normal_deriv} Let $X = Y_1 \cap \cdots \cap Y_k$ be a transverse intersection of smooth divisors in $M$, with conormal splitting $N^*X \cong \bigoplus_{i=1}^k \mathcal{L}_i$ as in \eqref{eq:decomp_nx}. Let $\tilde{F}$ be a smooth function defined on the normal bundle $NX$ (for instance, in a neighbourhood of the zero section). Let $u_1, \ldots, u_k$ be local linear fibre coordinates on $NX$ corresponding to local frames of $\mathcal{L}_i$. For a multi-index $b \in \mathbb{N}^k$, the expression
\[
D_b(\tilde{F}) = \frac{1}{b_1! \cdots b_k!} \frac{\partial^{|b|} \tilde{F}}{\partial u_1^{b_1} \cdots \partial u_k^{b_k}} \bigg|_{u=0} (du_1|_X)^{\otimes b_1} \otimes \cdots \otimes (du_k|_X)^{\otimes b_k}
\]
is independent of the choice of linear fibre coordinates and defines a global section of $\bigotimes_{i=1}^k \operatorname{Sym}^{b_i}(\mathcal{L}_i)$ on $X$.
\end{lem}

\begin{proof}
We must check that the expression is independent of the choice of local fibre frame. It suffices to treat each factor separately. Since the transition functions of a vector bundle are strictly linear on fibres, a change of local linear frame takes the form $u'_i = g_i \cdot u_i$ where $g_i$ is a smooth nonvanishing function of the base point alone, independent of the fibre coordinates. Moreover, partial derivatives along the fibres of a vector bundle are canonically defined independently of any choice of base coordinates. Consequently $\frac{\partial^{b_i}}{\partial (u'_i)^{b_i}} = g_i^{-b_i} \frac{\partial^{b_i}}{\partial u_i^{b_i}}$, so on the zero section $\frac{\partial^{b_i} \tilde{F}}{\partial (u'_i)^{b_i}}|_{u=0} = g_i(p)^{-b_i} \frac{\partial^{b_i} \tilde{F}}{\partial u_i^{b_i}}|_{u=0}$. Meanwhile $du'_i|_X = g_i|_X \cdot du_i|_X$, so $(du'_i|_X)^{\otimes b_i} = g_i(p)^{b_i} (du_i|_X)^{\otimes b_i}$. The factors of $g_i^{\pm b_i}$ cancel.
\end{proof}

To apply this to an observable $F \in C^\infty(M)$, we choose a tubular neighbourhood $\Phi \colon NX \to M$ mapping the zero section to $X$ (as discussed in \cref{subsec:tubular_nbhd}), and define the normal derivatives of $F$ by applying the lemma to the pullback $\tilde{F} = F \circ \Phi$. In algebraic geometry, the coordinate-independence of leading derivatives is usually understood via the canonical isomorphism $\mathscr{I}^r/\mathscr{I}^{r+1} \cong \operatorname{Sym}^r(\mathscr{I}/\mathscr{I}^2)$ for regular embeddings \citep[\S B.7]{fulton1998intersection}, where $\mathscr{I}$ is the ideal sheaf of $X$. However, since this canonical algebraic fact only applies to functions $F \in \mathscr{I}^r$ vanishing to order $r-1$ (for which the non-linear derivative shift terms naturally vanish), taking the full normal Taylor expansion of an arbitrary smooth function necessitates the geometric choice of $\Phi$.

\begin{defn}\label{defn:normal_diff} Given a tubular neighbourhood $\Phi \colon NX \to M$, we write
\[
D^r_{\perp}(F) = \sum_{|b| = r} D_b(F \circ \Phi) \in \Gamma\big(X, \operatorname{Sym}^r(N^*X)\big)
\]
and call this the \emph{normal $r$-th differential} of $F$ with respect to $\Phi$.
\end{defn}

The normal bundle of $S_I$ is trivial if we can find defining equations for the $E_i$ with $i \in I$ which work everywhere on the stratum \citep[\S 2.3 Ex. 20]{guillemindifferential}, and in this case we have well-defined global normal coordinates. To turn the tensor $D^r_{\perp}(F)$ into a scalar that can be integrated along $X$, we pair it with a section of the dual $\operatorname{Sym}^r(NX)$; as we explain in \cref{subsec:tubular_nbhd}, such sections arise naturally from the fibre moment integrals of the posterior.


### Paper text: subsec:tubular_nbhd
\subsection{Tubular neighbourhoods and integration along fibres}\label{subsec:tubular_nbhd}

Tubular neighbourhoods separate tangential and normal variables without a metric, reducing the per-stratum integral to an outer integral over $S_I$ and inner integrals in the normal fibres (\cref{subsec:per_stratum_decomp}; see \cref{fig:tubular_nbhd}).

[Lean remark omitted]

[figure omitted]



To express the coefficients of the asymptotic expansion in coordinate-free form, we replace a neighbourhood of each stratum with a tubular neighbourhood, and use the pushforward of densities (integration along fibres) to write the coefficients as integrals over the strata. To avoid orientation issues we work throughout with smooth densities; for background see \citet[\S 16]{lee2012smooth}.

Let $M$ be a smooth manifold, $X \subset M$ a smooth submanifold, and let $|\mu|$ be a smooth positive density on an open neighbourhood $V$ of $X$. A \emph{tubular neighbourhood} of $X$ is a smooth map $\Phi: NX \to M$ from the total space of the normal bundle $\tau: NX \to X$, restricting to the inclusion on the zero section, such that $\Phi$ is a diffeomorphism from an open neighbourhood of the zero section in $NX$ onto $V$. By the change of variables formula for densities,
\begin{equation}\label{eq:tubular_cov}
\int_V F\, |\mu| = \int_{\Phi^{-1}(V)} (F \circ \Phi)\, \Phi^*|\mu|\,.
\end{equation}
We may always take $\Phi^{-1}(V)$ to be a bounded disk bundle over $X$; the asymptotic exponents and their multiplicities are independent of this choice (\cref{rem:cutoff_correct}).

\begin{remark}[Analyticity of the tubular neighbourhood]\label{rem:analytic_tubular}
The regularity of $\Phi$ is load-bearing. The observable and the density factor are Taylor-expanded in the normal variables \emph{through} $\Phi$, and the summability of the resulting expansion (\cref{thm:TaylorTree}) rests on Cauchy estimates which require the pulled-back integrand to be real analytic in the normal variables, with a holomorphic extension of uniform radius on compact pieces of the stratum. This holds only if $\Phi$ is itself real-analytic: the classical tubular neighbourhood theorem in the smooth category \citep[\S 4.5--4.6]{hirsch2012differential} produces a merely smooth $\Phi$, and composing an analytic function with a smooth $\Phi$ destroys the analyticity that the Cauchy estimates consume. Real-analytic tubular neighbourhoods do exist, but this is a genuinely stronger theorem: analytic partitions of unity are unavailable (cf.\ \cref{rem:pou_analyticity}), so the standard gluing construction fails, and one instead embeds the real-analytic resolved space analytically \citep{grauert1958analytische}, pulls back an analytic Riemannian metric, and takes the geodesic exponential map on the normal bundle, which is invertible with analytic inverse by the analytic inverse function theorem. When the stratum is globally cut out by defining equations $G = 0$ with full-row-rank Jacobian $J$ (the trivial-normal-bundle situation of the preceding discussion), the tube can instead be produced directly, without a metric, by applying the analytic inverse function theorem to the multiplier system $\Lambda(p, y) = (G(p),\, p + J(p)^{\mathsf T} y)$. This latter statement --- a compact level set $S = G^{-1}(0)$ with full-row-rank Jacobian admits a tubular neighbourhood whose tubular coordinates are real-analytic whenever $G$ is --- has been formally verified in Lean~4, together with its smooth counterpart and a polynomial form in which the analyticity hypotheses are discharged automatically for compact nonsingular algebraic complete intersections. Beyond the globally-cut-out case, the embedded form with only \emph{local} defining equations --- the situation of a general stratum after embedding, with chart-independence of the tangent spaces proven rather than assumed, and no partition of unity anywhere in the construction --- is also formally verified. The chart-local situation of the present section is also verified directly: in an adapted chart a normal crossing stratum is a coordinate subspace, which is an analytic tube at every radius with no inverse function theorem and no compactness. (The formalisation records pointwise real-analyticity of the tubular coordinates on the tube; the holomorphic extension of uniform radius on compact pieces used in the Cauchy estimates then follows by standard compactness arguments and is not itself formalised.)
\end{remark}

Since the bundle projection $\tau: NX \to X$ is a surjective submersion, there is a canonical, metric-free \emph{pushforward} on densities \citep[\S 16]{lee2012smooth}: for any density $|\omega|$ on $NX$ with fibrewise compact support, its pushforward $\tau_*|\omega|$ is the unique density on $X$ satisfying
\begin{equation}\label{eq:pushforward_char}
\int_X f\,(\tau_*|\omega|) = \int_{NX} (f \circ \tau)\, |\omega| \qquad \text{for all } f \in C_c^\infty(X)\,.
\end{equation}
Locally, choosing coordinates $x = (x_1,\ldots,x_{\dim X})$ on $X$ and letting $u = (u_1,\ldots,u_k)$ be linear fibre coordinates induced by a local frame, the pulled-back density takes the form $\Phi^*|\mu| = g(x,u)\, |du|\, |dx|$ with $g > 0$ smooth. The pushforward then simply integrates out the normal variables:
\begin{equation}\label{eq:pushforward_local}
\tau_*\big((F \circ \Phi)\, \Phi^*|\mu|\big) = \bigg(\int_{D_x} (F \circ \Phi)(x,u)\, g(x,u)\, du\bigg) |dx|\,,
\end{equation}
where $D_x = \Phi^{-1}(V) \cap \tau^{-1}(x)$ is the bounded fibre over $x$. This separates the normal variables $u$ from the tangential variables $x$ without requiring a Riemannian metric.

\paragraph{Application to SLT integrals.}
In our setting, $M = U_{\R}$ is the resolved space, $X = S_{I,\R}$ is a real stratum, and the integrand is $(\phi \circ \pi)\, e^{-n(K \circ \pi)}\, \pi^*(\varphi\, |dw|)$. The resolution puts the Boltzmann weight and the Jacobian factor into a known monomial form: in local coordinates $(v, u)$ adapted to the stratum, where $v$ runs along $S_I$ and $u = (u_i)_{i \in I}$ are normal coordinates, we have $K \circ \pi = \prod_{i \in I} u_i^{2k_i} = u^{2k_I}$ and $|\det D\pi(v,u)| = b(v,u)\prod_{i \in I} |u_i|^{h_i}$ with $b > 0$ smooth (\cref{section:res_sing}). The observable $\phi \circ \pi$, by contrast, is simply an analytic function of $(v, u)$ which we do \emph{not} assume to be monomialised. This is by design: we wish to treat \emph{all} observables simultaneously using a single resolution adapted to the KL divergence $K$. Since the resolution cannot be tailored to each observable individually, the vanishing behaviour of $\phi \circ \pi$ along the exceptional divisor is read off from its Taylor expansion in the normal directions rather than from a monomial normal form.

Absorbing the prior and the Jacobian factor $b$ into a positive smooth density $|\mu_0| = b(v,u)\, (\varphi \circ \pi)\, |dv\, du|$, the integrand near $S_I$ takes the form
\[
(\phi \circ \pi)(v, u) \cdot |u|^{h_I} \cdot e^{-n u^{2k_I}} \cdot |\mu_0|
\]
where $u^{2k_I} = \prod_{i \in I} u_i^{2k_i}$ and $|u|^{h_I} = \prod_{i \in I} |u_i|^{h_i}$ are multi-index shorthands.

\paragraph{Normal Taylor expansion and the canonical pairing.}
We now expand $(\phi \circ \pi)(v, u)$ in a Taylor series in the normal variable $u$, keeping the tangential coordinate $v$ as a parameter:
\[
(\phi \circ \pi)(v, u) = \sum_{|\gamma| \le N} \frac{1}{\gamma!}\, D^\gamma_\perp(\phi \circ \pi)(v)\; u^\gamma \;+\; R_N(v, u)\,.
\]
Since the tubular neighbourhood identifies a neighbourhood of $S_I$ in $U$ with a neighbourhood of the zero section in $NS_I$, the function $(\phi \circ \pi)(v,u)$ is a smooth function on the normal bundle. By \cref{lem:normal_deriv}, each Taylor coefficient $D^\gamma_\perp(\phi \circ \pi) \in \Gamma(S_I, \operatorname{Sym}^{|\gamma|}(N^*S_I))$ is a globally well-defined section of the conormal bundle, independent of the choice of local fibre coordinates. The zeroth-order term $D^0_\perp(\phi \circ \pi)(v) = (\phi \circ \pi)(v, 0)$ is the restriction of $\phi$ to the stratum. In an adapted chart, the analyticity of these coefficients in the tangential variable is formally verified.

Substituting this expansion into the fibre integral requires care: the density factor $c(v,u) = b(v,u)\,(\varphi \circ \pi)(v,u)$ appearing in $|\mu_0|$ also depends on the normal variable $u$ and cannot be pulled outside the $u$-integral. We likewise expand $c$ in a Taylor series in $u$:
\[
c(v, u) = \sum_{\delta} \frac{1}{\delta!}\, c_\delta(v)\; u^\delta\,, \qquad c_\delta(v) = \partial^\delta_u c(v, 0)\,.
\]
Since $c > 0$, the zeroth-order coefficient $c_0(v) = b(v,0)\,(\varphi \circ \pi)(v,0)$ is strictly positive on $S_I$. Substituting both Taylor expansions into the fibre integral and collecting monomials in $u$, we obtain the \emph{dressed normal moment}
\begin{equation}\label{eq:dressed_moment}
\widetilde{M}_\gamma(v, n) = \int_{D_v} u^\gamma\, |u|^{h_I}\, e^{-n u^{2k_I}}\, c(v,u)\, du = \sum_\delta \frac{c_\delta(v)}{\delta!}\, M_{\gamma + \delta}(n)\,,
\end{equation}
where $M_\alpha(n) = \int u^{\alpha}\, |u|^{h_I}\, e^{-n u^{2k_I}}\, du$ is the \emph{bare normal moment} evaluated in \cref{subsec:standard_form}. The first expression shows that $\widetilde{M}_\gamma$ is a convergent fibre integral; the second is its Taylor expansion in the density factor $c$. (The choice of cutoff $b > 0$ does not affect the asymptotic exponents or their multiplicities, though it enters the coefficients; see \cref{rem:cutoff_correct}.) The per-stratum contribution then admits the asymptotic expansion
\begin{equation}\label{eq:tubular_expansion}
\mathcal{Z}_n[\phi; I] \sim \sum_\gamma \frac{1}{\gamma!} \int_{S_I} D^\gamma_\perp(\phi \circ \pi)(v) \; \widetilde{M}_\gamma(v, n) \; |dv|\,;
\end{equation}

the justification that the Taylor remainder is asymptotically negligible is given in the proof of \cref{thm:TaylorTree}.
The leading $n$-dependence of $\widetilde{M}_\gamma$ is captured by the $\delta = 0$ term. Increasing $\delta_i$ for a coordinate $i$ that achieves the minimum $\lambda_\gamma = (h_i + \gamma_i + 1)/(2k_i)$ produces a strictly larger exponent $\lambda_{\gamma+\delta} > \lambda_\gamma$ and hence a subleading contribution. Non-minimizing coordinates may contribute at the same leading order, but these contributions are already accounted for in the convergent fibre integral \eqref{eq:dressed_moment}. The upshot is:
\[
\widetilde{M}_\gamma(v, n) = c_0(v)\, M_\gamma(n) \;+\; \text{(subleading in $n$)}\,,
\]
so the bare moments $M_\gamma(n)$ capture the leading $n$-dependence at each order $\gamma$, and the density corrections from the $u$-dependence of $c$ in the minimizing coordinates are genuinely subleading. The coordinate-free formulation of the expansion \eqref{eq:tubular_expansion}, which ensures that the sum over $\gamma$ yields a well-defined scalar density on $S_I$, requires \emph{moment tensors} valued in the symmetric powers of the normal bundle; this is the subject of \cref{subsec:moment_tensors}. In words: \emph{expectation values probe the exceptional divisor by pairing conormal derivatives of the observable with dressed normal moments of the posterior}.

\begin{remark}[Parity]\label{rem:parity}
The domain $D_v$ depends on whether the exceptional divisors corresponding to the normal coordinates $u_i$ resolve boundaries of the parameter space $W$ or lie in its interior. If a normal coordinate $u_i$ resolves an interior component, it is integrated over a symmetric interval $(-\varepsilon, \varepsilon)$, and by symmetry the normal moments $M_\gamma$ vanish whenever the exponent $h_i + \gamma_i$ is odd. This parity effect causes certain subleading poles to vanish. If $u_i$ resolves a boundary, it is integrated over a half-space $[0,\varepsilon)$ and all degrees may contribute.
\end{remark}


### Paper text: subsec:moment_tensors
\subsection{Moment tensors and coordinate-free contraction}\label{subsec:moment_tensors}

This subsection promotes the dressed moments of \cref{subsec:tubular_nbhd} to coordinate-free objects, ensuring that the per-stratum expansion \eqref{eq:tubular_expansion} is independent of the choice of local defining equations.

The dressed moments $\widetilde{M}_\gamma(v,n)$ appearing in \eqref{eq:tubular_expansion} depend on the choice of local defining equations $u_i$ for the components of the exceptional divisor: changing these equations rescales $u_i$ and hence the monomial $u^\gamma$ inside the bare moments. The intrinsic objects are \emph{moment tensors} valued in symmetric powers of the normal bundle, whose contraction with the conormal derivatives $D^\gamma_\perp(\phi \circ \pi)$ produces a well-defined scalar density on the stratum.

Let $\Phi: NS_I \supset \mathcal{N} \to U$ be a tubular neighbourhood of $S_I$
contained in $V_I$, and write $\tau: NS_I \to S_I$ for the bundle projection.
Define the \emph{pulled-back phase}
\begin{equation}\label{eq:pulled_back_phase}
K_I := (K\circ\pi)\circ \Phi \in C^\infty(\mathcal{N})\,.
\end{equation}
Let $\chi$ be a smooth cutoff function with compact support in the tubular neighbourhood; a specific choice via a partition of unity adapted to the stratification is made in \cref{lem:adapted_pou}. As in \cref{subsec:tubular_nbhd}, write $|\det D\pi(v,u)| = b(v,u)\prod_{i \in I} |u_i|^{h_i}$ with $b > 0$ smooth. We define the \emph{smooth density factor}
\[
|\mu_I|
:=
\Phi^*\big(\chi\,(\varphi\circ\pi)\, b\,|du\,dv|\big),
\]
a smooth positive density on $\mathcal{N} \subset NS_I$ with fibrewise compact support; note that the singular monomial weight $|u|^{h_I} = \prod_{i \in I} |u_i|^{h_i}$ is kept separate. The disintegration of $|\mu_I|$ over $\tau$ factorises this density into conditional fibre densities and a marginal on the base (cf.\ the pushforward construction of \eqref{eq:pushforward_local} and \citet[\S 452]{fremlin2006measure}):
\[
|\mu_I| = |\mu_I|_v \cdot \tau^*(\tau_*|\mu_I|)\,,
\]
where $|\mu_I|_v$ is the conditional fibre measure at $v \in S_I$ and $\tau_*|\mu_I|$ is the marginal density on $S_I$.

For each $r \ge 0$ define the \emph{$r$-th moment tensor}
$\mathsf{M}_{I,r}(n) \in \Gamma\!\big(S_I, \operatorname{Sym}^r(NS_I)\big)$ by the requirement that,
for every $v \in S_I$ and every $\alpha \in \operatorname{Sym}^r(N_v^*S_I)$,
\begin{equation}\label{eq:moment_tensor_defn}
\big\langle \alpha,\,\mathsf{M}_{I,r}(n)(v)\big\rangle
:=
\int_{D_v} \alpha(\xi^{\otimes r})\,
|u|^{h_I}\,
e^{-n\,K_I(\xi)}\,
|\mu_I|_v(\xi)\,,
\end{equation}
where $D_v = \mathcal{N}\cap \tau^{-1}(v)$ is the bounded fibre over $v$,
$|u|^{h_I} = \prod_{i \in I} |u_i|^{h_i}$ is the monomial weight from the Jacobian,
$\langle\cdot,\cdot\rangle$ denotes the natural pairing
$\operatorname{Sym}^r(N_v^*S_I) \times \operatorname{Sym}^r(N_vS_I) \to \mathbb{R}$,
and $\alpha(\xi^{\otimes r})$ evaluates the symmetric multilinear form $\alpha$ on $r$ copies of the
fibre vector $\xi \in N_vS_I$.

In local frames $(e_i)_{i\in I}$ of $NS_I$ adapted to the normal crossing divisor,
write $\xi = \sum_{i\in I} u_i e_i$ for the corresponding linear fibre coordinates.
By the normal crossings form of the resolution (\cref{section:res_sing}),
after absorbing the unit $\varepsilon$ in the normal directions one may choose the tubular chart
so that
\[
K_I(v,u) = (K\circ\pi\circ\Phi)(v,u) = \prod_{i\in I} u_i^{2k_i} = u^{2k_I}
\]
on $\mathcal{N}$. In such coordinates, \eqref{eq:moment_tensor_defn} reduces to the bare
normal moment integrals studied in \cref{subsec:standard_form}.

On the other hand, the normal $r$-th differential of the observable,
$D_\perp^r(\phi\circ\pi) \in \Gamma\!\big(S_I, \operatorname{Sym}^r(N^*S_I)\big)$,
is defined intrinsically as in \cref{defn:normal_diff}. Since $D_\perp^r(\phi \circ \pi)(v)$ is constant along the fibre over $v$, we may pull it outside the fibre integral in \eqref{eq:moment_tensor_defn}: contracting the moment tensor with the conormal derivative yields a scalar function
\[
\big\langle D_\perp^r(\phi\circ\pi),\,\mathsf{M}_{I,r}(n)\big\rangle : S_I \to \mathbb{R}\,.
\]
Consequently, the per-stratum contribution admits the coordinate-free expansion
\begin{equation}\label{eq:per_stratum_expansion_coordfree}
\mathcal{Z}_n[\phi;\,I]
\sim
\sum_{r \ge 0}\frac{1}{r!}\int_{S_I}
\big\langle D_\perp^r(\phi\circ\pi),\,\mathsf{M}_{I,r}(n)\big\rangle\;
\tau_*|\mu_I|\,.
\end{equation}
In local frames $(e_i = \partial/\partial u_i)_{i \in I}$ adapted to the normal crossings divisor, the integrand in \cref{eq:per_stratum_expansion_coordfree} reduces to a sum over multi-indices $\gamma$ with $|\gamma| = r$. Concretely, the cancellation of marginal and conditional in the disintegration gives
\[
\langle D^r_\perp(\phi \circ \pi), \mathsf{M}_{I,r}(n)\rangle\, \tau_*|\mu_I| = \sum_{|\gamma|=r} D^\gamma_\perp(\phi \circ \pi)(v)\, \widetilde{M}_\gamma(v,n)\, |dv|\,,
\]
recovering the dressed moment expansion \eqref{eq:tubular_expansion}. The $n$-dependence of each $\widetilde{M}_\gamma$ is governed by the bare moments $M_\gamma(n)$ of \cref{subsec:standard_form} via \eqref{eq:dressed_moment}.

\begin{remark}\label{rem:reduce_to_box}
Since $\chi$ has compact support in $U$, the support of $|\mu_I|$ is compact in $\mathcal N$, and hence its
projection $\tau(\supp|\mu_I|)\subset S_I$ is contained in some relatively compact open set $U_0 \subset S_I$.
Choose a local trivialisation $NS_I|_{U_0}\cong U_0\times\R^{|I|}$ with linear fibre coordinates
$u=(u_i)_{i\in I}$. Shrinking $U_0$ if necessary, there exists $b>0$ and a smooth cutoff
$\kappa\in C_c^\infty(\R^{|I|})$ with $\kappa\equiv 1$ on the fibrewise projection of $\supp|\mu_I|$ and
$\supp(\kappa)\subseteq \prod_{i\in I} I_i$, where $I_i=(-b,b)$ for interior components and
$I_i=[0,b)$ for boundary components (cf.\ \cref{rem:parity}).

Writing $|\mu_I|_v = g(v,u)\,|du|$ in these coordinates (with $g > 0$ smooth), we may therefore compute the fibre pairing
\eqref{eq:moment_tensor_defn} over the fixed box $\prod_{i\in I} I_i$:
\[
\big\langle \alpha,\,\mathsf{M}_{I,r}(n)(v)\big\rangle
=
\int_{\prod_{i\in I} I_i}
\alpha(u^{\otimes r})\,|u|^{h_I}\,e^{-n\,K_I(v,u)}\,\kappa(u)\,g(v,u)\,du.
\]
In the local normal form chart where $K_I(v,u)=u^{2k_I}$ (after absorbing the unit $\varepsilon$ as in
\cref{section:res_sing}), Taylor expanding the smooth factor $\kappa(u)\,g(v,u)$ in $u$ reduces these
fibre integrals to finite linear combinations (to any fixed asymptotic order) of the model moments
\eqref{eq:normal_moment_defn} on a box.
Different choices of $\kappa$ and $b$ affect coefficients but do not change the pole set or the resulting
asymptotic exponents; see \cref{rem:cutoff_correct}.

[Lean remark omitted]

\end{remark}
