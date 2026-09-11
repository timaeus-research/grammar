# Astra consult #65

## Verdict

**The bundle programme has delivered a useful, substantial layer. But the geometric interpretation needs tightening before calling it paper closure.**

The main distinction is:

> You have constructed a smooth bundle from a labelled, independently spanning family of covectors along a smooth map. You have not yet proved that this is the geometric normal bundle of an embedded zero locus.

That is a good intermediate theorem—not a defect in the construction. It becomes an over-claim when the headline silently supplies the missing geometry.

My recommendation is **D: a short, bounded fidelity pass**, including an interface repair and a conditional unit 14. Then return to the companion note. Do not begin an implicit-function-theorem campaign now.

This review is based on the supplied declarations and descriptions, not an independent inspection of the repositories or the paper’s precise convention for `eq:decomp_nx`.

---

## 1. Fidelity review

### 1(a). `LabelledDefiningEquations`: sufficient algebraic data, insufficient geometric data

The differential overlap law is exactly the law needed for the frame construction:

\[
du^j_\ell=a_\ell\,du^i_\ell,\qquad a_\ell\ne0.
\]

For this purpose, **you do not need to carry the multiplying functions themselves**. Their pointwise scalar values suffice for preservation of kernels and labelled gradient lines; smoothness of the resulting transitions comes from the smooth frame/coframe machinery.

But the displayed structure does **not** assert:

1. `u i l (emb x) = 0`;
2. that `emb` is injective, an immersion, or an embedding;
3. that its differential identifies \(T_xB\) with \(\bigcap_\ell\ker du^i_\ell\);
4. that the local image of `emb` is the corresponding zero locus.

Consequently, calling `emb` an **embedding** in CLXXVI is presently false as a description of its hypotheses. Calling the equations **defining equations of that base** is also unsupported.

A simple diagnostic: take `emb` constant and take independent linear coordinate functions as the `u`s. The displayed interface can hold over a positive-dimensional \(B\). The resulting kernel field is plainly not established as the tangent bundle of that parametrised base.

**Required correction:** describe the current core as something like:

> Labelled independent differential data along a smooth map, with scalar overlap laws.

Retain the existing declaration name if renaming is disruptive, but put the limitation directly in its documentation. Add a geometric wrapper or adapter later.

For geometric normal-bundle identification, the essential extra assertion is the tangent-image equality
\[
\operatorname{range}(d\,\mathrm{emb}_x)
  =\bigcap_\ell\ker du^i_\ell.
\]
Together with the appropriate embedding hypotheses, this identifies the constructed orthogonal complement with the geometric normal space. Zero-set and unit-function hypotheses explain why the data arise from defining equations; they should not be silently inferred from the differential interface.

### A second issue: which labelled splitting?

**Diagonal transitions are the right descent theorem for the labelled lines you constructed.** They show that the gradient-frame coordinate lines agree on overlaps.

However, there are two potentially different decompositions here:

* the **gradient-line decomposition**
  \[
  N_x=\bigoplus_\ell \mathbb R\,\nabla u_\ell;
  \]
* the normal decomposition **dual to the equation-generated conormal decomposition**
  \[
  N_x^*=\bigoplus_\ell \mathbb R\,du_\ell.
  \]

These are not generally the same labelled decomposition under duality.

For example, with \(du_1=dx\) and \(du_2=dx+dy\), the gradient lines are
\[
\mathbb R(1,0),\quad \mathbb R(1,1),
\]
whereas the normal lines dual to the equation-labelled conormal summands are
\[
\mathbb R(1,-1),\quad \mathbb R(0,1).
\]

Thus:

* If `eq:decomp_nx` means the sum of metric normal lines to the labelled hypersurfaces, the gradient construction is appropriate.
* If it means the normal splitting dual to the defining conormal lines, you need the **dual frame of the differentials**, not merely their Riesz gradients.
* In orthogonal coordinate examples these distinctions disappear, so CLXXVIII does not test this issue.

**Bluntly:** “its dual splits the conormal bundle as in `eq:decomp_nx`” needs a convention check. Abstract dualisation gives a splitting, but not automatically the equation-generated labelled conormal splitting.

Also distinguish:

> “The atlas preserves labelled lines”

from

> “A direct-sum isomorphism of constructed line bundles has been formalised.”

The former is landed. The latter is not established by the displayed transition theorem alone.

### 1(b). `IsGlobalNormalSection`: yes, as a coordinate definition

**Yes.** A fibrewise symmetric continuous multilinear form whose coordinates are smooth in every smooth local frame is a standard, faithful coordinate definition of a smooth section of \(\operatorname{Sym}^r(N^*)\), over \(\mathbb R\) in your finite-dimensional setting.

An explicit Mathlib symmetric-power bundle is not necessary to justify that mathematical reading. The overlap law and `of_cover` are precisely the important checks.

Use this wording:

> A coordinate-based formalisation of smooth sections of the symmetric covariant-power bundle.

Do not say that you have constructed that bundle functor or proved equivalence with a separately existing section type.

Two qualifications matter:

* `pullForm_normalTaylorForm` establishes coordinate identification **for the chosen family \(\Phi\)**. It does not remove dependence on that family.
* The displayed global Taylor-section theorem is for a **normed-space base with the stated jointly smooth frame realisations**, not arbitrary manifold bases.

The second is an actual coverage boundary. The section predicate is manifold-general; the displayed theorem producing Taylor sections is not.

Also, \(C^\infty\) global sections are not analytic global sections. If the paper’s sentence requires analyticity rather than smoothness, the dot needs an additional qualification.

### 1(c). Headline and mirror-dot audit

| Claim or dot | Assessment |
|---|---|
| CLXXIV–V: smooth frame bundle, ambient realisation, smooth coframes | Sound at the stated abstraction level. |
| CLXXVI: “over an embedded base” | **Over-claimed.** The displayed hypothesis is only a smooth map. |
| CLXXVI: “tangent field” | Call it the **kernel field**, pending identification with the image of the manifold tangent bundle. |
| CLXXVI: canonical labelled lines | Sound **relative to the supplied labels and chosen metric**, for the gradient-line construction. Check the dual-splitting issue above. |
| `defn:normal_diff`: \(\Gamma(X,\operatorname{Sym}^rN^*X)\) | Acceptable as a coordinate-based reading, conditional on identifying the constructed \(N\) with the paper’s normal bundle. |
| `lem:normal_deriv`: global-section clause | Acceptable with the normed-base and regularity hypotheses exposed. `coordChange_single` supports label preservation, not by itself section smoothness. |
| Tubular-neighbourhood definition sentence | The cited identities certify decomposition and uniqueness for an existing StrucDual tube. **They do not themselves prove a smooth diffeomorphism of the constructed abstract bundle onto that tube.** Mark that distinction. |
| Adapted-coordinates sentence | Strong coordinate-model coverage. Do not infer the existence of adapted charts, or transport of the Euclidean additive normal tube through an arbitrary nonlinear chart. |
| CLXXVIII coordinate tube | An honest completed theorem. Its global, infinite-radius conclusion is special to this linear coordinate model. |

A nonlinear adapted chart need not preserve orthogonal normal spaces or ambient addition. Consequently, the coordinate result is not automatically a theorem about the ambient metric normal tube of a curved stratum.

---

## 2. General unit 14: land a conditional bridge

Choose **(i), with an explicit lifted-foot hypothesis**. Treat **(iii) as the endpoint of the existence programme** for now.

Do not undertake (ii) as a new graph campaign: the coordinate case already covers the main immediate use, and graph generalisation invites geometric work without resolving the abstract interface question.

### Recommended statement

Here is the mathematical contract; it is schematic, not proposed compiling Lean.

Let:

* \(A\) be the smooth normal-frame atlas over \(B\);
* \(U\subset E\) be the open domain of a supplied StrucDual tubular chart \(T\);
* \(\mathrm{emb}(B)=S\), with `emb` injective;
* the normal field of \(T\) at \(\mathrm{emb}(x)\) agree with \(N_x\);
* \(\Omega\subset\operatorname{TotalSpace}(A)\) be the **open certified admissible domain**, containing the zero section;
* \(P:U\to B\) be smooth, satisfying
  \[
  \mathrm{emb}(P(y))=T.\mathrm{proj}(y).
  \]

Assume the supplied tube identities and admissibility guarantees identify \(\Omega\) with the permitted normal displacements. Then
\[
\Psi:\Omega\longrightarrow U,\qquad
\Psi(x,v)=\mathrm{emb}(x)+A.\mathrm{realise}(x,v)
\]
is a \(C^\infty\) diffeomorphism.

Its inverse has base coordinate \(P(y)\) and fibre realisation
\[
y-\mathrm{emb}(P(y)).
\]

Prove inverse smoothness in frame coordinates using
\[
A.\mathrm{coframe}_i(P(y))
  \bigl(y-\mathrm{emb}(P(y))\bigr).
\]

This reuses exactly the machinery you have built.

A smooth ambient left inverse \(r\) of `emb`, defined near the zero section, supplies the lifted foot by
\[
P(y)=r(T.\mathrm{proj}(y)),
\]
with the relevant domain and smoothness conditions.

### What this does—and does not—close

It closes:

> Given a certified tube and a smooth identification of its foot with the manifold base, the frame-built bundle realises that tube diffeomorphically.

It does **not** prove existence of that smooth base identification, an embedded level-set manifold, or a tubular neighbourhood from the present `LabelledDefiningEquations` alone.

Do not take an arbitrary retraction \(r(y)\) as the inverse base coordinate. It is \(r(T.\mathrm{proj}(y))\) that is guaranteed to recover the certified foot.

---

## 3. Next direction: D, bounded to five units

The risks exposed above concern the meaning of already-dotted paper statements. Fix those before adding another major layer.

### Unit 1 — Hypothesis and claim ledger

Audit the coordinate-free and bundle headlines against actual theorem hypotheses.

Explicitly track:

* smooth map versus embedding;
* kernel field versus geometric tangent field;
* smooth versus analytic;
* coordinate model versus transported geometry;
* conditional construction versus existence.

**Deliverable:** corrected headlines, non-claims, and mirror-dot annotations.

**Stop rule:** documentation and theorem dependency inspection only; no new geometry.

### Unit 2 — Geometric identification adapter

Keep the current algebraic core. Add an interface recording the embedding and tangent-image hypotheses needed to interpret its bundle geometrically.

Prove the resulting normal-space identification, without constructing a level-set manifold.

**Stop rule:** accept tangent-image equality as a hypothesis if deriving it requires substantial manifold/IFT infrastructure. No unit 11A by stealth.

### Unit 3 — Resolve the labelled-splitting convention

Check the paper’s precise `eq:decomp_nx` convention.

Use a nonorthogonal two-equation example to distinguish gradient lines from the dual-to-conormal normal lines. Then either:

* certify that the current construction matches the paper; or
* provide the appropriate dual-frame construction and comparison at the frame level.

**Stop rule:** no general direct-sum or symmetric-power bundle library. If the paper-level identification remains unproved, downgrade the corresponding dot.

### Unit 4 — Conditional unit 14

Implement the lifted-foot theorem above, using the existing coframe and total-space smoothness APIs.

**Stop rule:** do not derive smoothness of the lifted foot from bare injectivity or bare smoothness of `emb`. If the bridge requires an unrelated infrastructure campaign, publish the precise contract and leave the theorem open.

### Unit 5 — Independent closure review

Have a reviewer check the revised claims and the two principal end-to-end routes:

1. coordinate stratum → normal bundle → coordinate tubular diffeomorphism;
2. chosen normal family → Taylor forms → coordinate-defined global section → contraction.

Record exactly which route reaches each paper clause.

**Stop rule:** a finite issue list, not an open-ended generalisation programme.

---

## After that

Return to **A, the companion note**, beginning with the sampling-identity gate from #62. Do not start B or C merely to make the geometry look more complete.

The present bundle work is already enough to support a strong, carefully qualified coordinate and chosen-normal-family account. The immediate priority is to ensure that **“constructed from differential data” is never silently promoted to “the geometric normal bundle of the paper’s stratum,”** and that **“diagonal gradient transitions” is not silently promoted to the wrong labelled dual decomposition**.
