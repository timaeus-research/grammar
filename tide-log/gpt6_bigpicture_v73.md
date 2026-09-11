## 1. Recommended next units

I would rank **(a), (b), (d), (c), (e)** by paper value, but implement a small part of (c)—the derivative formula—inside (a).

### 1. Local Jacobian density and tubular change of variables — highest priority

Put \(m=d-r\), \(R(z)=J(\operatorname{emb}z)^T\), and
\[
\Omega=\{(z,n):z\in W,\ \|R(z)n\|<\varepsilon\},\qquad
\psi(z,n)=\operatorname{emb}z+R(z)n.
\]
Use ambient coordinates \(z\in\mathbb R^m\), not a subtype, for the differentiation and integration theorem.

After fixing a **volume-preserving** linear identification \(L:\mathbb R^m\times\mathbb R^r\simeq_L\mathbb R^d\), define
\[
g(p)=\left|\det\bigl(D\psi(p)\circ L^{-1}\bigr)\right|.
\]

Deliver:

* `IsOpen Ω`, `InjOn ψ Ω`, and identification of `ψ '' Ω` with the tube whose foot lies in this graph patch;
* `∀ p ∈ Ω, 0 < g p`;
* `∀ p ∈ Ω, AnalyticAt ℝ g p`;
* for measurable \(B\subseteq\Omega\),
  \[
  \int_{\psi(B)}F(y)\,dy
  =\int_B g(p)F(\psi(p))\,dp.
  \]

This directly supports **eq:tubular_cov and the local density statement**.

**Important scope:** this computes the pullback of ambient Lebesgue measure. For \(d|\mu|=\rho(y)\,dy\), the density is
\[
g_\mu(p)=\rho(\psi(p))g(p).
\]
Positivity and analyticity require corresponding hypotheses on \(\rho\). Do not dot the arbitrary-\(|\mu|\) version using only the Lebesgue theorem.

### 2. Actual fibre integration of that density

Prove, under an explicit integrability hypothesis,
\[
\int_{\psi(\Omega)}F(y)\,dy
=\int_{z\in W}\int_{\|R(z)n\|<\varepsilon}
 F(\operatorname{emb}z+R(z)n)\,g(z,n)\,dn\,dz.
\]

Also prove the nonnegative `lintegral` version: it avoids unnecessary integrability assumptions and gives a good measure-level foundation.

Then identify the existing `fibreMeasure` construction with the pushforward of the **computed** pullback measure. This is the strongest next dot for the paper’s \(\tau_*|\omega|\), rather than another theorem taking the fibre density as input.

### 3. Bundle transport of the coefficient construction

Split this into two deliverables:

1. **Easy bridge:** instantiate every chosen-normal-family hypothesis with
   \[
   N_x=\operatorname{normal}(x),\qquad \Phi_x(v)=x+v,
   \]
   and identify these maps with restrictions of the global \(\Psi\).
2. **Genuine globalization:** prove that local vertical jets and moment tensors transform contragrediently under frame changes, so their pairing descends to a scalar—or a base density, depending on the integration convention—on `Stratum A`.

Target:
\[
c_k=\int_{\operatorname{Stratum}A}
 \sum_{\alpha\in I_k}
 \langle D_\perp^{q_\alpha}F,M_\alpha\rangle\,d\mu_X.
\]

The precise indices and constants should be inherited unchanged from CLXVI–CLXXII. A repackaging over `Stratum A` alone does **not** establish this coordinate-free formula: overlap compatibility and the base integration datum matter.

### 4. Density jets

First prove
\[
D\psi(z,n)(h,k)
 =D\operatorname{emb}(z)h+(DR(z)h)n+R(z)k.
\]
Consequently,
\[
g(z,0)=
\left|\det\bigl([D\operatorname{emb}(z),R(z)]\circ L^{-1}\bigr)\right|.
\]

Then expose vertical derivatives of \(g_\mu\) as the paper’s \(\partial^b g\) inputs. Analyticity gives local convergent Taylor expansions, **not automatically a common radius or uniform remainder over a noncompact patch**.

### 5. Resolved-space application — defer

Coordinate hyperplanes already have a linear model. The missing value is compatibility with the resolved-space atlas, exceptional divisor, densities, and resolution map—not another tubular theorem for a coordinate plane.

---

## 2. Cleanest handling of the \(E\to E\) restriction

Use **(i) with a canonical volume-preserving coordinate concatenation**, packaged once. Internally apply change of variables to
\[
f=\psi\circ L^{-1}:\mathbb R^d\to\mathbb R^d,
\qquad D=L(\Omega).
\]
Keep the public theorem in product coordinates; use product volume for Fubini.

This combines the useful parts of (i) and (ii), without forcing all subsequent statements into flattened coordinates.

* Obtain \(r\le d\) from full rank at a stratum point, using nonemptiness.
* Construct \(L\) from coordinate concatenation and \(m+r=d\).
* Prove `MeasurePreserving L volume volume` once.
* Avoid an arbitrary linear equivalence unless necessary. For arbitrary \(L\), if
  \[
  L_*(dp)=c_L^{-1}\,dy,
  \]
  the product-coordinate Jacobian is
  \[
  c_L\,|\det(D\psi\circ L^{-1})|.
  \]
  There is no intrinsic determinant of a map between two differently presented vector spaces without chosen volume normalizations.

**Declarations I am confident about:**

* `MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul`
* `MeasureTheory.integral_prod`
* `MeasureTheory.lintegral_prod`
* `MeasureTheory.Measure.prod`
* `MeasureTheory.MeasurePreserving`
* `ContinuousLinearMap.det`

From your checked inventory, also use:

* `MeasureTheory.Measure.addHaar_preimage_continuousLinearEquiv`
* `volume_preserving_piFinSuccAbove`
* `MeasurableEquiv.sumPiEquivProdPi`
* `Fin.appendEquiv`

I would verify the namespaces and signatures of the last three in the pinned checkout. I am **not** confident of an exact `MeasurableEquiv.piFinSumFin` name, nor of the exact determinant-analyticity and analytic-absolute-value convenience lemma names.

For analyticity, prove the determinant analytic, then use nonvanishing to make its sign locally constant; absolute value is analytic there.

---

## 3. What becomes reachable specifically from the global analytic tube?

Two distinct gains should be recorded.

### Global pullback and projection measure

Let \(\Omega\) be the global disk bundle and \(e:\Omega\simeq T.U\) the restricted tubular equivalence. Define
\[
\nu=(e^{-1})_*(dy|_{T.U}),\qquad \lambda=\tau_*\nu.
\]
Then
\[
\int_\Omega h(\tau p)\,d\nu(p)
=\int_{T.U}h(\operatorname{proj}_X y)\,dy
=\int_X h\,d\lambda
\]
for integrable pullbacks.

Lean sketch:
```lean
-- Use subtype source/target measures and the measurable equivalence
-- induced by the restricted tubular homeomorphism.
let ν := Measure.map e.symm volumeOnTube
let λ := Measure.map bundleProjection ν
-- Identify bundleProjection ∘ e.symm with liftedFoot.
-- Apply integral_map with its measurability/integrability hypotheses.
```

This dots the **global measure-theoretic meaning of integration along fibres**. It does not yet compute a density for \(\lambda\). Globality is essential here; analyticity is not.

### Global analytic vertical density jets

After units 1–3, the local analytic densities and their vertical jets can be glued, with the appropriate density transformation law, into global bundle-valued coefficient data. This is where **both globality and analyticity** add something beyond the earlier local tube: global coefficient sections with analytic local representatives and analytic normal expansions.

Do not claim a canonical global scalar \(g\): \(g\) depends on base and fibre coordinates.

---

## 4. Suggested HEADLINES non-claim

> Constructs a global real-analytic tubular equivalence for compact Euclidean strata admitting a compatible analytic LCI atlas. Does not yet compute the pulled-back ambient density, prove its fibre-integral disintegration, or globalize the coefficient formula with chart-independent density/moment data. Does not construct the resolved-space manifold and exceptional-divisor strata, establish their LCI/normal-bundle compatibility, or provide general manifold density integration.

Finally, qualify **“metric-free”**: the bundle presentation avoids choosing a global frame, but the supplied normal field, orthogonal splitting, and tube radius still use the ambient Euclidean inner product.
