## Recommendation

**Proceed with a partial-active chart model, keeping the phase unit tangential for E. Record the Jacobian orders explicitly. But make the first executable pilot the singleton-active model of the blow-up, not the entire water-filling generalisation.**

The shortest route to the paper theorem is:

> weighted chart cores → signed chart expansions → finite sum using the existing wedge change of variables.

Neither the honest projector space nor a quotient of the chart cubes is needed for that theorem. They are needed for the stronger claim that the resulting fields live intrinsically on the projective blow-up.

One qualification on this audit: **I can assess the obligations from the supplied declarations, but cannot call the revised table compile-checked.** The next gate should be an actual obligation-fixture module importing the landed modules and constructing the relevant data.

---

## 1. E0: accepted, with five corrections

### 1.1 The absolute Jacobian is always even

The table currently conflates the determinant and its absolute value:

\[
\det D\phi_\beta(y)=y_\beta^{d-1},
\qquad
|\det D\phi_\beta(y)|=|y_\beta|^{d-1}.
\]

* The **determinant** is even in \(y_\beta\) iff \(d\) is odd.
* The **absolute Jacobian** is even in \(y_\beta\) for every \(d\).
* On a reflected positive orthant, writing \(y=R_\sigma z\), \(z_i\ge0\),
  \[
  |\det D\phi_\beta(R_\sigma z)|=z_\beta^{d-1}.
  \]
  It is not generally equal to \(y_\beta^{d-1}\) in the original signed coordinates.

This matters directly to G’s reflection lemmas.

### 1.2 Tangential means independent of **all active coordinates**

For the recommended restricted model, require
\[
u(y)=u_0(y|_{A^c}).
\]

Then \(u\) is tangential to every stratum indexed by \(I\subseteq A\). A unit merely tangential to one chosen stratum does not automatically give a single model supporting the whole collar decomposition.

The cube unit satisfies this stronger condition for \(A=\{\beta\}\).

### 1.3 At a smaller stratum, there are tangential Jacobian factors too

For \(I\subseteq A\), the weight decomposes as
\[
\prod_{i\in A}|y_i|^{h_i}
=
\left(\prod_{j\in A\setminus I}|t_j|^{h_j}\right)
\left(\prod_{i\in I}|y_i|^{h_i}\right).
\]

Thus the proposed amplitude modification needs both:

* normal scaling factors \(\prod_{i\in I}\lambda_i^{h_i}\);
* active-tangential factors \(\prod_{j\in A\setminus I}|t_j|^{h_j}\), unless those are deliberately put in the base measure.

For the singleton blow-up pilot, \(I=A\), so the second product is empty. This is a substantial simplification.

### 1.4 Analytic composition is done in principle; the uniform series bridge is a separate obligation

Polynomial composition proves the required real analyticity. It does **not by itself** discharge a particular `UniformSeriesFamily` radius or one global holomorphic-polydisc hypothesis.

The E0 fixture should distinguish:

1. analytic pullback near the compact chart cube;
2. an appropriate holomorphic representative/packet;
3. a common collar level making the normalised series radii admissible.

The existing local bridge may handle all three, but they should not be collapsed into one “routine composition” row.

### 1.5 Blow-down properness is not inherited from `CoordModel.geometry`

The full affine chart map
\[
\phi_\beta:\mathbb R^d\to\mathbb R^d
\]
is not proper: its fibre over \(0\) contains the whole hyperplane \(y_\beta=0\).

Therefore one cannot replace `π := id` by `π := φ β` in the displayed full-space `ResolvedGeometry` and expect the properness field to go through.

This is another reason to keep:

* a coordinate chart certificate with `π := id`;
* a separate exact change-of-variables/assembly theorem.

Compact chart cubes can support a proper continuous map to the target, but adapting the normal-data interface to that compact subtype is an additional construction, not a free consequence of compactness.

---

## 2. The chart model: exact scope and data

### 2.1 Recommended scope

For E, use:

\[
Q_a=[-a,a]^d,\qquad
K_C(y)=u_0(y|_{A^c})\prod_{i\in A}y_i^{2k_i},
\]
\[
d\mu_C(y)=
\mathbf 1_{Q_a}(y)\,
\rho(y)\prod_{i\in A}|y_i|^{h_i}\,dy,
\]
where:

* \(A\subseteq\mathrm{Fin}\,d\) is nonempty;
* \(k_i>0\) on \(A\);
* \(h_i\in\mathbb N\) on \(A\);
* \(u_0>0\) near the inactive-coordinate box;
* \(\rho\ge0\) on the box and has the analytic packet required by the producer.

Here \(\rho\) can include the pulled-back prior and a positive analytic Jacobian unit.

**Do not add normal-dependent phase units to this producer yet.** General SNC charts can have such units, so call this a *tangential-unit SNC chart producer*, not a producer for arbitrary SNC charts.

### 2.2 Structure layers

I recommend three layers rather than one large structure.

#### A. Combinatorial chart signature

Lean-shaped specification, not a claimed compiling declaration:

```lean
structure ChartSignature (d : ℕ) where
  active : Finset (Fin d)
  active_nonempty : active.Nonempty
  k : ↥active → ℕ
  h : ↥active → ℕ
  k_pos : ∀ i, 0 < k i
```

Use `Component := ↥active`.

For a component finset `I`, its ambient coordinate support is its image under subtype inclusion. Define:

* `Nrm I`: ambient coordinates belonging to `I`;
* `Tan I`: **all ambient coordinates not belonging to `I`**;
* `Inactive`: ambient coordinates outside `active`.

This avoids fake exponents on inactive coordinates and eliminates the temptation to use `k i = 0` while retaining a geometry that falsely declares every hyperplane exceptional.

#### B. Tangential-unit box data

Fields:

* `a : ℝ`, `ha : 0 < a`;
* `unitDomain : Set (Inactive → ℝ)`;
* `isOpen_unitDomain`;
* inclusion of the closed inactive-coordinate box in `unitDomain`;
* `unit : (Inactive → ℝ) → ℝ`;
* `analyticOn_unit`;
* `unit_pos : ∀ t ∈ unitDomain, 0 < unit t`.

Define, rather than store independently:

* `box`;
* `phase`;
* `jacWeight`;
* `unitOnTan I`, by restricting `Tan I` to inactive coordinates.

Derive uniform constants
\[
0<u_{\min}\le u_0\le u_{\max}
\]
on the compact inactive box. Do not make users supply these redundant bounds.

The measure-theoretic core can use weaker regularity than analyticity. Keep the analytic bridge separate if that fits the existing module hierarchy.

#### C. Packet and target-chart obligations

The producer packet contains:

* the analytic/holomorphic prior-amplitude and observable data;
* prior nonnegativity;
* the equality identifying the localised measure with
  `jacWeight * prior`;
* the integrability hypotheses not already derived by the bridge.

A target-chart adapter separately supplies:

* `blowdown`;
* source and target integration sets;
* phase pullback equality;
* amplitude pullback equality;
* exact integral transport, or a measure transport statement strong enough to derive it.

The finite atlas adapter supplies coverage and a.e.-disjointness. It need not be baked into every local chart.

### 2.3 Geometry and normal data

The local geometry still has ambient space \(\mathbb R^d\), `π := id`, and components indexed by `↥active`. Its normal data is exactly the coordinate construction, restricted to active indices.

The deepest stratum is now
\[
\{y_i=0:i\in A\}\cong\mathbb R^{d-|A|},
\]
not a point.

That fact should be a first-class regression test.

### 2.4 Why defer normal-dependent units?

Locally, a positive analytic unit can often be removed by a change such as
\[
z_{i_0}=y_{i_0}u(y)^{1/(2k_{i_0})}.
\]

But this introduces obligations for:

* analytic roots;
* local invertibility and domains;
* transformed Jacobian units;
* non-box boundaries;
* changed tubular germs and normal-jet compatibility.

It is a later rectification adapter, not a small extension of `Data.hnorm`.

---

## 3. Which modules change—and the hidden assumptions

Your dependency reading is broadly correct. I would add the following audit targets.

| Area | Required change or check |
|---|---|
| `CoordinateResolvedGeometry` | Components become active indices; normal spans use their ambient-coordinate images. |
| Stratum definitions | Coordinates in \(A\setminus I\) must be nonzero; inactive coordinates may vanish freely. |
| `WaterFillingCollar.tanUnit` | Product only over \(A\setminus I\), multiplied by `unitOnTan I`. |
| `baseSet` | Box bounds for **every** tangential coordinate; water-filling inequalities only for active tangential coordinates. |
| Collar thresholds | Depend on uniform positive lower bounds for the unit, including the deepest-stratum case. |
| Collar complement | Reprove the positive phase lower bound and hence the negligible tail. |
| Core indexing | Nonempty subsets of \(A\), not nonempty subsets of `Fin d`. |
| Core dimensions | `I.card - 1`; maximum log bound \(|A|-1\), not \(d-1\). |
| Deepest base | Compact inactive-coordinate box, not the unique zero point. |
| Normalised transport | Explicit \(h\), normal scaling powers, and active-tangential weight. |
| Analytic bridge | Normal variables indexed by \(I\); all remaining coordinates are parameters. |
| Signed reflection | Weight invariant, but a general tangential unit must itself be reflected. |
| Spectrum normalisation | Depends on active exponents and core normal dimensions, not ambient dimension. |

### Revised water-filling formulas

On the positive orthant, put
\[
T_I(t)=u_0(t|_{A^c})\prod_{j\in A\setminus I}t_j^{2k_j}.
\]

Then retain
\[
q_I(t)=\left(\frac{\delta}{T_I(t)}\right)^{1/|I|}.
\]

The base conditions are:

\[
0\le t_j\le a\quad(j\notin I),
\]
and
\[
\delta\le T_I(t)\bigl(t_j^{2k_j}\bigr)^{|I|}
\quad(j\in A\setminus I).
\]

**Do not impose the second condition on inactive coordinates.** Otherwise you remove valid parts of the exceptional divisor, including inactive coordinate hyperplanes.

Since the unit depends only on inactive coordinates, it is fixed during each active-coordinate water-filling argument. That is why this generalisation remains tractable.

### Concrete searches

Search for:

* `Finset.univ`, `.compl`, `Iᶜ`, especially inside products;
* `d - 1`, `2 ^ d - 1`, `numCores d`, `NonemptyIdx d`;
* proofs that the deepest base is a singleton;
* proofs deriving tangential nonvanishing for **every** tangential coordinate;
* positivity lemmas calling `hk` without an active-membership witness;
* identifications between ambient dimension, number of components, and normal rank;
* `phase_refl` and reflection-invariant localisation data;
* `commonQ_piece` proofs by `rfl`.

`σI I : Fin (nI I + 1) ≃ ↥I` is not intrinsically problematic. Its domain should remain determined by `I.card`, with nonemptiness supplied for `I`. The problem is usually the surrounding indexing type.

### Reflection deserves its own warning

For general \(u_0\),
\[
K_C(R_\sigma z)
=
u_0((R_\sigma z)|_{A^c})\prod_{i\in A}z_i^{2k_i}.
\]

The phase is not necessarily reflection invariant. Each orthant must use the reflected unit. The cube’s quadratic tangential unit is invariant, but the general theorem must not infer that from positivity or tangentiality.

The generic certificate consumers look reusable from their advertised interfaces. That is an interface-level assessment, not a verification of their internal proofs.

---

## 4. Pilot: use a singleton core with a compact tangential parameter

There is a cheaper pilot than generalising the entire collar machinery.

### 4.1 The singleton construction

For chart \(\beta\), write \(r=y_\beta\), \(s=(y_\gamma)_{\gamma\ne\beta}\). Then
\[
K_C(r,s)=u(s)r^2,\qquad d\mu=|r|^{d-1}\rho(r,s)\,dr\,ds.
\]

On a positive normal side, choose
\[
\lambda(s)=u(s)^{-1/2},
\qquad
\Phi(s,v)=(\lambda(s)v,s).
\]

Then
\[
K_C(\Phi(s,v))=v^2.
\]

Take a sufficiently small common \(b>0\). The core \(0\le v\le b\) is a genuine phase collar, and outside it the phase is at least \(b^2\). The base is the entire compact tangential box.

This uses:

* one core;
* `n := 0`;
* `h := d - 1`;
* `k := 1`;
* no nontrivial subset indexing;
* no water-filling decomposition.

It can either be a small parameterised-one-normal producer or a specialised instantiation of a generalised `NormalisedBoxCore`.

### 4.2 Recommended ordering

1. Partial-active **geometry and normal data**.
2. Weighted transport for an **abstract normalised box**.
3. Singleton tangential-unit producer.
4. Signed singleton blow-up chart and all-order cube assembly.
5. General partial-active water filling.

Thus I would replace E1 by a sharper E1′:

> **One active coordinate, arbitrary compact inactive-coordinate base, positive tangential unit, and explicit normal order.**

Do not force an `h = 0` public milestone. A zero-order test is useful internally, but the abstract weighted transport is small enough to include before the first blow-up theorem.

A `d = 2` pilot does not remove the inactive-coordinate issue. Arbitrary \(d\) with one active coordinate is the useful simplification.

---

## 5. Weighted `NormalisedBoxCore`: what really changes?

Your proposed modification is essentially right **for \(I=A\)**. For general \(I\), use
\[
H_I(s)=\prod_{j\in A\setminus I}t_j(s)^{h_j},
\qquad
L_I(s)=\prod_{i\in I}\lambda_i(s)^{h_i}.
\]

If the base measure remains the existing unweighted one, define
\[
c_h(s,v)=J(s)\,H_I(s)\,L_I(s)\,f_\rho(s,v).
\]

Then
\[
\operatorname{chartDensity}(h|_I,c_h)
=
\left(\prod_{i\in I}v_i^{h_i}\right)c_h(s,v),
\]
which is exactly the pulled-back weighted density.

### Proof impact

* **`map_Φ`:** preferably unchanged. Apply the generic transport lemma to the weighted physical density.
* **`density_ae`:** changes materially, but locally: split the active product into normal and tangential factors, substitute \(y_i=\lambda_i v_i\), and rearrange powers/products.
* **`c_eq_of_mem_box`:** gains the factor \(H_I L_I\).
* **`measurable_c`, `nonneg_c`:** gain finite products and their positivity/measurability.
* **`xData`, `amplitude_eq`, `toEta_core_x`:** must be multiplied by the same tangential factor. Changing only `c` would break the certificate.
* **`presentation.cBound`:** gains a uniform bound for \(H_I L_I\), obtained by compactness and continuity.
* **Coefficient-certificate datum identities:** update the density family accordingly; the observable jets should not absorb the Jacobian order.

The last two bullets are the main additions to your list.

### Spectrum

For each normal coordinate,
\[
\alpha_{i,m}=\frac{h_i+1+m}{2k_i}.
\]

With integral \(h_i\ge0\), the denominator lattice can remain the one generated by \(2k_i\). However:

* `commonQ` is unchanged only **for a fixed active/core exponent family**;
* its proof may cease to be `rfl` after restructuring;
* the leading exponent and residue arithmetic change;
* the log-degree bound remains controlled by the number of normal coordinates, not by \(h\).

Also verify whether the generic Mellin layer already handles arbitrary `CorePresentation.h`. If it does, the work is mainly producer identities and spectrum specialisation, not a new Mellin theorem.

### Absorbing the order into the prior

This remains a valid regression strategy on positive orthants. It is not the right final certificate:

* it records the wrong geometric order;
* it produces an overlarge candidate spectrum with vanishing low coefficients;
* it hides the geometric reason for the leading exponent.

Use equality between the absorbed-order and explicit-order answers as a test, not as the E stopping theorem.

---

## 6. Assembly and the original integral

### 6.1 Yes: assembled chart expansions are an acceptable E5

Use the explicit description:

> “All-order expansion of the original cube integral, with coefficients assembled from strata integrals in the blow-up chart domains.”

Do not describe this as an intrinsic expansion on the projective blow-up unless the transition/gluing obligations are proved.

You do not even need to construct a disjoint-union `ResolvedGeometry` to obtain this statement. A finite family of chart certificates and an assembly theorem is cheaper and avoids the properness/tubular-data issue.

### 6.2 Minimal theorem

For each chart, construct coefficients \(C_\beta(q)\), represented by its strata measures and moment fields, and prove its all-order remainder estimate.

Use the existing exact identity
\[
I(N)=\sum_{\beta:\mathrm{Fin}\,d} I_\beta(N).
\]

Then define
\[
C(q)=\sum_\beta C_\beta(q).
\]

For every truncation level, finite summation preserves the prescribed remainder class. The chart spectra share the same lattice here.

**The exact integral identity—not a separate argument about null boundaries for every coefficient—is the primary justification of assembly.**

### 6.3 A strong cube-specific oracle

Let \(a=Fp\), and set
\[
v_\beta(s)_\beta=1,\qquad
v_\beta(s)_\gamma=s_\gamma,\qquad
u_\beta(s)=|v_\beta(s)|^2.
\]

Then
\[
a(\phi_\beta(r,s))=a(r\,v_\beta(s)).
\]

Symmetry in \(r\), together with the even absolute Jacobian, kills every odd normal Taylor order. Consequently the assembled expansion has actual powers
\[
N^{-d/2-j},\qquad j\in\mathbb N,
\]
with no logarithms.

For smooth analytic packets, the coefficient oracle is
\[
C_j=
\frac{\Gamma(d/2+j)}{(2j)!}
\sum_\beta
\int_{[-1,1]^{d-1}}
u_\beta(s)^{-d/2-j}
D^{2j}a(0)[v_\beta(s),\ldots,v_\beta(s)]\,ds.
\]

This is a mathematical test specification, not a request to formalise Gamma integration before assembly.

At \(j=0\), it must recover the landed leading coefficient. For \(a=1\), all higher coefficients vanish.

### 6.4 Why the leading-measure pushforward is not the all-order pushforward

At leading order, pushing the exceptional face to \(0\) gives a scalar multiple of \(\delta_0\).

At higher orders, the coefficients involve normal jets of \(a\circ\phi_\beta\). Their target counterparts are derivative functionals at \(0\), not ordinary signed measures acting only on values of \(a\).

Thus:

* source strata measures can be pushed forward;
* **higher-order moment/jet information cannot be discarded**;
* a later intrinsic theorem needs compatible transformation laws for that information.

Gluing the underlying sets alone would not finish the all-order intrinsic claim.

---

## 7. Next six units: sizes and stopping gates

Sizes below are relative proof-risk estimates, not line-count promises.

| Unit | Scope | Size / risk | Mandatory gate |
|---|---|---|---|
| **E0a — executable obligation fixture** | Instantiate the cube’s singleton active data; factor the unit through inactive coordinates; corrected absolute-Jacobian/reflection identities; exact chart integral adapter. | Small–medium | A compiling fixture with no producer assumptions and no claim that full-chart blow-down is proper. |
| **E1 — partial-active geometry** | Active-index components, strata, normal spaces, frames/reindexing; full-active compatibility adapter. | Medium | Old coordinate geometry recovered through a proved adapter; singleton deepest stratum retains \(d-1\) free coordinates. |
| **E2 — weighted abstract core** | General `h`; weighted density transport; \(H_I L_I\) amplitude; `xData` and coefficient compatibility. | Medium | `h=0` recovery; a nonzero-order core; an \(I\subsetneq A\) test detecting omission of \(H_I\). |
| **E3 — singleton tangential-unit producer** | Compact tangential base, \(\lambda=u^{-1/(2k)}\), common collar, analytic normal series, negligible complement. | Medium–large | Arbitrary ambient \(d\), one active coordinate, explicit \(h\), nonconstant tangential unit. |
| **E4 — signed blow-up charts and cube assembly** | Reflection adapter, \(d\) chart certificates, exact finite-sum expansion of original integral. | Medium–large | Leading coefficient agrees with CCXCV; odd normal orders vanish; constant packet has no higher coefficients. |
| **E5 — general partial-active collar** | Water filling for all nonempty \(I\subseteq A\), unit bounds, weighted bases, signed general producer. | Large / highest risk | Full-active unit-one recovers G; singleton recovers E3; \(|A|-1\) log bound; inactive zeros allowed in bases. |

If the paper’s immediate target is the cube blow-up, **stop after E4** and write the theorem as assembled chart expansions. E5 is the reusable tangential-unit SNC producer. The honest projector-space construction and intrinsic gluing should be a separately gated phase.

## Bottom line

The real blocker is not missing blow-up geometry; it is the producer’s identification of **ambient coordinates with divisor components**. Fix that identification once. Then exploit the cube’s singleton active set to avoid making a full collar refactor a prerequisite for the all-order application.

The weighted core should record \(h=d-1\) from the outset. The original-integral theorem should use finite chart assembly. Neither normal-dependent units nor projective gluing belongs on its critical path.
