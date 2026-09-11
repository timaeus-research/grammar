## Recommendation

**Choose D: independent review and a bounded main-paper closure pass. Do not open another construction programme yet.**

The two implementation programmes are closed. **Independent verification of their scope is not.** The next deliverable should be a publication certificate saying exactly which paper claims have Lean counterparts, with exactly which external inputs—not another headline theorem.

This assessment is based on the supplied statements and ledger, **not an inspection of the repository or a completed independent proof audit**.

## 1. Closure audit

### CLXXIX: sound conditional identification; keep the tangent hypothesis visible

The Riesz/conormal identification is the right resolution of the labelled-splitting question. The remaining danger is turning an adapter into a construction.

`GeometricIdentification` **assumes**
\[
\operatorname{range}(D\mathrm{emb}_x)=\bigcap_l\ker(du_l)_x.
\]
That supplies the substantive identification of the kernel field with tangent directions. Vanishing of the equations along `emb` gives one inclusion; it does not, without further regularity and dimension information, give equality.

**Keep or strengthen the headline to:**

> The frame-built normal field is identified with the orthogonal complement of the tangent image, **assuming the stated tangent-image equality**. Its labelled lines correspond under the Riesz identification to the paper’s labelled conormal lines.

Paper dots must not certify:

- construction of the stratum as a manifold;
- derivation of the tangent-image equality from labelled equations alone;
- a global direct-sum bundle isomorphism beyond the actual frame-level statements.

Also keep the Riesz direction unambiguous: `toDual` sends gradients to differentials; the inverse Riesz identification sends conormal lines to gradient lines.

### CLXXX: genuinely conditional, and substantially so

The headline is appropriately bounded. `LiftedFoot` is not harmless bookkeeping. Together with injectivity, it supplies the smooth base recovery needed for the inverse.

In particular, “given a smooth parametrisation of the stratum” is **not** an adequate paraphrase. An injective smooth map does not by itself provide a smooth inverse onto its image.

**Suggested publication wording:**

> Given a certified normal tube, a frame–coframe atlas, and a smooth lifted foot satisfying `emb ∘ P = proj`, the bundle tube map is a smooth equivalence between the certified open domains.

Two presentation cautions:

1. `tubeHomeomorph` itself packages an **open partial homeomorphism**. The diffeomorphism claim is supported by that definition **together with** the separate smoothness theorems. Cite both.
2. The “onto `S`” wording should be traced to an actual assumption or consequence of the certified tube axioms; it is not an explicit field of the displayed `LiftedFoot`.

**Do not put an existence dot on “there is a tubular neighbourhood” using this result.**

### CLXXXI: the algebraic gate is closed; the model gate remains open

This is a valuable exact identity, before any asymptotic argument. The sign correction is important and appears properly exposed.

But the inputs supply two distinct bridges:

- `hca`: the coefficient family evaluates to `−a`;
- `hφ`: the population mean of `a` is the deterministic chart factor.

The second deserves equal prominence. Neither follows merely from calling the coordinates “Taylor coefficients.”

Also, the displayed integral theorem has loss
\[
f(x,v)=\Bigl(\prod_i v_i^{k_i}\Bigr)a(x,v).
\]
Thus identification with a model’s sampling integral requires that factorisation, not only the Taylor evaluation identity.

**Suggested headline addition:**

> Under the coefficient-evaluation identity, the population-mean identity, and the displayed chart factorisation of the loss, the certified core equals the sampling integral exactly.

Do not claim that this proves convergence of the Taylor expansion of a model, constructs its coefficient certificate, or validates its resolution chart. The current non-claim is right but should list **all three model interfaces**, not just `hca`.

### CLXXXII: a genuine generalisation, not an assumption-free removal of boundedness

“Boundedness removed” is defensible if immediately qualified:

> Bounded observations are replaced by the stated integrability/coordinate hypotheses and a uniform full-box scalar sub-Gaussian hypothesis.

`UniformSubgaussianPhase` is a substantive assumption on the sampling law. It is not a consequence of the Gaussian limit, a scalar CLT, or ordinary \(L^2\) integrability. It is exactly the input used to control finite-sample exponential moments uniformly.

Keep these distinctions explicit:

- full-box control is used for the finite-sample annealed passage;
- face variances enter the limiting first-moment formula;
- the coordinate certificate supplies the Banach-valued limit machinery;
- none of this asserts a sub-Gaussian bound for the Banach norm.

The variance bound is legitimately sharp. Calling the **annealed criterion itself sharp** would require more: sufficiency of \(\beta\kappa<2\) is not a necessity theorem for arbitrary amplitudes and laws.

One useful publication clarification: for \(\beta>0\), \(\kappa\ge0\),
\[
\beta\kappa<2
\quad\Longrightarrow\quad
\exists p>1,\ p\beta\kappa<2.
\]
So the explicit \(p\)-hypothesis is not an additional numerical restriction when \(p\) is freely chosen. The Lean wrapper currently exposes the witness; say so, or add a tiny corollary if needed.

### CLXXXIII: two qualifications need to be carried into the headline

**First, a.e. constant face variance is an additional hypothesis.** It is not a conclusion of the sampling programme. The signed-amplitude and chart-specific-temperature non-claims are good.

**Second, the displayed theorem assumes more than \(\beta v_0<2\).** It also retains:

- uniform full-box sub-Gaussian control with \(\beta\kappa<2\);
- the Banach \(L^2\) hypothesis;
- Gaussian finite-coordinate marginals;
- the tail certificate `htail`;
- the standing chart and leading-exponent hypotheses.

The ledger’s “so when” can reasonably inherit the preceding framework, but a standalone paper sentence cannot omit it.

**Use:**

> Under the preceding Gaussian-limit, integrability, tail, and sub-Gaussian hypotheses, a.e. constant face variance \(v_0\) gives the effective-temperature identity.

Do not advertise the displayed theorem as requiring **only** a.e. constancy and \(\beta v_0<2\). A weaker-assumption theorem may be mathematically available; it is not the statement shown.

There is also an **interface check that the independent review must perform**:

> Does the Gaussian measure delivered by the annealed assembly come with the `htail` certificate required by the first-moment and effective-temperature theorems?

The displayed assembly output does not expose `htail`. It may be available from its underlying construction, or transferable using uniqueness of the law from finite-coordinate marginals. Either route is fine. **Do not silently identify two existential witnesses.**

The normal-location check is correctly bounded. Its variance \(2\) also means the corresponding temperature condition is \(\beta<1\), not \(\beta<2\). It is a sign/normalisation check, not an end-to-end model formalisation.

### One correction to the “externals” vocabulary

The Banach \(L^2\) bound is **not an independent mathematical external under the displayed weighted coordinate-\(L^2\) summability certificate**.

Writing the weighted coordinates as \(Y_\gamma\), the certificate has the form
\[
\sum_\gamma \|Y_\gamma\|_{L^2}<\infty.
\]
Finite-sum Minkowski followed by monotone convergence/Fatou gives
\[
\left\|\sum_\gamma |Y_\gamma|\right\|_{L^2}
\le \sum_\gamma\|Y_\gamma\|_{L^2}.
\]
With the existing measurability and coordinate-realisation facts, this yields `MemLp sampleObs 2`.

It is honest to say:

> The current theorem takes Banach \(L^2\) as an explicit hypothesis; its derivation from the coordinate certificate has not been formalised here.

It is misleading to list it as an irreducible additional assumption.

---

## 2. Next programme: closure certificate, at most six units

**Success criterion:** a reader can determine the precise formalised statement and its remaining inputs without reconstructing the development.

### Unit 1 — Freeze the claim universe

At a fixed revision, enumerate:

- all 633 dot occurrences;
- every associated claim sentence and `\leanrefL`;
- its theorem or theorem bundle;
- its explicit and section-variable hypotheses;
- its status: exact, conditional, restricted model, component only, or unformalised.

Occurrences sharing a theorem may share analysis, but **each occurrence needs a disposition**.

**Inputs:** source extraction and document tooling; no new mathematics.

**Stop rule:** inventory first. No theorem strengthening to improve the inventory.

### Unit 2 — Independent geometry review

Have a reviewer other than the implementer inspect the geometry claims, especially the dependency chain into CLXXIX–CLXXX.

Check:

- smooth versus analytic;
- map versus embedding;
- kernel field versus tangent bundle;
- gradient/conormal versus pairing-dual lines;
- hypotheses versus constructed geometric objects;
- decomposition/uniqueness versus tube existence;
- partial homeomorphism plus smoothness versus a packaged smooth equivalence.

**Mathlib inputs:** manifold derivative definitions, `ContMDiff`/`ContMDiffOn`, bundle trivialisation interfaces, Riesz duality, `OpenPartialHomeomorph`.

**Output:** signed scope report and corrected claim sentences.

**Stop rule:** no IFT, no new level-set manifold, no lifted-foot construction.

### Unit 3 — Independent empirical-chain review

Trace one route end to end:
\[
\text{model chart inputs}
\to\text{sample datum}
\to\text{certified core}
\to\text{limit law}
\to\text{annealed limit}
\to\text{Gaussian first moment}
\to\beta_{\rm eff}.
\]

Check sign, centring, \(N=n\), dimensions versus sample-size binders, leading-order normalisation, measurability, integrability, and the exact Gaussian witness.

Explicitly inspect:

- how `htail` reaches the first-moment theorem;
- where Banach \(L^2\) is needed;
- where full-box control is stronger than face control;
- common-proxy/common-\(p\) requirements across charts;
- the external remainder norm and scaling.

**Mathlib inputs:** `MemLp`, Bochner integrals, `HasSubgaussianMGF`, independence, Gaussian laws, the distributional-convergence and uniform-integrability interfaces already used.

**Stop rule:** fix a small interface omission if necessary; do not improve rates, proxy generality, or logarithmic orders.

### Unit 4 — Main-paper fidelity pass

Check every marked sentence, prioritising existence statements and global conclusions. Split sentences where one dot currently appears to cover both a proved component and an external geometric step.

Each conditional claim should expose its assumptions locally or point to a clearly named hypothesis package.

**Inputs:** the inventory and review reports, not new Mathlib machinery.

**Stop rule:** if a claim needs a new theorem, weaken its formalisation annotation or mark the missing part. Do not turn editorial closure into theorem development.

### Unit 5 — Compile publication-facing endpoint examples

Create a small release-check module that applies the selected public endpoints using explicitly named external inputs. This detects hidden binders and non-composing existential certificates.

Produce two dependency summaries:

1. main paper §3–4;
2. companion-note empirical/annealed chain.

**Inputs:** existing theorem APIs and a small amount of wrapper code.

**Stop rule:** wrappers may reorganise hypotheses; they must not conceal new assumptions or open a substantial proof project.

### Unit 6 — Publish the coverage statement and external register

Update `grammar_lean.tex`, the ledger, and the release summary consistently. Rebuild at the frozen release revision and run the repository’s existing axiom/sorry checks.

**Output:** an enumerated theorem list, an external-hypothesis register, and an explicit exclusions paragraph.

**Stop rule:** closure is achieved when every claim has an honest disposition—not when every external has disappeared.

### What not to open

For this programme:

- no A: general/local IFT or lifted-foot existence;
- no B: exact analytic resolution/localisation bridge;
- no chart-specific proxies;
- no next logarithmic order;
- no global resolved-\(U\) construction;
- no formalisation of heuristic appendices.

The coordinate-certificate-to-Banach-\(L^2\) lemma is a reasonable later cleanup. It is not a reason to postpone the review.

Also: the proposed A route through “an embedded submanifold with a smooth retraction” must be handled carefully. **Assuming a smooth retraction is not a construction of the missing smooth inverse.** It only helps once the relevant smooth identification with the base is actually available.

---

## 3. Publication readiness

### The shortest honest path

**Publish a conditional coverage statement after the reviews. You do not need to discharge every external to publish it.**

Do not say “§3–4 are formalised” and then repair that sentence with a distant caveat. Enumerate the actual paper theorem numbers, state the formalised versions, and attach the relevant external-input labels.

A suitable template is:

> At revision …, the Lean development formalises the following results of §§3–4 in the versions listed in Table … . The geometric results use the certified chart, frame, and tubular data specified there; construction of those data from the paper’s geometric setting is included only where explicitly indicated. The sampling and annealed conclusions additionally require the listed coefficient, distributional, and remainder hypotheses. The formalisation does not presently construct the full resolved geometric setting or prove the model-specific remainder estimates.

Then list the exact theorem numbers. **The supplied material is not enough to invent that list honestly.**

### External register

| Input or missing step | Classification | What closure requires |
|---|---|---|
| Certified resolution charts and their relation to the original model | Substantive geometry; bridge unfinished | Exact chart identities and domains, not merely matching notation |
| Analytic units, compatible localisation, and passage to the paper’s resolved setting | Unfinished | A precise compatibility theorem or an explicit external package |
| Level-set manifold and tangent-image identification | Unfinished under suitable regularity assumptions | IFT/regular-level-set construction, or externally supplied manifold data |
| Certified normal tube | Supplied geometric object unless constructed elsewhere | Separate existence/compatibility result |
| Smooth lifted foot | Unfinished; not implied by an arbitrary injective smooth map | Strong enough embedding/identification hypotheses and the construction |
| Loss factorisation, `hca`, and population-mean identity | Model-specific inputs | Verification for the chosen model and chart |
| Measurability, independence, identical distribution, moment and coordinate certificates | Genuine probabilistic/analytic assumptions | Model verification; not conclusions of the abstract theorem |
| Uniform full-box sub-Gaussian proxy | Genuine sufficient law assumption | Verification, or a different theorem using alternative tail control |
| Gaussian-law tail certificate `htail` | Construction/interface obligation if already produced internally | Show it belongs to the same limit law used downstream |
| Banach \(L^2\) from weighted coordinate-\(L^2\) summability | Derivable; formal derivation undone | Minkowski/Fatou lemma and measurability plumbing |
| Scaled \(L^1\) remainder decay | Substantive model/localisation estimate | Proof for the actual remainder, or explicit assumption |
| A.e. constant face variance | Additional structural assumption for the corollary | Model verification; not needed for the general variance-dependent formula |
| Common proxy across finitely many charts | Scope restriction, not a foundational external | Retain it explicitly or later generalise the theorem |

### “Essential” versus “merely undone”

Bluntly: **nothing true and precisely formulated is “unremovable by more Lean” merely because it is currently external.** The useful distinction is:

1. **Assumptions not implied by the current general setting.**  
   Sub-Gaussian tails, a.e. constant face variance, model identities, and sufficient sampling regularity cannot be manufactured by formalisation. They need mathematical assumptions or model-specific proofs. The exact sub-Gaussian criterion is sufficient, not necessarily necessary.

2. **Missing constructions or deductions from adequate assumptions.**  
   Banach \(L^2\) from the coordinate certificate is the clearest example. Level-set and lifted-foot constructions belong here only after the hypotheses are strong enough.

3. **Substantive unfinished mathematics or integration.**  
   The exact geometric bridge and model-specific remainder estimate are not editorial details. They may be the main work needed for an unconditional application to the paper’s setting.

**Bottom line:** you appear ready to prepare a release of **explicitly conditional formalised counterparts**. You are not yet justified in presenting all the paper’s geometric existence and sampling conclusions as an end-to-end formalisation. Complete the independent reviews, make the external register exhaustive against the source, and publish that precise boundary.
