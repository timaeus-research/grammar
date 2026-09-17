## Decision

**Use R1 for the generic first correction.** In fact, the gap assumption makes a direct dominated-convergence proof possible: **no product-sublevel-set estimate is needed.**

For the general readable coefficient theorem, use **tensor-product Hadamard finite parts**, packaged through a Laurent family. This gives a particularly clean singleton-resonance formula and correctly accounts for all the lower-log terms in the multiple-resonance case.

There is one important correction to the proposed comparison with the paper: **a convergent Taylor expansion at the origin is not available for arbitrary \(C^\infty\) amplitudes.** The face formula remains valid in that generality; an origin-Taylor-series formula needs additional hypotheses or a different interpretation.

---

## 1. The generic formula is correct

Write \(i=i_0\), \(L=[d]\setminus\{i\}\), and
\[
p(w)=\prod_{l\in L}w_l^{2k_l},\qquad
\lambda=\frac{h_i+1}{2k_i},\qquad
\mu_1=\frac{h_i+2}{2k_i}.
\]
Assume
\[
\mu_1<\lambda_l\quad(l\in L).
\]

Then your two coefficients are exactly
\[
C_\lambda=\frac1{2k_i}
 \int_{[0,1]^L}w^{h_L-2k_L\lambda}
       \eta(0,w)S_\lambda(\zeta(0,w))\,dw
\]
and
\[
\boxed{
C_{\mu_1}=\frac1{2k_i}
 \int_{[0,1]^L}w^{h_L-2k_L\mu_1}
 \left[
 \partial_i\eta(0,w)S_{\mu_1}(\zeta(0,w))
 +\eta(0,w)\partial_i\zeta(0,w)
       S_{\mu_1+1/2}(\zeta(0,w))
 \right]dw .
}
\]

Equivalently,
\[
C_{\mu_1}=\frac1{2k_i}
 \int_{[0,1]^L}w^{h_L-2k_L\mu_1}
 \left.\partial_u\bigl[\eta(u,w)S_{\mu_1}(\zeta(u,w))\bigr]\right|_{u=0}\,dw .
\]

The signs and factors are correct:

* \(du\) supplies \(1/(2k_i)\);
* Taylor order one supplies no additional factorial;
* \(\partial_aS_\nu(a)=S_{\nu+1/2}(a)\), with a **positive** sign;
* extracting \(T^{-\mu}\), where \(T=Np(w)\), supplies \(p(w)^{-\mu}\).

There is **no separate contribution from Taylor-expanding in \(L\)**. Those directions are already retained exactly in the face integral.

The upper-endpoint tails are exponentially small in **\(T=Np(w)\)**, not uniformly exponentially small in \(N\). Nevertheless, under the strict gap, their integrated contribution is \(o(N^{-\mu_1})\).

Thus
\[
Z_N=C_\lambda N^{-\lambda}+C_{\mu_1}N^{-\mu_1}
       +o(N^{-\mu_1}),
\]
and the engine coefficients satisfy:

* \(c(\lambda,0)=C_\lambda\);
* \(c(\mu_1,0)=C_{\mu_1}\);
* all positive log degrees at these exponents vanish;
* all coefficients at lattice exponents strictly between them vanish.

“First correction” here means the first **possible** correction: \(C_{\mu_1}\) may itself vanish.

---

## 2. R1: use one global domination, not two regions

Let
\[
I(T,w)=\int_0^1
 \eta(u,w)e^{\sqrt T\,u^{k_i}\zeta(u,w)}
 u^{h_i}e^{-Tu^{2k_i}}\,du,
\]
and put
\[
A_0(w)=\frac{\eta(0,w)S_\lambda(\zeta(0,w))}{2k_i},
\]
\[
A_1(w)=\frac{
 \partial_i\eta(0,w)S_{\mu_1}(\zeta(0,w))
 +\eta(0,w)\partial_i\zeta(0,w)S_{\mu_1+1/2}(\zeta(0,w))
}{2k_i}.
\]

The useful parameter-uniform 1D statement is
\[
B(T,w):=T^{\mu_1}\bigl(I(T,w)-A_0(w)T^{-\lambda}\bigr),
\]
with
\[
\sup_{T>0,\ w\in[0,1]^L}|B(T,w)|<\infty,
\qquad
B(T,w)\longrightarrow A_1(w)\quad(T\to\infty).
\]

For \(T\ge1\), this is the fixed-scaled-variable Taylor estimate. Compact uniform jet bounds suffice; the exponential domination follows from
\[
-y^2+My\le-\tfrac12y^2+\tfrac12M^2.
\]

For \(0<T\le1\), \(I(T,w)\) and \(A_0(w)\) are uniformly bounded, and
\[
T^{\mu_1}|I(T,w)|+|A_0(w)|T^{\mu_1-\lambda}
\]
is bounded. This is why the same bound holds for **all** \(T>0\).

Now
\[
N^{\mu_1}\bigl(Z_N-C_\lambda N^{-\lambda}\bigr)
 =
 \int_{[0,1]^L}
 w^{h_L-2k_L\mu_1}B(Np(w),w)\,dw.
\]
The weight is integrable precisely because
\[
h_l-2k_l\mu_1>-1\quad(l\in L).
\]
Also \(p(w)>0\) almost everywhere. Dominated convergence proves the result immediately.

### If a sublevel estimate is wanted

The stated sharp bound is correct, with log degree at most \(|L|-1\); more sharply, the degree is one less than the multiplicity of the minimum ratio.

But the cheaper sufficient bound is, for
\[
0<\sigma<\min_l\frac{a_l+1}{2k_l},\qquad 0<\varepsilon\le1,
\]
\[
\boxed{
\int_{\{p(w)\le\varepsilon\}}w^a\,dw
\le
\varepsilon^\sigma
\prod_l\frac1{a_l+1-2k_l\sigma}.
}
\]
It follows simply from
\[
\mathbf1_{\{p\le\varepsilon\}}\le\varepsilon^\sigma p^{-\sigma}.
\]
No logarithmic-volume theorem is necessary.

With one further Taylor order, one can also obtain
\[
Z_N-C_\lambda N^{-\lambda}-C_{\mu_1}N^{-\mu_1}
 =O(N^{-\mu_1-\delta})
\]
for every
\[
0<\delta<
\min\left\{\frac1{2k_i},\ \min_{l\in L}(\lambda_l-\mu_1)\right\}.
\]
This stronger conclusion is optional, not needed for coefficient identification.

### Reading off: finite asymptotic independence, not manufactured uniqueness

A full second `CutoffExpansion` is unnecessary. Take the existing expansion through a cutoff strictly above \(\mu_1\). After normalization by \(N^{\mu_1}\), terms above \(\mu_1\) tend to zero.

What remains is a finite sum of exponential-polynomial terms in \(x=\log N\). Such a sum can converge only if:

1. every positive exponential-growth block vanishes;
2. the exponent-zero polynomial is constant;
3. that constant is the limit.

Subtracting the two explicit monomials also gives a full expansion **by linearity of the existing expansion**, with coefficients modified at two entries. But uniqueness alone does not extract the vanishings from the limit; the same finite asymptotic-independence fact is still the essential lemma.

### Lean-typable core targets

The following is a standalone proposed interface, not a claim about existing repository identifiers. It uses smooth global extensions of the closed-cube data and the natural-number \(h,k\) setting underlying the stated lattice.

```lean
open Filter MeasureTheory
open scoped BigOperators

namespace Grammar
noncomputable section

abbrev EmpPoint (d : ℕ) := Fin d → ℝ
abbrev EmpFace (d : ℕ) (i : Fin d) :=
  {j : Fin d // j ≠ i} → ℝ

def empFacePoint {d : ℕ} (i : Fin d) (w : EmpFace d i) :
    EmpPoint d :=
  fun j => if hj : j = i then 0 else w ⟨j, hj⟩

def empNormalJet {d : ℕ} (i : Fin d) (a : ℕ)
    (f : EmpPoint d → ℝ) (w : EmpFace d i) : ℝ :=
  iteratedDeriv a
    (fun u => f (Function.update (empFacePoint i w) i u)) 0

def empMoment (ν a : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ),
    Real.rpow t (ν - 1) * Real.exp (-t + a * Real.sqrt t)

def empRatio {d : ℕ} (h k : Fin d → ℕ) (i : Fin d) : ℝ :=
  ((h i : ℝ) + 1) / (2 * (k i : ℝ))

def empFaceWeight {d : ℕ} (h k : Fin d → ℕ)
    (i : Fin d) (ν : ℝ) (w : EmpFace d i) : ℝ :=
  ∏ j : {j : Fin d // j ≠ i},
    Real.rpow (w j) ((h j.1 : ℝ) - 2 * (k j.1 : ℝ) * ν)

def empReadableFaceCoeff {d : ℕ}
    (η ζ : EmpPoint d → ℝ) (h k : Fin d → ℕ)
    (i : Fin d) (a : ℕ) (ν : ℝ) : ℝ :=
  (∫ w in Set.Icc (0 : EmpFace d i) 1,
    empFaceWeight h k i ν w *
      empNormalJet i a
        (fun v => η v * empMoment ν (ζ v)) w) /
    (2 * (k i : ℝ) * (Nat.factorial a : ℝ))

def empReadableBox {d : ℕ}
    (η ζ : EmpPoint d → ℝ) (h k : Fin d → ℕ)
    (T : ℝ) : ℝ :=
  ∫ v in Set.Icc (0 : EmpPoint d) 1,
    η v *
      Real.exp
        (Real.sqrt T * (∏ j, v j ^ k j) * ζ v) *
      (∏ j, v j ^ h j) *
      Real.exp (-T * (∏ j, v j ^ (2 * k j)))

theorem emp_firstCorrection_of_gap
    {d : ℕ} (hd : 2 ≤ d)
    (η ζ : EmpPoint d → ℝ) (h k : Fin d → ℕ)
    (i : Fin d)
    (hη : ContDiff ℝ ⊤ η) (hζ : ContDiff ℝ ⊤ ζ)
    (hk : ∀ j, 0 < k j)
    (hgap : ∀ j, j ≠ i →
      empRatio h k i + 1 / (2 * (k i : ℝ)) < empRatio h k j) :
    let λ := empRatio h k i
    let μ := λ + 1 / (2 * (k i : ℝ))
    Tendsto
      (fun T : ℝ =>
        Real.rpow T μ *
          (empReadableBox η ζ h k T -
            empReadableFaceCoeff η ζ h k i 0 λ *
              Real.rpow T (-λ)))
      atTop
      (nhds (empReadableFaceCoeff η ζ h k i 1 μ)) := by
  sorry
```

A reading-off lemma needs only a finite remainder statement:

```lean
theorem latticeCoeff_eq_of_twoTerm_limit
    (Z : ℝ → ℝ) (c : ℕ → ℕ → ℝ)
    (Q D p r : ℕ) (hQ : 0 < Q) (hpr : p < r)
    (A B : ℝ)
    (hcut :
      Tendsto
        (fun T : ℝ =>
          Real.rpow T ((r : ℝ) / (Q : ℝ)) *
            (Z T -
              ∑ n ∈ Finset.range (r + 1),
                Real.rpow T (-((n : ℝ) / (Q : ℝ))) *
                  ∑ q ∈ Finset.range (D + 1),
                    c n q * (Real.log T) ^ q))
        atTop (nhds 0))
    (hlim :
      Tendsto
        (fun T : ℝ =>
          Real.rpow T ((r : ℝ) / (Q : ℝ)) *
            (Z T - A * Real.rpow T (-((p : ℝ) / (Q : ℝ)))))
        atTop (nhds B)) :
    ∀ n, n ≤ r → ∀ q, q ≤ D →
      c n q =
        if n = p ∧ q = 0 then A
        else if n = r ∧ q = 0 then B
        else 0 := by
  sorry

end
end Grammar
```

Here \(D=d-1\), \(p=Q\lambda\), and \(r=Q\mu_1\). The lattice integrality is a separate arithmetic fact.

---

## 3. General readable coefficient: canonical finite parts

### The normalization of finite part matters

For a nonresonant real exponent \(a\), define
\[
\operatorname{FP}\int_0^1x^a f(x)\,dx
=
\int_0^1x^a
 \left(f(x)-\sum_{n=0}^{M-1}\frac{f^{(n)}(0)}{n!}x^n\right)dx
+
\sum_{n=0}^{M-1}
 \frac{f^{(n)}(0)}{n!(a+n+1)},
\]
where \(a+M>-1\), and \(a+n+1\ne0\) for every \(n\in\mathbb N\).

This is independent of sufficiently large \(M\). In several variables use the tensor product of these one-coordinate functionals. This specifies the finite part canonically; arbitrary cutoff-based “regularization” without the compensating terms would not.

Coordinates with \(a>-1\) need no subtraction: their functional is ordinary integration.

### Singleton resonance

Suppose
\[
J(\mu)=\{i\},\qquad
\alpha_i=2k_i\mu-h_i-1\in\mathbb N.
\]
Then the target theorem is
\[
\boxed{
c(\mu,0)=
\frac1{2k_i\alpha_i!}\,
\operatorname{FP}\int_{[0,1]^L}
 w^{h_L-2k_L\mu}
 \left.
 \partial_i^{\alpha_i}
 \bigl[\eta(v)S_\mu(\zeta(v))\bigr]
 \right|_{v_i=0}\,dw ,
}
\]
and
\[
c(\mu,q)=0\qquad(q\ge1).
\]

This includes coordinates \(l\in L\) with \(\lambda_l<\mu\): their weights are finite-part weights. Since \(l\notin J(\mu)\), none of their Taylor denominators vanishes.

This is the right next readable theorem. The generic first correction is exactly its \(\alpha_i=1\), ordinary-integrability special case.

### Multiple resonance: a clean Laurent formula, but not only the deepest face

Introduce a local variable
\[
z=\mu-s
\]
and the meromorphic weight functional
\[
T_i(z)[f]
=
\operatorname{AC}\int_0^1
 x^{h_i-2k_i\mu+2k_i z}f(x)\,dx.
\]
Here `AC` is defined by the same finite Taylor-subtraction formula, now with denominators
\[
h_i+n+1-2k_i\mu+2k_i z.
\]

Set
\[
\mathcal F_\mu(z)
=
\left(\bigotimes_{i=1}^dT_i(z)\right)
 \bigl[\eta\,S_{\mu-z}(\zeta)\bigr].
\]
Then the complete readable statement is
\[
\boxed{
c(\mu,q)=\frac1{q!}\,[z^{-q-1}]\,\mathcal F_\mu(z).
}
\]

This convention absorbs the Mellin-residue sign cleanly. In particular,
\[
S_{\mu-z}
=
\sum_{b\ge0}\frac{(-z)^b}{b!}\partial_\mu^b S_\mu,
\]
which explains the appearances of \((-\partial_\mu)^bS_\mu\).

For \(i\in J(\mu)\),
\[
T_i(z)=\frac{R_i}{z}+H_{i,0}+zH_{i,1}+\cdots,
\qquad
R_i[f]=\frac{f^{(\alpha_i)}(0)}{2k_i\alpha_i!}.
\]
For nonresonant \(i\), the family is regular at zero.

If \(r=|J(\mu)|\), this gives \(c(\mu,q)=0\) for \(q\ge r\), and the highest-log coefficient is especially simple:
\[
\boxed{
c(\mu,r-1)=
\frac{1}{(r-1)!\prod_{i\in J(\mu)}(2k_i\alpha_i!)}
\operatorname{FP}\int_{[0,1]^L}
 w^{h_L-2k_L\mu}
 \left.
 \partial_J^\alpha[\eta S_\mu(\zeta)]
 \right|_{v_J=0}\,dw .
}
\]

**Lower log powers require more than the product of the resonant pole factors.** They also involve the regular and higher Laurent coefficients \(H_{i,b}\), hence contributions from larger-dimensional faces.

For example, with two resonant coordinates and suppressing complementary coordinates, write
\[
A_0=\eta S_\mu(\zeta),\qquad
A_1=-\eta\,\partial_\mu S_\mu(\zeta).
\]
Then
\[
c(\mu,1)=R_1R_2[A_0],
\]
whereas
\[
c(\mu,0)
=(R_1H_{2,0}+H_{1,0}R_2)[A_0]+R_1R_2[A_1].
\]
Thus the log case has a clean **Laurent-functional** form, but generally not a single integral over the deepest resonant face.

---

## 4. Relation to the paper’s Taylor-tree formula

There is no conflict in the Mellin/Laurent algebra. Expanding a monomial in the complementary directions gives precisely the denominators
\[
\frac1{h_l+n_l+1-2k_l\mu},
\]
interpreted through Laurent coefficients when they vanish. Keeping those directions unexpanded gives the finite-part face functional. The \((-\partial_\mu)\)-terms agree with the expansion of \(S_{\mu-z}\).

However, the assertion

> “They must agree termwise after integrating the \(L\)-Taylor series”

needs an analyticity or convergence qualification.

For example, in dimension two take \(i=1\), \(\zeta=0\), and
\[
\eta(v_1,v_2)=
\begin{cases}
e^{-1/v_2^2},&v_2>0,\\
0,&v_2=0.
\end{cases}
\]
Every derivative of \(\eta\) at the origin vanishes. Nevertheless, when coordinate one is the unique leading coordinate, its leading face integral is strictly positive. Consequently, **no formula determined solely by the full origin jet can describe these coefficients for all smooth amplitudes**.

Under hypotheses ensuring that the origin Taylor series converges to the amplitude in the derivative topology required by the finite-part functionals—for example suitable analyticity on a neighborhood larger than the cube—the termwise identification is valid. Absolute pointwise convergence alone is not the right justification near regularized faces.

So the distinction is:

* **Smooth setting:** finite jets in normal directions, unexpanded face functions, and finite-part integrals.
* **Convergent origin-series setting:** the same functionals evaluated termwise, yielding the paper’s Taylor/Laurent series.

That distinction supports the face-integral route rather than contradicting it.