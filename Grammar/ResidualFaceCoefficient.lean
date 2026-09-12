/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.ProductChartTiedStrata

/-!
# The residual-face coefficient of a scalar-unit cell

Unit 4 of consult #79, in the form recommended by consult #80 (`tide-log/gpt6_bigpicture_v80.md`):
the coefficient of a NON-all-minimal cell is kept in the library's **projected orthant form** — the
amplitude evaluated on the minimal face (`faceProj` zeroes the minimal normal coordinates) against
the residual weight `∏_{a ∉ J} u_a^{h_a − 2k_a λ}` on the unit box — and the reflection sum is
reduced by pure finite combinatorics, with no coordinate-splitting measure theory.

* **Residual exponents.** `residualExponent h k λ a = h_a − 2k_a λ` is `−1` on the minimal
  coordinates `J = minimalCoords h k λ` and `> −1` off them (`residualExponent_eq_neg_one`,
  `residualExponent_gt_neg_one`); the **scaling identity**
  `Σ_a h_a + r − 2λ Σ_a k_a = Σ_{a ∉ J} (h_a − 2k_a λ + 1)` (`sum_residualExponent_add_one`) turns
  the box prefactor of `boxFaceCoeff` into the single power `b^s`, `s = Σ_{a∉J}(α_a + 1)`
  (`box_prefactor_eq`, generalising CCXXXIX's all-minimal case `s = 0`).
* **The expanded face coefficient.** `boxFaceCoeff = b^s · faceLeadConst · ∫_{unitBox}
  A(z, b·faceProj u) residualWeight u` (`boxFaceCoeff_eq_residual`) with
  `faceLeadConst h k λ 1 = Γ(λ)/(|J|−1)! ∏_{a∈J} 1/(2k_a)` — the denominator product runs over the
  MINIMAL coordinates only (`faceLeadConst_one_eq`).
* **Reflection reduction.** A sign sum `∑_{σ ∈ {±}^r} f σ` of a function depending only on the
  signs off `J` equals `2^{|J|}` times the sum over sign assignments off `J`
  (`sum_reduce_of_indep`, via the equivalence `(Fin r → Bool) ≃ (J → Bool) × (Jᶜ → Bool)`).
  Reflections on the minimal coordinates do not change the projected amplitude (`reflect_congr`),
  so the reflected cell coefficients depend only on the residual signs
  (`ScalarUnitCell.reflected_coeff_congr`) and
  `∑_σ (c.reflected σ).coeff = 2^{|J|} ∑_{τ ∈ {±}^{Jᶜ}} (c.reflected (extendFalse J τ)).coeff`
  (`sum_reflected_coeff`), each term being the explicit orthant integral (`reflected_coeff_eq`).
* **Tied pieces.** For a piece atlas all of whose cells sit at `(λ₀, k₀)`, the tied sum is the
  reduced reflection sum (`pieceAtlas_sum_tied_residual`); the all-minimal case (`J = everything`,
  a single residual sign class) is CCXLVIII's `pieceAtlas_sum_tied`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-! ### Reflection reduction -/

section Reflection

variable {r : ℕ}

/-- Extend a sign assignment off `J` by `false` on `J`. -/
def extendFalse (J : Finset (Fin r)) (τ : {a : Fin r // a ∉ J} → Bool) (a : Fin r) : Bool :=
  if h : a ∈ J then false else τ ⟨a, h⟩

theorem extendFalse_of_notMem (J : Finset (Fin r)) (τ : {a : Fin r // a ∉ J} → Bool) {a : Fin r}
    (ha : a ∉ J) : extendFalse J τ a = τ ⟨a, ha⟩ :=
  dif_neg ha

/-- **Reflection reduction**: a sign sum of a function depending only on the signs off `J` is
`2^{|J|}` times the sum over the signs off `J`. -/
theorem sum_reduce_of_indep (J : Finset (Fin r)) (f : (Fin r → Bool) → ℝ)
    (hf : ∀ σ σ' : Fin r → Bool, (∀ a, a ∉ J → σ a = σ' a) → f σ = f σ') :
    ∑ σ, f σ = 2 ^ J.card * ∑ τ : {a : Fin r // a ∉ J} → Bool, f (extendFalse J τ) := by
  classical
  rw [Fintype.sum_equiv (Equiv.piEquivPiSubtypeProd (fun a => a ∈ J) fun _ => Bool) f
    (fun p => f (extendFalse J p.2)) fun σ => hf σ _ fun a ha => by
      rw [extendFalse_of_notMem J _ ha]
      rfl]
  rw [Fintype.sum_prod_type]
  dsimp only
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_coe, Nat.cast_pow, Nat.cast_ofNat]

/-- Reflections agreeing where the vector is nonzero give the same reflected vector. -/
theorem reflect_congr {σ σ' : Fin r → Bool} {w : Fin r → ℝ} (h : ∀ a, w a ≠ 0 → σ a = σ' a) :
    reflect σ w = reflect σ' w := by
  funext a
  by_cases hw : w a = 0
  · simp only [reflect, hw, mul_zero]
  · simp only [reflect, h a hw]

end Reflection

/-! ### Residual exponents and the scaling identity -/

section Scaling

variable {r : ℕ} (h k : Fin r → ℕ) (hk : ∀ a, 0 < k a) (l : ℝ)

/-- The residual exponent `h_a − 2k_a λ`. -/
noncomputable def residualExponent (a : Fin r) : ℝ := (h a : ℝ) - 2 * (k a : ℝ) * l

/-- The minimal normal coordinates `{a | (h_a+1)/(2k_a) = λ}`. -/
noncomputable def minimalCoords : Finset (Fin r) := Finset.univ.filter fun a => ratioExp h k a = l

theorem mem_minimalCoords {a : Fin r} : a ∈ minimalCoords h k l ↔ ratioExp h k a = l := by
  unfold minimalCoords
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

include hk in
theorem residualExponent_gt_neg_one {a : Fin r} (hlt : l < ratioExp h k a) :
    -1 < residualExponent h k l a := by
  unfold residualExponent
  unfold ratioExp at hlt
  have hk' : (0 : ℝ) < 2 * (k a : ℝ) := by have := hk a; positivity
  rw [lt_div_iff₀ hk'] at hlt
  linarith

include hk in
theorem residualExponent_eq_neg_one {a : Fin r} (heq : ratioExp h k a = l) :
    residualExponent h k l a = -1 := by
  unfold residualExponent
  unfold ratioExp at heq
  have hk' : (2 * (k a : ℝ)) ≠ 0 := by have := hk a; positivity
  rw [div_eq_iff hk'] at heq
  linarith

theorem multCount_eq_card_minimalCoords :
    multCount (ratioExp h k) l = (minimalCoords h k l).card := by
  unfold multCount minimalCoords
  rw [Finset.sum_boole, Nat.cast_id]

include hk in
/-- **The scaling identity** `Σ_a h_a + r − 2λ Σ_a k_a = Σ_{a ∉ J} (h_a − 2k_a λ + 1)`. -/
theorem sum_residualExponent_add_one :
    ((∑ a, h a + r : ℕ) : ℝ) - 2 * l * ∑ a, (k a : ℝ) =
      ∑ a ∈ Finset.univ.filter (fun a => ¬ ratioExp h k a = l), (residualExponent h k l a + 1) := by
  have h1 : ((∑ a, h a + r : ℕ) : ℝ) - 2 * l * ∑ a, (k a : ℝ) =
      ∑ a, (residualExponent h k l a + 1) := by
    unfold residualExponent
    have : ∀ a, (h a : ℝ) - 2 * (k a : ℝ) * l + 1 = (h a : ℝ) - (2 * l) * (k a : ℝ) + 1 :=
      fun a => by ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    push_cast
    ring
  rw [h1, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun a => ratioExp h k a = l),
    Finset.sum_eq_zero fun a ha => by
      rw [residualExponent_eq_neg_one h k hk l (Finset.mem_filter.1 ha).2]; ring,
    zero_add]

include hk in
/-- The box prefactor is the single power `b^s`, `s = Σ_{a∉J}(α_a + 1)`. -/
theorem box_prefactor_eq {b : ℝ} (hb : 0 < b) :
    b ^ (∑ a, h a + r) * (b ^ (2 * ∑ a, k a)) ^ (-l) =
      b ^ (∑ a ∈ Finset.univ.filter (fun a => ¬ ratioExp h k a = l),
        (residualExponent h k l a + 1)) := by
  rw [← Real.rpow_natCast b (∑ a, h a + r), ← Real.rpow_natCast b (2 * ∑ a, k a),
    ← Real.rpow_mul hb.le, ← Real.rpow_add hb, ← sum_residualExponent_add_one h k hk l]
  congr 1
  push_cast
  ring

/-- **The face constant with the minimal set exposed**: `Γ(λ)/(|J|−1)! ∏_{a∈J} 1/(2k_a)`. -/
theorem faceLeadConst_one_eq :
    faceLeadConst h k l 1 = Real.Gamma l / (((minimalCoords h k l).card - 1).factorial : ℝ) *
      ∏ a ∈ minimalCoords h k l, 1 / (2 * (k a : ℝ)) := by
  unfold faceLeadConst
  rw [Real.one_rpow, mul_one, multCount_eq_card_minimalCoords]
  unfold minimalCoords
  rw [Finset.prod_filter]

end Scaling

/-! ### The expanded face coefficient -/

/-- **The expanded box face coefficient**: `b^s · faceLeadConst · ∫_{unitBox} A(z, b·faceProj u)
residualWeight u`. -/
theorem boxFaceCoeff_eq_residual {n t : ℕ} (h k : Fin (n + 1) → ℕ) (hk : ∀ a, 0 < k a) (l β b : ℝ)
    (hb : 0 < b) (A : (Fin t → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (z : Fin t → ℝ) :
    boxFaceCoeff n h k β b A l z =
      b ^ (∑ a ∈ Finset.univ.filter (fun a => ¬ ratioExp h k a = l),
          (residualExponent h k l a + 1)) *
        (faceLeadConst h k l β *
          ∫ u in unitBox (n + 1), A z (b • faceProj h k l u) * residualWeight h k l u) := by
  unfold boxFaceCoeff amplitudeCoeff
  rw [box_prefactor_eq h k hk l hb]

namespace ScalarUnitCell

variable {t : ℕ} (c : ScalarUnitCell t)

theorem reflected_n (σ : Fin (c.n + 1) → Bool) : (c.reflected σ).n = c.n := rfl
theorem reflected_h (σ : Fin (c.n + 1) → Bool) : (c.reflected σ).h = c.h := rfl
theorem reflected_k (σ : Fin (c.n + 1) → Bool) : (c.reflected σ).k = c.k := rfl
theorem reflected_b (σ : Fin (c.n + 1) → Bool) : (c.reflected σ).b = c.b := rfl
theorem reflected_q (σ : Fin (c.n + 1) → Bool) : (c.reflected σ).q = c.q := rfl
theorem reflected_base (σ : Fin (c.n + 1) → Bool) : (c.reflected σ).base = c.base := rfl
theorem reflected_βw (σ : Fin (c.n + 1) → Bool) : (c.reflected σ).βw = c.βw := rfl
theorem reflected_A (σ : Fin (c.n + 1) → Bool) : (c.reflected σ).A = reflectAmp c.n c.A σ := rfl

/-- **The reflected cell coefficient in projected orthant form.** -/
theorem reflected_coeff_eq (σ : Fin (c.n + 1) → Bool) :
    (c.reflected σ).coeff = ∫ z in c.base, c.βw z * (c.q z ^ (-c.lam) *
      (c.b ^ (∑ a ∈ Finset.univ.filter (fun a => ¬ ratioExp c.h c.k a = c.lam),
          (residualExponent c.h c.k c.lam a + 1)) *
        (faceLeadConst c.h c.k c.lam 1 *
          ∫ u in unitBox (c.n + 1),
            c.A z (reflect σ (c.b • faceProj c.h c.k c.lam u)) *
              residualWeight c.h c.k c.lam u))) := by
  unfold coeff scalarBoxFaceCoeff
  simp only [reflected_n, reflected_h, reflected_k, reflected_b, reflected_q, reflected_base,
    reflected_βw, reflected_A, reflected_lam]
  refine setIntegral_congr_fun c.base_compact.isClosed.measurableSet fun z _ => ?_
  rw [boxFaceCoeff_eq_residual c.h c.k c.k_pos c.lam 1 c.b c.b_pos]
  rfl

/-- Reflected cells whose signs agree off the minimal coordinates have equal coefficients. -/
theorem reflected_coeff_congr {σ σ' : Fin (c.n + 1) → Bool}
    (hσ : ∀ a, ¬ ratioExp c.h c.k a = c.lam → σ a = σ' a) :
    (c.reflected σ).coeff = (c.reflected σ').coeff := by
  rw [reflected_coeff_eq, reflected_coeff_eq]
  refine setIntegral_congr_fun c.base_compact.isClosed.measurableSet fun z _ => ?_
  refine congrArg (fun x => c.βw z * (c.q z ^ (-c.lam) *
    (c.b ^ (∑ a ∈ Finset.univ.filter (fun a => ¬ ratioExp c.h c.k a = c.lam),
      (residualExponent c.h c.k c.lam a + 1)) * (faceLeadConst c.h c.k c.lam 1 * x)))) ?_
  refine setIntegral_congr_fun (measurableSet_unitBox _) fun u _ => ?_
  rw [reflect_congr fun a ha => hσ a fun hmin => ha ?_]
  simp only [Pi.smul_apply, faceProj, hmin, if_true, smul_zero]

/-- **The reflection sum of a cell reduces to the residual signs**:
`∑_σ (c.reflected σ).coeff = 2^{|J|} ∑_{τ ∈ {±}^{Jᶜ}} (c.reflected (extendFalse J τ)).coeff`. -/
theorem sum_reflected_coeff :
    ∑ σ, (c.reflected σ).coeff =
      2 ^ (minimalCoords c.h c.k c.lam).card *
        ∑ τ : {a : Fin (c.n + 1) // a ∉ minimalCoords c.h c.k c.lam} → Bool,
          (c.reflected (extendFalse _ τ)).coeff :=
  sum_reduce_of_indep _ _ fun _ _ hσσ' => c.reflected_coeff_congr fun a ha =>
    hσσ' a fun hmem => ha ((mem_minimalCoords c.h c.k c.lam).1 hmem)

end ScalarUnitCell

/-! ### Tied sums of piece atlases -/

theorem FiniteScalarUnitAtlas.tied_eq_univ {t : ℕ} {Z : ℝ → ℝ} (At : FiniteScalarUnitAtlas t Z)
    (lam₀ : ℝ) (k₀ : ℕ) (hall : ∀ σ, (At.cell σ).lam = lam₀ ∧ (At.cell σ).mult - 1 = k₀) :
    At.tied lam₀ k₀ = Finset.univ :=
  Finset.filter_true_of_mem fun σ _ => hall σ

namespace ResolutionCover

variable {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι) (i : ι)
  (D : ι → Finset (Fin d)) {ε : ℝ} (hε : 0 < ε) (I : Finset (Fin d)) (hne : I.Nonempty)
  {F K : (Fin d → ℝ) → ℝ} {p : TubeWeight d}
  (Ad : AdaptedProductDensity (stratumSplit I hne) (R.boltzmannChartDensity i 0 K p)
    (sizePiece (D i) ε I))
  (hbase : IsCompact Ad.base) (hβ : IntegrableOn Ad.beta Ad.base)
  (hbox : Ad.normalBox = Metric.ball 0 ε)
  (h k : Fin (I.card - 1 + 1) → ℕ) (hk : ∀ j, 0 < k j)
  (q : (Fin (d - (I.card - 1 + 1)) → ℝ) → ℝ) (hq : Continuous q) (hq_pos : ∀ z ∈ Ad.base, 0 < q z)
  (A : (Fin (d - (I.card - 1 + 1)) → ℝ) → (Fin (I.card - 1 + 1) → ℝ) → ℝ)
  (hA : Continuous (Function.uncurry A))
  (hamp : ∀ z ∈ Ad.base, ∀ n ∈ Metric.ball (0 : Fin (I.card - 1 + 1) → ℝ) ε,
    Ad.amp z n * F ((R.chart i).φ (planeSplit (stratumSplit I hne) (z, n))) =
      A z n * ∏ j, |n j| ^ h j)
  (hphase : ∀ z ∈ Ad.base, ∀ n ∈ Metric.ball (0 : Fin (I.card - 1 + 1) → ℝ) ε,
    K ((R.chart i).Φ (planeSplit (stratumSplit I hne) (z, n))) = q z * ∏ j, n j ^ (2 * k j))
  (hFm : Measurable F)
  (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
  (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x)

include hbox hamp hphase hFm hF hK hK0 in
/-- **The tied sum of a (not necessarily all-minimal) piece atlas** in reduced orthant form:
`2^{|J|}` times the sum over the residual sign classes of the reflected cell coefficients, each an
explicit projected face integral (`ScalarUnitCell.reflected_coeff_eq`). -/
theorem pieceAtlas_sum_tied_residual {lam₀ : ℝ} {k₀ : ℕ} (hlam : minRatio h k = lam₀)
    (hk₀ : multCount (ratioExp h k) (minRatio h k) - 1 = k₀) :
    ∑ σ ∈ (R.pieceAtlas i D hε I hne Ad hbase hβ hbox h k hk q hq hq_pos A hA hamp hphase hFm hF
        hK hK0).tied lam₀ k₀,
      ((R.pieceAtlas i D hε I hne Ad hbase hβ hbox h k hk q hq hq_pos A hA hamp hphase hFm hF hK
        hK0).cell σ).coeff =
      2 ^ (minimalCoords h k (minRatio h k)).card *
        ∑ τ : {a : Fin (I.card - 1 + 1) // a ∉ minimalCoords h k (minRatio h k)} → Bool,
          ((R.pieceCell i D hε I hne Ad hbase hβ h k hk q hq hq_pos A hA).reflected
            (extendFalse _ τ)).coeff := by
  rw [FiniteScalarUnitAtlas.tied_eq_univ (R.pieceAtlas i D hε I hne Ad hbase hβ hbox h k hk q hq
    hq_pos A hA hamp hphase hFm hF hK hK0) lam₀ k₀ fun _ => ⟨hlam, hk₀⟩]
  exact (R.pieceCell i D hε I hne Ad hbase hβ h k hk q hq hq_pos A hA).sum_reflected_coeff

end ResolutionCover

end Grammar
