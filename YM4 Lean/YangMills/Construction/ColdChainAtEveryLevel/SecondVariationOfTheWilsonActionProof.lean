import YangMills.Construction.ColdChainAtEveryLevel.LeastQuarticGaugeProof
import YangMills.Construction.ColdChainAtEveryLevel.SecondVariationOfAFitInTheChartProof
import YangMills.Construction.ColdChainAtEveryLevel.SecondVariationOfTheActionInTheChartProof
import YangMills.Construction.ColdChainAtEveryLevel.SecondVariationOfTheWilsonAction
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open NormedSpace
namespace YangMills.Construction.BlockAverages.WilsonSecondVariation
variable {F : BlockFrame}
def realPartCLM : ℍ[ℝ] →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun q => q.re
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
theorem abs_re_le_norm (q : ℍ[ℝ]) : |q.re| ≤ ‖q‖ := by apply _root_.YangMills.Construction.BlockAverages.VariationRates.quaternion_abs_re_le_norm <;> assumption
theorem norm_sq_eq_sum_sq (x : ℍ[ℝ]) : ‖x‖ ^ 2 = x.re ^ 2 + x.imI ^ 2 + x.imJ ^ 2 + x.imK ^ 2 := by
  rw [sq ‖x‖, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
def expProduct (bs : List ℍ[ℝ]) (τ : ℝ) : ℍ[ℝ] := (bs.map fun b => exp (τ • b)).prod
theorem expProduct_nil (τ : ℝ) : expProduct [] τ = 1 := rfl
theorem expProduct_cons (b : ℍ[ℝ]) (bs : List ℍ[ℝ]) (τ : ℝ) :
    expProduct (b :: bs) τ = exp (τ • b) * expProduct bs τ := rfl
theorem expProduct_jets (bs : List ℍ[ℝ]) (hb : ∀ b ∈ bs, b.re = 0) :
    ∃ R₁ R₂ : ℝ → ℍ[ℝ], (∀ τ, HasDerivAt (expProduct bs) (R₁ τ) τ) ∧ (∀ τ, HasDerivAt R₁ (R₂ τ) τ) ∧
      expProduct bs 0 = 1 ∧ R₁ 0 = bs.sum ∧ (R₂ 0).re = -‖bs.sum‖ ^ 2 ∧
        ‖R₂ 0‖ ≤ (bs.map fun b => ‖b‖).sum ^ 2 ∧ bs.sum.re = 0 := by
  induction bs with
  | nil =>
    refine ⟨fun _ => 0, fun _ => 0, fun τ => ?_, fun τ => hasDerivAt_const τ 0, rfl, rfl, ?_, ?_, ?_⟩
    · have : expProduct [] = fun _ => (1 : ℍ[ℝ]) := rfl
      rw [this]
      exact hasDerivAt_const τ 1
    · simp
    · simp
    · simp
  | cons b r ih =>
    obtain ⟨R₁, R₂, h1, h2, h0, e1, e2, e3, e4⟩ := ih fun x hx => hb x (List.mem_cons_of_mem _ hx)
    have hbr : b.re = 0 := hb b List.mem_cons_self
    have hE : ∀ τ : ℝ, HasDerivAt (fun τ : ℝ => exp (τ • b)) (b * exp (τ • b)) τ :=
      fun τ => hasDerivAt_exp_smul_const' (𝕂 := ℝ) b τ
    have hE' : ∀ τ : ℝ, HasDerivAt (fun τ : ℝ => b * exp (τ • b)) (b * (b * exp (τ • b))) τ :=
      fun τ => (hE τ).const_mul b
    refine ⟨fun τ => b * exp (τ • b) * expProduct r τ + exp (τ • b) * R₁ τ,
      fun τ => (b * (b * exp (τ • b)) * expProduct r τ + b * exp (τ • b) * R₁ τ) +
        (b * exp (τ • b) * R₁ τ + exp (τ • b) * R₂ τ), fun τ => ?_, fun τ => ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (hE τ).mul (h1 τ)
    · exact ((hE' τ).mul (h1 τ)).add ((hE τ).mul (h2 τ))
    · rw [expProduct_cons, h0]
      simp
    · simp only [zero_smul, exp_zero, h0, mul_one, one_mul, List.sum_cons, e1]
    · simp only [zero_smul, exp_zero, h0, mul_one, one_mul, List.sum_cons, e1]
      set c := r.sum
      set D := R₂ 0
      exact show (b * b + b * c + (b * c + D)).re = -‖b + c‖ ^ 2 from by
        have hD : D.re = -(c.re ^ 2 + c.imI ^ 2 + c.imJ ^ 2 + c.imK ^ 2) := by
          rw [e2, norm_sq_eq_sum_sq]
        rw [norm_sq_eq_sum_sq]
        simp only [Quaternion.re_add, Quaternion.re_mul, Quaternion.imI_add, Quaternion.imJ_add,
          Quaternion.imK_add, hD, hbr, e4]
        ring
    · simp only [zero_smul, exp_zero, h0, mul_one, one_mul, List.map_cons, List.sum_cons, e1]
      set c := r.sum
      set D := R₂ 0
      set β := (r.map fun b => ‖b‖).sum
      have hc : ‖c‖ ≤ β := by
        clear_value D
        have : ∀ l : List ℍ[ℝ], ‖l.sum‖ ≤ (l.map fun b => ‖b‖).sum := by
          intro l
          induction l with
          | nil => simp
          | cons x t ih =>
            simp only [List.sum_cons, List.map_cons]
            exact (norm_add_le _ _).trans (add_le_add le_rfl ih)
        exact this r
      have hβ : 0 ≤ ‖c‖ := norm_nonneg _
      have h5 : ‖b * b + b * c + (b * c + D)‖ ≤ ‖b‖ * ‖b‖ + ‖b‖ * ‖c‖ + (‖b‖ * ‖c‖ + ‖D‖) := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans ?_) ((norm_add_le _ _).trans ?_))
        · rw [norm_mul, norm_mul]
        · rw [norm_mul]
      have h6 : ‖b‖ * ‖c‖ ≤ ‖b‖ * β := mul_le_mul_of_nonneg_left hc (norm_nonneg b)
      refine h5.trans ?_
      nlinarith
    · simp only [List.sum_cons, Quaternion.re_add, hbr, e4, add_zero]
theorem exp_adjointAction_mul (h : UnitQuaternion) (b : ℍ[ℝ]) :
    exp (_root_.YangMills.Construction.BlockAverages.adjointAction h b) * (h : ℍ[ℝ]) = (h : ℍ[ℝ]) * exp b := by
  have e : _root_.YangMills.Construction.BlockAverages.adjointAction h b = QuaternionLog.unitConj (h : ℍ[ℝ]) b := rfl
  rw [e, QuaternionLog.exp_unitConj (_root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion h)]
  simp only [QuaternionLog.unitConj, mul_assoc]
  rw [QuaternionLog.star_mul_self_of_norm_eq_one (_root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion h), mul_one]
theorem adjointAction_smul (g : UnitQuaternion) (t : ℝ) (b : ℍ[ℝ]) :
    _root_.YangMills.Construction.BlockAverages.adjointAction g (t • b) = t • _root_.YangMills.Construction.BlockAverages.adjointAction g b := by apply _root_.YangMills.Construction.BlockAverages.adjointAction_smul <;> assumption
theorem adjointAction_neg (g : UnitQuaternion) (b : ℍ[ℝ]) : _root_.YangMills.Construction.BlockAverages.adjointAction g (-b) = -_root_.YangMills.Construction.BlockAverages.adjointAction g b := by
  simp only [_root_.YangMills.Construction.BlockAverages.adjointAction]
  noncomm_ring
theorem adjointAction_add (g : UnitQuaternion) (a b : ℍ[ℝ]) :
    _root_.YangMills.Construction.BlockAverages.adjointAction g (a + b) = _root_.YangMills.Construction.BlockAverages.adjointAction g a + _root_.YangMills.Construction.BlockAverages.adjointAction g b := by apply _root_.YangMills.Construction.BlockAverages.adjointAction_add <;> assumption
theorem adjointAction_zero (g : UnitQuaternion) : _root_.YangMills.Construction.BlockAverages.adjointAction g 0 = 0 := by simp [_root_.YangMills.Construction.BlockAverages.adjointAction]
theorem sum_map_adjointAction (g : UnitQuaternion) (l : List ℍ[ℝ]) :
    (l.map (_root_.YangMills.Construction.BlockAverages.adjointAction g)).sum = _root_.YangMills.Construction.BlockAverages.adjointAction g l.sum := by
  induction l with
  | nil => simp [_root_.YangMills.Construction.BlockAverages.WilsonSecondVariation.adjointAction_zero]
  | cons x t ih => simp [_root_.YangMills.Construction.BlockAverages.WilsonSecondVariation.adjointAction_add, ih]
theorem expProduct_map_adjointAction_mul (g : UnitQuaternion) (bs : List ℍ[ℝ]) (τ : ℝ) :
    expProduct (bs.map (_root_.YangMills.Construction.BlockAverages.adjointAction g)) τ * (g : ℍ[ℝ]) = (g : ℍ[ℝ]) * expProduct bs τ := by
  induction bs with
  | nil => simp [expProduct_nil]
  | cons b r ih =>
    simp only [List.map_cons, expProduct_cons]
    rw [mul_assoc, ih, ← mul_assoc, ← _root_.YangMills.Construction.BlockAverages.WilsonSecondVariation.adjointAction_smul, exp_adjointAction_mul, mul_assoc]
variable {j : ℕ}
def transportedVariations (X : F.GaugeField j) (v : F.Site j → Fin 4 → imaginaryQuaternions) :
    F.Site j → List PathStep → List ℍ[ℝ]
  | _, [] => []
  | x, st :: r => linkValueVariation X v x st ::
      (transportedVariations X v (x + stepDisplacement j st) r).map (_root_.YangMills.Construction.BlockAverages.adjointAction (linkValue X x st))
theorem sum_transportedVariations (X : F.GaugeField j) (v : F.Site j → Fin 4 → imaginaryQuaternions)
    (l : List PathStep) : ∀ x, (transportedVariations X v x l).sum = pathHolonomyVariation X v x l := by
  induction l with
  | nil => intro x; rfl
  | cons st r ih =>
    intro x
    simp only [transportedVariations, pathHolonomyVariation, List.sum_cons, sum_map_adjointAction, ih]
theorem re_linkValueVariation (X : F.GaugeField j) (v : F.Site j → Fin 4 → imaginaryQuaternions)
    (x : F.Site j) (st : PathStep) : (linkValueVariation X v x st).re = 0 := by apply _root_.YangMills.Construction.BlockAverages.ChartFit.re_linkValueVariation <;> assumption
theorem re_transportedVariations (X : F.GaugeField j) (v : F.Site j → Fin 4 → imaginaryQuaternions)
    (l : List PathStep) : ∀ x, ∀ b ∈ transportedVariations X v x l, b.re = 0 := by
  induction l with
  | nil => intro x b hb; simp [transportedVariations] at hb
  | cons st r ih =>
    intro x b hb
    simp only [transportedVariations, List.mem_cons, List.mem_map] at hb
    rcases hb with rfl | ⟨a, ha, rfl⟩
    · exact re_linkValueVariation X v x st
    · exact re_adjointAction _ (ih _ a ha)
theorem inv_expUnit (u : imaginaryQuaternions) : ((expUnit u)⁻¹ : UnitQuaternion) = expUnit (-u) := by apply _root_.YangMills.Construction.LeastQuarticGauge.expUnit_inv <;> assumption
theorem linkValue_expRotatedField (X : F.GaugeField j) (v : F.Site j → Fin 4 → imaginaryQuaternions) (τ : ℝ)
    (x : F.Site j) (st : PathStep) :
    ((linkValue (expRotatedField (fun x i => τ • v x i) X) x st : UnitQuaternion) : ℍ[ℝ]) =
      exp (τ • linkValueVariation X v x st) * ((linkValue X x st : UnitQuaternion) : ℍ[ℝ]) := by
  unfold linkValue linkValueVariation
  by_cases h : st.2
  · simp only [h, if_true, expRotatedField]
    rfl
  · simp only [h, Bool.false_eq_true, if_false, expRotatedField, mul_inv_rev, inv_expUnit]
    set g := X (x - unitStep j st.1) st.1
    set u := v (x - unitStep j st.1) st.1
    have e : τ • -_root_.YangMills.Construction.BlockAverages.adjointAction g⁻¹ (u : ℍ[ℝ]) =
        _root_.YangMills.Construction.BlockAverages.adjointAction g⁻¹ (((-(τ • u) : imaginaryQuaternions)) : ℍ[ℝ]) := by
      rw [Submodule.coe_neg, Submodule.coe_smul, _root_.YangMills.Construction.BlockAverages.WilsonSecondVariation.adjointAction_neg, _root_.YangMills.Construction.BlockAverages.WilsonSecondVariation.adjointAction_smul, smul_neg]
    rw [e, exp_adjointAction_mul]
    rfl
theorem coe_unitQuaternion_mul (a b : UnitQuaternion) :
    ((a * b : UnitQuaternion) : ℍ[ℝ]) = (a : ℍ[ℝ]) * (b : ℍ[ℝ]) := rfl
theorem pathHolonomy_expRotatedField (X : F.GaugeField j) (v : F.Site j → Fin 4 → imaginaryQuaternions)
    (τ : ℝ) (l : List PathStep) :
    ∀ x, ((pathHolonomy (expRotatedField (fun x i => τ • v x i) X) x l : UnitQuaternion) : ℍ[ℝ]) =
      expProduct (transportedVariations X v x l) τ * ((pathHolonomy X x l : UnitQuaternion) : ℍ[ℝ]) := by
  induction l with
  | nil => intro x; simp [pathHolonomy, transportedVariations, expProduct_nil]
  | cons st r ih =>
    intro x
    simp only [pathHolonomy, transportedVariations, expProduct_cons]
    rw [coe_unitQuaternion_mul, linkValue_expRotatedField, ih, coe_unitQuaternion_mul]
    simp only [mul_assoc]
    rw [← mul_assoc (expProduct _ _), expProduct_map_adjointAction_mul]
    simp only [mul_assoc]
def bondsAlongPath : F.Site j → List PathStep → List (F.Site j × Fin 4)
  | _, [] => []
  | x, st :: r => (if st.2 then (x, st.1) else (x - unitStep j st.1, st.1)) ::
      bondsAlongPath (x + stepDisplacement j st) r
theorem norm_linkValueVariation (X : F.GaugeField j) (v : F.Site j → Fin 4 → imaginaryQuaternions)
    (x : F.Site j) (st : PathStep) :
    ‖linkValueVariation X v x st‖ =
      ‖v (if st.2 then (x, st.1) else (x - unitStep j st.1, st.1)).1
        (if st.2 then (x, st.1) else (x - unitStep j st.1, st.1)).2‖ := by apply _root_.YangMills.Construction.ChartSecondVariation.norm_linkValueVariation <;> assumption
theorem sum_norm_transportedVariations (X : F.GaugeField j)
    (v : F.Site j → Fin 4 → imaginaryQuaternions) (l : List PathStep) :
    ∀ x, ((transportedVariations X v x l).map fun b => ‖b‖).sum =
      ((bondsAlongPath x l).map fun b => ‖v b.1 b.2‖).sum := by
  induction l with
  | nil => intro x; rfl
  | cons st r ih =>
    intro x
    simp only [transportedVariations, bondsAlongPath, List.map_cons, List.sum_cons, List.map_map,
      norm_linkValueVariation]
    rw [← ih]
    congr 2
    refine List.map_congr_left fun b _ => ?_
    simp [norm_adjointAction]
def edge₁ (p : F.Site j × Fin 4 × Fin 4) : F.Site j × Fin 4 := (p.1, p.2.1)
def edge₂ (p : F.Site j × Fin 4 × Fin 4) : F.Site j × Fin 4 := (p.1 + unitStep j p.2.1, p.2.2)
def edge₃ (p : F.Site j × Fin 4 × Fin 4) : F.Site j × Fin 4 := (p.1 + unitStep j p.2.2, p.2.1)
def edge₄ (p : F.Site j × Fin 4 × Fin 4) : F.Site j × Fin 4 := (p.1, p.2.2)
theorem bondsAlongPath_boundary (p : F.Site j × Fin 4 × Fin 4) :
    bondsAlongPath p.1 [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] =
      [edge₁ p, edge₂ p, edge₃ p, edge₄ p] := by
  have e3 : p.1 + unitStep j p.2.1 + unitStep j p.2.2 - unitStep j p.2.1 = p.1 + unitStep j p.2.2 := by abel
  have e4 : p.1 + unitStep j p.2.1 + unitStep j p.2.2 + -unitStep j p.2.1 - unitStep j p.2.2 = p.1 := by abel
  simp [bondsAlongPath, stepDisplacement, edge₁, edge₂, edge₃, edge₄, e3, e4]
theorem sum_le_card_mul_sum_of_fibres {α β ι : Type} [Fintype ι] (P : Finset α) (B : Finset β)
    (f : α → β) (g : β → ℝ) (hg : ∀ b, 0 ≤ g b) (hm : ∀ p ∈ P, f p ∈ B) (r : α → ι)
    (hr : ∀ p ∈ P, ∀ q ∈ P, f p = f q → r p = r q → p = q) :
    ∑ p ∈ P, g (f p) ≤ Fintype.card ι * ∑ b ∈ B, g b := by apply _root_.YangMills.Construction.TopAverageCurl.sum_comp_le_card_mul_sum <;> assumption
theorem edges_mem_innerBonds (S : Finset F.Cell) {p : F.Site j × Fin 4 × Fin 4}
    (hp : p ∈ innerPlaquettes S j) :
    edge₁ p ∈ innerBonds S j ∧ edge₂ p ∈ innerBonds S j ∧ edge₃ p ∈ innerBonds S j ∧
      edge₄ p ∈ innerBonds S j := by apply _root_.YangMills.Construction.ChartSecondVariation.plaquetteEdges_mem_innerBonds <;> assumption
theorem sum_edges_le (S : Finset F.Cell) (g : F.Site j × Fin 4 → ℝ) (hg0 : ∀ b, 0 ≤ g b) :
    ∑ p ∈ innerPlaquettes S j, (g (edge₁ p) + g (edge₂ p) + g (edge₃ p) + g (edge₄ p)) ≤
      16 * ∑ b ∈ innerBonds S j, g b := by
  have s1 : ∑ p ∈ innerPlaquettes S j, g (edge₁ p) ≤ (Fintype.card (Fin 4)) * ∑ b ∈ innerBonds S j, g b :=
    sum_le_card_mul_sum_of_fibres _ _ edge₁ g hg0 (fun p hp => (edges_mem_innerBonds S hp).1)
      (fun p => p.2.2) (by
      rintro ⟨x, μ, ν⟩ _ ⟨x', μ', ν'⟩ _ h h'
      simp only [edge₁, Prod.mk.injEq] at h
      simp only at h'
      simp [h.1, h.2, h'])
  have s2 : ∑ p ∈ innerPlaquettes S j, g (edge₂ p) ≤ (Fintype.card (Fin 4)) * ∑ b ∈ innerBonds S j, g b :=
    sum_le_card_mul_sum_of_fibres _ _ edge₂ g hg0 (fun p hp => (edges_mem_innerBonds S hp).2.1)
      (fun p => p.2.1) (by
      rintro ⟨x, μ, ν⟩ _ ⟨x', μ', ν'⟩ _ h h'
      simp only [edge₂, Prod.mk.injEq] at h
      simp only at h'
      subst h'
      simp [add_right_cancel h.1, h.2])
  have s3 : ∑ p ∈ innerPlaquettes S j, g (edge₃ p) ≤ (Fintype.card (Fin 4)) * ∑ b ∈ innerBonds S j, g b :=
    sum_le_card_mul_sum_of_fibres _ _ edge₃ g hg0 (fun p hp => (edges_mem_innerBonds S hp).2.2.1)
      (fun p => p.2.2) (by
      rintro ⟨x, μ, ν⟩ _ ⟨x', μ', ν'⟩ _ h h'
      simp only [edge₃, Prod.mk.injEq] at h
      simp only at h'
      subst h'
      simp [add_right_cancel h.1, h.2])
  have s4 : ∑ p ∈ innerPlaquettes S j, g (edge₄ p) ≤ (Fintype.card (Fin 4)) * ∑ b ∈ innerBonds S j, g b :=
    sum_le_card_mul_sum_of_fibres _ _ edge₄ g hg0 (fun p hp => (edges_mem_innerBonds S hp).2.2.2)
      (fun p => p.2.1) (by
      rintro ⟨x, μ, ν⟩ _ ⟨x', μ', ν'⟩ _ h h'
      simp only [edge₄, Prod.mk.injEq] at h
      simp only at h'
      simp [h.1, h.2, h'])
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [Fintype.card_fin, Nat.cast_ofNat] at s1 s2 s3 s4
  linarith
theorem norm_list_sum_le (l : List ℍ[ℝ]) : ‖l.sum‖ ≤ (l.map fun b => ‖b‖).sum := by
  induction l with
  | nil => simp
  | cons x t ih =>
    simp only [List.sum_cons, List.map_cons]
    exact (norm_add_le _ _).trans (add_le_add le_rfl ih)
abbrev boundarySteps (p : F.Site j × Fin 4 × Fin 4) : List PathStep :=
  [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)]
theorem norm_variationCurl_le (X : F.GaugeField j) (v : F.Site j → Fin 4 → imaginaryQuaternions)
    (p : F.Site j × Fin 4 × Fin 4) :
    ‖variationCurl X v p‖ ≤ ((transportedVariations X v p.1 (boundarySteps p)).map fun b => ‖b‖).sum := by
  have hs : (transportedVariations X v p.1 (boundarySteps p)).sum = variationCurl X v p :=
    sum_transportedVariations X v _ p.1
  rw [← hs]
  exact norm_list_sum_le _
theorem plaquette_bounds (X : F.GaugeField j) (v : F.Site j → Fin 4 → imaginaryQuaternions)
    (p : F.Site j × Fin 4 × Fin 4)
    (σ : ℝ) (hp : plaquetteDefect X p ≤ σ) (R₁ R₂ : ℝ → ℍ[ℝ])
    (e1 : R₁ 0 = (transportedVariations X v p.1 (boundarySteps p)).sum)
    (e2 : (R₂ 0).re = -‖(transportedVariations X v p.1 (boundarySteps p)).sum‖ ^ 2)
    (e3 : ‖R₂ 0‖ ≤ ((transportedVariations X v p.1 (boundarySteps p)).map fun b => ‖b‖).sum ^ 2)
    (e4 : (transportedVariations X v p.1 (boundarySteps p)).sum.re = 0) (hσ : 0 ≤ σ) :
    ‖variationCurl X v p‖ ^ 2 - σ * (4 * (‖v (edge₁ p).1 (edge₁ p).2‖ ^ 2 + ‖v (edge₂ p).1 (edge₂ p).2‖ ^ 2 +
        ‖v (edge₃ p).1 (edge₃ p).2‖ ^ 2 + ‖v (edge₄ p).1 (edge₄ p).2‖ ^ 2)) ≤
      -(R₂ 0 * ((plaquetteHolonomy X p : UnitQuaternion) : ℍ[ℝ])).re ∧
    |(R₁ 0 * ((plaquetteHolonomy X p : UnitQuaternion) : ℍ[ℝ])).re| ≤
      σ * (‖v (edge₁ p).1 (edge₁ p).2‖ + ‖v (edge₂ p).1 (edge₂ p).2‖ +
        ‖v (edge₃ p).1 (edge₃ p).2‖ + ‖v (edge₄ p).1 (edge₄ p).2‖) := by
  have hs : (transportedVariations X v p.1 (boundarySteps p)).sum = variationCurl X v p :=
    sum_transportedVariations X v _ p.1
  have hn : ((transportedVariations X v p.1 (boundarySteps p)).map fun b => ‖b‖).sum =
      ‖v (edge₁ p).1 (edge₁ p).2‖ + (‖v (edge₂ p).1 (edge₂ p).2‖ +
        (‖v (edge₃ p).1 (edge₃ p).2‖ + ‖v (edge₄ p).1 (edge₄ p).2‖)) := by
    rw [sum_norm_transportedVariations, bondsAlongPath_boundary]
    simp
  rw [hs] at e1 e2 e4
  rw [hn] at e3
  set A := ‖v (edge₁ p).1 (edge₁ p).2‖ with hA
  set B := ‖v (edge₂ p).1 (edge₂ p).2‖ with hB
  set C := ‖v (edge₃ p).1 (edge₃ p).2‖ with hC
  set D := ‖v (edge₄ p).1 (edge₄ p).2‖ with hD
  set P := ((plaquetteHolonomy X p : UnitQuaternion) : ℍ[ℝ]) with hP
  have hcur : ‖P - 1‖ ≤ σ := hp
  have hsplit : ∀ q : ℍ[ℝ], (q * P).re = q.re + (q * (P - 1)).re := fun q => by
    rw [mul_sub, mul_one, ← Quaternion.re_add]
    congr 1
    abel
  have hb : ∀ q : ℍ[ℝ], |(q * (P - 1)).re| ≤ ‖q‖ * σ := fun q => by
    refine (abs_re_le_norm _).trans ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hcur (norm_nonneg _)
  constructor
  · rw [hsplit, e2]
    have h1 := (abs_le.1 (hb (R₂ 0))).2
    have h2 : ‖R₂ 0‖ * σ ≤ (A + (B + (C + D))) ^ 2 * σ := mul_le_mul_of_nonneg_right e3 hσ
    have h3 : (A + (B + (C + D))) ^ 2 ≤ 4 * (A ^ 2 + B ^ 2 + C ^ 2 + D ^ 2) := by
      nlinarith [sq_nonneg (A - B), sq_nonneg (A - C), sq_nonneg (A - D), sq_nonneg (B - C),
        sq_nonneg (B - D), sq_nonneg (C - D)]
    have h4 := mul_le_mul_of_nonneg_right h3 hσ
    linarith
  · rw [hsplit, e1, e4, zero_add]
    refine (hb _).trans ?_
    have h1 : ‖variationCurl X v p‖ ≤ A + (B + (C + D)) := by
      have := norm_variationCurl_le X v p
      rwa [hn] at this
    have := mul_le_mul_of_nonneg_right h1 hσ
    linarith
def bondSpreadCLM {k : ℕ} (c : Fin k → F.Site j × Fin 4) (y : F.Site j) (i : Fin 4) :
    (Fin k → imaginaryQuaternions) →L[ℝ] ℍ[ℝ] :=
  ∑ l, if c l = (y, i) then imaginaryQuaternions.subtypeL.comp (ContinuousLinearMap.proj l) else 0
theorem bondSpreadCLM_apply {k : ℕ} (c : Fin k → F.Site j × Fin 4) (y : F.Site j) (i : Fin 4)
    (ζ : Fin k → imaginaryQuaternions) :
    bondSpreadCLM c y i ζ = (((∑ l, if c l = (y, i) then ζ l else 0 : imaginaryQuaternions)) : ℍ[ℝ]) := by
  simp only [bondSpreadCLM, sum_apply]
  rw [Submodule.coe_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp
theorem analyticAt_exp_comp_clm {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (T : E →L[ℝ] ℍ[ℝ]) :
    AnalyticAt ℝ (fun ζ => exp (T ζ)) 0 :=
  (exp_analytic (𝕂 := ℝ) (T 0)).comp (T.analyticAt 0)
theorem analyticAt_linkValue {k : ℕ} (c : Fin k → F.Site j × Fin 4) (X : F.GaugeField j) (x : F.Site j)
    (st : PathStep) :
    AnalyticAt ℝ (fun ζ : Fin k → imaginaryQuaternions => ((linkValue (expRotatedField
      (fun y i => ∑ l, if c l = (y, i) then ζ l else 0) X) x st : UnitQuaternion) : ℍ[ℝ])) 0 := by
  unfold linkValue
  by_cases h : st.2
  · simp only [h, if_true, expRotatedField]
    have e : (fun ζ : Fin k → imaginaryQuaternions =>
        ((expUnit (∑ l, if c l = (x, st.1) then ζ l else 0) * X x st.1 : UnitQuaternion) : ℍ[ℝ])) =
        fun ζ => exp (bondSpreadCLM c x st.1 ζ) * ((X x st.1 : UnitQuaternion) : ℍ[ℝ]) := by
      funext ζ
      rw [bondSpreadCLM_apply]
      rfl
    rw [e]
    exact (analyticAt_exp_comp_clm _).mul analyticAt_const
  · simp only [h, Bool.false_eq_true, if_false, expRotatedField, mul_inv_rev, inv_expUnit]
    have e : (fun ζ : Fin k → imaginaryQuaternions => (((X (x - unitStep j st.1) st.1)⁻¹ *
        expUnit (-∑ l, if c l = (x - unitStep j st.1, st.1) then ζ l else 0) : UnitQuaternion) : ℍ[ℝ])) =
        fun ζ => (((X (x - unitStep j st.1) st.1)⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
          exp ((-bondSpreadCLM c (x - unitStep j st.1) st.1) ζ) := by
      funext ζ
      rw [neg_apply, bondSpreadCLM_apply, ← Submodule.coe_neg]
      rfl
    rw [e]
    exact analyticAt_const.mul (analyticAt_exp_comp_clm _)
theorem analyticAt_pathHolonomy {k : ℕ} (c : Fin k → F.Site j × Fin 4) (X : F.GaugeField j)
    (l : List PathStep) :
    ∀ x, AnalyticAt ℝ (fun ζ : Fin k → imaginaryQuaternions => ((pathHolonomy (expRotatedField
      (fun y i => ∑ l, if c l = (y, i) then ζ l else 0) X) x l : UnitQuaternion) : ℍ[ℝ])) 0 := by
  induction l with
  | nil =>
    intro x
    exact analyticAt_const
  | cons st r ih =>
    intro x
    exact (analyticAt_linkValue c X x st).mul (ih _)
theorem wilsonActionSecondVariation : wilsonActionSecondVariationStatement := by
  intro F S σ U hσ hcold
  refine ⟨fun k c => ?_, fun v => ?_⟩
  · unfold wilsonAction
    refine Finset.analyticAt_fun_sum _ fun p _ => ?_
    exact analyticAt_const.sub ((realPartCLM.analyticAt _).comp
      (analyticAt_pathHolonomy c U (boundarySteps p) p.1))
  · classical
    choose R₁ R₂ h1 h2 h0 e1 e2 e3 e4 using fun p : F.Site 0 × Fin 4 × Fin 4 =>
      expProduct_jets (transportedVariations U v p.1 (boundarySteps p)) (re_transportedVariations U v _ p.1)
    let g : F.Site 0 × Fin 4 × Fin 4 → ℍ[ℝ] := fun p => ((plaquetteHolonomy U p : UnitQuaternion) : ℍ[ℝ])
    have hval : (fun τ : ℝ => wilsonAction S (expRotatedField (fun x i => τ • v x i) U)) =
        fun τ : ℝ => ∑ p ∈ innerPlaquettes S 0,
          (1 - (expProduct (transportedVariations U v p.1 (boundarySteps p)) τ * g p).re) := by
      funext τ
      unfold wilsonAction
      refine Finset.sum_congr rfl fun p _ => ?_
      simp only [plaquetteHolonomy]
      rw [pathHolonomy_expRotatedField]
      rfl
    have hd1 : ∀ τ : ℝ, HasDerivAt
        (fun τ : ℝ => ∑ p ∈ innerPlaquettes S 0,
          (1 - (expProduct (transportedVariations U v p.1 (boundarySteps p)) τ * g p).re))
        (∑ p ∈ innerPlaquettes S 0, -(R₁ p τ * g p).re) τ := fun τ =>
      HasDerivAt.fun_sum fun p _ =>
        (realPartCLM.hasFDerivAt.comp_hasDerivAt τ ((h1 p τ).mul_const (g p))).const_sub 1
    have hd2 : ∀ τ : ℝ, HasDerivAt (fun τ : ℝ => ∑ p ∈ innerPlaquettes S 0, -(R₁ p τ * g p).re)
        (∑ p ∈ innerPlaquettes S 0, -(R₂ p τ * g p).re) τ := fun τ =>
      HasDerivAt.fun_sum fun p _ =>
        (realPartCLM.hasFDerivAt.comp_hasDerivAt τ ((h2 p τ).mul_const (g p))).neg
    have D1 : deriv (fun τ : ℝ => ∑ p ∈ innerPlaquettes S 0,
        (1 - (expProduct (transportedVariations U v p.1 (boundarySteps p)) τ * g p).re)) =
        fun τ : ℝ => ∑ p ∈ innerPlaquettes S 0, -(R₁ p τ * g p).re := funext fun τ => (hd1 τ).deriv
    rw [hval, D1, (hd2 0).deriv]
    have hper : ∀ p ∈ innerPlaquettes S 0, _ := fun p hp =>
      plaquette_bounds U v p σ (hcold p hp).le (R₁ p) (R₂ p) (e1 p) (e2 p) (e3 p) (e4 p) hσ.le
    have T2 := sum_edges_le S (fun b => ‖v b.1 b.2‖ ^ 2) fun b => by positivity
    have T1 := sum_edges_le S (fun b => ‖v b.1 b.2‖) fun b => norm_nonneg _
    constructor
    · have hs := Finset.sum_le_sum fun p hp => (hper p hp).1
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hs
      have := mul_le_mul_of_nonneg_left T2 hσ.le
      have e : (64 : ℝ) * σ * ∑ b ∈ innerBonds S 0, ‖v b.1 b.2‖ ^ 2 =
          4 * (σ * (16 * ∑ b ∈ innerBonds S 0, ‖v b.1 b.2‖ ^ 2)) := by ring
      rw [e]
      refine le_trans ?_ hs
      linarith
    · have hs := Finset.sum_le_sum fun p hp => (hper p hp).2
      rw [← Finset.mul_sum] at hs
      have := mul_le_mul_of_nonneg_left T1 hσ.le
      show |∑ p ∈ innerPlaquettes S 0, -(R₁ p 0 * g p).re| ≤ _
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      simp only [abs_neg]
      refine le_trans hs ?_
      linarith
end YangMills.Construction.BlockAverages.WilsonSecondVariation
end
