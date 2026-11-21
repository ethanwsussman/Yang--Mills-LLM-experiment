import YangMills.Construction.InfiniteLattice.FunctionsOfSomeOfTheBondsAndClassesStableUnderBoundedLimits
import YangMills.Construction.InfiniteLattice.OperatorsOfTheWilsonSpecification
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Set
open scoped Topology
noncomputable section
namespace YangMills.Construction
open InfiniteLattice FieldsAtSpacing Matrices
namespace InfiniteLattice.ConditionalAverageProof
variable {a : ℝ}
theorem secondCountable_specialUnitary : SecondCountableTopology ComplexMatrix2.specialUnitary :=
  have : SecondCountableTopology ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  TopologicalSpace.Subtype.secondCountableTopology _
attribute [local instance] secondCountable_specialUnitary
theorem secondCountable_gaugeField (a : ℝ) : SecondCountableTopology (GaugeField a) :=
  have : SecondCountableTopology (Link a → ComplexMatrix2.specialUnitary) := inferInstance
  TopologicalSpace.Subtype.secondCountableTopology
    (fun U : Link a → ComplexMatrix2.specialUnitary => ∀ e, U e.opposite = (U e)⁻¹)
attribute [local instance] secondCountable_gaugeField
theorem isProbabilityMeasure_haarProd (L : LinkWindow a) : IsProbabilityMeasure L.haarProd := by
  unfold LinkWindow.haarProd ComplexMatrix2.haarPi
  infer_instance
attribute [local instance] isProbabilityMeasure_haarProd
theorem norm_le_supNorm {F : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    (U : GaugeField a) : ‖F U‖ ≤ observableSupNorm F := by
  obtain ⟨C, hC⟩ := hF.2
  exact le_ciSup (f := fun U => ‖F U‖) ⟨C, by rintro _ ⟨U, rfl⟩; exact hC U⟩ U
theorem supNorm_nonneg {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) :
    0 ≤ observableSupNorm F :=
  (norm_nonneg _).trans (norm_le_supNorm hF (trivialField a))
section Glue
variable (L : LinkWindow a) (ha : 0 < a)
theorem glue_of_mem (V : L.Assignments) (ξ : GaugeField a) {e : Link a} (h : e ∈ L.links) :
    L.glue ha V ξ e = V ⟨e, h⟩ :=
  dif_pos h
theorem glue_of_opposite_mem (V : L.Assignments) (ξ : GaugeField a) {e : Link a}
    (h : e ∉ L.links) (h' : e.opposite ∈ L.links) : L.glue ha V ξ e = (V ⟨e.opposite, h'⟩)⁻¹ :=
  (dif_neg h).trans (dif_pos h')
theorem glue_of_not_mem (V : L.Assignments) (ξ : GaugeField a) {e : Link a} (h : e ∉ L.links)
    (h' : e.opposite ∉ L.links) : L.glue ha V ξ e = ξ e :=
  (dif_neg h).trans (dif_neg h')
theorem glue_of_positive (V : L.Assignments) (ξ : GaugeField a) {e : Link a}
    (he : e ∈ positiveLinkSet a) (h : e ∉ L.links) : L.glue ha V ξ e = ξ e :=
  glue_of_not_mem L ha V ξ h fun h' =>
    Link.opposite_not_isPositivelyOriented ha (mem_positiveLinks_iff.1 he) (L.isPositive _ h')
theorem glue_apply_eq (V : L.Assignments) {ξ ξ' : GaugeField a} {e : Link a}
    (he : e ∈ positiveLinkSet a) (h : e ∉ L.links → ξ e = ξ' e) :
    L.glue ha V ξ e = L.glue ha V ξ' e := by
  by_cases hL : e ∈ L.links
  · rw [glue_of_mem L ha V ξ hL, glue_of_mem L ha V ξ' hL]
  · rw [glue_of_positive L ha V ξ he hL, glue_of_positive L ha V ξ' he hL, h hL]
theorem gaugeField_ext {U U' : GaugeField a}
    (h : ∀ e ∈ positiveLinkSet a, U e = U' e) : U = U' := by
  refine Subtype.ext (funext fun e => ?_)
  rcases mem_positiveLinks_or_opposite_mem e with he | he
  · exact h e he
  · have h₁ := U.2 e.opposite
    have h₂ := U'.2 e.opposite
    rw [Link.opposite_opposite] at h₁ h₂
    rw [h₁, h₂, h _ he]
theorem glue_eq_of_agree (V : L.Assignments) {ξ ξ' : GaugeField a}
    (h : ∀ e ∈ positiveLinkSet a \ (L.links : Set (Link a)), ξ e = ξ' e) :
    L.glue ha V ξ = L.glue ha V ξ' :=
  gaugeField_ext fun e he => glue_apply_eq L ha V he fun hL => h e ⟨he, hL⟩
theorem continuous_glue :
    Continuous fun q : GaugeField a × L.Assignments => L.glue ha q.2 q.1 := by
  have hval : ∀ e : Link a, Continuous fun U : GaugeField a => U e := fun e =>
    (continuous_apply e).comp continuous_subtype_val
  have h : Continuous fun q : GaugeField a × L.Assignments =>
      ((L.glue ha q.2 q.1).1 : Link a → ComplexMatrix2.specialUnitary) := by
    refine continuous_pi fun e => ?_
    by_cases h₁ : e ∈ L.links
    · have : (fun q : GaugeField a × L.Assignments => (L.glue ha q.2 q.1).1 e) =
          fun q => q.2 ⟨e, h₁⟩ := funext fun q => glue_of_mem L ha q.2 q.1 h₁
      rw [this]
      exact (continuous_apply _).comp continuous_snd
    · by_cases h₂ : e.opposite ∈ L.links
      · have : (fun q : GaugeField a × L.Assignments => (L.glue ha q.2 q.1).1 e) =
            fun q => (q.2 ⟨e.opposite, h₂⟩)⁻¹ :=
          funext fun q => glue_of_opposite_mem L ha q.2 q.1 h₁ h₂
        rw [this]
        exact ((continuous_apply _).comp continuous_snd).inv
      · have : (fun q : GaugeField a × L.Assignments => (L.glue ha q.2 q.1).1 e) =
            fun q => q.1 e := funext fun q => glue_of_not_mem L ha q.2 q.1 h₁ h₂
        rw [this]
        exact (hval e).comp continuous_fst
  exact h.subtype_mk fun q => (L.glue ha q.2 q.1).2
end Glue
theorem faces_finite (L : LinkWindow a) : L.faces.Finite := by
  let T : Set (LatticePoint a) := ⋃ e ∈ (L.links : Set (Link a)),
    ({e.initial} ∪ Set.range fun κ : Fin 4 => e.initial - axisStep a κ)
  have hT : T.Finite :=
    L.links.finite_toSet.biUnion fun e _ => (Set.finite_singleton _).union (Set.finite_range _)
  have hfin : (T ×ˢ (Set.univ : Set (Fin 4 × Fin 4))).Finite := hT.prod Set.finite_univ
  refine (hfin.preimage (f := fun p : ElementaryPlaquette a => (p.corner, p.lowAxis, p.highAxis))
    ?_).subset ?_
  · intro p _ q _ h
    simp only [Prod.mk.injEq] at h
    exact ElementaryPlaquette.ext h.1 h.2.1 h.2.2
  · rintro p ⟨e, he, heL⟩
    have heL' : e ∈ (L.links : Set (Link a)) := heL
    refine ⟨?_, Set.mem_univ _⟩
    have hin : ∀ x : LatticePoint a, (x = e.initial ∨ ∃ κ, e.initial - axisStep a κ = x) →
        x ∈ T := by
      rintro x (hx | hx)
      · exact Set.mem_iUnion₂.2 ⟨e, heL', Or.inl hx⟩
      · exact Set.mem_iUnion₂.2 ⟨e, heL', Or.inr hx⟩
    simp only [ElementaryPlaquette.edges, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact hin _ (Or.inl rfl)
    · exact hin _ (Or.inr ⟨p.lowAxis, by simp [Link.forwardFrom]⟩)
    · exact hin _ (Or.inr ⟨p.highAxis, by simp [Link.forwardFrom]⟩)
    · exact hin _ (Or.inl rfl)
theorem windowAction_eq_sum (L : LinkWindow a) (hfin : L.faces.Finite) (U : GaugeField a) :
    L.windowAction U = ∑ p ∈ hfin.toFinset, faceEnergy U p :=
  finsum_mem_eq_finite_toFinset_sum _ hfin
theorem faceEnergy_congr {U U' : GaugeField a} {p : ElementaryPlaquette a}
    (h : ∀ e ∈ p.edges, U e = U' e) : faceEnergy U p = faceEnergy U' p := by
  have h₁ := h (Link.forwardFrom p.corner p.lowAxis) (by simp [ElementaryPlaquette.edges])
  have h₂ := h (Link.forwardFrom (p.corner + axisStep a p.lowAxis) p.highAxis)
    (by simp [ElementaryPlaquette.edges])
  have h₃ := h (Link.forwardFrom (p.corner + axisStep a p.highAxis) p.lowAxis)
    (by simp [ElementaryPlaquette.edges])
  have h₄ := h (Link.forwardFrom p.corner p.highAxis) (by simp [ElementaryPlaquette.edges])
  unfold faceEnergy faceHolonomy
  rw [h₁, h₂, h₃, h₄]
theorem edges_mem_positiveLinks {p : ElementaryPlaquette a} {e : Link a} (he : e ∈ p.edges) :
    e ∈ positiveLinkSet a := by
  simp only [ElementaryPlaquette.edges, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl⟩
section Weight
variable (hr : LinkFunctionsStatement) (ha : 0 < a) (L : LinkWindow a)
include hr ha
theorem faceFacts : FaceFunctionProperties a :=
  (hr a ha ∅ (Set.empty_subset _)).2.2.2.2.2
theorem continuous_faceEnergy (p : ElementaryPlaquette a) :
    Continuous fun U : GaugeField a => faceEnergy U p := by
  have h : Continuous (faceFunction p) := ((faceFacts hr ha).1 p).1.1
  have h' := Complex.continuous_re.comp h
  refine h'.congr fun U => ?_
  simp [faceFunction]
theorem continuous_windowAction : Continuous L.windowAction := by
  have hfin := faces_finite L
  have h : L.windowAction = fun U : GaugeField a => ∑ p ∈ hfin.toFinset, faceEnergy U p :=
    funext (windowAction_eq_sum L hfin)
  rw [h]
  exact continuous_finsetSum _ fun p _ => continuous_faceEnergy hr ha p
theorem windowAction_bounds (U : GaugeField a) :
    0 ≤ L.windowAction U ∧ L.windowAction U ≤ 2 * L.faceCount := by
  have hfin := faces_finite L
  have hb := fun p => ((faceFacts hr ha).1 p).2.1 U
  rw [windowAction_eq_sum L hfin]
  refine ⟨Finset.sum_nonneg fun p _ => (hb p).1, ?_⟩
  calc ∑ p ∈ hfin.toFinset, faceEnergy U p ≤ ∑ _p ∈ hfin.toFinset, (2 : ℝ) :=
        Finset.sum_le_sum fun p _ => (hb p).2
    _ = 2 * L.faceCount := by
        rw [Finset.sum_const, nsmul_eq_mul, LinkWindow.faceCount,
          Set.ncard_eq_toFinset_card _ hfin, mul_comm]
variable {β : ℝ}
theorem denominatorIntegrand_bounds (hβ : 0 < β) (ξ : GaugeField a) (V : L.Assignments) :
    denominatorLowerBound β L.faceCount ≤ L.denominatorIntegrand ha β ξ V ∧
      L.denominatorIntegrand ha β ξ V ≤ 1 := by
  obtain ⟨h₀, h₂⟩ := windowAction_bounds hr ha L (L.glue ha V ξ)
  unfold denominatorLowerBound LinkWindow.denominatorIntegrand
  constructor
  · refine Real.exp_le_exp.2 ?_
    nlinarith [mul_le_mul_of_nonneg_left h₂ hβ.le]
  · refine Real.exp_le_one_iff.2 ?_
    nlinarith [mul_nonneg hβ.le h₀]
variable (β) in
theorem continuous_denominatorIntegrand :
    Continuous fun q : GaugeField a × L.Assignments => L.denominatorIntegrand ha β q.1 q.2 :=
  Real.continuous_exp.comp
    (continuous_const.mul ((continuous_windowAction hr ha L).comp (continuous_glue L ha)))
end Weight
theorem norm_numeratorIntegrand_le (ha : 0 < a) (L : LinkWindow a) {F : GaugeField a → ℂ}
    (hF : IsBoundedObservable F) (β : ℝ) (ξ : GaugeField a) (V : L.Assignments) :
    ‖L.numeratorIntegrand ha β F ξ V‖ ≤
      observableSupNorm F * L.denominatorIntegrand ha β ξ V := by
  unfold LinkWindow.numeratorIntegrand LinkWindow.denominatorIntegrand
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact mul_le_mul_of_nonneg_right (norm_le_supNorm hF _) (Real.exp_pos _).le
theorem denominatorIntegrand_nonneg (ha : 0 < a) (L : LinkWindow a) (β : ℝ) (ξ : GaugeField a)
    (V : L.Assignments) : 0 ≤ L.denominatorIntegrand ha β ξ V :=
  (Real.exp_pos _).le
section Operator
variable (hr : LinkFunctionsStatement) (ha : 0 < a) (L : LinkWindow a) {β : ℝ}
include hr
theorem measurable_numeratorIntegrand {F : GaugeField a → ℂ} (hF : Measurable F) (β : ℝ) :
    Measurable fun q : GaugeField a × L.Assignments => L.numeratorIntegrand ha β F q.1 q.2 := by
  have h₁ : Measurable fun q : GaugeField a × L.Assignments => F (L.glue ha q.2 q.1) :=
    hF.comp (continuous_glue L ha).measurable
  have h₂ : Measurable fun q : GaugeField a × L.Assignments =>
      ((L.denominatorIntegrand ha β q.1 q.2 : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (continuous_denominatorIntegrand hr ha L β).measurable
  exact h₁.mul h₂
variable (hβ : 0 < β)
include hβ
theorem integrable_denominatorIntegrand (ξ : GaugeField a) :
    Integrable (L.denominatorIntegrand ha β ξ) L.haarProd := by
  have hm : Measurable (L.denominatorIntegrand ha β ξ) := by
    have h := (continuous_denominatorIntegrand hr ha L β).comp
      (Continuous.prodMk (f := fun _ : L.Assignments => ξ) (g := fun V => V) continuous_const
        continuous_id)
    exact h.measurable
  have hbd : ∀ V, ‖L.denominatorIntegrand ha β ξ V‖ ≤ 1 := fun V => by
    rw [Real.norm_of_nonneg (denominatorIntegrand_nonneg ha L β ξ V)]
    exact (denominatorIntegrand_bounds hr ha L hβ ξ V).2
  exact Integrable.of_bound hm.aestronglyMeasurable 1 (ae_of_all _ hbd)
theorem norm_numeratorIntegrand_le_of_le {F : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    {C : ℝ} (hC : observableSupNorm F ≤ C) (ξ : GaugeField a) (V : L.Assignments) :
    ‖L.numeratorIntegrand ha β F ξ V‖ ≤ C :=
  calc ‖L.numeratorIntegrand ha β F ξ V‖
      ≤ observableSupNorm F * L.denominatorIntegrand ha β ξ V :=
        norm_numeratorIntegrand_le ha L hF β ξ V
    _ ≤ observableSupNorm F * 1 :=
        mul_le_mul_of_nonneg_left (denominatorIntegrand_bounds hr ha L hβ ξ V).2
          (supNorm_nonneg hF)
    _ ≤ C := by rwa [mul_one]
theorem integrable_numeratorIntegrand {F : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    (ξ : GaugeField a) : Integrable (L.numeratorIntegrand ha β F ξ) L.haarProd := by
  have hm : Measurable (L.numeratorIntegrand ha β F ξ) :=
    (measurable_numeratorIntegrand hr ha L hF.1 β).comp measurable_prodMk_left
  exact Integrable.of_bound hm.aestronglyMeasurable (observableSupNorm F)
    (ae_of_all _ fun V => norm_numeratorIntegrand_le_of_le hr ha L hβ hF le_rfl ξ V)
theorem partitionDenominator_bounds (ξ : GaugeField a) :
    denominatorLowerBound β L.faceCount ≤ L.partitionDenominator ha β ξ ∧
      L.partitionDenominator ha β ξ ≤ 1 := by
  have hint := integrable_denominatorIntegrand hr ha L hβ ξ
  have hb := denominatorIntegrand_bounds hr ha L hβ ξ
  constructor
  · calc denominatorLowerBound β L.faceCount
        = ∫ _V, denominatorLowerBound β L.faceCount ∂L.haarProd := by simp
      _ ≤ L.partitionDenominator ha β ξ :=
          integral_mono (integrable_const _) hint fun V => (hb V).1
  · calc L.partitionDenominator ha β ξ ≤ ∫ _V, (1 : ℝ) ∂L.haarProd :=
          integral_mono hint (integrable_const _) fun V => (hb V).2
      _ = 1 := by simp
theorem partitionDenominator_pos (ξ : GaugeField a) : 0 < L.partitionDenominator ha β ξ :=
  lt_of_lt_of_le (Real.exp_pos _) (partitionDenominator_bounds hr ha L hβ ξ).1
theorem norm_conditionalAverage_le {F : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    (ξ : GaugeField a) : ‖L.conditionalAverage ha β F ξ‖ ≤ observableSupNorm F := by
  have hpos := partitionDenominator_pos hr ha L hβ ξ
  rw [L.conditionalAverage_eq_div, norm_div, Complex.norm_real,
    Real.norm_of_nonneg hpos.le, div_le_iff₀ hpos]
  calc ‖∫ V, L.numeratorIntegrand ha β F ξ V ∂L.haarProd‖
      ≤ ∫ V, ‖L.numeratorIntegrand ha β F ξ V‖ ∂L.haarProd :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ V, observableSupNorm F * L.denominatorIntegrand ha β ξ V ∂L.haarProd :=
        integral_mono (integrable_numeratorIntegrand hr ha L hβ hF ξ).norm
          ((integrable_denominatorIntegrand hr ha L hβ ξ).const_mul _)
          fun V => norm_numeratorIntegrand_le ha L hF β ξ V
    _ = observableSupNorm F * L.partitionDenominator ha β ξ := integral_const_mul _ _
theorem isBoundedObservable_conditionalAverage {F : GaugeField a → ℂ}
    (hF : IsBoundedObservable F) : IsBoundedObservable (L.conditionalAverage ha β F) := by
  refine ⟨?_, observableSupNorm F, norm_conditionalAverage_le hr ha L hβ hF⟩
  have hN : Measurable fun ξ => ∫ V, L.numeratorIntegrand ha β F ξ V ∂L.haarProd :=
    (StronglyMeasurable.integral_prod_right' (ν := L.haarProd)
      (measurable_numeratorIntegrand hr ha L hF.1 β).stronglyMeasurable).measurable
  have hD : Measurable fun ξ => L.partitionDenominator ha β ξ :=
    (StronglyMeasurable.integral_prod_right' (ν := L.haarProd)
      (continuous_denominatorIntegrand hr ha L β).measurable.stronglyMeasurable).measurable
  exact hN.div (Complex.measurable_ofReal.comp hD)
theorem isBlindTo_conditionalAverage {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) :
    IsBlindTo (L.links : Set (Link a)) (L.conditionalAverage ha β F) := by
  have hsub : positiveLinkSet a \ (L.links : Set (Link a)) ⊆ positiveLinkSet a :=
    sdiff_subset
  have hT := ((hr a ha _ hsub).2.1 _ (isBoundedObservable_conditionalAverage hr ha L hβ hF)).1
  refine (hT.out 1 0).1 ?_
  intro ξ ξ' h
  have hV : ∀ V, L.glue ha V ξ = L.glue ha V ξ' := fun V => glue_eq_of_agree L ha V h
  simp only [LinkWindow.conditionalAverage, hV]
omit hβ in
theorem conditionalAverage_mul {F H : GaugeField a → ℂ} (hH : IsBoundedObservable H)
    (hHr : IsBlindTo (L.links : Set (Link a)) H) :
    L.conditionalAverage ha β (H * F) = H * L.conditionalAverage ha β F := by
  have hsub : positiveLinkSet a \ (L.links : Set (Link a)) ⊆ positiveLinkSet a :=
    sdiff_subset
  have hT := ((hr a ha _ hsub).2.1 H hH).1
  have hag : FieldsAtSpacing.DependsOnlyOnLinks (positiveLinkSet a \ (L.links : Set (Link a))) H :=
    (hT.out 0 1).1 hHr
  funext ξ
  have hV : ∀ V, H (L.glue ha V ξ) = H ξ := fun V =>
    hag _ _ fun e he => glue_of_positive L ha V ξ he.1 he.2
  have hN : ∀ V, L.numeratorIntegrand ha β (H * F) ξ V =
      H ξ * L.numeratorIntegrand ha β F ξ V := fun V => by
    simp only [LinkWindow.numeratorIntegrand, Pi.mul_apply, hV, mul_assoc]
  rw [Pi.mul_apply, L.conditionalAverage_eq_div, L.conditionalAverage_eq_div]
  simp only [hN]
  rw [integral_const_mul, mul_div_assoc]
theorem conditionalAverage_add {F H : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    (hH : IsBoundedObservable H) :
    L.conditionalAverage ha β (F + H) =
      L.conditionalAverage ha β F + L.conditionalAverage ha β H := by
  funext ξ
  have hN : ∀ V, L.numeratorIntegrand ha β (F + H) ξ V =
      L.numeratorIntegrand ha β F ξ V + L.numeratorIntegrand ha β H ξ V := fun V => by
    simp only [LinkWindow.numeratorIntegrand, Pi.add_apply, add_mul]
  rw [Pi.add_apply, L.conditionalAverage_eq_div, L.conditionalAverage_eq_div,
    L.conditionalAverage_eq_div]
  simp only [hN]
  rw [integral_add (integrable_numeratorIntegrand hr ha L hβ hF ξ)
    (integrable_numeratorIntegrand hr ha L hβ hH ξ), add_div]
omit hr hβ in
theorem conditionalAverage_smul (F : GaugeField a → ℂ) (z : ℂ) :
    L.conditionalAverage ha β (z • F) = z • L.conditionalAverage ha β F := by
  funext ξ
  have hN : ∀ V, L.numeratorIntegrand ha β (z • F) ξ V =
      z * L.numeratorIntegrand ha β F ξ V := fun V => by
    simp only [LinkWindow.numeratorIntegrand, Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [Pi.smul_apply, L.conditionalAverage_eq_div, L.conditionalAverage_eq_div, smul_eq_mul]
  simp only [hN]
  rw [integral_const_mul, mul_div_assoc]
theorem conditionalAverage_one : L.conditionalAverage ha β 1 = 1 := by
  funext ξ
  have hpos := partitionDenominator_pos hr ha L hβ ξ
  have hN : ∀ V, L.numeratorIntegrand ha β 1 ξ V =
      ((L.denominatorIntegrand ha β ξ V : ℝ) : ℂ) := fun V => by
    simp [LinkWindow.numeratorIntegrand, LinkWindow.denominatorIntegrand]
  rw [L.conditionalAverage_eq_div, Pi.one_apply]
  simp only [hN]
  rw [integral_complex_ofReal]
  exact div_self (by exact_mod_cast hpos.ne')
theorem conditionalAverage_tendsto {F : GaugeField a → ℂ} (Fs : ℕ → GaugeField a → ℂ)
    (hFs : ∀ n, IsBoundedObservable (Fs n))
    (hb : BddAbove (Set.range fun n => observableSupNorm (Fs n)))
    (hlim : ∀ U, Tendsto (fun n => Fs n U) atTop (𝓝 (F U))) (ξ : GaugeField a) :
    Tendsto (fun n => L.conditionalAverage ha β (Fs n) ξ) atTop
      (𝓝 (L.conditionalAverage ha β F ξ)) := by
  obtain ⟨C, hC⟩ := hb
  have hCn : ∀ n, observableSupNorm (Fs n) ≤ C := fun n => hC ⟨n, rfl⟩
  simp only [L.conditionalAverage_eq_div]
  refine Tendsto.div_const ?_ _
  refine tendsto_integral_of_dominated_convergence (fun _ => C)
    (fun n => (integrable_numeratorIntegrand hr ha L hβ (hFs n) ξ).aestronglyMeasurable)
    (integrable_const _)
    (fun n => ae_of_all _ fun V =>
      norm_numeratorIntegrand_le_of_le hr ha L hβ (hFs n) (hCn n) ξ V)
    (ae_of_all _ fun V => ?_)
  exact (hlim _).mul_const _
theorem continuous_conditionalAverage {F : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    (hFc : Continuous F) : Continuous (L.conditionalAverage ha β F) := by
  have hpair : ∀ V : L.Assignments, Continuous fun ξ : GaugeField a => (ξ, V) := fun V =>
    Continuous.prodMk (f := fun ξ : GaugeField a => ξ) (g := fun _ => V) continuous_id
      continuous_const
  have hgl : ∀ V : L.Assignments, Continuous fun ξ : GaugeField a => L.glue ha V ξ := fun V => by
    have h := (continuous_glue L ha).comp (hpair V)
    exact h
  have hDI : ∀ V : L.Assignments, Continuous fun ξ : GaugeField a =>
      L.denominatorIntegrand ha β ξ V := fun V => by
    have h := (continuous_denominatorIntegrand hr ha L β).comp (hpair V)
    exact h
  have hNc : Continuous fun ξ => ∫ V, L.numeratorIntegrand ha β F ξ V ∂L.haarProd := by
    have hc : ∀ V : L.Assignments, Continuous fun ξ : GaugeField a =>
        L.numeratorIntegrand ha β F ξ V := fun V => by
      have h := (hFc.comp (hgl V)).mul (Complex.continuous_ofReal.comp (hDI V))
      exact h
    exact continuous_of_dominated (bound := fun _ => observableSupNorm F)
      (fun ξ => (integrable_numeratorIntegrand hr ha L hβ hF ξ).aestronglyMeasurable)
      (fun ξ => ae_of_all _ fun V => norm_numeratorIntegrand_le_of_le hr ha L hβ hF le_rfl ξ V)
      (integrable_const _) (ae_of_all _ hc)
  have hDc : Continuous fun ξ => L.partitionDenominator ha β ξ := by
    have hbd : ∀ (ξ : GaugeField a) (V : L.Assignments),
        ‖L.denominatorIntegrand ha β ξ V‖ ≤ 1 := fun ξ V => by
      rw [Real.norm_of_nonneg (denominatorIntegrand_nonneg ha L β ξ V)]
      exact (denominatorIntegrand_bounds hr ha L hβ ξ V).2
    exact continuous_of_dominated (bound := fun _ => (1 : ℝ))
      (fun ξ => (integrable_denominatorIntegrand hr ha L hβ ξ).aestronglyMeasurable)
      (fun ξ => ae_of_all _ (hbd ξ)) (integrable_const _) (ae_of_all _ hDI)
  have h : L.conditionalAverage ha β F = fun ξ =>
      (∫ V, L.numeratorIntegrand ha β F ξ V ∂L.haarProd) /
        (L.partitionDenominator ha β ξ : ℂ) :=
    funext (L.conditionalAverage_eq_div ha β F)
  rw [h]
  exact hNc.div (Complex.continuous_ofReal.comp hDc) fun ξ => by
    exact_mod_cast (partitionDenominator_pos hr ha L hβ ξ).ne'
omit hr hβ in
theorem dependsOnlyOnLinks_conditionalAverage {F : GaugeField a → ℂ} {S G : Set (Link a)}
    {f : LinkVariables S → ℂ} (hFf : ∀ U, F U = f (linkRestriction S U)) (hSG : S ⊆ G)
    (hpos : G ⊆ positiveLinkSet a)
    (hside : ∀ p ∈ L.faces, ∀ e ∈ p.edges, e ∈ G) :
    FieldsAtSpacing.DependsOnlyOnLinks (G \ (L.links : Set (Link a)))
      (L.conditionalAverage ha β F) := by
  intro ξ ξ' h
  have hfinP := faces_finite L
  have hag : ∀ (V : L.Assignments), ∀ e ∈ G, L.glue ha V ξ e = L.glue ha V ξ' e :=
    fun V e he => glue_apply_eq L ha V (hpos he) fun hL => h e ⟨he, hL⟩
  have h₁ : ∀ V, F (L.glue ha V ξ) = F (L.glue ha V ξ') := fun V => by
    rw [hFf (L.glue ha V ξ), hFf (L.glue ha V ξ')]
    congr 1
    funext e
    exact hag V e (hSG e.2)
  have h₂ : ∀ V, L.windowAction (L.glue ha V ξ) = L.windowAction (L.glue ha V ξ') := fun V => by
    rw [windowAction_eq_sum L hfinP, windowAction_eq_sum L hfinP]
    exact Finset.sum_congr rfl fun p hp => faceEnergy_congr fun e he =>
      hag V e (hside p (hfinP.mem_toFinset.1 hp) e he)
  simp only [LinkWindow.conditionalAverage, h₁, h₂]
theorem conditionalAverage_mem {F : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    (hC : F ∈ continuousFiniteLinkFunctions a) :
    L.conditionalAverage ha β F ∈ continuousFiniteLinkFunctions a := by
  obtain ⟨hFc, S, hfin, hsub, f, -, hFf⟩ := hC
  have hop : Continuous (L.conditionalAverage ha β F) :=
    continuous_conditionalAverage hr ha L hβ hF hFc
  have hfinP := faces_finite L
  obtain ⟨G, hG⟩ : ∃ G : Set (Link a), G = S ∪ ⋃ p ∈ L.faces, {e | e ∈ p.edges} :=
    ⟨_, rfl⟩
  have hfinG : G.Finite := by
    rw [hG]
    exact hfin.union (hfinP.biUnion fun p _ => p.edges.finite_toSet)
  have hpos : G ⊆ positiveLinkSet a := by
    rw [hG]
    rintro e (he | he)
    · exact hsub he
    · obtain ⟨p, -, hp⟩ := Set.mem_iUnion₂.1 he
      exact edges_mem_positiveLinks hp
  have hSG : S ⊆ G := by
    rw [hG]
    exact subset_union_left
  have hside : ∀ p ∈ L.faces, ∀ e ∈ p.edges, e ∈ G := fun p hp e he => by
    rw [hG]
    exact Or.inr (Set.mem_iUnion₂.2 ⟨p, hp, he⟩)
  have hsub' : G \ (L.links : Set (Link a)) ⊆ positiveLinkSet a :=
    sdiff_subset.trans hpos
  have hT := (hr a ha _ hsub').2.1 _ (isBoundedObservable_conditionalAverage hr ha L hβ hF)
  obtain ⟨f', hf'⟩ := (hT.1.out 1 2).1 (dependsOnlyOnLinks_conditionalAverage ha L hFf hSG hpos hside)
  exact ⟨hop, _, hfinG.subset sdiff_subset, hsub', f', (hT.2 f' hf').2.2 hop,
    fun U => congrFun hf'.2.2 U⟩
end Operator
theorem claim_holds (hr : LinkFunctionsStatement) : ConditionalAverageProperties.claim := by
  intro a ha β hβ L F H hF hH
  refine ⟨⟨faces_finite L, Real.exp_pos _, fun ξ =>
      ⟨integrable_numeratorIntegrand hr ha L hβ hF ξ,
        integrable_denominatorIntegrand hr ha L hβ ξ,
        (partitionDenominator_bounds hr ha L hβ ξ).1,
        (partitionDenominator_bounds hr ha L hβ ξ).2⟩⟩,
    ⟨isBoundedObservable_conditionalAverage hr ha L hβ hF,
      isBlindTo_conditionalAverage hr ha L hβ hF⟩,
    ?_, fun hHr => conditionalAverage_mul hr ha L hH hHr,
    conditionalAverage_mem hr ha L hβ hF,
    conditionalAverage_add hr ha L hβ hF hH,
    fun z => conditionalAverage_smul ha L F z,
    conditionalAverage_one hr ha L hβ,
    fun Fs hFs hb hlim ξ => conditionalAverage_tendsto hr ha L hβ Fs hFs hb hlim ξ⟩
  have : Nonempty (GaugeField a) := ⟨trivialField a⟩
  exact ciSup_le (norm_conditionalAverage_le hr ha L hβ hF)
end InfiniteLattice.ConditionalAverageProof
end YangMills.Construction
