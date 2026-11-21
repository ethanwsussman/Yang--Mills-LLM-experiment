import YangMills.Construction.InfiniteLattice.SpaceOfConfigurationsOnTheInfiniteLatticeProof
import YangMills.Construction.InfiniteLattice.BondsAndTheirVariables
import YangMills.Construction.InfiniteLattice.FactsFromTopologyMeasureAndFunctionTheoryProof
import YangMills.Construction.InfiniteLattice.FactsOfTheBondsConfigurationsAndMotionsAtOneSpacingProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open InfiniteLattice Matrices
namespace CutoffLinks.LinksAndTheirVariables
variable {a : ℝ}
theorem axisStep_injective (ha : 0 < a) {μ ν : Fin 4} (h : axisStep a μ = axisStep a ν) : μ = ν := by
  by_contra hne
  have h₁ := congrFun (congrArg Subtype.val h) μ
  simp [axisStep, Pi.single_eq_of_ne hne] at h₁
  linarith
theorem forwardFrom_injective (ha : 0 < a) {x y : LatticePoint a} {μ ν : Fin 4}
    (h : Link.forwardFrom x μ = Link.forwardFrom y ν) : x = y ∧ μ = ν := by apply _root_.YangMills.Construction.InfiniteLattice.OneSpacing.forwardFrom_inj <;> assumption
theorem countable_link (a : ℝ) : Countable (Link a) := by apply _root_.YangMills.Construction.InfiniteLattice.WilsonOperator.countable_link <;> assumption
theorem countable_positiveLinks (a : ℝ) : (positiveLinkSet a).Countable := by apply _root_.YangMills.Construction.InfiniteLattice.GaugeFieldSpace.positiveLinks_countable <;> assumption
theorem continuous_eval_link (l : Link a) : Continuous fun U : GaugeField a => U l := by apply _root_.YangMills.Construction.ReflectionPositivity.RepresentativeCovariance.continuous_eval_link <;> assumption
theorem t2Space_gaugeField : T2Space (GaugeField a) :=
  inferInstanceAs (T2Space {U : Link a → ComplexMatrix2.specialUnitary // ∀ l, U l.opposite = (U l)⁻¹})
theorem isClosed_setOf_opposite_eq_inv :
    IsClosed {U : Link a → ComplexMatrix2.specialUnitary | ∀ l, U l.opposite = (U l)⁻¹} := by
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun l => isClosed_eq (continuous_apply _) (continuous_apply _).inv
theorem compactSpace_gaugeField : CompactSpace (GaugeField a) := by apply _root_.YangMills.SharedProofs.p823 <;> assumption
theorem secondCountable_specialUnitary : SecondCountableTopology ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.InfiniteLattice.WilsonOperator.secondCountable_specialUnitary <;> assumption
theorem metrizableSpace_pi_specialUnitary (ι : Type) [Countable ι] :
    TopologicalSpace.MetrizableSpace (ι → ComplexMatrix2.specialUnitary) := by apply _root_.YangMills.Construction.InfiniteLattice.AmbientFacts.Proofs.metrizableSpace_linkVariables <;> assumption
theorem metrizableSpace_gaugeField : TopologicalSpace.MetrizableSpace (GaugeField a) := by apply _root_.YangMills.Construction.InfiniteLattice.AmbientFacts.Proofs.metrizableSpace_gaugeField <;> assumption
theorem continuous_restrictField (S : Set (Link a)) :
    Continuous fun U : GaugeField a => restrictField U S :=
  continuous_pi fun l => continuous_eval_link (l : Link a)
theorem continuous_gluedField (ha : 0 < a) {S : Set (Link a)}
    (hS : S ⊆ positiveLinkSet a) :
    Continuous fun p : LinkVariables S × GaugeField a => gluedField ha hS p.1 p.2 := by apply _root_.YangMills.Construction.FixedSpacing.BasicFactsProof.continuous_gluedField <;> assumption
theorem restrictField_gluedField (ha : 0 < a) {S : Set (Link a)}
    (hS : S ⊆ positiveLinkSet a) (V : LinkVariables S) (ω : GaugeField a) :
    restrictField (gluedField ha hS V ω) S = V :=
  funext fun l => gluedField_apply_of_mem ha hS V ω l
theorem bijective_restrictField_positiveLinks (ha : 0 < a) :
    Function.Bijective fun U : GaugeField a => restrictField U (positiveLinkSet a) := by
  constructor
  · intro U U' h
    have h₀ : restrictField U (positiveLinkSet a) =
        restrictField U' (positiveLinkSet a) := h
    have e₁ := eq_gluedField ha subset_rfl (restrictField U' _) (trivialField a) U
      (fun l => congrFun h₀ l) (fun l hl => absurd hl.1 hl.2)
    have e₂ := eq_gluedField ha subset_rfl (restrictField U' _) (trivialField a) U'
      (fun _ => rfl) (fun l hl => absurd hl.1 hl.2)
    exact e₁.trans e₂.symm
  · intro Y
    exact ⟨gluedField ha subset_rfl Y (trivialField a),
      restrictField_gluedField ha subset_rfl Y _⟩
theorem variablesDist_nonneg {S : Set (Link a)} (V V' : LinkVariables S) :
    0 ≤ variablesDist V V' :=
  Real.iSup_nonneg fun _ => norm_nonneg _
theorem le_variablesDist {S : Set (Link a)} [Finite S] (V V' : LinkVariables S) (l : S) :
    ComplexMatrix2.operatorNorm ((V l : ComplexMatrix2) - (V' l : ComplexMatrix2)) ≤ variablesDist V V' :=
  le_ciSup (f := fun l : S => ComplexMatrix2.operatorNorm ((V l : ComplexMatrix2) - (V' l : ComplexMatrix2)))
    (Set.finite_range _).bddAbove l
theorem variablesDist_le {S : Set (Link a)} {V V' : LinkVariables S} {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ l : S, ComplexMatrix2.operatorNorm ((V l : ComplexMatrix2) - (V' l : ComplexMatrix2)) ≤ r) :
    variablesDist V V' ≤ r :=
  Real.iSup_le h hr
theorem exists_metricSpace_dist_eq {S : Set (Link a)} (hS : S.Finite) :
    ∃ m : MetricSpace (LinkVariables S),
      (∀ V V' : LinkVariables S, m.dist V V' = variablesDist V V') ∧
      m.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace (LinkVariables S)) := by
  have : Fintype S := hS.fintype
  have : Finite S := hS
  refine ⟨inferInstance, fun V V' => le_antisymm ?_ ?_, rfl⟩
  · refine (dist_pi_le_iff (variablesDist_nonneg V V')).2 fun l => ?_
    rw [Subtype.dist_eq, dist_eq_norm]
    exact le_variablesDist V V' l
  · refine variablesDist_le dist_nonneg fun l => ?_
    have h := dist_le_pi_dist V V' l
    rw [Subtype.dist_eq, dist_eq_norm] at h
    exact h
theorem variablesUnionHomeomorph_symm_apply_left {S S' : Set (Link a)} (h : Disjoint S S')
    (P : LinkVariables S × LinkVariables S') (l : S) :
    (variablesUnionHomeomorph h).symm P ⟨l, Or.inl l.2⟩ = P.1 l :=
  congrFun (congrArg Prod.fst ((variablesUnionHomeomorph h).apply_symm_apply P)) l
theorem variablesUnionHomeomorph_symm_apply_right {S S' : Set (Link a)} (h : Disjoint S S')
    (P : LinkVariables S × LinkVariables S') (l : S') :
    (variablesUnionHomeomorph h).symm P ⟨l, Or.inr l.2⟩ = P.2 l :=
  congrFun (congrArg Prod.snd ((variablesUnionHomeomorph h).apply_symm_apply P)) l
theorem variablesDist_eq_max_restrict {S S' : Set (Link a)} [Finite S] [Finite S']
    (Z Z' : LinkVariables ↥(S ∪ S')) :
    variablesDist Z Z' =
      max (variablesDist (restrictVariables subset_union_left Z) (restrictVariables subset_union_left Z'))
        (variablesDist (restrictVariables subset_union_right Z)
          (restrictVariables subset_union_right Z')) := by
  apply le_antisymm
  · refine variablesDist_le (le_max_of_le_left (variablesDist_nonneg _ _)) ?_
    rintro ⟨l, hl | hl⟩
    · exact le_max_of_le_left (le_variablesDist (restrictVariables subset_union_left Z)
        (restrictVariables subset_union_left Z') ⟨l, hl⟩)
    · exact le_max_of_le_right (le_variablesDist (restrictVariables subset_union_right Z)
        (restrictVariables subset_union_right Z') ⟨l, hl⟩)
  · refine max_le (variablesDist_le (variablesDist_nonneg _ _) fun l => ?_)
      (variablesDist_le (variablesDist_nonneg _ _) fun l => ?_)
    · exact le_variablesDist Z Z' (Set.inclusion subset_union_left l)
    · exact le_variablesDist Z Z' (Set.inclusion subset_union_right l)
theorem variablesDist_union {S S' : Set (Link a)} [Finite S] [Finite S'] (h : Disjoint S S')
    (V V' : LinkVariables S) (Y Y' : LinkVariables S') :
    variablesDist ((variablesUnionHomeomorph h).symm (V, Y))
        ((variablesUnionHomeomorph h).symm (V', Y')) =
      max (variablesDist V V') (variablesDist Y Y') := by
  have e₁ : restrictVariables subset_union_left ((variablesUnionHomeomorph h).symm (V, Y)) = V :=
    congrArg Prod.fst ((variablesUnionHomeomorph h).apply_symm_apply (V, Y))
  have e₂ : restrictVariables subset_union_left ((variablesUnionHomeomorph h).symm (V', Y')) = V' :=
    congrArg Prod.fst ((variablesUnionHomeomorph h).apply_symm_apply (V', Y'))
  have e₃ : restrictVariables subset_union_right ((variablesUnionHomeomorph h).symm (V, Y)) = Y :=
    congrArg Prod.snd ((variablesUnionHomeomorph h).apply_symm_apply (V, Y))
  have e₄ : restrictVariables subset_union_right ((variablesUnionHomeomorph h).symm (V', Y')) = Y' :=
    congrArg Prod.snd ((variablesUnionHomeomorph h).apply_symm_apply (V', Y'))
  rw [variablesDist_eq_max_restrict, e₁, e₂, e₃, e₄]
theorem haarMeasure_eq_pi (ι : Type) [Fintype ι] :
    LinkVariables.haarMeasure ι = Measure.pi fun _ : ι => ComplexMatrix2.haarProb :=
  Measure.infinitePi_eq_pi _
theorem map_variablesUnionHomeomorph_haarMeasure {S S' : Set (Link a)} [Finite S] [Finite S']
    (h : Disjoint S S') :
    (LinkVariables.haarMeasure ↥(S ∪ S')).map (variablesUnionHomeomorph h) =
      (LinkVariables.haarMeasure S).prod (LinkVariables.haarMeasure S') := by
  classical
  have := Fintype.ofFinite S
  have := Fintype.ofFinite S'
  have := Fintype.ofFinite ↥(S ∪ S')
  rw [haarMeasure_eq_pi, haarMeasure_eq_pi, haarMeasure_eq_pi]
  have := secondCountable_specialUnitary
  have hm : Measurable (variablesUnionHomeomorph h) :=
    (variablesUnionHomeomorph h).continuous.measurable
  have hm' : Measurable (variablesUnionHomeomorph h).symm :=
    (variablesUnionHomeomorph h).symm.continuous.measurable
  have key : ((Measure.pi fun _ : S => ComplexMatrix2.haarProb).prod
      (Measure.pi fun _ : S' => ComplexMatrix2.haarProb)).map (variablesUnionHomeomorph h).symm =
      Measure.pi fun _ : ↥(S ∪ S') => ComplexMatrix2.haarProb := by
    symm
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.map_apply hm' (MeasurableSet.univ_pi hs)]
    have e : (variablesUnionHomeomorph h).symm ⁻¹' (Set.pi univ s) =
        (Set.pi univ fun l : S => s ⟨l, Or.inl l.2⟩) ×ˢ
          (Set.pi univ fun l : S' => s ⟨l, Or.inr l.2⟩) := by
      ext P
      constructor
      · intro hP
        refine ⟨fun l _ => ?_, fun l _ => ?_⟩
        · have := hP ⟨l, Or.inl l.2⟩ (mem_univ _)
          rwa [variablesUnionHomeomorph_symm_apply_left] at this
        · have := hP ⟨l, Or.inr l.2⟩ (mem_univ _)
          rwa [variablesUnionHomeomorph_symm_apply_right] at this
      · rintro ⟨h₁, h₂⟩ ⟨l, hl | hl⟩ _
        · have := h₁ ⟨l, hl⟩ (mem_univ _)
          rw [← variablesUnionHomeomorph_symm_apply_left h] at this
          exact this
        · have := h₂ ⟨l, hl⟩ (mem_univ _)
          rw [← variablesUnionHomeomorph_symm_apply_right h] at this
          exact this
    rw [e, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi,
      ← Equiv.prod_comp (Equiv.Set.union h).symm, Fintype.prod_sum_type]
    rfl
  rw [← key, Measure.map_map hm hm']
  simp
theorem statement_holds : Statement := by
  intro d
  have ha := d.spacing_pos
  have := countable_link d.spacing
  have : CompactSpace (GaugeField d.spacing) := compactSpace_gaugeField
  have : T2Space (GaugeField d.spacing) := t2Space_gaugeField
  have hext : ∀ {S : Set (Link d.spacing)} (hS : S ⊆ d.links), Continuous (d.extendByOne hS) :=
    fun hS => (continuous_gluedField ha hS).comp
      (continuous_id.prodMk continuous_const)
  have hre : ∀ {S : Set (Link d.spacing)} (hS : S ⊆ d.links) (V : LinkVariables S),
      restrictField (d.extendByOne hS V) S = V :=
    fun hS V => restrictField_gluedField ha hS V _
  have hfac : ∀ {E : Type} {S : Set (Link d.spacing)} (hS : S ⊆ d.links) (F : GaugeField d.spacing → E)
      (f : LinkVariables S → E), (∀ U, F U = f (restrictField U S)) →
      f = F ∘ d.extendByOne hS := fun hS F f hf => funext fun V => by
    change f V = F (d.extendByOne hS V)
    rw [hf, hre]
  refine ⟨⟨fun l => ?_, fun x y μ ν h => forwardFrom_injective ha h,
    countable_positiveLinks d.spacing⟩, ⟨?_, compactSpace_gaugeField,
    metrizableSpace_gaugeField, inferInstance, ?_⟩, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · rcases xor_mem_positiveLinks ha l with ⟨h, hn⟩ | ⟨h, hn⟩
    · refine Or.inl ⟨h, ?_⟩
      rintro ⟨l', hl', rfl⟩
      exact hn (by rwa [Link.opposite_opposite])
    · exact Or.inr ⟨⟨l.opposite, h, (Link.opposite_opposite l).symm⟩, hn⟩
  · exact isHomeomorph_iff_continuous_bijective.2
      ⟨continuous_restrictField _, bijective_restrictField_positiveLinks ha⟩
  · have : Countable d.links := (countable_positiveLinks d.spacing).to_subtype
    exact metrizableSpace_pi_specialUnitary _
  · intro S hS E _ F hF
    obtain ⟨f, hf⟩ := hF
    refine ⟨⟨f, hf, fun f' hf' => (hfac hS F f' hf').trans (hfac hS F f hf).symm⟩,
      fun f' hf' => ⟨hfac hS F f' hf', fun hc => ?_⟩⟩
    rw [hfac hS F f' hf']
    exact hc.comp (hext hS)
  · intro S hS hfin
    ext F
    constructor
    · rintro ⟨⟨hc, -⟩, f, hf⟩
      refine ⟨f, ?_, funext hf⟩
      change Continuous f
      rw [hfac hS F f hf]
      exact hc.comp (hext hS)
    · rintro ⟨f, hf, rfl⟩
      have hc : Continuous (liftToFields f) :=
        Continuous.comp (show Continuous f from hf) (continuous_restrictField S)
      exact ⟨⟨hc, S, hfin, hS, f, fun _ => rfl⟩, f, fun _ => rfl⟩
  · intro S _ hfin
    have : Finite S := hfin
    exact ⟨exists_metricSpace_dist_eq hfin, inferInstance⟩
  · intro S S' _ _ _ _ h
    exact ⟨fun V V' Y Y' => variablesDist_union h V V' Y Y',
      map_variablesUnionHomeomorph_haarMeasure h⟩
  · intro S hS
    refine ⟨continuous_restrictField S, hext hS, hre hS, fun W hW _ => ⟨?_, ?_, ?_⟩⟩
    · exact continuous_gluedField ha hW
    · exact fun V U => restrictField_gluedField ha hW V U
    · intro hSW V U
      refine funext fun l => ?_
      have hl : (l : Link d.spacing) ∉ W := fun hl =>
        (Set.eq_empty_iff_forall_notMem.mp hSW l) ⟨l.2, hl⟩
      exact d.replaceOn_of_notMem hW V U ⟨hS l.2, hl⟩
end CutoffLinks.LinksAndTheirVariables
end YangMills.Construction
