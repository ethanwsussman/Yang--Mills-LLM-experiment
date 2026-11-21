import YangMills.Construction.InfiniteLattice.HyperoctahedralMotionsAndCubes
import YangMills.Construction.InfiniteLattice.ImagesOfBondsAndInvariantMeasuresOnATorus
import YangMills.Construction.InfiniteLattice.OneLatticeAtOneSpacing
import YangMills.Construction.InfiniteLattice.ToriOfAnyShapeArraysAndPerturbedMeasures
import YangMills.Construction.Matrices.FunctionsAndOperatorsOfSeveralVariablesOnG
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
def HasFullRank (H : AddSubgroup AmbientSpace) : Prop :=
  ∃ v : Fin 4 → AmbientSpace, (∀ i, v i ∈ H) ∧ LinearIndependent ℝ v
namespace Link
variable {a : ℝ}
theorem initial_shiftBy (e : Link a) (g : LatticePoint a) : (e.shiftBy g).initial = e.initial + g :=
  rfl
theorem terminal_shiftBy (e : Link a) (g : LatticePoint a) : (e.shiftBy g).terminal = e.terminal + g :=
  rfl
theorem shiftBy_zero (e : Link a) : e.shiftBy 0 = e :=
  Link.ext (add_zero _) (add_zero _)
theorem shiftBy_shiftBy (e : Link a) (g g' : LatticePoint a) :
    (e.shiftBy g).shiftBy g' = e.shiftBy (g + g') :=
  Link.ext (add_assoc _ _ _) (add_assoc _ _ _)
theorem shiftBy_opposite (e : Link a) (g : LatticePoint a) :
    (e.shiftBy g).opposite = e.opposite.shiftBy g :=
  rfl
theorem isPositivelyOriented_shiftBy_iff (e : Link a) (g : LatticePoint a) :
    (e.shiftBy g).IsPositivelyOriented ↔ e.IsPositivelyOriented := by
  simp only [IsPositivelyOriented, initial_shiftBy, terminal_shiftBy, add_sub_add_right_eq_sub]
end Link
namespace PeriodSublattice
variable (L : PeriodSublattice 1)
theorem hasFullRank : HasFullRank (L.periods.map (latticeSubgroup 1).subtype) := by
  obtain ⟨v, hv, hl⟩ := L.exists_linearIndependent
  exact ⟨fun i => (v i : AmbientSpace), fun i => ⟨v i, hv i, rfl⟩, hl⟩
theorem quotientMap_add_period (x : LatticePoint 1) {g : LatticePoint 1} (hg : g ∈ L.periods) :
    L.quotientMap (x + g) = L.quotientMap x := by
  have h : L.quotientMap g = 0 := (QuotientAddGroup.eq_zero_iff g).2 hg
  rw [map_add, h, add_zero]
def orientedOrbit (e : Link 1) : Set (Link 1) :=
  {e' | ∃ g ∈ L.periods, e' = e.shiftBy g}
abbrev OrientedLink : Type := Set.range L.orientedOrbit
def orientedClass (e : Link 1) : L.OrientedLink := ⟨L.orientedOrbit e, e, rfl⟩
theorem self_mem_orientedOrbit (e : Link 1) : e ∈ L.orientedOrbit e :=
  ⟨0, zero_mem _, e.shiftBy_zero.symm⟩
theorem orientedClass_shiftBy (e : Link 1) {g : LatticePoint 1} (hg : g ∈ L.periods) :
    L.orientedClass (e.shiftBy g) = L.orientedClass e := by
  refine Subtype.ext (Set.ext fun e' => ⟨?_, ?_⟩)
  · rintro ⟨g', hg', rfl⟩
    exact ⟨g + g', add_mem hg hg', e.shiftBy_shiftBy g g'⟩
  · rintro ⟨g', hg', rfl⟩
    refine ⟨-g + g', add_mem (neg_mem hg) hg', ?_⟩
    rw [Link.shiftBy_shiftBy, add_neg_cancel_left]
theorem mem_orientedOrbit_of_orientedClass_eq {e e' : Link 1}
    (h : L.orientedClass e = L.orientedClass e') : e' ∈ L.orientedOrbit e := by
  have h' : L.orientedOrbit e = L.orientedOrbit e' := congrArg Subtype.val h
  rw [h']
  exact L.self_mem_orientedOrbit e'
theorem orientedLink_nonempty (c : L.OrientedLink) : (c : Set (Link 1)).Nonempty := by
  obtain ⟨_, e, rfl⟩ := c
  exact ⟨e, L.self_mem_orientedOrbit e⟩
def orientedRep (c : L.OrientedLink) : Link 1 :=
  (L.orientedLink_nonempty c).some
theorem exists_orientedRep_eq (e : Link 1) :
    ∃ g ∈ L.periods, L.orientedRep (L.orientedClass e) = e.shiftBy g :=
  (L.orientedLink_nonempty (L.orientedClass e)).some_mem
theorem orientedClass_orientedRep (c : L.OrientedLink) :
    L.orientedClass (L.orientedRep c) = c := by
  obtain ⟨_, e, rfl⟩ := c
  obtain ⟨g, hg, h⟩ := L.exists_orientedRep_eq e
  change L.orientedClass (L.orientedRep (L.orientedClass e)) = L.orientedClass e
  rw [h, L.orientedClass_shiftBy e hg]
def OrientedIsPositive (c : L.OrientedLink) : Prop := (L.orientedRep c).IsPositivelyOriented
theorem orientedIsPositive_orientedClass_iff (e : Link 1) :
    L.OrientedIsPositive (L.orientedClass e) ↔ e.IsPositivelyOriented := by
  obtain ⟨g, -, h⟩ := L.exists_orientedRep_eq e
  rw [OrientedIsPositive, h, Link.isPositivelyOriented_shiftBy_iff]
def sourcePoint (c : L.OrientedLink) : L.QuotientTorus :=
  L.quotientMap (L.orientedRep c).initial
def targetPoint (c : L.OrientedLink) : L.QuotientTorus :=
  L.quotientMap (L.orientedRep c).terminal
theorem sourcePoint_orientedClass (e : Link 1) :
    L.sourcePoint (L.orientedClass e) = L.quotientMap e.initial := by
  obtain ⟨g, hg, h⟩ := L.exists_orientedRep_eq e
  rw [sourcePoint, h]
  exact L.quotientMap_add_period e.initial hg
theorem targetPoint_orientedClass (e : Link 1) :
    L.targetPoint (L.orientedClass e) = L.quotientMap e.terminal := by
  obtain ⟨g, hg, h⟩ := L.exists_orientedRep_eq e
  rw [targetPoint, h]
  exact L.quotientMap_add_period e.terminal hg
def oppositeOriented (c : L.OrientedLink) : L.OrientedLink :=
  L.orientedClass (L.orientedRep c).opposite
theorem oppositeOriented_orientedClass (e : Link 1) :
    L.oppositeOriented (L.orientedClass e) = L.orientedClass e.opposite := by
  obtain ⟨g, hg, h⟩ := L.exists_orientedRep_eq e
  rw [oppositeOriented, h, Link.shiftBy_opposite, L.orientedClass_shiftBy _ hg]
theorem linkClass_translate (e : PositiveLink 1) {g : LatticePoint 1} (hg : g ∈ L.periods) :
    L.linkClass (e.translate g) = L.linkClass e := by
  refine Subtype.ext (Set.ext fun e' => ⟨?_, ?_⟩)
  · rintro ⟨g', hg', rfl⟩
    exact ⟨g + g', add_mem hg hg', Subtype.ext (e.1.shiftBy_shiftBy g g')⟩
  · rintro ⟨g', hg', rfl⟩
    refine ⟨-g + g', add_mem (neg_mem hg) hg', Subtype.ext ?_⟩
    change e.1.shiftBy g' = (e.1.shiftBy g).shiftBy (-g + g')
    rw [Link.shiftBy_shiftBy, add_neg_cancel_left]
theorem exists_linkRep_eq (e : PositiveLink 1) :
    ∃ g ∈ L.periods, L.linkRep (L.linkClass e) = e.translate g :=
  (L.quotientLink_nonempty (L.linkClass e)).some_mem
theorem linkClass_linkRep (c : L.QuotientLink) :
    L.linkClass (L.linkRep c) = c := by
  obtain ⟨_, e, rfl⟩ := c
  obtain ⟨g, hg, h⟩ := L.exists_linkRep_eq e
  change L.linkClass (L.linkRep (L.linkClass e)) = L.linkClass e
  rw [h, L.linkClass_translate e hg]
def orientedOfLink (c : L.QuotientLink) : L.OrientedLink :=
  L.orientedClass (L.linkRep c).1
theorem orientedOfLink_linkClass (e : PositiveLink 1) :
    L.orientedOfLink (L.linkClass e) = L.orientedClass e.1 := by
  obtain ⟨g, hg, h⟩ := L.exists_linkRep_eq e
  rw [orientedOfLink, h]
  exact L.orientedClass_shiftBy e.1 hg
theorem orientedOfLink_injective : Function.Injective L.orientedOfLink := by
  intro c c' h
  obtain ⟨g, hg, he⟩ := L.mem_orientedOrbit_of_orientedClass_eq h
  have he' : L.linkRep c' = (L.linkRep c).translate g := Subtype.ext he
  rw [← L.linkClass_linkRep c, ← L.linkClass_linkRep c', he', L.linkClass_translate _ hg]
theorem range_orientedOfLink :
    Set.range L.orientedOfLink = {c | L.OrientedIsPositive c} := by
  ext c
  constructor
  · rintro ⟨c', rfl⟩
    exact (L.orientedIsPositive_orientedClass_iff _).2 (L.linkRep c').2
  · intro h
    refine ⟨L.linkClass ⟨L.orientedRep c, h⟩, ?_⟩
    rw [L.orientedOfLink_linkClass]
    exact L.orientedClass_orientedRep c
theorem linkEndpoints_eq (c : L.QuotientLink) :
    L.linkEndpoints c = {L.sourcePoint (L.orientedOfLink c), L.targetPoint (L.orientedOfLink c)} := by
  rw [linkEndpoints, orientedOfLink, sourcePoint_orientedClass, targetPoint_orientedClass]
def IsLiftOfPlaquette (p : ElementaryPlaquette 1) (P : L.QuotientPlaquette) : Prop :=
  p ∈ (P : Set (ElementaryPlaquette 1))
def PlaquetteLiesInPlane (P : L.QuotientPlaquette) (μ ν : Fin 4) : Prop :=
  ∀ p, L.IsLiftOfPlaquette p P → p.LiesInPlane μ ν
theorem liftValue_shiftBy (U : L.QuotientField) (e : Link 1) {g : LatticePoint 1}
    (hg : g ∈ L.periods) : L.liftValue U (e.shiftBy g) = L.liftValue U e := by
  have pos : ∀ e' : PositiveLink 1,
      L.liftValue U (e'.1.shiftBy g) = L.liftValue U e'.1 := fun e' => by
    have h₁ := L.lift_apply_positive U (e'.translate g)
    have h₂ := L.lift_apply_positive U e'
    rw [L.linkClass_translate e' hg, ← h₂] at h₁
    exact h₁
  by_cases h : e.IsPositivelyOriented
  · exact pos ⟨e, h⟩
  · have hr := pos ⟨e.opposite, isPositivelyOriented_opposite_of_not h⟩
    change L.liftValue U (e.opposite.shiftBy g) = L.liftValue U e.opposite at hr
    rw [← Link.shiftBy_opposite, L.liftValue_opposite, L.liftValue_opposite] at hr
    exact inv_injective hr
def orientedValue (U : L.QuotientField) (c : L.OrientedLink) : Matrices.ComplexMatrix2.specialUnitary :=
  L.liftValue U (L.orientedRep c)
theorem orientedValue_orientedClass (U : L.QuotientField) (e : Link 1) :
    L.orientedValue U (L.orientedClass e) = L.liftValue U e := by
  obtain ⟨g, hg, h⟩ := L.exists_orientedRep_eq e
  rw [orientedValue, h, L.liftValue_shiftBy U e hg]
theorem orientedValue_positive (U : L.QuotientField) (e : PositiveLink 1) :
    L.orientedValue U (L.orientedClass e.1) = U (L.linkClass e) := by
  rw [orientedValue_orientedClass]
  exact L.lift_apply_positive U e
theorem orientedValue_opposite (U : L.QuotientField) (e : PositiveLink 1) :
    L.orientedValue U (L.orientedClass e.1.opposite) = (U (L.linkClass e))⁻¹ := by
  rw [orientedValue_orientedClass, L.liftValue_opposite]
  exact congrArg (·⁻¹) (L.lift_apply_positive U e)
instance borelSpace_quotientField : BorelSpace L.QuotientField := inferInstance
variable {L}
def supNorm {E : Type*} [Norm E] (F : L.QuotientField → E) : ℝ := ⨆ U, ‖F U‖
def DependsOnlyOn {E : Type*} (F : L.QuotientField → E) (S : Set L.QuotientLink) : Prop :=
  ∀ U U' : L.QuotientField, (∀ e ∈ S, U e = U' e) → F U = F U'
def PreservesFiniteMeasure (φ : L.QuotientField → L.QuotientField)
    (μ : Measure L.QuotientField) : Prop :=
  Measurable φ ∧ IsFiniteMeasure μ ∧
    ∀ F : L.QuotientField → ℂ, Measurable F → (∃ C : ℝ, ∀ U, ‖F U‖ ≤ C) →
      ∫ U, F (φ U) ∂μ = ∫ U, F U ∂μ
end PeriodSublattice
end InfiniteLattice
end YangMills.Construction
