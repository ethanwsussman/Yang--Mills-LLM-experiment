import YangMills.Construction.InfiniteLattice.ConfigurationsFunctionsAndMeasures
import YangMills.Construction.InfiniteLattice.LinkSupportAndRegionObservables
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open MeasureTheory Set InfiniteLattice GibbsAtFixedSpacing
noncomputable section
namespace FieldsAtSpacing
variable {a : ℝ}
def IsBoundedLocal (F : GaugeField a → ℂ) : Prop :=
  ∃ S : Set AmbientSpace, Bornology.IsBounded S ∧ F ∈ boundedRegionObservables a S
theorem isBoundedLocal_iff (F : GaugeField a → ℂ) :
    IsBoundedLocal F ↔ IsBoundedObservable F ∧ IsLocalObservable F := by
  constructor
  · rintro ⟨S, hS, hObs, hMeas⟩
    exact ⟨hObs, S, hS, hMeas⟩
  · rintro ⟨hObs, S, hS, hMeas⟩
    exact ⟨S, hS, hObs, hMeas⟩
def IsBlindTo (B : Set (Link a)) (F : GaugeField a → ℂ) : Prop :=
  Measurable[linkSigma (positiveLinkSet a \ B)] F
def linkRestriction (B : Set (Link a)) (U : GaugeField a) : LinkVariables B :=
  restrictField U B
def glueOnLinks (ha : 0 < a) {B : Set (Link a)} (hB : B ⊆ positiveLinkSet a)
    (g : LinkVariables B) (h : LinkVariables ↥(positiveLinkSet a \ B)) : GaugeField a :=
  gluedField ha hB g (gluedField ha sdiff_subset h (trivialField a))
theorem glueOnLinks_apply_of_mem (ha : 0 < a) {B : Set (Link a)} (hB : B ⊆ positiveLinkSet a)
    (g : LinkVariables B) (h : LinkVariables ↥(positiveLinkSet a \ B)) (b : B) :
    glueOnLinks ha hB g h b = g b :=
  gluedField_apply_of_mem ha hB g _ b
theorem glueOnLinks_apply_of_mem_diff (ha : 0 < a) {B : Set (Link a)}
    (hB : B ⊆ positiveLinkSet a) (g : LinkVariables B)
    (h : LinkVariables ↥(positiveLinkSet a \ B))
    (b : ↥(positiveLinkSet a \ B)) : glueOnLinks ha hB g h b = h b :=
  (gluedField_apply_of_notMem ha hB g _ b.2).trans (gluedField_apply_of_mem ha sdiff_subset h _ b)
def continuousSubalgebra (a : ℝ) : Subalgebra ℂ (GaugeField a → ℂ) where
  carrier := continuousFns a
  mul_mem' hF hG := Continuous.mul hF hG
  add_mem' hF hG := Continuous.add hF hG
  algebraMap_mem' _ := continuous_const
def continuousFiniteLinkFunctions (a : ℝ) : Set (GaugeField a → ℂ) :=
  {F | F ∈ continuousSubalgebra a ∧
    ∃ B : Set (Link a), B.Finite ∧ B ⊆ positiveLinkSet a ∧
      ∃ f : LinkVariables B → ℂ, Continuous f ∧ ∀ U, F U = f (linkRestriction B U)}
end FieldsAtSpacing
end
end YangMills.Construction
