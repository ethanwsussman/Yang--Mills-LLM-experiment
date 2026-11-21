import YangMills.Construction.InfiniteLattice.ConfigurationsFunctionsAndMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction
open InfiniteLattice
namespace GibbsAtFixedSpacing
variable {a : ℝ}
theorem hasNoOppositePairs_of_subset_positiveLinks (ha : 0 < a) {L : Set (Link a)}
    (hL : L ⊆ positiveLinkSet a) : HasNoOppositePairs L :=
  fun _ hmem hopp => opposite_notMem_positiveLinks ha (hL hmem) (hL hopp)
namespace LinkFunctions
def FieldsAreLinkFamilies (a : ℝ) : Prop :=
  IsHomeomorph (fun U : GaugeField a => restrictField U (positiveLinkSet a)) ∧
  (∀ (L : Set (Link a)) (hL : HasNoOppositePairs L),
    Continuous fun p : LinkVariables L × GaugeField a => overwriteLinks hL p.1 p.2) ∧
  borel (GaugeField a) = linkSigma (positiveLinkSet a) ∧
  linkSigma (positiveLinkSet a) = regionSigma (a := a) univ ∧
  ∀ S : Set AmbientSpace, regionSigma (a := a) S = linkSigma (positiveLinksWithin a S)
def IsBoundedBorelFactorization (L : Set (Link a)) (F : GaugeField a → ℂ)
    (f : LinkVariables L → ℂ) : Prop :=
  Measurable[borel (LinkVariables L)] f ∧ (∃ C : ℝ, ∀ V, ‖f V‖ ≤ C) ∧
    ∀ U, F U = f (restrictField U L)
def LinkMeasurableFactorization (ha : 0 < a) : Prop :=
  ∀ (L : Set (Link a)) (hL : L ⊆ positiveLinkSet a) (F : GaugeField a → ℂ),
    (∃ C : ℝ, ∀ U, ‖F U‖ ≤ C) →
      List.TFAE [Measurable[linkSigma L] F,
        Measurable F ∧ DependsOnlyOnLinks L F,
        ∃ f : LinkVariables L → ℂ, IsBoundedBorelFactorization L F f] ∧
      ∀ f : LinkVariables L → ℂ, IsBoundedBorelFactorization L F f →
        (∀ V, f V = F (overwriteLinks (hasNoOppositePairs_of_subset_positiveLinks ha hL) V
          (trivialField a))) ∧
        ⨆ V, ‖f V‖ = observableSupNorm F ∧
        (Continuous F → Continuous f)
def LocalObservablesSupports (ha : 0 < a) : Prop :=
  (∀ S : Set AmbientSpace, Bornology.IsBounded S →
    {x : LatticePoint a | (x : AmbientSpace) ∈ S}.Finite) ∧
  (∀ S : Set AmbientSpace, Bornology.IsBounded S → (positiveLinksWithin a S).Finite) ∧
  (∀ F : GaugeField a → ℂ, IsBoundedObservable F →
    (IsLocalObservable F ↔ IsCylinderFunction F)) ∧
  ∀ (F : GaugeField a → ℂ) (L : Set (Link a)), IsBoundedObservable F → L.Finite →
    L ⊆ positiveLinkSet a → DependsOnlyOnLinks L F →
      linkSupport ha F ⊆ L ∧ DependsOnlyOnLinks (linkSupport ha F) F ∧
      ∀ (L' : Set (Link a)) (hL' : HasNoOppositePairs L'),
        (∀ l ∈ linkSupport ha F, l ∉ L' ∧ l.opposite ∉ L') → IsIndependentOfLinks hL' F
def LocallyMeasurableCharacterization (a : ℝ) : Prop :=
  ∀ S : Set AmbientSpace,
    locallyMeasurableIn a S =
      {F | IsBoundedObservable F ∧ IsLocalObservable F ∧ IsRegionMeasurable S F}
def Assertion : Prop :=
  ∀ (a : ℝ) (ha : 0 < a),
    FieldsAreLinkFamilies a ∧ LinkMeasurableFactorization ha ∧
      LocalObservablesSupports ha ∧ LocallyMeasurableCharacterization a
end LinkFunctions
end GibbsAtFixedSpacing
end YangMills.Construction
