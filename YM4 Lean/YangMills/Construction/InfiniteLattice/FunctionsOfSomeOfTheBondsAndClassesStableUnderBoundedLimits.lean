import YangMills.Construction.InfiniteLattice.BondFamiliesJoinsAndContinuousFunctionsOfFinitelyManyBonds
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter YangMills.Construction.InfiniteLattice
open scoped Topology ComplexConjugate
noncomputable section
namespace YangMills.Construction
namespace FieldsAtSpacing
variable {a : ℝ}
def IsLinkMeasurable (L : Set (Link a)) (F : GaugeField a → ℂ) : Prop :=
  Measurable[linkSigma L] F
def DependsOnlyOnLinks (L : Set (Link a)) (F : GaugeField a → ℂ) : Prop :=
  ∀ U V : GaugeField a, (∀ ℓ ∈ L, U ℓ = V ℓ) → F U = F V
def IsBoundedBorelFactor (L : Set (Link a)) (F : GaugeField a → ℂ)
    (f : LinkVariables L → ℂ) : Prop :=
  Measurable[borel (LinkVariables L)] f ∧ (∃ C : ℝ, ∀ g, ‖f g‖ ≤ C) ∧
    F = f ∘ linkRestriction L
def FactorsThroughLinks (L : Set (Link a)) (F : GaugeField a → ℂ) : Prop :=
  ∃ f : LinkVariables L → ℂ, IsBoundedBorelFactor L F f
def HasLinkSupport (L : Set (Link a)) (F : GaugeField a → ℂ) : Prop :=
  IsLinkMeasurable L F ∧ DependsOnlyOnLinks L F ∧ FactorsThroughLinks L F
def faceFunction (p : ElementaryPlaquette a) : GaugeField a → ℂ :=
  fun U => (faceEnergy U p : ℂ)
def ContainsCorners (S : Set AmbientSpace) (p : ElementaryPlaquette a) : Prop :=
  ∀ y ∈ p.cornerSet, (y : AmbientSpace) ∈ S
def LinkSpaceStructure (ha : 0 < a) {L : Set (Link a)}
    (hL : L ⊆ positiveLinkSet a) : Prop :=
  CompactSpace (LinkVariables L) ∧ TopologicalSpace.MetrizableSpace (LinkVariables L) ∧
  borel (LinkVariables L) =
    (⨆ ℓ : L, MeasurableSpace.comap (fun g : LinkVariables L => g ℓ)
      (borel Matrices.ComplexMatrix2.specialUnitary)) ∧
  IsHomeomorph (fun q : LinkVariables L × LinkVariables ↥(positiveLinkSet a \ L) =>
    glueOnLinks ha hL q.1 q.2) ∧
  Continuous (linkRestriction L) ∧ Function.Surjective (linkRestriction L) ∧
  borel (GaugeField a) = linkSigma (positiveLinkSet a) ∧
  {A : Set (GaugeField a) | MeasurableSet[linkSigma L] A} =
    {A | ∃ E : Set (LinkVariables L), MeasurableSet[borel (LinkVariables L)] E ∧
      A = linkRestriction L ⁻¹' E}
def LinkSupportCharacterizations (L : Set (Link a)) : Prop :=
  ∀ F : GaugeField a → ℂ, IsBoundedObservable F →
    [IsLinkMeasurable L F, DependsOnlyOnLinks L F, FactorsThroughLinks L F].TFAE ∧
    ∀ f : LinkVariables L → ℂ, IsBoundedBorelFactor L F f →
      (∀ f' : LinkVariables L → ℂ, IsBoundedBorelFactor L F f' → f' = f) ∧
      (⨆ g, ‖f g‖) = observableSupNorm F ∧
      (Continuous F → Continuous f)
def RegionObservablesProperties (a : ℝ) (L : Set (Link a)) : Prop :=
  (∀ S : Set AmbientSpace,
    (regionSigma S : MeasurableSpace (GaugeField a)) =
      linkSigma (positiveLinksWithin a S) ∧
    boundedRegionObservables a S =
      {F | IsBoundedObservable F ∧ HasLinkSupport (positiveLinksWithin a S) F} ∧
    (∃ W : Submodule ℂ (GaugeField a → ℂ),
      (W : Set (GaugeField a → ℂ)) = boundedRegionObservables a S) ∧
    (∀ F ∈ boundedRegionObservables a S, ∀ G ∈ boundedRegionObservables a S,
      F * G ∈ boundedRegionObservables a S) ∧
    (∀ F ∈ boundedRegionObservables a S, (fun U => conj (F U)) ∈ boundedRegionObservables a S) ∧
    ∀ F ∈ boundedRegionObservables a S, Complex.exp ∘ F ∈ boundedRegionObservables a S) ∧
  (∀ S T : Set AmbientSpace, S ⊆ T → boundedRegionObservables a S ⊆ boundedRegionObservables a T) ∧
  ∀ F : GaugeField a → ℂ, IsBoundedObservable F →
    (IsBlindTo L F ↔ HasLinkSupport (positiveLinkSet a \ L) F)
def BoundedRegionFiniteness (a : ℝ) : Prop :=
  (∀ S : Set AmbientSpace, Bornology.IsBounded S →
    {x : LatticePoint a | (x : AmbientSpace) ∈ S}.Finite) ∧
  (∀ S : Set AmbientSpace, Bornology.IsBounded S → (positiveLinksWithin a S).Finite) ∧
  (∀ K : Set (Link a), K.Finite → K ⊆ positiveLinkSet a →
    ∃ S : Set AmbientSpace, Bornology.IsBounded S ∧ K ⊆ positiveLinksWithin a S) ∧
  continuousFiniteLinkFunctions a = {F | IsBoundedLocal F ∧ Continuous F}
def BoundedLimitClassProperty (a : ℝ) : Prop :=
  ∀ H : Submodule ℂ (GaugeField a → ℂ), (∀ F ∈ H, IsBoundedObservable F) →
    continuousFiniteLinkFunctions a ⊆ (H : Set (GaugeField a → ℂ)) →
    (∀ (Fn : ℕ → GaugeField a → ℂ) (F : GaugeField a → ℂ), (∀ n, Fn n ∈ H) →
      (∃ C : ℝ, ∀ n, observableSupNorm (Fn n) ≤ C) →
      (∀ U, Tendsto (fun n => Fn n U) atTop (𝓝 (F U))) → F ∈ H) →
    (H : Set (GaugeField a → ℂ)) = {F | IsBoundedObservable F}
def FaceFunctionProperties (a : ℝ) : Prop :=
  (∀ p : ElementaryPlaquette a,
    faceFunction p ∈ continuousFiniteLinkFunctions a ∧
    (∀ U : GaugeField a, faceEnergy U p ∈ Icc (0 : ℝ) 2) ∧
    ∀ S : Set AmbientSpace, ContainsCorners S p → faceFunction p ∈ boundedRegionObservables a S) ∧
  (∀ Q : Set AmbientSpace, Bornology.IsBounded Q →
    {p : ElementaryPlaquette a | p.center ∈ Q}.Finite) ∧
  (∀ v : AmbientSpace → ℂ, IsBoundedBorelCompactlySupported v →
    {p : ElementaryPlaquette a | v p.center • faceFunction p ≠ 0}.Finite ∧
    (smearedEnergy v : GaugeField a → ℂ) ∈ continuousFiniteLinkFunctions a ∧
    Complex.exp ∘ (smearedEnergy v : GaugeField a → ℂ) ∈ continuousFiniteLinkFunctions a ∧
    ∀ S : Set AmbientSpace,
      (∀ p : ElementaryPlaquette a, v p.center ≠ 0 → ContainsCorners S p) →
      (smearedEnergy v : GaugeField a → ℂ) ∈ boundedRegionObservables a S ∧
      Complex.exp ∘ (smearedEnergy v : GaugeField a → ℂ) ∈ boundedRegionObservables a S) ∧
  (∀ v w : AmbientSpace → ℂ, IsBoundedBorelCompactlySupported v →
    IsBoundedBorelCompactlySupported w →
    (smearedEnergy (v + w) : GaugeField a → ℂ) = smearedEnergy v + smearedEnergy w) ∧
  ∀ (z : ℂ) (v : AmbientSpace → ℂ), IsBoundedBorelCompactlySupported v →
    (smearedEnergy (z • v) : GaugeField a → ℂ) = z • smearedEnergy v
def LinkFunctionsStatement : Prop :=
  ∀ (a : ℝ) (ha : 0 < a) (L : Set (Link a)) (hL : L ⊆ positiveLinkSet a),
    LinkSpaceStructure ha hL ∧
    LinkSupportCharacterizations L ∧
    RegionObservablesProperties a L ∧
    BoundedRegionFiniteness a ∧
    BoundedLimitClassProperty a ∧
    FaceFunctionProperties a
end FieldsAtSpacing
end YangMills.Construction
