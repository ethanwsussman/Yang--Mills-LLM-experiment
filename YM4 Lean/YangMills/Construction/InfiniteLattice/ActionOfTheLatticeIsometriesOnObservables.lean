import YangMills.Construction.Conventions.LatticeAndStateDefs
import YangMills.Construction.InfiniteLattice.IsometriesOfTheUnitLattice
import YangMills.Construction.InfiniteLattice.LinkSupportAndRegionObservables
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.InfiniteLattice
variable {a : ℝ}
def LatticeSymmetry.IsInverse (t r : LatticeSymmetry a) : Prop :=
  Function.LeftInverse t.toFun r.toFun ∧ Function.RightInverse t.toFun r.toFun
def LinksAreNearestNeighbourPairs (a : ℝ) : Prop :=
  (∀ x y : LatticePoint a, (∃ l : Link a, l.initial = x ∧ l.terminal = y) ↔
    LatticeConventions.euclidNorm ((x : AmbientSpace) - (y : AmbientSpace)) = a) ∧
  ∀ (g : LatticeSymmetry a) (l : Link a),
    ∃ l' : Link a, l'.initial = g.pointMap l.initial ∧ l'.terminal = g.pointMap l.terminal
def PullbackFieldIsHomeomorph (a : ℝ) : Prop :=
  ∀ g : LatticeSymmetry a,
    (∀ (U : GaugeField a) (l : Link a), U (g.linkMap l.opposite) = (U (g.linkMap l))⁻¹) ∧
      IsHomeomorph g.pullbackField
def ActOnPreservesAlgebraAndRegions (a : ℝ) : Prop :=
  ∀ g : LatticeSymmetry a,
    (∀ F G : GaugeField a → ℂ, IsBoundedObservable F → IsBoundedObservable G →
      IsBoundedObservable (g.actOn F) ∧
      g.actOn (F * G) = g.actOn F * g.actOn G ∧
      g.actOn (LatticeConventions.conjFun F) =
        LatticeConventions.conjFun (g.actOn F)) ∧
    ∀ S : Set AmbientSpace,
      (fun F : GaugeField a → ℂ => g.actOn F) '' boundedRegionObservables a S =
        boundedRegionObservables a (g.setImage S)
def ActOnComp (a : ℝ) : Prop :=
  ∀ g h : LatticeSymmetry a,
    (g.comp h).toFun = g.toFun ∘ h.toFun ∧
    ∀ F : GaugeField a → ℂ, IsBoundedObservable F →
      (g.comp h).actOn F = g.actOn (h.actOn F)
def ShiftActOnRegions (a : ℝ) : Prop :=
  ∀ v : LatticePoint a,
    (∀ S : Set AmbientSpace,
      (fun F : GaugeField a → ℂ => (shift v).actOn F) ''
          boundedRegionObservables a S =
        boundedRegionObservables a (LatticeConventions.translateSet S (v : AmbientSpace))) ∧
    ∀ (L : Set (Link a)) (F : GaugeField a → ℂ), IsBoundedObservable F →
      Measurable[linkSigma L] F →
        Measurable[linkSigma ((shift v).linkMap '' L)]
          ((shift v).actOn F)
def ActOnLinearIsometric (a : ℝ) : Prop :=
  ∀ g : LatticeSymmetry a,
    g.actOn (LatticeConventions.constOne : GaugeField a → ℂ) =
      LatticeConventions.constOne ∧
    ∀ F : GaugeField a → ℂ, IsBoundedObservable F →
      (∀ G : GaugeField a → ℂ, IsBoundedObservable G →
        g.actOn (F + G) = g.actOn F + g.actOn G) ∧
      (∀ c : ℂ, g.actOn (c • F) = c • g.actOn F) ∧
      g.actOn (LatticeConventions.absFun F ^ 2) =
        LatticeConventions.absFun (g.actOn F) ^ 2 ∧
      observableSupNorm (g.actOn F) = observableSupNorm F
def RegionObservablesMonotone (a : ℝ) : Prop :=
  (∀ S : Set AmbientSpace,
    (regionSigma S : MeasurableSpace (GaugeField a)) =
      regionSigma (S ∩ (latticeSubgroup a : Set AmbientSpace))) ∧
  (∀ S T : Set AmbientSpace, S ⊆ T →
    boundedRegionObservables a S ⊆ boundedRegionObservables a T ∧
    localRegionObservables a S ⊆ localRegionObservables a T) ∧
  ∀ S : Set AmbientSpace, Bornology.IsBounded S →
    boundedRegionObservables a S = localRegionObservables a S
def IsStarAlgebraOfFunctions (𝒜 : Set (GaugeField a → ℂ)) : Prop :=
  (∀ c : ℂ, (fun _ => c) ∈ 𝒜) ∧
  (∀ F ∈ 𝒜, ∀ G ∈ 𝒜, F + G ∈ 𝒜) ∧
  (∀ c : ℂ, ∀ F ∈ 𝒜, c • F ∈ 𝒜) ∧
  (∀ F ∈ 𝒜, ∀ G ∈ 𝒜, F * G ∈ 𝒜) ∧
  ∀ F ∈ 𝒜, LatticeConventions.conjFun F ∈ 𝒜
def RegionObservablesStarAlgebra (a : ℝ) : Prop :=
  ∀ S : Set AmbientSpace,
    IsStarAlgebraOfFunctions (boundedRegionObservables a S) ∧
    IsStarAlgebraOfFunctions (localRegionObservables a S)
def ActOnLocalRegions (a : ℝ) : Prop :=
  (∀ (g : LatticeSymmetry a) (S : Set AmbientSpace),
    (fun F : GaugeField a → ℂ => g.actOn F) '' localRegionObservables a S =
      localRegionObservables a (g.setImage S)) ∧
  ∀ (v : LatticePoint a) (S : Set AmbientSpace),
    (fun F : GaugeField a → ℂ => (shift v).actOn F) ''
        localRegionObservables a S =
      localRegionObservables a (LatticeConventions.translateSet S (v : AmbientSpace))
def LatticeSymmetryInverses (a : ℝ) : Prop :=
  ∀ g : LatticeSymmetry a,
    Function.Bijective g.toFun ∧
    (∃ t : LatticeSymmetry a, t.IsInverse g) ∧
    ∀ t : LatticeSymmetry a, t.IsInverse g →
      (∀ F : GaugeField a → ℂ, IsBoundedObservable F →
        t.actOn (g.actOn F) = F ∧ F = g.actOn (t.actOn F)) ∧
      ∀ μ : Measure (GaugeField a), IsProbabilityMeasure μ →
        IsSymmetricUnder μ g → IsSymmetricUnder μ t
def SymmetricUnderCompAndMultiples (a : ℝ) : Prop :=
  ∀ μ : Measure (GaugeField a), IsProbabilityMeasure μ →
    (∀ g h : LatticeSymmetry a,
      IsSymmetricUnder μ g → IsSymmetricUnder μ h → IsSymmetricUnder μ (g.comp h)) ∧
    ∀ v : LatticePoint a, IsSymmetricUnder μ (shift v) →
      ∀ k : ℤ, IsSymmetricUnder μ (shift (k • v))
def SymmetryActionOnObservables : Prop :=
  ∀ a : LatticeConventions.Spacing,
    LinksAreNearestNeighbourPairs (a : ℝ) ∧
    PullbackFieldIsHomeomorph (a : ℝ) ∧
    ActOnPreservesAlgebraAndRegions (a : ℝ) ∧
    ActOnComp (a : ℝ) ∧
    ShiftActOnRegions (a : ℝ) ∧
    ActOnLinearIsometric (a : ℝ) ∧
    RegionObservablesMonotone (a : ℝ) ∧
    RegionObservablesStarAlgebra (a : ℝ) ∧
    ActOnLocalRegions (a : ℝ) ∧
    LatticeSymmetryInverses (a : ℝ) ∧
    SymmetricUnderCompAndMultiples (a : ℝ)
end YangMills.Construction.InfiniteLattice
