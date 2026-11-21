import YangMills.Construction.InfiniteLattice.CoarseStepsAndTheFivePointInequality
import YangMills.Construction.InfiniteLattice.LinkAndSitePicturesWithACoordinateAsTime
import Mathlib
set_option autoImplicit false
open MeasureTheory
open YangMills.Construction.OneLoopNotation YangMills.Construction.ComplexHilbert YangMills.Construction.ContractionUnitary
open scoped InnerProductSpace
noncomputable section
namespace YangMills.Construction.LatticeConventions.ReflectionPositiveStates
open YangMills.Construction.InfiniteLattice (GaugeField IsSymmetricUnder IsShiftInvariant LatticeSymmetry
  ElementaryPlaquette faceEnergy axisStep shift)
open SiteFrame
variable (a : Spacing) (ν : Measure (GaugeField (a : ℝ))) [IsProbabilityMeasure ν]
def SymmetricWithEqualFaceMeans : Prop :=
  (∀ r : LatticeSymmetry (a : ℝ), IsSymmetricUnder ν r) ∧
    ∀ p q : ElementaryPlaquette (a : ℝ),
      ∫ U : GaugeField (a : ℝ), faceEnergy U p ∂ν =
        ∫ U : GaugeField (a : ℝ), faceEnergy U q ∂ν
def SiteFrameMatrixElements : Prop :=
  LinkFrame.IsAdmissibleState a timeAxis ν ∧
  IsSymmetricOp (timeTransferOperator a ν) ∧
  OpGE (timeTransferOperator a ν) 0 ∧
  OpLE (timeTransferOperator a ν) (idOp (TimeSiteHilbertSpace a ν)) ∧
  (∀ j : SpatialDirection,
    IsUnitaryMap (spatialShift a ν j : TimeSiteHilbertSpace a ν →ₗ[ℂ] TimeSiteHilbertSpace a ν)) ∧
  (∀ j : SpatialDirection, Commute (timeTransferOperator a ν) (spatialShift a ν j)) ∧
  (∀ i j : SpatialDirection, Commute (spatialShift a ν i) (spatialShift a ν j)) ∧
  ∀ (F G : upperSpace a timeAxis) (m : ℕ) (y : SpatialDirection → ℤ),
    ⟪timeClass a ν F,
        (timeTransferOperator a ν ^ m * zpowOp (spatialShift a ν 0) (y 0) *
            zpowOp (spatialShift a ν 1) (y 1) * zpowOp (spatialShift a ν 2) (y 2))
          (timeClass a ν G)⟫_ℂ =
      ∫ U, conjFun ((timeReflection a).actOn F.1) U *
        (shift (m • axisStep (a : ℝ) timeAxis +
          ∑ j : SpatialDirection, y j • axisStep (a : ℝ) j.toDirection)).actOn G.1 U ∂ν
def EvenCorrelationBounds : Prop :=
  ∀ (F : upperSpace a timeAxis) (m : ℕ),
    (reflectedCorrelation a timeAxis ν F.1 ((2 * m) • axisStep (a : ℝ) timeAxis)).im = 0 ∧
    (siteForm a timeAxis ν F F).im = 0 ∧
    0 ≤ (reflectedCorrelation a timeAxis ν F.1 ((2 * m) • axisStep (a : ℝ) timeAxis)).re ∧
    (reflectedCorrelation a timeAxis ν F.1 ((2 * m) • axisStep (a : ℝ) timeAxis)).re ≤
      (siteForm a timeAxis ν F F).re
def FivePointBoundAllSpatial : Prop :=
  ∀ (i : SpatialDirection) (F : upperSpace a timeAxis) (k : ℕ), 1 ≤ k →
    FivePointBound a timeAxis i.toDirection ν F.1 k
def Statement : Prop :=
  ∀ (a : Spacing) (ν : Measure (GaugeField (a : ℝ))) [IsProbabilityMeasure ν],
    IsShiftInvariant ν →
    (∀ (Q : NormalHyperplane) (hQ : Q.IsLatticeMirror (a : ℝ)),
      NormalHyperplane.IsReflectionPositiveAcrossMirror hQ ν) →
      SymmetricWithEqualFaceMeans a ν ∧
      SiteFrameMatrixElements a ν ∧
      EvenCorrelationBounds a ν ∧
      FivePointBoundAllSpatial a ν
end YangMills.Construction.LatticeConventions.ReflectionPositiveStates
end
