import YangMills.Construction.InfiniteLattice.HypercubicMotionsOfTheLattice
import YangMills.Construction.InfiniteLattice.PeriodicGibbsAndTorusLimitSets
import YangMills.Construction.ReflectionPositivity.FacePlanesCellGroupAndCellsOfACellSide
import YangMills.Construction.ReflectionPositivity.LatticesAndBondVariablesOfACellSide
import YangMills.Construction.VolumeTransfer.LatticeSymmetriesCarryBondsAndInvariance
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.VolumeTransfer.PeriodicGibbsInvariance
open InfiniteLattice
variable {L K : ℕ}
def IsAxialMirror (P : LatticeMirror (refinedSpacing L K)) : Prop :=
  ∃ μ : Fin 4, P.cls = ReflectionClass.axial μ
def IsInvariantUnderMotionsShiftsAndAxialMirrors
    (ν : Measure (RefinedGaugeField L K)) : Prop :=
  (∀ r : latticeMotions (refinedSpacing L K),
      IsSymmetricUnder ν (latticeMotionSymmetry r)) ∧
    (∀ v : LatticePoint (refinedSpacing L K), IsSymmetricUnder ν (shift v)) ∧
    ∀ P : LatticeMirror (refinedSpacing L K), IsAxialMirror P → IsSymmetricUnder ν P.symmetry
def FaceHyperplanesAreAxialMirrorsBisectingLinks (L K : ℕ) (lc : ℝ) : Prop :=
  ∀ (μ : Fin 4) (ι : ℤ), ∃ P : LatticeMirror (refinedSpacing L K),
    P.cls = ReflectionClass.axial μ ∧
      P.plane = FaceReflections.faceHyperplane L K lc μ ι ∧ P.BisectsLinks
def IsInvariantUnderReflectionGroupInBothSenses (lc : ℝ) (ν : Measure (RefinedGaugeField L K))
    [IsProbabilityMeasure ν] : Prop :=
  ∀ r ∈ FaceReflections.reflectionGroup L K lc,
    (∃ g : LatticeSymmetry (refinedSpacing L K), g.toFun = r ∧ IsSymmetricUnder ν g) ∧
      ∃ h : (LatticeGeometry.euclidean L K).IsReflectionTranslation r,
        IsInvariantUnderReflectionTranslation ν h
def Statement : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ (K : ℕ+) (β : ℝ), 0 < β →
    ∀ (ν : Measure (RefinedGaugeField L (K : ℕ))) [IsProbabilityMeasure ν],
      ν ∈ periodicGibbsSet L (K : ℕ) β →
        IsGibbs β ν ∧ IsInvariantUnderMotionsShiftsAndAxialMirrors ν ∧
          ∀ lc : ℝ, ReflectionPositivity.Chessboard.IsCellSideOf L lc →
            FaceHyperplanesAreAxialMirrorsBisectingLinks L (K : ℕ) lc ∧
              IsInvariantUnderReflectionGroupInBothSenses lc ν
end YangMills.Construction.VolumeTransfer.PeriodicGibbsInvariance
end
