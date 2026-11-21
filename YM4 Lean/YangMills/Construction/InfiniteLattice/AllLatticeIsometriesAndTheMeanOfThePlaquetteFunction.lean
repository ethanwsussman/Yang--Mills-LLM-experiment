import YangMills.Construction.InfiniteLattice.ReflectionPositivityAtAMirrorGivenWithANormal
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace LatticeConventions
open InfiniteLattice (GaugeField IsSymmetricUnder IsShiftInvariant LatticeSymmetry
  ElementaryPlaquette faceEnergy)
def LatticeSymmetryInvarianceAndEqualFaceMeans : Prop :=
  ∀ (a : Spacing) (ν : Measure (GaugeField (a : ℝ))) [IsProbabilityMeasure ν],
    IsShiftInvariant ν →
    (∀ (Q : NormalHyperplane) (hQ : Q.IsLatticeMirror (a : ℝ)),
      NormalHyperplane.IsReflectionPositiveAcrossMirror hQ ν) →
      (∀ r : LatticeSymmetry (a : ℝ), IsSymmetricUnder ν r) ∧
      ∀ p p' : ElementaryPlaquette (a : ℝ),
        ∫ U : GaugeField (a : ℝ), faceEnergy U p ∂ν =
          ∫ U : GaugeField (a : ℝ), faceEnergy U p' ∂ν
end LatticeConventions
end YangMills.Construction
end
