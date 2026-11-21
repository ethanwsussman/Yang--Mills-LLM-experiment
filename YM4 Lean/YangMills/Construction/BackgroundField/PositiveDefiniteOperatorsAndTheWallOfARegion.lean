import YangMills.Construction.BackgroundField.GaugeFixedOperators
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.BackgroundField
open Set PeriodicLattice Matrices
def CurvatureSmallAtBoundary {L m t : ℕ} (R : NestedRegions L m t) (K : ℕ) (δ : ℝ)
    (U : FineBond L m K → ComplexMatrix2) : Prop :=
  ∀ p ∈ (plaquettesMeeting (R.regionAt 0) \ plaquettesInside (R.regionAt 0) :
      Set (FinePlaquette L m K)),
    ComplexMatrix2.operatorNorm (plaquetteHolonomy U p - 1) < δ
end YangMills.Construction.BackgroundField
