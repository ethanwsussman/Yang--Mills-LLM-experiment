import YangMills.Construction.InfiniteLattice.SidesOfAPlaquetteAndTheDensityOfBoundedSupport
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
variable {L K : ℕ}
abbrev LatticeCutoffPlaquette (L K : ℕ) : Type :=
  ElementaryPlaquette (PeriodicLattice.meshSize L (K : ℤ))
def cutoffSmearedEnergy (f : AmbientSpace → ℂ)
    (U : GaugeField (PeriodicLattice.meshSize L (K : ℤ))) : ℂ :=
  boundedSupportObservable f U
theorem cutoffSmearedEnergy_eq_finsum (f : AmbientSpace → ℂ)
    (U : GaugeField (PeriodicLattice.meshSize L (K : ℤ))) :
    cutoffSmearedEnergy f U =
      ∑ᶠ p : LatticeCutoffPlaquette L K, f p.center * (faceEnergy U p : ℂ) := by
  unfold cutoffSmearedEnergy boundedSupportObservable
  refine finsum_congr fun p => ?_
  by_cases h : f p.center = 0 <;> simp [h]
end InfiniteLattice
end YangMills.Construction
