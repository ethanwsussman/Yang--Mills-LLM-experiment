import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import YangMills.Construction.Probability.BoundedRealRandomVariable
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
def FaceEnergyBoundedAndFacesLocallyFinite : Prop :=
  ∀ (s : Conventions.StandingParameters)
    (ν : Measure (GaugeField (PeriodicLattice.meshSize s.L ((s.K : ℕ) : ℤ)))),
    IsProbabilityMeasure ν →
      (IsProbabilityMeasure ν ∧
        ∀ p : ElementaryPlaquette (PeriodicLattice.meshSize s.L ((s.K : ℕ) : ℤ)),
          Probability.IsBoundedRealRV
              (fun U : GaugeField (PeriodicLattice.meshSize s.L ((s.K : ℕ) : ℤ)) =>
                faceEnergy U p) ∧
            ∀ U : GaugeField (PeriodicLattice.meshSize s.L ((s.K : ℕ) : ℤ)),
              0 ≤ faceEnergy U p ∧ faceEnergy U p ≤ 2) ∧
      ∀ S : Set AmbientSpace, Bornology.IsBounded S →
        {p : ElementaryPlaquette (PeriodicLattice.meshSize s.L ((s.K : ℕ) : ℤ)) |
          p.center ∈ S}.Finite
end InfiniteLattice
end YangMills.Construction
end
