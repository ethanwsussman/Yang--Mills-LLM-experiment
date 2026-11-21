import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.InvertibleContourVariables
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Averaging
open Matrices PeriodicLattice
def BlockAverageRealAnalyticOnSmallFields : Prop :=
  ∀ s : Conventions.StandingParameters, ∀ ω ∈ Ioc (0 : ℝ) (averagingRadiusCap s.L),
    ∀ k, k < (s.K : ℕ) →
    ∀ c : BondAtLevel s.L s.m s.K (k + 1), c.IsPositivelyOriented →
      ∀ _ : Fintype (PositivelyOrientedBond s.L s.m (levelDepth s.K k)),
        ComplexMatrix2.IsRealAnalyticBetween
          (fun _ : PositivelyOrientedBond s.L s.m (levelDepth s.K k) =>
            ComplexMatrix2.FactorKind.group)
          (fun _ : Fin 1 => ComplexMatrix2.FactorKind.group)
          (valuesOnPositiveBonds ''
            (smallPlaquetteFields ω c : Set (BondAtLevel s.L s.m s.K k → ComplexMatrix2)))
          fun v _ => blockAverage ω (fieldOfPositiveValues v) c
end YangMills.Construction.Averaging
end
