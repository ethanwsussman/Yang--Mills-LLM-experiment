import YangMills.Construction.Towers.CovariantAveragesAsDifferentials
import YangMills.Construction.Towers.PeriodicExtensionsLocalKernelsAndKernelsThatDescend
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.LocalKernels
def QuadraticTermOfLift : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k m : ℕ, 0 < m →
    1 ≤ k → ∀ U ∈ Tower.fieldsIn L m k 0 PeriodicLattice.complexGaugeGroup,
      U ∈ Tower.smallIterateFields L m k →
      ∀ A ∈ Tower.complexEdgeForms L m k 0, ∀ A' ∈ Tower.complexEdgeForms L m k 0,
        ∀ e : PeriodicOperators.PosEdge L k k,
          Tower.FullSpace.AsDifferentials.complexQuadraticTerm L k
              (liftGaugeField L m k 0 U)
              (liftGaugeField L m k 0 A)
              (liftGaugeField L m k 0 A') e =
            Tower.AsDifferentials.complexQuadraticTerm L m k U A A'
              (projPositiveEdge L m k k e)
end YangMills.Construction.LocalKernels
