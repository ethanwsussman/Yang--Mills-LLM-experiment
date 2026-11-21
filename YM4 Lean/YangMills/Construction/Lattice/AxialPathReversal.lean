import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.GaugeConfigurations
import Mathlib
open YangMills.Construction.Matrices
namespace YangMills.Construction.PeriodicLattice
def AxialPathReversal : Prop :=
  ∀ L m : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m →
  ∀ j : ℤ, -(m : ℤ) ≤ j →
  ∀ (x x' : Site L m j) (μ : Fin 4) (n : ℤ), IsAxialDisplacement x x' μ n →
    (∃ q : Fin 4 × ℤ, IsAxialDisplacement x' x q.1 q.2) ∧
    axialPath x' x = reversePath (axialPath x x') ∧
    (∀ U : Bond L m j → ComplexMatrix2,
      IsGaugeField complexGaugeGroup
        {b | b ∈ axialPath x x' ∨ b.opposite ∈ axialPath x x'} U →
      pathHolonomy U (axialPath x' x) = (pathHolonomy U (axialPath x x'))⁻¹) ∧
    ∀ A : Bond L m j → ComplexMatrix2, IsBondForm complexLieAlgebra A →
      bondFormSumAlong A (axialPath x' x) = -bondFormSumAlong A (axialPath x x')
end YangMills.Construction.PeriodicLattice
