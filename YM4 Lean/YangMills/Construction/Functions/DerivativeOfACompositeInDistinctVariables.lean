import YangMills.Construction.ComplexAnalysis.PartialDerivativesAndLogarithm
import YangMills.Construction.Cumulants.NumberOfBlocksAndImagesOfPartitions
import Mathlib
namespace YangMills.Construction.CompositeDerivative
open ComplexVariables SetPartition
def PartitionChainRule : Prop :=
  ∀ (q : ℕ), 1 ≤ q →
    ∀ (U : Set (Coordinates.ComplexCoordinates q)) (W : Set ℂ)
      (V : Coordinates.ComplexCoordinates q → ℂ) (η : ℂ → ℂ),
      IsOpen U → IsOpen W → Set.MapsTo V U W → IsHolomorphicScalar U V →
      Coordinates.ComplexCoordinates.IsHolomorphicVia (Equiv.funUnique (Fin 1) ℂ).symm
        (Equiv.funUnique (Fin 1) ℂ).symm W η →
      ∀ A : Finset (Fin q), A.Nonempty →
        HasPartialOverFinset U A (η ∘ V) ∧
        (∀ π : Partitions A, ∀ J ∈ π.parts, HasPartialOverFinset U J V) ∧
        ∀ z ∈ U,
          partialOverFinset A (η ∘ V) z =
            ∑ π : Partitions A,
              iteratedDeriv (blockCount π) η (V z) * ∏ J ∈ π.parts, partialOverFinset J V z
end YangMills.Construction.CompositeDerivative
