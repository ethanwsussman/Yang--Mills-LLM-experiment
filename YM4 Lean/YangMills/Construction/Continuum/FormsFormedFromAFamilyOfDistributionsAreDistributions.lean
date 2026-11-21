import YangMills.Construction.Continuum.DistributionFormedFromAFamilyOfDistributions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open ReflectionSpaces.Euclidean SetPartition
namespace Continuum.BlockProducts
def AssembledFormsAreDistributions : Prop :=
  ∀ u : DistribFamily,
    (∀ (Q : ℕ), 2 ≤ Q → ∀ (π : PartitionsFin Q)
      (hπ : π ∈ nonSingletonPartitions Q),
      ∃ T : Distribution (distinctWithinBlocks π), T.form = partitionForm u hπ) ∧
    ∀ Q : ℕ, 1 ≤ Q → ∃ T : Distribution (configSpace Q), T.form = assembledForm Q u
end Continuum.BlockProducts
end YangMills.Construction
