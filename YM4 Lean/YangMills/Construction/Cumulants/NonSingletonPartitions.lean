import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
namespace SetPartition
def nonSingletonPartitions (m : ℕ) : Finset (Finpartition (Finset.univ : Finset (Fin m))) :=
  Finset.univ.filter fun π => ∀ B ∈ π.parts, 2 ≤ B.card
end SetPartition
end YangMills.Construction
