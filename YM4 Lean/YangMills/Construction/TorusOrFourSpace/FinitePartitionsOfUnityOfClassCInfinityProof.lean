import YangMills.Construction.TorusOrFourSpace.FinitePartitionsOfUnityOfClassCInfinity
import YangMills.Construction.TorusOrFourSpace.PartitionsOfUnityOnCompactSubsetsOfPowers
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.PeriodicSpace
theorem smoothFinitePartitionOfUnity_of_partitionsOfUnity
    (hpart : PartitionsOfUnity.Statement) : SmoothFinitePartitionOfUnity := by
  intro D n A C P hC hP hcover
  obtain ⟨ψ, hψ, -, N, hN, hCN, hsum⟩ := (hpart D Kind.euclidean n).1 A C P hC hP hcover
  exact ⟨ψ, hψ, N, hN, hCN, hsum⟩
end YangMills.Construction.PeriodicSpace
