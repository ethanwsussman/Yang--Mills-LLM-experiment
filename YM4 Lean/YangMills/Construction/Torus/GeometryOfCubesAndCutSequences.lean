import YangMills.Construction.Torus.PartsOfTheGeometryOfCubes
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.GeneralTorus
def CubeGeometryAndLocalChains : Prop :=
  ∀ (C : CubeGaugeSetting) (n : ℕ) (z : C.data.Space), ((n, z) : C.data.CubeIndex) ∈ C.chain.cubesAt n →
    C.LevelsNearCube (n, z) ∧ C.CoarsePartitionOfUnity ∧ C.UnityWeightLocalLipschitz (n, z) ∧
      C.LocalSetsAgreeNearCube (n, z) ∧ C.LocalObjectsAgreeNearCube (n, z) ∧
      C.BondSupportsNearCube (n, z) ∧ C.DistancesNearCube (n, z)
end YangMills.Construction.GeneralTorus
