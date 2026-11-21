import YangMills.Construction.Torus.CubesPartitionOfUnityAndCutSequencesOnAGeneralTorus
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.GeneralTorus
def ChainCubesFinite : Prop :=
  ∀ C : CubeGaugeSetting, C.chain.allCubes.Finite
end YangMills.Construction.GeneralTorus
