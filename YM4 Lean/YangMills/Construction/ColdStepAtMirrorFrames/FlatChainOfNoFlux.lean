import YangMills.Construction.ColdStepAtMirrorFrames.ChainOfConstantCurvature
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace BlockAverages
def ConstantCurvatureChainFlatOfZeroFlux : Prop :=
  ∀ (F : BlockFrame) (X : imaginaryQuaternions) (μ ν : Fin 4) (j : ℕ), Odd F.blockSide →
    ∀ x i, ColdStepAtMirrorFrames.constantCurvatureChain F X μ ν 0 j x i = 1
end BlockAverages
end YangMills.Construction
end
