import YangMills.Construction.Torus.CompressionOfTheCutOperatorToACube
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.GeneralTorus.CubeGaugeSetting
variable (C : CubeGaugeSetting)
def localInverse (Q : C.data.CubeIndex) : Module.End ℝ C.CoarseField :=
  C.compressInverse (C.bondsIn Q) (C.cubeGreen Q)
def approxInverse : Module.End ℝ C.CoarseField :=
  ∑ᶠ Q ∈ C.chain.allCubes,
    C.unityMul Q ∘ₗ C.localInverse Q ∘ₗ C.unityMul Q
def cutGreen (Q : C.data.CubeIndex) : Module.End ℝ C.CoarseField :=
  C.cubeIndicator Q ∘ₗ C.coarseGreen ∘ₗ C.cubeIndicator Q
def remainderDiag (Q : C.data.CubeIndex) : Module.End ℝ C.CoarseField :=
  (C.unityMul Q ∘ₗ C.cubeGreen Q -
      C.cubeGreen Q ∘ₗ C.unityMul Q) +
    (C.cubeGreen Q - C.cutGreen Q) ∘ₗ C.unityMul Q
def remainderOffDiag (Q' Q : C.data.CubeIndex) : Module.End ℝ C.CoarseField :=
  (C.cubeIndicator Q - 1) ∘ₗ C.unityMul Q' ∘ₗ C.unityMul Q' ∘ₗ
    C.coarseGreen ∘ₗ C.unityMul Q
open Classical in
def remainderEntry (Q' Q : C.data.CubeIndex) : Module.End ℝ C.CoarseField :=
  if Q' = Q then C.remainderDiag Q else C.remainderOffDiag Q' Q
def remainder : Module.End ℝ C.CoarseField :=
  ∑ᶠ Q' ∈ C.chain.allCubes, ∑ᶠ Q ∈ C.chain.allCubes,
    C.remainderEntry Q' Q ∘ₗ C.localInverse Q ∘ₗ C.unityMul Q
end YangMills.Construction.GeneralTorus.CubeGaugeSetting
