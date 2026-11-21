import YangMills.Construction.ColdChainAtEveryLevel.LevelsAndFields
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
def firstDerivNorm {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {j : ℕ} {B : Finset (F.Site j × Fin 4)}
    (A : P → ↥B → imaginaryQuaternions) (u : P) : ↥B → ℝ :=
  fun b => ‖iteratedFDeriv ℝ 1 (fun τ => A τ b) 0 ![u]‖
def secondDerivNorm {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {j : ℕ} {B : Finset (F.Site j × Fin 4)}
    (A : P → ↥B → imaginaryQuaternions) (u v : P) : ↥B → ℝ :=
  fun b => ‖iteratedFDeriv ℝ 2 (fun τ => A τ b) 0 ![u, v]‖
def thirdDerivNorm {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {j : ℕ} {B : Finset (F.Site j × Fin 4)}
    (A : P → ↥B → imaginaryQuaternions) (u v w : P) : ↥B → ℝ :=
  fun b => ‖iteratedFDeriv ℝ 3 (fun τ => A τ b) 0 ![u, v, w]‖
end YangMills.Construction.ColdStepAtMirrorFrames
end
