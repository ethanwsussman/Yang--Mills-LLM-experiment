import YangMills.Construction.ColdStepAtMirrorFrames.NumbersOfTheColdChainFormForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
def FlatCoordinatesScalar : Prop :=
  ∀ (a : ℝ) (L : ℕ) (c : ColdChainParameters), Odd L → c.Admissible a L →
    ∀ (F : BlockFrame) (b : F.Site F.depth × Fin 4) (e : F.Site F.top × Fin 4) (X : imaginaryQuaternions),
      IsBlockTorus L F → ‖X‖ = 1 →
      torusCoordinate a c.ρA b (uniformField F F.top) = 0 ∧
      bondDeriv (torusCoordinate a c.ρA b) (uniformField F F.top) ![e] ![X] =
        (-(((bondDeriv (torusCoordinate a c.ρA b) (uniformField F F.top) ![e] ![X] : imaginaryQuaternions) : ℍ[ℝ]) *
          (X : ℍ[ℝ])).re) • X
end YangMills.Construction.ColdStepAtMirrorFrames
end
