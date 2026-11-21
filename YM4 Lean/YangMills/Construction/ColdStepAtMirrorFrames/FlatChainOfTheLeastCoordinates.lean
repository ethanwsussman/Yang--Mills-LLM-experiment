import YangMills.Construction.ColdStepAtMirrorFrames.NumbersOfTheColdChainFormForm
import YangMills.Construction.ColdStepAtMirrorFrames.SumAgainstThreeFlatResponses
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
open Classical in
def flatMinimizerResponse (a ρ : ℝ) (c : F.Site F.top × Fin 4) (X : imaginaryQuaternions) :
    LevelForm F F.depth := fun x i =>
  - (((bondDeriv (torusCoordinate a ρ (x, i)) (uniformField F F.top) ![c] ![X] :
        imaginaryQuaternions) : Quaternion ℝ) * (X : Quaternion ℝ)).re +
    (if IsCrossingBond (x, i) ∧ enclosingCell x = c.1 ∧ i = c.2 then 1 else 0)
def flatChainOfMinimizerCoords : Prop :=
  ∀ a : ℝ, 1 ≤ a → ∃ L₀ : ℕ, ∀ (L : ℕ) (n : ColdChainParameters), Odd L → L₀ ≤ L → n.Admissible a L →
    ∀ (F : BlockFrame) (c : F.Site F.top × Fin 4) (X : imaginaryQuaternions), F.blockSide = L →
      IsLargeCubicTorus F → ‖X‖ = 1 →
      ∃ B : FormChain F, IsFlatChain a c B ∧ IsAxialResponse c B (flatMinimizerResponse a n.ρA c X)
end YangMills.Construction.ColdStepAtMirrorFrames
end
