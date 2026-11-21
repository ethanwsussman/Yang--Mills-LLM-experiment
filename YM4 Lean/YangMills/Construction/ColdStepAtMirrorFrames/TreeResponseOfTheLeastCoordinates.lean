import YangMills.Construction.ColdStepAtMirrorFrames.NumbersOfTheColdChainFormForm
import YangMills.Construction.ColdStepAtMirrorFrames.SumAgainstThreeFlatResponses
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.BlockAverages
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame}
open Classical in
def minimizerResponse (a ρ : ℝ) (c : F.Site F.top × Fin 4) (X : imaginaryQuaternions) : LevelForm F F.depth :=
  fun x i =>
  - (((bondDeriv (torusCoordinate a ρ (x, i)) (uniformField F F.top) ![c] ![X] : imaginaryQuaternions) :
      Quaternion ℝ) * (X : Quaternion ℝ)).re +
    (if IsCrossingBond (x, i) ∧ enclosingCell x = c.1 ∧ i = c.2 then 1 else 0)
def AxialResponseOfMinimizers : Prop :=
  ∀ a : ℝ, 1 ≤ a → ∀ L : ℕ, Odd L → ∀ c : ColdChainParameters, c.Admissible a L →
    ∀ (F : BlockFrame) (b : F.Site F.top × Fin 4) (X : imaginaryQuaternions), F.blockSide = L →
      IsLargeCubicTorus F → ‖X‖ = 1 →
      ∃ B : FormChain F, IsFlatChain a b B ∧ IsAxialResponse b B (minimizerResponse a c.ρA b X)
end ColdStepAtMirrorFrames
end YangMills.Construction
end
