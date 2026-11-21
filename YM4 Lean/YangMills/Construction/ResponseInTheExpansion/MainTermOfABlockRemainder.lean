import YangMills.Construction.ColdStepAtMirrorFrames.SumAgainstThreeFlatResponses
import YangMills.Construction.ResponseInTheExpansion.FamiliesOnOneTorus
import YangMills.Construction.SummableBoundsOfTheFlow.ExpansionAlongAMotion
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Estimates
namespace WeightedResponses
variable {F : BlockFrame}
def unitForm (B : LevelForm F F.depth) (X : imaginaryQuaternions) :
    F.Site F.depth → Fin 4 → imaginaryQuaternions := fun z i => B z i • X
def BlockSecondDerivativeBound : Prop :=
  ∀ a : ℝ, 1 ≤ a → ∃ del Ca : ℝ, 0 < del ∧ 0 < Ca ∧ ∃ L₀ : ℕ, ∀ (F : BlockFrame) (δ σ e e₃ : ℝ) (Y : F.Cell)
    (c : Fin 2 → F.Site F.top × Fin 4) (B : Fin 2 → FormChain F) (W : Fin 2 → LevelForm F F.depth)
    (X : Fin 2 → imaginaryQuaternions)
    (r : F.Site F.depth → F.GaugeField F.depth → ℝ), Odd F.blockSide → L₀ ≤ F.blockSide → IsLargeCubicTorus F →
    0 < δ → δ ≤ del / 64 → 0 < σ →
    0 ≤ e → (∀ i, IsFlatChain a (c i) (B i)) → (∀ i, IsAxialResponse (c i) (B i) (W i)) → AreUnitVectors X →
    IsDecayingSiteFamily F.blockSide σ δ e e₃ r →
    |∑ y ∈ blockFineSites Y, mixedDerivAlong (r y) (uniformField F F.depth)
        ![unitForm (W 0) (X 0), unitForm (W 1) (X 1)]| ≤
      Ca * (F.blockSide : ℝ) ^ (50 / 640 : ℝ) * e / torusDecayFactor F.blockSide δ (bondSpan Y c)
end WeightedResponses
end YangMills.Construction
end
