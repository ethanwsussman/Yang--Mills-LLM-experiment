import YangMills.Construction.ConfigurationSpace.WhitneyPiecesCubesConstants
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigurationSpace
open BumpFunctions WhitneyScales
def BlockProdDerivBound : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ (j : ℕ) (z : IntPoint n),
    ofRealFun (blockProd j z) ∈ smoothSet (Config n) ∧
    ∀ (α : MultiIdx (CoordIndex n)) (x : Config n),
      ‖configMultiDeriv α (ofRealFun (blockProd j z)) x‖ ≤
        integralConstBound ^ (4 * n) *
          (2 * blockConst * whitneyRatio⁻¹ * 2 ^ j) ^ MultiIdx.order α *
          ((MultiIdx.order α).factorial : ℝ) ^ 2
end YangMills.Construction.ConfigurationSpace
end
