import YangMills.Construction.Torus.AdmissiblePairs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Weighted
namespace SeparatedChain
variable {D : TorusData} (B : SeparatedChain D)
def AvgPreservesBlockUnion (W : Set D.Space) : Prop :=
  (∀ w ∈ B.layerSpaceOn W, (B.avgOpAdjoint w : D.BareSite → ℝ) ∈ B.bareSpaceOn W) ∧
    (∀ f : ↥(B.bareSpaceOn W),
      B.avgOp (B.bareSpaceOnIncl W f) ∈ B.layerSpaceOn W) ∧
    (∀ w : ↥(B.layerSpaceOn W),
      (B.restrictBare W (B.avgOpAdjoint w) : D.BareSite → ℝ) =
        (B.avgOpAdjoint w : D.BareSite → ℝ)) ∧
    ∀ f : ↥(B.bareSpaceOn W),
      (B.restrictLayer W (B.avgOp (B.bareSpaceOnIncl W f)) :
          B.LayerFn) =
        B.avgOp (B.bareSpaceOnIncl W f)
def AdmissibleAvgGreenSqUnrestricted (W : Set D.Space) (𝔟 : Set D.Bond) : Prop :=
  ∀ (w : ↥(B.layerSpaceOn W)) (g : ↥(B.bareSpaceOn W)),
    (g : D.BareSite → ℝ) = (B.avgOpAdjoint w : D.BareSite → ℝ) →
      (B.admissibleAvgGreenSq W 𝔟 w : B.LayerFn) =
        B.avgOp (B.bareSpaceOnIncl W
          ((B.admissibleGreen W 𝔟 * B.admissibleGreen W 𝔟) g))
end SeparatedChain
def BlockUnionAveragingStatement : Prop :=
  ∀ (D : TorusData) (B : SeparatedChain D) (W : Set D.Space),
    B.IsBlockUnion W →
      B.AvgPreservesBlockUnion W ∧
        ∀ 𝔟 : Set D.Bond, B.IsAdmissiblePair W 𝔟 →
          B.AdmissibleAvgGreenSqUnrestricted W 𝔟
end YangMills.Construction.Weighted
end
