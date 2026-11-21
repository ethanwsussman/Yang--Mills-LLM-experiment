import YangMills.Construction.ColdStepAtMirrorFrames.SumAgainstThreeFlatResponses
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
def CubicTorusCellGeometry : Prop :=
  (∀ F : BlockFrame, Odd F.blockSide → IsLargeCubicTorus F →
    (∀ (j : ℕ) (x y : F.Site j), siteSupDist x y = siteSupDist y x) ∧
    (∀ (j : ℕ) (x y z : F.Site j), siteSupDist x z ≤ siteSupDist x y + siteSupDist y z) ∧
    (∀ x y : F.Cell, cellSupDist x y = cellSupDist y x) ∧
    (∀ x y z : F.Cell, cellSupDist x z ≤ cellSupDist x y + cellSupDist y z) ∧
    ∀ x y : F.Site F.depth,
      F.blockSide * cellSupDist (enclosingCell x) (enclosingCell y) ≤ siteSupDist x y + F.blockSide) ∧
  ∀ r : ℝ, 0 < r → ∃ C : ℝ, 0 < C ∧ ∀ F : BlockFrame, Odd F.blockSide → IsLargeCubicTorus F →
    ∀ z : F.Cell,
    ∑ b ∈ fineBonds F, Real.exp (-(r * cellSupDist (enclosingCell b.1) z)) ≤
      C * (F.blockSide : ℝ) ^ 4
end ColdStepAtMirrorFrames
end YangMills.Construction
end
