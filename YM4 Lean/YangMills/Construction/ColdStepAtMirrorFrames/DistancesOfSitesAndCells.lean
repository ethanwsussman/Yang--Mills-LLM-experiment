import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionOfAFamilyOnTori
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames
def SupDistCellComparison : Prop :=
  (∀ (F : BlockFrame) (j : ℕ) (y z u : F.Site j), siteSupDist y y = 0 ∧ siteSupDist y z = siteSupDist z y ∧
    siteSupDist y u ≤ siteSupDist y z + siteSupDist z u) ∧
  (∀ (F : BlockFrame) (j : ℕ) (y : F.Site j) (o : Fin 4 → ℤ) (M : ℕ), (∀ i, (o i).natAbs ≤ M) →
    siteSupDist y (y + siteOfCoords j o) ≤ M) ∧
  ∀ (F : BlockFrame), Odd F.blockSide → (∀ i, 0 < F.extent i) →
    (∀ x x' : F.Site F.depth, (F.blockSide : ℝ) *
      ((siteSupDist (enclosingCell x) (enclosingCell x') : ℝ) - 1) ≤ siteSupDist x x') ∧
    (∀ x x' : F.Site F.depth, (siteSupDist x x' : ℝ) ≤
      (F.blockSide : ℝ) * ((siteSupDist (enclosingCell x) (enclosingCell x') : ℝ) + 1)) ∧
    ∀ y : F.Cell, enclosingCell (refineSite y) = y
end ColdStepAtMirrorFrames
end YangMills.Construction
end
