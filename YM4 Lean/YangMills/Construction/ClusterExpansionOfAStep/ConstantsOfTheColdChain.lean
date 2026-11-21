import YangMills.Construction.ColdChainAtEveryLevel.PropertiesOfTheColdChainForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace ColdChain
open YangMills.Construction.BlockAverages
def ColdChainConstants (a δ : ℝ) (L : ℕ) (lam ρ σA cg : ℝ) (N : ℕ → ℝ) : Prop :=
  0 < δ ∧ δ ≤ 1 / 8 ∧ 0 < lam ∧ 0 < ρ ∧ ρ ≤ 1 ∧ 0 < σA ∧ 0 < cg ∧ (∀ j, 0 < N j) ∧
    ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
      IsOrthantRegular S m →
      ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ σA → IsCold S F.top s V →
        HasColdMinimizer a ρ (N 0) s S V ∧ HasCoerciveHessian a lam ρ σA S V ∧
        HasRegularCellShares a δ s N S V ∧ HasRegularCoordinates a δ ρ N S V ∧
        HasHotPlaquettePenalty a cg σA s S V ∧
        ∀ (F' : BlockFrame) (S' : Finset F'.Cell) (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell)
          (r : ℕ), F'.blockSide = L → F'.depth = F.depth → IsAdmissibleAmbient F' → IsOrthantRegular S' m →
          IsCold S' F'.top s V' →
          AgreeOnBall S V S' V' Y Y' r →
          HasComparableCellShares a δ s N S V S' V' Y Y' r ∧
          HasComparableCoordinates a δ ρ s N S V S' V' Y Y' r
end ColdChain
end YangMills.Construction
end
