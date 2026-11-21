import YangMills.Construction.ColdChainAtEveryLevel.ChartsChainsAndShares
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BlockAverages
variable {F : BlockFrame}
theorem minimalCellShare_eq_of_chainMap {a : ℝ} {S S' : Finset F.Cell} {V V' : F.GaugeField F.top} {Y Y' : F.Cell}
    (T T' : F.FieldChain → F.FieldChain)
    (hT : ∀ X : F.FieldChain, X F.top = V → T X F.top = V')
    (hT' : ∀ X : F.FieldChain, X F.top = V' → T' X F.top = V)
    (hTt : ∀ X : F.FieldChain, X F.top = V → chainAction a S' (T X) = chainAction a S X)
    (hTt' : ∀ X : F.FieldChain, X F.top = V' → chainAction a S (T' X) = chainAction a S' X)
    (hs : ∀ X : F.FieldChain, X F.top = V' → cellShare a S Y (T' X) = cellShare a S' Y' X)
    (hex : ∃ X, IsMinimalChain a S' V' X)
    (hone : ∀ X, IsMinimalChain a S V X → cellShare a S Y X = minimalCellShare a S Y V) :
    minimalCellShare a S' Y' V' = minimalCellShare a S Y V := by
  have hX := hex.choose_spec
  have hmin : IsMinimalChain a S V (T' hex.choose) := by
    refine ⟨hT' _ hX.1, fun X₁ h₁ => ?_⟩
    rw [hTt' _ hX.1, ← hTt X₁ h₁]
    exact hX.2 _ (hT X₁ h₁)
  unfold minimalCellShare
  rw [dif_pos hex, ← hs _ hX.1]
  exact hone _ hmin
def gaugeInvarianceOfShareStatement : Prop :=
  ∀ (F : BlockFrame) (a : ℝ) (S : Finset F.Cell) (V : F.GaugeField F.top) (γ : F.Cell → UnitQuaternion), 0 ≤ a →
    Odd F.blockSide →
    (∀ X, IsMinimalChain a S V X → ∀ Y, cellShare a S Y X = minimalCellShare a S Y V) →
    ∀ Y, minimalCellShare a S Y (gaugeTransform γ V) = minimalCellShare a S Y V
end BlockAverages
end YangMills.Construction
end
