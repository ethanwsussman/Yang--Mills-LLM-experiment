import YangMills.Construction.ClusterExpansionOfAStep.SharesOfHoledFieldsForget
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ShareMeasurability
open YangMills.Construction.TorusFields YangMills.Construction.TorusLumps YangMills.Construction.ColdChain
open YangMills.Construction.HoledShares YangMills.Construction.StepCosts
def LevelShareOffHotMeasurable : Prop :=
  ∀ (ℓ : StepParameters) (δ lam ρA σA cg : ℝ) (N : ℕ → ℝ), ℓ.Admissible →
    ColdChainConstants ℓ.coupling δ ℓ.side lam ρA σA cg N →
    ℓ.threshold ≤ σA → ∀ (t n : ℕ) [NeZero n], IsBlockTorusSide ℓ n → ∀ Y : TorusSite n,
      Measurable fun V : TorusField n => levelShare ℓ.coupling ℓ.side (t + 1) (coldRegion ℓ V) Y V
end YangMills.Construction.ShareMeasurability
end
