import YangMills.Construction.ClusterExpansionOfAStep.SharesAndCostsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace HoledShares
open BlockAverages TorusFields TorusLumps StepCosts
variable {n : ℕ}
def LevelZeroShareIsLocal : Prop :=
  ∀ (ℓ : StepParameters), ℓ.Admissible → ∀ (n n' : ℕ) [NeZero n] [NeZero n'] (V : TorusField n)
    (V' : TorusField n') (y : TorusSite n) (y' : TorusSite n') (m : ℕ),
    ℓ.side ∣ n → ℓ.side ∣ n' → 2 ^ 16 + 4 ≤ m → 2 * m + 2 < n → 2 * m + 2 < n' →
    FieldsAgreeNear V V' y y' m → SameBlockPosition ℓ y y' →
    levelShare ℓ.coupling ℓ.side 0
        (Finset.univ \ thickening LumpContours.lumpRange (torusHotSites ℓ V)) y V =
      levelShare ℓ.coupling ℓ.side 0
        (Finset.univ \ thickening LumpContours.lumpRange (torusHotSites ℓ V')) y' V'
end HoledShares
end YangMills.Construction
end
