import YangMills.Construction.ClusterExpansionOfAStep.ConstantsOfTheColdChain
import YangMills.Construction.ClusterExpansionOfAStep.SharesAndCostsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace HoledShares
open TorusFields TorusLumps StepCosts ColdChain
variable {n : ℕ}
def coldRegion (ℓ : StepParameters) [NeZero n] (V : TorusField n) : Finset (TorusSite n) :=
  Finset.univ \ thickening LumpContours.lumpRange (torusHotSites ℓ V)
def NoHotLumpNear (ℓ : StepParameters) [NeZero n] (V : TorusField n) (y : TorusSite n) (m : ℕ) : Prop :=
  ∀ z ∈ torusHotSites ℓ V, m < supDist y z
def SharesOfHoledFieldsForget : Prop :=
  ∀ (δ lam ρ σA cg : ℝ) (N : ℕ → ℝ) (ℓ : StepParameters),
    ColdChainConstants ℓ.coupling δ ℓ.side lam ρ σA cg N → ℓ.Admissible → ℓ.threshold ≤ σA →
    ∀ (t n n' : ℕ) [NeZero n] [NeZero n'] (V : TorusField n) (V' : TorusField n') (y : TorusSite n)
      (y' : TorusSite n') (m : ℕ),
      ℓ.side ∣ n → 2 ^ 16 ≤ m → 2 * m + 2 < n → 2 * m + 2 < n' → FieldsAgreeNear V V' y y' m →
      (ℓ.side ∣ n' → (SameBlockPosition ℓ y y' ∨ (NoHotLumpNear ℓ V y m ∧ NoHotLumpNear ℓ V' y' m)) →
        |levelShare ℓ.coupling ℓ.side (t + 1) (coldRegion ℓ V) y V -
            levelShare ℓ.coupling ℓ.side (t + 1) (coldRegion ℓ V') y' V'| ≤
          ℓ.threshold ^ 2 * N 0 * Real.exp (-δ * ((m - 2 ^ 16 : ℕ) : ℝ))) ∧
      (TorusFields.IsCold ℓ.threshold V' → NoHotLumpNear ℓ V y m →
        |levelShare ℓ.coupling ℓ.side (t + 1) (coldRegion ℓ V) y V -
            levelShare ℓ.coupling ℓ.side (t + 1) Finset.univ y' V'| ≤
          ℓ.threshold ^ 2 * N 0 * Real.exp (-δ * ((m - 2 ^ 16 : ℕ) : ℝ)))
end HoledShares
end YangMills.Construction
end
