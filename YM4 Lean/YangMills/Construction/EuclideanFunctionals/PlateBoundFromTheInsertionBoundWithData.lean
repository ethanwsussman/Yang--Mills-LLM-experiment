import YangMills.Construction.EuclideanFunctionals.FractionsAndConstantsOfThePlateBound
import YangMills.Construction.EuclideanFunctionals.InsertionBoundAndPlateBound
import Mathlib
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.ProductBoundFromInsertion
variable {m : SharpScale} {S : ConnFamily} (σ : EuclidFunctionalWithRecon m S)
def BoundedByL1OnSlab (p C cS cPar cCau : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ h ∈ C1c ℝ, tsupport h ⊆ thinSlab cS η →
    ∀ F ∈ finCombIn {y | η / 4 < y 3}, ∀ A ∈ finCombIn {y | η / 4 < y 3},
      ‖insertion S F (fun y => (h y : ℂ)) A‖ ≤
        1 / 2 * productConst m p C cPar cCau * η ^ (-productExponent p) *
          l1Norm h * heightNorm σ (η / 4) F * heightNorm σ (η / 4) A
def Main : Prop :=
  ∀ (m : SharpScale) (S : ConnFamily) (σ : EuclidFunctionalWithRecon m S)
    (p C cI cS cPar cCau : ℝ),
    σ.ConeCondition → InsertionBoundHolds σ p C cI →
    ProductBoundParams p C cI cS cPar cCau →
      BoundedByL1OnSlab σ p C cS cPar cCau ∧
      ProductBoundHolds σ (productExponent p)
        (fun φ => productConst m p C cPar cCau * l1Norm φ) cS
end YangMills.Construction.EuclideanFunctionals.ProductBoundFromInsertion
