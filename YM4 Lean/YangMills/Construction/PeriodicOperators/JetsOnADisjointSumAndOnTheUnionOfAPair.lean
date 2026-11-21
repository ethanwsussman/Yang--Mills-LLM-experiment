import YangMills.Construction.PeriodicOperators.TheNumberOfASaddleJet
import YangMills.Construction.Towers.TheJetsOfTheTwoOperatorFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators
section Pair
variable {I₁ I₂ : PeriodicData}
def sumIndexOfSigma : (PeriodicData.sigma (pairData I₁ I₂)).Carrier → (I₁.disjSum I₂).Carrier
  | ⟨0, i⟩ => .inl i
  | ⟨1, i⟩ => .inr i
def readOnSigma {F : PeriodicData}
    (T : (F.Carrier → ℂ) → (I₁.disjSum I₂).Carrier → (I₁.disjSum I₂).Carrier → ℂ) :
    (F.Carrier → ℂ) → (PeriodicData.sigma (pairData I₁ I₂)).Carrier →
      (PeriodicData.sigma (pairData I₁ I₂)).Carrier → ℂ :=
  fun ζ j i => T ζ (sumIndexOfSigma j) (sumIndexOfSigma i)
end Pair
namespace DisjSumJets
open JetQuad (IsInvertibleJet logNumber)
def Claim : Prop :=
  ∀ F I₁ I₂ : PeriodicData, IsPeriodic F → IsPeriodic I₁ → IsPeriodic I₂ →
    IsPeriodic (I₁.disjSum I₂) ∧
    ∀ T : (F.Carrier → ℂ) → (I₁.disjSum I₂).Carrier → (I₁.disjSum I₂).Carrier → ℂ,
      IsLocalOpFun F (PeriodicData.sigma (pairData I₁ I₂))
          (PeriodicData.sigma (pairData I₁ I₂)) (readOnSigma T) →
        IsLocalOpFun F (I₁.disjSum I₂) (I₁.disjSum I₂) T ∧
        ∀ (δ : ℝ) (p : Fin 4 → ℂ) (εp εm : F.UnitQuot → ℂ), 0 < δ → p ∈ imStrip δ →
          IsInvertibleJet δ p (jetAlong F (PeriodicData.sigma (pairData I₁ I₂))
              (PeriodicData.sigma (pairData I₁ I₂)) (readOnSigma T) p εp εm) →
            IsInvertibleJet δ p (jetAlong F (I₁.disjSum I₂) (I₁.disjSum I₂) T p εp εm) ∧
            logNumber p (jetAlong F (I₁.disjSum I₂) (I₁.disjSum I₂) T p εp εm) =
              logNumber p (jetAlong F (PeriodicData.sigma (pairData I₁ I₂))
                (PeriodicData.sigma (pairData I₁ I₂)) (readOnSigma T) p εp εm)
end DisjSumJets
end YangMills.Construction.PeriodicOperators
end
