import YangMills.Construction.Towers.PropertiesOfTheRescaledLattice
import YangMills.Construction.Towers.TheJetsOfTheTwoOperatorFunctions
import Mathlib
noncomputable section
namespace YangMills.Construction.PeriodicOperators.DiagonalScaling
open JetQuad (IsInvertibleJet logNumber)
open YangMills.Construction.Tower.RescaledConditions (sumDiagScale)
def PreservesJetIndex : Prop :=
  ∀ F I₁ I₂ : PeriodicData, IsPeriodic F → IsPeriodic I₁ → IsPeriodic I₂ →
    ∀ x y x' y' : ℂ, x ≠ 0 → y ≠ 0 → x' ≠ 0 → y' ≠ 0 →
      ∀ M : (F.Carrier → ℂ) → (I₁.disjSum I₂).Carrier → (I₁.disjSum I₂).Carrier → ℂ,
        IsLocalOpFun F (I₁.disjSum I₂) (I₁.disjSum I₂) M →
          IsLocalOpFun F (I₁.disjSum I₂) (I₁.disjSum I₂)
              (fun ζ => sumDiagScale (S := I₁.Carrier) (B := I₂.Carrier) x y x' y' (M ζ)) ∧
          ∀ (δ : ℝ) (p : Fin 4 → ℂ) (εPlus εMinus : F.UnitQuot → ℂ), 0 < δ → p ∈ imStrip δ →
            IsInvertibleJet δ p (jetAlong F (I₁.disjSum I₂) (I₁.disjSum I₂) M p εPlus εMinus) →
              IsInvertibleJet δ p (jetAlong F (I₁.disjSum I₂) (I₁.disjSum I₂)
                  (fun ζ => sumDiagScale (S := I₁.Carrier) (B := I₂.Carrier) x y x' y' (M ζ))
                  p εPlus εMinus) ∧
              logNumber p (jetAlong F (I₁.disjSum I₂) (I₁.disjSum I₂)
                  (fun ζ => sumDiagScale (S := I₁.Carrier) (B := I₂.Carrier) x y x' y' (M ζ))
                  p εPlus εMinus) =
                logNumber p
                  (jetAlong F (I₁.disjSum I₂) (I₁.disjSum I₂) M p εPlus εMinus)
end YangMills.Construction.PeriodicOperators.DiagonalScaling
end
