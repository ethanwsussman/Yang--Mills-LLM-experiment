import YangMills.Construction.PeriodicOperators.SecondDifferentialsOfLogarithmsOfDeterminants
import YangMills.Construction.Towers.TheJetsOfTheTwoOperatorFunctions
import Mathlib
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.TorusDeterminants
open YangMills.Construction.Matrices
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.LogDetSecondDerivs (quotOperator)
def Claim : Prop :=
  ∀ (L : ℕ) (hL : 0 < L), Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → ∀ R : ℝ,
    (∃ ρ : ℝ, IsLocalWith (fieldPeriodicData L k hL) (vectorIndices L k) (vectorIndices L k)
      (vectorOpFn L k hL) ρ R) →
    (∃ ρ : ℝ, IsLocalWith (fieldPeriodicData L k hL) (ghostIndices L k) (ghostIndices L k)
      (ghostOpFn L k hL) ρ R) →
    ∀ n : ℕ, 0 < n → 4 * R < ((2 * L ^ n : ℕ) : ℝ) →
    ∃ ε : ℝ, 0 < ε ∧ ∀ (ζ : Tower.PeriodicField L n k) (r : Tower.RealPeriodicField L n k), ζ.RealizedBy r →
      IsSupBelow (fieldPeriodicData L k hL) (ζ.pauliCoeffs hL) ε →
      Tower.BackgroundFunctionalWellDefined
        (IdentityExpChart.expForm (r.1 : Tower.Edge L n k 0 → ComplexMatrix2)) r.2.1 r.2.2 ∧
      |Tower.hessianSaddleDet
        (IdentityExpChart.expForm (r.1 : Tower.Edge L n k 0 → ComplexMatrix2)) r.2.1 r.2.2| =
        ‖LinearMap.det (quotOperator (fieldPeriodicData L k hL) (vectorIndices L k)
          (vectorOpFn L k hL) (2 * L ^ n) (ζ.onQuotient hL))‖ ∧
      |Tower.ghostSaddleDet L n k
        (IdentityExpChart.expForm (r.1 : Tower.Edge L n k 0 → ComplexMatrix2))| =
        ‖LinearMap.det (quotOperator (fieldPeriodicData L k hL) (ghostIndices L k)
          (ghostOpFn L k hL) (2 * L ^ n) (ζ.onQuotient hL))‖
end YangMills.Construction.Tower.FullSpace.TorusDeterminants
end
