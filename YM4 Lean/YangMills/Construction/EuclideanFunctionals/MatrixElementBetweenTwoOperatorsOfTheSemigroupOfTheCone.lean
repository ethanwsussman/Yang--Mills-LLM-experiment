import YangMills.Construction.EuclideanFunctionals.ClosedInsertionDomainAndInsertionFunctionOfATriple
import YangMills.Construction.EuclideanFunctionals.SemigroupOfTheCone
import YangMills.Construction.EuclideanFunctionals.StandingDataOfTheStudyFromOneInsertionToPlates
import Mathlib
set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals
def timeEighthPoint (η : ℝ) : Fin 4 → ℂ :=
  SpectralPoint.ofRealPoint ((η / 8) • timeVec)
namespace EuclidFunctionalWithRecon
variable {c : SharpScale} {S : ConnFamily} (σ : EuclidFunctionalWithRecon c S)
def coneSandwich (η : ℝ) (Z : σ.space →L[ℂ] σ.space)
    (u v : σ.space) (z : Fin 4 → ℂ) : ℂ :=
  ⟪u, (σ.coneOp (timeEighthPoint η + z) * Z *
    σ.coneOp (timeEighthPoint η - z)) v⟫_ℂ
end EuclidFunctionalWithRecon
namespace ConeSandwich
open SpectralPoint
def Holds : Prop :=
  ∀ {c : SharpScale} {S : ConnFamily} (σ : EuclidFunctionalWithRecon c S), σ.ConeCondition →
    ∀ η : ℝ, 0 < η → η ≤ 1 →
    ∀ (Z : σ.space →L[ℂ] σ.space) (u v : σ.space),
      (IsOpen (complexExtensionDomain η) ∧
        closure (complexExtensionDomain η) = closedComplexExtensionDomain η ∧
        (∀ x : R4, ofRealPoint x ∈ complexExtensionDomain η ↔ |x 3| < η / 8) ∧
        ∀ x : R4, ofRealPoint x ∈ closedComplexExtensionDomain η ↔ |x 3| ≤ η / 8) ∧
      (∀ z : Fin 4 → ℂ,
        η / 8 - |(z 3).re| - ∑ j : Fin 3, |(z j.castSucc).im| ≤
            coneMargin (timeEighthPoint η + z) ∧
          η / 8 - |(z 3).re| - ∑ j : Fin 3, |(z j.castSucc).im| ≤
            coneMargin (timeEighthPoint η - z)) ∧
      (∀ z ∈ closedComplexExtensionDomain η,
        timeEighthPoint η + z ∈ pyramidDomain ∧
          timeEighthPoint η - z ∈ pyramidDomain ∧
          ‖σ.coneSandwich η Z u v z‖ ≤ ‖Z‖ * ‖u‖ * ‖v‖) ∧
      ContinuousOn (σ.coneSandwich η Z u v) (closedComplexExtensionDomain η) ∧
      IsHolomorphicFn (complexExtensionDomain η) (σ.coneSandwich η Z u v)
end ConeSandwich
end YangMills.Construction.EuclideanFunctionals
