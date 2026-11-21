import YangMills.Construction.HullsInEveryVolume.LimitDefs
import YangMills.Construction.LawByMomentsOfTheFlow.ComponentsOfTheLaw
import YangMills.Construction.LawByMomentsOfTheFlow.MeanScoresHaveMoments
import YangMills.Construction.LawByMomentsOfTheFlow.NumbersOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
namespace MomentPoint
variable {Λ : MomentParameters} (S : MomentPoint Λ)
def centredStateMoment {K : ℕ} (ρ : Measure (InfiniteLattice.RefinedGaugeField Λ.stepParams.side K))
    (c : Fin Λ.k → ℝ) (B : Finset (Fin Λ.k)) : ℝ :=
  ∫ U, ∏ i ∈ B, (InfiniteLattice.cutoffSmearedEnergyRe (S.rescaledTestFunction i) U - c i) ∂ρ
structure SameDataOtherSide (S' : MomentPoint Λ) : Prop where
  fn_eq : S'.data.fn = S.data.fn
  windowLevel_eq : S'.data.windowLevel = S.data.windowLevel
  scaleLevel_eq : S'.data.scaleLevel = S.data.scaleLevel
  center_eq : S'.data.center = S.data.center
  β_eq : S'.β = S.β
end MomentPoint
def componentMomentStatement : Prop :=
  ForAllHullParameters fun Λ => ∃ C X₀ : ℝ, 1 ≤ X₀ ∧ ∀ (K : ℕ) (β : ℝ),
    WeightedResponses.couplingWindowTop Λ.stepParams Λ.g ≤ β →
    WeightedResponses.IsFirstPassage Λ.stepParams (WeightedResponses.couplingWindowTop Λ.stepParams Λ.g) β K →
    ∀ ν : Measure (InfiniteLattice.RefinedGaugeField Λ.stepParams.side K),
      (∃ ms, TorusLimits.IsTorusLimitAlong Λ.stepParams.side K β ν ms) →
    ∀ (p : ℕ), 1 ≤ p → ∀ κ : Kernel (InfiniteLattice.RefinedGaugeField Λ.stepParams.side K)
        (InfiniteLattice.RefinedGaugeField Λ.stepParams.side K),
      TorusLimits.IsPeriodicConditionalKernel Λ.stepParams.side K ν p κ →
      ∀ S : MomentPoint Λ, S.data.windowLevel = K → S.β = β →
        ∃ c : Fin Λ.k → ℝ, ∀ᵐ U ∂ν,
          (S.scaleCoupling ≤ X₀ → ∀ B : Finset (Fin Λ.k), |S.centredStateMoment (κ U) c B| ≤ C) ∧
          (X₀ ≤ S.scaleCoupling → ∀ δ : ℝ, 0 < δ → ∃ (S' : MomentPoint Λ) (d : ℕ)
            (_ : S'.lastSeparated + d = S'.data.windowLevel)
            (μ : Measure (LevelChain Λ.stepParams.side (S'.lastSeparated + d) (S'.data.period Λ.stepParams.side))),
              S.SameDataOtherSide S' ∧
              IsCanonicalGaussian
                (levelEnergy Λ.stepParams.coupling (S'.lastSeparated + d) (S'.data.period Λ.stepParams.side)) μ ∧
              ∀ B : Finset (Fin Λ.k),
                |S.scaleCoupling ^ B.card * S.centredStateMoment (κ U) c B -
                    ∫ X, ∏ i ∈ B, S'.halfForm d (S'.data.period Λ.stepParams.side) i X ∂μ| ≤
                  C * (S.range : ℝ) ^ (4 * B.card + 3) * S.scaleCoupling ^ (-(1 / 2) + 1 / 1000 : ℝ) + δ ∧
                |∫ X, ∏ i ∈ B, S'.halfForm d (S'.data.period Λ.stepParams.side) i X ∂μ| ≤
                  C * (S.range : ℝ) ^ (4 * B.card) * S.scaleCoupling ^ ((1 : ℝ) / 1000))
end YangMills.Construction.MomentLaw
end
