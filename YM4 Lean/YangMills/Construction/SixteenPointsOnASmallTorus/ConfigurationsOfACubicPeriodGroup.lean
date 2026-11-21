import YangMills.Construction.ChessboardTori.PeriodGroupsAndTheirLattices
import YangMills.Construction.ResponseInTheExpansion.WeightsOfAnExpansion
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.SmallTorusCopies
def cubicPeriodFieldsStatement : Prop :=
  ∀ (D : ChessboardTori.ChessboardSetup) (P : ChessboardTori.PeriodSubgroup D) (m : ℕ) [NeZero m],
    (∀ μ, P.mult μ = (m : ℤ)) →
    ∃ (Ψ : P.GaugeConfig → TorusFields.TorusField m) (τ : WeightedResponses.OrientedPlaquette m ≃ P.Face),
      MeasurePreserving Ψ P.haarMeasure (TorusFields.fieldHaar m) ∧
      (∀ U, P.wilsonAction U = TorusFields.wilsonAction Finset.univ (Ψ U)) ∧
      ∀ (U : P.GaugeConfig) (p : WeightedResponses.OrientedPlaquette m),
        P.faceEnergy U (τ p) = WeightedResponses.plaquetteEnergyOf (Ψ U) p.1 ∧
        P.faceCenter (τ p) = P.proj fun μ => D.mesh / 2 * ((WeightedResponses.doubledBarycentre p.1 μ).val : ℝ)
end YangMills.Construction.SmallTorusCopies
end
