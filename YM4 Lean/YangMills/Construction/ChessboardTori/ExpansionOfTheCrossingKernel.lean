import YangMills.Construction.ChessboardTori.CrossingKernelAndItsExpansionFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ChessboardTori.KernelExpansion
open TransferSetup
def wordSeriesTerm (D : ChessboardSetup) (u u' : Conventions.StandingParameters.gaugeGroup)
    (γ : MatrixWord) : ℂ :=
  (poissonWeight D γ.length : ℂ) * starRingEnd ℂ (wordMonomial γ u) * wordMonomial γ u'
def indexSeriesTerm {D : ChessboardSetup} (T : TransferSetup D) (x y : T.EdgeField)
    (α : T.WordIndex) : ℂ :=
  (T.indexWeight α : ℂ) * starRingEnd ℂ (T.indexMonomial α x) * T.indexMonomial α y
def Statement : Prop :=
  ∀ (D : ChessboardSetup) (T : TransferSetup D),
    (∀ u u' : Conventions.StandingParameters.gaugeGroup,
      (∀ γ : MatrixWord, ‖wordMonomial γ u‖ ≤ 1) ∧
      HasSum (fun γ : MatrixWord => poissonWeight D γ.length * ‖wordMonomial γ u‖ ^ 2) 1 ∧
      Summable (fun γ : MatrixWord => ‖wordSeriesTerm D u u' γ‖) ∧
      HasSum (wordSeriesTerm D u u') (boltzmannFactor D (u⁻¹ * u'))) ∧
    (∀ x y : T.EdgeField,
      HasSum (fun α : T.WordIndex => T.indexWeight α * ‖T.indexMonomial α x‖ ^ 2) 1 ∧
      Summable (fun α : T.WordIndex => ‖indexSeriesTerm T x y α‖) ∧
      HasSum (indexSeriesTerm T x y)
        (∏ b : T.PositiveTransverseEdge, boltzmannFactor D ((x b)⁻¹ * y b))) ∧
    (∀ α : T.WordIndex, Continuous (T.normalizedMonomial α)) ∧
    (∀ x y : T.EdgeField,
      Summable (fun α : T.WordIndex => ‖T.normalizedMonomial α x‖ ^ 2) ∧
      ∑' α : T.WordIndex, ‖T.normalizedMonomial α x‖ ^ 2 ≤ 1 ∧
      Summable (fun α : T.WordIndex => ‖T.normalizedMonomial α x‖ * ‖T.normalizedMonomial α y‖) ∧
      ∑' α : T.WordIndex, ‖T.normalizedMonomial α x‖ * ‖T.normalizedMonomial α y‖ ≤ 1 ∧
      HasSum (fun α : T.WordIndex =>
          starRingEnd ℂ (T.normalizedMonomial α x) * T.normalizedMonomial α y)
        (T.transferKernel x y))
end YangMills.Construction.ChessboardTori.KernelExpansion
end
