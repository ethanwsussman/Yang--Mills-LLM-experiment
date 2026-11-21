import YangMills.Construction.Towers.ResponseNearZeroPropertyFacts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.ResponseSaddle
open YangMills.Construction.PeriodicOperators (colourEdges idKernel compKernel)
open YangMills.Construction.Tower.FreeResolvents (trivialRescaledOperators)
open YangMills.Construction.Tower.BackgroundFieldResponse (responseKernel responseDefect)
open YangMills.Construction.Tower.ResponseProperties (CompSummableEverywhere)
structure HoldsAt (L j : ℕ) : Prop where
  smoothing_summable : CompSummableEverywhere (trivialRescaledOperators L j).Q (responseKernel L j)
  smoothing_eq : compKernel (trivialRescaledOperators L j).Q (responseKernel L j) =
    idKernel (colourEdges L j j)
  hessian_summable : CompSummableEverywhere (trivialRescaledOperators L j).X (responseKernel L j)
  defect_summable : CompSummableEverywhere (trivialRescaledOperators L j).Qt (responseDefect L j)
  hessian_eq : compKernel (trivialRescaledOperators L j).X (responseKernel L j) =
    compKernel (trivialRescaledOperators L j).Qt (responseDefect L j)
def SaddleEquations : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ j : ℕ, 1 ≤ j → HoldsAt L j
end YangMills.Construction.Tower.ResponseSaddle
end
