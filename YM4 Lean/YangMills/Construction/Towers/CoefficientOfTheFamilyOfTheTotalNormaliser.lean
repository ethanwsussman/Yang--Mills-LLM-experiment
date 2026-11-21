import YangMills.Construction.OneLoopLaw.KernelsAndTensorFormOfASymbol
import YangMills.Construction.Towers.TheFamiliesOfTheTotalNormaliser
import YangMills.Construction.Towers.TheSymbolOfTheSecondDifferentialOfTheFunctional
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.NormaliserStiffness
open YangMills.Construction.OneLoopLaw.TemperedStiffness (secondPartialAtZero)
open YangMills.Construction.Tower.FullSpace (freePolarizationEntry)
def StiffnessIsMixedPartial : Prop :=
  ∀ (L : ℕ) (hL : 0 < L), Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ((OneLoopLaw.FunctionalStiffness.stiffnessConstant hL (logNormaliserFamily L k) : ℝ) : ℂ) =
      -secondPartialAtZero (freePolarizationEntry L k hL 0 1) 0 1
end YangMills.Construction.Tower.NormaliserStiffness
end
