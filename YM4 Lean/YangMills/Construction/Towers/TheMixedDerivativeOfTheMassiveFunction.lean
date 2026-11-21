import YangMills.Construction.OneLoopLaw.KernelsAndTensorFormOfASymbol
import YangMills.Construction.Towers.TheFunctionOfTheMassiveJets
import YangMills.Construction.Towers.TheMassiveFunctional
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.MassiveOpFunctions.MixedPartialOfMassiveLogFn
open FullSpace.BackgroundJets
def Claim : Prop :=
  ∀ (L : ℕ) (hpos : 0 < L), Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∀ m : ℝ, 0 < m →
    -OneLoopLaw.TemperedStiffness.secondPartialAtZero (fun q => massiveLogFn L k q 0 1 m) 0 1 =
      (massiveStiffness hpos (finestMesh L k ^ 2 * m) : ℂ)
end YangMills.Construction.Tower.MassiveOpFunctions.MixedPartialOfMassiveLogFn
end
