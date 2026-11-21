import YangMills.Construction.OneLoopLaw.KernelsAndTensorFormOfASymbol
import Mathlib
set_option autoImplicit false
open Filter Asymptotics
open scoped Topology
noncomputable section
namespace YangMills.Construction.OneLoopLaw.TemperedStiffness
def TemperedStiffnessClaim : Prop :=
  ∀ (L : ℕ) (hL : 0 < L), Conventions.IsAdmissibleBlockingFactor L →
    ∀ (F : PeriodicOperators.Tempered.FieldFamily L) (δ : ℝ) (π : PeriodicOperators.Tempered.SymbolArray) (e : ℕ → ℝ),
      PeriodicOperators.Tempered.IsLatticeFunctional L F → PeriodicOperators.Tempered.IsTemperedWitness L F δ π e →
        FirstVariationVanishes L F ∧ KernelsTendTo L F π ∧ KernelsRealAndDecaying δ π ∧
          ∃ b : ℝ, HasTransverseForm π b ∧
            FunctionalStiffness.HasStiffnessConstant hL F (FunctionalStiffness.stiffnessConstant hL F) ∧
            ∀ μ ν : Fin 4, μ ≠ ν →
              StiffnessFormulas π (FunctionalStiffness.stiffnessConstant hL F) b μ ν
end YangMills.Construction.OneLoopLaw.TemperedStiffness
end
