import YangMills.Construction.ChessboardTori.StandingConventions
import YangMills.Construction.ClusterExpansionOfAStep.FlowOfTheExpansion
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ReflectedCopies
def IsAdmissibleSetup (P : TorusLumps.StepParameters) (Ξ : ℝ)
    (D : ChessboardTori.ChessboardSetup) : Prop :=
  D.L = P.side ∧ (∀ n : ℕ, n ≤ (D.K : ℕ) → P.y₁ ≤ (TorusLumps.couplingFlow P D.β n).1) ∧
    (TorusLumps.couplingFlow P D.β (D.K : ℕ)).1 ≤ Ξ
end ReflectedCopies
end YangMills.Construction
end
