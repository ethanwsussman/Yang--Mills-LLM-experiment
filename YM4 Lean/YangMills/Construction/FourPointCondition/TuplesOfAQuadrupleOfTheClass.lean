import YangMills.Construction.ResponseInTheExpansion.ConnectedFunctionsOfTheExpansion
import YangMills.Construction.Torus.SeparatedQuadruples
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FourPointCondition
open TestFunctions PeriodicLattice ResponseInTheExpansion TorusLumps QuadrupleClasses Conventions
def normalizedQuadrupleIsTestTuple : Prop :=
  ∀ (p : StepParameters) (K m : ℕ+) (hs : IsAdmissibleBlockingFactor p.side) (d θ : ℝ)
    (f : Fin 4 → FourTorus p.side m → ℝ),
    f ∈ quadsTorus ⟨p.side, hs, K, m⟩ d θ →
    (∀ i, 0 < uniformNorm (f i)) ∧ IsSeparatedTestTuple p m d θ (fun i x => (uniformNorm (f i))⁻¹ * f i x) ∧
      ∀ i j, i ≠ j → IsSeparatedTestTuple p m d θ
        ![fun x => (uniformNorm (f i))⁻¹ * f i x, fun x => (uniformNorm (f j))⁻¹ * f j x]
end YangMills.Construction.FourPointCondition
end
