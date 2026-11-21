import YangMills.Construction.FourPointCondition.FourPointFunctionDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open Filter Set
namespace YangMills.Construction.FourPointCondition
def cumulantLawsAlongFlow : Prop :=
  ResponseInTheExpansion.HoldsOnParameterFamilies fun Tb y => ∃ Kr : WeightedResponses.ResponseParameters,
    Kr.Admissible (Tb.stepParameters y) ∧ ∀ vt : ℝ, 0 < vt → vt ≤ 1 →
    ∃ C X : ℝ, ∀ (β : ℝ) (k : ℕ), (∀ j ≤ k, X ≤ (TorusLumps.couplingFlow (Tb.stepParameters y) β j).1) →
      ∃ al : ℕ → ℝ, ResponseInTheExpansion.IsChainResponseCoeff (Tb.stepParameters y) Kr β k al ∧
        3 / 4 ≤ al k ∧ al k ≤ 5 / 4 ∧
        ∀ (K m : ℕ) (d e : ℝ),
          Real.exp (Real.log (TorusLumps.couplingFlow (Tb.stepParameters y) β k).1 ^ 3) ≤
            PeriodicLattice.torusSide (Tb.stepParameters y).side m / levelMesh (Tb.stepParameters y).side K k →
          IsLevelWindow (Tb.stepParameters y) (TorusLumps.couplingFlow (Tb.stepParameters y) β k).1 k
            (d / levelMesh (Tb.stepParameters y).side K k) e →
          CumulantLawsOnTorus (Tb.stepParameters y) vt C (TorusLumps.couplingFlow (Tb.stepParameters y) β k).1
            (al k) e β K m d
end YangMills.Construction.FourPointCondition
end
