import YangMills.Construction.FourPointCondition.FourPointFunctionDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open Filter Set
namespace YangMills.Construction.FourPointCondition
def cumulantLawsAtWindowLevel : Prop :=
  ResponseInTheExpansion.HoldsOnParameterFamilies fun Tb y => ∀ Kr : WeightedResponses.ResponseParameters,
    Kr.Admissible (Tb.stepParameters y) → ∀ vt : ℝ, 0 < vt → vt ≤ 1 →
    ∃ C X : ℝ, ∀ (β : ℝ) (k : ℕ) (al : ℕ → ℝ),
      (∀ j ≤ k, X ≤ (TorusLumps.couplingFlow (Tb.stepParameters y) β j).1) →
      ResponseInTheExpansion.IsChainResponseCoeff (Tb.stepParameters y) Kr β k al →
      ∀ (K m : ℕ) (d : ℝ),
        Real.exp (Real.log (TorusLumps.couplingFlow (Tb.stepParameters y) β k).1 ^ 3) ≤
          PeriodicLattice.torusSide (Tb.stepParameters y).side m / levelMesh (Tb.stepParameters y).side K k →
        2 ^ 12 * ((Tb.stepParameters y).side : ℝ) *
            (TorusLumps.clusterRange (TorusLumps.couplingFlow (Tb.stepParameters y) β k).1 : ℝ) ≤
          d / levelMesh (Tb.stepParameters y).side K k →
        d / levelMesh (Tb.stepParameters y).side K k ≤
          (TorusLumps.couplingFlow (Tb.stepParameters y) β k).1 ^ ((1 : ℝ) / 90) →
        CumulantLawsOnTorus (Tb.stepParameters y) vt C (TorusLumps.couplingFlow (Tb.stepParameters y) β k).1
          (al k) 0 β K m d
end YangMills.Construction.FourPointCondition
end
