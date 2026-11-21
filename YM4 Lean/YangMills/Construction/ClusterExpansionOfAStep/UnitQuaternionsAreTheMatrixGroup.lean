import YangMills.Construction.ClusterExpansionOfAStep.UnitQuaternionsAsSpecialUnitaryMatrices
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction
namespace ClusterExpansionOfAStep
open SoftAverages TorusFields Matrices
def UnitQuaternionHaarTraceNorm : Prop :=
  haarUnit.map unitQuaternionEquivSpecialUnitary = ComplexMatrix2.haarProb ∧
    (∀ u : BlockAverages.UnitQuaternion,
      (u : ℍ[ℝ]).re = (1 / 2) * (ComplexMatrix2.fullTrace (unitQuaternionEquivSpecialUnitary u : ComplexMatrix2)).re ∧
        (ComplexMatrix2.fullTrace (unitQuaternionEquivSpecialUnitary u : ComplexMatrix2)).im = 0) ∧
    ∀ q : ℍ[ℝ], ComplexMatrix2.operatorNorm (quaternionToMatrix q) = ‖q‖
end ClusterExpansionOfAStep
end YangMills.Construction
end
