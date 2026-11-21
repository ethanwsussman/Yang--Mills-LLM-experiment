import YangMills.Construction.Towers.TheFieldsAndTheTwoOperatorFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.IteratesPreserveRealFields
def Holds : Prop :=
  ∀ L : ℕ, YangMills.Construction.Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    (∀ A ∈ YangMills.Construction.Tower.FullSpace.edgeFormSpace
        (YangMills.Construction.Tower.meshAt L k 0),
      YangMills.Construction.Tower.FullSpace.expForm A ∈
        YangMills.Construction.Tower.FullSpace.fieldSpace L k 0) ∧
    ∀ U ∈ YangMills.Construction.Tower.FullSpace.smallIterateFields L k,
      U ∈ YangMills.Construction.Tower.FullSpace.fieldSpace L k 0 →
      (∀ j ≤ k, YangMills.Construction.Tower.FullSpace.complexIter L k j U ∈
        YangMills.Construction.Tower.FullSpace.fieldSpace L k j) ∧
      (∀ j ≤ k, ∀ B ∈ YangMills.Construction.Tower.FullSpace.edgeFormSpace
          (YangMills.Construction.Tower.meshAt L k 0),
        YangMills.Construction.Tower.FullSpace.complexIterDeriv L k j U B ∈
            YangMills.Construction.Tower.FullSpace.edgeFormSpace
              (YangMills.Construction.Tower.meshAt L k j) ∧
        YangMills.Construction.Tower.FullSpace.iterCovariantDeriv L k U j B ∈
            YangMills.Construction.Tower.FullSpace.edgeFormSpace
              (YangMills.Construction.Tower.meshAt L k j) ∧
        YangMills.Construction.Tower.FullSpace.iterContourLogDrift L k U j B ∈
            YangMills.Construction.Tower.FullSpace.vertexFunctionSpace
              (YangMills.Construction.Tower.meshAt L k j)) ∧
      (∀ j ≤ k, ∀ l ∈ YangMills.Construction.Tower.FullSpace.vertexFunctionSpace
          (YangMills.Construction.Tower.meshAt L k 0),
        YangMills.Construction.Tower.FullSpace.iterAdjointCubeAverage L k U j l ∈
          YangMills.Construction.Tower.FullSpace.vertexFunctionSpace
            (YangMills.Construction.Tower.meshAt L k j)) ∧
      ∀ B ∈ YangMills.Construction.Tower.FullSpace.edgeFormSpace
          (YangMills.Construction.Tower.meshAt L k 0),
        YangMills.Construction.Tower.FullSpace.gaugeParam U B ∈
            YangMills.Construction.Tower.FullSpace.vertexFunctionSpace
              (YangMills.Construction.Tower.meshAt L k 0) ∧
        YangMills.Construction.Tower.FullSpace.shiftedForm U B ∈
            YangMills.Construction.Tower.FullSpace.edgeFormSpace
              (YangMills.Construction.Tower.meshAt L k 0)
end YangMills.Construction.Tower.FullSpace.IteratesPreserveRealFields
end
