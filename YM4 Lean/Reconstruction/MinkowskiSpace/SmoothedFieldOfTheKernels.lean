import Reconstruction.MinkowskiSpace.FieldFormOfAFunctionalDefs
import Mathlib
set_option autoImplicit false
open scoped InnerProductSpace ContDiff
noncomputable section
namespace YangMills.Construction.SmoothedKernelField
open ProjectionMeasures HilbertToolkit OneLoopNotation FieldFormConditions InsertedFieldForm
def Regularity : Prop :=
  ∀ (sigma : TestSpaces.SepTuple → ℝ) (E : FourBorelSet → BddOp (StateSpace sigma)) (p C : ℝ),
    Hypotheses sigma E p C →
    ∀ η : ℝ, 0 < η → η ≤ 1 →
      (∀ (Γ : Finset (Fin 4)) (u v : StateSpace sigma),
        ContDiffOn ℝ ∞ (fun a => ⟪u, conjKernelInsertion sigma E η Γ a v⟫_ℂ)
          {a | |a TimeAxis.timeIdx| < η}) ∧
      (∀ a : Fin 4 → ℝ, |a TimeAxis.timeIdx| ≤ η / 2 →
        RepresentsForm (fun u v => smoothedPairing sigma E η a u v) (smoothedFieldOp sigma E η a) ∧
          opNormOf (smoothedFieldOp sigma E η a) ≤ smoothedFieldConst C * η ^ (-p - 5)) ∧
      ∀ u v : StateSpace sigma,
        ContinuousOn (fun a => ⟪u, smoothedFieldOp sigma E η a v⟫_ℂ)
          {a | |a TimeAxis.timeIdx| ≤ η / 2}
end YangMills.Construction.SmoothedKernelField
end
