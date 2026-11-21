import Reconstruction.MinkowskiSpace.FieldFormOfAFunctionalDefs
import Mathlib
set_option autoImplicit false
open scoped InnerProductSpace ContDiff
noncomputable section
namespace YangMills.Construction.InsertionSmearing
open OneLoopNotation ProjectionMeasures FieldFormConditions InsertedFieldForm
def Claim : Prop :=
  ∀ (sigma : TestSpaces.SepTuple → ℝ) (E : FourBorelSet → BddOp (StateSpace sigma)) (p C : ℝ),
    Hypotheses sigma E p C →
    ∀ (η : ℝ) (k φ : (Fin 4 → ℝ) → ℂ), 0 < η → η ≤ 1 →
      k ∈ TestSpaces.c1CompactSupp (Set.univ : Set (Fin 4 → ℝ)) →
      Continuous φ → HasCompactSupport φ →
      (∀ x ∈ tsupport φ, ∀ y ∈ tsupport k,
        η ≤ (x + y) TimeAxis.timeIdx ∧ (x + y) TimeAxis.timeIdx ≤ 3 * η) →
      (∀ x ∈ tsupport φ, ∀ y ∈ tsupport k, ∀ x' ∈ tsupport φ, ∀ y' ∈ tsupport k,
        TorusMetric.euclidNormVec ((x + y) - (x' + y')) ≤ 1) →
      ContinuousOn (fun x => insertionOp sigma η (translateFun x k)) (tsupport φ) ∧
      ∀ χ χ' : StateSpace sigma,
        ⟪χ, insertionOp sigma η (EuclideanFunctionals.conv k φ) χ'⟫_ℂ =
          ∫ x, φ x * ⟪χ, insertionOp sigma η (translateFun x k) χ'⟫_ℂ
end YangMills.Construction.InsertionSmearing
end
