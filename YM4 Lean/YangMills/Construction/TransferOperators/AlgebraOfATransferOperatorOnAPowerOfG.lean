import YangMills.Construction.Matrices.HilbertSchmidtOperatorsTraceClassAndTraceOnG
import YangMills.Construction.TransferOperators.CubicToriAndProductsOfOperatorsOnPowersOfG
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TransferOperators
open SpinHarmonics
def TransferAlgebraStatement : Prop :=
  ∀ (J : Type) [Finite J] (c : PeterWeylIndex J → ℝ)
    (R P M : HaarL2 J →L[ℂ] HaarL2 J),
    IsSymmetricOp R → IsSymmetricOp P → P * P = P → R * P = P * R →
    IsPositiveOp M → ‖M‖ ≤ 1 → M * P = P * M →
    (∀ i, ‖R (peterWeylVec i)‖ ≤ c i) →
    Summable (fun i => c i ^ 2) → Summable c →
    IsSymmetricOp (R * P) ∧
    IsHilbertSchmidtPW (R * P) ∧
    R * P * M * (R * P) = P * R * M * R * P ∧
    R * P * M * (R * P) = R * P * M * R ∧
    IsPositiveOp (R * P * M * (R * P)) ∧
    IsSymmetricOp (R * P * M * (R * P)) ∧
    IsTraceClassPW (R * P * M * (R * P)) ∧
    (∀ i j, ‖peterWeylEntry (R * P * M * (R * P)) i j‖ ≤ c i * c j) ∧
    Summable fun q : PeterWeylIndex J × PeterWeylIndex J =>
      ‖peterWeylEntry (R * P * M * (R * P)) q.1 q.2‖
end YangMills.Construction.TransferOperators
end
