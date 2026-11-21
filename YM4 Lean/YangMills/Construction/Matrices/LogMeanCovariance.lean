import YangMills.Construction.Matrices.LogMeanOfFamily
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Matrices.ComplexMatrix2
def LogMeanCovariance : Prop :=
  ∀ (ι : Type) [Fintype ι] (V : ι → ComplexMatrix2) (W W' : ComplexMatrix2),
    (∀ i, V i ∈ (specialUnitary : Set ComplexMatrix2)) →
    W ∈ (specialUnitary : Set ComplexMatrix2) → W' ∈ (specialUnitary : Set ComplexMatrix2) →
    (∀ X ∈ (specialUnitary : Set ComplexMatrix2),
      (IsLogMean (specialUnitary : Set ComplexMatrix2) V X ↔
        IsLogMean (specialUnitary : Set ComplexMatrix2) (fun i => W * V i * W') (W * X * W'))) ∧
    (HasUniqueLogMean (specialUnitary : Set ComplexMatrix2) V ↔
      HasUniqueLogMean (specialUnitary : Set ComplexMatrix2) (fun i => W * V i * W')) ∧
    (HasUniqueLogMean (specialUnitary : Set ComplexMatrix2) V →
      logMean (specialUnitary : Set ComplexMatrix2) (fun i => W * V i * W') =
        W * logMean (specialUnitary : Set ComplexMatrix2) V * W')
end YangMills.Construction.Matrices.ComplexMatrix2
