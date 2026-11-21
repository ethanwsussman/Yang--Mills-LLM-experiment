import YangMills.Construction.Matrices.SpecialUnitaryTwo
import Mathlib
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Matrices.ComplexMatrix2
variable {ι : Type*} [Fintype ι]
def familyDiameter (V : ι → ComplexMatrix2) : ℝ :=
  ⨆ p : ι × ι, operatorNorm (V p.1 * (V p.2)⁻¹ - 1)
def IsLogMean (S : Set ComplexMatrix2) (V : ι → ComplexMatrix2) (W : ComplexMatrix2) : Prop :=
  W ∈ S ∧ (∀ i, operatorNorm (V i * W⁻¹ - 1) < 1) ∧ ∑ i, logSeries (V i * W⁻¹) = 0
def IsLogMeanWithin (S : Set ComplexMatrix2) (ω : ℝ) (V : ι → ComplexMatrix2)
    (W : ComplexMatrix2) : Prop :=
  IsLogMean S V W ∧ ∀ i, operatorNorm (V i * W⁻¹ - 1) < ω
def HasUniqueLogMean (S : Set ComplexMatrix2) (V : ι → ComplexMatrix2) : Prop :=
  ∃! W, IsLogMean S V W
def logMean (S : Set ComplexMatrix2) (V : ι → ComplexMatrix2) : ComplexMatrix2 :=
  Classical.epsilon (IsLogMean S V)
end YangMills.Construction.Matrices.ComplexMatrix2
