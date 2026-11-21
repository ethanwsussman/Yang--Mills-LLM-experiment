import YangMills.Construction.Matrices.LogMeanOfFamily
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Matrices.ComplexMatrix2
def IsUnitFamily {n : ℕ} (V : Fin n → ComplexMatrix2) : Prop :=
  1 ≤ n ∧ ∀ i, IsUnit (V i)
def unitFamilyDiameter {n : ℕ} (V : Fin n → ComplexMatrix2) : ℝ := familyDiameter V
def closedBallEighth : Set ComplexMatrix2 := {Y | operatorNorm Y ≤ 1 / 8}
def IsSpecialUnitaryFamily {n : ℕ} (V : Fin n → ComplexMatrix2) : Prop :=
  1 ≤ n ∧ ∀ i, V i ∈ (specialUnitary : Set ComplexMatrix2)
def IsSpecialUnitaryLogMean {n : ℕ} (V : Fin n → ComplexMatrix2) (W : ComplexMatrix2) : Prop :=
  IsSpecialUnitaryFamily V ∧ IsLogMean (specialUnitary : Set ComplexMatrix2) V W
def IsLogMeanOfRadius (ω : ℝ) {n : ℕ} (V : Fin n → ComplexMatrix2) (W : ComplexMatrix2) : Prop :=
  ω ∈ Set.Ioc (0 : ℝ) 1 ∧ IsSpecialUnitaryFamily V ∧
    IsLogMeanWithin (specialUnitary : Set ComplexMatrix2) ω V W
end YangMills.Construction.Matrices.ComplexMatrix2
