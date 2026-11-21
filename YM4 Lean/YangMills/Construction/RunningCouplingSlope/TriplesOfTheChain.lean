import YangMills.Construction.RunningCouplingSlope.GaussianNumbersOfTheSoftChain
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
variable {L n k : ℕ}
abbrev LevelTriple (L n k : ℕ) : Type :=
  LevelForms L n k × LevelForms L n k × Tower.edgeFormSpace L n k k
def tripleFreeEnergy (a : ℝ) (t : LevelTriple L n k) : ℝ :=
  chainFreeEnergy a (expMove t.1 (unitPoint L n k)) t.2.1 t.2.2
def IsConjugatedCurrent (v : Tower.Vertex L n k 0 → Matrices.ComplexMatrix2) (J J' : LevelForms L n k) : Prop :=
  formValues J' = (Tower.adjointForm v (J.1 : Tower.Edge L n k 0 → Matrices.ComplexMatrix2),
    fun i : Fin k => Tower.adjointForm (Tower.restrictVertexFunction ((i : ℕ) + 1) v)
      (J.2 i : Tower.Edge L n k (i + 1) → Matrices.ComplexMatrix2))
end YangMills.Construction.RunningCouplingSlope
end
