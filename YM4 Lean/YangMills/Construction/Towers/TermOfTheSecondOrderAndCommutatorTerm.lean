import YangMills.Construction.Towers.TheLeftChart
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
variable {L n k : ℕ}
def bracketTerm (U : Edge L n k 0 → Matrices.ComplexMatrix2)
    (l : Vertex L n k 0 → Matrices.ComplexMatrix2)
    (B : Edge L n k 0 → Matrices.ComplexMatrix2) : Edge L n k 0 → Matrices.ComplexMatrix2 :=
  extendOddly fun b =>
    (Complex.I / 2) • ⁅l b.source + Matrices.ComplexMatrix2.conjugateBy (U b) (l b.target), B b⁆
end YangMills.Construction.Tower
end
