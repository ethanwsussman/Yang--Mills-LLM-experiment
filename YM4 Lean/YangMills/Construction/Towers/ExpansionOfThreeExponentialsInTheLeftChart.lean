import YangMills.Construction.Towers.LeftChartTranslationAlgebraFacts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.TripleExpExpansion
def tripleProduct (a B₀ a' V : Matrices.ComplexMatrix2) (s t : ℂ) : Matrices.ComplexMatrix2 :=
  Matrices.ComplexMatrix2.matExp (Complex.I • t • a) * Matrices.ComplexMatrix2.matExp (Complex.I • s • B₀) *
    Matrices.ComplexMatrix2.matExp (-(Complex.I • t • a')) * V
def principalPart (a B₀ a' : Matrices.ComplexMatrix2) (s t : ℂ) : Matrices.ComplexMatrix2 :=
  s • B₀ - t • (a' - a) + (s * t) • ((Complex.I / 2) • ⁅a + a', B₀⁆) -
    t ^ 2 • ((Complex.I / 2) • ⁅a, a'⁆)
def Claim : Prop :=
  ∀ a B₀ a' V : Matrices.ComplexMatrix2, a ∈ Matrices.ComplexMatrix2.traceless →
    B₀ ∈ Matrices.ComplexMatrix2.traceless → a' ∈ Matrices.ComplexMatrix2.traceless → IsUnit V →
    HasLocalExpExpansion (tripleProduct a B₀ a' V) V (principalPart a B₀ a')
end YangMills.Construction.Tower.TripleExpExpansion
end
