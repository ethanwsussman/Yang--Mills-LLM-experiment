import YangMills.Construction.Matrices.SpecialUnitaryTwo
import Mathlib
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
namespace YangMills.Construction.Matrices.ComplexifiedAlgebra
def EntrywiseHolomorphic (f : ComplexMatrix2 → ℂ) : Prop :=
  ∀ Y ∈ ComplexMatrix2.traceless, ∃ F : ComplexMatrix2 → ℂ, AnalyticAt ℂ F Y ∧
    ∀ᶠ Z in 𝓝[(ComplexMatrix2.traceless : Set ComplexMatrix2)] Y, f Z = F Z
def ComplexifiedAlgebraExponential : Prop :=
  ((ComplexMatrix2.traceless : Set ComplexMatrix2) =
      {A | ∃ X ∈ ComplexMatrix2.hermitianTraceless, ∃ Y ∈ ComplexMatrix2.hermitianTraceless,
        A = X + Complex.I • Y} ∧
    (ComplexMatrix2.traceless : Set ComplexMatrix2) = {A | ComplexMatrix2.fullTrace A = 0}) ∧
  (∀ Y ∈ ComplexMatrix2.traceless,
    ComplexMatrix2.matExp (Complex.I • Y) ∈ ComplexMatrix2.unitDeterminant) ∧
  ∀ i j : Fin 2, EntrywiseHolomorphic fun Y => ComplexMatrix2.matExp (Complex.I • Y) i j
end YangMills.Construction.Matrices.ComplexifiedAlgebra
