import YangMills.Construction.Matrices.FunctionsAndOperatorsOfSeveralVariablesOnG
import YangMills.Construction.Measures.ImageMeasuresAndJointLaws
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Matrices.ComplexMatrix2
def IsBiTranslateOrInvBiTranslate (j : specialUnitary → specialUnitary) : Prop :=
  ∃ u u' : specialUnitary, (∀ g, j g = u * g * u') ∨ (∀ g, j g = u * g⁻¹ * u')
def permuteThenApply {I : Type} (ς : Equiv.Perm I) (j : I → specialUnitary → specialUnitary) :
    (I → specialUnitary) → I → specialUnitary :=
  fun U i => j i (U (ς i))
def HaarPiInvariance.statement : Prop :=
  ∀ (I : Type) [Finite I] (ς : Equiv.Perm I) (j : I → specialUnitary → specialUnitary),
    (∀ i, IsBiTranslateOrInvBiTranslate (j i)) →
      IsHomeomorph (permuteThenApply ς j) ∧
        ∃ hΞ : Measurable (permuteThenApply ς j),
          Measures.Pushforward.IsInvariant (haarPi I) (permuteThenApply ς j) hΞ
end YangMills.Construction.Matrices.ComplexMatrix2
end
