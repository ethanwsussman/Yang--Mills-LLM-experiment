import YangMills.Construction.SpectralTheory.FactsOnResolvedOperators
import YangMills.Construction.SpectralTheory.JointSpectralMeasuresGeneratorsAndCommutation
import Mathlib
set_option autoImplicit false
open Set
open scoped InnerProductSpace
noncomputable section
namespace YangMills.Construction.SelfAdjointResolution
section
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
def BoundedSelfAdjointDiagonalized : Prop :=
  ∀ T : E →L[ℂ] E, OperatorTransport.IsSelfAdjointCLM T →
    ResolvedOps.IsDiagonalized (HilbertSpaceBasics.ofBounded T) ∧
    (SpectralTheorem.spectralMeasure (HilbertSpaceBasics.ofBounded T)).IsCarriedBy
      (BorelSpectral.realLineSet ⟨Icc (-‖T‖) ‖T‖, measurableSet_Icc⟩) ∧
    ∀ S : E →L[ℂ] E, Commute S T →
      BorelSpectral.SpectralMeasure.OpCommutes S
        (SpectralTheorem.spectralMeasure (HilbertSpaceBasics.ofBounded T))
def CommutingBoundedSelfAdjointStronglyCommute : Prop :=
  ∀ T T' : E →L[ℂ] E, OperatorTransport.IsSelfAdjointCLM T →
    OperatorTransport.IsSelfAdjointCLM T' → Commute T T' →
    ResolvedOps.StronglyCommute (HilbertSpaceBasics.ofBounded T) (HilbertSpaceBasics.ofBounded T')
def SelfAdjointResolventFacts : Prop :=
  ∀ A : HilbertSpaceBasics.UnboundedOp E, OperatorTransport.IsSelfAdjointUnbounded A →
    (∀ x y : A.domain,
      ⟪(x : E), A y⟫_ℂ = ⟪A x, (y : E)⟫_ℂ ∧
      ⟪A x + Complex.I • (x : E), A y + Complex.I • (y : E)⟫_ℂ =
        ⟪A x, A y⟫_ℂ + ⟪(x : E), (y : E)⟫_ℂ ∧
      ⟪A x - Complex.I • (x : E), A y - Complex.I • (y : E)⟫_ℂ =
        ⟪A x, A y⟫_ℂ + ⟪(x : E), (y : E)⟫_ℂ) ∧
    Function.Bijective (HilbertSpaceBasics.addConst A Complex.I).toFun ∧
    Function.Bijective (HilbertSpaceBasics.addConst A (-Complex.I)).toFun ∧
    ∃ Rp Rm : E →L[ℂ] E,
      SpectralTheorem.IsBoundedInverse Rp (HilbertSpaceBasics.addConst A Complex.I) ∧
      SpectralTheorem.IsBoundedInverse Rm (HilbertSpaceBasics.addConst A (-Complex.I)) ∧
      HilbertSpaceBasics.IsContraction Rp ∧ HilbertSpaceBasics.IsContraction Rm ∧
      OperatorTransport.IsBoundedAdjoint Rm Rp ∧
      Rp * Rm = (1 / (2 * Complex.I)) • (Rm - Rp) ∧
      Rm * Rp = (1 / (2 * Complex.I)) • (Rm - Rp)
def SelfAdjointDiagonalized : Prop :=
  ∀ A : HilbertSpaceBasics.UnboundedOp E, OperatorTransport.IsSelfAdjointUnbounded A →
    ResolvedOps.IsDiagonalized A
def DiagonalizedIffSelfAdjoint : Prop :=
  (∀ A : HilbertSpaceBasics.UnboundedOp E,
    ResolvedOps.IsDiagonalized A ↔ OperatorTransport.IsSelfAdjointUnbounded A) ∧
  ∀ A : HilbertSpaceBasics.UnboundedOp E, OperatorTransport.IsSelfAdjointUnbounded A →
    (∃! P : BorelSpectral.SpectralMeasure SpectralTheorem.RealLineSet E,
        SpectralTheorem.IsSpectralMeasureFor P A) ∧
      SpectralTheorem.IsSpectralMeasureFor (SpectralTheorem.spectralMeasure A) A
end
def SelfAdjointDiagonalizationTheorem : Prop :=
  (∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E],
    BoundedSelfAdjointDiagonalized E ∧
    CommutingBoundedSelfAdjointStronglyCommute E ∧
    SelfAdjointResolventFacts E ∧
    SelfAdjointDiagonalized E ∧
    DiagonalizedIffSelfAdjoint E) ∧
  ResolvedFacts.DiagonalizedFacts ∧
  JointSpectralGenerators.JointMeasureGeneratorsCommutation
end YangMills.Construction.SelfAdjointResolution
