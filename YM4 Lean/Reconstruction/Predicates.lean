import YangMills.Construction.LimitTheorem.AssertionsAtGivenConstants
import YangMills.Construction.SystemsWithFiveBounds.TheoremOverASystemWithFiveBounds
import Reconstruction.MinkowskiSpace.WightmanTheoriesOfOneHermitianScalarField

noncomputable section
namespace YangMills.Construction
open ConfigSpace (FlatSequence)
open SeparatedTuples (TupleFunctional)

namespace LimitTheorem
def IsWightmanSchwingerSequence (T : FlatSequence) : Prop :=
  ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
    (W : WightmanTheory.HermitianScalarTheory H),
    TopologicalSpace.SeparableSpace H ∧ W.UniqueVacuum ∧ W.IsPoincareCovariant ∧
      W.SpectrumCondition ∧ W.IsLocalField ∧ W.IsSchwingerSequence T

def HasWightmanReconstruction (C : ConditionConstants) (σ : TupleFunctional) : Prop :=
  ∀ T, HasSchwingerSequence σ T →
    SatisfiesAxiomLists C T ∧ IsWightmanSchwingerSequence T

end LimitTheorem

namespace SystemsWithFiveBounds
abbrev IsWightmanSchwingerSequence := LimitTheorem.IsWightmanSchwingerSequence

def WightmanReconstructs (K : LimitConstants) (σ : TupleFunctional) : Prop :=
  ∀ T, HasSchwingerSequence σ T → OSAxioms K T ∧ IsWightmanSchwingerSequence T

end SystemsWithFiveBounds
end YangMills.Construction
end
