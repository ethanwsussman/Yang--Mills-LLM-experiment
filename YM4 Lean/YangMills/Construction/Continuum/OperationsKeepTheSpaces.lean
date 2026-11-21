import YangMills.Construction.Continuum.ConjLinearSeminormInnerForm
import YangMills.Construction.Continuum.NormsOfASchwartzFunction
import YangMills.Construction.Continuum.OperationsOnFunctionsOfSeveralPoints
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigSpace
def OperationsPreserveSchwartzSpaces : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (∀ f ∈ schwartzFlatOffDiagonal n, ∀ (g : EuclidMotion) (σ : Equiv.Perm (Fin n)),
      motionAct g f ∈ schwartzFlatOffDiagonal n ∧
        permAct σ f ∈ schwartzFlatOffDiagonal n) ∧
    (∀ v ∈ zeroTimeHyperplane,
      Set.MapsTo (shiftAct v) (schwartzFlatOffPosTime n) (schwartzFlatOffPosTime n) ∧
        Set.MapsTo (shiftAct v) (schwartzFlatOffNegTime n) (schwartzFlatOffNegTime n)) ∧
    (∀ f : SchwartzFn n, ∃ hf : IsSchwartz (flipConj f.1),
      flipConj (flipConj f.1) = f.1 ∧
        ∀ k : ℕ, bracketNorm k ⟨flipConj f.1, hf⟩ = bracketNorm k f) ∧
    (∃ S : Submodule ℂ (Config n → ℂ), (S : Set (Config n → ℂ)) = {f | IsSchwartz f} ∧
      ∃ A : S → S, (∀ f : S, (A f).1 = flipConj f.1) ∧ Continuum.IsConjLinearMap A) ∧
    flipConj '' schwartzFlatOffPosTime n = schwartzFlatOffNegTime n
end YangMills.Construction.ConfigSpace
end
