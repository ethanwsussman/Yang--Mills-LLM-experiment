import Reconstruction.Continuum.TimeTranslationsOfASequence
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigSpace
structure FlatSequence.IsMotionInvariant (S : FlatSequence) : Prop where
  translation : S.IsTranslationInvariant
  orthogonal : ∀ (m : ℕ) (φ : schwartzFlatOffDiagonal (m + 1))
    (R : Matrix.orthogonalGroup (Fin 4) ℝ)
    (h : Motions.actOnFun ⟨R.1, R.2, 0⟩ φ.1 ∈ schwartzFlatOffDiagonal (m + 1)),
    S.atSucc m ⟨_, h⟩ = S.atSucc m φ
  perm : ∀ (m : ℕ) (φ : schwartzFlatOffDiagonal (m + 1))
    (p : Equiv.Perm (Fin (m + 1)))
    (h : Motions.permuteArgs p φ.1 ∈ schwartzFlatOffDiagonal (m + 1)),
    S.atSucc m ⟨_, h⟩ = S.atSucc m φ
def MotionInvarianceStatement : Prop :=
  ∀ S : FlatSequence, IsEuclidInvariant S → IsPermSymmetric S →
    S.IsMotionInvariant
end YangMills.Construction.ConfigSpace
end
