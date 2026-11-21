import YangMills.Construction.SeparatedSequences.InverseExpansionCutoff
import YangMills.Construction.Torus.ApproximateInverseAndRemainderOfTheCubes
import YangMills.Construction.Torus.FloorOfTheInverseBounds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.GeneralTorus
namespace CubeGaugeSetting
def remainderConst (L : ℕ) : ℝ :=
  SeparatedSequences.expansionRemainderConstant 4 L (GreenBounds.chosen L).rate
    (GreenBounds.chosen L).bound
def expansionBlockLower (L : ℕ) : ℝ :=
  SeparatedSequences.inverseExpansionBlockCutoff 4 L (GreenBounds.chosen L).rate
    (GreenBounds.chosen L).bound (GreenBounds.chosen L).blockLower
variable (C : CubeGaugeSetting)
def remainderPiece (Q' Q : C.data.CubeIndex) : Module.End ℝ C.CoarseField :=
  C.remainderEntry Q' Q ∘ₗ C.localInverse Q ∘ₗ C.unityMul Q
abbrev CubeWord (k : ℕ) : Type := Fin (2 * k + 1) → ↥C.chain.allCubes
variable {C}
def wordTerm {k : ℕ} (ω : C.CubeWord k) : Module.End ℝ C.CoarseField :=
  (C.unityMul (ω ⟨0, by omega⟩) ∘ₗ C.localInverse (ω ⟨0, by omega⟩) ∘ₗ
      C.unityMul (ω ⟨0, by omega⟩)) ∘ₗ
    ((List.finRange k).map fun j : Fin k =>
      C.remainderPiece (ω ⟨2 * j + 1, by omega⟩) (ω ⟨2 * j + 2, by omega⟩)).prod
variable (C)
end CubeGaugeSetting
end YangMills.Construction.GeneralTorus
end
