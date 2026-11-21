import Reconstruction.Continuum.InvarianceOfSequenceOnTestFunctionSpaces
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigSpace
private def orthogonalMotion (R : Matrix.orthogonalGroup (Fin 4) ℝ) :
    EuclidMotion :=
  ⟨fun u => R.1.mulVec u + 0, R.1, R.2, 0, fun _ => rfl⟩
private theorem actOnFun_eq_motionAct {n : ℕ} {F : Type*}
    (R : Matrix.orthogonalGroup (Fin 4) ℝ) (φ : Config n → F) :
    Motions.actOnFun ⟨R.1, R.2, 0⟩ φ =
      motionAct (orthogonalMotion R) φ := by
  funext x
  have hinv : ∀ u, (orthogonalMotion R).invMap u = R.1⁻¹.mulVec (u - 0) := fun u =>
    EuclidMotion.invMap_eq _ R.2 (fun _ => rfl) u
  simp only [Motions.actOnFun, motionAct, hinv,
    Motions.RigidMotion.invFun]
theorem motionInvariance_holds :
    MotionInvarianceStatement := by
  intro S hMot hPerm
  refine ⟨?_, ?_, ?_⟩
  · intro k v φ hφ
    exact hMot k φ (shiftMotion v) hφ
  · intro k φ R hφ
    have hfun := actOnFun_eq_motionAct R φ.1
    have hφ' : motionAct (orthogonalMotion R) φ.1 ∈
        schwartzFlatOffDiagonal (k + 1) := hfun ▸ hφ
    rw [← hMot k φ (orthogonalMotion R) hφ']
    exact congrArg (S.atSucc k) (Subtype.ext hfun)
  · intro k φ σ hφ
    exact hPerm k φ σ hφ
end YangMills.Construction.ConfigSpace
end
