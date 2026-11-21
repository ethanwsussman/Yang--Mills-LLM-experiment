import YangMills.Construction.Towers.EntriesOfTheHessianCurvatureKernel
import YangMills.Construction.Towers.FactsOnThePartsOfTheHessianOfTheWilsonAction
import YangMills.Construction.Towers.TheBackgroundKernelAtZeroProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open PeriodicOperators
namespace Tower.FullSpace.CurvatureEntries
variable {L k : ℕ}
theorem ofCoeffs_basisFunction (ι : Fin 3 × PositiveEdge (meshAt L k 0)) :
    (edgePauliCoordinates L k 0).ofCoeffs (basisFunction ι).1 = basisForm ι.1 ι.2 := by apply _root_.YangMills.Construction.Tower.FullSpace.KernelAtZeroSources.ofCoeffs_basisFunction <;> assumption
theorem curvatureKernelEntries_holds (hF : CurvatureHessianFacts.Claim)
    (hS : SymmetricKernels.Claim) : CurvatureKernelEntries := by
  intro L hL k hk U ι' ι
  obtain ⟨⟨β, hβ⟩, -, huniq⟩ := (hF L hL k hk).2.1 U
  have hL0 : (0 : ℝ) < L := by
    have := hL.2
    exact_mod_cast (by omega : 0 < L)
  have hη : 0 < finestMesh L k := zpow_pos hL0 _
  have hw : ∀ κ : Fin 3 × PositiveEdge (meshAt L k 0),
      0 < meshWeight (σ := PositiveEdge (meshAt L k 0)) (finestMesh L k) κ :=
    fun _ => pow_pos hη 4
  have hq := (hS.1 _ _ hw β).2
  have hX := huniq _ ⟨hq.2.1.1, fun f => (hq.2.1.2 f).trans (hβ f f)⟩
  have hv : ∀ κ' κ : Fin 3 × PositiveEdge (meshAt L k 0),
      β (basisFunction κ') (basisFunction κ) =
        curvatureBilinear U (basisForm κ'.1 κ'.2) (basisForm κ.1 κ.2) := by
    intro κ' κ
    rw [hβ, ofCoeffs_basisFunction, ofCoeffs_basisFunction]
  rw [← hX]
  have hne : finestMesh L k ^ 4 ≠ 0 := (pow_pos hη 4).ne'
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, wTranspose, bilinKernel,
    meshWeight, div_self hne, hv]
  push_cast
  ring
end Tower.FullSpace.CurvatureEntries
end YangMills.Construction
end
