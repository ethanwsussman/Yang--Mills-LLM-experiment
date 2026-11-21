import YangMills.Construction.SeparatedSequences.ConstantsArePositiveAndLowerBoundExceedsSquareProof
import YangMills.Construction.Torus.BoundsOnTheCompressedOperatorsProof
import YangMills.Construction.Torus.GeometryOfCubesAndCutSequences
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open TorusMetric
namespace GeneralTorus
namespace CubeGreenCompressionProof
theorem levelSpacing_pos (D : ScaleData) (n : ℕ) : 0 < D.levelSpacing n := by apply _root_.YangMills.Construction.GeneralTorus.ChainStructureProof.levelSpacing_pos <;> assumption
theorem coarseSpacing_pos {W : GaugeSetting} (c : W.CoarseBond) : 0 < GaugeSetting.coarseSpacing c := by apply _root_.YangMills.Construction.GeneralTorus.CompressedBoundsProof.coarseSpacing_pos <;> assumption
theorem torusSupNorm_zero_le {S s : ℝ} (hs : 0 ≤ s) : torusSupNorm (0 : Torus4 S) ≤ s := by
  have hnn : ∀ v : Fin 4 → ℝ, 0 ≤ supNormVec v := fun v =>
    (abs_nonneg (v 0)).trans (Finset.le_sup' (fun μ => |v μ|) (Finset.mem_univ 0))
  have h0 : supNormVec (0 : Fin 4 → ℝ) ≤ 0 :=
    Finset.sup'_le _ _ fun μ _ => by simp
  have hmem : supNormVec (0 : Fin 4 → ℝ) ∈ supNormVec '' (torusProj S ⁻¹' {(0 : Torus4 S)}) :=
    ⟨0, by
      funext μ
      simp [torusProj], rfl⟩
  have hb : BddBelow (supNormVec '' (torusProj S ⁻¹' {(0 : Torus4 S)})) :=
    ⟨0, by
      rintro _ ⟨v, -, rfl⟩
      exact hnn v⟩
  exact ((csInf_le hb hmem).trans h0).trans hs
theorem mem_cubeAt_self (D : ScaleData) (n : ℕ) (y : D.Space) : y ∈ D.cubeAt n y := by
  show torusSupNorm (y - y) ≤ D.levelSpacing n / 2
  rw [sub_self]
  exact torusSupNorm_zero_le (by have := levelSpacing_pos D n; positivity)
section LocalCorrespondence
variable {C : CubeGaugeSetting} {Q : C.data.CubeIndex}
end LocalCorrespondence
theorem compressedGreenLowerBound_pos :
    0 < SeparatedSequences.compressedGreenLowerBound 4 1 := by apply _root_.YangMills.Construction.SeparatedClasses.OperatorConstantsPos.compressedGreenLowerBound_pos <;> assumption
end CubeGreenCompressionProof
end GeneralTorus
end YangMills.Construction
