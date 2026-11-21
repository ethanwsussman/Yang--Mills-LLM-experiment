import YangMills.Construction.Towers.CommutatorTermAtAPeriodicExtensionDescendsProof
import YangMills.Construction.Towers.IteratedAveragesReadOnlyTheBlocksAtTheSideInfinityProof
import YangMills.Construction.Towers.PeriodicRestrictionDeterminesAForm
import YangMills.Construction.Towers.ScaledKernelsAreHolomorphicInTheFormAtTheSideInfinityProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.PeriodicCoeffsDetermineForm
open PeriodicForm (coeffsOnEdges)
theorem pauliCoeff_ext {X Y : Matrices.ComplexMatrix2}
    (hX : X ∈ Matrices.ComplexMatrix2.traceless) (hY : Y ∈ Matrices.ComplexMatrix2.traceless)
    (h : ∀ a, pauliCoeff a X = pauliCoeff a Y) : X = Y := by apply _root_.YangMills.Construction.Tower.FullSpace.IterLocality.eq_of_pauliCoeff_eq <;> assumption
theorem pauliCoeff_ofReal_smul (c : ℝ) {X : Matrices.ComplexMatrix2}
    (hX : X ∈ Matrices.ComplexMatrix2.traceless) (a : Fin 3) :
    pauliCoeff a (c • X) = (c : ℂ) * pauliCoeff a X := by apply _root_.YangMills.Construction.Tower.FullSpace.HolomorphicRescaledKernels.pauliCoeff_real_smul <;> assumption
theorem xor_isPositivelyOriented_opposite
    (hO : PeriodicLattice.LevelBondOrientationDichotomy)
    {L n k j : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k)
    (b : Edge L n k j) : Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := by apply _root_.YangMills.SharedProofs.p22685 <;> assumption
theorem statement_holds (hC : LocalKernels.PeriodicLiftCells.CellsAndClassesHold)
    (hO : PeriodicLattice.LevelBondOrientationDichotomy) : Statement := by
  intro L hL k n j hn hj
  have hsurj : Function.Surjective (LocalKernels.projPositiveEdge L n k j) :=
    (((hC L hL k n hn).1 j hj).1 LocalKernels.CellType.edge).1
  refine ⟨fun A A' h => ?_, fun c A => ?_⟩
  · have hpos : ∀ d : PositiveEdge L n k j,
        (A : Edge L n k j → Matrices.ComplexMatrix2) d.1 =
          (A' : Edge L n k j → Matrices.ComplexMatrix2) d.1 := by
      intro d
      have hA : (A : Edge L n k j → Matrices.ComplexMatrix2) d.1 ∈
          Matrices.ComplexMatrix2.hermitianTraceless := A.2.1 d.1 d.2
      have hA' : (A' : Edge L n k j → Matrices.ComplexMatrix2) d.1 ∈
          Matrices.ComplexMatrix2.hermitianTraceless := A'.2.1 d.1 d.2
      refine pauliCoeff_ext hA.2 hA'.2 fun a => ?_
      obtain ⟨b, rfl⟩ := hsurj d
      exact congrFun h (a, b)
    apply Subtype.ext
    funext b
    rcases xor_isPositivelyOriented_opposite hO hL hn hj b with ⟨h₁, -⟩ | ⟨h₁, -⟩
    · exact hpos ⟨b, h₁⟩
    · have e := hpos ⟨b.opposite, h₁⟩
      simp only [A.2.2 b, A'.2.2 b] at e
      exact neg_injective e
  · funext ι
    have hA : (A : Edge L n k j → Matrices.ComplexMatrix2)
        (LocalKernels.projPositiveEdge L n k j ι.2).1 ∈
          Matrices.ComplexMatrix2.hermitianTraceless :=
      A.2.1 _ (LocalKernels.projPositiveEdge L n k j ι.2).2
    exact pauliCoeff_ofReal_smul c hA.2 ι.1
end YangMills.Construction.Tower.PeriodicCoeffsDetermineForm
end
