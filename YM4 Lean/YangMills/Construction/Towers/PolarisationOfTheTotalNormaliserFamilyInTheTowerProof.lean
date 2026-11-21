import YangMills.Construction.Towers.PolarisationOfTheTotalNormaliserFamilyInTheTower
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.NormaliserHessianTransport
open PeriodicOperators.Tempered
variable {L n k : ℕ}
theorem topEdgeEquivUnit_isPositivelyOriented (b : Edge L n k k) :
    (topEdgeEquivUnit L n k b).IsPositivelyOriented ↔ b.IsPositivelyOriented := by
  have hb : ∀ μ, (topEdgeEquivUnit L n k b).target - (topEdgeEquivUnit L n k b).source =
        PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth 0 0) μ ↔
      b.target - b.source = PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k k) μ :=
    fun μ => by
    rw [← topVertexEquivUnit_unitStep L n k μ]
    change topVertexEquivUnit L n k b.target - topVertexEquivUnit L n k b.source = _ ↔ _
    rw [← map_sub]
    exact (topVertexEquivUnit L n k).injective.eq_iff
  exact exists_congr hb
theorem topEdgeEquivUnit_opposite (b : Edge L n k k) :
    topEdgeEquivUnit L n k b.opposite = (topEdgeEquivUnit L n k b).opposite := rfl
theorem topEdgeEquivUnit_symm_opposite (b : UnitEdge L n) :
    (topEdgeEquivUnit L n k).symm b.opposite = ((topEdgeEquivUnit L n k).symm b).opposite := by
  apply (topEdgeEquivUnit L n k).injective
  rw [topEdgeEquivUnit_opposite, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
theorem isBondForm_comp {𝔥 : Set Matrices.ComplexMatrix2} {B : UnitEdge L n → Matrices.ComplexMatrix2}
    (hB : PeriodicLattice.IsBondForm 𝔥 B) :
    PeriodicLattice.IsBondForm 𝔥 (B ∘ topEdgeEquivUnit L n k) :=
  ⟨fun b hb => hB.1 _ ((topEdgeEquivUnit_isPositivelyOriented b).2 hb),
    fun b => hB.2 (topEdgeEquivUnit L n k b)⟩
theorem isBondForm_comp_symm {𝔥 : Set Matrices.ComplexMatrix2}
    {C : Edge L n k k → Matrices.ComplexMatrix2}
    (hC : PeriodicLattice.IsBondForm 𝔥 C) :
    PeriodicLattice.IsBondForm 𝔥 (C ∘ (topEdgeEquivUnit L n k).symm) := by
  refine ⟨fun b hb => hC.1 _ ?_, fun b => ?_⟩
  · rw [← topEdgeEquivUnit_isPositivelyOriented, Equiv.apply_symm_apply]
    exact hb
  · simp only [Function.comp_apply]
    rw [topEdgeEquivUnit_symm_opposite]
    exact hC.2 _
theorem expTwist_comp (X U : UnitEdge L n → Matrices.ComplexMatrix2) :
    PeriodicLattice.expTwist X U ∘ topEdgeEquivUnit L n k =
      PeriodicLattice.expTwist (X ∘ topEdgeEquivUnit L n k) (U ∘ topEdgeEquivUnit L n k) := by
  funext b
  by_cases h : b.IsPositivelyOriented
  · have h' := (topEdgeEquivUnit_isPositivelyOriented b).2 h
    simp only [Function.comp_apply, PeriodicLattice.expTwist, if_pos h, if_pos h']
  · have h' : ¬(topEdgeEquivUnit L n k b).IsPositivelyOriented := fun p =>
      h ((topEdgeEquivUnit_isPositivelyOriented b).1 p)
    simp only [Function.comp_apply, PeriodicLattice.expTwist, if_neg h, if_neg h',
      topEdgeEquivUnit_opposite]
theorem logNormaliserFamily_expTwist (X : UnitEdge L n → Matrices.ComplexMatrix2) :
    logNormaliserFamily L k n
        (PeriodicLattice.expTwist X (PeriodicOperators.Tempered.identityField L n)) =
      logTotalNormaliserRatio L n k
        (PeriodicLattice.expTwist (X ∘ topEdgeEquivUnit L n k)
          (Tower.trivialField L n k k)) := by
  change logTotalNormaliserRatio L n k _ = _
  rw [expTwist_comp]
  rfl
theorem normaliserFamilyHessianOnTop_holds : NormaliserFamilyHessianOnTop := by
  intro L n k _ _ _
  refine ⟨Set.BijOn.mk ?_ ?_ ?_, fun B _ B' _ => ?_⟩
  · intro B hB
    exact isBondForm_comp (k := k)
      (show PeriodicLattice.IsBondForm PeriodicLattice.compactLieAlgebra B from hB)
  · intro B _ B' _ h
    exact (topEdgeEquivUnit L n k).surjective.injective_comp_right h
  · intro C hC
    refine ⟨C ∘ (topEdgeEquivUnit L n k).symm,
      isBondForm_comp_symm
        (show PeriodicLattice.IsBondForm PeriodicLattice.compactLieAlgebra C from hC), ?_⟩
    funext b
    simp
  · simp only [PeriodicOperators.Tempered.hessianAtIdentity, Tower.leftSecondDeriv,
      mixedDirectionalDeriv, logNormaliserFamily_expTwist]
    rfl
end YangMills.Construction.Tower.NormaliserHessianTransport
end
