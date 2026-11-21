import YangMills.Construction.SeparatedSequences.PropertiesOfTheOperatorsOfASequence
import YangMills.Construction.Torus.SeparatedSequenceOfACoarseRegion
import YangMills.Construction.Torus.SymmetricAndPositiveDefiniteOperatorsOnForms
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open SeparatedClasses.PeriodicExpansions
noncomputable section
namespace GeneralTorus.CenteredCompressionLowerBoundProof
theorem exists_isAdjointFor {V U : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [AddCommGroup U] [Module ℝ U] (q : U → U → ℝ)
    (hadd : ∀ x y y', q x (y + y') = q x y + q x y')
    (hsmul : ∀ (c : ℝ) x y, q x (c • y) = c * q x y)
    (hadd' : ∀ x x' y, q (x + x') y = q x y + q x' y)
    (hsmul' : ∀ (c : ℝ) x y, q (c • x) y = c * q x y) (K : V →ₗ[ℝ] U) :
    ∃ T : U →ₗ[ℝ] V, IsAdjointFor (fun v v' : V => inner ℝ v v') q K T := by
  let l : U → (V →ₗ[ℝ] ℝ) := fun u =>
    { toFun := fun v => q (K v) u
      map_add' := fun v v' => by simp only [map_add, hadd']
      map_smul' := fun c v => by simp only [map_smul, hsmul', RingHom.id_apply, smul_eq_mul] }
  let t : U → V := fun u =>
    (InnerProductSpace.toDual ℝ V).symm (LinearMap.toContinuousLinearMap (l u))
  have ht : ∀ u v, inner ℝ v (t u) = q (K v) u := by
    intro u v
    rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
    rfl
  refine ⟨{ toFun := t, map_add' := ?_, map_smul' := ?_ }, fun v u => (ht u v).symm⟩
  · intro u u'
    refine ext_inner_left ℝ fun v => ?_
    rw [inner_add_right, ht, ht, ht, hadd]
  · intro c u
    refine ext_inner_left ℝ fun v => ?_
    rw [RingHom.id_apply, inner_smul_right, ht, ht, hsmul]
section Pairing
variable {L j N : ℕ} (S : PeriodicLattice.Scales 4 L j N)
  (Λ' : Set (PeriodicLattice.GridPoint 4 S.coarseMesh))
end Pairing
section SeriesExpansions
variable (W : CoarseCubeRegion)
  (e : CenteredCoarseIndex W.scales W.sites ≃ W.gaugeSetting.CoarseBond)
end SeriesExpansions
end GeneralTorus.CenteredCompressionLowerBoundProof
end
end YangMills.Construction
