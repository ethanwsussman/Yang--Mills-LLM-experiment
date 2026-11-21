import YangMills.Construction.Lattice.DifferenceOperatorsOfTheBareLattice
import YangMills.Construction.Lattice.LayerBondsCoarseSpacesAndAverages
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open PeriodicLattice PeriodicLattice.DirichletOperators
namespace PeriodicLattice.ClosedBareForms
variable {L m K t : ℕ} {ι κ : Type}
theorem latticeInner_eq_sum [Fintype ι] (f g : ι → ℝ) :
    latticeInner L t f g = finestMeshInLevelUnits L t ^ 4 * ∑ i, f i * g i := by
  unfold latticeInner
  rw [finsum_eq_sum_of_fintype]
theorem latticeInner_comm [Fintype ι] (f g : ι → ℝ) :
    latticeInner L t f g = latticeInner L t g f := by
  simp only [latticeInner_eq_sum, mul_comm (f _)]
theorem latticeInner_formalAdjoint [Fintype ι] [Fintype κ] (T : (ι → ℝ) →ₗ[ℝ] (κ → ℝ))
    (f : ι → ℝ) (g : κ → ℝ) :
    latticeInner L t (formalAdjoint L t T g) f = latticeInner L t g (T f) := by
  classical
  have h : ∃ T' : (κ → ℝ) →ₗ[ℝ] (ι → ℝ),
      ∀ f g, latticeInner L t g (T f) = latticeInner L t (T' g) f := by
    refine ⟨(LinearMap.toMatrix' T).transpose.mulVecLin, fun f g => ?_⟩
    rw [latticeInner_eq_sum, latticeInner_eq_sum]
    congr 1
    have h : T f = (LinearMap.toMatrix' T).mulVec f := (LinearMap.toMatrix'_mulVec T f).symm
    rw [h]
    change g ⬝ᵥ (LinearMap.toMatrix' T).mulVec f =
      ((LinearMap.toMatrix' T).transpose.mulVec g) ⬝ᵥ f
    rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
  unfold formalAdjoint
  exact (Classical.epsilon_spec h f g).symm
end PeriodicLattice.ClosedBareForms
end YangMills.Construction
end
