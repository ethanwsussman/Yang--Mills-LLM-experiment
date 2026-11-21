import YangMills.Construction.Lattice.AdjointsAndProjectionsOfASequence
import YangMills.Construction.Lattice.RelationOfTheMassiveOperators
import YangMills.Construction.Lattice.TwoFormsOfTheMassiveFormOperator
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.PeriodicLattice YangMills.Construction.PeriodicLattice.DirichletOperators YangMills.Construction.FiniteDimReal YangMills.Construction.SeparatedSequences.BaseParameters
noncomputable section
namespace YangMills.Construction.SeparatedSequences.GreenDecomposition
theorem latticeInner_comm {ι : Type} (L t : ℕ) (f g : ι → ℝ) :
    latticeInner L t f g = latticeInner L t g f := by
  unfold latticeInner
  congr 1
  exact finsum_congr fun i => mul_comm _ _
theorem formalAdjoint_spec {ι κ : Type} [Finite ι] [Finite κ] (L t : ℕ)
    (T : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) :
    ∀ f g, latticeInner L t g (T f) = latticeInner L t (formalAdjoint L t T g) f := by
  classical
  cases nonempty_fintype ι
  cases nonempty_fintype κ
  refine Classical.epsilon_spec
    (p := fun T' : (κ → ℝ) →ₗ[ℝ] (ι → ℝ) =>
      ∀ f g, latticeInner L t g (T f) = latticeInner L t (T' g) f)
    ⟨Matrix.toLin' (LinearMap.toMatrix' T).transpose, fun f g => ?_⟩
  simp only [latticeInner, finsum_eq_sum_of_fintype]
  congr 1
  change g ⬝ᵥ T f = (Matrix.toLin' (LinearMap.toMatrix' T).transpose g) ⬝ᵥ f
  rw [Matrix.toLin'_apply, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec,
    LinearMap.toMatrix'_mulVec]
section Chain
variable (D : BaseParameters) (Ω : ℕ → Set D.Torus) (φ : BondFrame)
theorem finite_bareSite : Finite (BareSite D.L D.m D.K) :=
  BaseParameters.instFiniteLatticeSite D 0
theorem restrictedOneInner_comm (A B : ↥(oneFormsOn D.K (Ω 0) φ)) :
    D.restrictedOneInner Ω φ A B = D.restrictedOneInner Ω φ B A :=
  latticeInner_comm _ _ _ _
end Chain
end YangMills.Construction.SeparatedSequences.GreenDecomposition
end
