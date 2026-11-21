import YangMills.Construction.Lattice.MassiveDirichletOperatorIdentityFacts
import YangMills.Construction.Lattice.DirichletLaplacianWithItsBoundaryTermProof
import YangMills.Construction.SeparatedSequences.ClassExpansionsInASettingOfRegionsProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YangMills.Construction
open Set PeriodicLattice PeriodicLattice.DirichletOperators
namespace DirichletLaplacian
variable {L m K : ℕ}
theorem unitStep_injective (hL : 2 ≤ L) {j : ℤ} (hj : 0 ≤ j) :
    Function.Injective (unitStep L m j) := by apply _root_.YangMills.Construction.PeriodicLattice.DirichletLaplacianSplitsOffBoundary.unitStep_injective <;> assumption
section InnerProduct
variable {ι κ : Type} {t : ℕ}
theorem latticeInner_eq_sum [Fintype ι] (f g : ι → ℝ) :
    latticeInner L t f g = finestMeshInLevelUnits L t ^ 4 * ∑ i, f i * g i := by
  rw [latticeInner, finsum_eq_sum_of_fintype]
theorem latticeInner_symm [Fintype ι] (f g : ι → ℝ) : latticeInner L t f g = latticeInner L t g f := by
  simp only [latticeInner_eq_sum, mul_comm (f _)]
theorem latticeInner_add_right [Fintype ι] (f g h : ι → ℝ) :
    latticeInner L t f (g + h) = latticeInner L t f g + latticeInner L t f h := by
  simp only [latticeInner_eq_sum, Pi.add_apply, mul_add, Finset.sum_add_distrib]
theorem ext_of_latticeInner [Fintype ι] (hξ : finestMeshInLevelUnits L t ≠ 0) {u v : ι → ℝ}
    (h : ∀ f : ι → ℝ, latticeInner L t u f = latticeInner L t v f) : u = v := by
  classical
  funext i
  have hi := h (Pi.single i 1)
  simp only [latticeInner_eq_sum, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at hi
  exact mul_left_cancel₀ (pow_ne_zero 4 hξ) hi
theorem exists_latticeInner_adjoint [Fintype ι] [Fintype κ] (T : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) :
    ∃ T' : (κ → ℝ) →ₗ[ℝ] (ι → ℝ), ∀ f g, latticeInner L t g (T f) = latticeInner L t (T' g) f := by
  classical
  refine ⟨(LinearMap.toMatrix' T).transpose.mulVecLin, fun f g => ?_⟩
  rw [latticeInner_eq_sum, latticeInner_eq_sum]
  congr 1
  have h : T f = (LinearMap.toMatrix' T).mulVec f := (LinearMap.toMatrix'_mulVec T f).symm
  rw [h]
  change g ⬝ᵥ (LinearMap.toMatrix' T).mulVec f =
    ((LinearMap.toMatrix' T).transpose.mulVec g) ⬝ᵥ f
  rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
theorem latticeInner_formalAdjoint [Fintype ι] [Fintype κ] (T : (ι → ℝ) →ₗ[ℝ] (κ → ℝ))
    (f : ι → ℝ) (g : κ → ℝ) : latticeInner L t (formalAdjoint L t T g) f = latticeInner L t g (T f) := by
  have h := exists_latticeInner_adjoint (L := L) (t := t) T
  unfold formalAdjoint
  exact (Classical.epsilon_spec h f g).symm
theorem latticeInner_indicatorMul [Fintype ι] (X : Set ι) (f g : ι → ℝ) :
    latticeInner L t f (indicatorMul X g) = latticeInner L t (indicatorMul X f) g := by
  simp only [latticeInner_eq_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  change f i * X.indicator g i = X.indicator f i * g i
  by_cases h : i ∈ X <;> simp [h]
theorem indicatorMul_of_mem_range {X : Set ι} {f : ι → ℝ}
    (h : f ∈ LinearMap.range (indicatorMul X)) : indicatorMul X f = f := by apply _root_.YangMills.Construction.SeparatedClasses.NestedOneForms.indicatorMul_of_mem <;> assumption
theorem apply_eq_zero_of_mem_range_indicatorMul {X : Set ι} {f : ι → ℝ}
    (h : f ∈ LinearMap.range (indicatorMul X)) {i : ι} (hi : i ∉ X) : f i = 0 := by
  rw [← indicatorMul_of_mem_range h]
  exact Set.indicator_of_notMem hi _
end InnerProduct
section Components
variable {t : ℕ}
theorem bondFrom_bijective (hs : Function.Injective (unitStep L m (levelDepth K 0))) :
    Function.Bijective (fun q : BareSite L m K × Fin 4 => bondFrom q.1 q.2) := by
  constructor
  · rintro ⟨x, μ⟩ ⟨y, ν⟩ h
    have h1 : x = y := congrArg (fun b : BareBond L m K => b.1.source) h
    subst h1
    have h2 : x + unitStep L m (levelDepth K 0) μ = x + unitStep L m (levelDepth K 0) ν :=
      congrArg (fun b : BareBond L m K => b.1.target) h
    rw [hs (add_left_cancel h2)]
  · rintro ⟨b, μ, h⟩
    refine ⟨(b.source, μ), Subtype.ext (Bond.ext rfl ?_)⟩
    change b.source + unitStep L m (levelDepth K 0) μ = b.target
    rw [← h]
    abel
variable [Fintype (BareSite L m K)] [Fintype (BareBond L m K)] [Fintype (BarePlaquette L m K)]
theorem sum_bareBond (hs : Function.Injective (unitStep L m (levelDepth K 0))) (F : BareBond L m K → ℝ) :
    ∑ b, F b = ∑ x, ∑ μ, F (bondFrom x μ) := by
  rw [← (bondFrom_bijective hs).sum_comp, Fintype.sum_prod_type]
theorem latticeInner_oneForms (hs : Function.Injective (unitStep L m (levelDepth K 0))) (A B : OneForms L m K) :
    latticeInner L t A B = ∑ μ, latticeInner L t (axisComponent A μ) (axisComponent B μ) := by
  simp only [latticeInner_eq_sum, sum_bareBond hs, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  rfl
theorem latticeInner_gradAdjoint (A : OneForms L m K) (f : ZeroForms L m K) :
    latticeInner L t (gradAdjoint L m K t A) f = latticeInner L t A (grad t f) :=
  latticeInner_formalAdjoint _ _ _
theorem latticeInner_curlAdjoint (F : TwoForms L m K) (A : OneForms L m K) :
    latticeInner L t (curlAdjoint L m K t F) A = latticeInner L t F (curl t A) :=
  latticeInner_formalAdjoint _ _ _
theorem latticeInner_scalarLaplacian (f g : ZeroForms L m K) :
    latticeInner L t f (scalarLaplacian L m K t g) = latticeInner L t (grad t f) (grad t g) := by
  change latticeInner L t f (gradAdjoint L m K t (grad t g)) = _
  rw [latticeInner_symm, latticeInner_gradAdjoint, latticeInner_symm]
theorem latticeInner_hodgeLaplacian (A B : OneForms L m K) :
    latticeInner L t A (hodgeLaplacian L m K t B) =
      latticeInner L t (curl t A) (curl t B) +
        latticeInner L t (gradAdjoint L m K t A) (gradAdjoint L m K t B) := by
  change latticeInner L t A (curlAdjoint L m K t (curl t B) + grad t (gradAdjoint L m K t B)) = _
  rw [latticeInner_add_right, ← latticeInner_gradAdjoint, latticeInner_symm A, latticeInner_curlAdjoint,
    latticeInner_symm (curl t B)]
variable {Ω₀ : Set (FourTorus L m)} {φ : BondFrame}
end Components
end DirichletLaplacian
end YangMills.Construction
end
