import YangMills.Construction.Lattice.DecompositionOfTheFormGreenOperatorProof
import YangMills.Construction.Lattice.DifferenceOperatorsOfTheBareLattice
import YangMills.Construction.Lattice.ExistenceOfTheOperatorsOfASeparatedSequence
import YangMills.Construction.Lattice.ProductsOfTheFormGreenOperator
import YangMills.Construction.Lattice.RepresentationOfTheGaugeProjections
import YangMills.Construction.Lattice.SymmetryOfTheDirichletSiteOperators
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.PeriodicLattice YangMills.Construction.PeriodicLattice.DirichletOperators YangMills.Construction.FiniteDimReal
noncomputable section
namespace YangMills.Construction.SeparatedSequences.FormProjections
section Algebra
variable {V W C : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  [AddCommGroup C] [Module ℝ C]
namespace ProjectionIdentities
variable {G : Module.End ℝ V} {d : W →ₗ[ℝ] V} {s : V →ₗ[ℝ] W} {R : Module.End ℝ W}
  {Q : V →ₗ[ℝ] C} {Qs : C →ₗ[ℝ] V} {I : Module.End ℝ C}
end ProjectionIdentities
section Symmetry
variable {ip : V → V → ℝ} {X : Module.End ℝ V}
end Symmetry
end Algebra
section InnerProducts
theorem latticeInner_comm {ι : Type} (L t : ℕ) (f g : ι → ℝ) :
    latticeInner L t f g = latticeInner L t g f := by apply _root_.YangMills.Construction.SeparatedSequences.GreenDecomposition.latticeInner_comm <;> assumption
theorem latticeInner_sub_right {ι : Type} [Finite ι] (L t : ℕ) (f g h : ι → ℝ) :
    latticeInner L t f (g - h) = latticeInner L t f g - latticeInner L t f h := by
  let _ := Fintype.ofFinite ι
  simp only [latticeInner, finsum_eq_sum_of_fintype, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
end InnerProducts
namespace Pairings
variable (D : BaseParameters) (Ω : ℕ → Set D.Torus) (φ : BondFrame)
theorem restrictedOneInner_comm (A B : D.RegionOneForms Ω φ) :
    D.restrictedOneInner Ω φ A B = D.restrictedOneInner Ω φ B A := by apply _root_.YangMills.Construction.SeparatedSequences.GreenDecomposition.restrictedOneInner_comm <;> assumption
theorem restrictedZeroInner_comm (f g : D.RegionZeroForms Ω) :
    D.restrictedZeroInner Ω f g = D.restrictedZeroInner Ω g f :=
  latticeInner_comm _ _ _ _
end Pairings
end YangMills.Construction.SeparatedSequences.FormProjections
end
