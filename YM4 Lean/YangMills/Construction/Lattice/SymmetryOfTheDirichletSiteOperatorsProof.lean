import YangMills.Construction.Lattice.CommutationOfTheDifferenceWithTheLaplaciansProof
import YangMills.Construction.Lattice.CommutatorsOfTheDirichletOperatorsWithFunctionsProof
import YangMills.Construction.Lattice.ProductsOfTheFormGreenOperatorProof
import YangMills.Construction.Lattice.RelationOfTheMassiveOperatorsProof
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.PeriodicLattice YangMills.Construction.PeriodicLattice.DirichletOperators YangMills.Construction.FiniteDimReal YangMills.Construction.RealInnerForms YangMills.Construction.SeparatedSequences.BaseParameters
noncomputable section
namespace YangMills.Construction.SeparatedSequences.DirichletSymmetry
section Abstract
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
end Abstract
section Inner
variable {L t : ℕ} {ι : Type}
theorem latticeInner_comm (f g : ι → ℝ) : latticeInner L t f g = latticeInner L t g f := by apply _root_.YangMills.Construction.SeparatedSequences.MassiveRelation.latticeInner_comm <;> assumption
theorem latticeInner_sum [Finite ι] {κ : Type} [Fintype κ] (f : ι → ℝ) (g : κ → ι → ℝ) :
    latticeInner L t f (∑ k, g k) = ∑ k, latticeInner L t f (g k) := by
  have := Fintype.ofFinite ι
  simp only [latticeInner, finsum_eq_sum_of_fintype, Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
end Inner
variable (D : BaseParameters) (Ω : ℕ → Set D.Torus)
theorem finite_bareSite : Finite (BareSite D.L D.m D.K) := D.instFiniteLatticeSite 0
theorem siteProjection_coe (f : ↥(zeroFormsOn D.K (Ω 0))) :
    siteProjection D.K (Ω 0) f.1 = f.1 := by apply _root_.YangMills.Construction.GradLaplacianCommutation.siteProjection_val <;> assumption
theorem restrictedZeroInner_comm (f g : ↥(zeroFormsOn D.K (Ω 0))) :
    D.restrictedZeroInner Ω f g = D.restrictedZeroInner Ω g f :=
  latticeInner_comm _ _
theorem restrictedZeroInner_sub (f g h : ↥(zeroFormsOn D.K (Ω 0))) :
    D.restrictedZeroInner Ω f (g - h) =
      D.restrictedZeroInner Ω f g - D.restrictedZeroInner Ω f h := by apply _root_.YangMills.Construction.SeparatedSequences.GreenOperatorProducts.restrictedZeroInner_sub <;> assumption
theorem mem_fineBlock_self {n : ℕ} (y : D.LatticeSite n) :
    (y : D.Torus) ∈ fineBlock (D := D) y := by apply _root_.YangMills.Construction.SeparatedSequences.DirichletCommutators.mem_fineBlock_self <;> assumption
end YangMills.Construction.SeparatedSequences.DirichletSymmetry
end
