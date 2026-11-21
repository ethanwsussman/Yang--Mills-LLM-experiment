import YangMills.Construction.EuclideanFunctionals.BoundedOperatorOfOnePlate
import YangMills.Construction.EuclideanFunctionals.OneInsertionAsAnOperatorProof
import Mathlib
set_option autoImplicit false
open YangMills.Construction.RealPlane
open scoped InnerProductSpace
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.ProductInsertionOp
theorem prependComponent_eq (η : ℝ) (α : RealPlane → ℂ) (φ : RealPlane → ℝ)
    (A : FreeSep) :
    OneInsertionOperator.prependComponent (η / 4) (productFunction α φ) A = productTimesLifted η α φ A := by
  have h : 2 * (η / 4) = η / 2 := by ring
  simp only [OneInsertionOperator.prependComponent, OneInsertionOperator.liftComponent,
    OneInsertionOperator.liftTwice, productTimesLifted, liftedProduct, liftedElement, h]
theorem tensorComp_transl (hA : TupleRules.MotionOnFree) (z : R4)
    (A : FreeSep) (q : ℕ) :
    tensorComp q ((EuclidMotion.transl z).actFree A) =
      translateArgs z (tensorComp q A) := by apply _root_.YangMills.Construction.EuclideanFunctionals.OneInsertionOperator.tensorComp_actFree_transl <;> assumption
theorem holds_of_rules (hT : TupleRules.TupleSpanActionRules)
    (hI : OneInsertionOperator.statement)
    (hR : MotionMulRules.MotionMulTupleRules) : Holds := by
  intro m S σ p C c η α φ hb hd
  obtain ⟨-, -, hAct, -⟩ := hT
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hProd, -⟩ := hR
  obtain ⟨hC1, hSupp, -⟩ := hProd α hd.profile_mem φ hd.label_mem
  have hη := hd.height_pos
  have hcoef : 2 * (η / 4) = η / 2 := by ring
  have hsupport : supp (productFunction α φ) ⊆ {x | |x 3| < η / 4} := by
    intro x hx
    have hs : |(planeComponent x) 0| < c * η := hd.tsupport_subset (hSupp hx).1
    have h₀ : (planeComponent x) 0 = x 3 := by simp [planeComponent]
    rw [h₀] at hs
    have hc := hd.fraction_lt_quarter
    show |x 3| < η / 4
    nlinarith
  have hb₀ : 0 ≤ C φ * η ^ (-p) * profileL1Norm α :=
    mul_nonneg (mul_nonneg (hb.nonneg_constant φ hd.label_mem) (Real.rpow_nonneg hη.le _))
      (MeasureTheory.integral_nonneg fun _ => norm_nonneg _)
  have hbound : OneInsertionOperator.InsertionBounded σ (η / 4) (productFunction α φ)
      (C φ * η ^ (-p) * profileL1Norm α) := fun F hF A hA =>
    hb.le_bound η hη hd.height_le_one φ hd.label_mem α hd.profile_mem hd.tsupport_subset F hF A hA
  obtain ⟨hLin, hComp, -, hEx, hActs, hNorm, hForm⟩ :=
    hI m S σ (η / 4) (productFunction α φ) _ (by positivity) hC1 hsupport hb₀ hbound
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, OneInsertionOperator.insertionOp σ (η / 4) (productFunction α φ),
    ?_, hNorm, ?_, hForm⟩
  · intro A hA
    rw [← prependComponent_eq]
    exact hLin.mem_upper A hA
  · intro A hA A' hA' z
    simpa only [prependComponent_eq] using hLin.map_add_smul A hA A' hA' z
  · intro A hA
    rw [← prependComponent_eq]
    exact hComp.comp_zero A hA
  · intro A hA q x
    rw [← prependComponent_eq, hComp.comp_succ A hA q, liftedElement,
      tensorComp_transl hAct, hcoef]
    rfl
  · intro A hA q x
    rw [← prependComponent_eq, hComp.comp_succ_apply A hA q x, hcoef]
  · intro A hA
    rw [← prependComponent_eq]
    exact hActs A hA
  · intro B' hB'
    refine hEx.unique (fun A hA => ?_) hActs
    rw [prependComponent_eq]
    exact hB' A hA
end YangMills.Construction.EuclideanFunctionals.ProductInsertionOp
