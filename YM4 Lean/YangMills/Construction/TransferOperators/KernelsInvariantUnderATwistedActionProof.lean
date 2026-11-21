import YangMills.Construction.InfiniteLattice.TraceOnTheGroupAndOneBondWeight
import YangMills.Construction.Matrices.CharactersOfG
import YangMills.Construction.TransferOperators.KernelsInvariantUnderATwistedAction
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory SpinHarmonics
namespace TransferOperators
namespace TwistInvariantKernels
theorem twistedConjAction_mul_inv {J V : Type} (t h : J → V)
    (g : V → Matrices.ComplexMatrix2.specialUnitary)
    (u u' : J → Matrices.ComplexMatrix2.specialUnitary) (b : J) :
    twistedConjAction t h g u b * (twistedConjAction t h g u' b)⁻¹ =
      g (t b) * (u b * (u' b)⁻¹) * (g (t b))⁻¹ := by
  simp only [twistedConjAction]
  group
theorem continuous_singleBondWeight {β : ℝ}
    (hc : InfiniteLattice.SingleBondWeightRealClassFunction β) :
    Continuous (InfiniteLattice.singleBondWeight β) := by
  have h : InfiniteLattice.singleBondWeight β =
      fun w => (((InfiniteLattice.singleBondWeight β w).re : ℝ) : ℂ) :=
    funext fun w => Complex.ext (by simp) (by simp [hc.1 w])
  rw [h]
  exact Complex.continuous_ofReal.comp hc.2.1
theorem continuous_mul_inv_apply {J : Type} (b : J) :
    Continuous fun p : (J → Matrices.ComplexMatrix2.specialUnitary) ×
        (J → Matrices.ComplexMatrix2.specialUnitary) => p.1 b * (p.2 b)⁻¹ :=
  ((continuous_apply b).comp continuous_fst).mul ((continuous_apply b).comp continuous_snd).inv
end TwistInvariantKernels
theorem twistInvariantKernelsStatement_proof
    (hWeight : InfiniteLattice.TraceAndSingleBondWeight)
    (hChar : AllCharacterFacts) : TwistInvariantKernelsStatement := by
  intro β hβ J _
  have hc := (hWeight.2 β hβ).1
  refine ⟨fun V t h g u u' => ⟨?_, ?_, fun l => ?_⟩, ?_, fun l => ?_⟩
  · refine finprod_congr fun b => ?_
    rw [TwistInvariantKernels.twistedConjAction_mul_inv]
    exact hc.2.2.1 _ _
  · refine finprod_congr fun b => ?_
    refine tsum_congr fun l => ?_
    rw [TwistInvariantKernels.twistedConjAction_mul_inv, (hChar l).isConjInvariant]
  · refine finprod_congr fun b => ?_
    rw [TwistInvariantKernels.twistedConjAction_mul_inv, (hChar (l b)).isConjInvariant]
  · let _ : Fintype J := Fintype.ofFinite J
    simp only [linkProductKernel, finprod_eq_prod_of_fintype]
    exact continuous_finsetProd _ fun b _ =>
      (TwistInvariantKernels.continuous_singleBondWeight hc).comp
        (TwistInvariantKernels.continuous_mul_inv_apply b)
  · let _ : Fintype J := Fintype.ofFinite J
    simp only [isotypicKernel, finprod_eq_prod_of_fintype]
    exact continuous_finsetProd _ fun b _ => continuous_const.mul
      ((spinCharacter (l b)).continuous.comp
        (TwistInvariantKernels.continuous_mul_inv_apply b))
end TransferOperators
end YangMills.Construction
end
