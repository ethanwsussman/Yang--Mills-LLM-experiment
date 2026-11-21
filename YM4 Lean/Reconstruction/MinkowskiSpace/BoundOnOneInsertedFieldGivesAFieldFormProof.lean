import Reconstruction.MinkowskiSpace.BoundOnOneInsertedFieldGivesAFieldForm
import Reconstruction.MinkowskiSpace.DensityOfOneInsertedField
import Reconstruction.MinkowskiSpace.FormRepresentsItsFunctionalAndIsEuclidean
import Reconstruction.MinkowskiSpace.FormWithNoFieldOfAFunctional
import Reconstruction.MinkowskiSpace.OperatorsAtTheMiddleOfTheDensity
import Reconstruction.MinkowskiSpace.OperatorsWriteOneInsertedField
import Reconstruction.MinkowskiSpace.SelfAdjointnessOfTheFieldOperators
import Reconstruction.MinkowskiSpace.UniquenessOfTheFieldOperators
import Reconstruction.MinkowskiSpace.VectorsWriteTimeOrderedTuples
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InsertedFieldForm
theorem one_le_formConstant {p C : ℝ} (hp : 0 ≤ p) (hC : 1 ≤ C) :
    1 ≤ formConstant p C := by
  have hthree : (1 : ℝ) ≤ (3 : ℝ) ^ (p + 5) := Real.one_le_rpow (by norm_num) (by linarith)
  have hmax : (1 : ℝ) ≤ max 1 (max (TestFunctions.uniformNorm CubeKernels.quadBump)
      (max (TestFunctions.uniformNorm (deriv CubeKernels.quadBump))
        (max (TestFunctions.uniformNorm CubeKernels.thirdDerivBump)
          (TestFunctions.uniformNorm (deriv CubeKernels.thirdDerivBump))))) := le_max_left _ _
  have hkern : (1 : ℝ) ≤ CubeKernels.cubeKernelConst := by
    unfold CubeKernels.cubeKernelConst
    have := one_le_pow₀ hmax (n := 4)
    linarith
  unfold formConstant
  have hfirst : (1 : ℝ) ≤ (3 : ℝ) ^ (p + 5) * 7 ^ 4 * 8 ^ 5 := by nlinarith
  have hsecond : (1 : ℝ) ≤ (3 : ℝ) ^ (p + 5) * 7 ^ 4 * 8 ^ 5 * CubeKernels.cubeKernelConst :=
    one_le_mul_of_one_le_of_one_le hfirst hkern
  exact one_le_mul_of_one_le_of_one_le hsecond hC
theorem boundedFieldFormOfInsertionBound_holds (zeroField : ZeroFieldForm)
    (density : FieldDensityExists)
    (midOps : MidpointOperators.MidpointOperatorFacts)
    (midInsert : MidpointInsertion.MidpointHasInsertionIntegral)
    (midSelfAdj : MidpointSelfAdjoint.MidpointSelfAdjointStatement)
    (unique : FieldOperatorUniqueness.Unique)
    (timeOrdered : TimeOrderedVectors.Represents)
    (reps : RepresentsOfTimeOrdered) : BoundedFieldFormOfInsertionBound := by
  intro sigma hf hs hpos E hE p C hp hC hb
  have hyp : Hypotheses sigma E p C := ⟨hf, hs, hpos, hE, hp, hC, hb⟩
  obtain ⟨G, hG⟩ := density sigma E p C hyp
  have hzero := zeroField sigma E p C hyp
  obtain ⟨hshift, hnorm, -⟩ := midOps sigma E p C hyp G hG
  have hbdd : FieldForms.IsBoundedFieldForm E (FieldFormConditions.vacuumState sigma)
      (midpointField sigma G) (formExponent p) (formConstant p C) :=
    { exponent_nonneg := by unfold formExponent; linarith
      one_le_const := one_le_formConstant hp hC
      isPVM := hzero.isPVM
      supportedOn := hzero.supportedOn
      norm_vacuum := hzero.norm_vacuum
      origin_fixes := hzero.origin_fixes
      isSelfAdjoint := midSelfAdj sigma E p C hyp G hG
      shift_conj := hshift
      opNorm_le := hnorm }
  have hwrite := midInsert sigma E p C hyp G hG
  have hvec := timeOrdered sigma E p C hyp G hG _ _ hbdd
  exact ⟨midpointField sigma G, hwrite,
    fun B hB s hs' => unique sigma E p C hyp _ _ hwrite hB s hs',
    hbdd, hvec, reps sigma E p C hyp _ _ _ hbdd hvec⟩
end YangMills.Construction.InsertedFieldForm
end
