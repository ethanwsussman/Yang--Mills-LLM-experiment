import Reconstruction.MinkowskiSpace.TranslationOperatorsOfABoundedFieldFormProof
import Reconstruction.MinkowskiSpace.ScalarProductsOfTheVectorsAtRealPointsProof
import Reconstruction.MinkowskiSpace.TranslationOperatorsOfABoundedFieldForm
import Reconstruction.MinkowskiSpace.TranslationsOfTheVectorsAtRealPoints
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped ComplexConjugate InnerProductSpace Topology
noncomputable section
namespace YangMills.Construction.RealPointVectors.Translations
open YangMills.Construction.MinkowskiSpace YangMills.Construction.FieldForms YangMills.Construction.TestSpaces YangMills.Construction.WightmanReconstruction YangMills.Construction.OneLoopNotation YangMills.Construction.ComplexHilbert YangMills.Construction.ProjectionMeasures YangMills.Construction.RealPointVectors
theorem mem_diffCoordsInTube {n : ℕ} (x Y : PointTuple (n + 1))
    (hY : Y ∈ futureConeTuples (n + 1)) :
    tupleToComplex x + Complex.I • tupleToComplex (cumulativeSums Y) ∈ diffCoordsInTube (n + 1) := by apply _root_.YangMills.Construction.RealPointInnerProducts.shift_mem_diffCoordsInTube <;> assumption
theorem imPart_toComplex_mem_closedFutureCone (a : RealVec4) :
    MinkowskiSpace.imPart (toComplex a) ∈ closedFutureCone := by apply _root_.YangMills.Construction.FieldFormTranslations.imInClosedCone_toComplex <;> assumption
section Smeared
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {P : FourBorelSet → BddOp H} {Ω : H} {B : ℝ → BddOp H}
theorem spectralTranslation_shiftedStateVector (hst : StatesTranslateInner P Ω B) {n : ℕ}
    (a : RealVec4) (Y x : PointTuple (n + 1)) (hY : Y ∈ futureConeTuples (n + 1)) :
    spectralTranslation P (toComplex a) (shiftedStateVector P Ω B Y x) =
      shiftedStateVector P Ω B Y (x + fun _ => a) := by
  have hz := mem_diffCoordsInTube x Y hY
  have htr := (hst (n + 1) (n + 1) _ _ (toComplex a) hz hz
    (imPart_toComplex_mem_closedFutureCone a)).1
  refine htr.trans ?_
  simp only [shiftedStateVector]
  congr 1
  funext k μ
  simp only [tupleToComplex, toComplex, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Complex.ofReal_add]
  ring
theorem inner_smearedState_poincarePullback
    (hw : HilbertWellDefined.WeakIntegralUnique)
    (hst : StatesTranslateInner P Ω B) {n : ℕ} (a : RealVec4)
    (f : PointTuple (n + 1) → ℂ)
    (hf : ∀ Y ∈ futureConeTuples (n + 1),
      HasWeakIntegrandData Set.univ (shiftedStateVector P Ω B Y) f)
    (hf' : ∀ Y ∈ futureConeTuples (n + 1),
      HasWeakIntegrandData Set.univ (shiftedStateVector P Ω B Y) (poincarePullback (a, 1) f))
    (v : H) (Y : PointTuple (n + 1)) (hY : Y ∈ futureConeTuples (n + 1)) :
    ⟪v, smearedState P Ω B Y (poincarePullback (a, 1) f)⟫_ℂ =
      ⟪ContinuousLinearMap.adjoint (spectralTranslation P (toComplex a)) v,
        smearedState P Ω B Y f⟫_ℂ := by
  have hleft := (hw H (PointTuple (n + 1)) _ _ _ (hf' Y hY)).1 v
  have hright := (hw H (PointTuple (n + 1)) _ _ _ (hf Y hY)).1
    (ContinuousLinearMap.adjoint (spectralTranslation P (toComplex a)) v)
  simp only [smearedState]
  rw [hleft, hright, Measure.restrict_univ,
    ← integral_add_right_eq_self _ (fun _ => a : PointTuple (n + 1))]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only []
  rw [ContinuousLinearMap.adjoint_inner_left, spectralTranslation_shiftedStateVector hst a Y x hY]
  congr 1
  simp [poincarePullback]
end Smeared
theorem translationOfTestStates
    (hb : SmearedBoundaryVectors.Statement)
    (hm : TubeMatrixElements.Statement)
    (hs : RealPointVectors.SchwartzClosure)
    (hw : HilbertWellDefined.WellDefinedStatement)
    (hp : FieldForms.FieldProductProperties)
    (ht : FieldFormTranslations.TranslationOperatorFacts) :
    RealPointVectors.TranslationOfTestStatesStatement := by
  intro H _ _ _ P Ω B W C hcond n f a hf
  cases n with
  | zero =>
    have him := imPart_toComplex_mem_closedFutureCone a
    have hΩ := ((ht H P Ω B W C hcond).1.1 (toComplex a) (toComplex a) him him).2.2.2.2
    change spectralTranslation P (toComplex a) (scalarOfOrderZero f • Ω) =
      scalarOfOrderZero f • Ω
    rw [map_smul, hΩ]
  | succ n =>
    have hf' : poincarePullback (a, 1) f ∈ schwartzSet (n + 1) :=
      hs.2.2.1 (n + 1) f a hf
    have hf₀ : f ∈ schwartzSet (n + 1) := hf
    have hbv := hb P Ω B W C hcond
    have hst : StatesTranslateInner P Ω B :=
      (hp H P Ω B W C hcond).2.2.2.2.2.2.2.2.2.1
    refine hbv.eq_testState_of_isBoundaryLimit n _ hf' _ fun v => ?_
    have hlim := hbv.isBoundaryLimit_testState n f hf₀
      (ContinuousLinearMap.adjoint (spectralTranslation P (toComplex a)) v)
    rw [ContinuousLinearMap.adjoint_inner_left] at hlim
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with Y hY
    exact (inner_smearedState_poincarePullback hw.2.2.2 hst a f
      (fun Y hY => ((hm P Ω B W C hcond n v).2.2.2 Y hY f hf₀).1)
      (fun Y hY => ((hm P Ω B W C hcond n v).2.2.2 Y hY _ hf').1) v Y hY).symm
end YangMills.Construction.RealPointVectors.Translations
