import YangMills.Construction.Matrices.ClassicalHarmonicAnalysisOnG
import YangMills.Construction.Matrices.ProjectionsCommuteWithTwoSidedTranslations
import YangMills.Construction.TransferOperators.PeriodicStatesHaarMeasureCubicLatticesAndIntegralOperators
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.Matrices.ComplexMatrix2 YangMills.Construction.Schatten
open YangMills.Construction.TransferOperators.GibbsHaarKernels
  (HaarPiInvariance ContinuousKernelOperatorProps)
noncomputable section
namespace YangMills.Construction.SpinHarmonics.BiTranslation
open SeveralVariables
variable {J : Type} [Finite J]
theorem continuous_isotypicKernel (l : J → HalfNatural) :
    Continuous fun p : (J → specialUnitary) × (J → specialUnitary) => isotypicKernel l p.1 p.2 := by
  let _ : Fintype J := Fintype.ofFinite J
  simp only [isotypicKernel, finprod_eq_prod_of_fintype]
  refine continuous_finsetProd _ fun b _ =>
    continuous_const.mul ((spinCharacter (l b)).continuous.comp ?_)
  exact ((continuous_apply b).comp continuous_fst).mul
    ((continuous_apply b).comp continuous_snd).inv
omit [Finite J] in
theorem isotypicKernel_biTranslate
    (hconj : ∀ t : HalfNatural, IsConjInvariant (spinCharacter t)) (l : J → HalfNatural)
    (g g' u u' : J → specialUnitary) :
    isotypicKernel l (biTranslate g g' u) (biTranslate g g' u') =
      isotypicKernel l u u' := by
  refine finprod_congr fun b => ?_
  have h : biTranslate g g' u b * (biTranslate g g' u' b)⁻¹ =
      g b * (u b * (u' b)⁻¹) * (g b)⁻¹ := by
    simp only [biTranslate]
    group
  rw [h, hconj (l b) (u b * (u' b)⁻¹) (g b)]
theorem toHaarL2_ae_eq {f : (J → specialUnitary) → ℂ} (hf : MemLp f 2 (haarPi J)) :
    (toHaarL2 f : (J → specialUnitary) → ℂ) =ᵐ[haarPi J] f := by
  rw [toHaarL2, dif_pos hf]
  exact hf.coeFn_toLp
theorem isotypicProj_commutes_biTranslate (hH : HaarPiInvariance J)
    (hOp : ∀ A : (J → specialUnitary) × (J → specialUnitary) → ℂ, Continuous A →
      ContinuousKernelOperatorProps J A)
    (hconj : ∀ t : HalfNatural, IsConjInvariant (spinCharacter t)) (l : J → HalfNatural) :
    IsotypicProjCommutesBiTranslate l := by
  intro g g' F
  have hmp : MeasurePreserving (biTranslate g g') (haarPi J) (haarPi J) :=
    hH.1 g g'
  have hA := continuous_isotypicKernel l
  have hK : HasKernel (haarPi J) (fun p => isotypicKernel l p.1 p.2)
      (isotypicProj l) := (hOp _ hA).2.1
  have hmem : MemLp (fun u => F (biTranslate g g' u)) 2 (haarPi J) :=
    (Lp.memLp F).comp_measurePreserving hmp
  have hmem' : MemLp (fun u => isotypicProj l F (biTranslate g g' u)) 2
      (haarPi J) :=
    (Lp.memLp (isotypicProj l F)).comp_measurePreserving hmp
  refine ⟨hmem, Lp.ext ?_⟩
  have hright := toHaarL2_ae_eq hmem'
  have hcomp := hmp.quasiMeasurePreserving.ae_eq_comp (hK F)
  refine ((hK _).trans (Filter.Eventually.of_forall fun u => ?_)).trans
    (hcomp.symm.trans hright.symm)
  show ∫ w, isotypicKernel l u w *
        (toHaarL2 fun v => F (biTranslate g g' v) : HaarL2 J) w
        ∂haarPi J =
      ∫ w, isotypicKernel l (biTranslate g g' u) w * F w ∂haarPi J
  have hmeas : AEStronglyMeasurable
      (fun w => isotypicKernel l (biTranslate g g' u) w * F w)
      (Measure.map (biTranslate g g') (haarPi J)) := by
    rw [hmp.map_eq]
    exact (hA.comp (Continuous.prodMk_right _)).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable F)
  calc ∫ w, isotypicKernel l u w *
        (toHaarL2 fun v => F (biTranslate g g' v) : HaarL2 J) w
        ∂haarPi J
      = ∫ w, isotypicKernel l (biTranslate g g' u) (biTranslate g g' w) *
          F (biTranslate g g' w) ∂haarPi J := by
        refine integral_congr_ae ?_
        filter_upwards [toHaarL2_ae_eq hmem] with w hw
        rw [hw, isotypicKernel_biTranslate hconj]
    _ = ∫ w, isotypicKernel l (biTranslate g g' u) w * F w
          ∂Measure.map (biTranslate g g') (haarPi J) :=
        (integral_map hmp.aemeasurable hmeas).symm
    _ = ∫ w, isotypicKernel l (biTranslate g g' u) w * F w ∂haarPi J := by
        rw [hmp.map_eq]
theorem allIsotypicProjCommuteBiTranslate_of_facts (hFacts : HarmonicAnalysisFacts)
    (hKer : YangMills.Construction.TransferOperators.GibbsHaarKernels.Statement) :
    AllIsotypicProjCommuteBiTranslate := by
  intro J _ _ l
  exact isotypicProj_commutes_biTranslate (hKer.2.1 J) (hKer.2.2.2 J).1
    (fun t => (hFacts t t).2.2.1.isConjInvariant) l
end YangMills.Construction.SpinHarmonics.BiTranslation
end
