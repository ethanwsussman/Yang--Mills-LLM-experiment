import YangMills.Construction.Matrices.CharactersOfG
import YangMills.Construction.TransferOperators.OperatorHatKeepsTwoSidedInvariance
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.Matrices.ComplexMatrix2 YangMills.Construction.TransferOperators
open YangMills.Construction.TransferOperators.GibbsHaarKernels
noncomputable section
namespace YangMills.Construction.SpinHarmonics
namespace HatInvariance
theorem isotypicKernel_leftRightTranslate (hChar : AllCharacterFacts) {K : Type} [Finite K]
    (l : K → HalfNatural) (g g' v v' : K → specialUnitary) :
    isotypicKernel l (leftRightTranslate g g' v) (leftRightTranslate g g' v') =
      isotypicKernel l v v' := by
  unfold isotypicKernel
  refine finprod_congr fun b => ?_
  have h : leftRightTranslate g g' v b * (leftRightTranslate g g' v' b)⁻¹ =
      g b * (v b * (v' b)⁻¹) * (g b)⁻¹ := by
    simp only [leftRightTranslate]
    group
  rw [h, (hChar (l b)).isConjInvariant]
variable {J : Type} [Finite J]
omit [Finite J] in
theorem glue_leftRightTranslate (B : Set J) (g g' : J → specialUnitary) (v : ↥B → specialUnitary)
    (z : ↥Bᶜ → specialUnitary) :
    glue B (leftRightTranslate (restrictTo B g) (restrictTo B g') v)
        (restrictTo Bᶜ (leftRightTranslate g g' (glue B v z))) =
      leftRightTranslate g g' (glue B v z) := by
  funext b
  by_cases h : b ∈ B
  · have h₁ := glue_of_mem B
      (leftRightTranslate (restrictTo B g) (restrictTo B g') v)
      (restrictTo Bᶜ (leftRightTranslate g g' (glue B v z))) ⟨b, h⟩
    have h₂ := glue_of_mem B v z ⟨b, h⟩
    simp only at h₁ h₂
    rw [h₁]
    simp only [leftRightTranslate, restrictTo, h₂]
  · have h₁ := glue_of_notMem B
      (leftRightTranslate (restrictTo B g) (restrictTo B g') v)
      (restrictTo Bᶜ (leftRightTranslate g g' (glue B v z))) ⟨b, h⟩
    simp only at h₁
    rw [h₁]
    rfl
theorem continuous_kernelIntegrand_at (B : Set J) (l : ↥B → HalfNatural) (H : C(J → specialUnitary, ℂ))
    (x : J → specialUnitary) :
    Continuous fun v' : ↥B → specialUnitary => isotypicKernel l (restrictTo B x) v' *
      H (glue B v' (restrictTo Bᶜ x)) := by
  have hpair : Continuous fun v' : ↥B → specialUnitary =>
      ((x, v') : (J → specialUnitary) × (↥B → specialUnitary)) :=
    continuous_const.prodMk continuous_id
  have h := (continuous_partKernelIntegrand B l H).comp hpair
  exact h
theorem partIsotypicProjC_leftRightTranslate (hChar : AllCharacterFacts) (B : Set J)
    (hHaar : HaarPiInvariance ↥B) (l : ↥B → HalfNatural) (g g' : J → specialUnitary)
    (H : C(J → specialUnitary, ℂ))
    (hH : ∀ u, H (leftRightTranslate g g' u) = H u) (u : J → specialUnitary) :
    partIsotypicProjC B l H (leftRightTranslate g g' u) =
      partIsotypicProjC B l H u := by
  set gB := restrictTo B g with hgB
  set gB' := restrictTo B g' with hgB'
  have hmp : MeasurePreserving (leftRightTranslate gB gB') (haarPi ↥B) (haarPi ↥B) :=
    hHaar.1 gB fun b => (gB' b)⁻¹
  have hcont := continuous_kernelIntegrand_at B l H (leftRightTranslate g g' u)
  have hsub : ∫ v', isotypicKernel l (restrictTo B (leftRightTranslate g g' u)) v' *
        H (glue B v' (restrictTo Bᶜ (leftRightTranslate g g' u))) ∂haarPi ↥B =
      ∫ w, isotypicKernel l (restrictTo B (leftRightTranslate g g' u))
          (leftRightTranslate gB gB' w) *
        H (glue B (leftRightTranslate gB gB' w)
          (restrictTo Bᶜ (leftRightTranslate g g' u))) ∂haarPi ↥B := by
    conv_lhs => rw [← hmp.map_eq]
    exact integral_map hmp.aemeasurable (by rw [hmp.map_eq]; exact hcont.aestronglyMeasurable)
  have hres : restrictTo B (leftRightTranslate g g' u) =
      leftRightTranslate gB gB' (restrictTo B u) := rfl
  show (∫ v', isotypicKernel l (restrictTo B (leftRightTranslate g g' u)) v' *
        H (glue B v' (restrictTo Bᶜ (leftRightTranslate g g' u))) ∂haarPi ↥B) =
      ∫ v', isotypicKernel l (restrictTo B u) v' *
        H (glue B v' (restrictTo Bᶜ u)) ∂haarPi ↥B
  rw [hsub]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  have hj : glue B (leftRightTranslate gB gB' w)
      (restrictTo Bᶜ (leftRightTranslate g g' u)) =
      leftRightTranslate g g' (glue B w (restrictTo Bᶜ u)) := by
    have h := glue_leftRightTranslate B g g' w (restrictTo Bᶜ u)
    rw [← h]
    congr 1
    funext b
    have hb : glue B w (restrictTo Bᶜ u) b = u b :=
      glue_of_notMem B w (restrictTo Bᶜ u) b
    simp only [restrictTo, leftRightTranslate, hb]
  simp only []
  rw [hj, hH, hres, isotypicKernel_leftRightTranslate hChar]
theorem hatSummand_leftRightTranslate (hChar : AllCharacterFacts) (B : Set J)
    (hHaar : HaarPiInvariance ↥B) (f : (↥B → specialUnitary) → ℂ) (hf : IsRealEntryPolynomial f)
    (g g' : J → specialUnitary) (F : C(J → specialUnitary, ℂ))
    (hF : ∀ u, F (leftRightTranslate g g' u) = F u)
    (hfi : ∀ u, pullFromPart B f (leftRightTranslate g g' u) = pullFromPart B f u)
    (l l' : ↥B → HalfNatural) (u : J → specialUnitary) :
    hatSummand B f hf F l l' (leftRightTranslate g g' u) = hatSummand B f hf F l l' u := by
  refine partIsotypicProjC_leftRightTranslate hChar B hHaar l' g g' _ (fun w => ?_) u
  show pullFromPart B f (leftRightTranslate g g' w) *
      partIsotypicProjC B l F (leftRightTranslate g g' w) =
    pullFromPart B f w * partIsotypicProjC B l F w
  rw [hfi, partIsotypicProjC_leftRightTranslate hChar B hHaar l g g' F hF]
end HatInvariance
open HatInvariance in
theorem HatInvariance.hatBiInvarianceStatement_holds
    (hStates : YangMills.Construction.TransferOperators.GibbsHaarKernels.Statement)
    (hChar : AllCharacterFacts) : HatBiInvarianceStatement := by
  intro J _ _ β B f hf _ hB g g' F _ hF hfi u
  have : Nonempty ↥B := hB.to_subtype
  have hHaar : HaarPiInvariance ↥B := hStates.2.1 ↥B
  by_cases hs : Summable fun p : (↥B → HalfNatural) × (↥B → HalfNatural) =>
      charCoeffRatio β p.1 p.2 • hatSummand B f hf F p.1 p.2
  · have hx : ∀ x, hatSum β B f hf F x =
        ∑' p : (↥B → HalfNatural) × (↥B → HalfNatural),
          charCoeffRatio β p.1 p.2 * hatSummand B f hf F p.1 p.2 x := fun x =>
      (ContinuousMap.tsum_apply hs x).symm
    rw [hx, hx]
    refine tsum_congr fun p => ?_
    rw [hatSummand_leftRightTranslate hChar B hHaar f hf g g' F hF hfi]
  · have h0 : hatSum β B f hf F = 0 := tsum_eq_zero_of_not_summable hs
    rw [h0]
    rfl
end YangMills.Construction.SpinHarmonics
end
