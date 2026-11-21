import YangMills.Construction.ReflectionPositivity.ActionOfTheLatticeIsometriesTheTwoFieldsAndTheReflections
import YangMills.Construction.ReflectionPositivity.CarrierOfTheSitePictureProof
import YangMills.Construction.ReflectionPositivity.ZeroEnergyAndInvariantObservables
import YangMills.Construction.ReflectionPositivity.ZeroEnergyOfTheSitePicture
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Set
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.SitePictureGround
open YangMills.Construction.InfiniteLattice (axisStep halfSpaceLocalObservables)
open YangMills.Construction.ReflectionPositivity.MirrorHyperplanes (unitPositiveClass
  SymmetryActionAndReflections linkReflect)
open YangMills.Construction.FormHilbert
open YangMills.Construction.JointSpectrum (CommutingFamily SpectralDomain)
open YangMills.Construction.ReflectionPositivity.DirectionPictures
section Calculus
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {J : Type} [Fintype J] [Nonempty J]
theorem spectralOp_eq_of_isSpectralIntegral {E : BorelPVM J K} {φ : SpectralDomain J → ℂ}
    {A : K →L[ℂ] K} (hA : E.IsSpectralIntegral φ A) : E.spectralOp φ = A := by apply _root_.YangMills.Construction.ReflectionPositivity.SiteCarrier.spectralOp_eq <;> assumption
def indicatorTop (J : Type) : SpectralDomain J → ℂ :=
  (spectrumTop J).1.indicator fun _ => (1 : ℂ)
theorem spectralOp_indicatorTop (E : BorelPVM J K) :
    E.spectralOp (indicatorTop J) = E (spectrumTop J) := by
  refine spectralOp_eq_of_isSpectralIntegral fun ψ => ?_
  rw [indicatorTop, integral_indicator_const _ (spectrumTop J).2, E.inner_apply_eq_norm_sq,
    Measure.real, E.quadMeasure_apply ψ (spectrumTop J), ENNReal.toReal_ofReal (by positivity)]
  simp
theorem isBddMeasurable_indicatorTop : IsBddMeasurable (indicatorTop J) := by
  refine ⟨measurable_const.indicator (spectrumTop J).2, 1, fun p => ?_⟩
  by_cases h : p ∈ (spectrumTop J).1 <;> simp [indicatorTop, h]
def sqrtSpectralFunction (J : Type) (p : SpectralDomain J) : ℂ :=
  (((p.1 : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ)
theorem isBddMeasurable_sqrtSpectralFunction : IsBddMeasurable (sqrtSpectralFunction J) := by
  have hc : Continuous fun p : SpectralDomain J => (p.1 : ℝ) ^ (1 / 2 : ℝ) :=
    (continuous_subtype_val.comp continuous_fst).rpow_const fun _ => Or.inr (by norm_num)
  refine ⟨(Complex.continuous_ofReal.comp hc).measurable, 1, fun p => ?_⟩
  rw [sqrtSpectralFunction, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg p.1.2.1 _)]
  exact Real.rpow_le_one p.1.2.1 p.1.2.2 (by norm_num)
theorem spectrumTop_eq_sqrt_mul_mul_sqrt {S : CommutingFamily K J}
    {E : BorelPVM J K} (hc : BoundedFunctionalCalculus S E) :
    E (spectrumTop J) = spectralSqrt E * E (spectrumTop J) * spectralSqrt E := by
  have hr : spectralSqrt E = E.spectralOp (sqrtSpectralFunction J) := rfl
  have hb : IsBddMeasurable fun p => sqrtSpectralFunction J p * indicatorTop J p := by
    obtain ⟨m, C, hC⟩ := isBddMeasurable_sqrtSpectralFunction (J := J)
    obtain ⟨m', C', hC'⟩ := isBddMeasurable_indicatorTop (J := J)
    refine ⟨m.mul m', C * C', fun p => ?_⟩
    rw [norm_mul]
    exact mul_le_mul (hC p) (hC' p) (norm_nonneg _) ((norm_nonneg _).trans (hC p))
  rw [hr, ← spectralOp_indicatorTop E,
    ← hc.spectralOp_mul _ _ isBddMeasurable_sqrtSpectralFunction isBddMeasurable_indicatorTop,
    ← hc.spectralOp_mul _ _ hb isBddMeasurable_sqrtSpectralFunction]
  congr 1
  funext p
  by_cases h : p ∈ (spectrumTop J).1
  · have h₁ : p.1 = 1 := h
    simp [indicatorTop, sqrtSpectralFunction, h, h₁]
  · simp [indicatorTop, h]
end Calculus
section Transport
variable (ν : unitPositiveClass) (μ : Fin 4)
def linkSiteIsometry
    (h : ∀ ψ ψ', inner ℂ (linkSiteIntertwiner ν μ ψ) (linkSiteIntertwiner ν μ ψ') = inner ℂ ψ ψ') :
    ReflectionPair.link.Hilb ν μ →ₗᵢ[ℂ] ReflectionPair.site.Hilb ν μ :=
  (transferKernelOrth ν μ).subtypeₗᵢ.comp (LinearMap.isometryOfInner _ h)
end Transport
theorem sitePictureGroundState_holds (hPictures : ReflectionPairTheorem)
    (hSpectral : JointSpectralCalculusTheorem)
    (hLink : LinkPictureEmbedsInSitePicture)
    (hZero : GroundStateAndInvariance)
    (hAction : SymmetryActionAndReflections) :
    SitePictureGroundStateTheorem := by
  intro ν μ
  obtain ⟨hReflections, -, ⟨-, hW, hWT, hWU⟩, -⟩ := hLink ν μ
  have hZ := hZero ν μ
  refine ⟨fun F hF G hG => ?_, fun F hF v => ?_⟩
  · let W := (linkSiteIsometry ν μ hW.1.2).toContinuousLinearMap
    have hWapply : ∀ ψ, W ψ = (linkSiteIntertwiner ν μ ψ : ReflectionPair.site.Hilb ν μ) :=
      fun _ => rfl
    have hInter : IntertwinesIsometrically (ReflectionPair.site.opFamily ν μ)
        (ReflectionPair.link.opFamily ν μ) W :=
      { inner_map := (linkSiteIsometry ν μ hW.1.2).inner_map_map
        intertwine_A := by
          ext ψ
          exact hWT ψ
        intertwine_B := fun l => by
          ext ψ
          exact hWU l ψ }
    have hEsite := (hPictures ν μ ReflectionPair.site).2.2.2.2.1
    have hElink := (hPictures ν μ ReflectionPair.link).2.2.2.2.1
    obtain ⟨-, hCalc, -, -, -, hRoot, hTransport⟩ :=
      (hSpectral (ReflectionPair.site.Hilb ν μ) (TransverseAxis μ)
        (ReflectionPair.site.opFamily ν μ)).2.2 (ReflectionPair.site.jointPVM ν μ) hEsite
    have hProj := (hTransport (ReflectionPair.link.Hilb ν μ) (ReflectionPair.link.opFamily ν μ)
      (ReflectionPair.link.jointPVM ν μ) hElink W hInter).2 (indicatorTop _)
      isBddMeasurable_indicatorTop
    rw [spectralOp_indicatorTop, spectralOp_indicatorTop] at hProj
    have hself := (isSelfAdjoint_iff_inner_eq _).mp hRoot.selfAdjoint
    have hclass : ∀ G ∈ halfSpaceLocalObservables μ,
        spectralSqrt (ReflectionPair.site.jointPVM ν μ) (ReflectionPair.site.obsClass ν μ G) =
          W (ReflectionPair.link.obsClass ν μ G) := fun G hG => (hW.2 G hG).symm
    set P := ReflectionPair.site.jointPVM ν μ (spectrumTop (TransverseAxis μ)) with hPdef
    set R := spectralSqrt (ReflectionPair.site.jointPVM ν μ) with hRdef
    have hsplit : P = R * P * R := spectrumTop_eq_sqrt_mul_mul_sqrt hCalc
    have hmove : ∀ ψ, P (W ψ) =
        W (ReflectionPair.link.jointPVM ν μ (spectrumTop (TransverseAxis μ)) ψ) :=
      fun ψ => (congrArg (fun A => A ψ) hProj).symm
    calc inner ℂ (ReflectionPair.site.obsClass ν μ F)
          (groundProjection μ ReflectionPair.site ν (ReflectionPair.site.obsClass ν μ G))
        = inner ℂ (ReflectionPair.site.obsClass ν μ F)
            ((R * P * R) (ReflectionPair.site.obsClass ν μ G)) := by
          rw [← hsplit]
          rfl
      _ = inner ℂ (R (ReflectionPair.site.obsClass ν μ F))
            (P (R (ReflectionPair.site.obsClass ν μ G))) := hself _ _
      _ = inner ℂ (W (ReflectionPair.link.obsClass ν μ F))
            (W (groundProjection μ ReflectionPair.link ν
              (ReflectionPair.link.obsClass ν μ G))) := by
          rw [hclass F hF, hclass G hG, hmove]
          rfl
      _ = inner ℂ (ReflectionPair.link.obsClass ν μ F)
            (groundProjection μ ReflectionPair.link ν (ReflectionPair.link.obsClass ν μ G)) :=
          (linkSiteIsometry ν μ hW.1.2).inner_map_map _ _
      _ = _ := hZ.2.1 F hF G hG
  · have hobs := (hAction.2.2.2.2.1 (linkReflect μ) F hF).1
    refine ⟨?_, (hZ.1 F hF v).2⟩
    rw [(hReflections.2.2 F hF).2]
    exact (hZ.1 _ hobs (axisStep 1 μ)).2.symm.trans (hZ.1 F hF (axisStep 1 μ)).1
end YangMills.Construction.ReflectionPositivity.SitePictureGround
