import YangMills.Construction.ReflectionPositivity.CarrierOfTheSitePicture
import YangMills.Construction.ReflectionPositivity.CorrelationsOfTwoCubes
import YangMills.Construction.ReflectionPositivity.InequalitiesAtSeveralSteps
import YangMills.Construction.ReflectionPositivity.ReflectionSizesOfCubeObservables
import YangMills.Construction.ReflectionPositivity.SignChangesAndTheCube
import YangMills.Construction.ReflectionPositivity.SitePicturesOfADirection
import YangMills.Construction.ReflectionPositivity.ZeroEnergyOfTheSitePicture
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
open InfiniteLattice (GaugeField)
theorem SiteReflectionPair.conclusion_holds
    (hFlip : SignFlipsPreserveCube) (hCarrier : SiteCarrierFacts)
    (hSteps : MultiStepInequalities) (hGround : SitePictureGroundStateTheorem)
    (hCorr : CubeCorrelationsTheorem) (hNorm : CubeReflectionNormProps) :
    SiteReflectionPair.Conclusion := by
  intro ν μ r
  refine ⟨hFlip ν μ r, hCarrier ν μ, fun l k hk => hSteps ν μ l k hk, hGround ν μ, hCorr ν μ r, ?_⟩
  obtain ⟨hadd, hsmul, hsym, hle⟩ := hNorm ν r
  refine ⟨⟨Seminorm.of (fun A : cubeObservableSpace r =>
      cubeReflectionNorm ν r (A : GaugeField (1 : ℝ) → ℂ) ^ (1 / 2 : ℝ))
      (fun A B => hadd A.1 A.2 B.1 B.2) (fun a A => hsmul a A.1 A.2), fun _ => rfl⟩, hsym, hle⟩
end YangMills.Construction.ReflectionPositivity.DirectionPictures
