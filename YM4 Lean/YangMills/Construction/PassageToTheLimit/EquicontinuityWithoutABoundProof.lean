import YangMills.Construction.PassageToTheLimit.BoundedFormsThatConvergeAreEquicontinuous
import YangMills.Construction.PassageToTheLimit.EquicontinuityWithoutABound
import YangMills.Construction.PassageToTheLimit.LatticeFunctionalsAreBoundedForms
import YangMills.Construction.PassageToTheLimit.RestrictionsOfCentredFunctionalsToProducts
import YangMills.Construction.PassageToTheLimit.SpacesOfFunctionsOfClassC1AreBanachSpaces
import YangMills.Construction.PassageToTheLimit.TranslationsAreContinuousInTheC1Norm
import YangMills.Construction.PassageToTheLimit.TransportedLatticeFunctionalsAreBoundedForms
import Mathlib
set_option autoImplicit false
open Filter Set Topology
open scoped ENNReal NNReal
noncomputable section
namespace YangMills.Construction.LimitSpaces
open YangMills.Construction.LimitSpaces.Ambient YangMills.Construction.ReflectionPositivity.CutoffMirrors
namespace Ambient
variable {s : Conventions.StandingParameters} {E : Ambient} {q : ℕ} {W : Fin q → Set (E.Carrier s)}
theorem normC1_nonneg (f : E.Carrier s → ℝ) : 0 ≤ E.normC1 s f :=
  le_max_of_le_left (Real.iSup_nonneg fun _ => norm_nonneg _)
theorem isBoundedMultilinear_re_of_bound {S : E.C1ProductSpace s W → ℂ} {c : ℝ}
    (hS : IsRealFormBoundedBy S c) : IsBoundedMultilinear fun h => (S h).re := by
  refine lt_of_le_of_lt (b := ENNReal.ofReal |c|) ?_ ENNReal.ofReal_lt_top
  refine iSup₂_le fun h hh => ENNReal.ofReal_le_ofReal ?_
  have hprod0 : 0 ≤ ∏ l, E.normC1 s (h l).1 := Finset.prod_nonneg fun l _ => normC1_nonneg _
  have hprod1 : ∏ l, E.normC1 s (h l).1 ≤ 1 :=
    Finset.prod_le_one (fun l _ => normC1_nonneg _) fun l _ => hh l
  calc |(S h).re| ≤ ‖S h‖ := Complex.abs_re_le_norm _
    _ ≤ c * ∏ l, E.normC1 s (h l).1 := hS.2.2 h
    _ ≤ |c| * ∏ l, E.normC1 s (h l).1 := mul_le_mul_of_nonneg_right (le_abs_self c) hprod0
    _ ≤ |c| * 1 := mul_le_mul_of_nonneg_left hprod1 (abs_nonneg c)
    _ = |c| := mul_one _
end Ambient
theorem Ambient.uniformBoundednessEquicontinuity_holds
    (hComplete : Ambient.c1WithinComplete)
    (hShift : Ambient.translationContinuousC1Norm)
    (hConv : Ambient.pointwiseConvergentFormsEquicontinuous)
    (hRestr : Ambient.centredRestrictionsToProducts)
    (hTorus : torusFormsBounded)
    (hPeriod : periodizedFormsBounded) :
    Ambient.uniformBoundednessEquicontinuity := by
  intro M q hq
  refine ⟨fun s E => ⟨hComplete s E, hShift M s E, fun W hW hd => ?_⟩,
    fun D => (hTorus q hq).1 D, fun D W hW hd => (hTorus q hq).2 D W hW hd,
    fun s D W hL hW hd ht => hPeriod q hq s D W hL hW hd ht,
    fun s W hW hd => ?_, fun s W hW hd => ?_⟩
  · obtain ⟨hTup, hBdd⟩ := hConv s E q hq W hW hd
    exact ⟨hTup, hBdd, fun 𝒥 Dom Φ hΦ => hRestr s E q hq W hW hd 𝒥 Dom Φ hΦ⟩
  · intro 𝒥 K β hβ h𝒥 Ψ
    have hS : ∀ j, IsRealFormBoundedBy
        (fun h : Ambient.periodic.C1ProductSpace s W =>
          (cutoffData s (K j) (β j) (hβ j)).truncatedFunctional (components h))
        ((4 * ((cutoffData s (K j) (β j) (hβ j)).faceCount : ℝ)) ^ q) := fun j =>
      (hTorus q hq).2 (cutoffData s (K j) (β j) (hβ j)) W hW hd
    have hΨ : ∀ j, IsMultilinearRealForm (Ψ j) ∧ IsBoundedMultilinear (Ψ j) := fun j =>
      ⟨(hS j).2.1, isBoundedMultilinear_re_of_bound (hS j)⟩
    exact ⟨hΨ, fun hc => (hConv s .periodic q hq W hW hd).2 𝒥 Ψ h𝒥 (fun j => (hΨ j).1)
      (fun j => (hΨ j).2) hc⟩
  · intro 𝒥 D h𝒥 hL ht Ψ
    have hS : ∀ j, IsRealFormBoundedBy (periodizedForm (D j) (W := W))
        ((4 * ((D j).faceCount : ℝ)) ^ q) := fun j =>
      (hPeriod q hq s (D j) W (hL j) hW hd (ht j)).2.2.2
    have hΨ : ∀ j, IsMultilinearRealForm (Ψ j) ∧ IsBoundedMultilinear (Ψ j) := fun j =>
      ⟨(hS j).2.1, isBoundedMultilinear_re_of_bound (hS j)⟩
    exact ⟨hΨ, fun hc => (hConv s .euclidean q hq W hW hd).2 𝒥 Ψ h𝒥 (fun j => (hΨ j).1)
      (fun j => (hΨ j).2) hc⟩
end YangMills.Construction.LimitSpaces
end
