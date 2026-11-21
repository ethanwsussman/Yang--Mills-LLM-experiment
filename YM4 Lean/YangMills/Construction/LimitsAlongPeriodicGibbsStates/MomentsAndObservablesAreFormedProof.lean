import YangMills.Construction.Continuum.NormsBallsDistancesAndSupportsInFourSpace
import YangMills.Construction.InfiniteLattice.PeriodisationAndThreeIdentitiesOfTheCoveringProof
import YangMills.Construction.LimitsAlongPeriodicGibbsStates.MomentsAndObservablesAreFormed
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.PeriodicGibbsLimits
namespace ObservablesAndMomentsDefined
open InfiniteLattice FieldsAtSpacing
open CutoffLimits.CenteredMomentsAndVolumeFirst
variable {a : ℝ}
theorem hasFiniteFaceSum_of_hasCompactSupport (hP : FaceFunctionProperties a) {E : Type*}
    [AddCommMonoid E] [Module ℝ E] [TopologicalSpace E] {f : AmbientSpace → E}
    (hc : HasCompactSupport f) (U : GaugeField a) : HasFiniteFaceSum f U := by
  refine (hP.2.1 _ hc.isCompact.isBounded).subset fun p hp => ?_
  refine subset_tsupport f fun h0 => hp ?_
  show faceEnergy U p • f p.center = 0
  rw [h0, smul_zero]
theorem isBoundedObservable_of_mem (ha : 0 < a) (hR : LinkFunctionsStatement)
    {F : GaugeField a → ℂ} (hF : F ∈ continuousFiniteLinkFunctions a) :
    IsBoundedObservable F := by apply _root_.YangMills.Construction.PeriodizationIdentities.isBoundedObservable_of_mem <;> assumption
theorem smearedEnergy_ofReal (hP : FaceFunctionProperties a) {f : AmbientSpace → ℝ}
    (hc : HasCompactSupport f) (U : GaugeField a) :
    ((smearedEnergy f U : ℝ) : ℂ) = smearedEnergy (fun x => (f x : ℂ)) U := by apply _root_.YangMills.Construction.PeriodizationIdentities.smearedEnergy_ofReal <;> assumption
theorem isBoundedRealRV_smearedEnergy (ha : 0 < a) (hR : LinkFunctionsStatement)
    {f : AmbientSpace → ℝ} (hf : IsBoundedBorelCompactlySupported f) :
    Probability.IsBoundedRealRV (smearedEnergy f : GaugeField a → ℝ) := by
  obtain ⟨hm, ⟨C, hC⟩, hc⟩ := hf
  have hP := (hR a ha ∅ (Set.empty_subset _)).2.2.2.2.2
  have hv : IsBoundedBorelCompactlySupported (fun x => (f x : ℂ)) :=
    ⟨Complex.measurable_ofReal.comp hm, ⟨C, fun x => by simpa using hC x⟩,
      hc.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)⟩
  obtain ⟨hO, C', hC'⟩ := isBoundedObservable_of_mem ha hR (hP.2.2.1 _ hv).2.1
  have he : ∀ U : GaugeField a, smearedEnergy f U =
      (smearedEnergy (fun x => (f x : ℂ)) U : ℂ).re := by
    intro U
    rw [← smearedEnergy_ofReal hP hc, Complex.ofReal_re]
  refine ⟨?_, C', fun U => ?_⟩
  · have e : (smearedEnergy f : GaugeField a → ℝ) = fun U =>
        (smearedEnergy (fun x => (f x : ℂ)) U : ℂ).re := funext he
    rw [e]
    exact Complex.measurable_re.comp hO
  · rw [he]
    exact (Complex.abs_re_le_norm _).trans (hC' U)
theorem isBoundedBorelCompactlySupported_re {f : AmbientSpace → ℂ}
    (hf : IsBoundedBorelCompactlySupported f) :
    IsBoundedBorelCompactlySupported fun x => (f x).re := by
  obtain ⟨hm, ⟨C, hC⟩, hc⟩ := hf
  exact ⟨Complex.measurable_re.comp hm, ⟨C, fun x => (Complex.abs_re_le_norm _).trans (hC x)⟩,
    hc.comp_left (g := Complex.re) (by simp)⟩
theorem isBoundedBorelCompactlySupported_im {f : AmbientSpace → ℂ}
    (hf : IsBoundedBorelCompactlySupported f) :
    IsBoundedBorelCompactlySupported fun x => (f x).im := by
  obtain ⟨hm, ⟨C, hC⟩, hc⟩ := hf
  exact ⟨Complex.measurable_im.comp hm, ⟨C, fun x => (Complex.abs_im_le_norm _).trans (hC x)⟩,
    hc.comp_left (g := Complex.im) (by simp)⟩
theorem isBoundedObservable_complexObservable (ha : 0 < a) (hR : LinkFunctionsStatement)
    {f : AmbientSpace → ℂ} (hf : IsBoundedBorelCompactlySupported f) :
    IsBoundedObservable (complexObservable f : GaugeField a → ℂ) := by
  obtain ⟨m₁, C₁, h₁⟩ := isBoundedRealRV_smearedEnergy (a := a) ha hR
    (isBoundedBorelCompactlySupported_re hf)
  obtain ⟨m₂, C₂, h₂⟩ := isBoundedRealRV_smearedEnergy (a := a) ha hR
    (isBoundedBorelCompactlySupported_im hf)
  refine ⟨(Complex.measurable_ofReal.comp m₁).add
    (measurable_const.mul (Complex.measurable_ofReal.comp m₂)), C₁ + C₂, fun U => ?_⟩
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · simpa using h₁ U
  · simpa using h₂ U
theorem isBoundedBorelCompactlySupported_of_mem {X : EuclideanFunctionals.FnList}
    (hX : X ∈ EuclideanFunctionals.sepAll) {f : AmbientSpace → ℝ} (hf : f ∈ X) :
    IsBoundedBorelCompactlySupported f := by
  have h := (EuclideanFunctionals.isSeparatedList_of_mem_sepAll hX).1 f hf
  rw [← FourSpace.C1c_eq_compactC1 EuclideanFunctionals.defaultMirrorData] at h
  obtain ⟨h₁, h₂⟩ := h
  have hc : Continuous f := ContDiff.continuous h₁
  have hs : HasCompactSupport f := h₂
  exact ⟨hc.measurable, hc.bounded_above_of_compact_support hs, hs⟩
theorem centeredMomentIntegrable_of_prob (ha : 0 < a) (hR : LinkFunctionsStatement)
    (ρ ν : Measure (GaugeField a)) [IsProbabilityMeasure ρ] [IsProbabilityMeasure ν]
    {X : EuclideanFunctionals.FnList} (hX : X ∈ EuclideanFunctionals.sepAll) :
    CenteredMomentIntegrable ρ ν X := by
  have hb : ∀ i, Probability.IsBoundedRealRV
      (smearedEnergy (X.get i) : GaugeField a → ℝ) := fun i =>
    isBoundedRealRV_smearedEnergy ha hR
      (isBoundedBorelCompactlySupported_of_mem hX (List.get_mem X i))
  choose C hC using fun i => (hb i).bounded
  refine ⟨fun i => ?_, ?_⟩
  · exact Integrable.of_bound (Complex.measurable_ofReal.comp (hb i).measurable).aestronglyMeasurable
      (C i) (ae_of_all _ fun U => by simpa using hC i U)
  · have hm : Measurable (centeredProduct ν X.get) :=
      Finset.measurable_prod _ fun i _ =>
        (Complex.measurable_ofReal.comp (hb i).measurable).sub measurable_const
    refine Integrable.of_bound hm.aestronglyMeasurable
      (∏ i, (C i + ‖Probability.complexExpectation ν fun V =>
        ((smearedEnergy (X.get i) V : ℝ) : ℂ)‖)) (ae_of_all _ fun U => ?_)
    show ‖∏ i, (((smearedEnergy (X.get i) U : ℝ) : ℂ) - _)‖ ≤ _
    rw [norm_prod]
    refine Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_
    refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
    simpa using hC i U
theorem meshSize_pos {L : ℕ} (hL : 13 ≤ L) (K : ℤ) : 0 < PeriodicLattice.meshSize L K := by
  have h : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  exact zpow_pos h _
end ObservablesAndMomentsDefined
open ObservablesAndMomentsDefined in
theorem ObservablesAndMomentsDefined.holds
    (hR : FieldsAtSpacing.LinkFunctionsStatement) :
    ObservablesAndMomentsDefined.Statement := by
  refine ⟨fun a ha => ⟨fun f hf => ?_, fun f hf => ?_⟩, ?_, ?_⟩
  · have hP := (hR a ha ∅ (Set.empty_subset _)).2.2.2.2.2
    exact ⟨hasFiniteFaceSum_of_hasCompactSupport hP hf.2.2, isBoundedRealRV_smearedEnergy ha hR hf⟩
  · have hP := (hR a ha ∅ (Set.empty_subset _)).2.2.2.2.2
    exact ⟨hasFiniteFaceSum_of_hasCompactSupport hP hf.2.2,
      isBoundedObservable_of_mem ha hR (hP.2.2.1 f hf).2.1,
      isBoundedObservable_complexObservable ha hR hf⟩
  · intro D Q k ρ ν hρ hν X hX
    have h₁ : InfiniteLattice.IsPeriodicGibbs _ ρ := hρ
    have h₂ : InfiniteLattice.IsPeriodicGibbs _ ν := hν
    have := h₁.1.1
    have := h₂.1.1
    exact centeredMomentIntegrable_of_prob (meshSize_pos D.admissible.2 _) hR ρ ν hX
  · intro D g Q k ρ ν hρ hν X hX
    have h₁ : InfiniteLattice.IsPeriodicGibbs _ ρ := hρ
    have h₂ : InfiniteLattice.IsPeriodicGibbs _ ν := hν
    have := h₁.1.1
    have := h₂.1.1
    exact centeredMomentIntegrable_of_prob (meshSize_pos D.admissible.factor_admissible.2 _) hR ρ ν hX
end YangMills.Construction.PeriodicGibbsLimits
end
