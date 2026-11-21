import YangMills.Construction.InfiniteLattice.EquivalentFormsOfTheGibbsProperty
import YangMills.Construction.InfiniteLattice.PositivityAtAMirrorExtendsFromContinuousLocalObservablesProof
import YangMills.Construction.InfiniteLattice.RulesOfTheGibbsKernelOfTheUnitLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice
open MeasureTheory
open YangMills.Construction.GibbsAtFixedSpacing YangMills.Construction.InfiniteLattice.GibbsEquivalences
private theorem regionSigma_le_complementSigma {𝓛 W : Finset (Link (1 : ℝ))} (S : Set AmbientSpace)
    (h𝓛 : (𝓛 : Set (Link (1 : ℝ))) = positivePart W) (hS : ∀ b ∈ W, ¬ b.IsWithin S) :
    (regionSigma S : MeasurableSpace (GaugeField (1 : ℝ))) ≤ complementSigma 𝓛 := by
  have key : ∀ b : Link (1 : ℝ), b.IsWithin S → b ∈ positiveLinkSet 1 →
      b ∈ complementLinks 𝓛 := by
    intro b hb hp
    refine ⟨hp, fun hm => ?_⟩
    have hm' : b ∈ positivePart W := h𝓛 ▸ hm
    rcases hm'.2 with hw | ⟨c, hc, rfl⟩
    · exact hS b hw hb
    · exact hS c hc ⟨hb.2, hb.1⟩
  refine iSup₂_le fun b hb => ?_
  have hb' : b.IsWithin S := (mem_linksWithin_iff_isWithin b S).1 hb
  rcases mem_positiveLinks_or_opposite_mem b with hp | hp
  · exact le_iSup₂_of_le (f := fun b (_ : b ∈ complementLinks 𝓛) =>
      MeasurableSpace.comap (fun U : GaugeField (1 : ℝ) => U b) inferInstance)
      b (key b hb' hp) le_rfl
  · have hr : b.opposite ∈ complementLinks 𝓛 := key _ ⟨hb'.2, hb'.1⟩ hp
    have hle : MeasurableSpace.comap (fun U : GaugeField (1 : ℝ) => U b.opposite) inferInstance
        ≤ complementSigma 𝓛 :=
      le_iSup₂_of_le (f := fun b (_ : b ∈ complementLinks 𝓛) =>
        MeasurableSpace.comap (fun U : GaugeField (1 : ℝ) => U b) inferInstance)
        b.opposite hr le_rfl
    have hm : Measurable[complementSigma 𝓛] (fun U : GaugeField (1 : ℝ) => U b.opposite) :=
      Measurable.mono (comap_measurable _) hle le_rfl
    have hm₂ : Measurable[complementSigma 𝓛] (fun U : GaugeField (1 : ℝ) => U b) := by
      have he : (fun U : GaugeField (1 : ℝ) => U b) = fun U => (U b.opposite)⁻¹ := by
        funext U
        rw [U.2 b, inv_inv]
      rw [he]
      exact continuous_inv.measurable.comp hm
    exact hm₂.comap_le
private theorem isBoundedObservable_mul {A B : GaugeField (1 : ℝ) → ℂ}
    (hA : IsBoundedObservable A) (hB : IsBoundedObservable B) :
    IsBoundedObservable (A * B) := by apply _root_.YangMills.Construction.InfiniteLattice.ReflectionPositivityExtension.isBoundedObservable_mul <;> assumption
private theorem integrable_of_isBoundedObservable {A : GaugeField (1 : ℝ) → ℂ}
    (hA : IsBoundedObservable A) (m : Measure (GaugeField (1 : ℝ))) [IsProbabilityMeasure m] :
    Integrable A m := by
  obtain ⟨mA, C, hC⟩ := hA
  exact Integrable.of_bound mA.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
theorem unitGibbsKernelRules_of_gibbsEquivalence (hE : GibbsEquivalenceStatement) :
    UnitGibbsKernelRules := by
  intro β hβ
  have h1 : (0 : ℝ) < 1 := one_pos
  obtain ⟨hAgree, hProps, hStates, -⟩ := hE 1 β h1 hβ
  refine ⟨fun W h F hF => ?_, fun ν hν => ?_⟩
  · obtain ⟨𝓛, h𝓛, hset, -, hker⟩ := hAgree W h
    have hk : ∀ G : GaugeField (1 : ℝ) → ℂ, IsBoundedObservable G →
        gibbsKernelUnit β W h G = specKernel h1 β 𝓛 h𝓛 G := fun G hG => hker G hG
    obtain ⟨hp₁, hp₂, hp₃, -⟩ := hProps 𝓛 h𝓛
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [hk F hF]
      exact (hp₁ F hF).1
    · intro G hG c d
      have hcF : IsBoundedObservable (c • F) := hF.const_smul c
      have hdG : IsBoundedObservable (d • G) := hG.const_smul d
      rw [hk _ (hcF.add hdG), hk F hF, hk G hG]
      funext U
      obtain ⟨hprob, hint⟩ := hp₂ U
      rw [(hint _ (hcF.add hdG)).1, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, (hint F hF).1,
        (hint G hG).1]
      have iF := integrable_of_isBoundedObservable hF (specImage h1 β 𝓛 h𝓛 U)
      have iG := integrable_of_isBoundedObservable hG (specImage h1 β 𝓛 h𝓛 U)
      simp only [Pi.add_apply, Pi.smul_apply]
      rw [integral_add (f := fun x => c • F x) (g := fun x => d • G x) (iF.smul c) (iG.smul d),
        integral_smul, integral_smul]
    · rw [hk F hF]
      exact (hp₁ F hF).2.2
    · intro S hS H hH
      have hHF : IsBoundedObservable (H * F) := isBoundedObservable_mul hH.1 hF
      have hmeas : Measurable[complementSigma 𝓛] H :=
        hH.2.mono (regionSigma_le_complementSigma S hset hS) le_rfl
      rw [hk _ hHF, hk F hF]
      exact hp₃ F H hF hH.1 hmeas
  · obtain ⟨hT, hG⟩ := hStates ν hν
    have hiff : IsGibbs β ν ↔ KernelInvariant h1 β ν := by
      constructor
      · intro g
        exact (hG.1 g).2.2.2
      · intro k
        exact hG.2 ⟨(hT.out 3 0).1 k, (hT.out 3 1).1 k, (hT.out 3 2).1 k, k⟩
    rw [hiff]
    constructor
    · intro k W' h' F' hF'
      obtain ⟨𝓛, h𝓛, -, -, hker⟩ := hAgree W' h'
      have hk : gibbsKernelUnit β W' h' F' = specKernel h1 β 𝓛 h𝓛 F' :=
        hker F' hF'.1
      rw [hk]
      exact k 𝓛 h𝓛 F' hF'
    · intro k 𝓛 h𝓛 F hF
      exact k 𝓛 (hasNoOppositePairs_of_subset_positiveLinks h1 h𝓛) F hF
end YangMills.Construction.InfiniteLattice
