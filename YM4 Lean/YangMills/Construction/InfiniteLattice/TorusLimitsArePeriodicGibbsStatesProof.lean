import YangMills.Construction.InfiniteLattice.SpaceOfTheConfigurationsOnALatticeAndItsObservablesProof
import YangMills.Construction.InfiniteLattice.EquivalentFormsOfTheGibbsProperty
import YangMills.Construction.InfiniteLattice.PeriodicExtensionInAWindow
import YangMills.Construction.InfiniteLattice.PropertiesOfTheWilsonKernelOnObservablesProof
import YangMills.Construction.InfiniteLattice.StatesDeterminedByContinuousLocalFunctions
import YangMills.Construction.InfiniteLattice.TorusLimitsArePeriodicGibbsStates
import YangMills.Construction.InfiniteLattice.WindowDensitiesAndStandardWindows
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.InfiniteLattice.PeriodicGibbsOfTorusLimits
open YangMills.Construction.GibbsAtFixedSpacing
variable {a : ℝ}
theorem specKernel_eq_kernelOperator (ha : 0 < a) (β : ℝ) (𝓛 : Finset (Link a))
    (h𝓛 : (𝓛 : Set (Link a)) ⊆ positiveLinkSet a) (F : GaugeField a → ℂ) :
    GibbsEquivalences.specKernel ha β 𝓛 h𝓛 F =
      WilsonOperator.kernelOperator ha β h𝓛 F := by
  funext U
  have hs : ∀ V : LinkVariables (𝓛 : Set (Link a)),
      overwriteLinks (hasNoOppositePairs_of_subset_positiveLinks ha h𝓛) V U =
        WilsonOperator.splice ha h𝓛 V U := fun V => by
    refine WilsonOperator.eq_splice ha h𝓛 V U _ (fun e => ?_) (fun e he => ?_)
    · exact overwriteLinks_apply_of_mem (hasNoOppositePairs_of_subset_positiveLinks ha h𝓛) _ U
        ⟨e.1, e.2⟩
    · exact overwriteLinks_apply_of_not_mem (hasNoOppositePairs_of_subset_positiveLinks ha h𝓛) _ U
        he.2 (fun hr => opposite_notMem_positiveLinks ha he.1 (h𝓛 hr))
  have hp : plaquettesTouching 𝓛 = facesTouching 𝓛 := by
    ext p
    rw [mem_plaquettesTouching_iff ha]
    constructor
    · rintro ⟨e, he, h | h⟩
      · exact ⟨e, he, h⟩
      · exact absurd (h𝓛 h) (opposite_notMem_positiveLinks ha
          (WilsonOperator.mem_positiveLinks_of_mem_edgeList p he))
    · rintro ⟨e, he, h⟩
      exact ⟨e, he, Or.inl h⟩
  have hw : ∀ W : GaugeField a, Real.exp (-wilsonLinkEnergy β 𝓛 W) =
      WilsonOperator.localWeight β 𝓛 W := fun W => by
    simp only [wilsonLinkEnergy, WilsonOperator.localWeight, hp, neg_mul]
  simp only [GibbsEquivalences.specKernel, wilsonLinkKernel, linkKernel, hw, hs]
  unfold WilsonOperator.kernelOperator WilsonOperator.localPartition
  rw [div_eq_inv_mul]
  rfl
theorem isBoundedObservable_of_continuous (ha : 0 < a) {F : GaugeField a → ℂ}
    (hF : Continuous F) : IsBoundedObservable F := by apply _root_.YangMills.Construction.InfiniteLattice.WilsonOperatorPropertiesProof.isBoundedObservable_of_continuous <;> assumption
theorem dependsOnlyOnLinks_of_measurable {S : Set (Link a)} {F : GaugeField a → ℂ}
    (hF : Measurable[linkSigma S] F) : DependsOnlyOnLinks S F := by apply _root_.YangMills.Construction.InfiniteLattice.ConfigurationSpace.eq_of_measurable_of_restrict_eq <;> assumption
theorem mem_continuousCylinderFunctions_of_mem {F : GaugeField a → ℂ}
    (hF : F ∈ continuousLocal a) : F ∈ continuousCylinderFunctions a := by
  obtain ⟨hc, -, S, hS, hm⟩ := hF
  obtain ⟨R, hR⟩ := hS.exists_norm_le
  refine mem_continuousCylinderFunctions_iff.2
    ⟨hc, linksWithin S, ?_, dependsOnlyOnLinks_of_measurable hm⟩
  refine (linksWithin_supNormVec_le_finite a R).subset fun e he => ?_
  have key : ∀ x ∈ S, TorusMetric.supNormVec x ≤ R := fun x hx =>
    Finset.sup'_le _ _ fun μ _ => (norm_le_pi_norm x μ).trans (hR x hx)
  exact ⟨key _ he.1, key _ he.2⟩
theorem eventually_lt_torusSide {L : ℕ} (hL : 13 ≤ L) {n : ℕ → ℕ}
    (hn : StrictMono fun i => PeriodicLattice.torusSide L (n i)) (w : ℝ) :
    ∀ᶠ i in atTop, w < PeriodicLattice.torusSide L (n i) := by
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (by omega : 1 < L)
  have hmono : StrictMono n := by
    intro i j hij
    by_contra hle
    have hji : PeriodicLattice.torusSide L (n j) ≤ PeriodicLattice.torusSide L (n i) := by
      unfold PeriodicLattice.torusSide
      have := pow_le_pow_right₀ hL1.le (not_lt.1 hle)
      linarith
    exact absurd (hn hij) (not_lt.2 hji)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt w hL1
  filter_upwards [eventually_ge_atTop k] with i hi
  have hpow : (L : ℝ) ^ k ≤ (L : ℝ) ^ n i := pow_le_pow_right₀ hL1.le (hi.trans hmono.le_apply)
  have hpos : (0 : ℝ) < (L : ℝ) ^ n i := by positivity
  unfold PeriodicLattice.torusSide
  linarith
theorem torusLimitsSubsetPeriodicGibbs_holds
    (hStates : CylinderFunctionsDetermineStates.Statement)
    (hWindow : PeriodicLift.Statement)
    (hForms : GibbsEquivalences.GibbsEquivalenceStatement) :
    TorusLimitsSubsetPeriodicGibbs := by
  intro s β hβ ν hν
  obtain ⟨hprob, n, hpos, hside, hlim⟩ := hν
  have ha := PeriodicLift.meshSize_pos s
  let t : ℕ → Conventions.StandingParameters := fun i =>
    ⟨s.L, s.isAdmissible, s.K, ⟨n i, hpos i⟩⟩
  have hinv : ∀ (i : ℕ) (v : LatticePoint (PeriodicLattice.meshSize s.L ((s.K : ℕ) : ℤ))),
      IsSymmetricUnder (liftedWilsonMeasure s.L (n i) s.K β) (shift v) :=
    fun i v => (hWindow (t i) β hβ).2.1 v
  have hperiodic : IsPeriodicMeasure ν := by
    refine ⟨⊤, inferInstance, fun v _ => ?_⟩
    obtain ⟨hcont, -, hstate⟩ :=
      (hStates s.L s.K s.isAdmissible.1 s.isAdmissible.2 s.K.pos).2.1 (shift v)
    refine hstate ⟨ν, hprob⟩ fun F hF => ?_
    have hT := hlim _ (hcont F hF.1)
    have hI := hlim F hF.1
    have he : (fun i => ∫ U, (shift v).actOn F U
        ∂liftedWilsonMeasure s.L (n i) s.K β) =
        fun i => ∫ U, F U ∂liftedWilsonMeasure s.L (n i) s.K β :=
      funext fun i => hinv i v F (isBoundedObservable_of_continuous ha hF.1)
    rw [he] at hT
    exact tendsto_nhds_unique hT hI
  have hkeep : GibbsEquivalences.KernelInvariant ha β ν := by
    intro 𝓛 h𝓛 F hF
    have hprop := (hForms _ β ha hβ).2.1 𝓛 h𝓛
    have hG := hprop.2.2.2 F hF
    obtain ⟨-, W, hWfin, hWpos, hFW⟩ := mem_continuousCylinderFunctions_of_mem ⟨hF.2.2, hF.1, hF.2.1⟩
    classical
    let S : Finset (Link (PeriodicLattice.meshSize s.L ((s.K : ℕ) : ℤ))) :=
      hWfin.toFinset ∪ (WilsonOperator.thickenedLinks_finite 𝓛).toFinset
    have hSpos : (S : Set (Link (PeriodicLattice.meshSize s.L ((s.K : ℕ) : ℤ)))) ⊆
        positiveLinkSet (PeriodicLattice.meshSize s.L ((s.K : ℕ) : ℤ)) := by
      intro e he
      rcases Finset.mem_union.1 he with h | h
      · exact hWpos (hWfin.mem_toFinset.1 h)
      · exact WilsonOperator.thickenedLinks_subset h𝓛
          ((WilsonOperator.thickenedLinks_finite 𝓛).mem_toFinset.1 h)
    have hplus : WilsonOperator.thickenedLinks 𝓛 ⊆
        (S : Set (Link (PeriodicLattice.meshSize s.L ((s.K : ℕ) : ℤ)))) := fun e he =>
      Finset.mem_union_right _ ((WilsonOperator.thickenedLinks_finite 𝓛).mem_toFinset.2 he)
    have h𝓛S : (𝓛 : Set (Link (PeriodicLattice.meshSize s.L ((s.K : ℕ) : ℤ)))) ⊆
        (S : Set (Link (PeriodicLattice.meshSize s.L ((s.K : ℕ) : ℤ)))) :=
      fun e he => hplus (Or.inl he)
    have hFS : DependsOnlyOnLinks
        (S : Set (Link (PeriodicLattice.meshSize s.L ((s.K : ℕ) : ℤ)))) F := by
      intro U V h
      refine hFW U V (funext fun e => ?_)
      exact congrFun h ⟨e.1, Finset.mem_union_left _ (hWfin.mem_toFinset.2 e.2)⟩
    have hev : ∀ᶠ i in atTop,
        ∫ U, GibbsEquivalences.specKernel ha β 𝓛 h𝓛 F U
            ∂liftedWilsonMeasure s.L (n i) s.K β =
          ∫ U, F U ∂liftedWilsonMeasure s.L (n i) s.K β := by
      filter_upwards [eventually_lt_torusSide s.isAdmissible.2 hside
        (PeriodicLift.endpointDiameter S)] with i hi
      rw [specKernel_eq_kernelOperator ha β 𝓛 h𝓛 F]
      exact (hWindow (t i) β hβ).2.2 𝓛 S h𝓛S hSpos hplus hi F hF.1 hFS
    exact tendsto_nhds_unique ((hlim _ hG.2.2).congr' hev) (hlim F hF.2.2)
  obtain ⟨htfae, hgibbs⟩ := (hForms _ β ha hβ).2.2.1 ν hprob
  exact ⟨hgibbs.2 ⟨htfae.out 3 0 |>.1 hkeep, htfae.out 3 1 |>.1 hkeep,
    htfae.out 3 2 |>.1 hkeep, hkeep⟩, hperiodic⟩
end YangMills.Construction.InfiniteLattice.PeriodicGibbsOfTorusLimits
