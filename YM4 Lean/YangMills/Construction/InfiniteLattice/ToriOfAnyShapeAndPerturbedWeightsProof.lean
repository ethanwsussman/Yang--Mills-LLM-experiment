import YangMills.Construction.InfiniteLattice.ActionOfTheLatticeIsometriesOnConfigurationsAndFunctions
import YangMills.Construction.InfiniteLattice.ContinuousObservablesAndTheWilsonKernelOfACutoff
import YangMills.Construction.InfiniteLattice.CovarianceOfTheMeasuresOfATorus
import YangMills.Construction.InfiniteLattice.CumulantsArePolynomialsInTheMomentsAndWeakLimits
import YangMills.Construction.InfiniteLattice.EquilibriumEquationInAWindowThatEmbedsInATorus
import YangMills.Construction.InfiniteLattice.ObjectsAtOneSpacingAndThoseOfTheDefinitionsProof
import YangMills.Construction.InfiniteLattice.PlaquetteFunctionSeesNeitherCornerNorSense
import YangMills.Construction.InfiniteLattice.PropertiesOfTheKernelsOfBonds
import YangMills.Construction.InfiniteLattice.ReflectionFormAndTransferOperatorOfAPeriodicGibbsStateProof
import YangMills.Construction.InfiniteLattice.ReflectionPositivityInTheFullFormFromContinuousLocalFunctions
import YangMills.Construction.InfiniteLattice.TheSpaceOfConfigurationsAndTheSpaceOfMeasures
import YangMills.Construction.InfiniteLattice.ThreeFormsOfTheGibbsPropertyForBondsOfAnyOrientation
import YangMills.Construction.InfiniteLattice.ToriOfAnyShapeAndPerturbedWeights
import YangMills.Construction.InfiniteLattice.WeakLimitsInvariantFunctionsAndACriterionForErgodicity
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory Filter InfiniteLattice
open scoped Topology ComplexOrder
namespace GibbsAtFixedSpacing
namespace TiltedTori
variable {a : ℝ}
theorem tendsto_nhds_iff_tendstoWeak (ν : ℕ → BorelProb a) (μ : BorelProb a) :
    Tendsto ν atTop (𝓝 μ) ↔ BorelProb.TendstoWeak ν μ := by apply _root_.YangMills.Construction.InfiniteLattice.FixedSpacing.tendsto_iff_tendstoWeak <;> assumption
theorem exists_isSubseqWeakLimit (hc : CompactSpace (BorelProb a))
    (hm : TopologicalSpace.MetrizableSpace (BorelProb a)) (ρ : ℕ → BorelProb a) :
    ∃ ν, BorelProb.IsSubseqWeakLimit ρ ν := by
  obtain ⟨ν, ψ, hψ, hlim⟩ := CompactSpace.tendsto_subseq ρ
  refine ⟨ν, fun k => ψ (k + 1), fun i j hij => hψ (by omega), fun k => ?_, ?_⟩
  · exact (Nat.succ_le_succ (Nat.zero_le k)).trans (hψ.id_le (k + 1))
  · rw [← tendsto_nhds_iff_tendstoWeak]
    exact hlim.comp (tendsto_add_atTop_nat 1)
theorem isSubseqWeakLimit_iff_mapClusterPt (hm : TopologicalSpace.MetrizableSpace (BorelProb a))
    (ρ : ℕ → BorelProb a) (ν : BorelProb a) :
    BorelProb.IsSubseqWeakLimit ρ ν ↔ MapClusterPt ν atTop ρ := by
  constructor
  · rintro ⟨φ, hφ, -, hlim⟩
    rw [← tendsto_nhds_iff_tendstoWeak] at hlim
    exact (hlim.mapClusterPt).of_comp hφ.tendsto_atTop
  · intro h
    obtain ⟨ψ, hψ, hlim⟩ := h.tendsto_subseq
    refine ⟨fun k => ψ (k + 1), fun i j hij => hψ (by omega), fun k => ?_, ?_⟩
    · exact (Nat.succ_le_succ (Nat.zero_le k)).trans (hψ.id_le (k + 1))
    · rw [← tendsto_nhds_iff_tendstoWeak]
      exact hlim.comp (tendsto_add_atTop_nat 1)
theorem isClosed_setOf_isSubseqWeakLimit (hm : TopologicalSpace.MetrizableSpace (BorelProb a))
    (ρ : ℕ → BorelProb a) : IsClosed {ν | BorelProb.IsSubseqWeakLimit ρ ν} := by
  simp only [isSubseqWeakLimit_iff_mapClusterPt hm]
  exact isClosed_setOfPred_clusterPt
section RealValued
variable {B : Subalgebra ℂ (GaugeField a → ℂ)}
theorem isRealLocalContinuous_sub (hB : (B : Set (GaugeField a → ℂ)) = continuousLocal a)
    {f g : GaugeField a → ℝ} (hf : IsRealLocalContinuous f) (hg : IsRealLocalContinuous g) :
    IsRealLocalContinuous fun U => f U - g U := by
  unfold IsRealLocalContinuous at hf hg ⊢
  rw [← hB] at hf hg ⊢
  have h := B.sub_mem hf hg
  have e : (fun U => ((f U - g U : ℝ) : ℂ)) = (fun U => (f U : ℂ)) - fun U => (g U : ℂ) := by
    funext U
    simp
  change (fun U => ((f U - g U : ℝ) : ℂ)) ∈ B
  rw [e]
  exact h
theorem isRealLocalContinuous_const_mul (hB : (B : Set (GaugeField a → ℂ)) = continuousLocal a)
    (c : ℝ) {f : GaugeField a → ℝ} (hf : IsRealLocalContinuous f) :
    IsRealLocalContinuous fun U => c * f U := by
  unfold IsRealLocalContinuous at hf ⊢
  rw [← hB] at hf ⊢
  have h := B.smul_mem hf (c : ℂ)
  have e : (fun U => ((c * f U : ℝ) : ℂ)) = (c : ℂ) • fun U => (f U : ℂ) := by
    funext U
    simp
  change (fun U => ((c * f U : ℝ) : ℂ)) ∈ B
  rw [e]
  exact h
theorem isRealLocalContinuous_sum (hB : (B : Set (GaugeField a → ℂ)) = continuousLocal a)
    {ι : Type*} (s : Finset ι) (f : ι → GaugeField a → ℝ)
    (hf : ∀ i ∈ s, IsRealLocalContinuous (f i)) :
    IsRealLocalContinuous fun U => ∑ i ∈ s, f i U := by
  classical
  unfold IsRealLocalContinuous at hf ⊢
  rw [← hB] at ⊢
  have h : (∑ i ∈ s, fun U => ((f i U : ℝ) : ℂ)) ∈ B :=
    B.sum_mem fun i hi => by
      have := hf i hi
      rw [← hB] at this
      exact this
  have e : (fun U => ((∑ i ∈ s, f i U : ℝ) : ℂ)) = ∑ i ∈ s, fun U => ((f i U : ℝ) : ℂ) := by
    funext U
    simp
  change (fun U => ((∑ i ∈ s, f i U : ℝ) : ℂ)) ∈ B
  rw [e]
  exact h
theorem isRealLocalContinuous_finsum_mem (hB : (B : Set (GaugeField a → ℂ)) = continuousLocal a)
    {ι : Type*} {s : Set ι} (hs : s.Finite) (f : ι → GaugeField a → ℝ)
    (hf : ∀ i ∈ s, IsRealLocalContinuous (f i)) :
    IsRealLocalContinuous fun U => ∑ᶠ i ∈ s, f i U := by
  have h := isRealLocalContinuous_sum hB hs.toFinset f fun i hi => hf i (hs.mem_toFinset.1 hi)
  convert h using 2 with U
  exact finsum_mem_eq_finite_toFinset_sum _ hs
end RealValued
theorem dependsOnLink_ofReal (ha : 0 < a) (F : GaugeField a → ℝ) (b : Link a) :
    DependsOnLink ha (fun U => (F U : ℂ)) b ↔ DependsOnLink ha F b := by
  unfold DependsOnLink IsIndependentOfLinks
  simp only [Complex.ofReal_inj]
theorem linkSupport_ofReal (ha : 0 < a) (F : GaugeField a → ℝ) :
    linkSupport ha (fun U => (F U : ℂ)) = linkSupport ha F := by
  ext b
  simp only [linkSupport, Set.mem_ofPred_eq, dependsOnLink_ofReal]
theorem linkSupport_finite (ha : 0 < a)
    (hfac : LinkFunctions.LocalObservablesSupports ha)
    {F : GaugeField a → ℂ} (hF : F ∈ continuousLocal a) :
    (linkSupport ha F).Finite := by
  obtain ⟨-, -, hl, hs⟩ := hfac
  obtain ⟨W, hWf, hWp, hWF⟩ := (hl F hF.2.1).1 hF.2.2
  exact hWf.subset (hs F W hF.2.1 hWf hWp hWF).1
theorem supportIndices_finite (ha : 0 < a)
    (hfac : LinkFunctions.LocalObservablesSupports ha)
    (hmove : SymmetriesTransportLinksAndSupports a ha) (A : SingleGeneratorArray a)
    (𝓛 : Finset (Link a)) : (A.supportIndices ha 𝓛).Finite := by
  have hS : (linkSupport ha A.gen).Finite := by
    rw [← linkSupport_ofReal]
    exact linkSupport_finite ha hfac A.gen_mem
  have hT : (Set.image2 (fun (b c : Link a) => b.initial - c.initial) (𝓛 : Set (Link a))
        (linkSupport ha A.gen) ∪
      Set.image2 (fun (b c : Link a) => b.initial - c.terminal) (𝓛 : Set (Link a))
        (linkSupport ha A.gen)).Finite :=
    (𝓛.finite_toSet.image2 _ hS).union (𝓛.finite_toSet.image2 _ hS)
  refine (hT.preimage Subtype.val_injective.injOn).subset ?_
  rintro v ⟨b, hb, hread⟩
  obtain ⟨hbij, -, -, hreads⟩ := hmove.1 (shift (v : LatticePoint a))
  obtain ⟨c, rfl⟩ := hbij.2 b
  have hc : DependsOnLink ha A.gen c := (hreads ℝ A.gen c).2 hread
  have hinit : ((shift (v : LatticePoint a)).linkMap c).initial = c.initial + (v : LatticePoint a) :=
    Subtype.ext rfl
  by_cases hp : c.IsPositivelyOriented
  · refine Or.inl ⟨_, hb, c, ⟨mem_positiveLinks_iff.2 hp, hc⟩, ?_⟩
    simp only [hinit]
    abel
  · refine Or.inr ⟨_, hb, c.opposite,
      ⟨mem_positiveLinks_iff.2 (PeriodSublattice.isPositivelyOriented_opposite_of_not hp),
        hc.opposite ha⟩, ?_⟩
    simp only [hinit, Link.opposite]
    abel
open Classical in
def orientPositive (𝓛 : Finset (Link a)) : Finset (Link a) :=
  𝓛.image fun b => if b.IsPositivelyOriented then b else b.opposite
theorem orientPositive_subset (𝓛 : Finset (Link a)) :
    (orientPositive 𝓛 : Set (Link a)) ⊆ positiveLinkSet a := by
  classical
  intro c hc
  obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hc)
  by_cases hp : b.IsPositivelyOriented
  · simpa [hp] using mem_positiveLinks_iff.2 hp
  · simpa [hp] using
      mem_positiveLinks_iff.2 (PeriodSublattice.isPositivelyOriented_opposite_of_not hp)
theorem isPartialReversal_orientPositive (𝓛 : Finset (Link a)) :
    IsPartialReversal (orientPositive 𝓛) 𝓛 := by
  classical
  refine ⟨{b | b ∈ 𝓛 ∧ ¬b.IsPositivelyOriented}, fun b hb => hb.1, ?_⟩
  ext c
  simp only [orientPositive, Finset.coe_image, Set.mem_image, Finset.mem_coe, Set.mem_union,
    Set.mem_sdiff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨b, hb, rfl⟩
    by_cases hp : b.IsPositivelyOriented
    · exact Or.inl ⟨by simpa [hp] using hb, fun h => h.2 (by simp [hp])⟩
    · exact Or.inr ⟨b, ⟨hb, hp⟩, by simp [hp]⟩
  · rintro (⟨hc, hn⟩ | ⟨b, ⟨hb, hp⟩, rfl⟩)
    · have hp : c.IsPositivelyOriented := by
        by_contra hp
        exact hn ⟨hc, hp⟩
      exact ⟨c, hc, by simp [hp]⟩
    · exact ⟨b, hb, by simp [hp]⟩
theorem supportIndices_orientPositive (ha : 0 < a) (A : SingleGeneratorArray a)
    (𝓛 : Finset (Link a)) : A.supportIndices ha (orientPositive 𝓛) = A.supportIndices ha 𝓛 := by
  classical
  ext v
  simp only [SingleGeneratorArray.supportIndices, Set.mem_ofPred_eq, orientPositive,
    Finset.mem_image]
  constructor
  · rintro ⟨_, ⟨b, hb, rfl⟩, hr⟩
    refine ⟨b, hb, ?_⟩
    by_cases hp : b.IsPositivelyOriented
    · simpa [hp] using hr
    · have h2 := DependsOnLink.opposite ha
        (by simpa [hp] using hr : DependsOnLink ha (A.translate v) b.opposite)
      simpa [Link.opposite_opposite] using h2
  · rintro ⟨b, hb, hr⟩
    refine ⟨_, ⟨b, hb, rfl⟩, ?_⟩
    by_cases hp : b.IsPositivelyOriented
    · simpa [hp] using hr
    · simpa [hp] using DependsOnLink.opposite ha hr
open SpacesOfFieldsAndMeasures LinkFunctions in
structure Inputs (a : ℝ) (ha : 0 < a) : Prop where
  fields : GaugeFieldsCompactMetrizable a
  dense : LocalFnsDenseStarSubalgebra a
  probs : ProbCompactMetrizable a
  kernels : LinkKernelProperties
  factorization : LinkMeasurableFactorization ha
  supports : LocalObservablesSupports ha
  transport : SymmetriesTransportLinksAndSupports a ha
  faces : ∀ p : ElementaryPlaquette a, FaceEnergyIsLocalInEdges p
  symmetry : ∀ r : LatticeSymmetry a, PreservesNormAndFunctionSpaces r
variable {ha : 0 < a}
theorem isRealLocalContinuous_zero (H : Inputs a ha) :
    IsRealLocalContinuous (fun _ : GaugeField a => (0 : ℝ)) := by
  obtain ⟨-, -, hc, -⟩ := H.dense
  simpa [IsRealLocalContinuous] using hc 0
theorem plaquettesTouching_orientPositive (H : Inputs a ha) (𝓛 : Finset (Link a))
    (h : HasNoOppositePairs (𝓛 : Set (Link a))) :
    plaquettesTouching (orientPositive 𝓛) = plaquettesTouching 𝓛 := by
  obtain ⟨-, -, -, -, -, -, hg⟩ :=
    H.kernels a ha 𝓛 h _ _ (isRealLocalContinuous_zero H) (isRealLocalContinuous_zero H)
  obtain ⟨-, -, hp, -⟩ := hg _ (isPartialReversal_orientPositive 𝓛)
  exact hp
theorem plaquettesTouching_finite (H : Inputs a ha) (𝓛 : Finset (Link a))
    (h : HasNoOppositePairs (𝓛 : Set (Link a))) :
    (plaquettesTouching 𝓛).Finite := by
  rw [← plaquettesTouching_orientPositive H 𝓛 h]
  exact InfiniteLattice.CutoffStates.finite_plaquettesTouching ha (orientPositive_subset 𝓛)
theorem translate_isRealLocalContinuous (H : Inputs a ha) (A : SingleGeneratorArray a)
    (v : A.sublattice) : IsRealLocalContinuous (A.translate v) := by
  have hC := (H.symmetry (shift (v : LatticePoint a))).2.2.2
  exact show (shift (v : LatticePoint a)).actOn (fun U => (A.gen U : ℂ)) ∈ continuousLocal a from by
    rw [← hC]
    exact ⟨_, A.gen_mem, rfl⟩
theorem finsum_translate_isRealLocalContinuous (H : Inputs a ha) (A : SingleGeneratorArray a)
    (𝓛 : Finset (Link a)) :
    IsRealLocalContinuous fun U => ∑ᶠ v ∈ A.supportIndices ha 𝓛, A.translate v U := by
  obtain ⟨-, ⟨B, hB⟩, -⟩ := H.dense
  exact isRealLocalContinuous_finsum_mem hB
    (supportIndices_finite ha H.supports H.transport A 𝓛) _
    fun v _ => translate_isRealLocalContinuous H A v
theorem wilsonLinkEnergy_isRealLocalContinuous (H : Inputs a ha) (β : ℝ) (𝓛 : Finset (Link a))
    (h : HasNoOppositePairs (𝓛 : Set (Link a))) :
    IsRealLocalContinuous (wilsonLinkEnergy β 𝓛) := by
  obtain ⟨-, ⟨B, hB⟩, -⟩ := H.dense
  exact isRealLocalContinuous_const_mul hB β
    (isRealLocalContinuous_finsum_mem hB (plaquettesTouching_finite H 𝓛 h) _
      fun p _ => (H.faces p).2.1)
theorem tiltedEnergy_isRealLocalContinuous (H : Inputs a ha) (A : SingleGeneratorArray a)
    (β t : ℝ) (𝓛 : Finset (Link a)) (h : HasNoOppositePairs (𝓛 : Set (Link a))) :
    IsRealLocalContinuous (A.tiltedEnergy ha β t 𝓛) := by
  obtain ⟨-, ⟨B, hB⟩, -⟩ := H.dense
  exact isRealLocalContinuous_sub hB (wilsonLinkEnergy_isRealLocalContinuous H β 𝓛 h)
    (isRealLocalContinuous_const_mul hB t (finsum_translate_isRealLocalContinuous H A 𝓛))
theorem tiltedEnergy_orientPositive (H : Inputs a ha) (A : SingleGeneratorArray a) (β t : ℝ)
    (𝓛 : Finset (Link a)) (h : HasNoOppositePairs (𝓛 : Set (Link a))) :
    A.tiltedEnergy ha β t (orientPositive 𝓛) = A.tiltedEnergy ha β t 𝓛 := by
  funext U
  simp only [SingleGeneratorArray.tiltedEnergy, wilsonLinkEnergy,
    plaquettesTouching_orientPositive H 𝓛 h, supportIndices_orientPositive]
theorem tiltedKernel_orientPositive (H : Inputs a ha) (A : SingleGeneratorArray a) (β t : ℝ)
    (𝓛 : Finset (Link a)) (h : HasNoOppositePairs (𝓛 : Set (Link a)))
    (hPos : HasNoOppositePairs (orientPositive 𝓛 : Set (Link a)))
    {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) :
    A.tiltedKernel ha β t (orientPositive 𝓛) hPos F = A.tiltedKernel ha β t 𝓛 h F := by
  have hW := tiltedEnergy_isRealLocalContinuous H A β t 𝓛 h
  obtain ⟨-, -, -, -, -, -, hg⟩ := H.kernels a ha 𝓛 h _ _ hW hW
  obtain ⟨_, hk, -, -⟩ := hg _ (isPartialReversal_orientPositive 𝓛)
  unfold SingleGeneratorArray.tiltedKernel
  rw [tiltedEnergy_orientPositive H A β t 𝓛 h]
  exact hk F hF
theorem exists_adapted_window (H : Inputs a ha) (A : SingleGeneratorArray a) {𝓛 : Finset (Link a)}
    (hpos : (𝓛 : Set (Link a)) ⊆ positiveLinkSet a) {F : GaugeField a → ℂ}
    (hF : F ∈ continuousLocal a) :
    ∃ 𝓢 : Finset (Link a), 𝓛 ⊆ 𝓢 ∧ (𝓢 : Set (Link a)) ⊆ positiveLinkSet a ∧
      (∀ p ∈ plaquettesTouching 𝓛, edgesOf p ⊆ (𝓢 : Set (Link a))) ∧
      (∀ v ∈ A.supportIndices ha 𝓛, linkSupport ha (A.translate v) ⊆ (𝓢 : Set (Link a))) ∧
      Measurable[linkSigma (𝓢 : Set (Link a))] F := by
  have hone := hasNoOppositePairs_of_subset_positiveLinks ha hpos
  obtain ⟨W, hWf, hWp, hWF⟩ := (H.supports.2.2.1 F hF.2.1).1 hF.2.2
  have hedges : ∀ p : ElementaryPlaquette a, (edgesOf p).Finite := fun p => by
    apply Set.finite_of_ncard_ne_zero
    rw [(H.faces p).1]
    norm_num
  have hsupp : ∀ v : A.sublattice, (linkSupport ha (A.translate v)).Finite := fun v => by
    rw [← linkSupport_ofReal]
    exact linkSupport_finite ha H.supports (translate_isRealLocalContinuous H A v)
  have hfin : (((𝓛 : Set (Link a)) ∪ W) ∪ (⋃ p ∈ plaquettesTouching 𝓛, edgesOf p) ∪
      ⋃ v ∈ A.supportIndices ha 𝓛, linkSupport ha (A.translate v)).Finite :=
    ((𝓛.finite_toSet.union hWf).union
      ((plaquettesTouching_finite H 𝓛 hone).biUnion fun p _ => hedges p)).union
      ((supportIndices_finite ha H.supports H.transport A 𝓛).biUnion fun v _ => hsupp v)
  refine ⟨hfin.toFinset, fun b hb => ?_, fun b hb => ?_, fun p hp b hb => ?_,
    fun v hv b hb => ?_, ?_⟩
  · exact hfin.mem_toFinset.2 (Or.inl (Or.inl (Or.inl hb)))
  · rcases hfin.mem_toFinset.1 (Finset.mem_coe.1 hb) with ((hb | hb) | hb) | hb
    · exact hpos hb
    · exact hWp hb
    · obtain ⟨p, -, hb⟩ := Set.mem_iUnion₂.1 hb
      exact hb.1
    · obtain ⟨v, -, hb⟩ := Set.mem_iUnion₂.1 hb
      exact hb.1
  · exact Finset.mem_coe.2
      (hfin.mem_toFinset.2 (Or.inl (Or.inr (Set.mem_iUnion₂.2 ⟨p, hp, hb⟩))))
  · exact Finset.mem_coe.2 (hfin.mem_toFinset.2 (Or.inr (Set.mem_iUnion₂.2 ⟨v, hv, hb⟩)))
  · have hsub : (hfin.toFinset : Set (Link a)) ⊆ positiveLinkSet a := by
      intro b hb
      rcases hfin.mem_toFinset.1 (Finset.mem_coe.1 hb) with ((hb | hb) | hb) | hb
      · exact hpos hb
      · exact hWp hb
      · obtain ⟨p, -, hb⟩ := Set.mem_iUnion₂.1 hb
        exact hb.1
      · obtain ⟨v, -, hb⟩ := Set.mem_iUnion₂.1 hb
        exact hb.1
    have hT := (H.factorization _ hsub F hF.2.1.2).1
    have hfb : Measurable F ∧ DependsOnlyOnLinks (hfin.toFinset : Set (Link a)) F := by
      refine ⟨hF.2.1.1, fun U U' e => hWF U U' ?_⟩
      funext b
      exact congrFun e ⟨b.1, Finset.mem_coe.2
        (hfin.mem_toFinset.2 (Or.inl (Or.inl (Or.inr b.2))))⟩
    exact (hT.out 1 0).1 hfb
theorem exists_bound_linkEndpoints (𝓢 : Finset (Link a)) :
    ∃ M : ℝ, ∀ x ∈ SingleGeneratorArray.linkEndpoints 𝓢,
      ∀ y ∈ SingleGeneratorArray.linkEndpoints 𝓢,
        linfNorm ((x : AmbientSpace) - (y : AmbientSpace)) ≤ M := by
  have hfin : (SingleGeneratorArray.linkEndpoints 𝓢).Finite := by
    refine ((𝓢.finite_toSet.image Link.initial).union
      (𝓢.finite_toSet.image Link.terminal)).subset ?_
    rintro x ⟨b, hb, rfl | rfl⟩
    · exact Or.inl ⟨b, hb, rfl⟩
    · exact Or.inr ⟨b, hb, rfl⟩
  obtain ⟨M, hM⟩ := ((hfin.prod hfin).image
    fun q : LatticePoint a × LatticePoint a =>
      linfNorm ((q.1 : AmbientSpace) - (q.2 : AmbientSpace))).bddAbove
  exact ⟨M, fun x hx y hy => hM ⟨(x, y), ⟨hx, hy⟩, rfl⟩⟩
theorem integral_tiltedKernel_of_tendstoWeak (H : Inputs a ha)
    (hwin : EquilibriumInEmbeddableWindow.Statement) {β : ℝ} (hβ : 0 < β)
    (A : SingleGeneratorArray a) (t : ℝ) {Γ : ℕ → PeriodSublattice a}
    (hΓ : ∀ i, A.PeriodsWithin (Γ i))
    (hper : Tendsto (fun i => minPeriodNorm (Γ i)) atTop atTop) {ρ : ℕ → BorelProb a}
    (hρ : ∀ i, (ρ i).1 = A.liftedTiltMeasure (hΓ i) β t) {ν : BorelProb a}
    (hν : BorelProb.TendstoWeak ρ ν) (𝓛 : Finset (Link a))
    (h : HasNoOppositePairs (𝓛 : Set (Link a))) {F : GaugeField a → ℂ}
    (hF : F ∈ continuousLocal a) :
    ∫ U, A.tiltedKernel ha β t 𝓛 h F U ∂ν.1 = ∫ U, F U ∂ν.1 := by
  have hpos := orientPositive_subset 𝓛
  have hone := hasNoOppositePairs_of_subset_positiveLinks ha hpos
  rw [← tiltedKernel_orientPositive H A β t 𝓛 h hone hF.2.1]
  obtain ⟨𝓢, h𝓛, h𝓢, hedges, hsupp, hmeas⟩ := exists_adapted_window H A hpos hF
  obtain ⟨M, hM⟩ := exists_bound_linkEndpoints 𝓢
  have hW := tiltedEnergy_isRealLocalContinuous H A β t _ hone
  obtain ⟨-, -, ⟨-, hc, -⟩, -⟩ := H.kernels a ha (orientPositive 𝓛) hone _ _ hW hW
  have hKc : Continuous (A.tiltedKernel ha β t (orientPositive 𝓛) hone F) := hc F hF.2.1 hF.1
  have e1 := hν _ hKc
  have e2 := hν F hF.1
  have ev : (fun i => (ρ i).integral (A.tiltedKernel ha β t (orientPositive 𝓛) hone F))
      =ᶠ[atTop] fun i => (ρ i).integral F := by
    filter_upwards [tendsto_atTop.1 hper (M + 1)] with i hi
    have hw := hwin a ha β hβ A t (Γ i) (hΓ i) (orientPositive 𝓛) 𝓢 h𝓛 h𝓢
      ⟨hedges, hsupp, fun x hx y hy => lt_of_le_of_lt (hM x hx y hy) (by linarith)⟩
      F hF.2.1.2 hmeas
    change ∫ U, _ ∂(ρ i).1 = ∫ U, _ ∂(ρ i).1
    rw [hρ i]
    exact hw
  exact tendsto_nhds_unique (e1.congr' ev) e2
theorem continuous_of_isRealLocalContinuous {f : GaugeField a → ℝ}
    (hf : IsRealLocalContinuous f) : Continuous f := (Complex.continuous_re.comp hf.1).congr fun U => Complex.ofReal_re (f U)
theorem isProbabilityMeasure_liftedTiltMeasure (H : Inputs a ha)
    (hO : PeriodSublatticeQuotientFacts) (β t : ℝ) (A : SingleGeneratorArray a)
    {Γ : PeriodSublattice a} (h : A.PeriodsWithin Γ) :
    IsProbabilityMeasure (A.liftedTiltMeasure h β t) := by
  obtain ⟨⟨-, -, hBf, hPf, hQ⟩, ⟨hcont, -, -⟩, ⟨-, -, hper⟩⟩ := hO a ha Γ
  have hCf : Finite (A.QuotientClasses Γ) := hQ A.sublattice h
  have := Fintype.ofFinite (A.QuotientClasses Γ)
  have := Fintype.ofFinite Γ.QuotientPlaquette
  have : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  have : SecondCountableTopology Matrices.ComplexMatrix2.specialUnitary :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have hprob : IsProbabilityMeasure Γ.quotientHaar := by
    unfold PeriodSublattice.quotientHaar Matrices.ComplexMatrix2.haarPi
    infer_instance
  have hS : Continuous (A.foldedSum Γ) := by
    have e : A.foldedSum Γ =
        fun U => ∑ c, Γ.periodize (A.translate (A.classRep Γ c)) U := by
      funext U
      exact finsum_eq_sum_of_fintype _
    rw [e]
    exact continuous_finsetSum _ fun c _ =>
      hper ℝ _ (continuous_of_isRealLocalContinuous (translate_isRealLocalContinuous H A _))
  have hP : Continuous fun U : Γ.QuotientField =>
      ∑ᶠ p : Γ.QuotientPlaquette, Γ.quotientFaceEnergy U p := by
    have e : (fun U : Γ.QuotientField =>
        ∑ᶠ p : Γ.QuotientPlaquette, Γ.quotientFaceEnergy U p) =
        fun U => ∑ p, Γ.quotientFaceEnergy U p :=
      funext fun U => finsum_eq_sum_of_fintype _
    rw [e]
    exact continuous_finsetSum _ fun p _ =>
      hper ℝ _ (continuous_of_isRealLocalContinuous (H.faces _).2.1)
  have hw : Continuous (A.tiltWeight Γ β t) :=
    Real.continuous_exp.comp ((continuous_const.mul hS).sub (continuous_const.mul hP))
  have hint : Integrable (A.tiltWeight Γ β t) Γ.quotientHaar :=
    hw.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hZ : 0 < A.tiltNormalizer h β t := integral_exp_pos hint
  have hM : IsProbabilityMeasure (A.tiltMeasure h β t) := by
    constructor
    unfold SingleGeneratorArray.tiltMeasure
    rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun U => (Real.exp_pos _).le),
      smul_eq_mul]
    exact ENNReal.inv_mul_cancel (by simpa using hZ) ENNReal.ofReal_ne_top
  exact Measure.isProbabilityMeasure_map hcont.measurable.aemeasurable
theorem norm_le_supNorm {G : GaugeField a → ℂ} (hG : IsBoundedObservable G)
    (U : GaugeField a) : ‖G U‖ ≤ observableSupNorm G := by apply _root_.YangMills.Construction.LatticeConventions.TranslationReflectionProof.norm_le_supNorm <;> assumption
theorem oscillation_le_two_mul {D : GaugeField a → ℝ} {b : ℝ} (hD : ∀ U, |D U| ≤ b) :
    oscillation D ≤ 2 * b := by
  have : Nonempty (GaugeField a) := ⟨trivialField a⟩
  have h1 : ⨆ U, D U ≤ b := ciSup_le fun U => (abs_le.1 (hD U)).2
  have h2 : -b ≤ ⨅ U, D U := le_ciInf fun U => (abs_le.1 (hD U)).1
  unfold oscillation
  linarith
theorem integrable_of_isBoundedObservable (ν : Measure (GaugeField a)) [IsProbabilityMeasure ν]
    {G : GaugeField a → ℂ} (hG : IsBoundedObservable G) : Integrable G ν := by apply _root_.YangMills.Construction.InfiniteLattice.ReflectionPairingProof.integrable_of_isBoundedObservable <;> assumption
theorem integral_wilsonLinkKernel_of_tilt_tendsto_zero (H : Inputs a ha) {β : ℝ}
    (A : SingleGeneratorArray a) {s : ℕ → ℝ} {ρ : ℕ → BorelProb a} {ν : BorelProb a}
    (hs : Tendsto s atTop (𝓝 0))
    (hG : ∀ k, 1 ≤ k → A.IsTiltedGibbsState ha β (s k) (ρ k).1)
    (hν : BorelProb.TendstoWeak ρ ν) (𝓛 : Finset (Link a))
    (h : HasNoOppositePairs (𝓛 : Set (Link a))) {F : GaugeField a → ℂ}
    (hF : F ∈ continuousLocal a) :
    ∫ U, wilsonLinkKernel β 𝓛 h F U ∂ν.1 = ∫ U, F U ∂ν.1 := by
  have hW₀ := wilsonLinkEnergy_isRealLocalContinuous H β 𝓛 h
  obtain ⟨C, hC⟩ := (finsum_translate_isRealLocalContinuous H A 𝓛 (ha := ha)).2.1.2
  obtain ⟨⟨ha₁, -, -⟩, -, ⟨-, hc, -⟩, -⟩ := H.kernels a ha 𝓛 h _ _ hW₀ hW₀
  have hGobs : IsBoundedObservable (linkKernel 𝓛 h (wilsonLinkEnergy β 𝓛) F) :=
    (ha₁ F hF.2.1).2.2.2.2.1
  have hGc : Continuous (linkKernel 𝓛 h (wilsonLinkEnergy β 𝓛) F) := hc F hF.2.1 hF.1
  have e1 := hν _ hGc
  have e2 := hν F hF.1
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC (trivialField a))
  have key : ∀ k, 1 ≤ k →
      ‖(ρ k).integral (linkKernel 𝓛 h (wilsonLinkEnergy β 𝓛) F) - (ρ k).integral F‖ ≤
        observableSupNorm F * (Real.exp (2 * (|s k| * C)) - 1) := by
    intro k hk
    have hWk := tiltedEnergy_isRealLocalContinuous H A β (s k) 𝓛 h
    obtain ⟨⟨ha₂, -, -⟩, -, -, -, he, -, -⟩ := H.kernels a ha 𝓛 h _ _ hWk hW₀
    have : IsProbabilityMeasure (ρ k).1 := (ρ k).2
    have hGk := (hG k hk).2 𝓛 h F hF
    have hKobs : IsBoundedObservable (linkKernel 𝓛 h (A.tiltedEnergy ha β (s k) 𝓛) F) :=
      (ha₂ F hF.2.1).2.2.2.2.1
    have hosc : oscillation (fun U => A.tiltedEnergy ha β (s k) 𝓛 U -
        wilsonLinkEnergy β 𝓛 U) ≤ 2 * (|s k| * C) := by
      refine oscillation_le_two_mul fun U => ?_
      have e : A.tiltedEnergy ha β (s k) 𝓛 U - wilsonLinkEnergy β 𝓛 U =
          -(s k * ∑ᶠ v ∈ A.supportIndices ha 𝓛, A.translate v U) := by
        simp only [SingleGeneratorArray.tiltedEnergy]
        ring
      rw [e, abs_neg, abs_mul]
      have hCU := hC U
      rw [Complex.norm_real, Real.norm_eq_abs] at hCU
      exact mul_le_mul_of_nonneg_left hCU (abs_nonneg _)
    have hb := he F hF.2.1
    have hdiff : IsBoundedObservable fun U =>
        linkKernel 𝓛 h (A.tiltedEnergy ha β (s k) 𝓛) F U -
          linkKernel 𝓛 h (wilsonLinkEnergy β 𝓛) F U := by
      obtain ⟨m₁, C₁, h₁⟩ := hKobs
      obtain ⟨m₂, C₂, h₂⟩ := hGobs
      exact ⟨m₁.sub m₂, C₁ + C₂, fun U => (norm_sub_le _ _).trans (add_le_add (h₁ U) (h₂ U))⟩
    have hI : (ρ k).integral (linkKernel 𝓛 h (wilsonLinkEnergy β 𝓛) F) -
        (ρ k).integral F =
        -∫ U, (linkKernel 𝓛 h (A.tiltedEnergy ha β (s k) 𝓛) F U -
          linkKernel 𝓛 h (wilsonLinkEnergy β 𝓛) F U) ∂(ρ k).1 := by
      rw [integral_sub (integrable_of_isBoundedObservable _ hKobs)
        (integrable_of_isBoundedObservable _ hGobs)]
      change (∫ U, _ ∂(ρ k).1) - (∫ U, F U ∂(ρ k).1) = _
      rw [← hGk]
      simp only [SingleGeneratorArray.tiltedKernel]
      ring
    rw [hI, norm_neg]
    have hn : ‖∫ U, (linkKernel 𝓛 h (A.tiltedEnergy ha β (s k) 𝓛) F U -
        linkKernel 𝓛 h (wilsonLinkEnergy β 𝓛) F U) ∂(ρ k).1‖ ≤
        observableSupNorm fun U => linkKernel 𝓛 h (A.tiltedEnergy ha β (s k) 𝓛) F U -
          linkKernel 𝓛 h (wilsonLinkEnergy β 𝓛) F U := by
      simpa using norm_integral_le_of_norm_le_const (μ := (ρ k).1)
        (ae_of_all _ fun U => norm_le_supNorm hdiff U)
    refine hn.trans (hb.trans ?_)
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right (Real.exp_le_exp.2 hosc) 1)
      (Real.iSup_nonneg fun U => norm_nonneg _)
  have hb : Tendsto (fun k => observableSupNorm F * (Real.exp (2 * (|s k| * C)) - 1))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => 2 * (|s k| * C)) atTop (𝓝 (2 * (|(0 : ℝ)| * C))) :=
      ((hs.abs).mul_const C).const_mul 2
    have h2 := (Real.continuous_exp.tendsto _).comp h1
    have h3 := (h2.sub_const 1).const_mul (observableSupNorm F)
    simpa using h3
  have hz : Tendsto (fun k => (ρ k).integral (linkKernel 𝓛 h (wilsonLinkEnergy β 𝓛) F) -
      (ρ k).integral F) atTop (𝓝 0) :=
    squeeze_zero_norm' (eventually_atTop.2 ⟨1, key⟩) hb
  exact sub_eq_zero.1 (tendsto_nhds_unique hz (e1.sub e2)).symm
theorem isTiltedGibbsState_of_isSubseqWeakLimit (H : Inputs a ha)
    (hwin : EquilibriumInEmbeddableWindow.Statement)
    (hcov : TorusMeasureCovariance)
    (hweak : LimitsAndErgodicity.SymmetryClosedUnderWeakLimits a)
    {β : ℝ} (hβ : 0 < β) (B : SingleGeneratorArray a) (t : ℝ) {Γ : ℕ → PeriodSublattice a}
    (hΓ : ∀ i, 1 ≤ i → B.PeriodsWithin (Γ i))
    (hper : Tendsto (fun i => minPeriodNorm (Γ i)) atTop atTop) {σ : ℕ → BorelProb a}
    (hσ : ∀ i (hi : 1 ≤ i), (σ i).1 = B.liftedTiltMeasure (hΓ i hi) β t) {ν : BorelProb a}
    (hν : BorelProb.IsSubseqWeakLimit σ ν) :
    B.IsTiltedGibbsState ha β t ν.1 ∧
      ∀ v ∈ B.sublattice, IsSymmetricUnder ν.1 (shift v) := by
  obtain ⟨φ, hφ, h1, hconv⟩ := hν
  refine ⟨⟨ν.2, fun 𝓛 h F hF => integral_tiltedKernel_of_tendstoWeak H hwin hβ B t
    (Γ := Γ ∘ φ) (fun k => hΓ _ (h1 k)) (hper.comp hφ.tendsto_atTop) (ρ := σ ∘ φ)
    (fun k => hσ _ (h1 k)) hconv 𝓛 h hF⟩, fun v hv => ?_⟩
  refine hweak (σ ∘ φ) ν (shift v) hconv fun i => ?_
  change IsSymmetricUnder (σ (φ i)).1 _
  rw [hσ _ (h1 i)]
  exact (hcov a β ha hβ B t (Γ (φ i)) (hΓ _ (h1 i))).2.2 v hv
def zeroArray (hz : IsRealLocalContinuous (fun _ : GaugeField a => (0 : ℝ))) :
    SingleGeneratorArray a :=
  ⟨⊤, inferInstance, fun _ => 0, hz⟩
end TiltedTori
open TiltedTori in
open LatticeConventions (NormalHyperplane conjFun) in
open LatticeConventions.NormalHyperplane (reflectSymmetry) in
theorem tiltedTorusLimits_holds
    (hT : SpacesOfFieldsAndMeasures.FieldAndMeasureSpaceProperties)
    (hK : LinkKernelProperties)
    (hFac : LinkFunctions.Assertion)
    (hM : SymmetriesTransportLinksSupportsAndPlaquettes)
    (hPl : FaceEnergyIndependentOfBasepointAndOrientation)
    (hAct : LatticeSymmetryActionOnFields)
    (hBorel : AnyOrientationGibbs.Equivalences)
    (hCum : CumulantsPolynomialInMomentsAndWeakLimits)
    (hWeak : LimitsAndErgodicity.Statement)
    (hFull : FullReflectionPositivityFromContinuousLocal.Statement)
    (hCov : TorusMeasureCovariance)
    (hWin : EquilibriumInEmbeddableWindow.Statement)
    (hOrb : PeriodSublatticeQuotientFacts) :
    TiltedTorusLimits := by
  intro L K hL _ β hβ A
  have ha := CutoffLattice.spacingAt_pos hL K
  have H : Inputs (refinedSpacing L K) ha := by
    obtain ⟨c₁, c₂, c₃, -, -⟩ := hT _ ha
    obtain ⟨-, f₂, f₃, -⟩ := hFac _ ha
    obtain ⟨-, m₂, -⟩ := hM _ ha
    obtain ⟨-, p₂, -⟩ := hPl.2 _ ha
    exact ⟨c₁, c₂, c₃, hK, f₂, f₃, m₂, p₂, fun r => (hAct _ ha r r).2.2.2⟩
  obtain ⟨hcpt, hmet⟩ := H.probs
  have hWeak₁ := (hWeak _ ha).1
  refine ⟨fun s ρ ν hs hG hν => ((hBorel _ β ha hβ ν.1 ν.2).out 1 0).1
    fun 𝓛 h F hF => integral_wilsonLinkKernel_of_tilt_tendsto_zero H A hs hG hν 𝓛 h hF, ?_⟩
  intro t Γ hΓ hper
  refine ⟨fun i hi => isProbabilityMeasure_liftedTiltMeasure H hOrb β t A (hΓ i hi), ?_⟩
  intro ρ hρ
  refine ⟨fun φ _ _ => exists_isSubseqWeakLimit hcpt hmet _, exists_isSubseqWeakLimit hcpt hmet ρ,
    isClosed_setOf_isSubseqWeakLimit hmet ρ,
    fun ν hν => isTiltedGibbsState_of_isSubseqWeakLimit H hWin hCov hWeak₁ hβ A t hΓ hper hρ hν,
    ?_, ?_, ?_, ?_⟩
  · intro ρ₀ hρ₀ ν hν
    have hD : ∀ i, 1 ≤ i → (zeroArray (isRealLocalContinuous_zero H)).PeriodsWithin (Γ i) :=
      fun _ _ => le_top
    have hσ : ∀ i (hi : 1 ≤ i), (ρ₀ i).1 =
        (zeroArray (isRealLocalContinuous_zero H)).liftedTiltMeasure (hD i hi) β 0 :=
      fun i hi => by
        rw [SingleGeneratorArray.liftedTiltMeasure_zero]
        exact hρ₀ i hi
    obtain ⟨⟨-, hg⟩, hinv⟩ :=
      isTiltedGibbsState_of_isSubseqWeakLimit H hWin hCov hWeak₁ hβ _ 0 hD hper hσ hν
    refine ⟨((hBorel _ β ha hβ ν.1 ν.2).out 1 0).1 fun 𝓛 h F hF => ?_,
      fun v => hinv v (AddSubgroup.mem_top v)⟩
    have e := hg 𝓛 h F hF
    rwa [SingleGeneratorArray.tiltedKernel_zero] at e
  · intro ν hν
    obtain ⟨-, hcum₁, hcum₂, -⟩ := hCum
    refine ⟨fun F hF => hν F hF.1, fun f hb hs => ((hcum₁ _ ha).2 ρ ν hν).2 f ⟨hb, hs⟩,
      fun n f hn hf => ?_⟩
    have hlim := hcum₂ L K ha ρ ν hν n f hn fun j =>
      isBoundedBorelCompactlySupported_of_continuous
        (SeparatedFamilies.IsEuclidLipschitz.continuous (hf.lipschitz j))
        (hf.hasCompactSupport j)
    refine ⟨hlim, fun b i₀ hb => le_of_tendsto hlim.norm ?_⟩
    filter_upwards [eventually_ge_atTop (max 1 i₀)] with i hi
    exact hb i (le_of_max_le_left hi) (le_of_max_le_right hi)
  · rintro r w - - hinv ν ⟨φ, -, h1, hconv⟩
    exact hWeak₁ (ρ ∘ φ) ν r hconv fun i => hinv _ (h1 i)
  · rintro P hP hpos ν ⟨φ, hφ, h1, hconv⟩
    have hloc : ∀ F, Continuous F → F ∈ locallyMeasurableIn _ P.upperHalfSpace →
        0 ≤ reflectedPairing hP ν F := by
      intro F hFc hFl
      obtain ⟨i₀, hi₀⟩ := hpos F hFc hFl
      have hθ : (reflectSymmetry hP).actOn F ∈ continuousFns _ := by
        rw [← (H.symmetry (reflectSymmetry hP)).2.2.1]
        exact ⟨F, hFc, rfl⟩
      have hc : Continuous fun U =>
          conjFun ((reflectSymmetry hP).actOn F) U * F U :=
        (Complex.continuous_conj.comp hθ).mul hFc
      refine ge_of_tendsto (hconv _ hc) ?_
      filter_upwards [eventually_ge_atTop i₀] with k hk
      exact hi₀ _ (h1 k) (hk.trans (hφ.id_le k))
    exact ⟨hloc, fun hθ => hFull _ ha P hP ν hθ fun F hFl hFc => hloc F hFc hFl⟩
end GibbsAtFixedSpacing
end YangMills.Construction
