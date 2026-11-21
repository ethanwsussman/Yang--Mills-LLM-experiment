import YangMills.Construction.InfiniteLattice.ContinuousLocalObservablesDecideAndWeakCompactness
import YangMills.Construction.InfiniteLattice.FinitenessOfATorusNormalisersAndExtendedMeasures
import YangMills.Construction.InfiniteLattice.FoldInequality
import YangMills.Construction.InfiniteLattice.LowerTangentUpperTangentAndTheInequalityInFiniteVolume
import YangMills.Construction.InfiniteLattice.PeriodicExtensionOfATorusOfAnyShape
import YangMills.Construction.InfiniteLattice.WeakLimitsOfTorusMeasures
import YangMills.Construction.InfiniteLattice.WhatAnObservableDependsOnAndItsSupport
import YangMills.Construction.ReflectionPositivity.PerturbedTorusMeasuresHaveAllTheMirrorsOfTheLadder
import YangMills.Construction.ReflectionPositivity.PullBacksOnASplitTorus
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology ComplexOrder Matrix
noncomputable section
namespace YangMills.Construction.NormalFamilies
open InfiniteLattice
namespace FoldedStateBoundProof
theorem exists_siteCube_of_finite {𝓜 : Set (Link 1)} (h : 𝓜.Finite) :
    ∃ (ϱ : ℕ+) (x : LatticePoint 1),
      LinksLieIn 𝓜 ((fun y : LatticePoint 1 => (y : AmbientSpace)) '' siteCube x ϱ) := by
  obtain ⟨B, hB⟩ :=
    (h.image fun b : Link 1 => max ‖(b.initial : AmbientSpace)‖ ‖(b.terminal : AmbientSpace)‖).bddAbove
  obtain ⟨R, hRdef⟩ : ∃ R : ℕ, R = ⌈B⌉₊ + 1 := ⟨_, rfl⟩
  have hR0 : 0 < 2 * R := by omega
  have hBR : B ≤ R := (Nat.le_ceil B).trans (by rw [hRdef]; push_cast; linarith)
  let x : LatticePoint 1 := ⟨fun _ => -(R : ℝ), fun _ => -(R : ℤ), fun _ => by push_cast; ring⟩
  have key : ∀ y : LatticePoint 1, ‖(y : AmbientSpace)‖ ≤ R →
      (y : AmbientSpace) ∈ (fun y : LatticePoint 1 => (y : AmbientSpace)) '' siteCube x ⟨2 * R, hR0⟩ := by
    intro y hy
    obtain ⟨m, hm⟩ := y.2
    have hbound : ∀ μ, -(R : ℤ) ≤ m μ ∧ m μ ≤ R := fun μ => by
      have h1 := (norm_le_pi_norm (y : AmbientSpace) μ).trans hy
      rw [Real.norm_eq_abs, hm μ, mul_one] at h1
      obtain ⟨h2, h3⟩ := abs_le.1 h1
      exact ⟨by exact_mod_cast h2, by exact_mod_cast h3⟩
    refine ⟨y, ⟨fun μ => (m μ + R).toNat, fun μ => ?_, fun μ => ?_⟩, rfl⟩
    · have := hbound μ
      change (m μ + R).toNat ≤ 2 * R
      omega
    · have h0 := hbound μ
      have h1 : (((m μ + R).toNat : ℤ)) = m μ + R := Int.toNat_of_nonneg (by omega)
      have h2 : (((m μ + R).toNat : ℕ) : ℝ) = (m μ : ℝ) + R := by exact_mod_cast h1
      rw [h2, hm μ]
      change _ = -(R : ℝ) + _
      ring
  refine ⟨⟨2 * R, hR0⟩, x, fun b hb => ?_⟩
  have h1 := hB ⟨b, hb, rfl⟩
  exact ⟨key _ ((le_max_left _ _).trans (h1.trans hBR)),
    key _ ((le_max_right _ _).trans (h1.trans hBR))⟩
theorem exists_bound_dotProduct {𝓜 : Set (Link 1)} (h : 𝓜.Finite) (n : AmbientSpace) :
    ∃ B : ℝ, ∀ b ∈ 𝓜, n ⬝ᵥ (b.initial : AmbientSpace) ≤ B ∧ n ⬝ᵥ (b.terminal : AmbientSpace) ≤ B := by
  obtain ⟨B, hB⟩ :=
    (h.image fun b : Link 1 =>
      max (n ⬝ᵥ (b.initial : AmbientSpace)) (n ⬝ᵥ (b.terminal : AmbientSpace))).bddAbove
  exact ⟨B, fun b hb => ⟨(le_max_left _ _).trans (hB ⟨b, hb, rfl⟩),
    (le_max_right _ _).trans (hB ⟨b, hb, rfl⟩)⟩⟩
theorem observableSupport_finite (hSup : ObservableDependence.Statement)
    {F : GaugeField 1 → ℂ} (hF : F ∈ continuousLocalFunctions 1) :
    (observableSupport F).Finite :=
  ((hSup F hF.1 ∅ ∅ (Set.empty_subset _) (Set.empty_subset _) Set.univ).2.2.2.2.1 hF.2.1).2
theorem observableSupport_linksLieIn (hSup : ObservableDependence.Statement)
    {F : GaugeField 1 → ℂ} (hF : F ∈ continuousLocalFunctions 1) {O : Set AmbientSpace}
    (h : F ∈ regionObservables 1 O) : LinksLieIn (observableSupport F) O :=
  ((hSup F hF.1 ∅ ∅ (Set.empty_subset _) (Set.empty_subset _) O).2.2.2.2.2 hF.2.1).1.1 h
def ladderRung (L : MirrorLadder) (k : ℤ) : NormalLevelPair 1 where
  normal := L.normal
  normal_mem := L.normal_mem
  level := L.offset + (k : ℝ) * (L.spacing : ℝ)
  allowed := by
    have h := L.offset_allowed.add_intCast (k * L.spacing)
    rwa [Int.cast_mul] at h
theorem levelPair_eq_ladderRung {L : MirrorLadder} {w : ℤ} {S : SlabDecomposition}
    (h : L.IsAdaptedSlabDecomposition w S) (k : ℤ) : S.levelPair k = ladderRung L k := by
  obtain ⟨hf, hb, ht, -⟩ := h
  rcases S with ⟨f, fm, b, ba, th, t2, p, p1, lat, sp⟩
  simp only at hf hb ht
  subst hf hb ht
  rfl
theorem conjReflectObservable_mem (P : NormalLevelPair 1) {F : GaugeField 1 → ℂ}
    (hF : F ∈ continuousLocalFunctions 1) :
    P.conjReflectObservable F ∈ continuousLocalFunctions 1 := by
  obtain ⟨⟨hb, C, hC⟩, ⟨S, hS, hm⟩, hc⟩ :=
    actOn_mem_continuousLocalFunctions P.reflectSymmetry
      (continuous_reflectAcross _ _) hF
  refine ⟨⟨Complex.continuous_conj.measurable.comp hb, C, fun U => ?_⟩, ⟨S, hS, ?_⟩,
    Complex.continuous_conj.comp hc⟩
  · simpa [NormalLevelPair.conjReflectObservable, NormalLevelPair.reflectObservable] using hC U
  · exact Complex.continuous_conj.measurable.comp hm
theorem exists_adaptedSlabDecomposition (hAd : AdaptedTorusProperties) (L : MirrorLadder) (J : ℕ)
    (hJ : 1 ≤ J) (w : ℤ) (hw : Even w) (hw2 : 2 ≤ w) (h3 : 3 ≤ min ((J : ℤ) * L.spacing) w) :
    ∃ S : SlabDecomposition, L.IsAdaptedSlabDecomposition w S ∧ S.count = J := by
  have hnum : AdmissibleParams L.spacing (J : ℤ) w :=
    ⟨L.even_spacing, L.two_le_spacing, by exact_mod_cast hJ, hw, hw2⟩
  obtain ⟨ha, hb, -⟩ := hAd L.normal L.normal_mem L.spacing J w hnum
  obtain ⟨Γ, hΓ⟩ := ha.2.2.2.2.2.1 h3
  exact ⟨{ normal := L.normal
           normal_mem := L.normal_mem
           baseLevel := L.offset
           baseLevel_allowed := L.offset_allowed
           width := L.spacing
           two_le_width := L.two_le_spacing
           count := J
           one_le_count := hJ
           period := Γ
           splits := (hb h3 Γ hΓ).1 }, ⟨rfl, rfl, rfl, hnum, h3, hΓ⟩, rfl⟩
theorem norm_le_maxNorm (x : AmbientSpace) : ‖x‖ ≤ WholeSpace.maxNorm x := by
  have hle : ∀ μ, |x μ| ≤ WholeSpace.maxNorm x := fun μ =>
    Finset.le_sup' (fun μ => |x μ|) (Finset.mem_univ μ)
  exact (pi_norm_le_iff_of_nonneg ((abs_nonneg _).trans (hle 0))).2 fun μ => hle μ
theorem le_minSupPeriod (hAd : AdaptedTorusProperties) {L : MirrorLadder} {w : ℤ}
    {S : SlabDecomposition} (h : L.IsAdaptedSlabDecomposition w S) :
    ((min ((S.count : ℤ) * L.spacing) w : ℤ) : ℝ) ≤ S.period.minSupPeriod := by
  obtain ⟨ha, -, -⟩ := hAd L.normal L.normal_mem L.spacing S.count w h.admissible
  refine le_csInf ?_ ?_
  · obtain ⟨v, hv, hli⟩ := S.period.exists_linearIndependent
    have h0 : ((v 0 : LatticePoint 1) : AmbientSpace) ≠ 0 := hli.ne_zero 0
    exact ⟨_, v 0, hv 0, fun e => h0 (by rw [e]; rfl), rfl⟩
  · rintro _ ⟨γ, hγ, h0, rfl⟩
    have hmem : (γ : AmbientSpace) ∈ adaptedLattice L.normal L.normal_mem L.spacing S.count w := by
      rw [← h.toAmbient_eq]
      exact ⟨γ, hγ, rfl⟩
    exact (ha.2.2.2.2.1 _ hmem fun e => h0 (Subtype.ext e)).trans (norm_le_maxNorm _)
theorem foldedArray_fitsPeriods (hAd : AdaptedTorusProperties) {L : MirrorLadder} {w : ℤ}
    {S : SlabDecomposition} (h : L.IsAdaptedSlabDecomposition w S) (A : L.SlabZeroGenerator) :
    A.foldedArray.FitsPeriods S.period := by
  intro v hv
  have hle := (hAd L.normal L.normal_mem L.spacing S.count w h.admissible).2.2.2.2.1
  have hmem : (v : AmbientSpace) ∈ adaptedLattice L.normal L.normal_mem L.spacing S.count w := by
    rw [← h.toAmbient_eq]
    exact ⟨v, hv, rfl⟩
  change v ∈ L.normalSublattice
  exact AddSubgroup.mem_addSubgroupOf.mpr (hle hmem)
structure IsTorusSequence (L : MirrorLadder) (ϱ : ℕ+) (S : ℕ → SlabDecomposition) (w : ℕ → ℤ) :
    Prop where
  isAdapted : ∀ j, L.IsAdaptedSlabDecomposition (w j) (S j)
  count_eq : ∀ j, (S j).count = (ϱ : ℕ) + 1 + j
  side_eq : ∀ j, w j = 2 * (((ϱ : ℕ) : ℤ) + 1 + (j : ℤ))
theorem exists_torusSequence (hAd : AdaptedTorusProperties) (L : MirrorLadder) (ϱ : ℕ+) :
    ∃ S w, IsTorusSequence L ϱ S w := by
  have hϱ := ϱ.pos
  have hs := L.two_le_spacing
  have : ∀ j : ℕ, ∃ S : SlabDecomposition,
      L.IsAdaptedSlabDecomposition (2 * (((ϱ : ℕ) : ℤ) + 1 + (j : ℤ))) S ∧
        S.count = (ϱ : ℕ) + 1 + j := fun j => by
    refine exists_adaptedSlabDecomposition hAd L _ (by omega) _ (even_two_mul _) (by omega)
      (le_min ?_ (by omega))
    push_cast
    nlinarith
  choose S hS using this
  exact ⟨S, _, fun j => (hS j).1, fun j => (hS j).2, fun _ => rfl⟩
theorem IsTorusSequence.bounds_min {L : MirrorLadder} {ϱ : ℕ+} {S : ℕ → SlabDecomposition}
    {w : ℕ → ℤ} (T : IsTorusSequence L ϱ S w) (j : ℕ) :
    ((ϱ : ℕ) : ℤ) + 1 + (j : ℤ) ≤ min (((S j).count : ℤ) * L.spacing) (w j) ∧
      ((ϱ : ℕ) : ℤ) + 1 < min (((S j).count : ℤ) * L.spacing) (w j) := by
  have hϱ := ϱ.pos
  have hs := L.two_le_spacing
  have hp : ((S j).count : ℤ) = ((ϱ : ℕ) : ℤ) + 1 + (j : ℤ) := by
    rw [T.count_eq]
    push_cast
    ring
  have hm : 2 * (((ϱ : ℕ) : ℤ) + 1 + (j : ℤ)) ≤ (((ϱ : ℕ) : ℤ) + 1 + (j : ℤ)) * L.spacing := by
    nlinarith
  rw [hp, T.side_eq]
  exact ⟨le_min (by omega) (by omega), _root_.lt_min (by omega) (by omega)⟩
theorem IsTorusSequence.periodsDiverge {L : MirrorLadder} {ϱ : ℕ+} {S : ℕ → SlabDecomposition}
    {w : ℕ → ℤ} (hAd : AdaptedTorusProperties) (T : IsTorusSequence L ϱ S w) :
    PeriodsDiverge fun j => (S j).period := by
  refine tendsto_atTop_mono (fun j => ?_) tendsto_natCast_atTop_atTop
  have h2 : (j : ℤ) ≤ min (((S j).count : ℤ) * L.spacing) (w j) :=
    le_trans (by have := ϱ.pos; omega) (T.bounds_min j).1
  exact (by exact_mod_cast h2 :
    (j : ℝ) ≤ ((min (((S j).count : ℤ) * L.spacing) (w j) : ℤ) : ℝ)).trans
      (le_minSupPeriod hAd (T.isAdapted j))
theorem IsTorusSequence.tendsto_error {L : MirrorLadder} {ϱ : ℕ+} {S : ℕ → SlabDecomposition}
    {w : ℕ → ℤ} (T : IsTorusSequence L ϱ S w) (K : ℝ) :
    Tendsto (fun j => K * (1 / (((S j).count : ℝ) * (L.spacing : ℝ)) + 1 / (w j : ℝ)))
      atTop (𝓝 0) := by
  have hs : (L.spacing : ℝ) ≠ 0 := MirrorLadder.spacing_ne_zero L
  have hu : Tendsto (fun j : ℕ => ((ϱ : ℕ) : ℝ) + 1 + (j : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
  have h0 : Tendsto
      (fun j : ℕ => K * ((1 / (L.spacing : ℝ) + 1 / 2) * (((ϱ : ℕ) : ℝ) + 1 + (j : ℝ))⁻¹)) atTop
      (𝓝 (K * ((1 / (L.spacing : ℝ) + 1 / 2) * 0))) :=
    ((tendsto_inv_atTop_zero.comp hu).const_mul _).const_mul _
  rw [mul_zero, mul_zero] at h0
  refine h0.congr fun j => ?_
  have hpos : ((ϱ : ℕ) : ℝ) + 1 + (j : ℝ) ≠ 0 := by positivity
  rw [T.count_eq, T.side_eq]
  push_cast
  field_simp
theorem tendsto_atTop_of_strictMono_succ {κ : ℕ → ℕ} (h : ∀ i j, 1 ≤ i → i < j → κ i < κ j) :
    Tendsto κ atTop atTop := by
  have hm : StrictMono fun i => κ (i + 1) :=
    strictMono_nat_of_lt_succ fun n => h _ _ (by omega) (by omega)
  exact (tendsto_add_atTop_iff_nat 1).1 hm.tendsto_atTop
theorem isWeakClusterPoint_of_weakConverges {μ : ℕ → Measure (GaugeField 1)}
    {ν : Measure (GaugeField 1)} (h : WeakConvergesUnitSpacing μ ν) :
    IsWeakClusterPointUnitSpacing μ ν := by
  intro 𝒞 hC hcont ε hε k₀ _
  have hall : ∀ᶠ k in atTop, ∀ F ∈ 𝒞, ‖stateEval (μ k) F - stateEval ν F‖ ≤ ε := by
    refine (eventually_all_finite hC).2 fun F hF => ?_
    exact ((tendsto_iff_norm_sub_tendsto_zero.1 (h F (hcont F hF))).eventually
      (ge_mem_nhds hε)).mono fun _ hk => hk
  obtain ⟨k, hk₁, hk₂⟩ := (hall.and (eventually_ge_atTop k₀)).exists
  exact ⟨k, hk₂, hk₁⟩
theorem isProbabilityMeasure_tiltedMeasure (hFin : FiniteTorusPartitionsAndLifts)
    {β : ℝ} (hβ : 0 < β) (𝔸 : LocalObservableArray) (Γ : PeriodSublattice 1) (h : 𝔸.FitsPeriods Γ)
    (t : ℝ) : IsProbabilityMeasure (𝔸.tiltedMeasure Γ β t) := by
  obtain ⟨-, hE⟩ := (hFin β hβ Γ).2 𝔸 h t
  have hp := hE.isProbabilityMeasure_tiltedLift
  have hm := hE.continuous_lift.measurable
  constructor
  have := hp.measure_univ
  rw [LocalObservableArray.tiltedLiftMeasure, Measure.map_apply hm MeasurableSet.univ] at this
  simpa using this
theorem periodize_mem_plusAlgebra (hExt : PeriodicQuotient.FinitenessClaim)
    (S : SlabDecomposition) (k : ℤ) {F : GaugeField 1 → ℂ}
    (hF : F ∈ continuousLocalFunctions 1)
    (hh : ∀ b ∈ observableSupport F,
      (S.level k ≤ S.normal ⬝ᵥ (b.initial : AmbientSpace) ∧
        S.normal ⬝ᵥ (b.initial : AmbientSpace) ≤ S.level k + (S.halfPeriod : ℝ)) ∧
      (S.level k ≤ S.normal ⬝ᵥ (b.terminal : AmbientSpace) ∧
        S.normal ⬝ᵥ (b.terminal : AmbientSpace) ≤ S.level k + (S.halfPeriod : ℝ))) :
    S.period.periodize F ∈ S.period.plusAlgebra S.normal S.halfPeriod (S.level k) := by
  have hE := hExt.1 S.period
  obtain ⟨C, hC⟩ := hF.1.2
  refine (PeriodSublattice.mem_boundedAlgebra _).mpr
    ⟨(hE.continuous_periodize F hF).measurable, ⟨C, fun U => hC _⟩, fun U U' hUU =>
      hE.periodize_dependsOn F hF U U' fun c hc => hUU c ?_⟩
  obtain ⟨b, hb, rfl⟩ := hc
  obtain ⟨γ, hγ, hrep⟩ := S.period.exists_linkRep_eq b
  have hrep' : (S.period.linkRep (S.period.linkClass b)).1 = b.1.shiftBy γ :=
    congrArg Subtype.val hrep
  have hproj : S.period.quotientMap γ = 0 := (QuotientAddGroup.eq_zero_iff _).2 hγ
  have hsite : ∀ y : LatticePoint 1, S.level k ≤ S.normal ⬝ᵥ (y : AmbientSpace) →
      S.normal ⬝ᵥ (y : AmbientSpace) ≤ S.level k + (S.halfPeriod : ℝ) →
      S.period.quotientMap (y + γ) ∈
        S.period.plusHalf S.normal S.halfPeriod (S.level k) := by
    intro y h1 h2
    refine ⟨S.normal ⬝ᵥ (y : AmbientSpace), ⟨y, ?_, 0, by simp⟩, h1, h2⟩
    rw [map_add, hproj, add_zero]
  intro s hs
  simp only [PeriodSublattice.linkEndpoints, hrep'] at hs
  rcases hs with rfl | rfl
  · rw [Link.initial_shiftBy]
    exact hsite _ (hh b.1 hb).1.1 (hh b.1 hb).1.2
  · rw [Link.terminal_shiftBy]
    exact hsite _ (hh b.1 hb).2.1 (hh b.1 hb).2.2
theorem tiltedLiftMeasure_symmetric
    (hRP : TiltedTorusMeasureReflectsAtEveryRung)
    (hAd : AdaptedTorusProperties) (hExt : PeriodicQuotient.FinitenessClaim)
    (hPull : SplitTorusPullbacks)
    (hFin : FiniteTorusPartitionsAndLifts)
    {β : ℝ} (hβ : 0 < β) {L : MirrorLadder} (A : L.SlabZeroGenerator) {w : ℤ}
    {S : SlabDecomposition} (h : L.IsAdaptedSlabDecomposition w S) (t : ℝ) (k : ℤ) :
    IsSymmetricUnder (A.foldedArray.tiltedLiftMeasure S.period β t)
      (S.levelPair k).reflectSymmetry := by
  intro G hG
  have hμ := isProbabilityMeasure_tiltedMeasure hFin hβ A.foldedArray S.period
    (foldedArray_fitsPeriods hAd h A) t
  have hE := hExt.1 S.period
  have hr : IsClassIsometry S.normal (S.levelPair k).reflectSymmetry.toFun :=
    isClassIsometry_reflectAcross (S.level_allowed k)
  have hext := ((hPull β hβ S.period S.normal S.normal_mem S.halfPeriod S.splits).2.1 _ hr).2.2.2.2.1
  obtain ⟨-, -, -, -, hpres, -⟩ := hRP β hβ L A w S h t k
  have hmain := hpres.2.2 (fun U => G (S.period.lift U))
    (hE.measurable_bounded_comp_lift G hG).1 (hE.measurable_bounded_comp_lift G hG).2
  have hG' : IsBoundedObservable ((S.levelPair k).reflectSymmetry.actOn G) := by
    obtain ⟨hm, C, hC⟩ := hG
    exact ⟨hm.comp (continuous_pullbackField _).measurable, C, fun U => hC _⟩
  rw [LocalObservableArray.tiltedLiftMeasure,
    hE.integral_map_lift _ hμ _ hG', hE.integral_map_lift _ hμ G hG, ← hmain]
  refine integral_congr_ae (Eventually.of_forall fun U => ?_)
  change G ((S.levelPair k).reflectSymmetry.pullbackField _) = G _
  rw [← hext U]
  rfl
theorem integralOf_conj_mul_nonneg
    (hRP : TiltedTorusMeasureReflectsAtEveryRung)
    (hPull : SplitTorusPullbacks)
    {β : ℝ} (hβ : 0 < β) {L : MirrorLadder} (A : L.SlabZeroGenerator) {w : ℤ}
    {S : SlabDecomposition} (h : L.IsAdaptedSlabDecomposition w S) (t : ℝ) (k : ℤ)
    {F : GaugeField 1 → ℂ} (hF : F ∈ continuousLocalFunctions 1)
    (hU : S.period.periodize F ∈ S.period.plusAlgebra S.normal S.halfPeriod (S.level k)) :
    0 ≤ PeriodSublattice.integralOf (A.foldedArray.tiltedMeasure S.period β t)
      (S.period.periodize ((S.levelPair k).conjReflectObservable F * F)) := by
  have hP := hPull β hβ S.period S.normal S.normal_mem S.halfPeriod S.splits
  have hc := conjReflectObservable_mem (S.levelPair k) hF
  obtain ⟨-, h1, -⟩ := hP.1 (S.level k) (S.level_allowed k)
  have h1' : S.period.periodize ((S.levelPair k).conjReflectObservable F) =
      S.conjReflectAt k (S.period.periodize F) := h1 F hF
  have h2 := (hP.2.2.2.1 _ hc F hF).1
  obtain ⟨-, -, -, -, -, hpos⟩ := hRP β hβ L A w S h t k
  have h3 := hpos _ (Or.inl hU)
  rw [h2, h1']
  exact h3
theorem axialPeriodDensity_nonneg (n : AmbientSpace) (h : ℤ) : 0 ≤ axialPeriodDensity n h := by
  unfold axialPeriodDensity
  split_ifs
  · positivity
  · exact le_rfl
theorem exists_tiltedLimit
    (hWeak : LocalDeterminationAndCompactness)
    (hLimits : TorusMeasureWeakLimits)
    (hTan : FiniteVolumeTangentBounds.Statement)
    (hRP : TiltedTorusMeasureReflectsAtEveryRung)
    (hAd : AdaptedTorusProperties) (hExt : PeriodicQuotient.FinitenessClaim)
    (hPull : SplitTorusPullbacks)
    (hSup : ObservableDependence.Statement)
    (hFin : FiniteTorusPartitionsAndLifts)
    {β : ℝ} (hβ : 0 < β) {L : MirrorLadder} (A : L.SlabZeroGenerator) (ϱ : ℕ+) (x : LatticePoint 1)
    (hx : LinksLieIn (observableSupport A.toFun)
      ((fun y : LatticePoint 1 => (y : AmbientSpace)) '' siteCube x ϱ))
    {S : ℕ → SlabDecomposition} {w : ℕ → ℤ} (T : IsTorusSequence L ϱ S w)
    {ν : Measure (GaugeField 1)} (hν : ν ∈ subgroupInvariantGibbsClass one_pos β L.axialSublattice)
    {t : ℝ} (ht : 0 < t) :
    ∃ νt : Measure (GaugeField 1), IsProbabilityMeasure νt ∧
      νt ∈ A.foldedArray.tiltedGibbsClass β t ∧
      (∀ v ∈ L.normalSublattice, IsSymmetricUnder νt (shift v)) ∧
      (∀ k : ℤ, IsSymmetricUnder νt (ladderRung L k).reflectSymmetry) ∧
      (∀ k : ℤ, ∀ F ∈ halfSpaceContinuousLocal 1 (ladderRung L k).normal
          (ladderRung L k).level 1,
        0 ≤ stateEval νt ((ladderRung L k).conjReflectObservable F * F)) ∧
      (stateEval ν A.toFun).re ≤ (stateEval νt A.toFun).re := by
  have hdesc := fun j => foldedArray_fitsPeriods hAd (T.isAdapted j) A
  have hprob : ∀ j, IsProbabilityMeasure
      (A.foldedArray.tiltedLiftMeasure (S j).period β t) := fun j =>
    ((hFin β hβ (S j).period).2 A.foldedArray (hdesc j) t).2.isProbabilityMeasure_tiltedLift
  obtain ⟨κ, νt, hνt, -, hκ, hconv⟩ := hWeak.2.2.1
    (fun j => A.foldedArray.tiltedLiftMeasure (S j).period β t) (fun j _ => hprob j)
  have tκ := tendsto_atTop_of_strictMono_succ hκ
  have hper : PeriodsDiverge fun i => (S (κ i)).period := (T.periodsDiverge hAd).comp tκ
  obtain ⟨-, -, -, hl⟩ := hLimits β hβ
  obtain ⟨ha, -, hc⟩ := hl A.foldedArray t (fun i => (S (κ i)).period)
    (fun i _ => hdesc (κ i)) hper
  have hwl := isWeakClusterPoint_of_weakConverges hconv
  obtain ⟨hcl, htr⟩ := ha νt hνt hwl
  refine ⟨νt, hνt, hcl, htr, fun k => ?_, fun k => ?_, ?_⟩
  · refine (hWeak.2.2.2 _).2 (fun i => A.foldedArray.tiltedLiftMeasure (S (κ i)).period β t)
      νt (fun i _ => hprob (κ i)) hνt hconv fun i _ => ?_
    rw [← levelPair_eq_ladderRung (T.isAdapted (κ i)) k]
    exact tiltedLiftMeasure_symmetric hRP hAd hExt hPull hFin hβ A (T.isAdapted (κ i)) t k
  · refine fun F hF => hc (ladderRung L k) (fun F hF => ?_) νt hνt hwl F hF
    obtain ⟨hside, hloc⟩ := hF
    have hlinks := observableSupport_linksLieIn hSup hloc hside
    obtain ⟨B, hB⟩ := exists_bound_dotProduct (observableSupport_finite hSup hloc) L.normal
    obtain ⟨i₀, hi₀⟩ := eventually_atTop.1 ((tendsto_natCast_atTop_atTop.comp tκ).eventually_ge_atTop
      (B - (ladderRung L k).level))
    refine ⟨i₀, fun i _ hi => ?_⟩
    have hm := levelPair_eq_ladderRung (T.isAdapted (κ i)) k
    rw [← hm]
    refine integralOf_conj_mul_nonneg hRP hPull hβ A (T.isAdapted (κ i)) t k hloc
      (periodize_mem_plusAlgebra hExt _ k hloc fun b hb => ?_)
    have hlev : (S (κ i)).level k = (ladderRung L k).level := by rw [← hm]; rfl
    have hnor : (S (κ i)).normal = L.normal := (T.isAdapted (κ i)).normal_eq
    have hz : (κ i : ℝ) ≤ ((S (κ i)).halfPeriod : ℝ) := by
      have hs := L.two_le_spacing
      have hz' : (κ i : ℤ) ≤ (S (κ i)).halfPeriod := by
        rw [SlabDecomposition.halfPeriod, T.count_eq, (T.isAdapted (κ i)).width_eq]
        push_cast
        nlinarith [Int.natCast_nonneg (κ i), Int.natCast_nonneg (ϱ : ℕ)]
      exact_mod_cast hz'
    have hk := hi₀ i hi
    have hside' : ∀ y : AmbientSpace, y ∈ closedHalfSpace (ladderRung L k).normal
        (ladderRung L k).level 1 → (ladderRung L k).level ≤ L.normal ⬝ᵥ y := by
      intro y hy
      simp only [closedHalfSpace, Set.mem_ofPred_eq, Units.val_one, Int.cast_one, one_mul] at hy
      have : (ladderRung L k).normal = L.normal := rfl
      rw [this] at hy
      linarith
    have h1 := hside' _ (hlinks b hb).1
    have h2 := hside' _ (hlinks b hb).2
    have h3 := hB b hb
    rw [hlev, hnor]
    simp only [Function.comp_apply] at hk
    exact ⟨⟨h1, by linarith [h3.1]⟩, ⟨h2, by linarith [h3.2]⟩⟩
  · have hκ0 := axialPeriodDensity_nonneg L.normal L.spacing
    have hle : ∀ i, (stateEval ν A.toFun).re ≤
        (stateEval (A.foldedArray.tiltedLiftMeasure (S (κ i)).period β t) A.toFun).re +
          (3 * (tangentLowerConst : ℝ) * (β + t * observableSupNorm A.toFun) *
            ((ϱ : ℕ) : ℝ) ^ 5 *
              (1 / (((S (κ i)).count : ℝ) * (L.spacing : ℝ)) + 1 / (w (κ i) : ℝ))) /
            (t * axialPeriodDensity L.normal L.spacing) := fun i => by
      obtain ⟨hbound, -, -, -, -, -, -, -, -, -, -, -, hd⟩ :=
        hTan β hβ L A ϱ x hx (w (κ i)) (S (κ i)) (T.isAdapted (κ i)) (T.bounds_min (κ i)).2
      refine (hd ν hν t ht).trans (add_le_add_right ?_ _)
      exact div_le_div_of_nonneg_right (hbound t ht.le) (mul_nonneg ht.le hκ0)
    have hlim := ((Complex.continuous_re.tendsto _).comp
        (hconv A.toFun A.mem_continuousLocal.2.2)).add
      (((T.tendsto_error (3 * (tangentLowerConst : ℝ) * (β + t * observableSupNorm A.toFun) *
        ((ϱ : ℕ) : ℝ) ^ 5)).comp tκ).div_const (t * axialPeriodDensity L.normal L.spacing))
    have := ge_of_tendsto' hlim hle
    simpa using this
theorem stateEval_im_eq_zero {L : MirrorLadder} (A : L.SlabZeroGenerator)
    (μ : Measure (GaugeField 1)) : (stateEval μ A.toFun).im = 0 := by
  have h : A.toFun = fun U => (((A.toFun U).re : ℝ) : ℂ) :=
    funext fun U => Complex.ext (by simp) (by simp [A.im_eq_zero U])
  have h' : stateEval μ A.toFun = ((∫ U, (A.toFun U).re ∂μ : ℝ) : ℂ) := by
    change ∫ U, A.toFun U ∂μ = _
    rw [← integral_complex_ofReal]
    exact integral_congr_ae (Eventually.of_forall fun U => congrFun h U)
  rw [h', Complex.ofReal_im]
theorem holds
    (hWeak : LocalDeterminationAndCompactness)
    (hLimits : TorusMeasureWeakLimits)
    (hTan : FiniteVolumeTangentBounds.Statement)
    (hRP : TiltedTorusMeasureReflectsAtEveryRung)
    (hAd : AdaptedTorusProperties) (hExt : PeriodicQuotient.FinitenessClaim)
    (hPull : SplitTorusPullbacks)
    (hSup : ObservableDependence.Statement)
    (hFin : FiniteTorusPartitionsAndLifts) :
    FoldedStateBound := by
  intro β hβ L A ν hν
  obtain ⟨ϱ, x, hx⟩ := exists_siteCube_of_finite (observableSupport_finite hSup A.mem_continuousLocal)
  obtain ⟨S, w, T⟩ := exists_torusSequence hAd L ϱ
  have hstate := fun i : ℕ => exists_tiltedLimit hWeak hLimits hTan hRP hAd hExt hPull hSup hFin hβ A
    ϱ x hx T hν (t := 1 / ((i : ℝ) + 1)) (by positivity)
  choose μ hμp hμc hμτ hμθ hμF hμA using hstate
  obtain ⟨κ, ν₀, hν₀, -, hκ, hconv⟩ := hWeak.2.2.1 μ fun j _ => hμp j
  have tκ := tendsto_atTop_of_strictMono_succ hκ
  have htk : Tendsto (fun i => 1 / ((κ i : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp tκ
  obtain ⟨-, hb, hd, -⟩ := hLimits β hβ
  have hEq := hb A.foldedArray _ (fun i => μ (κ i)) ν₀ hν₀ htk (fun k _ => hμc (κ k)) hconv
  have hinv : ∀ k : ℤ, IsSymmetricUnder ν₀ (ladderRung L k).reflectSymmetry := fun k =>
    (hWeak.2.2.2 _).2 (fun i => μ (κ i)) ν₀ (fun i _ => hμp _) hν₀ hconv fun i _ => hμθ _ k
  refine ⟨ν₀, ⟨hEq, fun v hv => ?_⟩, fun k => ⟨ladderRung L k, rfl, rfl, hinv k, fun F hF => ?_⟩, ?_⟩
  · exact (hWeak.2.2.2 _).2 (fun i => μ (κ i)) ν₀ (fun i _ => hμp _) hν₀ hconv
      fun i _ => hμτ _ v hv
  · have hsides := hd (ladderRung L k) ν₀ hν₀ (hinv k) (fun F hF =>
      ge_of_tendsto' (hconv _ ((conjReflectObservable_mem _ hF.2).2.2.mul hF.2.2.2))
        fun i => hμF (κ i) k F hF) F
    refine hsides ?_
    have e1 : closedHalfSpace (ladderRung L k).normal (ladderRung L k).level 1 =
        {x | (ladderRung L k).level ≤ L.normal ⬝ᵥ x} := by
      ext y
      simp only [closedHalfSpace, Set.mem_ofPred_eq, Units.val_one, Int.cast_one, one_mul,
        sub_nonneg]
      rfl
    have e2 : closedHalfSpace (ladderRung L k).normal (ladderRung L k).level (-1) =
        {x | L.normal ⬝ᵥ x ≤ (ladderRung L k).level} := by
      ext y
      simp only [closedHalfSpace, Set.mem_ofPred_eq, Units.val_neg, Units.val_one, Int.cast_neg,
        Int.cast_one, neg_mul, one_mul, neg_sub, sub_nonneg]
      rfl
    rcases hF with hF | hF
    · left
      rw [halfSpaceObservables, e1]
      exact hF
    · right
      rw [halfSpaceObservables, e2]
      exact hF
  · have hre : (stateEval ν A.toFun).re ≤ (stateEval ν₀ A.toFun).re :=
      ge_of_tendsto' ((Complex.continuous_re.tendsto _).comp
        (hconv A.toFun A.mem_continuousLocal.2.2)) fun i => hμA (κ i)
    exact Complex.le_def.2 ⟨hre, by rw [stateEval_im_eq_zero, stateEval_im_eq_zero]⟩
end FoldedStateBoundProof
end YangMills.Construction.NormalFamilies
