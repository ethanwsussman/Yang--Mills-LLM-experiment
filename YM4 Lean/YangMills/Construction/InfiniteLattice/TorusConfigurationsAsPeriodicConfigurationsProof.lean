import YangMills.Construction.InfiniteLattice.CoveringOnSitesBondsPlaquettesAndCorners
import YangMills.Construction.InfiniteLattice.CubicTorusOfACutoffIsAPeriodicExtensionProof
import YangMills.Construction.InfiniteLattice.TorusConfigurationsAsPeriodicConfigurations
import YangMills.Construction.InfiniteLattice.TorusLimitsArePeriodicGibbsStates
import YangMills.Construction.InfiniteLattice.TorusStatesAreTheVolumeLimitPointsProof
import YangMills.Construction.InfiniteLattice.TorusStatesAsPeriodicMeasures
import YangMills.Construction.InfiniteLattice.WeakLimitPointsAreLimitsOfSequences
import YangMills.Construction.InfiniteLattice.WeakLimitPointsOfExtensionsAreNonEmptyAndClosed
import YangMills.Construction.Lattice.WilsonWeightGaugeInvariance
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.InfiniteLattice.TorusFieldsAsPeriodic
section ContinuousIntegrands
variable {a : ℝ}
theorem compactSpace_gaugeField (a : ℝ) : CompactSpace (GaugeField a) := by apply _root_.YangMills.SharedProofs.p823 <;> assumption
theorem integrable_of_continuous_gaugeField {E : Type*} [NormedAddCommGroup E]
    (ν : Measure (GaugeField a)) [IsFiniteMeasure ν] {F : GaugeField a → E}
    (hF : Continuous F) : Integrable F ν := by
  have := compactSpace_gaugeField a
  exact hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)
theorem tendsto_integral_complex_of_weaklyConvergent {μ : ℕ → Measure (GaugeField a)}
    [∀ i, IsProbabilityMeasure (μ i)] {ν : Measure (GaugeField a)} [IsProbabilityMeasure ν]
    (h : CutoffLattice.WeaklyConvergent μ ν) {A : GaugeField a → ℂ} (hA : Continuous A) :
    Tendsto (fun i => ∫ U, A U ∂μ i) atTop (𝓝 (∫ U, A U ∂ν)) := by
  have hre := h ⟨fun U => (A U).re, Complex.continuous_re.comp hA⟩
  have him := h ⟨fun U => (A U).im, Complex.continuous_im.comp hA⟩
  have key : ∀ ρ : Measure (GaugeField a), ∀ [IsProbabilityMeasure ρ],
      ∫ U, A U ∂ρ = ((∫ U, (A U).re ∂ρ : ℝ) : ℂ) + ((∫ U, (A U).im ∂ρ : ℝ) : ℂ) * Complex.I := by
    intro ρ _
    exact (integral_re_add_im (𝕜 := ℂ) (integrable_of_continuous_gaugeField ρ hA)).symm
  simp only [key]
  exact ((Complex.continuous_ofReal.tendsto _).comp hre).add
    (((Complex.continuous_ofReal.tendsto _).comp him).mul_const _)
theorem weaklyConvergent_of_tendsto_integral_complex {μ : ℕ → Measure (GaugeField a)}
    {ν : Measure (GaugeField a)}
    (h : ∀ A : GaugeField a → ℂ, Continuous A →
      Tendsto (fun i => ∫ U, A U ∂μ i) atTop (𝓝 (∫ U, A U ∂ν))) :
    CutoffLattice.WeaklyConvergent μ ν := by
  intro F
  have hF := h (fun U => ((F U : ℝ) : ℂ)) (Complex.continuous_ofReal.comp F.continuous)
  have key : ∀ ρ : Measure (GaugeField a),
      ∫ U, ((F U : ℝ) : ℂ) ∂ρ = ((CutoffLattice.integralAgainst ρ F : ℝ) : ℂ) :=
    fun ρ => integral_ofReal
  simp only [key] at hF
  have := (Complex.continuous_re.tendsto _).comp hF
  simpa [Function.comp_def] using this
end ContinuousIntegrands
section Links
variable {L m K : ℕ}
theorem projectPoint_add (x y : LatticePoint (PeriodicLattice.meshSize L (K : ℤ))) :
    projectPoint L m (K : ℤ) (x + y) = projectPoint L m (K : ℤ) x + projectPoint L m (K : ℤ) y := by
  refine Subtype.ext (funext fun μ => ?_)
  simp [projectPoint, TorusMetric.torusProj]
theorem projectPoint_eq_iff (h : LatticeCovering.SitesCover L m K)
    (x y : LatticePoint (PeriodicLattice.meshSize L (K : ℤ))) :
    projectPoint L m (K : ℤ) x = projectPoint L m (K : ℤ) y ↔
      (y : AmbientSpace) - (x : AmbientSpace) ∈ latticeSubgroup (PeriodicLattice.torusSide L m) := by
  rw [← h.2.2.1 x y]
  exact Subtype.ext_iff
theorem exists_projectPoint_eq (h : LatticeCovering.SitesCover L m K)
    (y : PeriodicLattice.Site L m (K : ℤ)) :
    ∃ x : LatticePoint (PeriodicLattice.meshSize L (K : ℤ)), projectPoint L m (K : ℤ) x = y := by
  have hy : (y : PeriodicLattice.FourTorus L m) ∈
      CutoffLattice.torusCover L m '' (CutoffLattice.latticeAt L K : Set AmbientSpace) := by
    rw [h.2.2.2.2]
    exact y.2
  obtain ⟨x, hx, e⟩ := hy
  exact ⟨⟨x, hx⟩, Subtype.ext e⟩
theorem eq_zero_of_mem_latticeSubgroup {ℓ : ℝ} (hℓ : 0 < ℓ) {w : AmbientSpace}
    (hw : w ∈ latticeSubgroup ℓ) (hlt : ∀ μ, |w μ| < ℓ) : w = 0 := by
  obtain ⟨n, hn⟩ := hw
  funext μ
  have h := hlt μ
  rw [hn μ, abs_mul, abs_of_pos hℓ] at h
  have h1 : |(n μ : ℝ)| < 1 := by
    by_contra hc
    exact absurd h (not_lt.mpr (le_mul_of_one_le_left hℓ.le (not_lt.mp hc)))
  have h2 : |n μ| < 1 := by exact_mod_cast h1
  have h3 : n μ = 0 := Int.abs_lt_one_iff.mp h2
  simp [hn μ, h3]
theorem abs_apply_le_of_isAxisStep {a : ℝ} (ha : 0 ≤ a) {w : LatticePoint a}
    (hw : ∃ μ, w = axisStep a μ ∨ w = -axisStep a μ) (κ : Fin 4) :
    |(w : AmbientSpace) κ| ≤ a := by
  obtain ⟨μ, rfl | rfl⟩ := hw
  · by_cases h : κ = μ
    · subst h
      simp [axisStep, abs_of_nonneg ha]
    · simp [axisStep, Pi.single_eq_of_ne h, ha]
  · by_cases h : κ = μ
    · subst h
      simp [axisStep, abs_of_nonneg ha]
    · simp [axisStep, Pi.single_eq_of_ne h, ha]
theorem projectLink_surjective (h : LatticeCovering.SitesCover L m K)
    (c : PeriodicLattice.Bond L m (K : ℤ)) :
    ∃ b : Link (CutoffLattice.spacingAt L K), projectLink L m (K : ℤ) b = c := by
  obtain ⟨x, hx⟩ := exists_projectPoint_eq h c.source
  obtain ⟨μ, hμ | hμ⟩ := c.isNeighbour
  · refine ⟨⟨x, x + axisStep _ μ, μ, Or.inl (by abel)⟩, PeriodicLattice.Bond.ext hx ?_⟩
    change projectPoint L m (K : ℤ) (x + axisStep _ μ) = c.target
    rw [projectPoint_add, projectPoint_axisStep, hx, ← hμ]
    abel
  · refine ⟨⟨x, x - axisStep _ μ, μ, Or.inr (by abel)⟩, PeriodicLattice.Bond.ext hx ?_⟩
    change projectPoint L m (K : ℤ) (x - axisStep _ μ) = c.target
    rw [projectPoint_sub, projectPoint_axisStep, hx]
    have : c.target = c.source + (c.target - c.source) := by abel
    rw [this, hμ]
    abel
theorem projectLink_translateLink (h : LatticeCovering.SitesCover L m K)
    (b : Link (CutoffLattice.spacingAt L K)) (v : LatticePoint (CutoffLattice.spacingAt L K))
    (hv : (v : AmbientSpace) ∈ latticeSubgroup (PeriodicLattice.torusSide L m)) :
    projectLink L m (K : ℤ) b = projectLink L m (K : ℤ) (CutoffLattice.translateLink b v) := by
  refine PeriodicLattice.Bond.ext ?_ ?_
  · refine (projectPoint_eq_iff h _ _).mpr ?_
    simpa [CutoffLattice.translateLink] using hv
  · refine (projectPoint_eq_iff h _ _).mpr ?_
    simpa [CutoffLattice.translateLink] using hv
theorem exists_translate_of_projectLink_eq (h : LatticeCovering.SitesCover L m K)
    (hlt : 2 * CutoffLattice.spacingAt L K < PeriodicLattice.torusSide L m)
    (ha : 0 < CutoffLattice.spacingAt L K)
    {b b' : Link (CutoffLattice.spacingAt L K)}
    (e : projectLink L m (K : ℤ) b = projectLink L m (K : ℤ) b') :
    ∃ v : LatticePoint (CutoffLattice.spacingAt L K),
      (v : AmbientSpace) ∈ latticeSubgroup (PeriodicLattice.torusSide L m) ∧
        b' = CutoffLattice.translateLink b v := by
  have ht : (b'.initial : AmbientSpace) - (b.initial : AmbientSpace) ∈
      latticeSubgroup (PeriodicLattice.torusSide L m) :=
    (projectPoint_eq_iff h _ _).mp (congrArg PeriodicLattice.Bond.source e)
  have hh : (b'.terminal : AmbientSpace) - (b.terminal : AmbientSpace) ∈
      latticeSubgroup (PeriodicLattice.torusSide L m) :=
    (projectPoint_eq_iff h _ _).mp (congrArg PeriodicLattice.Bond.target e)
  have hdiff : ((b'.terminal - b'.initial : LatticePoint _) : AmbientSpace) -
      ((b.terminal - b.initial : LatticePoint _) : AmbientSpace) ∈
        latticeSubgroup (PeriodicLattice.torusSide L m) := by
    have := sub_mem hh ht
    convert this using 1
    push_cast
    abel
  have hzero := eq_zero_of_mem_latticeSubgroup (lt_trans (by positivity) hlt) hdiff (fun κ => by
    have h1 := abs_le.mp (abs_apply_le_of_isAxisStep ha.le b'.isAdjacent κ)
    have h2 := abs_le.mp (abs_apply_le_of_isAxisStep ha.le b.isAdjacent κ)
    rw [Pi.sub_apply, abs_lt]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2])
  have hw : b'.terminal - b'.initial = b.terminal - b.initial :=
    Subtype.ext (sub_eq_zero.mp hzero)
  refine ⟨b'.initial - b.initial, ht, Link.ext ?_ ?_⟩
  · change b'.initial = b.initial + (b'.initial - b.initial)
    abel
  · change b'.terminal = b.terminal + (b'.initial - b.initial)
    have : b'.terminal = b'.initial + (b.terminal - b.initial) := by
      rw [← hw]
      abel
    rw [this]
    abel
theorem projectionOnOrientedLinks_holds (h : LatticeCovering.SitesCover L m K)
    (hlt : 2 * CutoffLattice.spacingAt L K < PeriodicLattice.torusSide L m)
    (ha : 0 < CutoffLattice.spacingAt L K) : ProjectionOnOrientedLinks L m K :=
  ⟨fun b => projectLink_opposite b, projectLink_surjective h, fun _ _ =>
    ⟨fun e => exists_translate_of_projectLink_eq h hlt ha e, by
      rintro ⟨v, hv, rfl⟩
      exact projectLink_translateLink h _ v hv⟩⟩
theorem linkMap_shift {a : ℝ} (v : LatticePoint a) (b : Link a) :
    (shift v).linkMap b = CutoffLattice.translateLink b v :=
  Link.ext (Subtype.ext rfl) (Subtype.ext rfl)
theorem linkPeriodicFields_eq (L m K : ℕ) :
    linkPeriodicFields L m K = periodicFields L m (K : ℤ) := by
  ext U
  constructor
  · intro hU v hv
    refine Subtype.ext (funext fun b => ?_)
    change U ((shift v).linkMap b) = U b
    rw [linkMap_shift]
    exact hU b v hv
  · intro hU b v hv
    have h := congrArg (fun W : GaugeField _ => W b) (hU v hv)
    change U ((shift v).linkMap b) = U b at h
    rwa [linkMap_shift] at h
theorem liftOntoPeriodicFields_holds
    (h : BijOn (liftCompactField : PeriodicLattice.CompactGaugeField L m (K : ℤ) → _) univ
      (periodicFields L m (K : ℤ))) : LiftOntoPeriodicFields L m K := by
  refine ⟨fun U b => liftCompactField_apply U b, continuous_liftCompactField,
    injOn_univ.mp h.injOn, ?_, linkPeriodicFields_eq L m K⟩
  rw [linkPeriodicFields_eq, ← image_univ, h.image_eq]
theorem liftedWilsonMeasure_eq_preimage {β : ℝ}
    (hnull : PeriodicLattice.wilsonGibbsMeasure L m K β
      (PeriodicLattice.compactGaugeFields L m (K : ℤ))ᶜ = 0)
    {E : Set (CutoffLattice.FieldsAt L K)} (hE : MeasurableSet E) :
    liftedWilsonMeasure L m K β E =
      PeriodicLattice.wilsonGibbsMeasure L m K β
        {U | ∃ h : U ∈ PeriodicLattice.compactGaugeFields L m (K : ℤ),
          liftCompactField (⟨U, h⟩ : PeriodicLattice.CompactGaugeField L m (K : ℤ)) ∈ E} := by
  rw [liftedWilsonMeasure_apply L m K β hE]
  refine measure_congr ?_
  have hR : ∀ᵐ U ∂PeriodicLattice.wilsonGibbsMeasure L m K β,
      U ∈ PeriodicLattice.compactGaugeFields L m (K : ℤ) := by
    rw [ae_iff]
    exact hnull
  filter_upwards [hR] with U hU
  exact propext ⟨fun h => ⟨hU, h⟩, fun ⟨_, h⟩ => h⟩
end Links
section InfiniteVolumeLimits
theorem one_lt_blockingFactor (s : Conventions.StandingParameters) : (1 : ℝ) < s.L := by apply _root_.YangMills.Construction.InfiniteLattice.CubicTorusAtCutoffLifts.one_lt_L <;> assumption
theorem tendsto_torusSide_comp (s : Conventions.StandingParameters) {i : ℕ → ℕ}
    (hi : StrictMono i) :
    Tendsto (fun j => PeriodicLattice.torusSide s.L (i j)) atTop atTop :=
  ((tendsto_pow_atTop_atTop_of_one_lt (one_lt_blockingFactor s)).comp
    hi.tendsto_atTop).const_mul_atTop (by norm_num : (0 : ℝ) < 2)
theorem strictMono_torusSide_comp (s : Conventions.StandingParameters) {i : ℕ → ℕ}
    (hi : StrictMono i) : StrictMono fun j => PeriodicLattice.torusSide s.L (i j) :=
  fun _ _ h => mul_lt_mul_of_pos_left (pow_lt_pow_right₀ (one_lt_blockingFactor s) (hi h)) two_pos
variable (hT : TorusStatesAsPeriodic.Statement)
  (s : Conventions.StandingParameters) {β : ℝ} (hβ : 0 < β)
include hT hβ
theorem isProbabilityMeasure_liftedWilsonMeasure {n : ℕ} (hn : 0 < n) :
    IsProbabilityMeasure (liftedWilsonMeasure s.L n s.K β) :=
  (hT { s with m := ⟨n, hn⟩ } β hβ).2.1.1
def liftedStateAt {n : ℕ} (hn : 0 < n) :
    PeriodicExtensions.RealWeakState (PeriodicLattice.meshSize s.L (s.K : ℕ)) :=
  Subtype.mk (liftedWilsonMeasure s.L n s.K β)
    (isProbabilityMeasure_liftedWilsonMeasure hT s hβ hn)
variable (hN : PeriodicExtensions.LimitSetIsNonemptyClosed)
include hN in
theorem isInfiniteVolumeLimit_iff
    (ν : PeriodicExtensions.RealWeakState (PeriodicLattice.meshSize s.L (s.K : ℕ))) :
    IsInfiniteVolumeLimit s.L s.K β ν.measure ↔
      ν ∈ PeriodicExtensions.limitsOfLiftedMeasures s.L s.K β := by
  have := compactSpace_gaugeField (PeriodicLattice.meshSize s.L (s.K : ℕ))
  rw [(hN s β hβ).1]
  constructor
  · rintro ⟨-, φ, hφ, hF⟩
    have hpos : ∀ n, 1 ≤ φ (n + 1) := fun n => by
      have := hφ.le_apply (x := n + 1)
      omega
    refine ⟨fun n => φ (n + 1), fun n => liftedStateAt hT s hβ (hpos n),
      fun a b h => hφ (by omega), hpos, fun _ => rfl, fun F => ?_⟩
    exact (hF (BoundedContinuousFunction.mkOfCompact F)).comp (tendsto_add_atTop_nat 1)
  · rintro ⟨i, ρ, hi, -, hρ, hc⟩
    refine ⟨inferInstance, i, hi, fun F => ?_⟩
    have h : Tendsto (fun n => ∫ U, F U ∂(ρ n).measure) atTop (𝓝 (∫ U, F U ∂ν.measure)) :=
      hc F.toContinuousMap
    simpa only [hρ] using h
variable (hS : PeriodicExtensions.SequentialLimitCharacterization)
include hN hS in
theorem isWeakLimitAlongSides_iff
    (ν : PeriodicExtensions.RealWeakState (PeriodicLattice.meshSize s.L (s.K : ℕ))) :
    IsWeakLimitAlongSides s.L s.K β ν.measure ↔
      ν ∈ PeriodicExtensions.limitsOfLiftedMeasures s.L s.K β := by
  constructor
  · rintro ⟨-, n, hn, ht, hF⟩
    refine ((hS s.L s.K s.isAdmissible s.K.pos β hβ ν).1).mpr
      ⟨fun j => PeriodicLattice.torusSide s.L (n j), fun j => liftedStateAt hT s hβ (hn j),
        ⟨fun i _ => ⟨n i, hn i, rfl⟩, fun r => ?_⟩, fun i _ => ⟨n i, hn i, rfl, rfl⟩, ?_⟩
    · obtain ⟨N, hN'⟩ := eventually_atTop.mp (tendsto_atTop.mp ht r)
      exact (Set.finite_lt_nat N).subset fun i hi =>
        by_contra fun hc => hi.2 (hN' i (not_lt.mp hc))
    · exact weaklyConvergent_of_tendsto_integral_complex hF
  · intro hν
    rw [(hN s β hβ).1] at hν
    obtain ⟨i, ρ, hi, hi1, hρ, hc⟩ := hν
    refine ⟨inferInstance, i, fun j => hi1 j, tendsto_torusSide_comp s hi, fun F hF => ?_⟩
    have h := tendsto_integral_complex_of_weaklyConvergent (μ := fun j => (ρ j).measure) hc hF
    simpa only [hρ] using h
include hN in
theorem torusLimitsArePeriodicGibbs_holds (hP : TorusLimitsSubsetPeriodicGibbs) :
    TorusLimitsArePeriodicGibbs s.L s.K β := by
  refine ⟨(hN s β hβ).2.1, fun ν hν => hP s β hβ ?_⟩
  rw [(hN s β hβ).1] at hν
  obtain ⟨i, ρ, hi, hi1, hρ, hc⟩ := hν
  refine ⟨inferInstance, i, fun j => hi1 j, strictMono_torusSide_comp s hi, fun A hA => ?_⟩
  have h := tendsto_integral_complex_of_weaklyConvergent (μ := fun j => (ρ j).measure) hc hA
  simpa only [hρ] using h
end InfiniteVolumeLimits
theorem spacingAt_bounds (s : Conventions.StandingParameters) :
    0 < CutoffLattice.spacingAt s.L s.K ∧
      2 * CutoffLattice.spacingAt s.L s.K < PeriodicLattice.torusSide s.L s.m := by
  have h1 := one_lt_blockingFactor s
  have hpos : 0 < CutoffLattice.spacingAt s.L s.K := by
    simp only [CutoffLattice.spacingAt, PeriodicLattice.meshSize]
    exact zpow_pos (by linarith) _
  have hlt : CutoffLattice.spacingAt s.L s.K < 1 := by
    simp only [CutoffLattice.spacingAt, PeriodicLattice.meshSize, zpow_neg, zpow_natCast]
    exact inv_lt_one_of_one_lt₀ (one_lt_pow₀ h1 s.K.ne_zero)
  have hside : 1 < (s.L : ℝ) ^ (s.m : ℕ) := one_lt_pow₀ h1 s.m.ne_zero
  refine ⟨hpos, ?_⟩
  simp only [PeriodicLattice.torusSide]
  linarith
theorem statement_holds (hC : LatticeCovering.CoveringStatement)
    (hT : TorusStatesAsPeriodic.Statement)
    (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement)
    (hS : PeriodicExtensions.SequentialLimitCharacterization)
    (hN : PeriodicExtensions.LimitSetIsNonemptyClosed)
    (hP : TorusLimitsSubsetPeriodicGibbs) : Statement := by
  intro s β hβ
  have hL : 1 < s.L := by
    have := s.isAdmissible.2
    omega
  have hb := spacingAt_bounds s
  have hw := hW s.L s.m s.K β hL s.m.pos s.K.pos
  have ht := hT s β hβ
  exact ⟨projectionOnOrientedLinks_holds (hC s).1 hb.2 hb.1, liftOntoPeriodicFields_holds ht.1.2,
    ⟨ht.2.1.1, fun E hE => liftedWilsonMeasure_eq_preimage hw.2.2.2.2.2.2.2.2.1 hE⟩,
    fun ν => ⟨isInfiniteVolumeLimit_iff hT s hβ hN ν, isWeakLimitAlongSides_iff hT s hβ hN hS ν⟩,
    torusLimitsArePeriodicGibbs_holds hT s hβ hN hP⟩
end YangMills.Construction.InfiniteLattice.TorusFieldsAsPeriodic
