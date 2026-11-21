import YangMills.Construction.InfiniteLattice.CovarianceOfTheMeasuresOfATorus
import YangMills.Construction.InfiniteLattice.CoveringOnBondsAndPlaquettesProof
import YangMills.Construction.InfiniteLattice.CubicToriAmongTheToriOfAnyShapeProof
import YangMills.Construction.InfiniteLattice.FunctionsOfTheBondsOfASetAndSupports
import YangMills.Construction.InfiniteLattice.InfiniteVolumeLimitPointsOfTheTorusStates
import YangMills.Construction.InfiniteLattice.PeriodicGibbsStatesUnderTheDilation
import YangMills.Construction.InfiniteLattice.TheSpaceOfConfigurationsAndTheSpaceOfMeasures
import YangMills.Construction.InfiniteLattice.ToriOfAnyShapeAndPerturbedWeights
import YangMills.Construction.InfiniteLattice.WeakLimitsInvariantFunctionsAndACriterionForErgodicity
import YangMills.Construction.ReflectionPositivity.PositivityOfTheWilsonMeasureAtALinkMirror
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Set
open scoped Topology ComplexOrder
noncomputable section
namespace YangMills.Construction.InfiniteLattice.LimitPointsOfTorusStates
open GibbsAtFixedSpacing TestFunctions LatticeConventions
open LatticeConventions.NormalHyperplane (reflectSymmetry)
theorem tendsto_nhds_of_tendstoWeak {a : ℝ} {ν : ℕ → BorelProb a} {μ : BorelProb a}
    (h : BorelProb.TendstoWeak ν μ) : Tendsto ν atTop (𝓝 μ) := by
  change Tendsto ν atTop (@nhds _ (⨅ F : continuousFns a,
    TopologicalSpace.induced (fun ν : BorelProb a => ν.integral F.1) inferInstance) μ)
  rw [nhds_iInf, tendsto_iInf]
  intro F
  rw [nhds_induced, tendsto_comap_iff]
  exact h F.1 F.2
theorem tendstoWeak_of_tendsto_nhds {a : ℝ} {ν : ℕ → BorelProb a} {μ : BorelProb a}
    (h : Tendsto ν atTop (𝓝 μ)) : BorelProb.TendstoWeak ν μ := by
  intro F hF
  have hc : Continuous fun ν : BorelProb a => ν.integral F :=
    continuous_iInf_dom (i := (⟨F, hF⟩ : continuousFns a)) continuous_induced_dom
  exact (hc.tendsto μ).comp h
def trivialArray (a : ℝ) : SingleGeneratorArray a where
  sublattice := ⊤
  sublattice_finiteIndex := inferInstance
  gen := fun _ => 0
  gen_mem := ⟨continuous_const, ⟨measurable_const, 0, by simp⟩,
    ⟨∅, Bornology.isBounded_empty, measurable_const⟩⟩
def standingParams {L K m : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hK : 0 < K)
    (hm : 0 < m) : Conventions.StandingParameters := ⟨L, hL, ⟨K, hK⟩, ⟨m, hm⟩⟩
theorem one_lt_blockingFactor {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) :
    (1 : ℝ) < L := by apply _root_.YangMills.Construction.InfiniteLattice.Covering.one_lt_factor <;> assumption
theorem tendsto_torusSide_succ {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) :
    Tendsto (fun i : ℕ => PeriodicLattice.torusSide L (i + 1)) atTop atTop := by
  unfold PeriodicLattice.torusSide
  exact (tendsto_pow_atTop_atTop_of_one_lt (one_lt_blockingFactor hL)).comp
    (tendsto_add_atTop_nat 1) |>.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
variable {L K : ℕ} {β : ℝ}
theorem refinedSpacing_pos (hL : Conventions.IsAdmissibleBlockingFactor L) :
    0 < refinedSpacing L K :=
  CutoffLattice.spacingAt_pos hL K
theorem exists_cubicPeriodSublattice (Hcub : CubicTorusAsQuotient.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hK : 0 < K) (hβ : 0 < β) {m : ℕ}
    (hm : 0 < m) :
    ∃ Γ : PeriodSublattice (refinedSpacing L K),
      Γ.HasCubicPeriods (PeriodicLattice.torusSide L m) ∧
      CubicPeriodSublatticeProperties Γ (PeriodicLattice.torusSide L m) ∧
      QuotientByCubicPeriodsIsPeriodicLattice L m K β Γ := by
  obtain ⟨⟨Γ, hΓ⟩, h2, -, -⟩ := Hcub (standingParams hL hK hm) β hβ
  obtain ⟨h3, h4⟩ := h2 Γ hΓ
  exact ⟨Γ, hΓ, h3, h4⟩
theorem isProbabilityMeasure_liftedWilsonMeasure
    (Hww : PeriodicLattice.WilsonWeightGaugeInvariance.statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hK : 0 < K) (β : ℝ) {m : ℕ} (hm : 0 < m) :
    IsProbabilityMeasure (liftedWilsonMeasure L m K β) := by
  have h1 : 1 < L := by have := hL.2; omega
  have hp : IsProbabilityMeasure (PeriodicLattice.wilsonGibbsMeasure L m K β) :=
    (Hww L m K β h1 hm hK).2.2.2.2.2.2.2.1
  exact Measure.isProbabilityMeasure_map (measurable_liftField L m _).aemeasurable
structure AlongSideSequence (L K : ℕ) (β : ℝ) (ρ : ℕ → BorelProb (refinedSpacing L K)) :
    Prop where
  subseq_limit : ∀ φ : ℕ → ℕ, StrictMono φ → (∀ k, 1 ≤ φ k) →
    ∃ ν, BorelProb.IsSubseqWeakLimit (ρ ∘ φ) ν
  gibbs_shift : ∀ ν, BorelProb.IsSubseqWeakLimit ρ ν → IsGibbs β ν.1 ∧ IsShiftInvariant ν.1
  motion_invariant : ∀ (r : LatticeSymmetry (refinedSpacing L K)),
    r.toFun ∈ affineHyperoctahedralMaps (refinedSpacing L K) → ∀ i, IsSymmetricUnder (ρ i).1 r
  mirror_positive : ∀ (P : NormalHyperplane) (hP : P.IsLatticeMirror (refinedSpacing L K)),
    (∀ F, Continuous F → F ∈ locallyMeasurableIn (refinedSpacing L K) P.upperHalfSpace →
      ∃ i₀ : ℕ, ∀ i, 1 ≤ i → i₀ ≤ i → 0 ≤ reflectedPairing hP (ρ i) F) →
    ∀ ν, BorelProb.IsSubseqWeakLimit ρ ν → IsSymmetricUnder ν.1 (reflectSymmetry hP) →
      IsFullyReflectionPositive hP ν
theorem alongSideSequence (Hany : GibbsAtFixedSpacing.TiltedTorusLimits)
    (Hcub : CubicTorusAsQuotient.Statement)
    (Htor : GibbsAtFixedSpacing.TorusMeasureCovariance)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hK : 0 < K) (hβ : 0 < β) {m : ℕ → ℕ}
    (hm : SideExponentsTendToInfinity L m) {ρ : ℕ → BorelProb (refinedSpacing L K)}
    (hρ : ∀ i, (ρ i).1 = liftedWilsonMeasure L (m i) K β) : AlongSideSequence L K β ρ := by
  choose Γ h1 h2 h3 using fun i => exists_cubicPeriodSublattice Hcub hL hK hβ (hm.1 i)
  have ht : Tendsto (fun i => minPeriodNorm (Γ i)) atTop atTop := by
    have : (fun i => minPeriodNorm (Γ i)) = fun i => PeriodicLattice.torusSide L (m i) :=
      funext fun i => (h2 i).minPeriodNorm_eq
    rw [this]
    exact hm.2
  have hρ' : ∀ i, (ρ i).1 = (Γ i).liftedGibbsMeasure β := fun i => by
    rw [hρ i, (h3 i).liftedGibbsMeasure_eq]
  have H := ((Hany L K hL hK β hβ (trivialArray _)).2 0 Γ (fun _ _ => le_top) ht).2 ρ
    (fun i _ => (hρ' i).trans (SingleGeneratorArray.liftedTiltMeasure_zero _ _ _).symm)
  obtain ⟨Ha, -, -, -, Hb, -, -, Hd⟩ := H
  refine ⟨Ha, fun ν hν => Hb ρ (fun i _ => hρ' i) ν hν, ?_, ?_⟩
  · rintro r ⟨w, hw, v, hr⟩ i
    rw [hρ']
    refine ((Htor _ β (refinedSpacing_pos hL) hβ (trivialArray _) 0 (Γ i)
      (le_top)).2.1 r w ⟨hw, v, hr⟩ ?_).2
    change (fun x => w x) '' (Subtype.val '' _) = _
    have hc : (fun γ : LatticePoint (refinedSpacing L K) => (γ : AmbientSpace)) ''
        ((Γ i).periods : Set _) = cubicPeriodSet (PeriodicLattice.torusSide L (m i)) := h1 i
    change (fun x => w x) '' ((fun γ : LatticePoint (refinedSpacing L K) => (γ : AmbientSpace)) '' _) =
      (fun γ : LatticePoint (refinedSpacing L K) => (γ : AmbientSpace)) '' _
    rw [hc]
    exact (h2 i).image_cubicPeriodSet w hw
  · intro P hP h ν hν hinv
    exact (Hd P hP h ν hν).2 hinv
theorem isSubseqWeakLimit_of_tendstoWeak {a : ℝ} {ρ : ℕ → BorelProb a} {ν : BorelProb a}
    (h : BorelProb.TendstoWeak ρ ν) : BorelProb.IsSubseqWeakLimit ρ ν :=
  ⟨Nat.succ, strictMono_nat_of_lt_succ fun _ => Nat.lt_succ_self _,
    fun k => Nat.succ_le_succ (Nat.zero_le k),
    fun F hF => (h F hF).comp (tendsto_add_atTop_nat 1)⟩
theorem limitSet_closed_nonempty (Hany : GibbsAtFixedSpacing.TiltedTorusLimits)
    (Hcub : CubicTorusAsQuotient.Statement)
    (Htor : GibbsAtFixedSpacing.TorusMeasureCovariance)
    (Htop : GibbsAtFixedSpacing.SpacesOfFieldsAndMeasures.FieldAndMeasureSpaceProperties)
    (Hww : PeriodicLattice.WilsonWeightGaugeInvariance.statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hK : 0 < K) (hβ : 0 < β) :
    LimitSetClosedNonemptyAndSubseqConvergent L K β := by
  have hsub : ∀ m : ℕ → ℕ, SideExponentsTendToInfinity L m →
      ∃ (φ : ℕ → ℕ) (ν : BorelProb (refinedSpacing L K)), StrictMono φ ∧
        LiftedMeasuresTendstoWeakly L K β (m ∘ φ) ν := by
    intro m hm
    let ρ : ℕ → BorelProb (refinedSpacing L K) := fun i =>
      (⟨liftedWilsonMeasure L (m i) K β,
        isProbabilityMeasure_liftedWilsonMeasure Hww hL hK β (hm.1 i)⟩ :
        GaugeFieldProbability _)
    have C := alongSideSequence Hany Hcub Htor hL hK hβ hm (ρ := ρ) (fun _ => rfl)
    have hs : StrictMono Nat.succ := strictMono_nat_of_lt_succ fun _ => Nat.lt_succ_self _
    obtain ⟨ν, ψ, hψ, -, hν⟩ := C.subseq_limit Nat.succ hs
      (fun k => Nat.succ_le_succ (Nat.zero_le k))
    exact ⟨Nat.succ ∘ ψ, ν, hs.comp hψ, ρ ∘ (Nat.succ ∘ ψ), fun _ => rfl, hν⟩
  refine ⟨?_, ?_, hsub⟩
  · have hm : SideExponentsTendToInfinity L (fun i => i + 1) :=
      ⟨fun i => Nat.succ_pos i, tendsto_torusSide_succ hL⟩
    obtain ⟨φ, ν, hφ, ρ, hρ, hν⟩ := hsub _ hm
    exact ⟨ν, _, ρ, fun i => Nat.succ_pos _, (tendsto_torusSide_succ hL).comp hφ.tendsto_atTop,
      hρ, hν⟩
  · have hmet := (Htop _ (refinedSpacing_pos (K := K) hL)).2.2.1.2
    let _ := TopologicalSpace.metrizableSpaceMetric (BorelProb (refinedSpacing L K))
    apply IsSeqClosed.isClosed
    intro νk ν hν hlim
    have key : ∀ j : ℕ, ∃ (n : ℕ) (q : BorelProb (refinedSpacing L K)), 0 < n ∧
        (j : ℝ) ≤ PeriodicLattice.torusSide L n ∧ q.1 = liftedWilsonMeasure L n K β ∧
        dist (νk j) q < 1 / ((j : ℝ) + 1) := by
      intro j
      obtain ⟨m, ρ, hm, ht, hρ, hc⟩ := hν j
      have h1 := (tendsto_nhds_of_tendstoWeak hc)
      have h2 : ∀ᶠ i in atTop, dist (νk j) (ρ i) < 1 / ((j : ℝ) + 1) := by
        have := (Metric.tendsto_nhds.1 h1) (1 / ((j : ℝ) + 1)) (by positivity)
        filter_upwards [this] with i hi
        rwa [dist_comm]
      obtain ⟨i, hi1, hi2⟩ := ((ht.eventually_ge_atTop (j : ℝ)).and h2).exists
      exact ⟨m i, ρ i, hm i, hi1, hρ i, hi2⟩
    choose n q hn hj hq hd using key
    refine ⟨n, q, hn, ?_, hq, ?_⟩
    · exact tendsto_atTop_mono hj tendsto_natCast_atTop_atTop
    · refine tendstoWeak_of_tendsto_nhds (tendsto_of_tendsto_of_dist hlim ?_)
      exact squeeze_zero (fun _ => dist_nonneg) (fun j => (hd j).le)
        tendsto_one_div_add_atTop_nhds_zero_nat
open ReflectionPositivity.CutoffMirrors (MirrorData LinkLevel SlabSide)
theorem axial_reflect_eq (μ : Direction) (c : ℝ) (x : AmbientSpace) :
    (NormalHyperplane.axial μ c).reflect x =
      x - (2 * (x μ - c)) • PeriodicLattice.coordVec μ := by
  have h1 : euclidNorm (_root_.YangMills.Construction.LatticeConventions.basisVector μ) ^ 2 = 1 := by
    rw [euclidNorm_sq_eq_dotProduct]
    exact (euclidDot_basisVector μ (_root_.YangMills.Construction.LatticeConventions.basisVector μ)).trans (by simp [_root_.YangMills.Construction.LatticeConventions.basisVector])
  have h2 : PeriodicLattice.coordVec μ = _root_.YangMills.Construction.LatticeConventions.basisVector μ := rfl
  simp only [NormalHyperplane.reflect, NormalHyperplane.axial, h1, h2,
    euclidDot_basisVector, div_one]
section SingleCutoff
variable {D : MirrorData} (C : LinkLevel D)
theorem reflectedEdge_projectLink
    (hP : (NormalHyperplane.axial D.dir C.pos).IsLatticeMirror
      (PeriodicLattice.meshSize D.L ((D.K : ℕ) : ℤ)))
    (b : Link (PeriodicLattice.meshSize D.L ((D.K : ℕ) : ℤ))) :
    C.reflectedEdge (projectLink D.L D.m ((D.K : ℕ) : ℤ) b) =
      projectLink D.L D.m ((D.K : ℕ) : ℤ) ((reflectSymmetry hP).linkMap b) := by
  have hsite : ∀ x : LatticePoint (PeriodicLattice.meshSize D.L ((D.K : ℕ) : ℤ)),
      ((projectPoint D.L D.m ((D.K : ℕ) : ℤ) ((reflectSymmetry hP).pointMap x) : _) : D.Torus) =
        C.refl (projectPoint D.L D.m ((D.K : ℕ) : ℤ) x : _) := by
    intro x
    have h := congrFun (D.induces_reflect C.pos) (x : AmbientSpace)
    simp only [Function.comp_apply, MirrorData.reflectVec_eq_sub] at h
    refine Eq.trans ?_ h.symm
    change D.proj ((NormalHyperplane.axial D.dir C.pos).reflect x) = _
    rw [axial_reflect_eq]
  have hI : C.IsReflectedEdge (projectLink D.L D.m ((D.K : ℕ) : ℤ) b)
      (projectLink D.L D.m ((D.K : ℕ) : ℤ) ((reflectSymmetry hP).linkMap b)) :=
    ⟨hsite b.initial, hsite b.terminal⟩
  have h : ∃ b', C.IsReflectedEdge (projectLink D.L D.m ((D.K : ℕ) : ℤ) b) b' := ⟨_, hI⟩
  have e : C.reflectedEdge (projectLink D.L D.m ((D.K : ℕ) : ℤ) b) = h.choose := dif_pos h
  rw [e]
  exact PeriodicLattice.Bond.ext (Subtype.ext (h.choose_spec.1.trans hI.1.symm))
    (Subtype.ext (h.choose_spec.2.trans hI.2.symm))
theorem pullbackField_liftCompactField
    (hP : (NormalHyperplane.axial D.dir C.pos).IsLatticeMirror
      (PeriodicLattice.meshSize D.L ((D.K : ℕ) : ℤ))) (U : D.FieldSpace) :
    (reflectSymmetry hP).pullbackField (liftCompactField U) =
      liftCompactField (C.reflectField U) := by
  refine Subtype.ext (funext fun b => ?_)
  change liftCompactField U ((reflectSymmetry hP).linkMap b) =
    liftCompactField (C.reflectField U) b
  refine (liftCompactField_apply (L := D.L) (m := D.m) U _).trans ?_
  refine Eq.trans ?_ (liftCompactField_apply (L := D.L) (m := D.m)
    (C.reflectField U) b).symm
  rw [← reflectedEdge_projectLink C hP b]
  exact Subtype.ext rfl
theorem projectPoint_mem_halfVertices
    (x : LatticePoint (PeriodicLattice.meshSize D.L ((D.K : ℕ) : ℤ)))
    (h₁ : C.pos ≤ (x : AmbientSpace) D.dir) (h₂ : (x : AmbientSpace) D.dir < C.pos + D.side / 2) :
    ((projectPoint D.L D.m ((D.K : ℕ) : ℤ) x : _) : D.Torus) ∈ C.halfVertices SlabSide.pos := by
  refine ⟨(projectPoint D.L D.m ((D.K : ℕ) : ℤ) x).2, (x : AmbientSpace), ?_, rfl⟩
  obtain ⟨n, hn⟩ := C.isLinkLevel
  obtain ⟨k, hk⟩ := x.2
  have hne : (x : AmbientSpace) D.dir ≠ C.pos := by
    intro h
    have ha : D.spacing ≠ 0 := by
      have : 0 < PeriodicLattice.meshSize D.L ((D.K : ℕ) : ℤ) := by
        have h0 : (0 : ℝ) < D.L := by
          have := D.isAdmissible.2
          exact_mod_cast (by omega : 0 < D.L)
        exact zpow_pos h0 _
      exact this.ne'
    have h3 : (k D.dir : ℝ) * D.spacing = D.spacing * ((n : ℝ) + 1 / 2) := by
      rw [← hn, ← h]
      exact (hk D.dir).symm
    have h4 : (k D.dir : ℝ) = (n : ℝ) + 1 / 2 := by
      apply mul_right_cancel₀ ha
      rw [h3]
      ring
    have h5 : (2 * k D.dir : ℤ) = 2 * n + 1 := by
      have : (2 * (k D.dir : ℝ)) = 2 * n + 1 := by rw [h4]; ring
      exact_mod_cast this
    omega
  have hlt : C.pos < (x : AmbientSpace) D.dir := lt_of_le_of_ne h₁ (Ne.symm hne)
  simp only [SlabSide.toReal, one_mul, Set.mem_ofPred_eq]
  constructor <;> linarith
theorem reflectedPairing_nonneg
    (Hfac : GibbsAtFixedSpacing.LinkFunctions.Assertion)
    (Hpos : ReflectionPositivity.CutoffMirrors.LinkPositivity.ReflectionPositivityAtLink)
    (Hww : PeriodicLattice.WilsonWeightGaugeInvariance.statement)
    (hP : (NormalHyperplane.axial D.dir C.pos).IsLatticeMirror
      (PeriodicLattice.meshSize D.L ((D.K : ℕ) : ℤ)))
    {ρ : BorelProb (PeriodicLattice.meshSize D.L ((D.K : ℕ) : ℤ))}
    (hρ : ρ.1 = liftedWilsonMeasure D.L D.m D.K D.coupling)
    {F : GaugeField (PeriodicLattice.meshSize D.L ((D.K : ℕ) : ℤ)) → ℂ} (hFc : Continuous F)
    {S : Set AmbientSpace}
    (hF : F ∈ boundedMeasurableIn (PeriodicLattice.meshSize D.L ((D.K : ℕ) : ℤ)) S)
    (hS : S ⊆ (NormalHyperplane.axial D.dir C.pos).upperHalfSpace)
    (hR : ∀ x ∈ S, x D.dir < C.pos + D.side / 2) : 0 ≤ reflectedPairing hP ρ F := by
  have h0 : (0 : ℝ) < D.L := by
    have := D.isAdmissible.2
    exact_mod_cast (by omega : 0 < D.L)
  have ha : 0 < PeriodicLattice.meshSize D.L ((D.K : ℕ) : ℤ) := zpow_pos h0 _
  obtain ⟨hFm, B, hB⟩ := hF
  obtain ⟨hfa, hfb, -, -⟩ := Hfac _ ha
  have h𝓢 : positiveLinksWithin _ S ⊆
      positiveLinkSet (PeriodicLattice.meshSize D.L ((D.K : ℕ) : ℤ)) := inter_subset_left
  obtain ⟨tfae, hfactor⟩ := hfb _ h𝓢 F ⟨B, hB⟩
  have hm' : Measurable[linkSigma (positiveLinksWithin _ S)] F := by
    rw [← hfa.2.2.2.2 S]
    exact hFm
  obtain ⟨f, hf⟩ := (tfae.out 0 2).1 hm'
  have hfc : Continuous f := (hfactor f hf).2.2 hFc
  obtain ⟨-, ⟨Bf, hBf⟩, hFf⟩ := hf
  have hmem : ∀ b : positiveLinksWithin
      (PeriodicLattice.meshSize D.L ((D.K : ℕ) : ℤ)) S,
      projectLink D.L D.m ((D.K : ℕ) : ℤ) b.1 ∈ C.halfEdges SlabSide.pos := by
    rintro ⟨b, hb, ht, hh⟩
    have hside : ∀ x : LatticePoint (PeriodicLattice.meshSize D.L ((D.K : ℕ) : ℤ)),
        (x : AmbientSpace) ∈ S → C.pos ≤ (x : AmbientSpace) D.dir := fun x hx => by
      have := hS hx
      simpa [NormalHyperplane.upperHalfSpace, NormalHyperplane.axial,
        euclidDot_basisVector] using this
    obtain ⟨κ, h⟩ := mem_positiveLinks_iff.1 hb
    refine ⟨⟨κ, ?_⟩, projectPoint_mem_halfVertices C _ (hside _ ht) (hR _ ht),
      projectPoint_mem_halfVertices C _ (hside _ hh) (hR _ hh)⟩
    change projectPoint _ _ _ b.terminal - projectPoint _ _ _ b.initial = _
    rw [← projectPoint_sub, h, projectPoint_axisStep]
  let Ψ : D.FieldSpace → ℂ := fun U => F (liftCompactField U)
  have hΨ : Ψ ∈ C.halfAlgebra SlabSide.pos := by
    refine ⟨fun g => f fun b => g ⟨_, hmem b⟩, ?_, ⟨Bf, fun _ => hBf _⟩, ?_⟩
    · have hcont : Continuous fun g : C.halfEdges SlabSide.pos →
          Matrices.ComplexMatrix2.specialUnitary => f fun b => g ⟨_, hmem b⟩ :=
        hfc.comp (continuous_pi fun b =>
          continuous_apply (⟨_, hmem b⟩ : C.halfEdges SlabSide.pos))
      let _ : MeasurableSpace (C.halfEdges SlabSide.pos → Matrices.ComplexMatrix2.specialUnitary) :=
        borel (C.halfEdges SlabSide.pos → Matrices.ComplexMatrix2.specialUnitary)
      have : BorelSpace (C.halfEdges SlabSide.pos → Matrices.ComplexMatrix2.specialUnitary) :=
        ⟨rfl⟩
      exact hcont.measurable
    · funext U
      change F _ = f _
      rw [hFf]
      congr 1
      funext b
      exact (liftCompactField_apply U b.1).trans (Subtype.ext rfl)
  have hnn : 0 ≤ C.thetaForm Ψ Ψ := ((Hpos D C).2.1.2.2.1) Ψ hΨ
  have hdk : 1 < D.L := by have := D.isAdmissible.2; omega
  have hnull := (Hww D.L D.m D.K D.coupling hdk D.m.pos D.K.pos).2.2.2.2.2.2.2.2
  have hae : ∀ᵐ U ∂PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.coupling,
      U ∈ PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ) := mem_ae_iff.2 hnull.1
  have hval : Continuous fun U : GaugeField (PeriodicLattice.meshSize D.L ((D.K : ℕ) : ℤ)) =>
      (U : Link _ → Matrices.ComplexMatrix2.specialUnitary) := continuous_subtype_val
  have hrc : Continuous (reflectSymmetry hP).pullbackField := by
    refine continuous_induced_rng (f := (Subtype.val : {U : Link (PeriodicLattice.meshSize D.L
      ((D.K : ℕ) : ℤ)) → Matrices.ComplexMatrix2.specialUnitary //
        ∀ b, U b.opposite = (U b)⁻¹} → _)).2 ?_
    exact continuous_pi fun b =>
      (continuous_apply ((reflectSymmetry hP).linkMap b)).comp hval
  have hG : Continuous fun U : GaugeField (PeriodicLattice.meshSize D.L ((D.K : ℕ) : ℤ)) =>
      conjFun ((reflectSymmetry hP).actOn F) U * F U :=
    (Complex.continuous_conj.comp (hFc.comp hrc)).mul hFc
  have heq : reflectedPairing hP ρ F = C.thetaForm Ψ Ψ := by
    change ∫ U, conjFun ((reflectSymmetry hP).actOn F) U * F U ∂ρ.1 = _
    rw [hρ, liftedWilsonMeasure, integral_map (measurable_liftField _ _ _).aemeasurable
      hG.aestronglyMeasurable]
    refine integral_congr_ae ?_
    filter_upwards [hae] with U hU
    rw [dif_pos hU]
    change starRingEnd ℂ (F ((reflectSymmetry hP).pullbackField
      (liftCompactField ⟨U, hU⟩))) * F (liftCompactField ⟨U, hU⟩) = _
    rw [pullbackField_liftCompactField C hP]
  rw [heq]
  exact hnn
end SingleCutoff
def mirrorDataOf (hL : Conventions.IsAdmissibleBlockingFactor L) (hK : 0 < K) (hβ : 0 < β)
    {m : ℕ} (hm : 0 < m) (μ : Direction) : MirrorData :=
  { standingParams hL hK hm with coupling := β, coupling_pos := hβ, dir := μ }
theorem isSymmetricReflPosGibbs_of_mem (Hany : GibbsAtFixedSpacing.TiltedTorusLimits)
    (Hcub : CubicTorusAsQuotient.Statement)
    (Htor : GibbsAtFixedSpacing.TorusMeasureCovariance)
    (Hweak : GibbsAtFixedSpacing.LimitsAndErgodicity.Statement)
    (Hdil : GibbsAtFixedSpacing.PeriodicGibbsUnderRescaling.Statement)
    (Hfac : GibbsAtFixedSpacing.LinkFunctions.Assertion)
    (Hpos : ReflectionPositivity.CutoffMirrors.LinkPositivity.ReflectionPositivityAtLink)
    (Hww : PeriodicLattice.WilsonWeightGaugeInvariance.statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hK : 0 < K) (hβ : 0 < β)
    {ν : BorelProb (refinedSpacing L K)} (hν : ν ∈ cubicTorusLimitStates L K β) :
    IsSymmetricReflPosGibbs L K β ν := by
  obtain ⟨m, ρ, hm, ht, hρ, hc⟩ := hν
  have ha : 0 < refinedSpacing L K := refinedSpacing_pos hL
  have C := alongSideSequence Hany Hcub Htor hL hK hβ ⟨hm, ht⟩ hρ
  have hW := isSubseqWeakLimit_of_tendstoWeak hc
  obtain ⟨hG, hT⟩ := C.gibbs_shift ν hW
  have hkeep := (Hweak _ ha).1
  have hinv : ∀ r : LatticeSymmetry (refinedSpacing L K),
      r.toFun ∈ affineHyperoctahedralMaps (refinedSpacing L K) → IsSymmetricUnder ν.1 r :=
    fun r hr => hkeep ρ ν r hc (C.motion_invariant r hr)
  have hrefl : ∀ (Q : NormalHyperplane) (hQ : Q.IsLatticeMirror (refinedSpacing L K)),
      IsSymmetricUnder ν.1 (reflectSymmetry hQ) := fun Q hQ =>
    hinv _ ((Hdil _ β ha hβ).2.2.2.1 Q hQ)
  refine ⟨hG, hinv, hT, ?_, fun μ c h => hrefl _ _, ⟨hG, ⊤, inferInstance, fun v _ => hT v⟩, ?_⟩
  · rintro r ⟨w, hw, hr⟩
    refine hinv r ⟨w, hw, 0, ?_⟩
    rw [hr]
    funext x
    simp [latticeMotion]
  · intro μ c h
    refine C.mirror_positive _ _ ?_ ν hW (hrefl _ _)
    intro F hFc hF
    simp only [locallyMeasurableIn, mem_iUnion] at hF
    obtain ⟨Q, hQ, hFQ⟩ := hF
    obtain ⟨R, hR⟩ := (Bornology.IsBounded.subset_closedBall
      (show Bornology.IsBounded Q from hQ) (0 : AmbientSpace))
    obtain ⟨i₀, hi₀⟩ := eventually_atTop.1 (ht.eventually_gt_atTop (2 * (R - c)))
    refine ⟨i₀, fun i _ hi => ?_⟩
    obtain ⟨q, hq⟩ := h
    let D : MirrorData := mirrorDataOf hL hK hβ (hm i) μ
    let Cp : LinkLevel D := ⟨c, q, by rw [hq]; exact mul_comm _ _⟩
    refine reflectedPairing_nonneg Cp Hfac Hpos Hww _ (hρ i) hFc hFQ inter_subset_left ?_
    intro x hx
    have h1 : ‖x‖ ≤ R := by simpa using hR hx.2
    have h2 : x μ ≤ ‖x‖ := (le_abs_self _).trans (norm_le_pi_norm x μ)
    have h3 := hi₀ i hi
    change x μ < c + PeriodicLattice.torusSide L (m i) / 2
    linarith
theorem euclidNormVec_le_two_mul_norm (v : AmbientSpace) :
    TorusMetric.euclidNormVec v ≤ 2 * ‖v‖ := by apply _root_.YangMills.SharedProofs.p8643 <;> assumption
theorem exists_hasDiameterLE {A : Set AmbientSpace} (hA : Bornology.IsBounded A) :
    ∃ D : ℝ, HasDiameterLE A D := by
  obtain ⟨R, hR⟩ := hA.subset_closedBall (0 : AmbientSpace)
  refine ⟨2 * (R + R), fun x hx y hy => (euclidNormVec_le_two_mul_norm _).trans ?_⟩
  have h1 : ‖x‖ ≤ R := by simpa using hR hx
  have h2 : ‖y‖ ≤ R := by simpa using hR hy
  have := norm_sub_le x y
  linarith
theorem hasDiameterLE_mono {A : Set AmbientSpace} {D D' : ℝ} (h : HasDiameterLE A D)
    (hD : D ≤ D') : HasDiameterLE A D' := fun x hx y hy => (h x hx y hy).trans hD
theorem continuous_of_isLipschitzFor {f : AmbientSpace → ℝ} (h : IsLipschitzFor euclidDist f) :
    Continuous f := by apply _root_.YangMills.Construction.InfiniteLattice.CubicTorusAsQuotient.continuous_of_isLipschitzFor <;> assumption
theorem localQuantitiesTendsto (Hcub : CubicTorusAsQuotient.Statement)
    (Hcum : GibbsAtFixedSpacing.CumulantsPolynomialInMomentsAndWeakLimits)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hK : 0 < K) (hβ : 0 < β) {m : ℕ → ℕ}
    (hm : SideExponentsTendToInfinity L m) {ν : BorelProb (refinedSpacing L K)}
    (hν : LiftedMeasuresTendstoWeakly L K β m ν) : LocalQuantitiesTendsto L K β m ν := by
  obtain ⟨ρ, hρ, hc⟩ := hν
  have ha : 0 < refinedSpacing L K := refinedSpacing_pos hL
  have hint : ∀ (F : GaugeField (refinedSpacing L K) → ℂ) (i : ℕ),
      (ρ i).integral F = ∫ U, F U ∂liftedWilsonMeasure L (m i) K β := fun F i => by
    change ∫ U, F U ∂(ρ i).1 = _
    rw [hρ]
  have hS : ∀ i, PlaquetteSmearingUnderProjection L (m i) K β := fun i =>
    (Hcub (standingParams hL hK (hm.1 i)) β hβ).2.2.2
  refine ⟨fun F hF => (hc F hF.2.2).congr (hint F), ?_, ?_⟩
  · intro f hfb hfs
    obtain ⟨D, hD⟩ := exists_hasDiameterLE hfs
    have hev : ∀ᶠ i in atTop, ∃ A : Set AmbientSpace,
        HasDiameterLE A (PeriodicLattice.torusSide L (m i) / 2) ∧ Function.support f ⊆ A := by
      filter_upwards [hm.2.eventually_ge_atTop (2 * D)] with i hi
      exact ⟨_, hasDiameterLE_mono hD (by linarith), subset_rfl⟩
    refine ⟨hev, ?_⟩
    refine (((Hcum.2.1 _ ha).2 ρ ν hc).2 f ⟨hfb, hfs⟩).congr' ?_
    filter_upwards [hev] with i hi
    rw [hint]
    obtain ⟨A, hA, hs⟩ := hi
    exact (hS i).integral_plaquetteSmearing f hfb ⟨A, hA, hs⟩
  · rintro n f ⟨hn, hlip, hcomp, hdisj⟩
    have hbdd : Bornology.IsBounded (⋃ i, tsupport (f i)) :=
      (isCompact_iUnion fun i => hcomp i).isBounded
    obtain ⟨D, hD⟩ := exists_hasDiameterLE hbdd
    have hev : ∀ᶠ i in atTop, IsSeparatedLipschitzTuple (PeriodicLattice.torusSide L (m i)) f := by
      filter_upwards [hm.2.eventually_ge_atTop (2 * D)] with i hi
      exact ⟨hn, hlip, hcomp, hdisj, _, hasDiameterLE_mono hD (by linarith),
        fun j => subset_iUnion (fun i => tsupport (f i)) j⟩
    refine ⟨hev, ?_⟩
    refine (Hcum.2.2.1 L K ha ρ ν hc n f hn fun j =>
      isBoundedBorelCompactlySupported_of_continuous (continuous_of_isLipschitzFor (hlip j))
        (hcomp j)).congr' ?_
    filter_upwards [hev] with i hi
    rw [← (hS i).ursellFunctionOfMeasure_eq f hi, hρ]
theorem ursellBoundsPassToLimits (Hcub : CubicTorusAsQuotient.Statement)
    (Hcum : GibbsAtFixedSpacing.CumulantsPolynomialInMomentsAndWeakLimits)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hK : 0 < K) (hβ : 0 < β) :
    UrsellBoundsPassToLimits L K β := by
  intro n f hf b m₀ _ _ hall ν hν
  obtain ⟨m, ρ, hm, ht, hρ, hc⟩ := hν
  have hloc := localQuantitiesTendsto Hcub Hcum hL hK hβ ⟨hm, ht⟩ ⟨ρ, hρ, hc⟩
  refine le_of_tendsto (hloc.2.2 n f hf).2.norm ?_
  filter_upwards [ht.eventually_ge_atTop (PeriodicLattice.torusSide L m₀)] with i hi
  exact (hall (m i) (hm i) hi).2
theorem torusStateLimitPoints_holds (Hany : GibbsAtFixedSpacing.TiltedTorusLimits)
    (Hcub : CubicTorusAsQuotient.Statement)
    (Htor : GibbsAtFixedSpacing.TorusMeasureCovariance)
    (Hweak : GibbsAtFixedSpacing.LimitsAndErgodicity.Statement)
    (Hcum : GibbsAtFixedSpacing.CumulantsPolynomialInMomentsAndWeakLimits)
    (Htop : GibbsAtFixedSpacing.SpacesOfFieldsAndMeasures.FieldAndMeasureSpaceProperties)
    (Hdil : GibbsAtFixedSpacing.PeriodicGibbsUnderRescaling.Statement)
    (Hfac : GibbsAtFixedSpacing.LinkFunctions.Assertion)
    (Hpos : ReflectionPositivity.CutoffMirrors.LinkPositivity.ReflectionPositivityAtLink)
    (Hww : PeriodicLattice.WilsonWeightGaugeInvariance.statement) :
    TorusStateLimitPoints := by
  intro L hL K hK β hβ
  exact ⟨limitSet_closed_nonempty Hany Hcub Htor Htop Hww hL hK hβ,
    fun ν hν => isSymmetricReflPosGibbs_of_mem Hany Hcub Htor Hweak Hdil Hfac Hpos Hww hL hK hβ hν,
    fun m ν hm hν => localQuantitiesTendsto Hcub Hcum hL hK hβ hm hν,
    ursellBoundsPassToLimits Hcub Hcum hL hK hβ⟩
end YangMills.Construction.InfiniteLattice.LimitPointsOfTorusStates
