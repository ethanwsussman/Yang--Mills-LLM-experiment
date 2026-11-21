import YangMills.Construction.FourPointCondition.ConditionsOfTheRatioAtAnObservableProof
import YangMills.Construction.FourPointCondition.FourPointBoundAlongTheFlow
import YangMills.Construction.ParameterData.FirstPassageOfTheFlowProof
import YangMills.Construction.ReflectionPositivity.NestedLatticesAdicPointsAndMirrorsProof
import YangMills.Construction.SystemOfAdmissibleConstants.TheLawAtALevelProof
import YangMills.Construction.SystemsWithFiveBounds.CanonicalDecompositionAlongStatesProof
import YangMills.Construction.Torus.GeometryTransportLiftAndDilationOfTestPairs
import YangMills.Construction.Torus.OneBallLiftAndTransportOfQuadruples
import YangMills.Construction.TotalDensitiesGiveASystem.GlueAtDrawnParameters
import YangMills.Construction.TotalDensitiesGiveASystem.TheExpansionFlowIsTheTotalFlow
import YangMills.Construction.TotalDensitiesGiveASystem.TheFourPointLawInTheLimits
import YangMills.Construction.TotalDensitiesGiveASystem.TheLawOnTheWindow
import YangMills.Construction.TotalDensitiesGiveASystem.TheLawsAtEveryShape
import YangMills.Construction.TotalDensitiesGiveASystem.TheParametersAreDrawnParameters
import YangMills.Construction.TotalDensitiesGiveASystem.TheStatesOfTheToriAreLimitsOfTheTori
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.TotalDensities
private def couplingAtScale (ℓ : TorusLumps.StepParameters) (room : ℕ → ℝ) (al : ℝ → ℕ → ℝ) : ℕ+ → ℝ → ℝ → ℝ :=
  fun K β d => al β ((K : ℕ) - RoomFunctions.scaleDepth ℓ.side room d)
private theorem isFirstPassagePair_iff {ℓ : TorusLumps.StepParameters} {Bs g : ℝ}
    (hR : ExpansionFlowEqTotalFlowAt ℓ Bs g) (K : ℕ+) (β : ℝ) :
    TotalDensitySystem.IsFirstPassagePair ℓ Bs g K β ↔ IsFirstPassagePoint ℓ Bs g K β := by
  show β ∈ SequencePassage.definedPassageWindow _ Bs g (TotalDensityFlow.coupling ℓ) K ↔
    β ∈ SequencePassage.passageWindow Bs g (ClusterExpansionOfAStep.flowCoupling ℓ) K
  rw [(hR K).1]
private theorem totalFlowValue_coupling_eq {ℓ : TorusLumps.StepParameters} {Bs g : ℝ}
    (hR : ExpansionFlowEqTotalFlowAt ℓ Bs g) {room : ℕ → ℝ}
    {ζ : ℕ+ → ℝ → ℝ → ℝ} {al : ℝ → ℕ → ℝ} {K : ℕ+} {β : ℝ} (hp : IsFirstPassagePoint ℓ Bs g K β) (d : ℝ) :
    (TotalDensitySystem.totalFlowValue ℓ g Bs room ζ).coupling K β d =
      (FourPointCondition.flowProfile ℓ g Bs room al).coupling K β d := by
  show TotalDensityFlow.coupling ℓ β _ ^ _ = (TorusLumps.couplingFlow ℓ β _).1 ^ _
  rw [(hR K).2 β hp _ (Nat.sub_le _ _)]
  rfl
private theorem sharpLaws_totalFlow {ℓ : TorusLumps.StepParameters} {Bs g vt d' d₀ : ℝ}
    (hR : ExpansionFlowEqTotalFlowAt ℓ Bs g) {room : ℕ → ℝ}
    {al : ℝ → ℕ → ℝ} {ηB εB ηBar : ℝ → ℝ} (hd : d₀ ≤ d')
    (hS : FourPointCondition.SharpEvaluationLaws (FourPointCondition.flowProfile ℓ g Bs room al) ℓ.side vt d' 1 ηB
      fun _ => εB)
    (hmono : MonotoneOn ηBar (Ioc 0 d₀)) (hmem : ∀ d ∈ Ioc (0 : ℝ) d₀, ηBar d ∈ Icc (0 : ℝ) (1 / 3))
    (hten : Tendsto ηBar (nhdsWithin 0 (Ioi 0)) (nhds 0)) (hle : ∀ d ∈ Ioc (0 : ℝ) d₀, ηB d ≤ ηBar d) :
    FourPointCondition.SharpEvaluationLaws
      (TotalDensitySystem.totalFlowValue ℓ g Bs room (couplingAtScale ℓ room al)) ℓ.side vt d₀ 1 ηBar
      fun _ => εB := by
  have hsub : Ioc (0 : ℝ) d₀ ⊆ Ioc 0 d' := Ioc_subset_Ioc_right hd
  refine ⟨hmono, fun _ => (hS.εBar_mono 0).mono hsub, hmem, fun m d hd' => hS.εBar_mem m d (hsub hd'), hten,
    hS.εBar_tendsto, ?_, ?_, ?_⟩
  · intro K β hp m hm d hd' hdeep f h hfh
    have hq := (isFirstPassagePair_iff hR K β).1 hp
    obtain ⟨ε, hε, he⟩ := hS.twoPoint K β hq m hm d (hsub hd') hdeep f h hfh
    refine ⟨ε, hε, ?_⟩
    rw [totalFlowValue_coupling_eq hR (al := al) hq d]
    exact he
  · intro K β hp d hd' hdeep
    exact (hS.fieldNorm_le K β ((isFirstPassagePair_iff hR K β).1 hp) d (hsub hd') hdeep).trans (hle d hd')
  · intro K β hp d hd' hdeep
    have hq := (isFirstPassagePair_iff hR K β).1 hp
    rw [totalFlowValue_coupling_eq hR (al := al) hq d]
    exact (hS.log_le K β hq d (hsub hd') hdeep).trans (hle d hd')
private theorem fourPointBound_totalFlow {ℓ : TorusLumps.StepParameters} {Bs g vt d' d₄ : ℝ}
    (hR : ExpansionFlowEqTotalFlowAt ℓ Bs g)
    {room : ℕ → ℝ} {al : ℝ → ℕ → ℝ} {ζ : ℕ+ → ℝ → ℝ → ℝ} (hd : d₄ ≤ d')
    (hC : FourPointCondition.FourPointConditionHolds (FourPointCondition.flowProfile ℓ g Bs room al) ℓ.side vt d' 1) :
    FourPointCondition.FourPointConditionHolds (TotalDensitySystem.totalFlowValue ℓ g Bs room ζ) ℓ.side vt d₄ 1 := by
  intro s β hs hp d hdd hdeep f hf
  have hq := (isFirstPassagePair_iff hR s.K β).1 hp
  rw [totalFlowValue_coupling_eq hR (al := al) hq d]
  exact hC s β hs hq d (Ioc_subset_Ioc_right hd hdd) hdeep f hf
private theorem twoPointPrefactor_eq : SystemsWithFiveBounds.twoPointPrefactor =
    TwoPointFunction.amplitudeConstant * FourPointCondition.oneLoopCoeff ^ 2 := by
  unfold SystemsWithFiveBounds.twoPointPrefactor TwoPointFunction.amplitudeConstant FourPointCondition.oneLoopCoeff
  norm_num [ParameterChoice.colorNumber]
private theorem oneLoopCoeff_pos : 0 < FourPointCondition.oneLoopCoeff := by apply _root_.YangMills.SharedProofs.p28620 <;> assumption
private theorem exists_mem_Icc_mul_eq {z G l e η ε A Kf : ℝ} (hl : 0 < l) (hz : |z - 1| ≤ η)
    (hG : |G ^ 2 * l / FourPointCondition.oneLoopCoeff - 1| ≤ η) (hε : |ε| ≤ e) (hη : η ≤ 1 / 3) (he : e ≤ 1 / 2) :
    ∃ t ∈ Icc ((1 - e) * (1 - η) ^ 4) ((1 + e) * (1 + η) ^ 4),
      z ^ 2 * A * G ^ 4 * Kf * (1 + ε) = A * FourPointCondition.oneLoopCoeff ^ 2 * Kf / l ^ 2 * t := by
  have ha := oneLoopCoeff_pos
  set u := G ^ 2 * l / FourPointCondition.oneLoopCoeff with hu
  have hz' := abs_le.1 hz
  have hG' := abs_le.1 hG
  have hε' := abs_le.1 hε
  have h₁ : 0 ≤ 1 - η := by linarith
  have hz₁ : 1 - η ≤ z := by linarith
  have hz₂ : z ≤ 1 + η := by linarith
  have hu₁ : 1 - η ≤ u := by linarith
  have hu₂ : u ≤ 1 + η := by linarith
  have hz0 : 0 ≤ z := h₁.trans hz₁
  have hu0 : 0 ≤ u := h₁.trans hu₁
  have he₁ : 0 ≤ 1 - e := by linarith
  have he₂ : 1 - e ≤ 1 + ε := by linarith
  have he₃ : 1 + ε ≤ 1 + e := by linarith
  have hzs₁ : (1 - η) ^ 2 ≤ z ^ 2 := pow_le_pow_left₀ h₁ hz₁ 2
  have hzs₂ : z ^ 2 ≤ (1 + η) ^ 2 := pow_le_pow_left₀ hz0 hz₂ 2
  have hus₁ : (1 - η) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ h₁ hu₁ 2
  have hus₂ : u ^ 2 ≤ (1 + η) ^ 2 := pow_le_pow_left₀ hu0 hu₂ 2
  refine ⟨(1 + ε) * (z ^ 2 * u ^ 2), ⟨?_, ?_⟩, ?_⟩
  · have h₂ : (1 - η) ^ 2 * (1 - η) ^ 2 ≤ z ^ 2 * u ^ 2 :=
      mul_le_mul hzs₁ hus₁ (by positivity) (by positivity)
    have h₃ := mul_le_mul he₂ h₂ (by positivity) (he₁.trans he₂)
    calc (1 - e) * (1 - η) ^ 4 = (1 - e) * ((1 - η) ^ 2 * (1 - η) ^ 2) := by ring
      _ ≤ _ := h₃
  · have h₂ : z ^ 2 * u ^ 2 ≤ (1 + η) ^ 2 * (1 + η) ^ 2 :=
      mul_le_mul hzs₂ hus₂ (by positivity) (by positivity)
    have h₃ := mul_le_mul he₃ h₂ (by positivity) (by linarith)
    calc _ ≤ (1 + e) * ((1 + η) ^ 2 * (1 + η) ^ 2) := h₃
      _ = (1 + e) * (1 + η) ^ 4 := by ring
  · rw [hu]
    field_simp
private theorem exists_mem_of_tendsto_image {ι : Type*} {l : Filter ι} [l.NeBot] {u : ι → ℂ} {v : ℂ} {C : Set ℝ}
    {φ : ℝ → ℂ} (hC : IsCompact C) (hφ : Continuous φ) (hu : Tendsto u l (𝓝 v))
    (h : ∀ᶠ i in l, ∃ t ∈ C, u i = φ t) :
    ∃ t ∈ C, v = φ t := by
  have hcl : IsClosed (φ '' C) := (hC.image hφ).isClosed
  have := hcl.mem_of_tendsto hu (h.mono fun i ⟨t, ht, e⟩ => ⟨t, ht, e.symm⟩)
  obtain ⟨t, ht, e⟩ := this
  exact ⟨t, ht, e.symm⟩
private theorem continuous_ofReal_const_mul (M : ℝ) : Continuous fun t : ℝ => ((M * t : ℝ) : ℂ) :=
  Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)
private theorem satisfiesWithError_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] {u : ι → ℂ} {value main d : ℝ}
    {ηBar εBar : ℝ → ℝ} (hu : Tendsto u l (𝓝 (value : ℂ)))
    (h : ∀ᶠ i in l, ∃ t ∈ Icc ((1 - εBar d) * (1 - ηBar d) ^ 4) ((1 + εBar d) * (1 + ηBar d) ^ 4),
      u i = ((main * t : ℝ) : ℂ)) : SatisfiesTwoPointLawWithError main ηBar εBar d value := by
  obtain ⟨t, ht, e⟩ := exists_mem_of_tendsto_image isCompact_Icc (continuous_ofReal_const_mul main) hu h
  have e' : value = main * t := Complex.ofReal_injective e
  exact ⟨t - 1, by rw [e']; ring_nf, by linarith [ht.1], by linarith [ht.2]⟩
private theorem satisfiesTwoPointLaw_mono {ηW ηBar : ℝ → ℝ} {d t : ℝ} {f h : (Fin 4 → ℝ) → ℝ} (h0 : 0 ≤ ηW d)
    (hle : ηW d ≤ ηBar d) (h3 : ηBar d ≤ 1 / 3) (ho : SystemsWithFiveBounds.SatisfiesTwoPointLaw ηW d t f h) :
    SystemsWithFiveBounds.SatisfiesTwoPointLaw ηBar d t f h := by
  obtain ⟨η, e, a, b⟩ := ho
  refine ⟨η, e, le_trans ?_ a, le_trans b ?_⟩
  · have : (1 - ηBar d) ^ 4 ≤ (1 - ηW d) ^ 4 := pow_le_pow_left₀ (by linarith) (by linarith) 4
    linarith
  · have : (1 + ηW d) ^ 4 ≤ (1 + ηBar d) ^ 4 := pow_le_pow_left₀ (by linarith) (by linarith) 4
    linarith
private theorem matrixVecCons_eta {Y : Type*} (X : Fin 2 → Y → ℝ) : ![X 0, X 1] = X := by
  funext i
  fin_cases i <;> rfl
private theorem isCompact_closedBallR4 (c : Fin 4 → ℝ) (r : ℝ) : IsCompact (TestFunctions.closedBallR4 c r) := by apply _root_.YangMills.SharedProofs.p20989 <;> assumption
private theorem separatedPair_props (hG : TestFunctions.PairTransport.PairTransportStatement)
    (s : Conventions.StandingParameters)
    {d vt : ℝ} (hd : 0 < d) (hvt : vt ∈ Ioc (0 : ℝ) 1) {f h : (Fin 4 → ℝ) → ℝ}
    (hfh : (f, h) ∈ TestFunctions.separatedPairsR4 d vt) :
    TestFunctions.IsLipschitzFor TestFunctions.euclidDistR4 f ∧
      TestFunctions.IsLipschitzFor TestFunctions.euclidDistR4 h ∧ HasCompactSupport f ∧ HasCompactSupport h ∧
      Disjoint (tsupport f) (tsupport h) := by
  obtain ⟨x₁, x₂, h₁, h₂, h₃, h₄⟩ := id hfh
  obtain ⟨-, -, -, hsf, hsh, hdist, -⟩ := (hG s d vt ⟨hd, hvt⟩).1 f h x₁ x₂ hfh ⟨h₁.2.2.2, h₂.2.2.2, h₃, h₄⟩
  refine ⟨h₁.1, h₂.1, (isCompact_closedBallR4 _ _).of_isClosed_subset (isClosed_tsupport _) hsf,
    (isCompact_closedBallR4 _ _).of_isClosed_subset (isClosed_tsupport _) hsh,
    Set.disjoint_left.2 fun u hu hv => ?_⟩
  have := (hdist u hu u hv).1
  simp [TestFunctions.euclidDistR4, TorusMetric.euclidNormVec] at this
  linarith
private theorem periodizeAll_pair (L m : ℕ) (f h : (Fin 4 → ℝ) → ℝ) :
    SchwingerFunctions.periodizeAll L m ![f, h] =
      ![TestFunctions.periodize (PeriodicLattice.torusSide L m) f,
        TestFunctions.periodize (PeriodicLattice.torusSide L m) h] := by
  funext i
  fin_cases i <;> rfl
private theorem twoPoint_in_state (hSt : TotalDensitiesGiveASystem.TorusStatesAreLimitsOfTori)
    (hG : TestFunctions.PairTransport.PairTransportStatement) {L : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L)
    {K : ℕ+} {β : ℝ} (hβ : 0 < β)
    {ν : Measure (InfiniteLattice.GaugeField (PeriodicLattice.meshSize L (((K : ℕ)) : ℤ)))}
    (hν : ν ∈ InfiniteLattice.torusLimitSet L K β ∨ InfiniteLattice.IsInfiniteVolumeLimit L K β ν) {d vt : ℝ}
    (hd : 0 < d) (hvt : vt ∈ Ioc (0 : ℝ) 1) {f h : (Fin 4 → ℝ) → ℝ}
    (hfh : (f, h) ∈ TestFunctions.separatedPairsR4 d vt) {M e : ℝ}
    (hlaw : ∀ m : ℕ, 0 < m → 40 * d ≤ PeriodicLattice.torusSide L m → ∃ ε : ℝ, |ε| ≤ e ∧
      PeriodicLattice.torusUrsellFunction L m K β
        ![TestFunctions.periodize (PeriodicLattice.torusSide L m) f,
          TestFunctions.periodize (PeriodicLattice.torusSide L m) h] = ((M * (1 + ε) : ℝ) : ℂ)) :
    ∃ ε : ℝ, |ε| ≤ e ∧ InfiniteLattice.smearedEnergyCumulant ν ![f, h] = ((M * (1 + ε) : ℝ) : ℂ) := by
  obtain ⟨m, hm, hside, ht⟩ := hSt L hL K β hβ ν hν
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := separatedPair_props hG ⟨L, hL, K, K⟩ hd hvt hfh
  have hlim := ht 2 ![f, h] le_rfl
    (fun i => by fin_cases i; exacts [h₁, h₂]) (fun i => by fin_cases i; exacts [h₃, h₄])
    (fun i k hik => by
      fin_cases i <;> fin_cases k
      · exact absurd rfl hik
      · exact h₅
      · exact h₅.symm
      · exact absurd rfl hik)
  have hφ : Continuous fun ε : ℝ => ((M * (1 + ε) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_const.mul (continuous_const.add continuous_id))
  obtain ⟨ε, hε, e'⟩ := exists_mem_of_tendsto_image (C := Icc (-e) e) isCompact_Icc hφ hlim (by
    filter_upwards [hside.eventually_ge_atTop (40 * d)] with i hi
    obtain ⟨ε, hε, he⟩ := hlaw (m i) (hm i) hi
    refine ⟨ε, abs_le.1 hε, ?_⟩
    show PeriodicLattice.torusUrsellFunction L (m i) K β (SchwingerFunctions.periodizeAll L (m i) ![f, h]) = _
    rw [periodizeAll_pair]
    exact he)
  exact ⟨ε, abs_le.2 hε, e'⟩
private theorem couplingFlow_step_le {ℓ : TorusLumps.StepParameters} (hr : StepReturn.ExpansionReturnsAt ℓ)
    (β : ℝ) (t : ℕ)
    (hy : ℓ.y₁ ≤ (TorusLumps.couplingFlow ℓ β t).1)
    (hrow : TorusLumps.HasExpansion ℓ t (TorusLumps.couplingFlow ℓ β t).1 (TorusLumps.couplingFlow ℓ β t).2) :
    |(TorusLumps.couplingFlow ℓ β (t + 1)).1 - (TorusLumps.couplingFlow ℓ β t).1| ≤ 2 * ℓ.B := by apply _root_.YangMills.SharedProofs.p80822 <;> assumption
private theorem flowCoupling_envelopes {T : RenormalizationStepParameters.ParameterAssignment} {y : ℝ} (D : TrajectoryData.TrajectoryParameters T y)
    {Bs g : ℝ} (hH : (D.withShift Bs D.rateBound).Admissible)
    (hData : TrajectoryData.HasTrajectoryData (D.withShift Bs D.rateBound)) (hg : 0 < g)
    (hy : D.floorStar ≤ g ^ (-2 : ℤ)) {K : ℕ} {β : ℝ}
    (hp : β ∈ SequencePassage.passageWindow Bs g (ClusterExpansionOfAStep.flowCoupling (T.stepParameters y)) K) {s : ℕ}
    (hs : s ≤ K) :
    g ^ (-2 : ℤ) + D.rateBound * s - D.c₅ ≤ ClusterExpansionOfAStep.flowCoupling (T.stepParameters y) β (K - s) ∧
      ClusterExpansionOfAStep.flowCoupling (T.stepParameters y) β (K - s) ≤ g ^ (-2 : ℤ) + Bs * ((s : ℝ) + 1) := by
  have hb := hH.errorMargin
  have hsl := hData.slope g hg hy K β hp (K - s) K (Nat.sub_le _ _) le_rfl
  obtain ⟨K', hK'⟩ := hData.passage g hg hy β hp.1
  have hKK : K' = K := by
    have h₁ := hK'.isFirstPassageIndex
    have h₂ := hp.2
    rcases lt_trichotomy K' K with h | h | h
    · exact absurd h₁.1 (not_le.2 (h₂.2 K' h))
    · exact h
    · exact absurd h₂.1 (not_le.2 (h₁.2 K h))
  subst hKK
  have habove := hK'.coupling_gt K' le_rfl
  have hcast : ((K' : ℝ) - ((K' - s : ℕ) : ℝ)) = s := by
    rw [Nat.cast_sub hs]
    ring
  rw [hcast] at hsl
  have hXy : D.X₀ ≤ D.floorStar := le_max_of_le_left (le_max_left _ _)
  have hstep : ∀ k < K', |ClusterExpansionOfAStep.flowCoupling (T.stepParameters y) β (k + 1) -
      ClusterExpansionOfAStep.flowCoupling (T.stepParameters y) β k| ≤ 2 * T.B := by
    intro k hk
    have ha := hK'.coupling_gt k hk.le
    have hfl : y ≤ (TorusLumps.couplingFlow (T.stepParameters y) β k).1 :=
      (hb.floor_le.trans (hXy.trans hy)).trans ha.le
    exact couplingFlow_step_le hb.returns β k hfl (hK'.hasExpansion k hk.le)
  have hup : ∀ i : ℕ, i ≤ K' →
      ClusterExpansionOfAStep.flowCoupling (T.stepParameters y) β (K' - i) ≤
        ClusterExpansionOfAStep.flowCoupling (T.stepParameters y) β K' + i * (2 * T.B) := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      have h₁ := ih (by omega)
      have h₂ := hstep (K' - (i + 1)) (by omega)
      have e : K' - (i + 1) + 1 = K' - i := by omega
      rw [e] at h₂
      have h₃ := (abs_le.1 h₂).1
      push_cast
      linarith
  have hBs : 2 * T.B ≤ Bs := hH.shift_ge
  have hcut : ClusterExpansionOfAStep.flowCoupling (T.stepParameters y) β K' ≤ g ^ (-2 : ℤ) + Bs := hp.2.1
  refine ⟨?_, ?_⟩
  · have h₁ : g ^ (-2 : ℤ) < ClusterExpansionOfAStep.flowCoupling (T.stepParameters y) β K' := habove
    have h₂ : D.rateBound * (s : ℝ) - D.c₅ ≤ ClusterExpansionOfAStep.flowCoupling (T.stepParameters y) β (K' - s) -
        ClusterExpansionOfAStep.flowCoupling (T.stepParameters y) β K' := hsl
    linarith
  · have h₁ := hup s hs
    have h₂ : (s : ℝ) * (2 * T.B) ≤ s * Bs := mul_le_mul_of_nonneg_left hBs (Nat.cast_nonneg _)
    nlinarith
private theorem tendsto_pnat_coe : Tendsto (fun n : ℕ+ => (n : ℕ)) atTop atTop := by apply _root_.YangMills.Construction.ReflectionPositivity.AdicLattices.tendsto_pnat_coe_atTop <;> assumption
private theorem tendsto_succPNat : Tendsto Nat.succPNat atTop atTop := by apply _root_.YangMills.SharedProofs.p14344 <;> assumption
private theorem tendsto_torusSide {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) {ι : Type*}
    {l : Filter ι} {m : ι → ℕ+}
    (hm : Tendsto m l atTop) : Tendsto (fun j => PeriodicLattice.torusSide L (m j : ℕ)) l atTop := by
  have h1 : (1 : ℝ) < L := by
    have : 1 < L := lt_of_lt_of_le (by norm_num) hL.2
    exact_mod_cast this
  have hp := tendsto_pow_atTop_atTop_of_one_lt h1
  have hs : Tendsto (fun m : ℕ => PeriodicLattice.torusSide L m) atTop atTop := by
    refine Tendsto.congr (fun m => ?_) (hp.const_mul_atTop (show (0 : ℝ) < 2 by norm_num))
    simp [PeriodicLattice.torusSide]
  exact hs.comp (tendsto_pnat_coe.comp hm)
section
variable {ℓ : TorusLumps.StepParameters} {Bs g vt d₀ : ℝ} {room : ℕ → ℝ} {ηBar εBar : ℝ → ℝ}
  {ζ : ℕ+ → ℝ → ℝ → ℝ}
private theorem exists_bracket_at_observable
    (hS : FourPointCondition.SharpEvaluationLaws (TotalDensitySystem.totalFlowValue ℓ g Bs room ζ) ℓ.side vt d₀ 1
      ηBar fun _ => εBar)
    {K : ℕ+} {β d : ℝ} (hp : TotalDensitySystem.IsFirstPassagePair ℓ Bs g K β) (hd : d ∈ Ioc (0 : ℝ) d₀)
    (hd1 : d < 1)
    (hdeep : (TotalDensitySystem.totalFlowValue ℓ g Bs room ζ).IsDeepEnough ℓ.side K 1 d) {ε : ℝ}
    (hε : |ε| ≤ εBar d) (Kf : ℝ) :
    ∃ t ∈ Icc ((1 - εBar d) * (1 - ηBar d) ^ 4) ((1 + εBar d) * (1 + ηBar d) ^ 4),
      ζ K β d ^ 2 * TwoPointFunction.amplitudeConstant *
          (TotalDensitySystem.totalFlowValue ℓ g Bs room ζ).coupling K β d ^ 4 * Kf * (1 + ε) =
        SystemsWithFiveBounds.twoPointPrefactor * Kf / Real.log (1 / d) ^ 2 * t := by
  have hl : 0 < Real.log (1 / d) := by
    apply Real.log_pos
    rw [lt_div_iff₀ hd.1]
    linarith
  rw [twoPointPrefactor_eq]
  exact exists_mem_Icc_mul_eq hl (hS.fieldNorm_le K β hp d hd hdeep) (hS.log_le K β hp d hd hdeep) hε
    (hS.ηBar_mem d hd).2 (hS.εBar_mem 0 d hd).2
private theorem isDeepEnough_of_le {K : ℕ+} {d : ℝ} (h : RoomFunctions.scaleDepth ℓ.side room d + 1 ≤ (K : ℕ)) :
    (TotalDensitySystem.totalFlowValue ℓ g Bs room ζ).IsDeepEnough ℓ.side K 1 d := by
  show ((1 : ℕ) : ℤ) ≤ ((K : ℕ) : ℤ) - (RoomFunctions.scaleDepth ℓ.side room d : ℤ)
  omega
private theorem twoPoint_in_states (hSt : TotalDensitiesGiveASystem.TorusStatesAreLimitsOfTori)
    (hG : TestFunctions.PairTransport.PairTransportStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor ℓ.side)
    (hS : FourPointCondition.SharpEvaluationLaws (TotalDensitySystem.totalFlowValue ℓ g Bs room ζ) ℓ.side vt d₀ 1
      ηBar fun _ => εBar)
    (hvt : vt ∈ Ioc (0 : ℝ) 1) {K : ℕ+} {β : ℝ} (hβ : 0 < β)
    (hp : TotalDensitySystem.IsFirstPassagePair ℓ Bs g K β)
    {ν : Measure (InfiniteLattice.GaugeField (PeriodicLattice.meshSize ℓ.side (((K : ℕ)) : ℤ)))}
    (hν : ν ∈ InfiniteLattice.torusLimitSet ℓ.side K β ∨ InfiniteLattice.IsInfiniteVolumeLimit ℓ.side K β ν)
    {d : ℝ} (hd : d ∈ Ioc (0 : ℝ) d₀)
    (hdeep : (TotalDensitySystem.totalFlowValue ℓ g Bs room ζ).IsDeepEnough ℓ.side K 1 d)
    {f h : (Fin 4 → ℝ) → ℝ} (hfh : (f, h) ∈ TestFunctions.separatedPairsR4 d vt) :
    ∃ ε : ℝ, |ε| ≤ εBar d ∧ InfiniteLattice.smearedEnergyCumulant ν ![f, h] =
      ((ζ K β d ^ 2 * TwoPointFunction.amplitudeConstant *
        (TotalDensitySystem.totalFlowValue ℓ g Bs room ζ).coupling K β d ^ 4 *
        TestFunctions.inverseEighthKernel f h * (1 + ε) : ℝ) : ℂ) := by
  refine twoPoint_in_state hSt hG hL hβ hν hd.1 hvt hfh fun m hm h40 => ?_
  have tr := (hG ⟨ℓ.side, hL, K, ⟨m, hm⟩⟩ d vt ⟨hd.1, hvt⟩).2.1 h40 f h hfh
  obtain ⟨ε, hε, he⟩ := hS.twoPoint K β hp m ⟨m, hm, rfl⟩ d hd hdeep _ _ tr.1
  obtain ⟨-, -, -, -, hk, -⟩ := tr
  refine ⟨ε, hε, ?_⟩
  rw [← hk]
  exact he
private theorem twoPointLawInLimits_of (hSt : TotalDensitiesGiveASystem.TorusStatesAreLimitsOfTori)
    (hG : TestFunctions.PairTransport.PairTransportStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor ℓ.side)
    (hS : FourPointCondition.SharpEvaluationLaws (TotalDensitySystem.totalFlowValue ℓ g Bs room ζ) ℓ.side vt d₀ 1
      ηBar fun _ => εBar)
    (hvt : vt ∈ Ioc (0 : ℝ) 1)
    (hβ : ∀ (K : ℕ+) (β : ℝ), TotalDensitySystem.IsFirstPassagePair ℓ Bs g K β → 0 < β) (hd₀ : d₀ < 1) :
    TwoPointLawInLimits ℓ Bs g vt d₀ ηBar εBar := by
  refine ⟨?_, ?_⟩
  · rintro ⟨L', hL', Ks, ms⟩ S hs hlim d hd X hX
    change L' = ℓ.side at hs
    subst hs
    obtain ⟨K, β, hp, hK, hconv⟩ := hlim
    have hd1 : d < 1 := lt_of_le_of_lt hd.2 hd₀
    refine satisfiesWithError_of_tendsto (hconv 2 le_rfl X) ?_
    filter_upwards [(tendsto_pnat_coe.comp hK).eventually_ge_atTop
      (RoomFunctions.scaleDepth ℓ.side room d + 1)] with j hj
    have hdeep := isDeepEnough_of_le (ℓ := ℓ) (g := g) (Bs := Bs) (room := room) (ζ := ζ) (K := K j) (d := d) hj
    obtain ⟨ε, hε, he⟩ := hS.twoPoint (K j) (β j) (hp j) ms ⟨ms, ms.pos, rfl⟩ d hd hdeep (X.1 0) (X.1 1) hX
    obtain ⟨t, ht, et⟩ := exists_bracket_at_observable hS (hp j) hd hd1 hdeep hε
      (TestFunctions.inverseEighthKernelTorus (ℓ := PeriodicLattice.torusSide ℓ.side ms) (X.1 0) (X.1 1))
    refine ⟨t, ht, ?_⟩
    have e : SchwingerFunctions.connectedSchwinger ℓ.side ms (K j) (β j) X.1 =
        PeriodicLattice.torusUrsellFunction ℓ.side ms (K j) (β j) ![X.1 0, X.1 1] :=
      congrArg (PeriodicLattice.torusUrsellFunction ℓ.side ms (K j) (β j))
        (matrixVecCons_eta (Y := PeriodicLattice.FourTorus ℓ.side ms) X.1).symm
    rw [e, he]
    exact congrArg _ et
  · intro S hS' d hd X hX
    have hd1 : d < 1 := lt_of_le_of_lt hd.2 hd₀
    rcases hS' with ⟨K, m, β, hp, hK, hm, hconv⟩ | ⟨Q, hQ⟩
    · refine satisfiesWithError_of_tendsto (hconv 2 le_rfl X) ?_
      filter_upwards [(tendsto_pnat_coe.comp hK).eventually_ge_atTop
          (RoomFunctions.scaleDepth ℓ.side room d + 1),
        (tendsto_torusSide hL hm).eventually_ge_atTop (40 * d)] with j hj h40
      have hdeep := isDeepEnough_of_le (ℓ := ℓ) (g := g) (Bs := Bs) (room := room) (ζ := ζ) (K := K j) (d := d) hj
      have tr := (hG ⟨ℓ.side, hL, K j, m j⟩ d vt ⟨hd.1, hvt⟩).2.1 h40 (X.1 0) (X.1 1) hX
      obtain ⟨ε, hε, he⟩ := hS.twoPoint (K j) (β j) (hp j) (m j) ⟨m j, (m j).pos, rfl⟩ d hd hdeep _ _ tr.1
      obtain ⟨-, -, -, -, hk, -⟩ := tr
      obtain ⟨t, ht, et⟩ := exists_bracket_at_observable hS (hp j) hd hd1 hdeep hε
        (TestFunctions.inverseEighthKernel (X.1 0) (X.1 1))
      refine ⟨t, ht, ?_⟩
      have e : (fun i => TestFunctions.periodize (PeriodicLattice.torusSide ℓ.side (m j)) (X.1 i)) =
          ![TestFunctions.periodize (PeriodicLattice.torusSide ℓ.side (m j)) (X.1 0),
            TestFunctions.periodize (PeriodicLattice.torusSide ℓ.side (m j)) (X.1 1)] := by
        funext i
        fin_cases i <;> rfl
      show PeriodicLattice.torusUrsellFunction ℓ.side (m j) (K j) (β j)
        (fun i => TestFunctions.periodize (PeriodicLattice.torusSide ℓ.side (m j)) (X.1 i)) = _
      rw [e, he]
      have hk' : TestFunctions.inverseEighthKernelTorus (ℓ := PeriodicLattice.torusSide ℓ.side (m j))
          (TestFunctions.periodize (PeriodicLattice.torusSide ℓ.side (m j)) (X.1 0))
          (TestFunctions.periodize (PeriodicLattice.torusSide ℓ.side (m j)) (X.1 1)) =
          TestFunctions.inverseEighthKernel (X.1 0) (X.1 1) := hk
      rw [hk']
      exact congrArg _ et
    · refine satisfiesWithError_of_tendsto (hQ 2 le_rfl X) ?_
      filter_upwards [Q.tendsto_cutoff.eventually_ge_atTop (RoomFunctions.scaleDepth ℓ.side room d + 1)] with j hj
      have hdeep := isDeepEnough_of_le (ℓ := ℓ) (g := g) (Bs := Bs) (room := room) (ζ := ζ)
        (K := Q.cutoff j) (d := d) hj
      obtain ⟨ε, hε, he⟩ := twoPoint_in_states hSt hG hL hS hvt (hβ _ _ (Q.pair j)) (Q.pair j)
        (Or.inr (Q.isLimit j)) hd hdeep hX
      obtain ⟨t, ht, et⟩ := exists_bracket_at_observable hS (Q.pair j) hd hd1 hdeep hε
        (TestFunctions.inverseEighthKernel (X.1 0) (X.1 1))
      refine ⟨t, ht, ?_⟩
      rw [← matrixVecCons_eta X.1, he]
      exact congrArg _ et
end
theorem lawsAtEveryShape_holds (hT : TotalDensitiesGiveASystem.ResponseParametersToAdmissibleParameters)
    (hD : TrajectoryData.trajectoryDataStatement)
    (hL : FourPointCondition.lawsAtFlowDataStatement) (hC : FourPointCondition.fourPointBoundAtFlowDataStatement)
    (hLim : FourPointCondition.LimitBoundStatement) (hR : expansionFlowEqTotalFlow)
    (hW : twoPointLawOnWindow) (hFL : fourPointLawInLimits)
    (hSt : TotalDensitiesGiveASystem.TorusStatesAreLimitsOfTori)
    (hG : TestFunctions.PairTransport.PairTransportStatement)
    (hB : QuadrupleBalls.BallLiftPeriodizationStatement) : LawsAtEveryShape := by
  have h₂ : HoldsAtAdmissibleParameters fun T y =>
      ∃ D : TrajectoryData.TrajectoryParameters T y, FourPointCondition.HasTrajectoryDataForAllShifts D := by
    obtain ⟨Q, hQ, floorL, ceilRt, ceilσ, floorN, floorCs, C₀, h1, h2, hT'⟩ := hD
    refine ⟨⟨Q, floorL, fun _ => C₀, ceilRt, ceilσ, floorN, floorCs, fun _ => 0⟩, ⟨hQ, h1, h2⟩,
      fun T hDr hM => ?_⟩
    exact hT' T hDr hM.side_ge hM.rt_le hM.threshold_le hM.n₀_ge hM.Cs_ge hM.derivBound_ge hM.holds
  refine HoldsAtAdmissibleParameters.mono (HoldsAtAdmissibleParameters.and (HoldsAtAdmissibleParameters.and
    (HoldsAtAdmissibleParameters.and (HoldsAtAdmissibleParameters.and (HoldsAtAdmissibleParameters.and
    (HoldsAtAdmissibleParameters.and (hT _ hL) (hT _ hC)) (hT _ hLim)) h₂) hR) hW) hFL) fun T y hDr hA => ?_
  obtain ⟨⟨⟨⟨⟨⟨hLaws, hCl⟩, hLi⟩, D, hDat⟩, hRr⟩, hWw⟩, hFp⟩ := hA
  obtain ⟨Kr, -, h₃⟩ := hLaws
  obtain ⟨al, -, hLa⟩ := h₃ D hDat
  have hBs : 2 * T.B ≤ 2 * T.B := le_rfl
  have hst : Conventions.IsAdmissibleBlockingFactor (T.stepParameters y).side :=
    ⟨hDr.L_odd, le_trans (by norm_num) hDr.L_ge⟩
  have hL2 : 2 ≤ (T.stepParameters y).side := le_trans (by norm_num) hst.2
  have hlamR : 0 < D.rateBound := by
    have hL' : (1 : ℝ) < T.side := by
      have h : 2 ^ 40 ≤ T.side := hDr.L_ge
      have h' : 1 < T.side := lt_of_lt_of_le (by norm_num) h
      exact_mod_cast h'
    have hlog := Real.log_pos hL'
    have hpi := Real.pi_pos
    show 0 < 3 / 4 * (11 / (3 * Real.pi ^ 2) * Real.log T.side)
    positivity
  have hlam_eq : 3 / 4 * TotalDensitySystem.oneLoopShift T.side = D.rateBound := by
    show 3 / 4 * (SystemsWithFiveBounds.asymptoticFreedomSlope * Real.log T.side) =
      3 / 4 * (11 / (3 * Real.pi ^ 2) * Real.log T.side)
    unfold SystemsWithFiveBounds.asymptoticFreedomSlope
    have hp := Real.pi_ne_zero
    field_simp
    ring
  obtain ⟨hH, hData⟩ := hDat (2 * T.B) D.rateBound hBs hlamR le_rfl
  refine ⟨D.c₅, fun c₅ hc₅ => ?_⟩
  obtain ⟨yR, fR⟩ := hRr (2 * T.B) hBs
  obtain ⟨yW, fW⟩ := hWw (2 * T.B) hBs
  obtain ⟨yF, fF⟩ := hFp (2 * T.B) hBs
  refine ⟨max (max D.floorStar yR) (max yW yF), fun g hg hy ϑ hϑ room hroom d₁ η₁ hd₁ hη₁ => ?_⟩
  have hyS : D.floorStar ≤ g ^ (-2 : ℤ) := (le_max_left _ _).trans ((le_max_left _ _).trans hy)
  have hyR : yR ≤ g ^ (-2 : ℤ) := (le_max_right _ _).trans ((le_max_left _ _).trans hy)
  have hyW : yW ≤ g ^ (-2 : ℤ) := (le_max_left _ _).trans ((le_max_right _ _).trans hy)
  have hyF : yF ≤ g ^ (-2 : ℤ) := (le_max_right _ _).trans ((le_max_right _ _).trans hy)
  have hScaleFlow := fR g hg hyR
  obtain ⟨dW, ηW, K₀, hSM, hLW⟩ := fW g hg hyW ϑ hϑ
  obtain ⟨d', ηB, εB, hLw, hSh, -⟩ :=
    hLa (2 * T.B) D.rateBound hBs hlamR le_rfl ϑ hϑ.1 hϑ.2 g hg hyS room hroom
  obtain ⟨dL, hdL, hLimits⟩ := hLi ϑ hϑ.1 hϑ.2 _ _ _ _ _ hLw
  obtain ⟨dC, hdC, hCentered⟩ := (hCl D hDat (2 * T.B) hBs g hg hyS).2 ϑ hϑ.1 hϑ.2 room hroom
  obtain ⟨dF, hdF, hVol⟩ := fF g hg hyF ϑ hϑ.1 hϑ.2
  have hd'pos : 0 < d' := hLw.d₀_mem.1
  have hdWpos : 0 < dW := hSM.scale_mem.1
  have hdm : 0 < min (min d' dW) (min d₁ (1 / 40)) :=
    lt_min (lt_min hd'pos hdWpos) (lt_min hd₁ (by norm_num))
  have e₁ : ∀ᶠ d in 𝓝[>] (0 : ℝ), c₅ + 1 ≤ 3 / 4 * TotalDensitySystem.oneLoopShift T.side *
      (RoomFunctions.scaleDepth (T.stepParameters y).side room d : ℝ) := by
    filter_upwards [(RoomFunctions.tendsto_scaleDepth hroom hL2).eventually_ge_atTop
      ⌈(c₅ + 1) / D.rateBound⌉₊] with d hd
    have h₁ : (c₅ + 1) / D.rateBound ≤ (RoomFunctions.scaleDepth (T.stepParameters y).side room d : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hd)
    rw [hlam_eq]
    rw [div_le_iff₀ hlamR] at h₁
    linarith
  obtain ⟨d₀, hd₀a, hd₀b⟩ := (e₁.and (Ioc_mem_nhdsGT hdm)).exists
  have hd₀' : d₀ ≤ d' := hd₀b.2.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hd₀W : d₀ ≤ dW := hd₀b.2.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hd₀₁ : d₀ ≤ d₁ := hd₀b.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hd₀40 : d₀ ≤ 1 / 40 := hd₀b.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hsub' : Ioc (0 : ℝ) d₀ ⊆ Ioc 0 d' := Ioc_subset_Ioc_right hd₀'
  have hsubW : Ioc (0 : ℝ) d₀ ⊆ Ioc 0 dW := Ioc_subset_Ioc_right hd₀W
  have hsub₁ : Ioc (0 : ℝ) d₀ ⊆ Ioc 0 d₁ := Ioc_subset_Ioc_right hd₀₁
  let ηBar : ℝ → ℝ := fun d => max (max (ηB d) (ηW d)) (η₁ d)
  have hmono : MonotoneOn ηBar (Ioc 0 d₀) := fun a ha b hb hab =>
    max_le_max (max_le_max (hSh.ηBar_mono (hsub' ha) (hsub' hb) hab)
      (hSM.modulus_monotoneOn (hsubW ha) (hsubW hb) hab)) (hη₁.monotoneOn (hsub₁ ha) (hsub₁ hb) hab)
  have hmem : ∀ d ∈ Ioc (0 : ℝ) d₀, ηBar d ∈ Icc (0 : ℝ) (1 / 3) := fun d hd =>
    ⟨le_max_of_le_right (hη₁.mem_Icc d (hsub₁ hd)).1,
      max_le (max_le (hSh.ηBar_mem d (hsub' hd)).2 (hSM.modulus_mem d (hsubW hd)).2)
        (hη₁.mem_Icc d (hsub₁ hd)).2⟩
  have hten : Tendsto ηBar (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have := (hSh.ηBar_tendsto.max hSM.modulus_tendsto_zero).max hη₁.tendsto
    simpa using this
  have hleB : ∀ d ∈ Ioc (0 : ℝ) d₀, ηB d ≤ ηBar d := fun d _ =>
    le_max_of_le_left (le_max_left _ _)
  have hS := sharpLaws_totalFlow hScaleFlow hd₀' hSh hmono hmem hten hleB
  have hβ : ∀ (K : ℕ+) (β : ℝ), TotalDensitySystem.IsFirstPassagePair (T.stepParameters y) (2 * T.B) g K β →
      0 < β := fun K β hp => by
    have h₁ : SequencePassage.passageThreshold (2 * T.B) g ≤ β := ((isFirstPassagePair_iff hScaleFlow K β).1 hp).1
    have h₂ : 0 < g ^ (-2 : ℤ) := zpow_pos hg _
    have h₃ : 1 ≤ T.B := hDr.B_ge
    unfold SequencePassage.passageThreshold at h₁
    linarith
  have hd₀1 : d₀ < 1 := lt_of_le_of_lt hd₀40 (by norm_num)
  have hd₄pos : 0 < min (min dC dL) (min dF d₀) :=
    lt_min (lt_min hdC hdL.1) (lt_min hdF hd₀b.1)
  have hd₄C : min (min dC dL) (min dF d₀) ≤ dC := (min_le_left _ _).trans (min_le_left _ _)
  have hd₄L : min (min dC dL) (min dF d₀) ≤ dL := (min_le_left _ _).trans (min_le_right _ _)
  have hd₄F : min (min dC dL) (min dF d₀) ≤ dF := (min_le_right _ _).trans (min_le_left _ _)
  have hd₄₀ : min (min dC dL) (min dF d₀) ≤ d₀ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨d₀, ηBar, εB, couplingAtScale (T.stepParameters y) room al, K₀, min (min dC dL) (min dF d₀), hd₀₁,
    fun d _ => le_max_right _ _, ⟨⟨hd₀b.1, hd₀40⟩, hd₀a, hS, ?_, ?_, ?_⟩,
    twoPointLawInLimits_of hSt hG hst hS hϑ hβ hd₀1, ⟨hd₄pos, hd₄₀⟩,
    fourPointBound_totalFlow hScaleFlow hd₄C (hCentered al), ⟨?_, ?_⟩⟩
  · intro K β hp d hd hdeep
    have hq := (isFirstPassagePair_iff hScaleFlow K β).1 hp
    have hs : RoomFunctions.scaleDepth (T.stepParameters y).side room d ≤ (K : ℕ) := by
      have h : ((1 : ℕ) : ℤ) ≤ ((K : ℕ) : ℤ) -
          (RoomFunctions.scaleDepth (T.stepParameters y).side room d : ℤ) := hdeep
      omega
    obtain ⟨e₁, e₂⟩ := flowCoupling_envelopes D hH hData hg hyS hq hs
    have ee := (hScaleFlow K).2 β hq _ (Nat.sub_le _ (RoomFunctions.scaleDepth (T.stepParameters y).side room d))
    rw [ee, hlam_eq]
    exact ⟨by linarith, e₂⟩
  · intro K β hp ν hν d hd hdeep f h hfh
    exact twoPoint_in_states hSt hG hst hS hϑ (hβ K β hp) hp (Or.inl hν) hd hdeep hfh
  · intro d hd K β hp hK ν hν f h hfh
    obtain ⟨t, ht, ho⟩ := hLW d (hsubW hd) K β ((isFirstPassagePair_iff hScaleFlow K β).1 hp) hK ν hν f h hfh
    exact ⟨t, ht, satisfiesTwoPointLaw_mono (hSM.modulus_mem d (hsubW hd)).1
      (le_max_of_le_left (le_max_right _ _)) (hmem d hd).2 ho⟩
  · rintro ⟨L', hL', Ks, ms⟩ S hs hl d hd X hX
    change L' = (T.stepParameters y).side at hs
    subst hs
    obtain ⟨K, β, hp, hK, hconv⟩ := hl
    obtain ⟨h₁, -, -⟩ := hLimits d ⟨hd.1, hd.2.trans hd₄L⟩
    obtain ⟨r, hr, hI⟩ := h₁ (fun j => K j.succPNat) (fun j => β j.succPNat)
      (fun j => (isFirstPassagePair_iff hScaleFlow _ _).1 (hp _)) ((tendsto_pnat_coe.comp hK).comp tendsto_succPNat)
      ⟨_, hL', Ks, ms⟩ rfl ⟨ms, ms.pos, rfl⟩ X.1 hX _ ((hconv 4 (by norm_num) X).comp tendsto_succPNat)
    have e : S 4 (by norm_num) X = r := Complex.ofReal_injective hr
    rw [e]
    exact hI
  · intro S hS' d hd X hX
    rcases hS' with ⟨K, m, β, hp, hK, hm, hconv⟩ | ⟨Q, hQ⟩
    · have hsep : InfiniteLattice.IsSeparatedC1cTuple X.1 := by
        obtain ⟨hspace, -⟩ := hB d ϑ hd.1 ⟨hϑ.1, hϑ.2⟩
        have hfQ := hspace.1 hX
        obtain ⟨-, ⟨x, hx⟩, hall⟩ := hspace.2 _ hfQ
        obtain ⟨hsp, -, -⟩ := hall x hx
        exact ⟨fun i => ⟨(X.2.1 i).1, (X.2.1 i).2.1⟩, d, hd.1, fun i k hik => (hsp i k hik).1⟩
      obtain ⟨-, h₂', -⟩ := hLimits d ⟨hd.1, hd.2.trans hd₄L⟩
      obtain ⟨r, hr, hI⟩ := h₂' (fun j => K j.succPNat) (fun j => β j.succPNat) (fun j => m j.succPNat)
        (fun j => (isFirstPassagePair_iff hScaleFlow _ _).1 (hp _)) (fun j => ⟨_, (m _).pos, rfl⟩)
        ((tendsto_pnat_coe.comp hK).comp tendsto_succPNat) ((tendsto_pnat_coe.comp hm).comp tendsto_succPNat)
        X.1 hX hsep _ ((hconv 4 (by norm_num) X).comp tendsto_succPNat)
      have e : S 4 (by norm_num) X = r := Complex.ofReal_injective hr
      rw [e]
      exact hI
    · exact hVol d ⟨hd.1, hd.2.trans hd₄F⟩
        ⟨Q.cutoff, Q.tendsto_cutoff, Q.coupling, fun j => (isFirstPassagePair_iff hScaleFlow _ _).1 (Q.pair j), Q.state,
          Q.isLimit⟩
        S hQ X hX
end YangMills.Construction.TotalDensities
end
