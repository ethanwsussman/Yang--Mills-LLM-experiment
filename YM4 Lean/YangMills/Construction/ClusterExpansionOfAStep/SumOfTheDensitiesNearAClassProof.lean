import YangMills.Construction.ClusterExpansionOfAStep.CutDensitiesOffNear
import YangMills.Construction.ClusterExpansionOfAStep.IntegralOfACutPotential
import YangMills.Construction.ClusterExpansionOfAStep.OffNearDensitiesMoveLittleProof
import YangMills.Construction.ClusterExpansionOfAStep.SumOfTheDensitiesNearAClass
import YangMills.Construction.ClusterExpansionOfAStep.SumOfTheDensitiesOfASplit
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages TorusFields TorusLumps TorusCounting BlockOffsets StepSettings RenormalizationStepParameters StepCosts
  ColdStepAtMirrorFrames Interpolation Restriction
namespace NearComponents
section Geometry
variable {L n : ℕ} [NeZero L] [NeZero n]
theorem exists_site_in_block_supDist_le (hodd : Odd L) (y : TorusSite (n * L)) (Y' : TorusSite n) :
    ∃ y' : TorusSite (n * L), parentBlock L y' = Y' ∧ _root_.YangMills.Construction.TorusFields.supDist y y' ≤ L * _root_.YangMills.Construction.TorusFields.supDist (parentBlock L y) Y' := by
  obtain ⟨e, he, hb⟩ := exists_offset_of_supDist (parentBlock L y) Y'
  obtain ⟨A, o, ho, hc⟩ := exists_block_offset (L := L) hodd fun i => ((y i).cast : ℤ)
  have hyc : y = siteOfInt (blockPoint L A o) := by
    funext i
    have := hc i
    simp only [siteOfInt, blockPoint]
    rw [← this]
    simp
  have hbl : parentBlock L y = siteOfInt A := by
    conv_lhs => rw [hyc]
    exact parentBlock_blockPoint hodd A o ho
  refine ⟨siteOfInt (blockPoint L (A + e) o), ?_, ?_⟩
  · rw [parentBlock_blockPoint hodd _ o ho, siteOfInt_add, ← hbl, he]
  · have h1 : (siteOfInt (blockPoint L (A + e) o) : TorusSite (n * L)) =
        y + siteOfInt fun i => (L : ℤ) * e i := by
      conv_rhs => rw [hyc]
      funext i
      simp only [siteOfInt, blockPoint, Pi.add_apply]
      push_cast
      ring
    rw [h1]
    refine _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le _ _ _ fun i => ?_
    rw [Int.natAbs_mul, Int.natAbs_natCast]
    exact Nat.mul_le_mul_left _ (hb i)
theorem lt_supDist_of_not_mem_blocksNear {r : ℕ} {K : Finset (TorusSite (n * L))} {y k : TorusSite (n * L)}
    (hy : parentBlock L y ∉ blocksNear L r K) (hk : k ∈ K) : 5 * r < _root_.YangMills.Construction.TorusFields.supDist y k := by
  classical
  by_contra h
  push Not at h
  apply hy
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, y, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
  · simp [sitesInBlocks]
  · exact (mem_thickening _ _ _).2 ⟨k, hk, h⟩
theorem lt_supDist_of_mem_chainComponents_ne {M : ℕ} [NeZero M] {r : ℕ} {Y X X' : Finset (TorusSite M)}
    (hX : X ∈ chainComponents r Y) (hX' : X' ∈ chainComponents r Y) (hne : X ≠ X')
    {z z' : TorusSite M} (hz : z ∈ X) (hz' : z' ∈ X') :
    r < _root_.YangMills.Construction.TorusFields.supDist z z' := by exact _root_.YangMills.Construction.FarBlocks.lt_supDist_of_mem_chainComponents_of_ne hX hX' hne hz hz'
end Geometry
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem awayFromCore_of_near_boundary (s : ChartSetting R n) (c : SettingCore R n)
    {𝒦 : Finset (Finset (TorusSite (n * R.params.side)))}
    (h𝒦 : 𝒦 ⊆ s.storedComponents c) (hodd : Odd R.params.side) (hL : 64 * R.params.side ≤ R.range)
    {Y Y' : TorusSite n}
    (hY : Y ∈ blocksNear R.params.side R.range (𝒦.biUnion id))
    (hY' : Y' ∉ blocksNear R.params.side R.range (𝒦.biUnion id))
    (hd : 4 * (R.params.side * _root_.YangMills.Construction.TorusFields.supDist Y Y') ≤ R.range + 12 * R.params.side) : s.AwayFromCore c Y := by
  classical
  intro Z hZ y hy z hz
  have hby : parentBlock R.params.side y = Y := by simpa [sitesInBlocks] using hy
  have hbz : parentBlock R.params.side z = Z := by simpa [sitesInBlocks] using hz
  obtain ⟨u, hu, hzu⟩ : ∃ u ∈ (s.storedComponents c).biUnion id,
      _root_.YangMills.Construction.TorusFields.supDist z u ≤ 4 * R.range + R.params.side := by
    rcases Finset.mem_union.mp hZ with hC | hCore
    · have hzs : z ∈ c.badBonds.image Prod.fst ∪ s.support ∪ sitesInBlocks R.params.side c.core :=
        Finset.mem_union_right _ (by simpa [sitesInBlocks, hbz] using hC)
      obtain ⟨X, hX, hzX⟩ := exists_mem_chainComponents (r := 10 * R.range) hzs
      refine ⟨z, Finset.mem_biUnion.mpr ⟨X, hX, hzX⟩, ?_⟩
      rw [_root_.YangMills.Construction.TorusFields.supDist_self]
      omega
    · obtain ⟨w, hw⟩ := (Finset.mem_filter.mp hCore).2
      obtain ⟨hw1, hw2⟩ := Finset.mem_inter.mp hw
      obtain ⟨u, hu, hwu⟩ := (mem_thickening _ _ _).1 hw2
      have hbw : parentBlock R.params.side w = Z := by simpa [sitesInBlocks] using hw1
      have hzw : _root_.YangMills.Construction.TorusFields.supDist z w ≤ R.params.side := _root_.YangMills.Construction.TorusCounting.supDist_le_of_parentBlock_eq (hbz.trans hbw.symm)
      refine ⟨u, hu, ?_⟩
      have := _root_.YangMills.Construction.TorusFields.supDist_triangle z w u
      omega
  obtain ⟨X, hX, huX⟩ := Finset.mem_biUnion.mp hu
  by_cases hXK : X ∈ 𝒦
  · obtain ⟨y', hy', hyy⟩ := exists_site_in_block_supDist_le hodd y Y'
    rw [hby] at hyy
    have h1 : 5 * R.range < _root_.YangMills.Construction.TorusFields.supDist y' u :=
      lt_supDist_of_not_mem_blocksNear (hy' ▸ hY')
        (Finset.mem_biUnion.mpr ⟨X, hXK, huX⟩ : u ∈ 𝒦.biUnion id)
    have t1 := _root_.YangMills.Construction.TorusFields.supDist_triangle y' y u
    have t2 := _root_.YangMills.Construction.TorusFields.supDist_triangle y z u
    have e1 : _root_.YangMills.Construction.TorusFields.supDist y' y = _root_.YangMills.Construction.TorusFields.supDist y y' := _root_.YangMills.Construction.TorusFields.supDist_comm _ _
    have h2 : R.range < 8 * _root_.YangMills.Construction.TorusFields.supDist y z := by
      generalize R.params.side * _root_.YangMills.Construction.TorusFields.supDist Y Y' = a at *
      omega
    have h3 : (R.range : ℝ) < 8 * supDist y z := by exact_mod_cast h2
    linarith only [h3]
  · obtain ⟨w, hw⟩ := (Finset.mem_filter.mp hY).2
    obtain ⟨hw1, hw2⟩ := Finset.mem_inter.mp hw
    obtain ⟨k, hk, hkd⟩ := (mem_thickening _ _ _).1 hw2
    obtain ⟨X', hX'K, hkX'⟩ := Finset.mem_biUnion.mp hk
    have hbw : parentBlock R.params.side w = Y := by simpa [sitesInBlocks] using hw1
    have hyw : _root_.YangMills.Construction.TorusFields.supDist y w ≤ R.params.side := _root_.YangMills.Construction.TorusCounting.supDist_le_of_parentBlock_eq (hby.trans hbw.symm)
    have hne : X ≠ X' := fun e => hXK (e ▸ hX'K)
    have hfar : 10 * R.range < _root_.YangMills.Construction.TorusFields.supDist u k :=
      lt_supDist_of_mem_chainComponents_ne hX (h𝒦 hX'K) hne huX hkX'
    have t1 := _root_.YangMills.Construction.TorusFields.supDist_triangle u z k
    have t2 := _root_.YangMills.Construction.TorusFields.supDist_triangle z y k
    have t3 := _root_.YangMills.Construction.TorusFields.supDist_triangle y w k
    have e1 : _root_.YangMills.Construction.TorusFields.supDist u z = _root_.YangMills.Construction.TorusFields.supDist z u := _root_.YangMills.Construction.TorusFields.supDist_comm _ _
    have e2 : _root_.YangMills.Construction.TorusFields.supDist z y = _root_.YangMills.Construction.TorusFields.supDist y z := _root_.YangMills.Construction.TorusFields.supDist_comm _ _
    have h2 : R.range < 8 * _root_.YangMills.Construction.TorusFields.supDist y z := by omega
    have h3 : (R.range : ℝ) < 8 * supDist y z := by exact_mod_cast h2
    linarith only [h3]
theorem integral_cutoffProd_mul_exp_pos (hcore : LogIntegralExpInterpolationStatement)
    (hρ : 0 < R.ballRadius) (hp : IsCutoff R.ballRadius R.barrierFn)
    {free : Finset (TorusBond (n * R.params.side))} {D : BlockDensitySplit R n free} (hreg : D.IsRegular) :
    0 < ∫ η, cutoffProd (R := R) η * Real.exp (-D.potential η) := by
  have hBm : MeasurableSet (openBallsIn R free) := measurableSet_openBallsIn
  obtain ⟨hμ, hw, hw0⟩ := cutoffProd_setup (R := R) (free := free) hρ hp
  have hPsi : AEBounded (volume.restrict (openBallsIn R free)) D.totalInteraction :=
    AEBounded.sum _ fun Y _ => aeBounded_interaction hreg Y
  have hΦ : AEBounded (volume.restrict (openBallsIn R free)) fun η => ∑ Y : TorusSite n, D.density Y η :=
    AEBounded.sum _ fun Y _ => aeBounded_density hreg Y
  have hf := hPsi.neg
  obtain ⟨M, a, b⟩ := hf.exists_common_bound hΦ
  have hcr := hcore _ cutoffProd _ _ M hμ hw hw0 hf.1 hΦ.1 a b
  set A₀ : ℝ := R.coupling * D.totalCost 0 - ∑ Y : TorusSite n, D.logJacobian Y 0 with hA₀
  have hL : ∫ η, cutoffProd (R := R) η * Real.exp (-D.potential η) =
      Real.exp (-A₀) * ∫ η, cutoffProd (R := R) η *
        Real.exp (-D.totalInteraction η + 1 * ∑ Y : TorusSite n, D.density Y η)
        ∂(volume.restrict (openBallsIn R free)) := by
    rw [integral_eq_setIntegral_openBallsIn (fun η h => by rw [cutoffProd_eq_zero h]; simp),
      ← integral_const_mul]
    refine setIntegral_congr_fun hBm fun η h => ?_
    show cutoffProd (R := R) η * Real.exp (-D.potential η) =
      Real.exp (-A₀) * (cutoffProd (R := R) η *
        Real.exp (-D.totalInteraction η + 1 * ∑ Y : TorusSite n, D.density Y η))
    rw [potential_eq hreg (openBallsIn_subset_closedBallsIn h)]
    have e : -(D.totalInteraction η + A₀ - ∑ Y : TorusSite n, D.density Y η) =
        -A₀ + (-D.totalInteraction η + 1 * ∑ Y : TorusSite n, D.density Y η) := by ring
    rw [e, Real.exp_add]
    ring
  rw [hL]
  exact mul_pos (Real.exp_pos _) (hcr.1 1)
theorem card_compl_freeNear_eq_sum (s : ChartSetting R n) (N : Finset (TorusSite n)) :
    (((Finset.univ \ s.freeNear N).card : ℕ) : ℝ) =
      ∑ Y ∈ Finset.univ \ N, ((freeBondsAt s.free Y).card : ℝ) := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise (s := Finset.univ \ s.freeNear N) (t := Finset.univ \ N)
    (f := fun b : s.free => bondBlock (R := R) b.1) (fun b hb => by
      have h1 : b ∉ s.freeNear N := (Finset.mem_sdiff.mp hb).2
      have h2 : bondBlock (R := R) b.1 ∉ N := fun hm =>
        h1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩)
      simpa using h2)
  rw [h]
  push_cast
  refine Finset.sum_congr rfl fun Y hY => ?_
  have hYN : Y ∉ N := by simpa using hY
  congr 2
  ext b
  simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and, freeBondsAt]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨fun hm => hYN ?_, h⟩
    have := (Finset.mem_filter.mp hm).2
    rwa [h] at this
end NearComponents
open NearComponents in
set_option maxHeartbeats 1600000 in
theorem densitySumNearComponentsBound_of_parts (hcore : LogIntegralExpInterpolationStatement)
    (hsum : SumActivitiesEqLogIntegral) (hreg : DensitySplitRegular)
    (hint : CutPotentialIntegralFactors) (hfar : CutActivitiesAwayFromNear)
    (hdeep : DeepActivityIgnoresCutoff) (hsize : ActivityNearLevelShare) :
    DensitySumNearComponentsBound := by
  classical
  obtain ⟨r₁, hr₁, hreg⟩ := hreg
  obtain ⟨r₂, hr₂, hfar⟩ := hfar
  obtain ⟨r₃, hr₃, hdeep⟩ := hdeep
  obtain ⟨r₄, hr₄, hsize⟩ := hsize
  refine ⟨fun c => min (min (r₁ c) (r₂ c)) (min (r₃ c) (r₄ c)),
    fun c => lt_min (lt_min (hr₁ c) (hr₂ c)) (lt_min (hr₃ c) (hr₄ c)), fun T hT hrt => ?_⟩
  have hrt1 : T.rt ≤ r₁ T.toChainParameters := hrt.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hrt2 : T.rt ≤ r₂ T.toChainParameters := hrt.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hrt3 : T.rt ≤ r₃ T.toChainParameters := hrt.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrt4 : T.rt ≤ r₄ T.toChainParameters := hrt.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨y₁, hreg⟩ := hreg T hT hrt1
  obtain ⟨Cf, y₂, hCf, hfar⟩ := hfar T hT hrt2
  obtain ⟨y₃, hdeep⟩ := hdeep T hT hrt3
  obtain ⟨Cs, y₄, hCs, hsize⟩ := hsize T hT hrt4
  set r₀ : ℕ := 64 * T.side + 1 with hr₀
  refine ⟨Cf + 2 * Cs + 1, max (max y₁ y₂) (max y₃ (max y₄ (max (Real.exp 1) ((r₀ : ℝ) ^ 100)))),
    by positivity, fun y hy R hR n _ hn s c hs hc hmk 𝒦 h𝒦 => ?_⟩
  have hy1 : y₁ ≤ y := ((le_max_left _ _).trans (le_max_left _ _)).trans hy
  have hy2 : y₂ ≤ y := ((le_max_right _ _).trans (le_max_left _ _)).trans hy
  have hy3 : y₃ ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have hy4 : y₄ ≤ y := ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hy
  have hy5 : Real.exp 1 ≤ y :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))).trans hy
  have hy6 : (r₀ : ℝ) ^ 100 ≤ y :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))).trans hy
  have hlog : 1 ≤ Real.log R.coupling := by
    rw [Real.le_log_iff_exp_le (by
      have := hy5.trans hR.le_coupling
      have h1 := Real.exp_pos 1
      linarith)]
    exact hy5.trans hR.le_coupling
  have hr : r₀ ≤ R.range := le_clusterRange_of_pow_le (hy6.trans hR.le_coupling)
  have hLl : R.params.side = T.side := by rw [hR.params_eq]; rfl
  have hρe : R.ballRadius = T.ballRadius := by
    unfold StepSetup.ballRadius ParameterAssignment.ballRadius
    rw [hR.params_eq]
    rfl
  have hρ : 0 < R.ballRadius := by
    rw [hρe]
    have := hT.σ_pos
    unfold ParameterAssignment.ballRadius
    positivity
  have hp : IsCutoff R.ballRadius R.barrierFn := by
    rw [hρe, hR.barrierFn_eq]
    exact hT.cut
  have hlam : 0 < T.lam := hT.chain.2.2.1
  have hx0 : 0 < R.coupling := by
    have := hy5.trans hR.le_coupling
    have h1 := Real.exp_pos 1
    linarith
  have hodd : Odd R.params.side := hLl ▸ hT.L_odd
  have hsr := hreg y hy1 R hR n hn s hs
  have hfN := hfar y hy2 R hR n hn s c hs hc 𝒦 h𝒦
  have hoffst : ∀ {Y Y' : TorusSite n}, Y ∈ blocksNear R.params.side R.range (𝒦.biUnion id) →
      Y' ∉ blocksNear R.params.side R.range (𝒦.biUnion id) →
      4 * (R.params.side * _root_.YangMills.Construction.TorusFields.supDist Y Y') ≤ R.range + 12 * R.params.side →
      s.AwayFromCore c Y := fun hY hY' hd =>
    awayFromCore_of_near_boundary s c h𝒦 hodd (by rw [hLl]; omega) hY hY' hd
  generalize hN : blocksNear R.params.side R.range (𝒦.biUnion id) = N at hfN hoffst ⊢
  set X := s.freeNear N with hX
  set D := s.restrictedSplit T.lam X with hD
  have hDreg : D.IsRegular := restrictedSplit_isRegular s T.lam X hρ hsr
  have hsplit := hsum R n _ D T.lam hx0 hlam hρ hp hDreg
  have hpos := integral_cutoffProd_mul_exp_pos hcore hρ hp hDreg
  have hI := hint R n s T.lam N
  set A : ℝ := ∫ ζ : s.freeNear N → EuclideanSpace ℝ (Fin 3),
    (∏ b, cutoffFactor R.ballRadius R.barrierFn (coordNorm (ζ b))) *
      Real.exp (-s.potential (s.extendByZero N ζ)) with hA
  have hA0 : 0 ≤ A := integral_nonneg fun ζ =>
    mul_nonneg (Finset.prod_nonneg fun _ _ => cutoffFactor_nonneg _) (Real.exp_pos _).le
  set G := R.bondGaussian T.lam with hG
  set m := (Finset.univ \ X).card with hm
  have hprod : 0 < A * G ^ m := hI ▸ hpos
  have hAne : A ≠ 0 := fun h => by rw [h, zero_mul] at hprod; exact lt_irrefl _ hprod
  have hGne : G ^ m ≠ 0 := fun h => by rw [h, mul_zero] at hprod; exact lt_irrefl _ hprod
  have hApos : 0 < A := lt_of_le_of_ne hA0 (Ne.symm hAne)
  have hnear : s.localIntegral N = Real.exp (s.farEnergy N) * A := by
    unfold ChartSetting.localIntegral
    rw [hA, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
    show (∏ b, cutoffFactor R.ballRadius R.barrierFn (coordNorm (ζ b))) *
        Real.exp (-s.localPotential N ζ) =
      Real.exp (s.farEnergy N) * ((∏ b, cutoffFactor R.ballRadius R.barrierFn (coordNorm (ζ b))) *
        Real.exp (-s.potential (s.extendByZero N ζ)))
    have e : -s.localPotential N ζ = s.farEnergy N + -s.potential (s.extendByZero N ζ) := by
      unfold ChartSetting.localPotential
      ring
    rw [e, Real.exp_add]
    ring
  refine ⟨?_, ?_⟩
  · rw [hnear]
    exact mul_pos (Real.exp_pos _) hApos
  have hlogI : Real.log (s.localIntegral N) = s.farEnergy N + Real.log A := by
    rw [hnear, Real.log_mul (Real.exp_pos _).ne' hAne, Real.log_exp]
  have hlogS : Real.log (∫ η, cutoffProd (R := R) η * Real.exp (-D.potential η)) =
      Real.log A + (m : ℝ) * R.gaussianLogMass T.lam := by
    rw [hI, Real.log_mul hAne hGne, Real.log_pow]
    rfl
  have hparts : ∑ Y ∈ N, D.activity T.lam Y + ∑ Y ∈ Finset.univ \ N, D.activity T.lam Y =
      Real.log A + (m : ℝ) * R.gaussianLogMass T.lam := by
    rw [← hlogS, hsplit, add_comm]
    exact Finset.sum_sdiff (Finset.subset_univ N)
  have hoffsum : s.farEnergy N = ∑ Y ∈ Finset.univ \ N,
      (R.coupling * s.blockCostAt Y 0 - s.blockDensityAt Y 0 - s.logJacobianAt Y 0) := rfl
  have hmcard : (m : ℝ) * R.gaussianLogMass T.lam =
      ∑ Y ∈ Finset.univ \ N, R.gaussianLogMass T.lam * (freeBondsAt s.free Y).card := by
    rw [hm, card_compl_freeNear_eq_sum s N, Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hfarsum : ∑ Y ∈ Finset.univ \ N, (D.activity T.lam Y +
      (R.coupling * s.blockCostAt Y 0 - s.blockDensityAt Y 0 - s.logJacobianAt Y 0) -
        R.gaussianLogMass T.lam * (freeBondsAt s.free Y).card) =
      ∑ Y ∈ Finset.univ \ N, D.activity T.lam Y + s.farEnergy N - (m : ℝ) * R.gaussianLogMass T.lam := by
    rw [hoffsum, hmcard, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hfarsum] at hfN
  have hblock : ∀ Y ∈ N, |s.blockActivity T.lam Y - D.activity T.lam Y| ≤
      1 + 2 * Cs * Real.log R.coupling := by
    intro Y hY
    have hCl : 0 ≤ 2 * Cs * Real.log R.coupling := by positivity
    by_cases hd : ∀ Y' : TorusSite n, Y' ∉ N → (R.range : ℝ) / (4 * T.side) + 3 ≤ _root_.YangMills.Construction.TorusFields.supDist Y Y'
    · have := hdeep y hy3 R hR n hn s hs N Y hY hd
      linarith only [this, hCl]
    · push Not at hd
      obtain ⟨Y', hY', hlt⟩ := hd
      have hLpos : (0 : ℝ) < T.side := by
        have : 0 < T.side := by
          have := hT.L_ge
          omega
        exact_mod_cast this
      have hnat : 4 * (R.params.side * _root_.YangMills.Construction.TorusFields.supDist Y Y') ≤ R.range + 12 * R.params.side := by
        rw [hLl]
        have h1 : (4 * ((T.side : ℝ) * _root_.YangMills.Construction.TorusFields.supDist Y Y')) ≤ R.range + 12 * T.side := by
          have h2 : (_root_.YangMills.Construction.TorusFields.supDist Y Y' : ℝ) * (4 * T.side) <
              ((R.range : ℝ) / (4 * T.side) + 3) * (4 * T.side) :=
            mul_lt_mul_of_pos_right hlt (by positivity)
          have h3 : ((R.range : ℝ) / (4 * T.side) + 3) * (4 * T.side) = R.range + 12 * T.side := by
            field_simp
            ring
          rw [h3] at h2
          linarith only [h2]
        exact_mod_cast h1
      have hst := hoffst hY hY' hnat
      have hb := hsize y hy4 R hR n hn s hs
      have h1 := (hb.1 c Y hc hmk hst).1
      have hfree : s.freeBondsOf Y ⊆ X := by
        intro b hb'
        have h3 : bondBlock (R := R) b.1 = Y := (Finset.mem_filter.mp hb').2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h3 ▸ hY⟩
      have h2 := (hb.1 c Y hc hmk hst).2 X hfree
      have h3 := abs_sub_le (s.blockActivity T.lam Y)
        (-(R.coupling * levelShare R.params.coupling R.params.side (R.depth + 1) s.region Y s.coarse))
        (D.activity T.lam Y)
      rw [sub_neg_eq_add,
        sub_eq_add_neg
          (-(R.coupling * levelShare R.params.coupling R.params.side (R.depth + 1) s.region Y s.coarse)),
        ← neg_add, abs_neg,
        add_comm (R.coupling * levelShare R.params.coupling R.params.side (R.depth + 1) s.region Y s.coarse)]
        at h3
      linarith only [h1, h2, h3]
  have hNsum : |∑ Y ∈ N, s.blockActivity T.lam Y - ∑ Y ∈ N, D.activity T.lam Y| ≤
      (N.card : ℝ) * (1 + 2 * Cs * Real.log R.coupling) := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ _Y ∈ N, (1 + 2 * Cs * Real.log R.coupling) := Finset.sum_le_sum hblock
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hrR : (1 : ℝ) ≤ R.range := by
    have : 1 ≤ R.range := by omega
    exact_mod_cast this
  have hr4R : (1 : ℝ) ≤ (R.range : ℝ) ^ 4 := one_le_pow₀ hrR
  have hcard0 : (0 : ℝ) ≤ N.card := Nat.cast_nonneg _
  have hlogpos : 0 < Real.log R.coupling := by linarith only [hlog]
  set rl : ℝ := (R.range : ℝ) ^ 4 * Real.log R.coupling with hrl
  have hrl1 : Real.log R.coupling ≤ rl := le_mul_of_one_le_left hlogpos.le hr4R
  have hbr : 1 + 2 * Cs * Real.log R.coupling ≤ (1 + 2 * Cs) * rl := by
    have h1 : 1 ≤ rl := hlog.trans hrl1
    have h2 : 2 * Cs * Real.log R.coupling ≤ 2 * Cs * rl :=
      mul_le_mul_of_nonneg_left hrl1 (by positivity)
    linarith only [h1, h2]
  have hN2 : (N.card : ℝ) * (1 + 2 * Cs * Real.log R.coupling) ≤ (N.card : ℝ) * ((1 + 2 * Cs) * rl) :=
    mul_le_mul_of_nonneg_left hbr hcard0
  have hmain : ∑ Y ∈ N, s.blockActivity T.lam Y - Real.log (s.localIntegral N) =
      (∑ Y ∈ N, s.blockActivity T.lam Y - ∑ Y ∈ N, D.activity T.lam Y) -
        (∑ Y ∈ Finset.univ \ N, D.activity T.lam Y + s.farEnergy N -
          (m : ℝ) * R.gaussianLogMass T.lam) := by
    rw [hlogI]
    linarith only [hparts]
  rw [hmain]
  refine (abs_sub _ _).trans ?_
  have e : (Cf + 2 * Cs + 1) * (R.range : ℝ) ^ 4 * Real.log R.coupling * (N.card : ℝ) =
      Cf * (R.range : ℝ) ^ 4 * Real.log R.coupling * (N.card : ℝ) + (N.card : ℝ) * ((1 + 2 * Cs) * rl) := by
    rw [hrl]
    ring
  rw [e]
  linarith only [hNsum, hN2, hfN]
end YangMills.Construction.ClusterExpansionOfAStep
end
