import YangMills.Construction.ClusterExpansionOfAStep.MeanOfTheGainProof
import YangMills.Construction.ClusterExpansionOfAStep.CostAtTheFramesIsTheShare
import YangMills.Construction.ClusterExpansionOfAStep.CutOfASplit
import YangMills.Construction.ClusterExpansionOfAStep.FloorsOfTheParameters
import YangMills.Construction.ClusterExpansionOfAStep.MeanOfTheGain
import YangMills.Construction.ClusterExpansionOfAStep.SizeOfTheGaussianOfABond
import YangMills.Construction.ClusterExpansionOfAStep.SizeOfTheLogOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.ThreeFactsOfAnExpansion
import YangMills.Construction.ColdChainAtEveryLevel.FlatTopCostsNothing
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction
open TorusFields TorusLumps StepSettings RenormalizationStepParameters StepCosts StepFloors BlockAverages ColdStepAtMirrorFrames
namespace ClusterExpansionOfAStep
namespace DensityBound
variable {R : StepSetup} {n : ℕ}
theorem coordNorm_eq_norm (z : EuclideanSpace ℝ (Fin 3)) : coordNorm z = ‖z‖ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.coordNorm_eq_norm <;> assumption
theorem card_parentBlock_fibre_le [NeZero n] (L : ℕ) [NeZero L] (Y : TorusSite n) :
    ((Finset.univ : Finset (TorusSite (n * L))).filter fun x => parentBlock L x = Y).card ≤ L ^ 4 := by
  classical
  have hL : (0 : ℤ) < (L : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hcard : (Fintype.piFinset fun _ : Fin 4 => Finset.Ico (0 : ℤ) (L : ℤ)).card = L ^ 4 := by
    rw [Fintype.card_piFinset]
    simp
  rw [← hcard]
  refine Finset.card_le_card_of_injOn
    (fun x i => (((x i).cast : ℤ) + ((L : ℤ) - 1) / 2) % (L : ℤ)) ?_ ?_
  · intro x _
    refine Fintype.mem_piFinset.mpr fun i => ?_
    simp only [Finset.mem_Ico]
    exact ⟨Int.emod_nonneg _ hL.ne', Int.emod_lt_of_pos _ hL⟩
  · intro x hx x' hx' hf
    have hxY : parentBlock L x = Y := by simpa using hx
    have hx'Y : parentBlock L x' = Y := by simpa using hx'
    funext i
    have hq := congrFun (hxY.trans hx'Y.symm) i
    simp only [parentBlock] at hq
    have hm := congrFun hf i
    simp only at hm
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hq
    set u : ℤ := (x i).cast with hu
    set u' : ℤ := (x' i).cast with hu'
    set h : ℤ := ((L : ℤ) - 1) / 2
    have e1 := Int.mul_ediv_add_emod (u + h) (L : ℤ)
    have e2 := Int.mul_ediv_add_emod (u' + h) (L : ℤ)
    have hd : u' - u = (L : ℤ) * ((u' + h) / (L : ℤ) - (u + h) / (L : ℤ)) := by
      rw [hm] at e1
      linarith
    obtain ⟨k, hk⟩ := hq
    have hdiv : ((n * L : ℕ) : ℤ) ∣ u' - u := by
      refine ⟨k, ?_⟩
      rw [hd, hk]
      push_cast
      ring
    have hcast : ((u : ℤ) : ZMod (n * L)) = ((u' : ℤ) : ZMod (n * L)) :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr hdiv
    rw [hu, hu', ZMod.intCast_zmod_cast, ZMod.intCast_zmod_cast] at hcast
    exact hcast
theorem abs_weightedMean_le {m : ℕ} {free : Finset (TorusBond m)} {d G : FreeCoords free → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hd : ∀ η, 0 ≤ d η) (hG : ∀ η, d η ≠ 0 → |G η| ≤ M) : |weightedMean d G| ≤ M := by
  unfold weightedMean
  by_cases hI : Integrable d
  · have hnn : 0 ≤ ∫ η, d η := integral_nonneg hd
    rcases hnn.eq_or_lt with h0 | hpos
    · rw [← h0, div_zero, abs_zero]
      exact hM
    · rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
      have hle : ‖∫ η, G η * d η‖ ≤ ∫ η, M * d η := by
        refine norm_integral_le_of_norm_le (hI.const_mul M) (Filter.Eventually.of_forall fun η => ?_)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hd η)]
        by_cases h : d η = 0
        · rw [h]
          simp
        · exact mul_le_mul_of_nonneg_right (hG η h) (hd η)
      rw [integral_const_mul] at hle
      simpa using hle
  · rw [integral_undef hI, div_zero, abs_zero]
    exact hM
theorem coordNorm_le_of_cutoffProd_ne_zero {free : Finset (TorusBond (n * R.params.side))} {η : FreeCoords free}
    (h : cutoffProd (R := R) η ≠ 0) : ∀ b, coordNorm (η b) ≤ R.ballRadius := by
  intro b
  have hb : cutoffFactor R.ballRadius R.barrierFn (coordNorm (η b)) ≠ 0 := by
    intro h0
    exact h (Finset.prod_eq_zero (Finset.mem_univ b) h0)
  unfold cutoffFactor at hb
  by_contra hn
  rw [not_le] at hn
  exact hb (if_neg (not_lt.mpr hn.le))
theorem cutoffProd_nonneg {free : Finset (TorusBond (n * R.params.side))} (η : FreeCoords free) :
    0 ≤ cutoffProd (R := R) η := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.cutoffProd_nonneg <;> assumption
theorem inBalls_restrictTo [NeZero n] (s : ChartSetting R n) (hρ : 0 ≤ R.ballRadius) (X : Finset s.free)
    {η : FreeCoords s.free} (h : ∀ b, coordNorm (η b) ≤ R.ballRadius) : s.InBalls (s.restrictTo X η) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GainMean.inBalls_restrictTo <;> assumption
theorem restrictTo_zero [NeZero n] (s : ChartSetting R n) (X : Finset s.free) : s.restrictTo X 0 = 0 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.Restriction.restrictTo_zero <;> assumption
theorem restrictTo_univ [NeZero n] (s : ChartSetting R n) (η : FreeCoords s.free) :
    s.restrictTo Finset.univ η = η := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.Restriction.restrictTo_univ <;> assumption
theorem activity_restrictedSplit_univ [NeZero n] (s : ChartSetting R n) (lam : ℝ) (Y : TorusSite n) :
    (s.restrictedSplit lam Finset.univ).activity lam Y = s.blockActivity lam Y := by
  have hcost : (s.restrictedSplit lam Finset.univ).cost = s.blockCostAt := by
    funext Y η
    show s.blockCostAt Y (s.restrictTo Finset.univ η) +
      lam / 2 * ∑ b ∈ freeBondsAt s.free Y \ Finset.univ, ‖η b‖ ^ 2 = _
    have he : freeBondsAt s.free Y \ Finset.univ = ∅ :=
      Finset.sdiff_eq_empty_iff_subset.mpr (Finset.subset_univ _)
    rw [restrictTo_univ, he]
    simp
  have hjac : (s.restrictedSplit lam Finset.univ).logJacobian = s.logJacobianAt := by
    funext Y η
    show s.logJacobianAt Y (s.restrictTo Finset.univ η) = _
    rw [restrictTo_univ]
  have hdens : (s.restrictedSplit lam Finset.univ).density = s.blockDensityAt := by
    funext Y η
    show s.blockDensityAt Y (s.restrictTo Finset.univ η) = _
    rw [restrictTo_univ]
  have h : s.restrictedSplit lam Finset.univ = s.densitySplit := by
    cases hD : s.restrictedSplit lam Finset.univ with
    | mk c j p =>
      rw [hD] at hcost hjac hdens
      simp only at hcost hjac hdens
      subst hcost hjac hdens
      rfl
  rw [h]
  rfl
theorem storedBlockSet_empty [NeZero n] (s : ChartSetting R n) (h : s.support = ∅) :
    s.storedBlockSet ⟨∅, ∅⟩ = ∅ := by
  classical
  have hb : sitesInBlocks R.params.side (∅ : Finset (TorusSite n)) = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun x hx => ?_
    have := (Finset.mem_filter.mp hx).2
    simp at this
  have hc : s.storedComponents (⟨∅, ∅⟩ : SettingCore R n) = ∅ := by
    show chainComponents (10 * R.range) ((∅ : Finset (TorusBond (n * R.params.side))).image Prod.fst ∪
      s.support ∪ sitesInBlocks R.params.side ∅) = ∅
    rw [hb, h]
    simp [chainComponents]
  show (∅ : Finset (TorusSite n)) ∪ coreBlocks R.params.side R.range ((s.storedComponents ⟨∅, ∅⟩).biUnion id) = ∅
  rw [hc]
  refine Finset.eq_empty_of_forall_notMem fun Z hZ => ?_
  rw [Finset.empty_union] at hZ
  obtain ⟨x, hx⟩ := (Finset.mem_filter.mp hZ).2
  have hx2 := (Finset.mem_filter.mp (Finset.mem_inter.mp hx).2).2
  simp at hx2
end DensityBound
set_option maxHeartbeats 4000000 in
open DensityBound in
theorem activityNearLevelShare_holds (hMean : GainMeanLogBound) (hCostS : FrameCostNearLevelShare)
    (hLog : LogJacobianBound) (hGauss : GaussianLogMassLeLog)
    (hThree : ExpansionBasicBounds) (hFloors : EventuallyFloorConditions)
    (hFlat : flatTopVanishingStatement) : ActivityNearLevelShare := by
  classical
  obtain ⟨rt₀, hrt₀, hM⟩ := hMean
  refine ⟨rt₀, hrt₀, fun T hT hrt => ?_⟩
  obtain ⟨Cm, ym, hCm, hMT⟩ := hM T hT hrt
  obtain ⟨C1, c1, y1, hC1, hc1, hCost⟩ := hCostS T hT
  obtain ⟨Cj, yj, hCj, hJ⟩ := hLog T hT
  have hρT : 0 < T.ballRadius := by
    have := hT.σ_pos
    unfold ParameterAssignment.ballRadius
    positivity
  obtain ⟨_, _, hlam, _⟩ := hT.chain
  obtain ⟨Cg, yg, hCg, hG⟩ := hGauss T.lam T.ballRadius T.cutoff hlam hρT hT.cut
  have hE1 : 1 ≤ T.E := by
    have := hT.B_ge
    unfold ParameterAssignment.E
    linarith
  set Cf : ℝ := C1 + 1 + 4 * (T.n₀ : ℝ) + 2 ^ 16 with hCf
  have hCf0 : 0 < Cf := by positivity
  obtain ⟨yf, hF⟩ := hFloors T hT Cf c1 hCf0 hc1
  set L4 : ℝ := (T.side : ℝ) ^ 4 with hL4
  have hL40 : 0 ≤ L4 := by positivity
  have hkey : ∃ C y₀ : ℝ, 0 < C ∧ ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y →
      ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n → ∀ s : ChartSetting R n, s.IsAdmissible →
        ∀ (c : SettingCore R n) (Y : TorusSite n), s.IsCoreOf c → s.IsMarked c → s.AwayFromCore c Y →
          ∀ X : Finset s.free, s.freeBondsOf Y ⊆ X →
            |(s.restrictedSplit T.lam X).activity T.lam Y +
              R.coupling * levelShare R.params.coupling R.params.side (R.depth + 1) s.region Y s.coarse| ≤
              C * Real.log R.coupling := by
    refine ⟨1 + Cj + Cg * (L4 * 4) + Cm + 2 * T.E * L4,
      max (max (max ym y1) (max yj yg)) (max (max yf T.floorMin) (Real.exp 1)),
      by positivity, fun y hy R hR n _ hn s hs c Y hst hmk hoff X hX => ?_⟩
    simp only [max_le_iff] at hy
    obtain ⟨⟨⟨hym, hy1⟩, hyj, hyg⟩, ⟨hyf, hyT⟩, hye⟩ := hy
    have hx : y ≤ R.coupling := hR.le_coupling
    have hxe : Real.exp 1 ≤ R.coupling := hye.trans hx
    have hxpos : 0 < R.coupling := (Real.exp_pos 1).trans_le hxe
    have hx1 : 1 ≤ R.coupling := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have hlog1 : 1 ≤ Real.log R.coupling := by
      have := Real.log_le_log (Real.exp_pos 1) hxe
      rwa [Real.log_exp] at this
    have hLe : R.params.side = T.side := by rw [hR.params_eq]; rfl
    have hEe : R.params.E = T.E := by rw [hR.params_eq]; rfl
    have hσe : R.params.threshold = T.threshold := by rw [hR.params_eq]; rfl
    have hn₀e : R.params.n₀ = T.n₀ := by rw [hR.params_eq]; rfl
    have hρe : R.ballRadius = T.ballRadius := by
      show R.params.threshold / 64 = T.threshold / 64
      rw [hσe]
    have hρ0 : 0 ≤ R.ballRadius := by rw [hρe]; exact hρT.le
    have hFx := hF R.coupling (hyf.trans hx)
    set D := s.restrictedSplit T.lam X with hD
    set a := levelShare R.params.coupling R.params.side (R.depth + 1) s.region Y s.coarse with ha
    set I₁ := ∫ τ in (0 : ℝ)..1, weightedMean (D.interpolatedDensity T.lam τ)
      (fun η => D.interaction Y η - gaussianPart T.lam Y η) with hI₁
    set I₂ := ∫ ν in (0 : ℝ)..1, weightedMean (D.perturbedDensity ν) (D.density Y) with hI₂
    have hzeta : D.activity T.lam Y + R.coupling * a = -(R.coupling * (s.blockCostAt Y 0 - a)) +
        s.logJacobianAt Y 0 + R.gaussianLogMass T.lam * ((freeBondsAt s.free Y).card : ℝ) - I₁ + I₂ := by
      have hc0 : D.cost Y 0 = s.blockCostAt Y 0 := by
        simp [hD, ChartSetting.restrictedSplit, restrictTo_zero]
      have hj0 : D.logJacobian Y 0 = s.logJacobianAt Y 0 := by
        simp [hD, ChartSetting.restrictedSplit, restrictTo_zero]
      show -(R.coupling * D.cost Y 0) + D.logJacobian Y 0 +
        R.gaussianLogMass T.lam * ((freeBondsAt s.free Y).card : ℝ) - I₁ + I₂ + R.coupling * a = _
      rw [hc0, hj0]
      ring
    have t1 : |R.coupling * (s.blockCostAt Y 0 - a)| ≤ 1 := by
      have h1 := hCost y hy1 R hR n hn s hs c Y hst hmk hoff
      have h2 := hFx.stretched_tail.1
      have hr : (R.range : ℝ) = (clusterRange R.coupling : ℝ) := rfl
      rw [hr, neg_mul] at h1
      have h3 : R.coupling * R.coupling ^ C1 ≤ R.coupling ^ Cf := by
        have : R.coupling * R.coupling ^ C1 = R.coupling ^ (C1 + 1) := by
          rw [Real.rpow_add hxpos, Real.rpow_one, mul_comm]
        rw [this]
        exact Real.rpow_le_rpow_of_exponent_le hx1 (by
          have : (0 : ℝ) ≤ 4 * (T.n₀ : ℝ) + 2 ^ 16 := by positivity
          rw [hCf]
          linarith)
      have hCf1 : 1 ≤ Cf := by
        have : (0 : ℝ) ≤ 4 * (T.n₀ : ℝ) := by positivity
        rw [hCf]
        nlinarith
      have hE0 := Real.exp_pos (-(c1 * (clusterRange R.coupling : ℝ)))
      have h4 : Real.exp (-(R.coupling ^ (1 / 200 : ℝ))) ≤ 1 := by
        refine Real.exp_le_one_iff.mpr ?_
        have := Real.rpow_nonneg hxpos.le (1 / 200 : ℝ)
        linarith
      have hpow : 0 ≤ R.coupling ^ Cf := Real.rpow_nonneg hxpos.le _
      rw [abs_mul, abs_of_pos hxpos]
      calc R.coupling * |s.blockCostAt Y 0 - a|
            ≤ R.coupling * (R.coupling ^ C1 * Real.exp (-(c1 * (clusterRange R.coupling : ℝ)))) :=
            mul_le_mul_of_nonneg_left h1 hxpos.le
        _ = R.coupling * R.coupling ^ C1 * Real.exp (-(c1 * (clusterRange R.coupling : ℝ))) := by ring
        _ ≤ R.coupling ^ Cf * Real.exp (-(c1 * (clusterRange R.coupling : ℝ))) :=
            mul_le_mul_of_nonneg_right h3 hE0.le
        _ ≤ Cf * R.coupling ^ Cf * Real.exp (-(c1 * (clusterRange R.coupling : ℝ))) := by
            have : 0 ≤ R.coupling ^ Cf * Real.exp (-(c1 * (clusterRange R.coupling : ℝ))) := by positivity
            nlinarith
        _ ≤ 1 := h2.trans h4
    have hzero : s.InBalls (0 : FreeCoords s.free) := by
      intro b
      simpa [coordNorm_eq_norm] using hρ0
    have t2 := hJ y R hR.params_eq hR.anchorRadius_eq (hyj.trans hx) n s Y 0 hzero
    have hcardL : ((freeBondsAt s.free Y).card : ℝ) ≤ L4 * 4 := by
      have h1 := card_parentBlock_fibre_le (n := n) R.params.side Y
      have h2 : (freeBondsAt s.free Y).card ≤
          (((Finset.univ : Finset (TorusSite (n * R.params.side))).filter
            fun x => parentBlock R.params.side x = Y) ×ˢ (Finset.univ : Finset (Fin 4))).card := by
        refine Finset.card_le_card_of_injOn (fun b => b.1) ?_ ?_
        · intro b hb
          have hb' : bondBlock (R := R) b.1 = Y := by simpa [freeBondsAt] using hb
          simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_filter,
            Finset.mem_univ, true_and, and_true]
          exact hb'
        · intro b _ b' _ h
          exact Subtype.ext h
      rw [Finset.card_product] at h2
      simp only [Finset.card_univ, Fintype.card_fin] at h2
      have h3 : (freeBondsAt s.free Y).card ≤ R.params.side ^ 4 * 4 := h2.trans (Nat.mul_le_mul_right 4 h1)
      have h4 : ((freeBondsAt s.free Y).card : ℝ) ≤ (R.params.side : ℝ) ^ 4 * 4 := by exact_mod_cast h3
      have hLr : (R.params.side : ℝ) = (T.side : ℝ) := by rw [hLe]
      rw [hLr] at h4
      exact h4
    have t3 : |R.gaussianLogMass T.lam * ((freeBondsAt s.free Y).card : ℝ)| ≤
        Cg * Real.log R.coupling * (L4 * 4) := by
      have h1 := hG R hρe (by rw [hR.barrierFn_eq]) (hyg.trans hx)
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _ : (0 : ℝ) ≤ ((freeBondsAt s.free Y).card : ℝ))]
      exact mul_le_mul h1 hcardL (Nat.cast_nonneg _) (by positivity)
    have t4 : |I₁| ≤ Cm * Real.log R.coupling := by
      have h1 : ‖I₁‖ ≤ Cm * Real.log R.coupling * |(1 : ℝ) - 0| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const fun τ hτ => ?_
        have hτ' := Set.uIoc_of_le (zero_le_one' ℝ) ▸ hτ
        exact hMT y hym R hR n hn s hs c Y hst hmk hoff X hX τ hτ'.1.le hτ'.2
      simpa using h1
    have hfits : R.params.Admissible := by
      rw [hR.params_eq]
      exact hT.fits y hyT
    have hE1' : 1 ≤ R.params.E := by rw [hEe]; exact hE1
    have hrange : 4 * R.params.n₀ + 2 ^ 16 ≤ clusterRange R.coupling := by
      have h1 := hFx.range_ge
      have h2 : ((4 * R.params.n₀ + 2 ^ 16 : ℕ) : ℝ) ≤ (clusterRange R.coupling : ℝ) := by
        rw [hn₀e]
        push_cast
        rw [hCf] at h1
        linarith
      exact_mod_cast h2
    have hrow := hR.isStep.1
    have hthree := (hThree R.params R.depth R.coupling R.functional R.density R.labels R.labelWeight
      R.clusterFactor R.siteDensity hfits hE1' hxpos hrange hrow.1 hrow.2).2.1
    have hside : IsBlockTorusSide R.params (n * R.params.side) :=
      ⟨Dvd.intro_left _ rfl, by
        rw [mul_comm]
        exact Nat.mul_le_mul_right _ (by rw [hn₀e]; exact hn)⟩
    have hfar : ∀ y' ∈ sitesInBlocks R.params.side {Y}, ∀ z ∈ s.support,
        (clusterRange R.coupling : ℝ) / 4 ≤ supDist y' z := by
      intro y' hy' z hz
      by_contra hlt
      rw [not_le] at hlt
      have hle : supDist y' z ≤ 4 * R.range := by
        have h1 : (supDist y' z : ℝ) ≤ ((4 * R.range : ℕ) : ℝ) := by
          have hr : (R.range : ℝ) = (clusterRange R.coupling : ℝ) := rfl
          have h0 : (0 : ℝ) ≤ (clusterRange R.coupling : ℝ) := Nat.cast_nonneg _
          push_cast
          rw [hr]
          linarith
        exact_mod_cast h1
      have hθ : z ∈ (s.storedComponents c).biUnion id := by
        refine Finset.mem_biUnion.mpr ?_
        have hU : z ∈ c.badBonds.image Prod.fst ∪ s.support ∪ sitesInBlocks R.params.side c.core :=
          Finset.mem_union_left _ (Finset.mem_union_right _ hz)
        refine ⟨_, Finset.mem_image.mpr ⟨z, hU, rfl⟩, ?_⟩
        exact Finset.mem_filter.mpr ⟨hU, Relation.ReflTransGen.refl⟩
      have hY : Y ∈ s.storedBlockSet c := by
        refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
        exact ⟨y', Finset.mem_inter.mpr ⟨hy', Finset.mem_filter.mpr ⟨Finset.mem_univ _, z, hθ, hle⟩⟩⟩
      have h0 := hoff Y hY y' hy' y' hy'
      have h1 : supDist y' y' = 0 := by simp [supDist]
      rw [h1] at h0
      have : (0 : ℝ) ≤ (R.range : ℝ) := Nat.cast_nonneg _
      simp at h0
      linarith
    have hphi : ∀ ζ : FreeCoords s.free, s.InBalls ζ → |s.blockDensityAt Y ζ| ≤ 2 * T.E * L4 := by
      intro ζ hζ
      have hcard : ((sitesInBlocks R.params.side {Y}).card : ℝ) ≤ L4 := by
        have h1 := card_parentBlock_fibre_le (n := n) R.params.side Y
        have h2 : (sitesInBlocks R.params.side {Y}).card ≤
            ((Finset.univ : Finset (TorusSite (n * R.params.side))).filter
              fun x => parentBlock R.params.side x = Y).card := by
          refine Finset.card_le_card fun x hx => ?_
          simpa [sitesInBlocks] using hx
        have h3 : ((sitesInBlocks R.params.side {Y}).card : ℝ) ≤ (R.params.side : ℝ) ^ 4 := by
          exact_mod_cast h2.trans h1
        have hLr : (R.params.side : ℝ) = (T.side : ℝ) := by rw [hLe]
        rw [hLr] at h3
        exact h3
      show |∑ y' ∈ sitesInBlocks R.params.side {Y},
        R.siteDensity (n * R.params.side) y' (s.field ζ) s.support s.labelling| ≤ _
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have h1 : ∀ y' ∈ sitesInBlocks R.params.side {Y},
          |R.siteDensity (n * R.params.side) y' (s.field ζ) s.support s.labelling| ≤ 2 * T.E := by
        intro y' hy'
        have := hthree (n * R.params.side) hside (s.field ζ) s.support s.labelling y'
          (hs.isHull ζ hζ) (hs.factor_ne_zero ζ hζ) (hfar y' hy')
        rwa [hEe] at this
      refine (Finset.sum_le_sum h1).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      have : 0 ≤ 2 * T.E := by linarith
      nlinarith
    have t5 : |I₂| ≤ 2 * T.E * L4 := by
      have hM0 : 0 ≤ 2 * T.E * L4 := by
        have : 0 ≤ 2 * T.E := by linarith
        positivity
      have h1 : ‖I₂‖ ≤ 2 * T.E * L4 * |(1 : ℝ) - 0| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const fun ν _ => ?_
        rw [Real.norm_eq_abs]
        refine abs_weightedMean_le hM0 (fun η => ?_) fun η hη => ?_
        · exact mul_nonneg (cutoffProd_nonneg η) (Real.exp_pos _).le
        · have hc : cutoffProd (R := R) η ≠ 0 := fun h0 => hη (by
            show cutoffProd (R := R) η * _ = 0
            rw [h0, zero_mul])
          exact hphi _ (inBalls_restrictTo s hρ0 X (coordNorm_le_of_cutoffProd_ne_zero hc))
      simpa using h1
    rw [hzeta]
    have hneg : |-(R.coupling * (s.blockCostAt Y 0 - a))| ≤ 1 := by rwa [abs_neg]
    have e1 := abs_add_le (-(R.coupling * (s.blockCostAt Y 0 - a)) + s.logJacobianAt Y 0 +
      R.gaussianLogMass T.lam * ((freeBondsAt s.free Y).card : ℝ) - I₁) I₂
    have e2 := abs_sub (-(R.coupling * (s.blockCostAt Y 0 - a)) + s.logJacobianAt Y 0 +
      R.gaussianLogMass T.lam * ((freeBondsAt s.free Y).card : ℝ)) I₁
    have e3 := abs_add_le (-(R.coupling * (s.blockCostAt Y 0 - a)) + s.logJacobianAt Y 0)
      (R.gaussianLogMass T.lam * ((freeBondsAt s.free Y).card : ℝ))
    have e4 := abs_add_le (-(R.coupling * (s.blockCostAt Y 0 - a))) (s.logJacobianAt Y 0)
    have hEL : 0 ≤ 2 * T.E * L4 := by
      have : 0 ≤ 2 * T.E := by linarith
      positivity
    nlinarith
  obtain ⟨C, y₀, hC, hB⟩ := hkey
  refine ⟨C, y₀, hC, fun y hy R hR n _ hn s hs => ⟨fun c Y hst hmk hoff => ⟨?_, fun X hX =>
    hB y hy R hR n hn s hs c Y hst hmk hoff X hX⟩, fun hst hmk hV hYt Y => ?_⟩⟩
  · rw [← activity_restrictedSplit_univ]
    exact hB y hy R hR n hn s hs c Y hst hmk hoff _ (Finset.subset_univ _)
  · have hoff : s.AwayFromCore ⟨∅, ∅⟩ Y := by
      intro Z hZ
      rw [storedBlockSet_empty s hYt] at hZ
      simp at hZ
    have h1 := hB y hy R hR n hn s hs ⟨∅, ∅⟩ Y hst hmk hoff _ (Finset.subset_univ _)
    rw [activity_restrictedSplit_univ] at h1
    have hLe : R.params.side = T.side := by rw [hR.params_eq]; rfl
    have haR : R.params.coupling = T.coupling := by rw [hR.params_eq]; rfl
    have hsh : levelShare R.params.coupling R.params.side (R.depth + 1) s.region Y s.coarse = 0 := by
      rw [hV]
      exact (hFlat (torusFrame R.params.side R.depth n) R.params.coupling _ (by rw [haR]; linarith [hT.a_ge])
        (by show Odd R.params.side; rw [hLe]; exact hT.L_odd)).2.2 _
    rwa [hsh, mul_zero, add_zero] at h1
end ClusterExpansionOfAStep
end YangMills.Construction
end
