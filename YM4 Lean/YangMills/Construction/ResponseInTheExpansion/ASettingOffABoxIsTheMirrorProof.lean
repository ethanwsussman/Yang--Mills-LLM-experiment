import YangMills.Construction.ClusterExpansionOfAStep.ColdSettingIsASetting
import YangMills.Construction.ClusterExpansionOfAStep.MarkedIntegralsAreCarriedProof
import YangMills.Construction.ResponseInTheExpansion.ASettingOffABoxIsTheMirror
import YangMills.Construction.ResponseInTheExpansion.ImageResponseIsAMeanOfTheGasProof
import YangMills.Construction.ResponseInTheExpansion.MeanInTheColdSetting
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation RenormalizationStepParameters StepSettings StepCosts StepMarks TorusFields TorusLumps
  TorusCharts TopLevelSites BlockTrees BlockOffsets BlockZones BoxAgreement TorusMirror WeightedResponses
namespace ResponseInTheExpansion
namespace SettingNearColdMirror
private theorem imaginaryComponent_toImaginary (c : Fin 3) (v : EuclideanSpace ℝ (Fin 3)) :
    imaginaryComponent c (toImaginary v) = v c := by
  fin_cases c <;> rfl
private theorem norm_frameCoord_le {n : ℕ} (ℓ : TorusLumps.StepParameters) (ρA : ℝ) (hρ : 0 ≤ ρA) (t m : ℕ)
    (V : TorusField n) (b : TorusBond (n * ℓ.side)) :
    ‖((frameCoord ℓ ρA t m V b : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ ρA := by apply _root_.YangMills.Construction.StepInvariance.norm_frameCoord_le <;> assumption
private theorem weightedMean_congr {n : ℕ} {free : Finset (TorusBond n)} {d G G' : FreeCoords free → ℝ}
    (h : ∀ η, d η ≠ 0 → G η = G' η) : weightedMean d G = weightedMean d G' := by apply _root_.YangMills.SharedProofs.p17143 <;> assumption
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem inBalls_of_chartDensity_ne_zero (s : ChartSetting R n) {η : FreeCoords s.free}
    (h : chartDensity s η ≠ 0) : s.InBalls η := by apply _root_.YangMills.SharedProofs.p4538 <;> assumption
private theorem frameDeviation_of_free (s : ChartSetting R n) (hc : s.free ⊆ chartBonds R.params.side n)
    (hL : Odd R.params.side) (hn : 2 ≤ n) (hρA : 0 ≤ R.anchorRadius) (hρA' : R.anchorRadius ≤ 1)
    (hρ : R.ballRadius ≤ 1) {η : FreeCoords s.free} (hη : s.InBalls η) (b : s.free) :
    _root_.YangMills.Construction.StepMarks.frameDeviation R.params R.anchorRadius R.depth R.frameReach s.coarse (s.field η) b.1 = toImaginary (η b) := by
  have hw : ‖((s.frame b.1 + toImaginary (η b) : imaginaryQuaternions) : ℍ[ℝ])‖ < Real.pi := by
    have h1 : ‖((s.frame b.1 + toImaginary (η b) : imaginaryQuaternions) : ℍ[ℝ])‖ ≤
        ‖((s.frame b.1 : imaginaryQuaternions) : ℍ[ℝ])‖ +
          ‖((toImaginary (η b) : imaginaryQuaternions) : ℍ[ℝ])‖ := norm_add_le _ _
    have h2 : ‖((s.frame b.1 : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ R.anchorRadius := norm_frameCoord_le _ _ hρA _ _ _ _
    have h3 : ‖((toImaginary (η b) : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ R.ballRadius := hη b
    have := Real.pi_gt_three
    linarith
  unfold _root_.YangMills.Construction.StepMarks.frameDeviation
  rw [chartCoord_field_of_mem_free hc hL hn η b hw]
  show s.frame b.1 + toImaginary (η b) - s.frame b.1 = _
  abel
abbrev _root_.YangMills.SharedProofs.p26285 := @frameDeviation_of_free
private theorem exists_nearIndex_of_bond {L : ℕ} [NeZero L] (hodd : Odd L) (o : TorusSite n) (b : TorusBond (n * L))
    (r : ℕ) (hr : 2 * r < n) (hd : supDist (parentBlock L b.1) o ≤ r) (t m : ℕ) (hm : 0 < m) :
    ∃ q : NearBondIndex, nearBond L o q = b ∧ q.2.1 ∈ centredCube L ∧ OffsetInBox r q.1 ∧
      reflectedBondPosition L t m o b = (torusSiteInFrame (reflectedTorusFrame L t m n) (reflectedTorusFrame L t m n).depth
        (nearBond L (0 : TorusSite (4 * m)) q).1, q.2.2) := by
  have : NeZero (n * L) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne L)⟩
  have : NeZero (4 * m) := ⟨by omega⟩
  set d : Fin 4 → ℤ := fun i => (b.1 i - (siteOfInt (n := n * L) fun l => (L : ℤ) * ((o l).cast : ℤ)) i).valMinAbs with hdd
  obtain ⟨kk, oo, ho, hdec⟩ := exists_block_offset hodd d
  have hfine : fineSite L o kk oo = b.1 := by
    funext i
    have e1 : ((d i : ℤ) : ZMod (n * L)) = b.1 i - (siteOfInt (n := n * L) fun l => (L : ℤ) * ((o l).cast : ℤ)) i :=
      ZMod.coe_valMinAbs _
    have e2 : (L : ℤ) * (((o i).cast : ℤ) + kk i) + oo i = (L : ℤ) * ((o i).cast : ℤ) + d i := by
      rw [hdec i]
      ring
    simp only [fineSite, siteOfInt]
    rw [e2, Int.cast_add, e1]
    simp [siteOfInt]
  refine ⟨(kk, oo, b.2), Prod.ext hfine rfl, ho, ?_, ?_⟩
  · intro i
    have hblock : parentBlock L b.1 = o + siteOfInt kk := by
      rw [← hfine]
      exact parentBlock_fineSite hodd o kk oo ho
    have hdist := (supDist_le_iff _ _ _).mp hd i
    rw [hblock] at hdist
    have e3 : (o + siteOfInt kk : TorusSite n) i - o i = ((kk i : ℤ) : ZMod n) := by
      simp [siteOfInt]
    rw [e3] at hdist
    set c : ℤ := (((kk i : ℤ) : ZMod n)).valMinAbs with hc
    have hmod : ((kk i : ℤ) : ZMod n) = ((c : ℤ) : ZMod n) := (ZMod.coe_valMinAbs _).symm
    obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hmod
    have hdn : (d i).natAbs ≤ (n * L) / 2 := ZMod.natAbs_valMinAbs_le _
    have hoo := (TopLevelSites.mem_centredCube_iff oo).mp ho i
    have hhalf : 2 * halfWidth L ≤ (L : ℤ) - 1 := by
      unfold halfWidth
      omega
    have hN : (((n * L : ℕ)) : ℤ) = (n : ℤ) * L := by push_cast; ring
    have h1 : 2 * d i ≤ (n : ℤ) * L ∧ -(2 * d i) ≤ (n : ℤ) * L := by
      rw [← hN]
      omega
    have hdi := hdec i
    have hK1 : 2 * kk i ≤ n := by
      by_contra hc'
      have h5 : (n : ℤ) + 1 ≤ 2 * kk i := by omega
      nlinarith [hoo.1, hoo.2, h1.1]
    have hK2 : -(2 * kk i) ≤ n := by
      by_contra hc'
      have h5 : (n : ℤ) + 1 ≤ -(2 * kk i) := by omega
      nlinarith [hoo.1, hoo.2, h1.2]
    have hcr : |c| ≤ (r : ℤ) := by
      rw [Int.abs_eq_natAbs]
      exact_mod_cast hdist
    have hcr' := abs_le.mp hcr
    have hk0 : k = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hneg | hpos
      · have : k ≤ -1 := by omega
        nlinarith
      · have : 1 ≤ k := by omega
        nlinarith
    rw [hk0, mul_zero] at hk
    have : kk i = c := by omega
    show |kk i| ≤ (r : ℤ)
    rw [this]
    exact hcr
  · unfold reflectedBondPosition
    refine Prod.ext ?_ rfl
    funext i
    have hp : 4 * m * L = (reflectedTorusFrame L t m n).period (reflectedTorusFrame L t m n).depth i :=
      (period_depth_of_extent (F := reflectedTorusFrame L t m n) (n := 4 * m) (fun _ => rfl) i).symm
    have e : (fineSite L (0 : TorusSite (4 * m)) kk oo) i = ((d i : ℤ) : ZMod (4 * m * L)) := by
      simp only [fineSite, siteOfInt]
      rw [hdec i]
      simp
    show ((d i : ℤ) : ZMod ((reflectedTorusFrame L t m n).period (reflectedTorusFrame L t m n).depth i)) =
      ((((fineSite L (0 : TorusSite (4 * m)) kk oo) i).cast : ℤ) :
        ZMod ((reflectedTorusFrame L t m n).period (reflectedTorusFrame L t m n).depth i))
    rw [e]
    have : NeZero (4 * m * L) := ⟨mul_ne_zero (by omega) (NeZero.ne L)⟩
    exact (castInt_intCast hp (d i)).symm
private abbrev topStepFrame (R : StepSetup) (n : ℕ) : BlockFrame := torusFrame R.params.side R.depth n
private theorem frameDeviation_coldField (hL : Odd R.params.side) (hn : 2 ≤ n) (hρA : 0 ≤ R.anchorRadius)
    (hρA' : R.anchorRadius ≤ 1) (hρ0 : 0 ≤ R.ballRadius) (hρ : R.ballRadius ≤ 1)
    (V : TorusField n) (k : StepVariable (finiteCells (torusFrame R.params.side R.depth n)))
    (hk : ∀ b, ‖k b‖ < R.ballRadius) (b : TorusBond (n * R.params.side)) (hb : b ∈ chartBonds R.params.side n) :
    _root_.YangMills.Construction.StepMarks.frameDeviation R.params R.anchorRadius R.depth R.frameReach V (coldFieldAboveFrames R V k) b =
      stepCoordinates k (torusSiteInFrame (torusFrame R.params.side R.depth n)
        (torusFrame R.params.side R.depth n).depth b.1) b.2 := by
  classical
  have : NeZero (n * R.params.side) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne _)⟩
  have : NeZero (n * (topStepFrame R n).blockSide) := inferInstanceAs (NeZero (n * R.params.side))
  have : NeZero (n * (stepBlockFrame R.params.side n).blockSide) := inferInstanceAs (NeZero (n * R.params.side))
  have hside : ∀ i, (topStepFrame R n).extent i = n := fun _ => rfl
  have hLF : Odd (topStepFrame R n).blockSide := hL
  set w : (topStepFrame R n).Site (topStepFrame R n).depth → Fin 4 → imaginaryQuaternions :=
    interpolatedCoords 1 R.params.coupling R.anchorRadius R.frameReach
      (readAtLevel (topStepFrame R n) (topStepFrame R n).top V) k with hw
  have hfield : ∀ (x : TorusSite (n * R.params.side)) (i : Fin 4), coldFieldAboveFrames R V k x i =
      torusChart R.params.side (fun b => w (torusSiteInFrame (topStepFrame R n) (topStepFrame R n).depth b.1) b.2)
        V x i := fun x i =>
    chartedField_readAtLevel (F := topStepFrame R n) hside hLF hn w V x i
  have htree : ∀ z i, IsAxialTreeBond (F := stepBlockFrame R.params.side n)
      (torusSiteInFrame (stepBlockFrame R.params.side n) 0 z, i) → coldFieldAboveFrames R V k z i = 1 := by
    intro z i ht
    rw [hfield]
    have ht' : IsBlockTreeBond R.params.side z i :=
      (isAxialTreeBond_torusSiteInFrame_iff (F := stepBlockFrame R.params.side n)
        (stepBlockFrame_extent _ _) hL hn z i).mp ht
    have hc' : ¬ IsBlockEndBond R.params.side z i := fun h =>
      ht.1 ((isCrossingBond_torusSiteInFrame_iff (F := stepBlockFrame R.params.side n)
        (stepBlockFrame_extent _ _) hL hn z i).mpr h)
    unfold torusChart
    rw [if_neg hc', if_pos ht']
  have htr : ∀ x, blockGauge R.params.side (coldFieldAboveFrames R V k) x = 1 := fun x => by
    rw [blockGauge_congr hL hn (coldFieldAboveFrames R V k) (trivialField _) x
      (fun z i _ ht => by rw [htree z i ht]; rfl)]
    exact blockGauge_of_forall_eq_one _ (fun _ _ => rfl) x
  have hnt : ¬ IsAxialTreeBond (F := stepBlockFrame R.params.side n)
      (torusSiteInFrame (stepBlockFrame R.params.side n) 0 b.1, b.2) := by
    unfold chartBonds at hb
    exact (Finset.mem_filter.mp hb).2
  have hnt' : ¬ IsBlockTreeBond R.params.side b.1 b.2 := fun h =>
    hnt ((isAxialTreeBond_torusSiteInFrame_iff (F := stepBlockFrame R.params.side n)
      (stepBlockFrame_extent _ _) hL hn b.1 b.2).mpr h)
  have hframe : w (torusSiteInFrame (topStepFrame R n) (topStepFrame R n).depth b.1) b.2 =
      frameCoord R.params R.anchorRadius R.depth R.frameReach V b +
        stepCoordinates k (torusSiteInFrame (topStepFrame R n) (topStepFrame R n).depth b.1) b.2 := by
    simp only [hw, interpolatedCoords, interpolatedFrame]
    simp
    rfl
  have hsmall : ‖((w (torusSiteInFrame (topStepFrame R n) (topStepFrame R n).depth b.1) b.2 :
      imaginaryQuaternions) : ℍ[ℝ])‖ < Real.pi := by
    have h1 : ‖((stepCoordinates k (torusSiteInFrame (topStepFrame R n) (topStepFrame R n).depth b.1) b.2 :
        imaginaryQuaternions) : ℍ[ℝ])‖ ≤ R.ballRadius := by
      unfold stepCoordinates
      split_ifs with hm
      · have := (hk ⟨_, hm⟩).le
        rw [← SettingShifts.coordNorm_eq_norm] at this
        exact this
      · simpa using hρ0
    have h2 : ‖((frameCoord R.params R.anchorRadius R.depth R.frameReach V b : imaginaryQuaternions) : ℍ[ℝ])‖ ≤
        R.anchorRadius := norm_frameCoord_le _ _ hρA _ _ _ _
    have h3 : ‖((w (torusSiteInFrame (topStepFrame R n) (topStepFrame R n).depth b.1) b.2 :
        imaginaryQuaternions) : ℍ[ℝ])‖ ≤
        ‖((frameCoord R.params R.anchorRadius R.depth R.frameReach V b : imaginaryQuaternions) : ℍ[ℝ])‖ +
          ‖((stepCoordinates k (torusSiteInFrame (topStepFrame R n) (topStepFrame R n).depth b.1) b.2 :
            imaginaryQuaternions) : ℍ[ℝ])‖ := by
      rw [hframe]
      exact norm_add_le _ _
    have := Real.pi_gt_three
    linarith
  have hchart : chartCoord R.params V (coldFieldAboveFrames R V k) b =
      w (torusSiteInFrame (topStepFrame R n) (topStepFrame R n).depth b.1) b.2 := by
    rw [chartCoord_eq_minimalLog R.params V (coldFieldAboveFrames R V k) b
      (expUnit (w (torusSiteInFrame (topStepFrame R n) (topStepFrame R n).depth b.1) b.2)) ?_]
    · exact minimalLog_expUnit hsmall
    · rw [htr, htr, hfield]
      unfold torusChart
      by_cases hc : IsCrossingBond (F := stepBlockFrame R.params.side n)
          (torusSiteInFrame (stepBlockFrame R.params.side n) 0 b.1, b.2)
      · have hc' : IsBlockEndBond R.params.side b.1 b.2 :=
          (isCrossingBond_torusSiteInFrame_iff (F := stepBlockFrame R.params.side n)
            (stepBlockFrame_extent _ _) hL hn b.1 b.2).mp hc
        rw [if_pos hc, if_pos hc']
        simp
      · have hc' : ¬ IsBlockEndBond R.params.side b.1 b.2 := fun h =>
          hc ((isCrossingBond_torusSiteInFrame_iff (F := stepBlockFrame R.params.side n)
            (stepBlockFrame_extent _ _) hL hn b.1 b.2).mpr h)
        rw [if_neg hc, if_neg hc', if_neg hnt']
        simp
  unfold _root_.YangMills.Construction.StepMarks.frameDeviation
  rw [hchart, hframe]
  abel
private theorem familyLawExponent_eq_stepExponent {F : BlockFrame} (a ρA x : ℝ) (m : ℕ) (φ : LocalFamily)
    (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)) :
    familyLawExponent 1 a ρA x m φ V η = stepExponent false a ρA x m φ 1 V η := by
  have hfr : ∀ (b : F.Site F.depth × Fin 4), interpolatedFrame 1 a ρA m b V =
      ColdStepAtMirrorFrames.stepFrame false a ρA m b V := fun b => by
    simp [interpolatedFrame]
  have ha : ∀ η', interpolatedCoords 1 a ρA m V η' = coordsAboveFrame false a ρA m V η' := fun η' => by
    funext z i
    simp only [interpolatedCoords, coordsAboveFrame, hfr]
  have hf : ∀ η', interpolatedField 1 a ρA m V η' = fieldAboveFrame false a ρA m V η' := fun η' => by
    simp only [interpolatedField, fieldAboveFrame, ha]
  simp only [familyLawExponent, interpolatedExponent, stepExponent, interpolatedExpansion, centredExpansion, ha, hf, one_mul]
end SettingNearColdMirror
theorem settingNearColdMirror_holds (h₁ : ClusterExpansionOfAStep.LocalMeansClose) (h₂ : coldSettingMeanEqStepMean)
    (h₃ : ColdChartSettingIsAdmissible) : settingNearColdMirrorStatement := by
  classical
  open SettingNearColdMirror in
  obtain ⟨rt₀, hrt₀, h1⟩ := h₁
  refine ⟨rt₀, hrt₀, fun T hT hC hrt => ?_⟩
  obtain ⟨ya, h1a⟩ := h1 T hT hrt
  obtain ⟨yb, h2a⟩ := h₂ T hT hC
  obtain ⟨yc, h3a⟩ := h₃ T hT
  refine ⟨max ya (max yb yc), fun y hy R hOn n m m' _ _ s o hn hm hs hcold hag hr Z F B hZ hF hB => ?_⟩
  have hya : ya ≤ y := le_trans (le_max_left _ _) hy
  have hyb : yb ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hy
  have hyc : yc ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hy
  have eL : R.params.side = T.side := congrArg (·.side) hOn.params_eq
  have eσ : R.params.threshold = T.threshold := by rw [hOn.params_eq]; rfl
  have hodd : Odd R.params.side := by rw [eL]; exact hT.L_odd
  have hn₀ : 4096 ≤ T.n₀ := hT.n₀_ge
  have hn2 : 2 ≤ n := by omega
  have hm2 : 2 ≤ 4 * m := by omega
  have hmpos : 0 < m := by omega
  obtain ⟨_, _, _, hρA0, hρA1, _⟩ := hT.chain
  have hρA0' : 0 ≤ R.anchorRadius := by rw [hOn.anchorRadius_eq]; exact hρA0.le
  have hρA1' : R.anchorRadius ≤ 1 := by rw [hOn.anchorRadius_eq]; exact hρA1
  have hρ0 : 0 ≤ R.ballRadius := by
    unfold StepSetup.ballRadius
    rw [eσ]
    have := hT.σ_pos
    positivity
  have hρ1 : R.ballRadius ≤ 1 := by
    unfold StepSetup.ballRadius
    rw [eσ]
    have := hT.σ_one
    linarith
  set V' := mirrorField m o s.coarse with hV'
  set s' := coldChartSetting R V' with hs'def
  have hs' : s'.IsAdmissible := h3a y hyc R hOn (4 * m) hm V' hcold
  have hside : 2 * (m' / 4) < n := by
    have := hag.lt_extent
    omega
  have hidx : ∀ b : ↥Z, ∃ q : NearBondIndex, nearBond R.params.side o q = b.1 ∧ q.2.1 ∈ centredCube R.params.side ∧
      OffsetInBox (m' / 4) q.1 ∧
      reflectedBondPosition R.params.side R.depth m o b.1 =
        (torusSiteInFrame (reflectedTorusFrame R.params.side R.depth m n)
          (reflectedTorusFrame R.params.side R.depth m n).depth
          (nearBond R.params.side (0 : TorusSite (4 * m)) q).1, q.2.2) :=
    fun b => exists_nearIndex_of_bond hodd o b.1 (m' / 4) hside (hZ b.1 b.2).2 R.depth m hmpos
  choose idx hidx1 hidx2 hidx3 hidx4 using hidx
  have hnear : ∀ b, IsNearIndex R.params.side m' (idx b) := fun b =>
    ⟨fun i => le_trans (hidx3 b i) (by exact_mod_cast Nat.div_le_self _ _), hidx2 b⟩
  have hchart' : ∀ b : ↥Z, nearBond R.params.side (0 : TorusSite (4 * m)) (idx b) ∈ s'.free := fun b => by
    have h := (hZ b.1 b.2).1
    rw [← hidx1 b] at h
    exact (fineSite_mem_chartBonds_iff (R := R) hodd hn2 hm2 o 0 _ _ (hidx2 b) _).mp h
  have hfree : ∀ b : ↥Z, b.1 ∈ s.free := fun b => by
    have := (hag.free_iff _ (hnear b)).mpr (hchart' b)
    rwa [hidx1 b] at this
  have hfreeN : ∀ b : ↥Z, nearBond R.params.side o (idx b) ∈ s.free := fun b => by
    rw [hidx1 b]
    exact hfree b
  set F' : (NearBondIndex → EuclideanSpace ℝ (Fin 3)) → ℝ := fun z => F fun p => z (idx p.1) p.2 with hF'
  have hF'm : Measurable F' := hF.comp (measurable_pi_lambda _ fun p =>
    ((EuclideanSpace.proj (𝕜 := ℝ) p.2 : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).continuous.measurable).comp
      (measurable_pi_apply _))
  have hread : DependsWithin T.side (m' / 4) F' := by
    intro z z' hzz
    show F _ = F _
    congr 1
    funext p
    rw [hzz (idx p.1) ⟨hidx3 p.1, by rw [← eL]; exact hidx2 p.1⟩]
  have hosc : ∀ z z', ClusterExpansionOfAStep.CoordsInBalls R z → ClusterExpansionOfAStep.CoordsInBalls R z' → |F' z - F' z'| ≤ 2 * B := by
    intro z z' _ _
    have h1 := hB (fun p => z (idx p.1) p.2)
    have h2 := hB (fun p => z' (idx p.1) p.2)
    have := abs_sub (F' z) (F' z')
    show |F _ - F _| ≤ _
    have h3 := abs_sub_le (F fun p => z (idx p.1) p.2) 0 (F fun p => z' (idx p.1) p.2)
    simp only [sub_zero, zero_sub, abs_neg] at h3
    linarith
  have hdens : ∀ {k : ℕ} [NeZero k] (u : ChartSetting R k), u.lawDensity (u.partPotential 1) = chartDensity u := by
    intro k _ u
    funext η
    simp [ChartSetting.lawDensity, chartDensity, ChartSetting.partPotential, ChartSetting.potential]
  have hidxS : ∀ (η : FreeCoords s.free) (b : ↥Z), s.coordsByIndex o η (idx b) = η ⟨b.1, hfree b⟩ := by
    intro η b
    unfold ChartSetting.coordsByIndex
    rw [dif_pos (hfreeN b)]
    congr 1
    exact Subtype.ext (hidx1 b)
  have hidxC : ∀ (η : FreeCoords s'.free) (b : ↥Z), s'.coordsByIndex 0 η (idx b) = η ⟨_, hchart' b⟩ := by
    intro η b
    unfold ChartSetting.coordsByIndex
    rw [dif_pos (hchart' b)]
  have e1 : weightedMean (chartDensity s) (fun η => F (imaginaryComponentsOn Z
      (_root_.YangMills.Construction.StepMarks.frameDeviation R.params R.anchorRadius R.depth R.frameReach s.coarse (s.field η)))) =
      weightedMean (s.lawDensity (s.partPotential 1)) (fun η => F' (s.coordsByIndex o η)) := by
    rw [hdens]
    refine weightedMean_congr fun η hη => ?_
    have hb := inBalls_of_chartDensity_ne_zero s hη
    show F _ = F _
    congr 1
    funext p
    have h := frameDeviation_of_free s hs.subset_chart hodd hn2 hρA0' hρA1' hρ1 hb ⟨p.1.1, hfree p.1⟩
    rw [hidxS]
    show imaginaryComponent p.2
      (_root_.YangMills.Construction.StepMarks.frameDeviation R.params R.anchorRadius R.depth R.frameReach s.coarse (s.field η) p.1.1) = _
    rw [h, imaginaryComponent_toImaginary]
  set G : TorusField (4 * m * R.params.side) → ℝ := fun W => F fun p =>
    imaginaryComponent p.2 (_root_.YangMills.Construction.StepMarks.frameDeviation R.params R.anchorRadius R.depth R.frameReach V' W
      (nearBond R.params.side (0 : TorusSite (4 * m)) (idx p.1))) with hG
  have e3 : weightedMean (s'.lawDensity (s'.partPotential 1)) (fun η => F' (s'.coordsByIndex 0 η)) =
      weightedMean (chartDensity s') (fun η => G (s'.field η)) := by
    rw [hdens]
    refine weightedMean_congr fun η hη => ?_
    have hb := inBalls_of_chartDensity_ne_zero s' hη
    show F _ = F _
    congr 1
    funext p
    have h := frameDeviation_of_free s' hs'.subset_chart hodd hm2 hρA0' hρA1' hρ1 hb ⟨_, hchart' p.1⟩
    rw [hidxC]
    have h' : _root_.YangMills.Construction.StepMarks.frameDeviation R.params R.anchorRadius R.depth R.frameReach V' (s'.field η)
        (nearBond R.params.side (0 : TorusSite (4 * m)) (idx p.1)) = toImaginary (η ⟨_, hchart' p.1⟩) := h
    rw [h', imaginaryComponent_toImaginary]
  have hval : ∀ (k : StepVariable (finiteCells (torusFrame R.params.side R.depth (4 * m)))),
      (∀ b, ‖k b‖ < R.ballRadius) →
      G (coldFieldAboveFrames R V' k) =
        F (imaginaryComponentsOn Z (reflectedCoordinateAt R.params.side R.depth m o k)) := by
    intro k hk
    show F _ = F _
    congr 1
    funext p
    have h := frameDeviation_coldField hodd hm2 hρA0' hρA1' hρ0 hρ1 V' k hk _ (hchart' p.1)
    rw [h]
    show _ = imaginaryComponent p.2 (stepCoordinates k
      (reflectedBondPosition R.params.side R.depth m o p.1.1).1 (reflectedBondPosition R.params.side R.depth m o p.1.1).2)
    rw [hidx4 p.1]
    rfl
  have e4 := h2a y hyb R hOn (4 * m) hm V' hcold G
  have htop : reflectedTopField R.params.side R.depth m o s.coarse =
      readAtLevel (torusFrame R.params.side R.depth (4 * m)) (torusFrame R.params.side R.depth (4 * m)).top V' :=
    reflectedField_readAtLevel (F := torusFrame R.params.side R.depth n) (fun _ => rfl) hmpos o s.coarse
  have e5 : coldStepMean R V' (fun k => G (coldFieldAboveFrames R V' k)) =
      reflectedStepMean R m o s.coarse
        (fun k => F (imaginaryComponentsOn Z (reflectedCoordinateAt R.params.side R.depth m o k))) := by
    unfold coldStepMean reflectedStepMean cutoffMean
    have hexp : ∀ η : StepVariable (finiteCells (torusFrame R.params.side R.depth (4 * m))),
        familyLawExponent 1 R.params.coupling R.anchorRadius R.coupling R.frameReach (localFamilyOfDensity R.density)
          (readAtLevel (torusFrame R.params.side R.depth (4 * m)) (torusFrame R.params.side R.depth (4 * m)).top V') η =
        stepExponent false R.params.coupling R.anchorRadius R.coupling R.frameReach (localFamilyOfDensity R.density) 1
          (reflectedTopField R.params.side R.depth m o s.coarse) η := by
      intro η
      rw [htop, familyLawExponent_eq_stepExponent]
      rfl
    simp only [hexp]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    show G (coldFieldAboveFrames R V' η) * _ =
      F (imaginaryComponentsOn Z (reflectedCoordinateAt R.params.side R.depth m o η)) * _
    by_cases hw : cutoffWeight R.ballRadius R.barrierFn η = 0
    · simp [hw]
      exact Or.inr hw
    · have hk : ∀ b, ‖η b‖ < R.ballRadius := by
        intro b
        by_contra hc
        apply hw
        unfold cutoffWeight
        refine Finset.prod_eq_zero (Finset.mem_univ b) ?_
        unfold cutoffFactor
        exact if_neg hc
      rw [hval η hk]
      rfl
  have hmain := h1a y hya R hOn n (4 * m) hn hm s s' o 0 m' hs hs' hag (by rw [eL] at *; exact hr) _ _
    (ClusterExpansionOfAStep.AlikePotentials.part_potential 1 zero_le_one le_rfl) F' (2 * B) hF'm hread hosc
  rw [e1, ← e5, ← e4, ← e3]
  exact hmain
end ResponseInTheExpansion
end YangMills.Construction
end
