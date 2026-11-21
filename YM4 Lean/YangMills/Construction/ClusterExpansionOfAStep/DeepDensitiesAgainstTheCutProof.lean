import YangMills.Construction.ClusterExpansionOfAStep.ContoursFromBases
import YangMills.Construction.ClusterExpansionOfAStep.CutOfASplit
import YangMills.Construction.ClusterExpansionOfAStep.DensitiesOfASplit
import YangMills.Construction.ClusterExpansionOfAStep.NearAClassOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
import YangMills.Construction.ClusterExpansionOfAStep.FloorsOfTheParameters
import YangMills.Construction.ClusterExpansionOfAStep.OscillationOfTheStateDensities
import YangMills.Construction.ClusterExpansionOfAStep.PsiOfTwoSettings
import YangMills.Construction.ClusterExpansionOfAStep.ShiftsOfTwoSettings
import YangMills.Construction.ClusterExpansionOfAStep.SplitOfASettingIsRegular
import YangMills.Construction.ClusterExpansionOfAStep.StateDensitiesOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.StateDensitiesOfTwoSettings
import YangMills.Construction.ClusterExpansionOfAStep.TwoSettingsOnABox
set_option autoImplicit false

noncomputable section
namespace YangMills.Construction
open BlockAverages LumpContours ColdStepAtMirrorFrames TorusFields TorusLumps RenormalizationStepParameters StepSettings StepCosts
def ClusterExpansionOfAStep.DeepActivityIgnoresCutoff : Prop :=
  ∃ rt₀ : ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧ ∀ T : ParameterAssignment, T.Admissible →
    T.rt ≤ rt₀ T.toChainParameters →
    ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y → ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n →
      ∀ s : ChartSetting R n, s.IsAdmissible → ∀ (N : Finset (TorusSite n)) (Y : TorusSite n), Y ∈ N →
        (∀ Y' : TorusSite n, Y' ∉ N → (R.range : ℝ) / (4 * T.side) + 3 ≤ supDist Y Y') →
        |s.blockActivity T.lam Y - (s.restrictedSplit T.lam (s.freeNear N)).activity T.lam Y| ≤ 1
end YangMills.Construction
end

set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Set
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages LumpContours ColdStepAtMirrorFrames Restriction StepSettings TorusFields TorusLumps
  BlockOffsets Interpolation RenormalizationStepParameters StepFloors StepCosts
namespace DeepCutoff
section Extension
variable {R : StepSetup} {n n' : ℕ} [NeZero n] [NeZero n']
theorem isNearIndex_mono {L k m : ℕ} {q : NearBondIndex} (hq : IsNearIndex L k q) (h : k ≤ m) :
    IsNearIndex L m q :=
  ⟨fun i => (hq.1 i).trans (by exact_mod_cast h), hq.2⟩
theorem nearBond_inj_of_isNearIndex (hodd : Odd R.params.side) {Y : TorusSite n} {k : ℕ} (hk : 2 * k + 2 < n)
    {q q' : NearBondIndex} (hq : IsNearIndex R.params.side k q) (hq' : IsNearIndex R.params.side k q')
    (e : nearBond R.params.side Y q = nearBond R.params.side Y q') : q = q' := by
  obtain ⟨h, o, i⟩ := q
  obtain ⟨h', o', i'⟩ := q'
  have e1 : fineSite R.params.side Y h o = fineSite R.params.side Y h' o' := congrArg Prod.fst e
  have e2 : i = i' := congrArg Prod.snd e
  obtain ⟨H, hH⟩ := id hodd
  have hL : ((R.params.side : ℤ) - 1) / 2 = (H : ℤ) := by rw [hH]; push_cast; omega
  have hLH : (R.params.side : ℤ) = 2 * H + 1 := by rw [hH]; push_cast; ring
  have key : ∀ l, h l = h' l ∧ o l = o' l := by
    intro l
    have h1 := congrFun e1 l
    simp only [fineSite, siteOfInt] at h1
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h1
    have hb := (_root_.YangMills.Construction.BlockOffsets.mem_centredCube_iff o).mp hq.2 l
    have hb' := (_root_.YangMills.Construction.BlockOffsets.mem_centredCube_iff o').mp hq'.2 l
    rw [hL] at hb hb'
    have ha : -(k : ℤ) ≤ h l ∧ h l ≤ k := abs_le.mp (hq.1 l)
    have ha' : -(k : ℤ) ≤ h' l ∧ h' l ≤ k := abs_le.mp (hq'.1 l)
    set d := h' l - h l with hd
    set w := o' l - o l with hw
    have h2 : ((n * R.params.side : ℕ) : ℤ) ∣ (R.params.side : ℤ) * d + w := by
      have : (R.params.side : ℤ) * (((Y l).cast : ℤ) + h' l) + o' l -
          ((R.params.side : ℤ) * (((Y l).cast : ℤ) + h l) + o l) = (R.params.side : ℤ) * d + w := by
        rw [hd, hw]
        ring
      rwa [this] at h1
    have hdk : |d| ≤ 2 * (k : ℤ) := by
      rw [abs_le]
      constructor <;> omega
    have hwL : |w| ≤ 2 * (H : ℤ) := by
      rw [abs_le]
      constructor <;> omega
    have hLpos : (0 : ℤ) < R.params.side := by omega
    have hnk : (2 * (k : ℤ) + 3) ≤ n := by exact_mod_cast hk
    have h3 : |(R.params.side : ℤ) * d + w| < ((n * R.params.side : ℕ) : ℤ) := by
      calc |(R.params.side : ℤ) * d + w| ≤ |(R.params.side : ℤ) * d| + |w| := abs_add_le _ _
        _ = (R.params.side : ℤ) * |d| + |w| := by rw [abs_mul, abs_of_pos hLpos]
        _ ≤ (R.params.side : ℤ) * (2 * k) + 2 * H := by
            have := mul_le_mul_of_nonneg_left hdk hLpos.le
            linarith
        _ < (R.params.side : ℤ) * (2 * k + 3) := by nlinarith
        _ ≤ (R.params.side : ℤ) * n := mul_le_mul_of_nonneg_left hnk hLpos.le
        _ = ((n * R.params.side : ℕ) : ℤ) := by push_cast; ring
    have h4 := Int.eq_zero_of_abs_lt_dvd h2 h3
    have hd0 : d = 0 := by
      by_contra hne
      have h5 : 1 ≤ |d| := Int.one_le_abs hne
      have h6 : (R.params.side : ℤ) * |d| = |w| := by
        have e3 : (R.params.side : ℤ) * d = -w := by linarith
        have e4 : |(R.params.side : ℤ) * d| = |w| := by rw [e3, abs_neg]
        rwa [abs_mul, abs_of_pos hLpos] at e4
      nlinarith
    have hw0 : w = 0 := by
      rw [hd0] at h4
      simpa using h4
    constructor <;> omega
  have hh : h = h' := funext fun l => (key l).1
  have ho : o = o' := funext fun l => (key l).2
  rw [hh, ho, e2]
open Classical in
def extendByIndex (s : ChartSetting R n) (Y : TorusSite n) (k : ℕ)
    (z : NearBondIndex → EuclideanSpace ℝ (Fin 3)) : FreeCoords s.free :=
  fun b => if h : ∃ q, IsNearIndex R.params.side k q ∧ nearBond R.params.side Y q = b.1 then z h.choose else 0
theorem extendByIndex_apply (hodd : Odd R.params.side) (s : ChartSetting R n) {Y : TorusSite n} {k : ℕ}
    (hk : 2 * k + 2 < n) (z : NearBondIndex → EuclideanSpace ℝ (Fin 3)) {q : NearBondIndex}
    (hq : IsNearIndex R.params.side k q) (h : nearBond R.params.side Y q ∈ s.free) :
    extendByIndex s Y k z ⟨_, h⟩ = z q := by
  classical
  have hex : ∃ q', IsNearIndex R.params.side k q' ∧ nearBond R.params.side Y q' = (⟨_, h⟩ : s.free).1 :=
    ⟨q, hq, rfl⟩
  unfold extendByIndex
  rw [dif_pos hex]
  rw [nearBond_inj_of_isNearIndex hodd hk hex.choose_spec.1 hq hex.choose_spec.2]
theorem coordsAgreeNear_extendByIndex (hodd : Odd R.params.side) {s : ChartSetting R n}
    {s' : ChartSetting R n'} {Y : TorusSite n} {Y' : TorusSite n'} {m k : ℕ}
    (hag : SettingsAgreeNear s s' Y Y' m) (hkm : k ≤ m) (η' : FreeCoords s'.free) :
    CoordsAgreeNear s s' Y Y' k (extendByIndex s Y k (s'.coordsByIndex Y' η')) η' := by
  classical
  have hk : 2 * k + 2 < n := by have := hag.lt_extent; omega
  intro q hq
  by_cases h : nearBond R.params.side Y q ∈ s.free
  · have e : s.coordsByIndex Y (extendByIndex s Y k (s'.coordsByIndex Y' η')) q =
        extendByIndex s Y k (s'.coordsByIndex Y' η') ⟨_, h⟩ := dif_pos h
    rw [e, extendByIndex_apply hodd s hk _ hq h]
  · have h' : nearBond R.params.side Y' q ∉ s'.free :=
      fun hh => h ((hag.free_iff q (isNearIndex_mono hq hkm)).mpr hh)
    have e : s.coordsByIndex Y (extendByIndex s Y k (s'.coordsByIndex Y' η')) q = 0 := dif_neg h
    have e' : s'.coordsByIndex Y' η' q = 0 := dif_neg h'
    rw [e, e']
theorem coordNorm_zero : coordNorm 0 = 0 := by
  rw [coordNorm_eq_norm, norm_zero]
theorem extendByIndex_inBalls (s : ChartSetting R n) (Y : TorusSite n) (k : ℕ)
    {z : NearBondIndex → EuclideanSpace ℝ (Fin 3)} (hρ : 0 ≤ R.ballRadius) (hz : CoordsInBalls R z) :
    s.InBalls (extendByIndex s Y k z) := by
  classical
  intro b
  unfold extendByIndex
  by_cases h : ∃ q, IsNearIndex R.params.side k q ∧ nearBond R.params.side Y q = b.1
  · rw [dif_pos h]
    exact hz _
  · rw [dif_neg h, coordNorm_zero]
    exact hρ
theorem extendByIndex_mem_openBallsIn (s : ChartSetting R n) (Y : TorusSite n) (k : ℕ)
    {z : NearBondIndex → EuclideanSpace ℝ (Fin 3)} (hρ : 0 < R.ballRadius)
    (hz : ∀ q, coordNorm (z q) < R.ballRadius) : extendByIndex s Y k z ∈ openBallsIn R s.free := by
  classical
  intro b
  unfold extendByIndex
  by_cases h : ∃ q, IsNearIndex R.params.side k q ∧ nearBond R.params.side Y q = b.1
  · rw [dif_pos h]
    exact hz _
  · rw [dif_neg h, coordNorm_zero]
    exact hρ
theorem coordsByIndex_inBalls (s : ChartSetting R n) (Y : TorusSite n) {η : FreeCoords s.free}
    (hρ : 0 ≤ R.ballRadius) (hη : s.InBalls η) : CoordsInBalls R (s.coordsByIndex Y η) := by
  classical
  intro q
  unfold ChartSetting.coordsByIndex
  by_cases h : nearBond R.params.side Y q ∈ s.free
  · rw [dif_pos h]
    exact hη _
  · rw [dif_neg h, coordNorm_zero]
    exact hρ
theorem coordNorm_coordsByIndex_lt (s : ChartSetting R n) (Y : TorusSite n) {η : FreeCoords s.free}
    (hρ : 0 < R.ballRadius) (hη : η ∈ openBallsIn R s.free) (q : NearBondIndex) :
    coordNorm (s.coordsByIndex Y η q) < R.ballRadius := by
  classical
  unfold ChartSetting.coordsByIndex
  by_cases h : nearBond R.params.side Y q ∈ s.free
  · rw [dif_pos h]
    exact hη _
  · rw [dif_neg h, coordNorm_zero]
    exact hρ
theorem measurable_coordsByIndex (s : ChartSetting R n) (Y : TorusSite n) :
    Measurable (s.coordsByIndex Y) := by
  classical
  refine measurable_pi_iff.mpr fun q => ?_
  unfold ChartSetting.coordsByIndex
  by_cases h : nearBond R.params.side Y q ∈ s.free
  · simp only [dif_pos h]
    exact measurable_pi_apply _
  · simp only [dif_neg h]
    exact measurable_const
theorem measurable_extendByIndex (s : ChartSetting R n) (Y : TorusSite n) (k : ℕ) :
    Measurable (extendByIndex s Y k) := by
  classical
  refine measurable_pi_iff.mpr fun b => ?_
  unfold extendByIndex
  by_cases h : ∃ q, IsNearIndex R.params.side k q ∧ nearBond R.params.side Y q = b.1
  · simp only [dif_pos h]
    exact measurable_pi_apply _
  · simp only [dif_neg h]
    exact measurable_const
theorem extendByIndex_congr (s : ChartSetting R n) (Y : TorusSite n) {k m : ℕ} (hkm : k ≤ m)
    {z z' : NearBondIndex → EuclideanSpace ℝ (Fin 3)} (h : ∀ q, IsNearIndex R.params.side m q → z q = z' q) :
    extendByIndex s Y k z = extendByIndex s Y k z' := by
  classical
  funext b
  unfold extendByIndex
  by_cases he : ∃ q, IsNearIndex R.params.side k q ∧ nearBond R.params.side Y q = b.1
  · rw [dif_pos he, dif_pos he]
    exact h _ (isNearIndex_mono he.choose_spec.1 hkm)
  · rw [dif_neg he, dif_neg he]
end Extension
section Laws
variable {R : StepSetup} {n : ℕ} [NeZero n] {free : Finset (TorusBond (n * R.params.side))}
theorem weightedMean_const_mul {d d' G : FreeCoords free → ℝ} {c : ℝ} (hc : c ≠ 0) (h : ∀ a, d' a = c * d a) :
    weightedMean d' G = weightedMean d G := by
  unfold weightedMean
  have e1 : ∫ a, G a * d' a = c * ∫ a, G a * d a := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    simp only [h]
    ring
  have e2 : ∫ a, d' a = c * ∫ a, d a := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall h)
  rw [e1, e2, mul_div_mul_left _ _ hc]
theorem partPotential_eq (s : ChartSetting R n) (ν : ℝ) (η : FreeCoords s.free) :
    s.partPotential ν η = R.coupling * s.densitySplit.totalCost η - ν * ∑ Y : TorusSite n, s.blockDensityAt Y η -
      ∑ Y : TorusSite n, s.logJacobianAt Y η := by
  unfold ChartSetting.partPotential
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rfl
theorem weightedMean_interpolatedDensity_eq_lawDensity (s : ChartSetting R n) (hreg : s.densitySplit.IsRegular)
    (lam τ : ℝ) (G : FreeCoords s.free → ℝ) :
    weightedMean (s.interpolatedDensity lam τ) G = weightedMean (s.lawDensity fun η => τ * s.partPotential 0 η +
      (1 - τ) * s.restrictedPotential lam 0 ∅ (s.partPotential 0) η) G := by
  classical
  symm
  refine weightedMean_const_mul (c := Real.exp (-s.partPotential 0 0)) (Real.exp_pos _).ne' fun η => ?_
  unfold ChartSetting.lawDensity ChartSetting.interpolatedDensity
  by_cases h : η ∈ openBallsIn R s.free
  · have hΨ : s.totalInteraction η = _ := totalInteraction_eq hreg (openBallsIn_subset_closedBallsIn h)
    have hcut : s.restrictTo ∅ η = 0 := by
      funext b
      simp [ChartSetting.restrictTo]
    have hq : ∑ Y : TorusSite n, s.blockGaussian lam Y η =
        R.coupling * lam / 2 * ∑ b ∈ Finset.univ \ (∅ : Finset s.free), ‖η b‖ ^ 2 := by
      have e1 : ∀ Y, s.blockGaussian lam Y η = R.coupling * lam / 2 * ∑ b ∈ freeBondsAt s.free Y, ‖η b‖ ^ 2 :=
        fun Y => rfl
      simp only [e1, ← Finset.mul_sum]
      rw [sum_freeBondsAt (fun b => ‖η b‖ ^ 2)]
      simp
    have hU := partPotential_eq s 0 η
    have hU0 := partPotential_eq s 0 0
    unfold ChartSetting.restrictedPotential
    beta_reduce
    rw [hcut, hq, hΨ, mul_left_comm, ← Real.exp_add]
    congr 2
    rw [hU, hU0]
    simp only [show ∀ (Y : TorusSite n) (ξ : FreeCoords s.free),
      s.densitySplit.logJacobian Y ξ = s.logJacobianAt Y ξ from fun _ _ => rfl]
    ring
  · have hz : s.cutoffProduct η = 0 := cutoffProd_eq_zero h
    rw [hz]
    simp
theorem weightedMean_perturbedDensity_eq_lawDensity (s : ChartSetting R n) (hreg : s.densitySplit.IsRegular)
    (ν : ℝ) (G : FreeCoords s.free → ℝ) :
    weightedMean (s.perturbedDensity ν) G = weightedMean (s.lawDensity (s.partPotential ν)) G := by
  symm
  refine weightedMean_const_mul (c := Real.exp (-s.partPotential 0 0)) (Real.exp_pos _).ne' fun η => ?_
  unfold ChartSetting.lawDensity ChartSetting.perturbedDensity
  by_cases h : η ∈ openBallsIn R s.free
  · have hΨ : s.totalInteraction η = _ := totalInteraction_eq hreg (openBallsIn_subset_closedBallsIn h)
    have hU := partPotential_eq s ν η
    have hU0 := partPotential_eq s 0 0
    rw [hΨ, mul_left_comm, ← Real.exp_add]
    congr 2
    rw [hU, hU0]
    show _ = _ + (-(R.coupling * (s.densitySplit.totalCost η - s.densitySplit.totalCost 0) -
      ∑ Y : TorusSite n, s.logJacobianAt Y η + ∑ Y : TorusSite n, s.logJacobianAt Y 0) +
      ν * ∑ Y : TorusSite n, s.blockDensityAt Y η)
    ring
  · have hz : s.cutoffProduct η = 0 := cutoffProd_eq_zero h
    rw [hz]
    simp
theorem abs_weightedMean_interpolatedDensity_sub_le (hcore : LogIntegralExpInterpolationStatement)
    (hρ : 0 < R.ballRadius) (hp : IsCutoff R.ballRadius R.barrierFn) {D : BlockDensitySplit R n free}
    (hreg : D.IsRegular) (lam τ : ℝ) {G H : FreeCoords free → ℝ} {ε : ℝ}
    (hG : AEBounded (volume.restrict (openBallsIn R free)) G) (hH : AEBounded (volume.restrict (openBallsIn R free)) H)
    (hc : ∀ η ∈ openBallsIn R free, |G η - H η| ≤ ε) :
    |weightedMean (D.interpolatedDensity lam τ) G - weightedMean (D.interpolatedDensity lam τ) H| ≤ ε := by
  obtain ⟨hμ, hw, hw0⟩ := cutoffProd_setup (R := R) (free := free) hρ hp
  have hPsi : AEBounded (volume.restrict (openBallsIn R free)) D.totalInteraction :=
    AEBounded.sum _ fun Y _ => aeBounded_interaction hreg Y
  have hQ : AEBounded (volume.restrict (openBallsIn R free)) fun η =>
      ∑ Y : TorusSite n, gaussianPart (R := R) lam Y η :=
    AEBounded.sum _ fun Y _ => aeBounded_gaussianPart lam Y
  have hf := hQ.neg
  have hg := hQ.sub hPsi
  obtain ⟨M, a, b⟩ := hf.exists_common_bound hg
  have hpos := (hcore _ cutoffProd _ _ M hμ hw hw0 hf.1 hg.1 a b).1 τ
  rw [weightedMean_interpolatedDensity_eq, weightedMean_interpolatedDensity_eq]
  unfold tiltedMean
  obtain ⟨KG, hKG⟩ := hG.2
  obtain ⟨KH, hKH⟩ := hH.2
  have hint := integrable_mul_weight_exp hw hf.1 hg.1 a b (G := fun _ => (1 : ℝ)) aestronglyMeasurable_const
    (K := 1) (by simp) τ
  simp only [one_mul] at hint
  exact abs_sub_integral_div_le (fun η => mul_nonneg (cutoffProd_nonneg η) (Real.exp_pos _).le) hint hpos
    (integrable_mul_weight_exp hw hf.1 hg.1 a b hG.1 hKG τ) (integrable_mul_weight_exp hw hf.1 hg.1 a b hH.1 hKH τ)
    (fun η hd => hc η (by
      by_contra hn
      exact hd (by rw [cutoffProd_eq_zero hn, zero_mul])))
theorem abs_weightedMean_perturbedDensity_sub_le (hcore : LogIntegralExpInterpolationStatement)
    (hρ : 0 < R.ballRadius) (hp : IsCutoff R.ballRadius R.barrierFn) {D : BlockDensitySplit R n free}
    (hreg : D.IsRegular) (ν : ℝ) {G H : FreeCoords free → ℝ} {ε : ℝ}
    (hG : AEBounded (volume.restrict (openBallsIn R free)) G) (hH : AEBounded (volume.restrict (openBallsIn R free)) H)
    (hc : ∀ η ∈ openBallsIn R free, |G η - H η| ≤ ε) :
    |weightedMean (D.perturbedDensity ν) G - weightedMean (D.perturbedDensity ν) H| ≤ ε := by
  obtain ⟨hμ, hw, hw0⟩ := cutoffProd_setup (R := R) (free := free) hρ hp
  have hPsi : AEBounded (volume.restrict (openBallsIn R free)) D.totalInteraction :=
    AEBounded.sum _ fun Y _ => aeBounded_interaction hreg Y
  have hΦ : AEBounded (volume.restrict (openBallsIn R free)) fun η => ∑ Y : TorusSite n, D.density Y η :=
    AEBounded.sum _ fun Y _ => aeBounded_density hreg Y
  have hf := hPsi.neg
  obtain ⟨M, a, b⟩ := hf.exists_common_bound hΦ
  have hpos := (hcore _ cutoffProd _ _ M hμ hw hw0 hf.1 hΦ.1 a b).1 ν
  rw [weightedMean_perturbedDensity_eq, weightedMean_perturbedDensity_eq]
  unfold tiltedMean
  obtain ⟨KG, hKG⟩ := hG.2
  obtain ⟨KH, hKH⟩ := hH.2
  have hint := integrable_mul_weight_exp hw hf.1 hΦ.1 a b (G := fun _ => (1 : ℝ)) aestronglyMeasurable_const
    (K := 1) (by simp) ν
  simp only [one_mul] at hint
  exact abs_sub_integral_div_le (fun η => mul_nonneg (cutoffProd_nonneg η) (Real.exp_pos _).le) hint hpos
    (integrable_mul_weight_exp hw hf.1 hΦ.1 a b hG.1 hKG ν) (integrable_mul_weight_exp hw hf.1 hΦ.1 a b hH.1 hKH ν)
    (fun η hd => hc η (by
      by_contra hn
      exact hd (by rw [cutoffProd_eq_zero hn, zero_mul])))
end Laws
section Self
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem toTorusSite_torusSiteInFrame (Y : TorusSite n) :
    (toTorusSite n (torusSiteInFrame (stepBlockFrame R.params.side n) 1 Y :
      (stepBlockFrame R.params.side n).Cell) : TorusSite n) = Y := by
  unfold torusSiteInFrame
  rw [TorusContours.toTorusSite_siteOfCoords (F := stepBlockFrame R.params.side n) (j := 1)
    (fun i => TorusContours.stepBlockFrame_period_one i)]
  funext k
  simp [siteOfInt]
theorem settingsAgreeNear_refl (s : ChartSetting R n) (hs : s.IsAdmissible) (Y : TorusSite n) {m : ℕ}
    (hside : 2 * m + 2 < n) : SettingsAgreeNear s s Y Y m := by apply _root_.YangMills.Construction.SettingShifts.settingsAgreeNear_refl <;> assumption
theorem mem_freeNear_of_isNearIndex (hodd : Odd R.params.side) (s : ChartSetting R n) {N : Finset (TorusSite n)}
    {Y : TorusSite n} {m : ℕ} (hdeep : ∀ Y' : TorusSite n, Y' ∉ N → m < supDist Y Y') {q : NearBondIndex}
    (hq : IsNearIndex R.params.side m q) (h : nearBond R.params.side Y q ∈ s.free) :
    (⟨_, h⟩ : s.free) ∈ s.freeNear N := by
  classical
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  show parentBlock R.params.side (fineSite R.params.side Y q.1 q.2.1) ∈ N
  rw [parentBlock_fineSite hodd Y q.1 q.2.1 hq.2]
  by_contra hn
  have h1 := hdeep _ hn
  have h2 : supDist Y (Y + siteOfInt q.1) ≤ m := supDist_add_siteOfInt_le Y q.1 m fun i => by
    have := hq.1 i
    rw [abs_le] at this
    omega
  omega
theorem mem_freeNear_of_mem_freeBondsAt (s : ChartSetting R n) {N : Finset (TorusSite n)} {Y : TorusSite n}
    (hY : Y ∈ N) : ∀ b ∈ freeBondsAt s.free Y, b ∈ s.freeNear N := by
  classical
  intro b hb
  have h1 : bondBlock (R := R) b.1 = Y := (Finset.mem_filter.mp hb).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1 ▸ hY⟩
theorem coordsAgreeNear_restrictTo (hodd : Odd R.params.side) (s : ChartSetting R n) {N : Finset (TorusSite n)}
    {Y : TorusSite n} {m : ℕ} (hdeep : ∀ Y' : TorusSite n, Y' ∉ N → m < supDist Y Y') {k : ℕ} (hkm : k ≤ m)
    (η : FreeCoords s.free) : CoordsAgreeNear s s Y Y k η (s.restrictTo (s.freeNear N) η) := by
  classical
  intro q hq
  by_cases h : nearBond R.params.side Y q ∈ s.free
  · have e : s.coordsByIndex Y η q = η ⟨_, h⟩ := dif_pos h
    have e' : s.coordsByIndex Y (s.restrictTo (s.freeNear N) η) q = s.restrictTo (s.freeNear N) η ⟨_, h⟩ :=
      dif_pos h
    rw [e, e']
    simp only [ChartSetting.restrictTo]
    rw [if_pos (mem_freeNear_of_isNearIndex hodd s hdeep (isNearIndex_mono hq hkm) h)]
  · have e : s.coordsByIndex Y η q = 0 := dif_neg h
    have e' : s.coordsByIndex Y (s.restrictTo (s.freeNear N) η) q = 0 := dif_neg h
    rw [e, e']
theorem restrictedPotential_univ (s : ChartSetting R n) (lam : ℝ) (u : FreeCoords s.free → ℝ) :
    s.restrictedPotential lam 0 Finset.univ u = u := by
  classical
  funext η
  unfold ChartSetting.restrictedPotential
  rw [restrictTo_univ]
  simp
theorem restrictedSplit_univ (s : ChartSetting R n) (lam : ℝ) :
    s.restrictedSplit lam Finset.univ = s.densitySplit := by
  classical
  have e1 : (fun (Y : TorusSite n) (η : FreeCoords s.free) => s.blockCostAt Y (s.restrictTo Finset.univ η) +
      lam / 2 * ∑ b ∈ freeBondsAt s.free Y \ Finset.univ, ‖η b‖ ^ 2) = s.blockCostAt := by
    funext Y η
    have e0 : freeBondsAt s.free Y \ Finset.univ = ∅ := by
      ext b
      simp
    rw [restrictTo_univ, e0, Finset.sum_empty, mul_zero, add_zero]
  have e2 : (fun (Y : TorusSite n) (η : FreeCoords s.free) => s.logJacobianAt Y (s.restrictTo Finset.univ η)) =
      s.logJacobianAt := by
    funext Y η
    rw [restrictTo_univ]
  have e3 : (fun (Y : TorusSite n) (η : FreeCoords s.free) => s.blockDensityAt Y (s.restrictTo Finset.univ η)) =
      s.blockDensityAt := by
    funext Y η
    rw [restrictTo_univ]
  show (BlockDensitySplit.mk _ _ _ : BlockDensitySplit R n s.free) =
    BlockDensitySplit.mk s.blockCostAt s.logJacobianAt s.blockDensityAt
  rw [e1, e2, e3]
theorem restrictedSplit_totalInteraction_eq (s : ChartSetting R n) (lam : ℝ) (X : Finset s.free)
    (hreg : (s.restrictedSplit lam X).IsRegular) {η : FreeCoords s.free} (h : η ∈ closedBallsIn R s.free) :
    (s.restrictedSplit lam X).totalInteraction η = s.partPotential 0 (s.restrictTo X η) +
      R.coupling * lam / 2 * ∑ b ∈ Finset.univ \ X, ‖η b‖ ^ 2 - s.partPotential 0 0 := by
  rw [totalInteraction_eq hreg h, restrictedSplit_totalCost_eq, restrictedSplit_totalCost_eq, partPotential_eq,
    partPotential_eq, restrictTo_zero]
  have e1 : ∑ Y : TorusSite n, (s.restrictedSplit lam X).logJacobian Y η =
      ∑ Y : TorusSite n, s.logJacobianAt Y (s.restrictTo X η) := rfl
  have e2 : ∑ Y : TorusSite n, (s.restrictedSplit lam X).logJacobian Y 0 = ∑ Y : TorusSite n, s.logJacobianAt Y 0 :=
    Finset.sum_congr rfl fun Y _ => restrictedSplit_logJacobian_zero s lam X Y
  have e3 : ∑ b ∈ Finset.univ \ X, ‖(0 : FreeCoords s.free) b‖ ^ 2 = 0 := by simp
  rw [e1, e2, e3]
  have e4 : s.densitySplit.totalCost (s.restrictTo X η) = s.totalCost (s.restrictTo X η) := rfl
  have e5 : s.densitySplit.totalCost 0 = s.totalCost 0 := rfl
  rw [e4, e5]
  ring
theorem sum_gaussianPart_eq (s : ChartSetting R n) (lam : ℝ) (X : Finset s.free) (η : FreeCoords s.free) :
    ∑ Y : TorusSite n, gaussianPart (R := R) lam Y η = R.coupling * lam / 2 *
      ∑ b ∈ Finset.univ \ (∅ : Finset s.free), ‖s.restrictTo X η b‖ ^ 2 +
      R.coupling * lam / 2 * ∑ b ∈ Finset.univ \ X, ‖η b‖ ^ 2 := by
  classical
  have e1 : ∀ Y : TorusSite n, gaussianPart (R := R) lam Y η =
      R.coupling * lam / 2 * ∑ b ∈ freeBondsAt s.free Y, ‖η b‖ ^ 2 :=
    fun Y => rfl
  simp only [e1, ← Finset.mul_sum]
  rw [sum_freeBondsAt (fun b => ‖η b‖ ^ 2), ← mul_add]
  congr 1
  rw [Finset.sdiff_empty, ← Finset.sum_add_sum_compl X]
  have h1 : ∑ b, ‖s.restrictTo X η b‖ ^ 2 = ∑ b ∈ X, ‖η b‖ ^ 2 := by
    rw [← Finset.sum_add_sum_compl X]
    have h2 : ∑ b ∈ Xᶜ, ‖s.restrictTo X η b‖ ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun b hb => ?_
      have : b ∉ X := Finset.mem_compl.mp hb
      simp [ChartSetting.restrictTo, this]
    have h3 : ∑ b ∈ X, ‖s.restrictTo X η b‖ ^ 2 = ∑ b ∈ X, ‖η b‖ ^ 2 :=
      Finset.sum_congr rfl fun b hb => by simp [ChartSetting.restrictTo, hb]
    rw [h2, h3, add_zero]
  rw [h1, Finset.compl_eq_univ_sdiff]
theorem weightedMean_restricted_interpolatedDensity_eq (s : ChartSetting R n) (lam τ : ℝ) (X : Finset s.free)
    (hreg : (s.restrictedSplit lam X).IsRegular) (G : FreeCoords s.free → ℝ) :
    weightedMean ((s.restrictedSplit lam X).interpolatedDensity lam τ) G =
      weightedMean (s.lawDensity (s.restrictedPotential lam 0 X fun η =>
        τ * s.partPotential 0 η + (1 - τ) * s.restrictedPotential lam 0 ∅ (s.partPotential 0) η)) G := by
  classical
  symm
  refine weightedMean_const_mul (c := Real.exp (-s.partPotential 0 0)) (Real.exp_pos _).ne' fun η => ?_
  show s.cutoffProduct η * Real.exp (-_) =
    Real.exp (-s.partPotential 0 0) * (cutoffProd (R := R) η * Real.exp _)
  by_cases h : η ∈ openBallsIn R s.free
  · have hΨ := restrictedSplit_totalInteraction_eq s lam X hreg (openBallsIn_subset_closedBallsIn h)
    have hQ := sum_gaussianPart_eq s lam X η
    have hcut : s.restrictTo ∅ (s.restrictTo X η) = 0 := by
      funext b
      simp [ChartSetting.restrictTo]
    have e : s.cutoffProduct η = cutoffProd (R := R) η := rfl
    rw [e, mul_left_comm, ← Real.exp_add]
    congr 2
    unfold ChartSetting.restrictedPotential
    beta_reduce
    rw [hcut, hΨ, hQ]
    ring
  · have hz : s.cutoffProduct η = 0 := cutoffProd_eq_zero h
    have hz' : cutoffProd (R := R) η = 0 := cutoffProd_eq_zero h
    rw [hz, hz']
    simp
theorem weightedMean_restricted_perturbedDensity_eq (s : ChartSetting R n) (lam ν : ℝ) (X : Finset s.free)
    (hreg : (s.restrictedSplit lam X).IsRegular) (G : FreeCoords s.free → ℝ) :
    weightedMean ((s.restrictedSplit lam X).perturbedDensity ν) G =
      weightedMean (s.lawDensity (s.restrictedPotential lam 0 X (s.partPotential ν))) G := by
  classical
  symm
  refine weightedMean_const_mul (c := Real.exp (-s.partPotential 0 0)) (Real.exp_pos _).ne' fun η => ?_
  show s.cutoffProduct η * Real.exp (-_) =
    Real.exp (-s.partPotential 0 0) * (cutoffProd (R := R) η * Real.exp _)
  by_cases h : η ∈ openBallsIn R s.free
  · have hΨ := restrictedSplit_totalInteraction_eq s lam X hreg (openBallsIn_subset_closedBallsIn h)
    have e : s.cutoffProduct η = cutoffProd (R := R) η := rfl
    have hU := partPotential_eq s ν (s.restrictTo X η)
    have hU0 := partPotential_eq s 0 (s.restrictTo X η)
    have hΦ : ∑ Y : TorusSite n, (s.restrictedSplit lam X).density Y η =
        ∑ Y : TorusSite n, s.blockDensityAt Y (s.restrictTo X η) := rfl
    rw [e, mul_left_comm, ← Real.exp_add]
    congr 2
    unfold ChartSetting.restrictedPotential
    rw [hΨ, hΦ, hU, hU0]
    ring
  · have hz : s.cutoffProduct η = 0 := cutoffProd_eq_zero h
    have hz' : cutoffProd (R := R) η = 0 := cutoffProd_eq_zero h
    rw [hz, hz']
    simp
end Self
end DeepCutoff
open DeepCutoff in
set_option maxHeartbeats 3200000 in
theorem deepActivityIgnoresCutoff (hcore : LogIntegralExpInterpolationStatement)
    (hpsi : blockInteractionLocalityBound) (hstate : BlockDensitiesClose)
    (hosc : BlockDensityOscillationBound) (hsd : BlockDensitiesMeasurableBounded)
    (h3 : LocalMeansClose) (hreg : DensitySplitRegular)
    (hfl : EventuallyFloorConditions) : DeepActivityIgnoresCutoff := by
  obtain ⟨r₁, p₁, g₁⟩ := h3
  obtain ⟨r₂, p₂, g₂⟩ := hreg
  obtain ⟨r₃, p₃, g₃⟩ := hpsi
  refine ⟨fun c => min (r₁ c) (min (r₂ c) (r₃ c)), fun c => lt_min (p₁ c) (lt_min (p₂ c) (p₃ c)),
    fun T hD hrt => ?_⟩
  have a₁ : T.rt ≤ r₁ T.toChainParameters := hrt.trans (min_le_left _ _)
  have a₂ : T.rt ≤ r₂ T.toChainParameters := hrt.trans ((min_le_right _ _).trans (min_le_left _ _))
  have a₃ : T.rt ≤ r₃ T.toChainParameters := hrt.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨y₁, L3⟩ := g₁ T hD a₁
  obtain ⟨y₂, Rg⟩ := g₂ T hD a₂
  obtain ⟨Cψ, y₃, hCψ, Ps⟩ := g₃ T hD a₃
  have hσ := hD.σ_pos
  have hrtpos := hD.rt_pos
  have hL40 : (2 : ℝ) ^ 40 ≤ T.side := by exact_mod_cast hD.L_ge
  have hL0 : (0 : ℝ) < T.side := by linarith [show (0 : ℝ) < 2 ^ 40 by positivity]
  have hEpos : 1 ≤ T.E := by
    have := hD.B_ge
    unfold ParameterAssignment.E
    linarith
  set Kf : ℝ := 4 * Cψ + 2 * (T.side : ℝ) ^ 4 + (T.side : ℝ) ^ 4 * (4 * T.E + 2) with hKf
  have hKfpos : 0 < Kf := by positivity
  set C₀ : ℝ := Kf + 2 ^ 21 * T.side + 4 * T.n₀ + 2 ^ 17 + 2 with hC₀
  have hC₀pos : 0 < C₀ := by positivity
  set c₀ : ℝ := T.rt / (32 * T.side) with hc₀
  have hc₀pos : 0 < c₀ := by positivity
  obtain ⟨yF, hF⟩ := hfl T hD C₀ c₀ hC₀pos hc₀pos
  refine ⟨max (max T.floorMin (max y₁ y₂)) (max (max y₃ yF) 1),
    fun y hy R hR n _ hn s hs N Y hYN hdeep => ?_⟩
  have hy0 : T.floorMin ≤ y := (le_max_left _ _).trans ((le_max_left _ _).trans hy)
  have hyL : y₁ ≤ y := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hy))
  have hyR : y₂ ≤ y := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hy))
  have hyP : y₃ ≤ y := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hy))
  have hyF : yF ≤ y := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hy))
  have hy1 : (1 : ℝ) ≤ y := (le_max_right _ _).trans ((le_max_right _ _).trans hy)
  have hxy := hR.le_coupling
  have hx1 : 1 ≤ R.coupling := hy1.trans hxy
  have hx : 0 < R.coupling := by linarith
  have hfit : R.params.Admissible := hR.params_eq ▸ hD.fits y hy0
  have hodd : Odd R.params.side := hfit.L_odd
  have hLq : R.params.side = T.side := by rw [hR.params_eq]; rfl
  have hσq : R.params.threshold = T.threshold := by rw [hR.params_eq]; rfl
  have hEq : R.params.E = T.E := by rw [hR.params_eq]; rfl
  have hn₀q : R.params.n₀ = T.n₀ := by rw [hR.params_eq]; rfl
  have hρq : R.ballRadius = T.ballRadius := by
    unfold StepSetup.ballRadius ParameterAssignment.ballRadius
    rw [hσq]
  have hρ : 0 < R.ballRadius := by
    rw [hρq]
    unfold ParameterAssignment.ballRadius
    positivity
  have hp : IsCutoff R.ballRadius R.barrierFn := by
    rw [hρq, hR.barrierFn_eq]
    exact hD.cut
  have hFl := hF R.coupling (hyF.trans hxy)
  have hrC : C₀ ≤ R.range := hFl.range_ge
  have hr2 : (2 : ℝ) ^ 21 * T.side ≤ R.range := by
    have h1 : 0 ≤ 4 * (T.n₀ : ℝ) := by positivity
    linarith
  have hrn : 4 * R.params.n₀ + 2 ^ 16 ≤ R.range := by
    have : ((4 * T.n₀ + 2 ^ 16 : ℕ) : ℝ) ≤ R.range := by
      push_cast
      have h2 : 0 ≤ 2 ^ 21 * (T.side : ℝ) := by positivity
      linarith
    rw [hn₀q]
    exact_mod_cast this
  have hrL : R.params.side + 2 ≤ R.range := by
    have : ((T.side + 2 : ℕ) : ℝ) ≤ R.range := by
      push_cast
      nlinarith
    rw [hLq]
    exact_mod_cast this
  have hE1 : 1 ≤ R.params.E := by rw [hEq]; exact hEpos
  have hnq : R.params.n₀ ≤ n := by rw [hn₀q]; exact hn
  have hregs : s.densitySplit.IsRegular := Rg y hyR R hR n hn s hs
  by_cases hall : ∀ Y' : TorusSite n, Y' ∈ N
  · have hX : s.freeNear N = Finset.univ := by
      classical
      ext b
      simp only [Finset.mem_univ, iff_true]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hall _⟩
    rw [hX, restrictedSplit_univ]
    show |s.densitySplit.activity T.lam Y - s.densitySplit.activity T.lam Y| ≤ 1
    rw [sub_self, abs_zero]
    exact zero_le_one
  push Not at hall
  obtain ⟨Y₀, hY₀⟩ := hall
  have hLR : (R.params.side : ℝ) = T.side := by exact_mod_cast hLq
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ, m = ⌈(R.range : ℝ) / (4 * T.side)⌉₊ := ⟨_, rfl⟩
  have hrm' : (R.range : ℝ) / (4 * T.side) ≤ m := by
    rw [hmdef]
    exact Nat.le_ceil _
  have hrm : (R.range : ℝ) / (4 * R.params.side) ≤ m := by rw [hLR]; exact hrm'
  have hmlt : (m : ℝ) < (R.range : ℝ) / (4 * T.side) + 1 := by
    rw [hmdef]
    exact Nat.ceil_lt_add_one (by positivity)
  have hdeep' : ∀ Y' : TorusSite n, Y' ∉ N → m + 2 ≤ supDist Y Y' := by
    intro Y' hY'
    have h1 := hdeep Y' hY'
    have h2 : ((m + 2 : ℕ) : ℝ) ≤ supDist Y Y' := by
      push_cast
      linarith
    exact_mod_cast h2
  have hdm : ∀ Y' : TorusSite n, Y' ∉ N → m < supDist Y Y' := fun Y' h => by
    have := hdeep' Y' h
    omega
  have hside : 2 * m + 2 < n := by
    have h1 := hdeep' Y₀ hY₀
    have h2 : supDist Y Y₀ ≤ n / 2 := (supDist_le_iff Y Y₀ _).2 fun i => ZMod.natAbs_valMinAbs_le _
    omega
  have hself : SettingsAgreeNear s s Y Y m := settingsAgreeNear_refl s hs Y hside
  set X := s.freeNear N with hXdef
  set D := s.restrictedSplit T.lam X with hDdef
  have hDreg : D.IsRegular := restrictedSplit_isRegular s T.lam X hρ hregs
  have hin : ∀ b ∈ freeBondsAt s.free Y, b ∈ X := mem_freeNear_of_mem_freeBondsAt s hYN
  have hMbig : (2 : ℝ) ^ 19 ≤ m := by
    refine le_trans ?_ hrm'
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hmN : 2 ^ 19 ≤ m := by exact_mod_cast hMbig
  obtain ⟨k, hkdef⟩ : ∃ k, k = m / 8 := ⟨_, rfl⟩
  have hk8 : m ≤ 8 * k + 7 := by omega
  have hk4 : 4 ≤ k := by omega
  have hkm : k ≤ m := by omega
  have hkq : k ≤ m / 4 := by omega
  have hk8R : (m : ℝ) ≤ 8 * k + 7 := by exact_mod_cast hk8
  have hkR : (m : ℝ) / 16 ≤ k := by linarith
  have hrk : (R.range : ℝ) / (2 ^ 8 * T.side) ≤ k := by
    have e : (R.range : ℝ) / (2 ^ 8 * T.side) = (R.range : ℝ) / (4 * T.side) / 2 ^ 6 := by
      field_simp
      ring
    rw [e]
    have h0 : (0 : ℝ) ≤ k := by positivity
    linarith
  have hLk2 : 2 * R.params.side ≤ R.params.side * k := by
    rw [mul_comm 2]
    exact Nat.mul_le_mul_left _ (by omega)
  have hW₂cast : ((R.params.side * k - 2 * R.params.side : ℕ) : ℝ) = T.side * k - 2 * T.side := by
    rw [Nat.cast_sub hLk2, hLq]
    push_cast
    ring
  have hrM : (R.range : ℝ) ≤ 4 * T.side * m := by
    rwa [div_le_iff₀ (by positivity), mul_comm] at hrm'
  have hLk : (T.side : ℝ) * ((m : ℝ) - 7) / 8 ≤ T.side * k := by
    have : ((m : ℝ) - 7) / 8 ≤ k := by linarith
    calc (T.side : ℝ) * ((m : ℝ) - 7) / 8 = T.side * (((m : ℝ) - 7) / 8) := by ring
      _ ≤ T.side * k := mul_le_mul_of_nonneg_left this hL0.le
  have hW₂ : (R.range : ℝ) / 64 ≤ ((R.params.side * k - 2 * R.params.side : ℕ) : ℝ) := by
    rw [hW₂cast]
    nlinarith
  have hopen : ∀ η ∈ openBallsIn R s.free, s.InBalls η := fun η h b => (h b).le
  have hBm : MeasurableSet (openBallsIn R s.free) := isOpen_openBallsIn.measurableSet
  have Pss : ∀ η ζ : FreeCoords s.free, s.InBalls η → s.InBalls ζ → CoordsAgreeNear s s Y Y k η ζ →
      |(s.blockInteraction Y η - s.blockGaussian T.lam Y η) - (s.blockInteraction Y ζ - s.blockGaussian T.lam Y ζ)| ≤
        Cψ * Real.exp (-(4 * T.rt * k)) ∧
        |s.blockInteraction Y η - s.blockGaussian T.lam Y η| ≤ Cψ * R.coupling := fun η ζ hη hζ hnr =>
    Ps y hyP R hR n n hn hn s s Y Y m k η ζ hs hs hself hk4 hkm hrk hnr hη hζ
  set g : FreeCoords s.free → ℝ := fun η => s.blockInteraction Y η - s.blockGaussian T.lam Y η with hg
  set g' : FreeCoords s.free → ℝ := fun η => D.interaction Y η - gaussianPart T.lam Y η with hg'
  have hgB : AEBounded (volume.restrict (openBallsIn R s.free)) g :=
    (aeBounded_interaction hregs Y).sub (aeBounded_gaussianPart T.lam Y)
  have hgB' : AEBounded (volume.restrict (openBallsIn R s.free)) g' :=
    (aeBounded_interaction hDreg Y).sub (aeBounded_gaussianPart T.lam Y)
  have hg'eq : ∀ η, g' η = g (s.restrictTo X η) := by
    intro η
    have e1 : D.interaction Y η = s.blockInteraction Y (s.restrictTo X η) :=
      restrictedSplit_interaction_of_mem s T.lam X hin η
    have e2 : gaussianPart (R := R) T.lam Y η = s.blockGaussian T.lam Y (s.restrictTo X η) := by
      classical
      show R.coupling * T.lam / 2 * ∑ b ∈ freeBondsAt s.free Y, ‖η b‖ ^ 2 =
        R.coupling * T.lam / 2 * ∑ b ∈ freeBondsAt s.free Y, ‖s.restrictTo X η b‖ ^ 2
      congr 1
      refine Finset.sum_congr rfl fun b hb => ?_
      simp [ChartSetting.restrictTo, hin b hb]
    simp only [hg', hg]
    rw [e1, e2]
  have hgm : Measurable ((openBallsIn R s.free).indicator g) := by
    classical
    have hc : ContinuousOn (fun η => R.coupling * ∑ b ∈ freeBondsAt s.free Y, s.densitySplit.segmentIntegral b η)
        (openBallsIn R s.free) :=
      (continuousOn_const.mul (continuousOn_finsetSum _ fun b _ =>
        continuousOn_segmentIntegral hregs b)).mono openBallsIn_subset_closedBallsIn
    have h1 : Measurable ((openBallsIn R s.free).indicator
        fun η => R.coupling * ∑ b ∈ freeBondsAt s.free Y, s.densitySplit.segmentIntegral b η) := by
      have := hc.measurable_piecewise (g := fun _ => (0 : ℝ)) continuousOn_const hBm
      rwa [show (openBallsIn R s.free).piecewise
        (fun η => R.coupling * ∑ b ∈ freeBondsAt s.free Y, s.densitySplit.segmentIntegral b η)
          (fun _ => (0 : ℝ)) =
          (openBallsIn R s.free).indicator
            (fun η => R.coupling * ∑ b ∈ freeBondsAt s.free Y, s.densitySplit.segmentIntegral b η) from
        Set.piecewise_eq_indicator] at this
    have h2 : Measurable ((openBallsIn R s.free).indicator (s.logJacobianAt Y)) :=
      hregs.measurable_logJacobian Y
    have h3 : Measurable ((openBallsIn R s.free).indicator fun _ : FreeCoords s.free => s.logJacobianAt Y 0) :=
      measurable_const.indicator hBm
    have h4 : Measurable ((openBallsIn R s.free).indicator (s.blockGaussian T.lam Y)) :=
      (continuous_gaussianPart (R := R) (free := s.free) T.lam Y).measurable.indicator hBm
    have e : (openBallsIn R s.free).indicator g = fun η =>
        (openBallsIn R s.free).indicator
          (fun η => R.coupling * ∑ b ∈ freeBondsAt s.free Y, s.densitySplit.segmentIntegral b η) η -
        (openBallsIn R s.free).indicator (s.logJacobianAt Y) η +
        (openBallsIn R s.free).indicator (fun _ => s.logJacobianAt Y 0) η -
        (openBallsIn R s.free).indicator (s.blockGaussian T.lam Y) η := by
      funext η
      by_cases h : η ∈ openBallsIn R s.free
      · simp only [Set.indicator_of_mem h, hg]
        have := interaction_eq hregs (openBallsIn_subset_closedBallsIn h) Y
        show s.densitySplit.interaction Y η - s.blockGaussian T.lam Y η = _
        rw [this]
        rfl
      · simp only [Set.indicator_of_notMem h]
        ring
    rw [e]
    exact ((h1.sub h2).add h3).sub h4
  set Fψ : (NearBondIndex → EuclideanSpace ℝ (Fin 3)) → ℝ := fun z =>
    (openBallsIn R s.free).indicator g (extendByIndex s Y k z) with hFψ
  have hFψm : Measurable Fψ := hgm.comp (measurable_extendByIndex s Y k)
  have hFψb : ∀ z, |Fψ z| ≤ Cψ * R.coupling := by
    intro z
    by_cases h : extendByIndex s Y k z ∈ openBallsIn R s.free
    · simp only [hFψ, Set.indicator_of_mem h]
      exact (Pss _ _ (hopen _ h) (hopen _ h) (fun _ _ => rfl)).2
    · simp only [hFψ, Set.indicator_of_notMem h, abs_zero]
      positivity
  have hFψr : DependsWithin T.side (m / 4) Fψ := by
    intro z z' h
    simp only [hFψ]
    rw [extendByIndex_congr s Y hkq (R := R) (fun q hq => h q (by rw [← hLq] at *; exact hq))]
  have hFψo : ∀ z z', CoordsInBalls R z → CoordsInBalls R z' → |Fψ z - Fψ z'| ≤ 2 * (Cψ * R.coupling) := by
    intro z z' _ _
    have h1 := hFψb z
    have h2 := hFψb z'
    have h3 := abs_sub (Fψ z) (Fψ z')
    linarith
  have hHB : AEBounded (volume.restrict (openBallsIn R s.free)) fun η => Fψ (s.coordsByIndex Y η) :=
    ⟨(hFψm.comp (measurable_coordsByIndex s Y)).aestronglyMeasurable, Cψ * R.coupling,
      Filter.Eventually.of_forall fun η => hFψb _⟩
  have hcl : ∀ η ∈ openBallsIn R s.free,
      |g η - Fψ (s.coordsByIndex Y η)| ≤ Cψ * Real.exp (-(4 * T.rt * k)) := by
    intro η h
    have hz := extendByIndex_mem_openBallsIn s Y k hρ (coordNorm_coordsByIndex_lt s Y hρ h)
    simp only [hFψ, Set.indicator_of_mem hz]
    have hn' := coordsAgreeNear_extendByIndex hodd hself hkm η
    have := (Pss _ _ (hopen _ hz) (hopen _ h) hn').1
    rwa [abs_sub_comm] at this
  have hcl' : ∀ η ∈ openBallsIn R s.free,
      |g' η - Fψ (s.coordsByIndex Y η)| ≤ Cψ * Real.exp (-(4 * T.rt * k)) := by
    intro η h
    have hz := extendByIndex_mem_openBallsIn s Y k hρ (coordNorm_coordsByIndex_lt s Y hρ h)
    have hcz : s.restrictTo X η ∈ openBallsIn R s.free := restrictTo_mem_openBallsIn s X hρ h
    simp only [hFψ, Set.indicator_of_mem hz]
    rw [hg'eq]
    have hn1 := coordsAgreeNear_extendByIndex hodd hself hkm η
    have hn2 := coordsAgreeNear_restrictTo hodd s hdm hkm η
    have hn' : CoordsAgreeNear s s Y Y k (extendByIndex s Y k (s.coordsByIndex Y η)) (s.restrictTo X η) :=
      fun q hq => (hn1 q hq).trans (hn2 q hq)
    have := (Pss _ _ (hopen _ hz) (hopen _ hcz) hn').1
    rwa [abs_sub_comm] at this
  have hτ : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      |weightedMean (s.densitySplit.interpolatedDensity T.lam τ) g - weightedMean (D.interpolatedDensity T.lam τ) g'| ≤
        2 * (Cψ * Real.exp (-(4 * T.rt * k))) + 2 * (Cψ * R.coupling) * Real.exp (-(T.rt * m / 2 ^ 3)) := by
    intro τ hτ'
    have hW : AlikePotentials s s T.lam Y Y m
        (fun η => τ * s.partPotential 0 η + (1 - τ) * s.restrictedPotential T.lam 0 ∅ (s.partPotential 0) η)
        (fun η => τ * s.partPotential 0 η + (1 - τ) * s.restrictedPotential T.lam 0 ∅ (s.partPotential 0) η) :=
      AlikePotentials.convex τ _ _ _ _ hτ'.1 hτ'.2 (AlikePotentials.part_potential 0 le_rfl zero_le_one)
        (AlikePotentials.restrict 0 ∅ ∅ _ _ le_rfl zero_le_one (fun q h h' _ => by simp)
          (AlikePotentials.part_potential 0 le_rfl zero_le_one))
    have hA := AlikePotentials.restrict (s := s) (s' := s) (lam := T.lam) (Y := Y) (Y' := Y) (m := m) 0
      Finset.univ X _ _ le_rfl zero_le_one (fun q h h' hq => by
        simp only [Finset.mem_univ, true_iff]
        exact mem_freeNear_of_isNearIndex hodd s hdm hq h') hW
    have h2 := L3 y hyL R hR n n hn hn s s Y Y m hs hs hself hrm'
      _ _ hA Fψ _ hFψm hFψr hFψo
    rw [restrictedPotential_univ s T.lam, ← weightedMean_interpolatedDensity_eq_lawDensity s hregs,
      ← weightedMean_restricted_interpolatedDensity_eq s T.lam τ X hDreg] at h2
    have h1 := abs_weightedMean_interpolatedDensity_sub_le hcore hρ hp hregs T.lam τ hgB hHB hcl
    have h3 := abs_weightedMean_interpolatedDensity_sub_le hcore hρ hp hDreg T.lam τ hgB' hHB hcl'
    have e := abs_sub_le (weightedMean (s.densitySplit.interpolatedDensity T.lam τ) g)
      (weightedMean (s.densitySplit.interpolatedDensity T.lam τ) fun η => Fψ (s.coordsByIndex Y η))
      (weightedMean (D.interpolatedDensity T.lam τ) g')
    have e2 := abs_sub_le (weightedMean (s.densitySplit.interpolatedDensity T.lam τ) fun η =>
        Fψ (s.coordsByIndex Y η))
      (weightedMean (D.interpolatedDensity T.lam τ) fun η => Fψ (s.coordsByIndex Y η))
      (weightedMean (D.interpolatedDensity T.lam τ) g')
    rw [abs_sub_comm (weightedMean (D.interpolatedDensity T.lam τ) fun η => Fψ (s.coordsByIndex Y η))] at e2
    have h2' : |weightedMean (s.densitySplit.interpolatedDensity T.lam τ) (fun η => Fψ (s.coordsByIndex Y η)) -
        weightedMean (D.interpolatedDensity T.lam τ) fun η => Fψ (s.coordsByIndex Y η)| ≤
        2 * (Cψ * R.coupling) * Real.exp (-(T.rt * m / 2 ^ 3)) := h2
    linarith only [h1, h2', h3, e, e2]
  obtain ⟨hGφ, Mφ, hMφ⟩ := hsd R n s hfit hE1 hx hrn hrL hR.isStep.1 hnq hs
  obtain ⟨G, hGm, hGe⟩ := hGφ Y
  set Fφ : (NearBondIndex → EuclideanSpace ℝ (Fin 3)) → ℝ := fun z => G (extendByIndex s Y k z) with hFφ
  have hFφm : Measurable Fφ := hGm.comp (measurable_extendByIndex s Y k)
  have hFφr : DependsWithin T.side (m / 4) Fφ := by
    intro z z' h
    simp only [hFφ]
    rw [extendByIndex_congr s Y hkq (R := R) (fun q hq => h q (by rw [← hLq] at *; exact hq))]
  have hFφo : ∀ z z', CoordsInBalls R z → CoordsInBalls R z' →
      |Fφ z - Fφ z'| ≤ (R.params.side : ℝ) ^ 4 * (4 * R.params.E + 2) := by
    intro z z' hz hz'
    have a := extendByIndex_inBalls s Y k hρ.le hz
    have b := extendByIndex_inBalls s Y k hρ.le hz'
    simp only [hFφ]
    rw [hGe _ a, hGe _ b]
    exact hosc R n s hfit hE1 hx hrn hrL hR.isStep.1 hnq hs Y _ _ a b
  set eφ : ℝ := (R.params.side : ℝ) ^ 4 *
    Real.exp (-R.params.decayRate * ((R.params.side * k - 2 * R.params.side : ℕ) : ℝ)) with heφ
  have Sss : ∀ η ζ : FreeCoords s.free, s.InBalls η → s.InBalls ζ → CoordsAgreeNear s s Y Y k η ζ →
      |s.blockDensityAt Y η - s.blockDensityAt Y ζ| ≤ eφ := fun η ζ hη hζ hnr =>
    hstate R n n s s Y Y m k η ζ hfit hR.isStep.1 hnq hnq hs hs hself (by omega) hkm hW₂ hnr hη hζ
  have hφB : AEBounded (volume.restrict (openBallsIn R s.free)) (s.densitySplit.density Y) :=
    aeBounded_density hregs Y
  have hφB' : AEBounded (volume.restrict (openBallsIn R s.free)) (D.density Y) := aeBounded_density hDreg Y
  have hKB : AEBounded (volume.restrict (openBallsIn R s.free)) fun η => Fφ (s.coordsByIndex Y η) := by
    refine ⟨(hFφm.comp (measurable_coordsByIndex s Y)).aestronglyMeasurable, Mφ,
      ae_restrict_of_forall_mem hBm fun η h => ?_⟩
    have hz := extendByIndex_inBalls s Y k hρ.le (coordsByIndex_inBalls s Y hρ.le (hopen η h))
    simp only [hFφ]
    rw [hGe _ hz]
    exact hMφ _ hz Y
  have hcφ : ∀ η ∈ openBallsIn R s.free, |s.densitySplit.density Y η - Fφ (s.coordsByIndex Y η)| ≤ eφ := by
    intro η h
    have hz := extendByIndex_inBalls s Y k hρ.le (coordsByIndex_inBalls s Y hρ.le (hopen η h))
    simp only [hFφ]
    rw [hGe _ hz]
    have hn' := coordsAgreeNear_extendByIndex hodd hself hkm η
    have := Sss _ _ hz (hopen η h) hn'
    rwa [abs_sub_comm] at this
  have hcφ' : ∀ η ∈ openBallsIn R s.free, |D.density Y η - Fφ (s.coordsByIndex Y η)| ≤ eφ := by
    intro η h
    have hz := extendByIndex_inBalls s Y k hρ.le (coordsByIndex_inBalls s Y hρ.le (hopen η h))
    have hcz : s.restrictTo X η ∈ openBallsIn R s.free := restrictTo_mem_openBallsIn s X hρ h
    simp only [hFφ]
    rw [hGe _ hz]
    have hn1 := coordsAgreeNear_extendByIndex hodd hself hkm η
    have hn2 := coordsAgreeNear_restrictTo hodd s hdm hkm η
    have hn' : CoordsAgreeNear s s Y Y k (extendByIndex s Y k (s.coordsByIndex Y η)) (s.restrictTo X η) :=
      fun q hq => (hn1 q hq).trans (hn2 q hq)
    have := Sss _ _ hz (hopen _ hcz) hn'
    rw [abs_sub_comm] at this
    exact this
  have hν : ∀ ν ∈ Set.Icc (0 : ℝ) 1,
      |weightedMean (s.densitySplit.perturbedDensity ν) (s.densitySplit.density Y) -
        weightedMean (D.perturbedDensity ν) (D.density Y)| ≤
        2 * eφ + (R.params.side : ℝ) ^ 4 * (4 * R.params.E + 2) * Real.exp (-(T.rt * m / 2 ^ 3)) := by
    intro ν hν'
    have hA := AlikePotentials.restrict (s := s) (s' := s) (lam := T.lam) (Y := Y) (Y' := Y) (m := m) 0
      Finset.univ X _ _ le_rfl zero_le_one (fun q h h' hq => by
        simp only [Finset.mem_univ, true_iff]
        exact mem_freeNear_of_isNearIndex hodd s hdm hq h') (AlikePotentials.part_potential ν hν'.1 hν'.2)
    have h2 := L3 y hyL R hR n n hn hn s s Y Y m hs hs hself hrm'
      _ _ hA Fφ _ hFφm hFφr hFφo
    rw [restrictedPotential_univ s T.lam, ← weightedMean_perturbedDensity_eq_lawDensity s hregs,
      ← weightedMean_restricted_perturbedDensity_eq s T.lam ν X hDreg] at h2
    have h1 := abs_weightedMean_perturbedDensity_sub_le hcore hρ hp hregs ν hφB hKB hcφ
    have h3 := abs_weightedMean_perturbedDensity_sub_le hcore hρ hp hDreg ν hφB' hKB hcφ'
    have e := abs_sub_le (weightedMean (s.densitySplit.perturbedDensity ν) (s.densitySplit.density Y))
      (weightedMean (s.densitySplit.perturbedDensity ν) fun η => Fφ (s.coordsByIndex Y η))
      (weightedMean (D.perturbedDensity ν) (D.density Y))
    have e2 := abs_sub_le (weightedMean (s.densitySplit.perturbedDensity ν) fun η => Fφ (s.coordsByIndex Y η))
      (weightedMean (D.perturbedDensity ν) fun η => Fφ (s.coordsByIndex Y η))
      (weightedMean (D.perturbedDensity ν) (D.density Y))
    rw [abs_sub_comm (weightedMean (D.perturbedDensity ν) fun η => Fφ (s.coordsByIndex Y η))] at e2
    have h2' : |weightedMean (s.densitySplit.perturbedDensity ν) (fun η => Fφ (s.coordsByIndex Y η)) -
        weightedMean (D.perturbedDensity ν) fun η => Fφ (s.coordsByIndex Y η)| ≤
        (R.params.side : ℝ) ^ 4 * (4 * R.params.E + 2) * Real.exp (-(T.rt * m / 2 ^ 3)) := h2
    linarith only [h1, h2', h3, e, e2]
  have h0' : |R.coupling * s.densitySplit.cost Y 0 - R.coupling * D.cost Y 0| ≤ 0 := by
    have : D.cost Y 0 = s.blockCostAt Y 0 := restrictedSplit_cost_zero s T.lam X Y
    rw [this]
    show |R.coupling * s.blockCostAt Y 0 - R.coupling * s.blockCostAt Y 0| ≤ 0
    simp
  have hz := abs_activity_sub_le (D := s.densitySplit) (D' := D) (lam := T.lam) (Y := Y) (Y' := Y) h0'
    (restrictedSplit_logJacobian_zero s T.lam X Y).symm rfl hτ hν
    (continuous_weightedMean_interpolatedDensity hcore hρ hp hregs T.lam hgB)
    (continuous_weightedMean_interpolatedDensity hcore hρ hp hDreg T.lam hgB')
    (continuous_weightedMean_perturbedDensity hcore hρ hp hregs hφB)
    (continuous_weightedMean_perturbedDensity hcore hρ hp hDreg hφB')
  refine le_trans hz ?_
  set q : ℝ := Real.exp (-(c₀ * clusterRange R.coupling)) with hq
  have hqpos : 0 < q := Real.exp_pos _
  have hRr : (clusterRange R.coupling : ℝ) = R.range := rfl
  have hc₀r : c₀ * R.range = T.rt * (R.range / (32 * T.side)) := by
    rw [hc₀]
    field_simp
  have hm32 : (R.range : ℝ) / (32 * T.side) ≤ m / 8 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have q1 : Real.exp (-(T.rt * m / 2 ^ 3)) ≤ q := by
    apply Real.exp_le_exp.mpr
    rw [hRr, hc₀r]
    have := mul_le_mul_of_nonneg_left hm32 hrtpos.le
    have e : T.rt * m / 2 ^ 3 = T.rt * (m / 8) := by ring
    linarith only [this, e]
  have q2 : Real.exp (-(4 * T.rt * k)) ≤ q := by
    apply Real.exp_le_exp.mpr
    rw [hRr, hc₀r]
    have h1 : (m : ℝ) / 8 ≤ 4 * k := by linarith only [hkR]
    have h2 := mul_le_mul_of_nonneg_left (hm32.trans h1) hrtpos.le
    have e : 4 * T.rt * k = T.rt * (4 * k) := by ring
    linarith only [h2, e]
  have hforget : R.params.decayRate = T.rt / 2 ^ 12 := by
    unfold StepParameters.decayRate
    rw [hR.params_eq]
    rfl
  have q3 : Real.exp (-R.params.decayRate * ((R.params.side * k - 2 * R.params.side : ℕ) : ℝ)) ≤ q := by
    apply Real.exp_le_exp.mpr
    rw [hRr, hc₀r, hforget]
    have h1 : (R.range : ℝ) / (32 * T.side) ≤ (R.range : ℝ) / 2 ^ 18 := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      linarith only [hL40]
    have h2 : T.rt * ((R.range : ℝ) / (32 * T.side)) ≤
        T.rt / 2 ^ 12 * ((R.params.side * k - 2 * R.params.side : ℕ) : ℝ) := by
      calc _ ≤ T.rt * ((R.range : ℝ) / 2 ^ 18) := mul_le_mul_of_nonneg_left h1 hrtpos.le
        _ = T.rt / 2 ^ 12 * ((R.range : ℝ) / 64) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hW₂ (by positivity)
    linarith only [h2]
  have hLl4 : (R.params.side : ℝ) ^ 4 = (T.side : ℝ) ^ 4 := by rw [hLR]
  have hrpow : R.coupling ≤ R.coupling ^ C₀ := by
    have hC1 : 1 ≤ C₀ := by
      have h1 : 0 ≤ 2 ^ 21 * (T.side : ℝ) := by positivity
      have h2 : 0 ≤ 4 * (T.n₀ : ℝ) := by positivity
      linarith only [h1, h2, hKfpos]
    exact Real.self_le_rpow_of_one_le hx1 hC1
  have hy7 := hFl.stretched_tail.1
  have hsum : 0 + (2 * (Cψ * Real.exp (-(4 * T.rt * k))) +
      2 * (Cψ * R.coupling) * Real.exp (-(T.rt * m / 2 ^ 3))) +
      (2 * eφ + (R.params.side : ℝ) ^ 4 * (4 * R.params.E + 2) * Real.exp (-(T.rt * m / 2 ^ 3))) ≤
      Kf * R.coupling * q := by
    have a1 : Cψ * Real.exp (-(4 * T.rt * k)) ≤ Cψ * q := mul_le_mul_of_nonneg_left q2 hCψ.le
    have a2 : Cψ * R.coupling * Real.exp (-(T.rt * m / 2 ^ 3)) ≤ Cψ * R.coupling * q :=
      mul_le_mul_of_nonneg_left q1 (by positivity)
    have a3 : eφ ≤ (T.side : ℝ) ^ 4 * q := by
      rw [heφ, hLl4]
      exact mul_le_mul_of_nonneg_left q3 (by positivity)
    have a4 : (T.side : ℝ) ^ 4 * (4 * T.E + 2) * Real.exp (-(T.rt * m / 2 ^ 3)) ≤
        (T.side : ℝ) ^ 4 * (4 * T.E + 2) * q := mul_le_mul_of_nonneg_left q1 (by positivity)
    have hb : Cψ * q ≤ Cψ * R.coupling * q := by
      have : Cψ * q * 1 ≤ Cψ * q * R.coupling := mul_le_mul_of_nonneg_left hx1 (by positivity)
      linarith only [this]
    have hc : (T.side : ℝ) ^ 4 * q ≤ (T.side : ℝ) ^ 4 * R.coupling * q := by
      have : (T.side : ℝ) ^ 4 * q * 1 ≤ (T.side : ℝ) ^ 4 * q * R.coupling :=
        mul_le_mul_of_nonneg_left hx1 (by positivity)
      linarith only [this]
    have hd : (T.side : ℝ) ^ 4 * (4 * T.E + 2) * q ≤ (T.side : ℝ) ^ 4 * (4 * T.E + 2) * R.coupling * q := by
      have : (T.side : ℝ) ^ 4 * (4 * T.E + 2) * q * 1 ≤ (T.side : ℝ) ^ 4 * (4 * T.E + 2) * q * R.coupling :=
        mul_le_mul_of_nonneg_left hx1 (by positivity)
      linarith only [this]
    rw [hLl4, hEq]
    have e : Kf * R.coupling * q = 4 * (Cψ * R.coupling * q) + 2 * ((T.side : ℝ) ^ 4 * R.coupling * q) +
        (T.side : ℝ) ^ 4 * (4 * T.E + 2) * R.coupling * q := by
      rw [hKf]
      ring
    have e2 : 2 * (Cψ * R.coupling) * Real.exp (-(T.rt * m / 2 ^ 3)) =
        2 * (Cψ * R.coupling * Real.exp (-(T.rt * m / 2 ^ 3))) := by ring
    rw [e, e2]
    linarith only [a1, a2, a3, a4, hb, hc, hd]
  refine hsum.trans ?_
  have hKC : Kf ≤ C₀ := by
    have h1 : 0 ≤ 2 ^ 21 * (T.side : ℝ) := by positivity
    have h2 : 0 ≤ 4 * (T.n₀ : ℝ) := by positivity
    linarith only [h1, h2]
  have h5 : Kf * R.coupling * q ≤ C₀ * R.coupling ^ C₀ * q := by
    have h6 : Kf * R.coupling ≤ C₀ * R.coupling ^ C₀ := mul_le_mul hKC hrpow hx.le hC₀pos.le
    exact mul_le_mul_of_nonneg_right h6 hqpos.le
  have h7 : Real.exp (-(R.coupling ^ (1 / 200 : ℝ))) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have : 0 ≤ R.coupling ^ (1 / 200 : ℝ) := Real.rpow_nonneg hx.le _
    linarith only [this]
  exact h5.trans (hy7.trans h7)
end YangMills.Construction.ClusterExpansionOfAStep
end
