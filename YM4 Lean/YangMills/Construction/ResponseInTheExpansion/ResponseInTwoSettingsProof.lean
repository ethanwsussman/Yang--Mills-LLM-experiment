import YangMills.Construction.ClusterExpansionOfAStep.AllowedStatesReadTheirBoxProof
import YangMills.Construction.ClusterExpansionOfAStep.DeepDensitiesAgainstTheCutProof
import YangMills.Construction.ClusterExpansionOfAStep.SecondOrderOnMultiplesOfASideProof
import YangMills.Construction.ResponseInTheExpansion.FarSpinsMoveAVariableProof
import YangMills.Construction.ResponseInTheExpansion.ScoresOfTwoSettings
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open scoped Quaternion
open MeasureTheory Set
namespace YangMills.Construction.StepSettings
open BlockAverages ColdStepAtMirrorFrames TorusFields TorusLumps BlockOffsets StepCosts RenormalizationStepParameters StepGas
open YangMills.Construction.ClusterExpansionOfAStep
section Extension
variable {R : StepSetup} {n n' : ℕ} [NeZero n] [NeZero n']
private theorem isNearIndex_mono {L k m : ℕ} {q : NearBondIndex} (hq : IsNearIndex L k q) (h : k ≤ m) :
    IsNearIndex L m q :=
  ⟨fun i => (hq.1 i).trans (by exact_mod_cast h), hq.2⟩
private theorem nearBond_injOn (hodd : Odd R.params.side) {Y : TorusSite n} {k : ℕ} (hk : 2 * k + 2 < n)
    {q q' : NearBondIndex} (hq : IsNearIndex R.params.side k q) (hq' : IsNearIndex R.params.side k q')
    (e : nearBond R.params.side Y q = nearBond R.params.side Y q') : q = q' := by
  exact _root_.YangMills.Construction.ClusterExpansionOfAStep.DeepCutoff.nearBond_inj_of_isNearIndex
    (R := R) (n := n) (Y := Y) (k := k) hodd hk hq hq' e
open Classical in
private def ChartSetting.extendNear (s : ChartSetting R n) (Y : TorusSite n) (k : ℕ)
    (z : NearBondIndex → EuclideanSpace ℝ (Fin 3)) : FreeCoords s.free :=
  fun b => if h : ∃ q, IsNearIndex R.params.side k q ∧ nearBond R.params.side Y q = b.1 then z h.choose else 0
private theorem extendNear_apply (hodd : Odd R.params.side) (s : ChartSetting R n) {Y : TorusSite n} {k : ℕ}
    (hk : 2 * k + 2 < n) (z : NearBondIndex → EuclideanSpace ℝ (Fin 3)) {q : NearBondIndex}
    (hq : IsNearIndex R.params.side k q) (h : nearBond R.params.side Y q ∈ s.free) :
    s.extendNear Y k z ⟨_, h⟩ = z q := by
  classical
  have hex : ∃ q', IsNearIndex R.params.side k q' ∧ nearBond R.params.side Y q' = (⟨_, h⟩ : s.free).1 :=
    ⟨q, hq, rfl⟩
  unfold ChartSetting.extendNear
  rw [dif_pos hex]
  rw [nearBond_injOn hodd hk hex.choose_spec.1 hq hex.choose_spec.2]
private theorem coordsAgreeNear_extendNear (hodd : Odd R.params.side) {s : ChartSetting R n}
    {s' : ChartSetting R n'} {Y : TorusSite n} {Y' : TorusSite n'} {m k : ℕ}
    (hag : SettingsAgreeNear s s' Y Y' m) (hkm : k ≤ m) (η' : FreeCoords s'.free) :
    CoordsAgreeNear s s' Y Y' k (s.extendNear Y k (s'.coordsByIndex Y' η')) η' := by
  classical
  have hk : 2 * k + 2 < n := by have := hag.lt_extent; omega
  intro q hq
  by_cases h : nearBond R.params.side Y q ∈ s.free
  · have e : s.coordsByIndex Y (s.extendNear Y k (s'.coordsByIndex Y' η')) q =
        s.extendNear Y k (s'.coordsByIndex Y' η') ⟨_, h⟩ := dif_pos h
    rw [e, extendNear_apply hodd s hk _ hq h]
  · have h' : nearBond R.params.side Y' q ∉ s'.free := fun hh =>
      h ((hag.free_iff q (isNearIndex_mono hq hkm)).mpr hh)
    have e : s.coordsByIndex Y (s.extendNear Y k (s'.coordsByIndex Y' η')) q = 0 := dif_neg h
    have e' : s'.coordsByIndex Y' η' q = 0 := dif_neg h'
    rw [e, e']
private theorem settingsAgreeNear_self {s : ChartSetting R n} {s' : ChartSetting R n'} {Y : TorusSite n}
    {Y' : TorusSite n'} {m : ℕ} (hag : SettingsAgreeNear s s' Y Y' m) : SettingsAgreeNear s s Y Y m :=
  ⟨hag.lt_extent, hag.lt_extent, fun _ _ => rfl, fun _ _ => Iff.rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
    fun _ _ _ _ => Iff.rfl, fun _ _ _ _ _ _ => rfl, fun h hh => by
      obtain ⟨o, ho, e, _⟩ := hag.bases_match h hh
      exact ⟨o, ho, e, e⟩⟩
private theorem coordNorm_zero : coordNorm 0 = 0 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.DeepCutoff.coordNorm_zero <;> assumption
private theorem extendNear_inBalls (s : ChartSetting R n) (Y : TorusSite n) (k : ℕ)
    {z : NearBondIndex → EuclideanSpace ℝ (Fin 3)} (hρ : 0 ≤ R.ballRadius) (hz : CoordsInBalls R z) :
    s.InBalls (s.extendNear Y k z) := by
  classical
  intro b
  unfold ChartSetting.extendNear
  by_cases h : ∃ q, IsNearIndex R.params.side k q ∧ nearBond R.params.side Y q = b.1
  · rw [dif_pos h]
    exact hz _
  · rw [dif_neg h, coordNorm_zero]
    exact hρ
private theorem coordsInBalls_coordsByIndex (s : ChartSetting R n) (Y : TorusSite n) {η : FreeCoords s.free}
    (hρ : 0 ≤ R.ballRadius) (hη : s.InBalls η) : CoordsInBalls R (s.coordsByIndex Y η) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.DeepCutoff.coordsByIndex_inBalls <;> assumption
private theorem measurable_coordsByIndex (s : ChartSetting R n) (Y : TorusSite n) :
    Measurable (s.coordsByIndex Y) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.DeepCutoff.measurable_coordsByIndex <;> assumption
private theorem measurable_extendNear (s : ChartSetting R n) (Y : TorusSite n) (k : ℕ) :
    Measurable (s.extendNear Y k) := by
  classical
  refine measurable_pi_iff.mpr fun b => ?_
  unfold ChartSetting.extendNear
  by_cases h : ∃ q, IsNearIndex R.params.side k q ∧ nearBond R.params.side Y q = b.1
  · simp only [dif_pos h]
    exact measurable_pi_apply _
  · simp only [dif_neg h]
    exact measurable_const
private theorem extendNear_congr (s : ChartSetting R n) (Y : TorusSite n) {k m : ℕ} (hkm : k ≤ m)
    {z z' : NearBondIndex → EuclideanSpace ℝ (Fin 3)} (h : ∀ q, IsNearIndex R.params.side m q → z q = z' q) :
    s.extendNear Y k z = s.extendNear Y k z' := by
  classical
  funext b
  unfold ChartSetting.extendNear
  by_cases he : ∃ q, IsNearIndex R.params.side k q ∧ nearBond R.params.side Y q = b.1
  · rw [dif_pos he, dif_pos he]
    exact h _ (isNearIndex_mono he.choose_spec.1 hkm)
  · rw [dif_neg he, dif_neg he]
end Extension
private theorem cellOffset_torusFrame_blockPoint {L n : ℕ} [NeZero L] [NeZero n] (t : ℕ) (hodd : Odd L)
    (A o : Fin 4 → ℤ) (ho : o ∈ centredCube L) :
    cellOffset (F := torusFrame L t n)
      (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).depth
        (siteOfInt (blockPoint L A o) : TorusSite (n * L))) = o := by apply _root_.YangMills.Construction.InBoxTransfer.cellOffset_torusFrame <;> assumption
private theorem measurable_chartField {R : StepSetup} {n : ℕ} (s : ChartSetting R n) : Measurable s.field := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ChartSetting.measurable_field <;> assumption
end YangMills.Construction.StepSettings
namespace YangMills.Construction.WeightedResponses
open YangMills.Construction.StepSettings
open BlockAverages ColdStepAtMirrorFrames TorusFields TorusLumps BlockOffsets StepCosts RenormalizationStepParameters StepGas
open YangMills.Construction.ClusterExpansionOfAStep
section Means
variable {R : StepSetup} {n : ℕ} [NeZero n] {free : Finset (TorusBond (n * R.params.side))}
private theorem abs_weightedMean_le {d G : FreeCoords free → ℝ} {M : ℝ} (hd : ∀ η, 0 ≤ d η) (hM : 0 ≤ M)
    (hG : ∀ η, d η ≠ 0 → |G η| ≤ M) : |weightedMean d G| ≤ M := by
  unfold weightedMean
  by_cases hi : Integrable d
  · have h0 : 0 ≤ ∫ η, d η := integral_nonneg hd
    rcases h0.eq_or_lt with h | h
    · rw [← h, div_zero, abs_zero]
      exact hM
    · rw [abs_div, abs_of_pos h, div_le_iff₀ h]
      calc |∫ η, G η * d η| ≤ ∫ η, |G η * d η| := abs_integral_le_integral_abs
        _ ≤ ∫ η, M * d η := by
            refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _) (hi.const_mul M)
              (Filter.Eventually.of_forall fun η => ?_)
            by_cases h0 : d η = 0
            · simp [h0]
            · show |G η * d η| ≤ M * d η
              rw [abs_mul, abs_of_nonneg (hd η)]
              exact mul_le_mul_of_nonneg_right (hG η h0) (hd η)
        _ = M * ∫ η, d η := integral_const_mul _ _
  · rw [integral_undef hi, div_zero, abs_zero]
    exact hM
private theorem weightedMean_congr {d G G' : FreeCoords free → ℝ} (h : ∀ η, d η ≠ 0 → G η = G' η) :
    weightedMean d G = weightedMean d G' := by
  unfold weightedMean
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
  by_cases h0 : d η = 0
  · simp [h0]
  · show G η * d η = G' η * d η
    rw [h η h0]
private theorem integrable_mul_of_abs_le {d G : FreeCoords free → ℝ} {M : ℝ} (hi : Integrable d)
    (hd : ∀ η, 0 ≤ d η) (hGm : Measurable G) (hG : ∀ η, d η ≠ 0 → |G η| ≤ M) :
    Integrable fun η => G η * d η := by
  refine Integrable.mono' (hi.const_mul M) (hGm.aestronglyMeasurable.mul hi.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun η => ?_)
  by_cases h0 : d η = 0
  · simp [h0]
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hd η)]
    exact mul_le_mul_of_nonneg_right (hG η h0) (hd η)
private theorem abs_weightedMean_sub_le {d G G' : FreeCoords free → ℝ} {e : ℝ} (hd : ∀ η, 0 ≤ d η)
    (he : 0 ≤ e) (h1 : Integrable fun η => G η * d η) (h2 : Integrable fun η => G' η * d η)
    (hG : ∀ η, d η ≠ 0 → |G η - G' η| ≤ e) : |weightedMean d G - weightedMean d G'| ≤ e := by
  have : weightedMean d G - weightedMean d G' = weightedMean d fun η => G η - G' η := by
    unfold weightedMean
    rw [← sub_div, ← integral_sub h1 h2]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    show G η * d η - G' η * d η = (G η - G' η) * d η
    ring
  rw [this]
  exact abs_weightedMean_le hd he hG
end Means
section Settings
variable {R : StepSetup} {n n' : ℕ} [NeZero n] [NeZero n']
private theorem chartDensity_nonneg (s : ChartSetting R n) (η : FreeCoords s.free) : 0 ≤ chartDensity s η := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSpin.chartDensity_nonneg <;> assumption
private theorem inBalls_of_chartDensity_ne_zero (s : ChartSetting R n) {η : FreeCoords s.free}
    (h : chartDensity s η ≠ 0) : s.InBalls η := by
  intro b
  have h1 : s.cutoffProduct η ≠ 0 := left_ne_zero_of_mul h
  have h2 := (Finset.prod_ne_zero_iff.mp h1) b (Finset.mem_univ _)
  unfold cutoffFactor at h2
  by_contra hc
  rw [if_neg (fun hlt => hc hlt.le)] at h2
  exact h2 rfl
abbrev _root_.YangMills.SharedProofs.p4538 := @inBalls_of_chartDensity_ne_zero
private theorem weightNorm_nonneg (L t : ℕ) {m : ℕ} (h : PlaquetteWeight m) : 0 ≤ weightNorm L t h :=
  le_max_of_le_left (Real.iSup_nonneg fun _ => abs_nonneg _)
private theorem isCold_trivialField (m : ℕ) {σ : ℝ} (hσ : 0 < σ) : IsCold σ (trivialField m) := by apply _root_.YangMills.Construction.AbelianSecondOrder.isCold_trivialField <;> assumption
private theorem isLiveState_chartField (hrow : R.HasExpansions) (hfit : R.params.Admissible)
    (hn : R.params.n₀ ≤ n) {s : ChartSetting R n} (hs : s.IsAdmissible) {η : FreeCoords s.free}
    (hη : s.InBalls η) : IsLiveState R.params R.coupling R.labelWeight (s.field η) s.support s.labelling := by
  have hL : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hbs : IsBlockTorusSide R.params (n * R.params.side) :=
    ⟨Dvd.intro_left _ rfl, by rw [mul_comm]; exact Nat.mul_le_mul_right _ hn⟩
  refine ⟨hs.isHull η hη, ?_⟩
  have hnn : R.params.n₀ ≤ n * R.params.side := hn.trans (Nat.le_mul_of_pos_right _ hL)
  rw [hrow.2.form (n * R.params.side) hbs (s.field η) s.support s.labelling (hs.isHull η hη)]
  refine mul_pos (mul_pos (hrow.1.positive (n * R.params.side) hnn _
    (isCold_trivialField _ hfit.σ_pos)) (Real.exp_pos _)) ?_
  refine Finset.prod_pos fun X hX => lt_of_le_of_ne ?_ (hs.factor_ne_zero η hη X hX).symm
  exact hrow.2.factor_nonneg (n * R.params.side) hbs _ _ _ X
abbrev _root_.YangMills.SharedProofs.p48283 := @isLiveState_chartField
variable (A : ResponseSetup R)
private theorem abs_centeredHullResponse_sub_le (hrow : R.HasExpansions) (hfit : R.params.Admissible)
    (hA : ResponseBounds R.params A.responseParams R.depth R.coupling A.coeff R.labels R.labelWeight A.score
      A.cold A.hull A.siteRemainder A.totalRemainder)
    (hn : R.params.n₀ ≤ n) (hn' : R.params.n₀ ≤ n') {s : ChartSetting R n} {s' : ChartSetting R n'}
    {Y : TorusSite n} {Y' : TorusSite n'} {m k : ℕ} {η : FreeCoords s.free} {η' : FreeCoords s'.free}
    (hs : s.IsAdmissible) (hs' : s'.IsAdmissible) (hag : SettingsAgreeNear s s' Y Y' m) (hk2 : 2 ≤ k)
    (hk : k ≤ m) (hr : (R.range : ℝ) / 64 ≤ ((R.params.side * k - 2 * R.params.side : ℕ) : ℝ))
    (hnear : CoordsAgreeNear s s' Y Y' k η η') (hb : s.InBalls η) (hb' : s'.InBalls η')
    {o : Fin 4 → ℤ} (ho : o ∈ centredCube R.params.side)
    {h : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side))}
    {h' : PlaquetteWeight (fineSide R.params.side R.depth (n' * R.params.side))}
    (hw : WeightsAgreeAt R.params.side R.depth (fineSite R.params.side Y 0 o) (fineSite R.params.side Y' 0 o) h h') :
    |centeredHullResponse A.cold A.hull (n * R.params.side) (fineSite R.params.side Y 0 o) (s.field η)
          s.support s.labelling h -
        centeredHullResponse A.cold A.hull (n' * R.params.side) (fineSite R.params.side Y' 0 o) (s'.field η')
          s'.support s'.labelling h'| ≤
      (1 + siteScore A.score s.support s.labelling (fineSite R.params.side Y 0 o)) *
        Real.exp (-R.params.decayRate * ((R.params.side * k - 2 * R.params.side : ℕ) : ℝ)) *
          weightNorm R.params.side R.depth h := by
  have hodd := hfit.L_odd
  have hn0 := hfit.n₀_ge
  have h2 : 2 ≤ n := by omega
  have h2' : 2 ≤ n' := by omega
  have hL : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hk1 : 1 ≤ k := by omega
  set m₂ := R.params.side * k - 2 * R.params.side with hm₂
  have hm₂le : m₂ ≤ R.params.side * k - R.params.side := by omega
  have hbs : IsBlockTorusSide R.params (n * R.params.side) :=
    ⟨Dvd.intro_left _ rfl, by rw [mul_comm]; exact Nat.mul_le_mul_right _ hn⟩
  have hbs' : IsBlockTorusSide R.params (n' * R.params.side) :=
    ⟨Dvd.intro_left _ rfl, by rw [mul_comm]; exact Nat.mul_le_mul_right _ hn'⟩
  have hside : ∀ N : ℕ, 2 * m + 2 < N → 2 * m₂ + 2 < N * R.params.side := by
    intro N hN
    have h1 : (2 * m + 3) * R.params.side ≤ N * R.params.side := Nat.mul_le_mul_right _ hN
    have h2 : R.params.side * k ≤ R.params.side * m := Nat.mul_le_mul_left _ hk
    have h3 : (2 * m + 3) * R.params.side = 2 * (R.params.side * m) + 3 * R.params.side := by ring
    omega
  have hfa := fieldsAgreeNear_of_settings hodd h2 h2' hs.subset_chart hag hk1 hk hnear ho
  refine hA.forget (n * R.params.side) (n' * R.params.side) hbs hbs' _ _ _ _ _ _ _ _ m₂ h h'
    (isLiveState_chartField hrow hfit hn hs hb) (isLiveState_chartField hrow hfit hn' hs' hb') hr ?_ hw
  refine ⟨hside n hag.lt_extent, hside n' hag.lt_extent', ?_, ?_, ?_, ?_⟩
  · intro b hbb
    exact hfa b ⟨fun l => (hbb.1 l).trans (by exact_mod_cast hm₂le),
      fun l => (hbb.2 l).trans (by exact_mod_cast hm₂le)⟩
  · intro e hh
    obtain ⟨kk, o', ho', hkk, hx⟩ := exists_fineSite_add hodd hk1 ho
      (fun l => (hh l).trans (by exact_mod_cast hm₂le) :
        OffsetInBox (R.params.side * k - R.params.side) e)
    rw [hx, hx]
    exact hag.support_iff kk o' (fun l => by have := hkk l; omega) ho'
  · intro e hh hz hz' _
    obtain ⟨kk, o', ho', hkk, hx⟩ := exists_fineSite_add hodd hk1 ho
      (fun l => (hh l).trans (by exact_mod_cast hm₂le) :
        OffsetInBox (R.params.side * k - R.params.side) e)
    have e1 := hx _ Y
    have e2 := hx _ Y'
    have hz1 : fineSite R.params.side Y kk o' ∈ s.support := e1 ▸ hz
    have hz2 : fineSite R.params.side Y' kk o' ∈ s'.support := e2 ▸ hz'
    have := hag.labelling_eq kk o' hz1 hz2 (fun l => by have := hkk l; omega) ho'
    calc s.labelling ⟨_, hz⟩ = s.labelling ⟨_, hz1⟩ := by congr 1; exact Subtype.ext e1
      _ = s'.labelling ⟨_, hz2⟩ := this
      _ = s'.labelling ⟨_, hz'⟩ := by congr 1; exact Subtype.ext e2.symm
  · intro _
    exact sameBlockPosition_fineSite R.params Y Y' 0 o
private def liveHullResponse (s : ChartSetting R n) (y : TorusSite (n * R.params.side))
    (h : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side)))
    (W : TorusField (n * R.params.side)) : ℝ :=
  open Classical in
  (if IsLiveState R.params R.coupling R.labelWeight W s.support s.labelling then
      A.hull (n * R.params.side) y W s.support s.labelling h else 0) -
    A.cold (n * R.params.side) y (trivialField (n * R.params.side)) h
private theorem measurable_liveHullResponse
    (hA : ResponseBounds R.params A.responseParams R.depth R.coupling A.coeff R.labels R.labelWeight A.score
      A.cold A.hull A.siteRemainder A.totalRemainder)
    (hbs : IsBlockTorusSide R.params (n * R.params.side)) (s : ChartSetting R n)
    (y : TorusSite (n * R.params.side)) (h : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side))) :
    Measurable (liveHullResponse A s y h) := by
  classical
  have h1 := hA.hull_borel (n * R.params.side) hbs y s.support h
  have h2 : Measurable fun W : TorusField (n * R.params.side) => (W, s.labelling) :=
    measurable_id.prodMk measurable_const
  exact (h1.comp h2).sub_const _
private theorem liveHullResponse_eq {s : ChartSetting R n} {y : TorusSite (n * R.params.side)}
    {h : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side))} {W : TorusField (n * R.params.side)}
    (hl : IsLiveState R.params R.coupling R.labelWeight W s.support s.labelling) :
    liveHullResponse A s y h W = centeredHullResponse A.cold A.hull (n * R.params.side) y W s.support s.labelling h := by
  classical
  unfold liveHullResponse centeredHullResponse
  rw [if_pos hl]
private theorem exp_bound_two_charts {rt f m m₂ C : ℝ} (hrt : 0 < rt) (hC : 0 ≤ C) (hf : rt * m / 16 ≤ f * m₂)
    (hbig : 2 + 2 * C ≤ rt * m / 32) :
    2 * Real.exp (-f * m₂) + 2 * C * Real.exp (-(rt * m / 2 ^ 3)) ≤ Real.exp (-(rt * m / 2 ^ 5)) := by
  have e1 : Real.exp (-f * m₂) ≤ Real.exp (-(rt * m / 16)) := by
    apply Real.exp_le_exp.mpr
    linarith
  have e2 : Real.exp (-(rt * m / 2 ^ 3)) ≤ Real.exp (-(rt * m / 16)) := by
    apply Real.exp_le_exp.mpr
    norm_num
    linarith
  have e3 : Real.exp (-(rt * m / 2 ^ 5)) = Real.exp (-(rt * m / 16)) * Real.exp (rt * m / 32) := by
    rw [← Real.exp_add]
    congr 1
    norm_num
    ring
  have e4 : 2 + 2 * C ≤ Real.exp (rt * m / 32) := by
    have := Real.add_one_le_exp (rt * m / 32)
    linarith
  have hpos := Real.exp_pos (-(rt * m / 16))
  rw [e3]
  calc 2 * Real.exp (-f * m₂) + 2 * C * Real.exp (-(rt * m / 2 ^ 3))
      ≤ 2 * Real.exp (-(rt * m / 16)) + 2 * C * Real.exp (-(rt * m / 16)) := by
        have := mul_le_mul_of_nonneg_left e2 (by positivity : 0 ≤ 2 * C)
        linarith
    _ = Real.exp (-(rt * m / 16)) * (2 + 2 * C) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left e4 hpos.le
end Settings
private theorem weighted_error_bound {K sy S E₁ E₂ E₃ : ℝ} (hK1 : 1 ≤ K) (hsy : 0 ≤ sy) (hS : 0 ≤ S)
    (hE₃ : 0 < E₃) (hnm : 2 * E₂ + 2 * K * E₃ ≤ E₁) :
    2 * ((1 + sy) * E₂ * S) + 2 * ((K + sy) * S) * E₃ ≤ (1 + sy) * S * E₁ := by
  have h0 : 0 ≤ (1 + sy) * S := mul_nonneg (by linarith) hS
  have h1 := mul_le_mul_of_nonneg_left hnm h0
  have h2 : 0 ≤ (K - 1) * sy * S * E₃ :=
    mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hsy) hS) hE₃.le
  nlinarith only [h1, h2]
private theorem siteScore_nonneg {Ω : Type} {s : Ω → ℝ} (hs : ∀ w, 0 ≤ s w) {n : ℕ} (Y : Finset (TorusSite n))
    (ω : Y → Ω) (y : TorusSite n) : 0 ≤ siteScore s Y ω y := by apply _root_.YangMills.SharedProofs.p22275 <;> assumption
private theorem lawDensity_partPotential_one {R : StepSetup} {n : ℕ} [NeZero n] (s : ChartSetting R n) :
    s.lawDensity (s.partPotential 1) = chartDensity s := by
  funext η
  unfold ChartSetting.lawDensity chartDensity ChartSetting.partPotential ChartSetting.potential
  simp only [one_mul]
private theorem radius_bounds {Lr r m k rt Cc : ℝ} (hL40 : (2 : ℝ) ^ 40 ≤ Lr) (hrt : 0 < rt)
    (hr2 : 2 ^ 21 * Lr ≤ r) (hr3 : 2 ^ 7 * Lr * (2 + 2 * Cc) / rt ≤ r) (hrm : r / (4 * Lr) ≤ m)
    (hk8 : m ≤ 8 * k + 7) :
    (2 : ℝ) ^ 19 ≤ m ∧ r / 64 ≤ Lr * k - 2 * Lr ∧ rt * m / 16 ≤ rt / 2 ^ 12 * (Lr * k - 2 * Lr) ∧
      2 + 2 * Cc ≤ rt * m / 32 := by
  have hL0 : 0 < Lr := lt_of_lt_of_le (by positivity) hL40
  have hM : (2 : ℝ) ^ 19 ≤ m := by
    refine le_trans ?_ hrm
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [hr2, hL0]
  have hrM : r ≤ 4 * Lr * m := by
    rwa [div_le_iff₀ (by positivity), mul_comm] at hrm
  have hkge : m / 16 ≤ k - 2 := by linarith only [hk8, hM]
  have hLk : Lr * (m / 16) ≤ Lr * (k - 2) := mul_le_mul_of_nonneg_left hkge hL0.le
  have e1 : Lr * k - 2 * Lr = Lr * (k - 2) := by ring
  have hm0 : 0 ≤ m := le_trans (by positivity) hM
  refine ⟨hM, ?_, ?_, ?_⟩
  · rw [e1]
    linarith only [hLk, hrM]
  · rw [e1]
    have h3 : (2 : ℝ) ^ 8 * m ≤ Lr * (k - 2) := by
      have h4 : (2 : ℝ) ^ 40 * (m / 16) ≤ Lr * (m / 16) :=
        mul_le_mul_of_nonneg_right hL40 (by positivity)
      have h5 : (2 : ℝ) ^ 8 * m ≤ 2 ^ 40 * (m / 16) := by
        norm_num
        linarith only [hm0]
      linarith only [h4, h5, hLk]
    have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ rt / 2 ^ 12)
    have e2 : rt / 2 ^ 12 * ((2 : ℝ) ^ 8 * m) = rt * m / 16 := by ring
    linarith only [h4, e2]
  · have h1 : 2 ^ 7 * Lr * (2 + 2 * Cc) ≤ r * rt := by
      rwa [div_le_iff₀ hrt] at hr3
    have h2 : r * rt ≤ 4 * Lr * m * rt := mul_le_mul_of_nonneg_right hrM hrt.le
    have h3 : 2 ^ 7 * Lr * (2 + 2 * Cc) ≤ 2 ^ 7 * Lr * (rt * m / 32) := by
      have e : 2 ^ 7 * Lr * (rt * m / 32) = 4 * Lr * m * rt := by ring
      rw [e]
      linarith only [h1, h2]
    exact le_of_mul_le_mul_left h3 (by positivity)
private theorem abs_weightedMean_sub_of_chain {R : StepSetup} {n n' : ℕ} [NeZero n] [NeZero n']
    {free : Finset (TorusBond (n * R.params.side))} {free' : Finset (TorusBond (n' * R.params.side))}
    {d G₁ G₂ : FreeCoords free → ℝ} {d' G₃ G₄ : FreeCoords free' → ℝ} {e B : ℝ} (hd : ∀ η, 0 ≤ d η)
    (hd' : ∀ η, 0 ≤ d' η) (he : 0 ≤ e)
    (i₁ : Integrable fun η => G₁ η * d η) (i₂ : Integrable fun η => G₂ η * d η)
    (i₃ : Integrable fun η => G₃ η * d' η) (i₄ : Integrable fun η => G₄ η * d' η)
    (c₁ : ∀ η, d η ≠ 0 → |G₁ η - G₂ η| ≤ e) (c₂ : ∀ η, d' η ≠ 0 → |G₃ η - G₄ η| ≤ e)
    (hB : |weightedMean d G₂ - weightedMean d' G₃| ≤ B) :
    |weightedMean d G₁ - weightedMean d' G₄| ≤ 2 * e + B := by
  have a1 := abs_weightedMean_sub_le hd he i₁ i₂ c₁
  have a3 := abs_weightedMean_sub_le hd' he i₃ i₄ c₂
  have t1 := abs_sub_le (weightedMean d G₁) (weightedMean d G₂) (weightedMean d' G₄)
  have t2 := abs_sub_le (weightedMean d G₂) (weightedMean d' G₃) (weightedMean d' G₄)
  linarith only [a1, a3, t1, t2, hB]
section Parts
variable {R : StepSetup} {n n' : ℕ} [NeZero n] [NeZero n']
private theorem abs_chartResponse_sub_le (A : ResponseSetup R) (hrow : R.HasExpansions)
    (hfit : R.params.Admissible)
    (hA : ResponseBounds R.params A.responseParams R.depth R.coupling A.coeff R.labels R.labelWeight A.score
      A.cold A.hull A.siteRemainder A.totalRemainder)
    (hn : R.params.n₀ ≤ n) (hn' : R.params.n₀ ≤ n') (hρ : 0 < R.ballRadius) (hsnn : ∀ w, 0 ≤ A.score w)
    (hK1 : 1 ≤ A.responseParams.C₀) {s : ChartSetting R n} {s' : ChartSetting R n'} {Y : TorusSite n}
    {Y' : TorusSite n'} {m k Lt : ℕ} (hs : s.IsAdmissible) (hs' : s'.IsAdmissible)
    (hag : SettingsAgreeNear s s' Y Y' m) (hk2 : 2 ≤ k) (hkm : k ≤ m) (hkq : k ≤ m / 4) (hLq : R.params.side = Lt)
    (hW₂ : (R.range : ℝ) / 64 ≤ ((R.params.side * k - 2 * R.params.side : ℕ) : ℝ)) {E₁ E₃ : ℝ} (hE₃ : 0 < E₃)
    (hnum : 2 * Real.exp (-R.params.decayRate * ((R.params.side * k - 2 * R.params.side : ℕ) : ℝ)) +
      2 * A.responseParams.C₀ * E₃ ≤ E₁)
    (hL3 : ∀ (F : (NearBondIndex → EuclideanSpace ℝ (Fin 3)) → ℝ) (o : ℝ), Measurable F →
      DependsWithin Lt (m / 4) F →
      (∀ z z', CoordsInBalls R z → CoordsInBalls R z' → |F z - F z'| ≤ o) →
      |weightedMean (chartDensity s) (fun η => F (s.coordsByIndex Y η)) -
          weightedMean (chartDensity s') (fun η => F (s'.coordsByIndex Y' η))| ≤ o * E₃)
    (hdI : Integrable (chartDensity s)) (hdI' : Integrable (chartDensity s'))
    {o : Fin 4 → ℤ} (ho : o ∈ centredCube R.params.side)
    {h : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side))}
    {h' : PlaquetteWeight (fineSide R.params.side R.depth (n' * R.params.side))}
    (hw : WeightsAgreeAt R.params.side R.depth (fineSite R.params.side Y 0 o) (fineSite R.params.side Y' 0 o) h h') :
    |chartResponse A s (fineSite R.params.side Y 0 o) h - chartResponse A s' (fineSite R.params.side Y' 0 o) h'| ≤
      (1 + chartSiteScore A s (fineSite R.params.side Y 0 o)) * E₁ * weightNorm R.params.side R.depth h := by
  have hodd : Odd R.params.side := hfit.L_odd
  have hbs : IsBlockTorusSide R.params (n * R.params.side) :=
    ⟨Dvd.intro_left _ rfl, by rw [mul_comm]; exact Nat.mul_le_mul_right _ hn⟩
  have hbs' : IsBlockTorusSide R.params (n' * R.params.side) :=
    ⟨Dvd.intro_left _ rfl, by rw [mul_comm]; exact Nat.mul_le_mul_right _ hn'⟩
  have hself := settingsAgreeNear_self hag
  obtain ⟨yy, hyy⟩ : ∃ yy, yy = fineSite R.params.side Y 0 o := ⟨_, rfl⟩
  obtain ⟨y', hy'⟩ : ∃ y', y' = fineSite R.params.side Y' 0 o := ⟨_, rfl⟩
  rw [← hyy, ← hy']
  obtain ⟨sy, hsy⟩ : ∃ sy, sy = siteScore A.score s.support s.labelling yy := ⟨_, rfl⟩
  have hsy0 : 0 ≤ sy := by rw [hsy]; exact siteScore_nonneg hsnn _ _ _
  obtain ⟨S, hS⟩ : ∃ S, S = weightNorm R.params.side R.depth h := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hS]; exact weightNorm_nonneg _ _ _
  obtain ⟨E₂, hE₂⟩ : ∃ E₂, E₂ = Real.exp (-R.params.decayRate * ((R.params.side * k - 2 * R.params.side : ℕ) : ℝ)) :=
    ⟨_, rfl⟩
  have hE₂0 : 0 ≤ E₂ := by rw [hE₂]; exact (Real.exp_pos _).le
  rw [← hE₂] at hnum
  have he0 : 0 ≤ (1 + sy) * E₂ * S := mul_nonneg (mul_nonneg (by linarith only [hsy0]) hE₂0) hS0
  have hliv : ∀ η, s.InBalls η →
      IsLiveState R.params R.coupling R.labelWeight (s.field η) s.support s.labelling := fun η hη =>
    isLiveState_chartField hrow hfit hn hs hη
  have hliv' : ∀ η, s'.InBalls η →
      IsLiveState R.params R.coupling R.labelWeight (s'.field η) s'.support s'.labelling := fun η hη =>
    isLiveState_chartField hrow hfit hn' hs' hη
  have hHm := measurable_liveHullResponse A hA hbs s yy h
  have hHm' := measurable_liveHullResponse A hA hbs' s' y' h'
  have hfm := measurable_chartField s
  have hfm' := measurable_chartField s'
  have hHb : ∀ η, s.InBalls η → |liveHullResponse A s yy h (s.field η)| ≤ (A.responseParams.C₀ + sy) * S := by
    intro η hη
    rw [liveHullResponse_eq A (hliv η hη), hsy, hS]
    exact hA.size_hull (n * R.params.side) hbs yy _ _ _ (hliv η hη) h
  have hHb' : ∀ η, s'.InBalls η → |liveHullResponse A s' y' h' (s'.field η)| ≤
      (A.responseParams.C₀ + siteScore A.score s'.support s'.labelling y') * weightNorm R.params.side R.depth h' := by
    intro η hη
    rw [liveHullResponse_eq A (hliv' η hη)]
    exact hA.size_hull (n' * R.params.side) hbs' y' _ _ _ (hliv' η hη) h'
  have hFm : Measurable fun z => liveHullResponse A s yy h (s.field (s.extendNear Y k z)) :=
    hHm.comp (hfm.comp (measurable_extendNear s Y k))
  have hFb : ∀ z, CoordsInBalls R z →
      |liveHullResponse A s yy h (s.field (s.extendNear Y k z))| ≤ (A.responseParams.C₀ + sy) * S :=
    fun z hz => hHb _ (extendNear_inBalls s Y k hρ.le hz)
  have hFr : DependsWithin Lt (m / 4) fun z => liveHullResponse A s yy h (s.field (s.extendNear Y k z)) := by
    intro z z' hzz
    show liveHullResponse A s yy h (s.field _) = liveHullResponse A s yy h (s.field _)
    rw [extendNear_congr s Y hkq (R := R) (fun q hq => hzz q (by rw [← hLq]; exact hq))]
  have hFo : ∀ z z', CoordsInBalls R z → CoordsInBalls R z' →
      |liveHullResponse A s yy h (s.field (s.extendNear Y k z)) -
          liveHullResponse A s yy h (s.field (s.extendNear Y k z'))| ≤
        2 * ((A.responseParams.C₀ + sy) * S) := by
    intro z z' hz hz'
    have h1 := hFb z hz
    have h2 := hFb z' hz'
    have h3 := abs_sub (liveHullResponse A s yy h (s.field (s.extendNear Y k z)))
      (liveHullResponse A s yy h (s.field (s.extendNear Y k z')))
    linarith only [h1, h2, h3]
  have hB := hL3 _ _ hFm hFr hFo
  have hd0 := chartDensity_nonneg s
  have hd0' := chartDensity_nonneg s'
  have hbd : ∀ η, chartDensity s η ≠ 0 → s.InBalls η := fun η hh => inBalls_of_chartDensity_ne_zero s hh
  have hbd' : ∀ η, chartDensity s' η ≠ 0 → s'.InBalls η := fun η hh => inBalls_of_chartDensity_ne_zero s' hh
  have i1 : Integrable fun η => liveHullResponse A s yy h (s.field η) * chartDensity s η :=
    integrable_mul_of_abs_le hdI hd0 (hHm.comp hfm) fun η hη => hHb η (hbd η hη)
  have i2 : Integrable fun η =>
      liveHullResponse A s yy h (s.field (s.extendNear Y k (s.coordsByIndex Y η))) * chartDensity s η :=
    integrable_mul_of_abs_le hdI hd0 (hFm.comp (measurable_coordsByIndex s Y)) fun η hη =>
      hFb _ (coordsInBalls_coordsByIndex s Y hρ.le (hbd η hη))
  have i3 : Integrable fun η =>
      liveHullResponse A s yy h (s.field (s.extendNear Y k (s'.coordsByIndex Y' η))) * chartDensity s' η :=
    integrable_mul_of_abs_le hdI' hd0' (hFm.comp (measurable_coordsByIndex s' Y')) fun η hη =>
      hFb _ (coordsInBalls_coordsByIndex s' Y' hρ.le (hbd' η hη))
  have i4 : Integrable fun η => liveHullResponse A s' y' h' (s'.field η) * chartDensity s' η :=
    integrable_mul_of_abs_le hdI' hd0' (hHm'.comp hfm') fun η hη => hHb' η (hbd' η hη)
  have c1 : ∀ η, chartDensity s η ≠ 0 →
      |liveHullResponse A s yy h (s.field η) -
          liveHullResponse A s yy h (s.field (s.extendNear Y k (s.coordsByIndex Y η)))| ≤
        (1 + sy) * E₂ * S := by
    intro η hη
    have hb := hbd η hη
    have hz := extendNear_inBalls s Y k hρ.le (coordsInBalls_coordsByIndex s Y hρ.le hb)
    have hnr := coordsAgreeNear_extendNear hodd hself hkm η
    have := abs_centeredHullResponse_sub_le A hrow hfit hA hn hn hs hs hself hk2 hkm hW₂ hnr hz hb ho
      (h := h) (h' := h) (fun _ _ _ _ _ => rfl)
    rw [liveHullResponse_eq A (hliv _ hb), liveHullResponse_eq A (hliv _ hz), abs_sub_comm, hyy, hsy, hE₂, hS, hyy]
    exact this
  have c2 : ∀ η, chartDensity s' η ≠ 0 →
      |liveHullResponse A s yy h (s.field (s.extendNear Y k (s'.coordsByIndex Y' η))) -
          liveHullResponse A s' y' h' (s'.field η)| ≤
        (1 + sy) * E₂ * S := by
    intro η hη
    have hb := hbd' η hη
    have hz := extendNear_inBalls s Y k hρ.le (coordsInBalls_coordsByIndex s' Y' hρ.le hb)
    have hnr := coordsAgreeNear_extendNear hodd hag hkm η
    have := abs_centeredHullResponse_sub_le A hrow hfit hA hn hn' hs hs' hag hk2 hkm hW₂ hnr hz hb ho hw
    rw [liveHullResponse_eq A (hliv _ hz), liveHullResponse_eq A (hliv' _ hb), hyy, hy', hsy, hE₂, hS, hyy]
    exact this
  have q1 : chartResponse A s yy h =
      weightedMean (chartDensity s) fun η => liveHullResponse A s yy h (s.field η) :=
    weightedMean_congr fun η hη => (liveHullResponse_eq A (hliv _ (hbd η hη))).symm
  have q2 : chartResponse A s' y' h' =
      weightedMean (chartDensity s') fun η => liveHullResponse A s' y' h' (s'.field η) :=
    weightedMean_congr fun η hη => (liveHullResponse_eq A (hliv' _ (hbd' η hη))).symm
  rw [q1, q2]
  have hfin := weighted_error_bound hK1 hsy0 hS0 hE₃ hnum
  have hmain := abs_weightedMean_sub_of_chain hd0 hd0' he0 i1 i2 i3 i4 c1 c2 hB
  have hgoal : (1 + chartSiteScore A s yy) * E₁ * weightNorm R.params.side R.depth h = (1 + sy) * S * E₁ := by
    rw [hsy, hS]
    show (1 + siteScore A.score s.support s.labelling yy) * E₁ * _ = _
    ring
  rw [hgoal]
  exact hmain.trans (by linarith only [hfin])
set_option maxHeartbeats 1000000 in
private theorem abs_chartBondScore_sub_le (hsc : BondScoresAgreeNearBlocks) (hsb : BondScoreProperties)
    (hfit : R.params.Admissible) (hJ : 11 * 2 ^ 12 * R.params.baseDepth < R.params.side) (h16 : 16 ≤ n)
    (h16' : 16 ≤ n') {s : ChartSetting R n} {s' : ChartSetting R n'} {Y : TorusSite n} {Y' : TorusSite n'}
    {m k Lt : ℕ} (hs : s.IsAdmissible) (hag : SettingsAgreeNear s s' Y Y' m) (hk4 : 4 ≤ k) (hkm : k ≤ m)
    (hkq : k ≤ m / 4) (hLq : R.params.side = Lt) {E₃ : ℝ}
    (hL3 : ∀ (F : (NearBondIndex → EuclideanSpace ℝ (Fin 3)) → ℝ) (o : ℝ), Measurable F →
      DependsWithin Lt (m / 4) F →
      (∀ z z', CoordsInBalls R z → CoordsInBalls R z' → |F z - F z'| ≤ o) →
      |weightedMean (chartDensity s) (fun η => F (s.coordsByIndex Y η)) -
          weightedMean (chartDensity s') (fun η => F (s'.coordsByIndex Y' η))| ≤ o * E₃)
    {c : (Fin 4 → ℤ) × Fin 4} (hc : IsBondAtOrigin c) :
    |chartBondScore s (bondFrom Y c) - chartBondScore s' (bondFrom Y' c)| ≤ 4 * E₃ := by
  have hodd : Odd R.params.side := hfit.L_odd
  have hself := settingsAgreeNear_self hag
  have hbox1 : OffsetInBox 1 c.1 := by
    intro l
    rcases hc with e | e <;> rw [e]
    · simp
    · by_cases hl : l = c.2
      · subst hl
        simp
      · simp [hl]
  have hbox2 : OffsetInBox 1 (c.1 + Pi.single c.2 1) := by
    intro l
    rcases hc with e | e <;> rw [e]
    · by_cases hl : l = c.2
      · subst hl
        simp
      · simp [hl]
    · simp
  have hsbs := hsb R.params hfit R.coupling n s.bases (bondFrom Y c)
  have hFm : Measurable fun z =>
      bondScore R.params R.coupling (s.field (s.extendNear Y k z)) s.coarse s.bases (bondFrom Y c) := by
    have h1 := hsbs.2.2.2.2
    have h2 : Measurable fun z : NearBondIndex → EuclideanSpace ℝ (Fin 3) =>
        ((s.field (s.extendNear Y k z), s.coarse) : TorusField (n * R.params.side) × TorusField n) :=
      ((measurable_chartField s).comp (measurable_extendNear s Y k)).prodMk measurable_const
    have h3 := Measurable.comp h1 h2
    exact h3
  have hFr : DependsWithin Lt (m / 4) fun z =>
      bondScore R.params R.coupling (s.field (s.extendNear Y k z)) s.coarse s.bases (bondFrom Y c) := by
    intro z z' hzz
    show bondScore R.params R.coupling (s.field _) s.coarse s.bases (bondFrom Y c) =
      bondScore R.params R.coupling (s.field _) s.coarse s.bases (bondFrom Y c)
    rw [extendNear_congr s Y hkq (R := R) (fun q hq => hzz q (by rw [← hLq]; exact hq))]
  have hFo : ∀ z z', CoordsInBalls R z → CoordsInBalls R z' →
      |bondScore R.params R.coupling (s.field (s.extendNear Y k z)) s.coarse s.bases (bondFrom Y c) -
        bondScore R.params R.coupling (s.field (s.extendNear Y k z')) s.coarse s.bases (bondFrom Y c)| ≤ 4 := by
    intro z z' _ _
    have h1 := hsbs.2.2.1 (s.field (s.extendNear Y k z)) s.coarse
    have h2 := hsbs.2.2.1 (s.field (s.extendNear Y k z')) s.coarse
    have h3 := abs_sub (bondScore R.params R.coupling (s.field (s.extendNear Y k z)) s.coarse s.bases (bondFrom Y c))
      (bondScore R.params R.coupling (s.field (s.extendNear Y k z')) s.coarse s.bases (bondFrom Y c))
    linarith only [h1, h2, h3]
  have hB := hL3 _ _ hFm hFr hFo
  have e1 : (fun η => bondScore R.params R.coupling (s.field η) s.coarse s.bases (bondFrom Y c)) =
      fun η => bondScore R.params R.coupling (s.field (s.extendNear Y k (s.coordsByIndex Y η))) s.coarse s.bases
        (bondFrom Y c) := by
    funext η
    exact (hsc R n n s s Y Y m k _ η c.1 c.2 hfit hJ h16 h16 hs.subset_chart hself hk4 hkm
      (coordsAgreeNear_extendNear hodd hself hkm η) hbox1 hbox2).symm
  have e2 : (fun η => bondScore R.params R.coupling (s'.field η) s'.coarse s'.bases (bondFrom Y' c)) =
      fun η => bondScore R.params R.coupling (s.field (s.extendNear Y k (s'.coordsByIndex Y' η))) s.coarse s.bases
        (bondFrom Y c) := by
    funext η
    exact (hsc R n n' s s' Y Y' m k _ η c.1 c.2 hfit hJ h16 h16' hs.subset_chart hag hk4 hkm
      (coordsAgreeNear_extendNear hodd hag hkm η) hbox1 hbox2).symm
  unfold chartBondScore
  rw [e1, e2]
  exact hB
end Parts
theorem chartResponseComparison_holds (h3 : LocalMeansClose) (hfr : _root_.YangMills.Construction.FrameLocality.FrameCoordLocal)
    (hfl : _root_.YangMills.Construction.StepFloors.EventuallyFloorConditions) (hms : SettingMassEqIntegral) (hsc : BondScoresAgreeNearBlocks)
    (hsb : BondScoreProperties) : ChartResponseComparison := by
  obtain ⟨r₁, p₁, g₁⟩ := h3
  obtain ⟨r₂, p₂, g₂⟩ := hms
  refine ⟨fun c => min (r₁ c) (r₂ c), fun c => lt_min (p₁ c) (p₂ c), fun T hD hrt K => ?_⟩
  obtain ⟨y₁, L3⟩ := g₁ T hD (hrt.trans (min_le_left _ _))
  obtain ⟨y₂, Ms⟩ := g₂ T hD (hrt.trans (min_le_right _ _))
  have hrtpos := hD.rt_pos
  have hL40 : (2 : ℝ) ^ 40 ≤ T.side := by exact_mod_cast hD.L_ge
  have hL0 : (0 : ℝ) < T.side := by linarith [show (0 : ℝ) < 2 ^ 40 by positivity]
  set Cc : ℝ := |K.C₀| + 4 with hCc
  have hCc4 : 4 ≤ Cc := by
    have := abs_nonneg K.C₀
    linarith
  have hCcK : K.C₀ ≤ Cc := by
    have := le_abs_self K.C₀
    linarith
  set C₀ : ℝ := 2 ^ 21 * T.side + 4 * T.n₀ + 2 ^ 17 + 2 + 2 ^ 7 * T.side * (2 + 2 * Cc) / T.rt with hC₀
  have hbigpos : 0 ≤ 2 ^ 7 * (T.side : ℝ) * (2 + 2 * Cc) / T.rt := by positivity
  have hC₀pos : 0 < C₀ := by positivity
  obtain ⟨yF, hF⟩ := hfl T hD C₀ 1 hC₀pos one_pos
  refine ⟨max (max T.floorMin (max y₁ y₂)) (max yF 1), fun y hy R A hK hAt => ?_⟩
  have hy0 : T.floorMin ≤ y := (le_max_left _ _).trans ((le_max_left _ _).trans hy)
  have hyL : y₁ ≤ y := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hy))
  have hyM : y₂ ≤ y := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hy))
  have hyF : yF ≤ y := (le_max_left _ _).trans ((le_max_right _ _).trans hy)
  have hy1 : (1 : ℝ) ≤ y := (le_max_right _ _).trans ((le_max_right _ _).trans hy)
  have hR := hAt.onFamily
  have hxy := hR.le_coupling
  have hfit : R.params.Admissible := hR.params_eq ▸ hD.fits y hy0
  have hodd : Odd R.params.side := hfit.L_odd
  have hLq : R.params.side = T.side := by rw [hR.params_eq]; rfl
  have hn₀q : R.params.n₀ = T.n₀ := by rw [hR.params_eq]; rfl
  have hrtq : R.params.rt = T.rt := by rw [hR.params_eq]; rfl
  have hσq : R.params.threshold = T.threshold := by rw [hR.params_eq]; rfl
  have hJq : R.params.baseDepth = T.baseDepth := by rw [hR.params_eq]; rfl
  have hρ : 0 < R.ballRadius := by
    have := hfit.σ_pos
    unfold StepSetup.ballRadius
    positivity
  have hrow : R.HasExpansions := hR.isStep.1
  have hFl := hF R.coupling (hyF.trans hxy)
  have hrC : C₀ ≤ R.range := hFl.range_ge
  have hr2 : (2 : ℝ) ^ 21 * T.side ≤ R.range := by
    have h1 : 0 ≤ 4 * (T.n₀ : ℝ) := by positivity
    have h2 : (0 : ℝ) ≤ 2 ^ 17 := by positivity
    linarith
  have hr3 : 2 ^ 7 * (T.side : ℝ) * (2 + 2 * Cc) / T.rt ≤ R.range := by
    have h1 : 0 ≤ 4 * (T.n₀ : ℝ) := by positivity
    have h2 : (0 : ℝ) ≤ 2 ^ 17 := by positivity
    have h3 : 0 ≤ 2 ^ 21 * (T.side : ℝ) := by positivity
    linarith
  have hAr := hAt.admissible
  have hrowA := hAr.bounds
  have hKf := hAr.params_admissible
  have hC₀eq := hKf.C₀_eq
  have hN₀ := hKf.N₀_nonneg
  have hKc := hKf.Kc_ge
  have ha1 := hfit.a_ge
  have hAK : A.responseParams.C₀ = K.C₀ := by rw [hK]
  have hK1 : 1 ≤ A.responseParams.C₀ := by
    rw [hC₀eq]
    linarith
  have hKC : A.responseParams.C₀ ≤ Cc := by rw [hAK]; exact hCcK
  have hsnn : ∀ w, 0 ≤ A.score w := hAr.price.nonneg
  have hLr : (R.params.side : ℝ) = T.side := by exact_mod_cast hLq
  refine ⟨?_, ?_⟩
  · intro n _ s hn hs y h
    have hL : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
    have hbs : IsBlockTorusSide R.params (n * R.params.side) :=
      ⟨Dvd.intro_left _ rfl, by rw [mul_comm]; exact Nat.mul_le_mul_right _ hn⟩
    refine abs_weightedMean_le (chartDensity_nonneg s)
      (mul_nonneg (add_nonneg (by linarith) (siteScore_nonneg hsnn _ _ _)) (weightNorm_nonneg _ _ _))
      fun η hη => ?_
    exact hrowA.size_hull (n * R.params.side) hbs y _ _ _
      (isLiveState_chartField hrow hfit hn hs (inBalls_of_chartDensity_ne_zero s hη)) h
  · intro n n' _ _ s s' Y Y' m hn hn' hs hs'
    have hnT : T.n₀ ≤ n := by rw [← hn₀q]; exact hn
    have hnT' : T.n₀ ≤ n' := by rw [← hn₀q]; exact hn'
    have hbs : IsBlockTorusSide R.params (n * R.params.side) :=
      ⟨Dvd.intro_left _ rfl, by rw [mul_comm]; exact Nat.mul_le_mul_right _ hn⟩
    have hbs' : IsBlockTorusSide R.params (n' * R.params.side) :=
      ⟨Dvd.intro_left _ rfl, by rw [mul_comm]; exact Nat.mul_le_mul_right _ hn'⟩
    obtain ⟨hdI, -, -⟩ := Ms y hyM R hR n hnT s hs
    obtain ⟨hdI', -, -⟩ := Ms y hyM R hR n' hnT' s' hs'
    have hn16 : 16 ≤ n := by
      have := hfit.n₀_ge
      omega
    have hn16' : 16 ≤ n' := by
      have := hfit.n₀_ge
      omega
    have hJ : 11 * 2 ^ 12 * R.params.baseDepth < R.params.side := by
      rw [hJq, hLq]
      exact hD.L_gt
    have key : ∀ m : ℕ, (R.range : ℝ) / (4 * R.params.side) ≤ m → SettingsAgreeNear s s' Y Y' m →
        (∀ (o : Fin 4 → ℤ), o ∈ centredCube R.params.side →
          ∀ (h : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side)))
          (h' : PlaquetteWeight (fineSide R.params.side R.depth (n' * R.params.side))),
          WeightsAgreeAt R.params.side R.depth (fineSite R.params.side Y 0 o) (fineSite R.params.side Y' 0 o) h h' →
          |chartResponse A s (fineSite R.params.side Y 0 o) h -
              chartResponse A s' (fineSite R.params.side Y' 0 o) h'| ≤
            (1 + chartSiteScore A s (fineSite R.params.side Y 0 o)) * Real.exp (-(R.params.rt * m / 2 ^ 5)) *
              weightNorm R.params.side R.depth h) ∧
        ∀ c : (Fin 4 → ℤ) × Fin 4, IsBondAtOrigin c →
          |chartBondScore s (bondFrom Y c) - chartBondScore s' (bondFrom Y' c)| ≤
            Real.exp (-(R.params.rt * m / 2 ^ 5)) := by
      intro m hrm hag
      have hrmT : (R.range : ℝ) / (4 * T.side) ≤ m := by rwa [hLr] at hrm
      obtain ⟨k, hkdef⟩ : ∃ k, k = m / 8 := ⟨_, rfl⟩
      have hk8 : m ≤ 8 * k + 7 := by omega
      have hk8R : (m : ℝ) ≤ 8 * k + 7 := by exact_mod_cast hk8
      obtain ⟨hMbig, hW₂', hf', hbigm⟩ := radius_bounds hL40 hrtpos hr2 hr3 hrmT hk8R
      have hmN : 2 ^ 19 ≤ m := by exact_mod_cast hMbig
      have hk4 : 4 ≤ k := by omega
      have hkm : k ≤ m := by omega
      have hkq : k ≤ m / 4 := by omega
      have hLk2 : 2 * R.params.side ≤ R.params.side * k := by
        rw [mul_comm 2]
        exact Nat.mul_le_mul_left _ (by omega)
      have hW₂cast : ((R.params.side * k - 2 * R.params.side : ℕ) : ℝ) = T.side * k - 2 * T.side := by
        rw [Nat.cast_sub hLk2, hLq]
        push_cast
        ring
      have hW₂ : (R.range : ℝ) / 64 ≤ ((R.params.side * k - 2 * R.params.side : ℕ) : ℝ) := by
        rw [hW₂cast]
        exact hW₂'
      have hfo : R.params.decayRate = T.rt / 2 ^ 12 := by
        unfold _root_.YangMills.Construction.TorusLumps.StepParameters.decayRate
        rw [hrtq]
      have hf : T.rt * m / 16 ≤ R.params.decayRate * ((R.params.side * k - 2 * R.params.side : ℕ) : ℝ) := by
        rw [hfo, hW₂cast]
        exact hf'
      have hnum : ∀ C : ℝ, 0 ≤ C → C ≤ Cc →
          2 * Real.exp (-R.params.decayRate * ((R.params.side * k - 2 * R.params.side : ℕ) : ℝ)) +
            2 * C * Real.exp (-(T.rt * m / 2 ^ 3)) ≤ Real.exp (-(T.rt * m / 2 ^ 5)) := by
        intro C h0 h1
        exact exp_bound_two_charts hrtpos h0 hf (by linarith only [h1, hbigm])
      have hL3 : ∀ (F : (NearBondIndex → EuclideanSpace ℝ (Fin 3)) → ℝ) (o : ℝ), Measurable F →
          DependsWithin T.side (m / 4) F →
          (∀ z z', CoordsInBalls R z → CoordsInBalls R z' → |F z - F z'| ≤ o) →
          |weightedMean (chartDensity s) (fun η => F (s.coordsByIndex Y η)) -
              weightedMean (chartDensity s') (fun η => F (s'.coordsByIndex Y' η))| ≤
            o * Real.exp (-(T.rt * m / 2 ^ 3)) := by
        intro F o hFm hFr hFo
        have h2 := L3 y hyL R hR n n' hnT hnT' s s' Y Y' m hs hs' hag
          hrmT _ _ (AlikePotentials.part_potential 1 zero_le_one le_rfl) F _ hFm hFr hFo
        rwa [lawDensity_partPotential_one, lawDensity_partPotential_one] at h2
      rw [hrtq]
      refine ⟨fun o ho h h' hw => ?_, fun c hc => ?_⟩
      · exact abs_chartResponse_sub_le A hrow hfit hrowA hn hn' hρ hsnn hK1 hs hs' hag (by omega) hkm hkq hLq
          hW₂ (Real.exp_pos _) (hnum A.responseParams.C₀ (by linarith only [hK1]) hKC) hL3 hdI hdI' ho hw
      · have h4 := abs_chartBondScore_sub_le hsc hsb hfit hJ hn16 hn16' hs hag hk4 hkm hkq hLq hL3 hc
        have hnm := hnum 2 (by norm_num) (by linarith only [hCc4])
        have hE₂0 := Real.exp_pos (-R.params.decayRate * ((R.params.side * k - 2 * R.params.side : ℕ) : ℝ))
        linarith only [h4, hnm, hE₂0]
    refine ⟨fun hag hrm => key m hrm hag, fun hoff hm₀ => ?_⟩
    have hm0le : R.frameReach ≤ m := by omega
    obtain ⟨m', hm'⟩ : ∃ m', m' = m - R.frameReach := ⟨_, rfl⟩
    have hm'm : m' ≤ m := by omega
    have hcast : (m' : ℝ) = (m : ℝ) - R.frameReach := by
      rw [hm', Nat.cast_sub hm0le]
    have hrlarge : 2 ^ 11 ≤ R.range := by
      have hb : (2 : ℝ) ^ 11 ≤ R.range := by nlinarith only [hr2, hL40]
      exact_mod_cast hb
    have hm₀pos : 0 < R.frameReach := by
      unfold StepSetup.frameReach
      exact Nat.div_pos hrlarge (by norm_num)
    have hside : 4 * R.frameReach + 5 < n := by have := hoff.lt_extent; omega
    have hside' : 4 * R.frameReach + 5 < n' := by have := hoff.lt_extent'; omega
    have hag' : SettingsAgreeNear s s' Y Y' m' := by
      refine ⟨by have := hoff.lt_extent; omega, by have := hoff.lt_extent'; omega, ?_,
        fun q hq => hoff.free_iff q (isNearIndex_mono hq hm'm),
        fun q hq => hoff.fine_eq q (isNearIndex_mono hq hm'm), ?_,
        fun h o hh ho => hoff.support_iff h o (fun i => (hh i).trans (by exact_mod_cast hm'm)) ho,
        fun h o hz hz' hh ho => hoff.labelling_eq h o hz hz' (fun i => (hh i).trans (by exact_mod_cast hm'm)) ho,
        fun h hh => hoff.bases_match h (fun i => (hh i).trans (by exact_mod_cast hm'm))⟩
      · intro b hb
        exact hoff.coarse_agree b ⟨fun i => (hb.1 i).trans (by exact_mod_cast hm'm),
          fun i => (hb.2 i).trans (by exact_mod_cast hm'm)⟩
      · rintro ⟨h, o, i⟩ hq _
        have ho : o ∈ centredCube R.params.side := hq.2
        have hoff₁ := cellOffset_torusFrame_blockPoint (L := R.params.side) (n := n) R.depth hodd
          (fun i => ((Y i).cast : ℤ) + h i) o ho
        have hoff₂ := cellOffset_torusFrame_blockPoint (L := R.params.side) (n := n') R.depth hodd
          (fun i => ((Y' i).cast : ℤ) + h i) o ho
        refine hfr R.params R.anchorRadius R.depth R.frameReach n n' s.coarse s'.coarse _ _ hfit hm₀pos hside hside'
          rfl (hoff₁.trans hoff₂.symm) ?_
        show FieldsAgreeNear s.coarse s'.coarse (parentBlock R.params.side (fineSite R.params.side Y h o))
          (parentBlock R.params.side (fineSite R.params.side Y' h o)) R.frameReach
        rw [parentBlock_fineSite hodd Y h o ho, parentBlock_fineSite hodd Y' h o ho]
        intro b hb
        have hbox : BondOffsetInBox m (h + b.1, b.2) := by
          constructor
          · intro i
            have h1 : |h i| ≤ (m' : ℤ) := hq.1 i
            have h2 : |b.1 i| ≤ (R.frameReach : ℤ) := hb.1 i
            have : ((m' : ℤ) + R.frameReach) ≤ m := by omega
            show |h i + b.1 i| ≤ (m : ℤ)
            rw [abs_le] at h1 h2 ⊢
            constructor <;> omega
          · intro i
            have h1 : |h i| ≤ (m' : ℤ) := hq.1 i
            have h2 : |(b.1 + Pi.single b.2 1 : Fin 4 → ℤ) i| ≤ (R.frameReach : ℤ) := hb.2 i
            have : ((m' : ℤ) + R.frameReach) ≤ m := by omega
            have e : ((h + b.1) + Pi.single b.2 1 : Fin 4 → ℤ) i =
                h i + (b.1 + Pi.single b.2 1 : Fin 4 → ℤ) i := by
              simp only [Pi.add_apply]
              ring
            show |((h + b.1) + Pi.single b.2 1 : Fin 4 → ℤ) i| ≤ (m : ℤ)
            rw [e]
            rw [abs_le] at h1 h2 ⊢
            constructor <;> omega
        have hh := hoff.coarse_agree (h + b.1, b.2) hbox
        have e1 : ∀ (N : ℕ) [NeZero N] (Z : TorusSite N), (bondFrom (Z + siteOfInt h) b).1 = (bondFrom Z (h + b.1, b.2)).1 := by
          intro N _ Z
          simp only [bondFrom]
          rw [add_assoc, ← TorusFields.siteOfInt_add]
        show s.coarse (bondFrom (Y + siteOfInt h) b).1 b.2 = s'.coarse (bondFrom (Y' + siteOfInt h) b).1 b.2
        rw [e1, e1]
        exact hh
    have hm₀R : (R.range : ℝ) / 2 ^ 11 - 1 ≤ R.frameReach := by
      have h1 : R.range < 2 ^ 11 * (R.frameReach + 1) := by
        unfold StepSetup.frameReach
        have := Nat.lt_mul_div_succ R.range (show 0 < 2 ^ 11 by norm_num)
        simpa using this
      have h2 : (R.range : ℝ) < 2 ^ 11 * ((R.frameReach : ℝ) + 1) := by exact_mod_cast h1
      have : (R.range : ℝ) / 2 ^ 11 < (R.frameReach : ℝ) + 1 := by
        rw [div_lt_iff₀ (by norm_num)]
        linarith
      linarith
    have hm₀m : (16 : ℝ) * R.frameReach ≤ m := by exact_mod_cast hm₀
    have hrm' : (R.range : ℝ) / (4 * R.params.side) ≤ m' := by
      rw [hcast, hLr, div_le_iff₀ (by positivity)]
      have hr0 : (0 : ℝ) ≤ R.range := by positivity
      have h15 : 15 * (R.frameReach : ℝ) ≤ (m : ℝ) - R.frameReach := by linarith
      have h1 : (2 : ℝ) ^ 21 * T.side ≤ R.range := hr2
      have h2 : (R.range : ℝ) ≤ ((m : ℝ) - R.frameReach) * (4 * T.side) := by
        have h3 : 15 * ((R.range : ℝ) / 2 ^ 11 - 1) ≤ (m : ℝ) - R.frameReach := by linarith
        have h4 : (R.range : ℝ) / 2 ^ 12 ≤ 15 * ((R.range : ℝ) / 2 ^ 11 - 1) := by
          have : (2 : ℝ) ^ 21 ≤ R.range := by nlinarith only [hr2, hL40]
          linarith only [this]
        have h5 : (R.range : ℝ) / 2 ^ 12 ≤ (m : ℝ) - R.frameReach := h4.trans h3
        have h6 : (R.range : ℝ) / 2 ^ 12 * (4 * T.side) ≤ ((m : ℝ) - R.frameReach) * (4 * T.side) :=
          mul_le_mul_of_nonneg_right h5 (by positivity)
        have h7 : (R.range : ℝ) ≤ (R.range : ℝ) / 2 ^ 12 * (4 * T.side) := by nlinarith only [hL40, hr0]
        linarith
      linarith
    obtain ⟨k₁, k₂⟩ := key m' hrm' hag'
    have hexp : Real.exp (-(R.params.rt * m' / 2 ^ 5)) ≤ Real.exp (-(15 / 16 * R.params.rt * m / 2 ^ 5)) := by
      apply Real.exp_le_exp.mpr
      have h15 : 15 / 16 * (m : ℝ) ≤ m' := by rw [hcast]; linarith
      have hrr : 0 ≤ R.params.rt := by rw [hrtq]; exact hrtpos.le
      have h2 := mul_le_mul_of_nonneg_left h15 hrr
      have e : 15 / 16 * R.params.rt * (m : ℝ) / 2 ^ 5 = R.params.rt * (15 / 16 * (m : ℝ)) / 2 ^ 5 := by ring
      rw [e]
      have h3 : R.params.rt * (15 / 16 * (m : ℝ)) / 2 ^ 5 ≤ R.params.rt * (m' : ℝ) / 2 ^ 5 :=
        div_le_div_of_nonneg_right h2 (by norm_num)
      linarith
    refine ⟨fun o ho h h' hw => (k₁ o ho h h' hw).trans ?_, fun c hc => (k₂ c hc).trans hexp⟩
    have hsy0 : 0 ≤ chartSiteScore A s (fineSite R.params.side Y 0 o) := siteScore_nonneg hsnn _ _ _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp (by linarith)) (weightNorm_nonneg _ _ _)
end YangMills.Construction.WeightedResponses
end
