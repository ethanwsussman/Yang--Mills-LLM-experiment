import YangMills.Construction.ClusterExpansionOfAStep.ColdGroundOfTheFlatField
import YangMills.Construction.ClusterExpansionOfAStep.DeepDensitiesAgainstTheCutProof
import YangMills.Construction.ClusterExpansionOfAStep.FactorsOfAnAttachedUnion
import YangMills.Construction.ClusterExpansionOfAStep.HotGroundIsOfItsStateProof
import YangMills.Construction.ClusterExpansionOfAStep.HullStatesAreGrounds
import YangMills.Construction.ClusterExpansionOfAStep.ImageStateIsAGas
import YangMills.Construction.ClusterExpansionOfAStep.IntegralNearAClassIsBounded
import YangMills.Construction.ClusterExpansionOfAStep.NearPotentialAgainstTheCostProof
import YangMills.Construction.ClusterExpansionOfAStep.PriceOfAClassBeforeItsLength
import YangMills.Construction.ClusterExpansionOfAStep.SharesUnderASettingAreBounded
import YangMills.Construction.ClusterExpansionOfAStep.StatesOfASlice
import YangMills.Construction.ClusterExpansionOfAStep.SumOfTheDensitiesNearAClass
import YangMills.Construction.ClusterExpansionOfAStep.SumOfTheGasDensities
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
open TorusFields TorusLumps StepSettings StepGas RenormalizationStepParameters ImageDensities SliceStates SlicedLabels StepCosts
namespace ComponentPrice
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem coordNorm_zero : coordNorm (0 : EuclideanSpace ℝ (Fin 3)) = 0 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.DeepCutoff.coordNorm_zero <;> assumption
theorem liePointBallVolume_pos {ρ : ℝ} (hρ : 0 < ρ) : 0 < liePointBallVolume ρ := by
  unfold liePointBallVolume
  exact ENNReal.toReal_pos (Metric.measure_ball_pos volume _ hρ).ne' measure_ball_lt_top.ne
theorem sum_blockActivity_near_le (s : ChartSetting R n) (N : Finset (TorusSite n)) (hρ : 0 < R.ballRadius)
    (hp : ColdStepAtMirrorFrames.IsCutoff R.ballRadius R.barrierFn) (hint : LocalIntegralLeBallVolume)
    (S Bi Bp Be Sφ A Lk : ℝ) (hpos : 0 < s.localIntegral N)
    (hI : S ≤ Real.log (s.localIntegral N) + Bi)
    (hP : ∀ η : FreeCoords s.free, s.InBalls η →
      -(s.localPotential N fun b => η b.1) ≤ -(R.coupling * s.energyNear N η) + Sφ + Bp)
    (hE : ∀ η : FreeCoords s.free, s.InBalls η →
      R.coupling * A - Be ≤ R.coupling * (s.energyNear N η + Lk)) :
    S ≤ Bi + ((s.freeNear N).card : ℝ) * |Real.log (liePointBallVolume R.ballRadius)| + Sφ + Bp + Be -
      R.coupling * A + R.coupling * Lk := by
  set m : ℝ := -(R.coupling * A) + Be + R.coupling * Lk + Sφ + Bp with hm
  have hU : ∀ ζ : s.freeNear N → EuclideanSpace ℝ (Fin 3), (∀ b, coordNorm (ζ b) < R.ballRadius) →
      -(s.localPotential N ζ) ≤ m := by
    intro ζ hζ
    have hin : s.InBalls (s.extendByZero N ζ) := by
      intro b
      unfold ChartSetting.extendByZero
      by_cases hb : b ∈ s.freeNear N
      · simp only [hb, dite_true]
        exact (hζ _).le
      · simp only [hb, dite_false]
        rw [coordNorm_zero]
        exact hρ.le
    have heq : (fun b : s.freeNear N => s.extendByZero N ζ b.1) = ζ := by
      funext b
      unfold ChartSetting.extendByZero
      simp
    have h1 := hP _ hin
    have h2 := hE _ hin
    rw [heq] at h1
    rw [hm]
    nlinarith
  have hB := hint R n s N m hρ hp hU
  have hV := liePointBallVolume_pos hρ
  have hlog : Real.log (s.localIntegral N) ≤
      ((s.freeNear N).card : ℝ) * Real.log (liePointBallVolume R.ballRadius) + m := by
    have h3 := Real.log_le_log hpos hB
    rw [Real.log_mul (pow_pos hV _).ne' (Real.exp_pos _).ne', Real.log_pow, Real.log_exp] at h3
    exact h3
  have habs : ((s.freeNear N).card : ℝ) * Real.log (liePointBallVolume R.ballRadius) ≤
      ((s.freeNear N).card : ℝ) * |Real.log (liePointBallVolume R.ballRadius)| :=
    mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
  rw [hm] at hlog
  linarith
theorem sum_near_le_of_bounds {ι : Type} [DecidableEq ι] (Near N : Finset ι) (hsub : N ⊆ Near)
    (ζ g a ζ₁ g₁ : ι → ℝ) (x x' Bm A c : ℝ) (hx' : |x' - x| ≤ Bm)
    (hg : ∀ z, g z ≤ 1) (hg₁ : ∀ z, 0 ≤ g₁ z) (hz₁ : ∀ z, |ζ₁ z| ≤ c)
    (ha : ∀ z, 0 ≤ a z ∧ a z ≤ A) (hoff : ∀ z ∈ Near \ N, |ζ z + x * a z| ≤ c) :
    ∑ z ∈ Near, (ζ z + g z + x' * a z - (ζ₁ z + g₁ z)) ≤
      ∑ z ∈ N, ζ z + x * ∑ z ∈ N, a z + (Near.card : ℝ) * (1 + Bm * A + 2 * c) := by
  have hbm : 0 ≤ Bm := (abs_nonneg _).trans hx'
  have key : ∀ z, x' * a z ≤ x * a z + Bm * A := by
    intro z
    obtain ⟨h0, h1⟩ := ha z
    have h2 : (x' - x) * a z ≤ Bm * A := by
      have h3 := (abs_le.mp hx').2
      have : (x' - x) * a z ≤ Bm * a z := mul_le_mul_of_nonneg_right h3 h0
      exact this.trans (mul_le_mul_of_nonneg_left h1 hbm)
    linarith
  have hN : ∀ z ∈ N, ζ z + g z + x' * a z - (ζ₁ z + g₁ z) ≤ ζ z + x * a z + (1 + Bm * A + 2 * c) := by
    intro z _
    have h1 := hg z
    have h2 := hg₁ z
    have h3 := (abs_le.mp (hz₁ z)).1
    have h4 := key z
    have h5 : 0 ≤ c := (abs_nonneg _).trans (hz₁ z)
    linarith
  have hO : ∀ z ∈ Near \ N, ζ z + g z + x' * a z - (ζ₁ z + g₁ z) ≤ 1 + Bm * A + 2 * c := by
    intro z hz
    have h1 := hg z
    have h2 := hg₁ z
    have h3 := (abs_le.mp (hz₁ z)).1
    have h4 := key z
    have h5 := (abs_le.mp (hoff z hz)).2
    linarith
  rw [← Finset.sum_sdiff hsub]
  have s1 := Finset.sum_le_sum hN
  have s2 := Finset.sum_le_sum hO
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at s1 s2
  have hcard : ((Near \ N).card : ℝ) + (N.card : ℝ) = (Near.card : ℝ) := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hsub
  rw [← hcard, add_mul]
  linarith
def NearDensityBound (R : StepSetup) (lam cE ClassCost : ℝ) : Prop :=
  ∀ (n : ℕ) [NeZero n], IsBlockTorusSide R.params n → ∀ (V : TorusField n) (q : CoarseState R n)
    (P : Finset (Finset (TorusSite n))),
    IsHullState R.params R.nextRange V q.1 → (∀ X ∈ chainComponents R.nextRange q.1, coarseFactor V q X ≠ 0) →
    P ⊆ chainComponents R.nextRange q.1 →
    ∑ z ∈ nearSites R.nextRange (P.biUnion id), groundDensity R (hotCaseGround R V q) lam z ≤
      ∑ w ∈ nearSites R.range (componentsWithin R.params.side R.range (hotCaseGround R V q).groundSetting.support
          (attachedInBlocks R.params.side R.range (hotCaseGround R V q).recordedBad
            (hotCaseGround R V q).groundSetting.support (hotCoreSites R V) (P.biUnion id))),
        R.siteDensity (n * R.params.side) w (hotCaseGround R V q).groundSetting.fine
          (hotCaseGround R V q).groundSetting.support (hotCaseGround R V q).groundSetting.labelling -
      R.coupling * (6 * R.params.κ * R.params.threshold ^ 2 *
          ((open Classical in (torusHotLumps R.params V).filter (· ⊆ P.biUnion id)).card : ℝ) +
        R.params.κ / 4 * R.params.threshold ^ 2 * (hotLumpsInAttached R.params R.range
          (hotCaseGround R V q).groundSetting.fine (hotCaseGround R V q).recordedBad
          (hotCaseGround R V q).groundSetting.support (hotCoreSites R V) (P.biUnion id) : ℝ) +
        cE * (badBlocksInAttached R.params R.range (hotCaseGround R V q).recordedBad
          (hotCaseGround R V q).groundSetting.support (hotCoreSites R V) (P.biUnion id) : ℝ)) +
      R.coupling * (R.params.κ * R.params.threshold ^ 2 * (hotLumpsInAttached R.params R.range
          (hotCaseGround R V q).groundSetting.fine (hotCaseGround R V q).recordedBad
          (hotCaseGround R V q).groundSetting.support (hotCoreSites R V) (P.biUnion id) : ℝ)) +
      ClassCost * ((nearSites R.nextRange (P.biUnion id)).card : ℝ)
theorem torusHotSites_subset_hotCoreSites (V : TorusField n) : torusHotSites R.params V ⊆ hotCoreSites R V := by
  intro z hz
  unfold hotCoreSites
  rw [mem_thickening]
  exact ⟨z, hz, by simp [supDist_self]⟩
theorem card_sitesInBlocks (hodd : Odd R.params.side) (N : Finset (TorusSite n)) :
    ((sitesInBlocks R.params.side N).card : ℝ) = (R.params.side : ℝ) ^ 4 * (N.card : ℝ) := by
  classical
  have h1 : (sitesInBlocks R.params.side N).card = ∑ Y ∈ N, (sitesInBlocks R.params.side {Y}).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := parentBlock R.params.side) (t := N)
      (fun x hx => by simpa [sitesInBlocks] using hx)]
    refine Finset.sum_congr rfl fun Y hY => ?_
    congr 1
    ext x
    simp only [sitesInBlocks, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨h ▸ hY, h⟩
  have h2 : ∀ Y ∈ N, (sitesInBlocks R.params.side {Y}).card = R.params.side ^ 4 := fun Y _ => by
    have := BlockOffsets.sum_sitesInBlocks (L := R.params.side) hodd Y (fun _ => (1 : ℕ))
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at this
    rw [this, BlockOffsets.card_centredCube hodd]
  rw [h1, Finset.sum_congr rfl h2]
  simp [mul_comm]
theorem card_freeNear_le (s : ChartSetting R n) (N : Finset (TorusSite n)) (hodd : Odd R.params.side) :
    ((s.freeNear N).card : ℝ) ≤ 4 * (R.params.side : ℝ) ^ 4 * (N.card : ℝ) := by
  classical
  have h1 : (s.freeNear N).card ≤
      ((sitesInBlocks R.params.side N) ×ˢ (Finset.univ : Finset (Fin 4))).card := by
    refine Finset.card_le_card_of_injOn (fun b => b.1) ?_ ?_
    · intro b hb
      have hb' : bondBlock (R := R) b.1 ∈ N := (Finset.mem_filter.mp hb).2
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_univ, and_true]
      simpa [sitesInBlocks, bondBlock] using hb'
    · intro b _ b' _ h
      exact Subtype.ext h
  have h2 := card_sitesInBlocks hodd N
  have h3 : ((s.freeNear N).card : ℝ) ≤
      (((sitesInBlocks R.params.side N) ×ˢ (Finset.univ : Finset (Fin 4))).card : ℝ) := by
    exact_mod_cast h1
  rw [Finset.card_product] at h3
  push_cast at h3
  rw [h2] at h3
  simp at h3
  linarith
theorem nearDensityBound_of {T : ParameterAssignment} {y : ℝ} {R : StepSetup} (hT : T.Admissible) (hR : R.OnParameters T y)
    (hy0 : T.floorMin ≤ y) (hmv : |R.nextCoupling - R.coupling| ≤ 2 * T.B) (hr8 : 8 * R.params.side ≤ R.range)
    (hr16 : 2 ^ 16 ≤ R.range) (hx : 1 ≤ R.coupling) (hlog : 0 ≤ Real.log R.coupling)
    (hint : LocalIntegralLeBallVolume) {Cd Cp Ca A Cg cg : ℝ} (hCd : 0 ≤ Cd) (hCp : 0 ≤ Cp) (hCa : 0 ≤ Ca)
    (hA : 0 ≤ A)
    (hdens : ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n → ∀ (s : ChartSetting R n) (c : SettingCore R n), s.IsAdmissible →
      s.IsCoreOf c → s.IsMarked c → ∀ K ⊆ s.storedComponents c,
        0 < s.localIntegral (blocksNear R.params.side R.range (K.biUnion id)) ∧
        |∑ Y ∈ blocksNear R.params.side R.range (K.biUnion id), s.blockActivity T.lam Y -
            Real.log (s.localIntegral (blocksNear R.params.side R.range (K.biUnion id)))| ≤
          Cd * (R.range : ℝ) ^ 4 * Real.log R.coupling *
            ((blocksNear R.params.side R.range (K.biUnion id)).card : ℝ))
    (hpot : ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n → ∀ (s : ChartSetting R n) (c : SettingCore R n), s.IsAdmissible →
      s.IsCoreOf c → ∀ K ⊆ s.storedComponents c, ∀ Yk : Finset (TorusSite (n * R.params.side)), Yk ⊆ s.support →
        Yk ⊆ K.biUnion id →
        (∀ z ∈ s.support \ Yk, ∀ y ∈ sitesInBlocks R.params.side (blocksNear R.params.side R.range (K.biUnion id)),
          (R.range : ℝ) / 4 ≤ supDist y z) →
        ∀ η : FreeCoords s.free, s.InBalls η →
          -(s.localPotential (blocksNear R.params.side R.range (K.biUnion id)) fun b => η b.1) ≤
            -(R.coupling * s.energyNear (blocksNear R.params.side R.range (K.biUnion id)) η) +
              ∑ z ∈ nearSites R.range Yk, R.siteDensity (n * R.params.side) z (s.field 0) s.support s.labelling +
              Cp * (R.range : ℝ) ^ 4 * Real.log R.coupling *
                ((blocksNear R.params.side R.range (K.biUnion id)).card : ℝ))
    (hEn : StepEnergy.EnergyNearPieceAt R T.cE Cg cg)
    (hsmall : R.coupling ^ Cg * Real.exp (-(cg * R.range)) ≤ 1)
    (hof : ∀ (n : ℕ) [NeZero n], IsBlockTorusSide R.params n → ∀ (V : TorusField n) (q : CoarseState R n),
      IsHullState R.params R.nextRange V q.1 →
      (∀ X ∈ chainComponents R.nextRange q.1, coarseFactor V q X ≠ 0) → (hotCaseGround R V q).IsOverState)
    (hset : ∀ (n : ℕ) [NeZero n] (G : GasGround R n), G.IsAdmissibleGround → G.groundSetting.IsAdmissible)
    (hgas : ∀ (n : ℕ) [NeZero n] (G : GasGround R n), G.IsAdmissibleGround → ∀ Y : TorusSite n,
      0 ≤ G.blockDensity Y ∧ G.blockDensity Y ≤ 1)
    (hsh : ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n → ∀ s : ChartSetting R n, s.IsAdmissible → ∀ Y : TorusSite n,
      0 ≤ levelShare R.params.coupling R.params.side (R.depth + 1) s.region Y s.coarse ∧
        levelShare R.params.coupling R.params.side (R.depth + 1) s.region Y s.coarse ≤ A)
    (hoff : ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n → ∀ s : ChartSetting R n, s.IsAdmissible →
      ∀ (c : SettingCore R n) (Y : TorusSite n), s.IsCoreOf c → s.IsMarked c → s.AwayFromCore c Y →
        |s.blockActivity T.lam Y + R.coupling * levelShare R.params.coupling R.params.side (R.depth + 1) s.region Y
          s.coarse| ≤ Ca * Real.log R.coupling)
    (hcold : ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n → (coldCaseGround R (trivialField n)).IsAdmissibleGround ∧
      ∀ Y : TorusSite n, |(coldCaseGround R (trivialField n)).groundSetting.blockActivity T.lam Y| ≤
        Ca * Real.log R.coupling) :
    NearDensityBound R T.lam T.cE ((Cd + Cp) * (R.range : ℝ) ^ 4 * Real.log R.coupling +
      4 * (R.params.side : ℝ) ^ 4 * |Real.log (liePointBallVolume R.ballRadius)| + 2 + 2 * T.B * A +
      2 * (Ca * Real.log R.coupling)) := by
  classical
  intro n _ hn V q P hhull hΦ hP
  have hfit : R.params.Admissible := hR.params_eq ▸ hT.fits y hy0
  have hL0 : 0 < R.params.side := by have := hfit.L_ge; omega
  have hn₀ : T.n₀ ≤ n := by
    have h1 : R.params.n₀ = T.n₀ := by rw [hR.params_eq]; rfl
    have h2 := hn.2
    rw [← h1]
    nlinarith
  have hn₀' : R.params.n₀ ≤ n := by
    have h1 : R.params.n₀ = T.n₀ := by rw [hR.params_eq]; rfl
    rw [h1]; exact hn₀
  have hρ : 0 < R.ballRadius := by
    have := hfit.σ_pos
    unfold StepSetup.ballRadius
    positivity
  have hcut : ColdStepAtMirrorFrames.IsCutoff R.ballRadius R.barrierFn := by
    have h1 : R.ballRadius = T.ballRadius := by
      unfold StepSetup.ballRadius ParameterAssignment.ballRadius
      rw [hR.params_eq]; rfl
    rw [h1, hR.barrierFn_eq]
    exact hT.cut
  have hG := hof n hn V q hhull hΦ
  set G := hotCaseGround R V q with hGdef
  have hs : G.groundSetting.IsAdmissible := hset n G (Or.inr hG.isHot)
  have hd : KeptRegion.KeptPartData R.params.side R.range R.nextRange G.recordedBad G.groundSetting.support
      (hotCoreSites R V) P :=
    { attached_eq := hG.attached_eq
      subset_components := by
        have h1 : coarseHull R.params.side R.range R.nextRange G.recordedBad G.groundSetting.support
            (hotCoreSites R V) = q.1 :=
          congrArg Sigma.fst hG.state_eq
        rw [h1]
        exact hP
      side_ge := hfit.L_ge
      side_odd := hfit.L_odd
      range_ge := hr8
      range_floor := hr16
      range_le := hR.isStep.2.2 }
  set K := attachedInBlocks R.params.side R.range G.recordedBad G.groundSetting.support (hotCoreSites R V)
    (P.biUnion id) with hKdef
  obtain ⟨K', hK'sub, hK'⟩ := KeptRegion.exists_clusters_eq_attachedInBlocks hd
  set N := blocksNear R.params.side R.range K with hNdef
  set Yk := componentsWithin R.params.side R.range G.groundSetting.support K with hYkdef
  set Near := nearSites R.nextRange (P.biUnion id) with hNeardef
  have hNsub : N ⊆ Near := fun Y hY => KeptRegion.mem_nearSites_of_mem_blocksNear hd hY
  have eD := hdens n hn₀ G.groundSetting G.settingCore hs hG.isCore hG.isMarked K' hK'sub
  rw [hK'] at eD
  obtain ⟨hIpos, hID⟩ := eD
  have hdens' : ∑ Y ∈ N, G.groundSetting.blockActivity T.lam Y ≤ Real.log (G.groundSetting.localIntegral N) +
      Cd * (R.range : ℝ) ^ 4 * Real.log R.coupling * (N.card : ℝ) := by
    have := (abs_le.mp hID).2
    linarith
  have hpot' : ∀ η : FreeCoords G.groundSetting.free, G.groundSetting.InBalls η →
      -(G.groundSetting.localPotential N fun b => η b.1) ≤ -(R.coupling * G.groundSetting.energyNear N η) +
        ∑ w ∈ nearSites R.range Yk, R.siteDensity (n * R.params.side) w G.groundSetting.fine
          G.groundSetting.support G.groundSetting.labelling +
        Cp * (R.range : ℝ) ^ 4 * Real.log R.coupling * (N.card : ℝ) := by
    intro η hη
    have := hpot n hn₀ G.groundSetting G.settingCore hs hG.isCore K' hK'sub Yk
      (KeptRegion.componentsWithin_subset_support hd)
      (by rw [hK']; exact KeptRegion.componentsWithin_subset_attached hd)
      (fun z hz w hw => by
        rw [hK'] at hw
        exact KeptRegion.quarter_le_supDist hd (Finset.mem_sdiff.mp hz).1 (Finset.mem_sdiff.mp hz).2 hw)
      η hη
    rw [hK', hG.field_zero] at this
    exact this
  have hE' : ∀ η : FreeCoords G.groundSetting.free, G.groundSetting.InBalls η →
      R.coupling * (∑ Y ∈ N, levelShare R.params.coupling R.params.side (R.depth + 1)
            (G.groundSetting.restSet G.settingCore) Y G.groundSetting.coarse +
          6 * R.params.κ * R.params.threshold ^ 2 *
            ((G.groundSetting.coarseLumpsInPiece G.settingCore K).card : ℝ) +
          R.params.κ / 4 * R.params.threshold ^ 2 * ((G.groundSetting.lumpsInPiece K).card : ℝ) +
          T.cE * ((badBlocksOff R.params.side G.recordedBad (hotCoreSites R V) K).card : ℝ)) -
        R.coupling ^ Cg * Real.exp (-(cg * R.range)) * (N.card : ℝ) ≤
      R.coupling * (G.groundSetting.energyNear N η +
        R.params.κ * R.params.threshold ^ 2 * ((G.groundSetting.lumpsInPiece K).card : ℝ)) :=
    fun η hη => hEn n G.groundSetting G.settingCore K η hn₀' hs hG.isCore hG.isMarked
      (Or.inr ⟨P, hd.subset_components, rfl⟩) hη (fun b hb _ => hG.bad_far b hb)
  have e0 := sum_blockActivity_near_le G.groundSetting N hρ hcut hint _ _ _ _ _ _ _ hIpos hdens' hpot' hE'
  obtain ⟨hG₁, hz₁⟩ := hcold n hn₀
  have hnear := sum_near_le_of_bounds Near N hNsub (fun z => G.groundSetting.blockActivity T.lam z)
    (fun z => G.blockDensity z)
    (fun z => levelShare R.params.coupling R.params.side (R.depth + 1) G.region z G.coarse)
    (fun z => (coldCaseGround R (trivialField n)).groundSetting.blockActivity T.lam z)
    (fun z => (coldCaseGround R (trivialField n)).blockDensity z)
    R.coupling R.nextCoupling (2 * T.B) A (Ca * Real.log R.coupling) hmv
    (fun z => (hgas n G (Or.inr hG.isHot) z).2)
    (fun z => (hgas n _ hG₁ z).1) hz₁ (fun z => hsh n hn₀ G.groundSetting hs z)
    (fun z hz => by
      obtain ⟨hz1, hz2⟩ := Finset.mem_sdiff.mp hz
      refine hoff n hn₀ G.groundSetting hs G.settingCore z hG.isCore hG.isMarked ?_
      intro Z hZ w hw u hu
      have hZ' : Z ∈ storedBlocks R.params.side R.range G.recordedBad G.groundSetting.support (hotCoreSites R V) := by
        have h1 : (G.groundSetting.storedComponents G.settingCore).biUnion id =
            attachedSites R.params.side R.range G.recordedBad G.groundSetting.support (hotCoreSites R V) := by
          rw [hd.attached_eq]
          exact biUnion_chainComponents
        unfold ChartSetting.storedBlockSet at hZ
        rw [h1] at hZ
        exact hZ
      exact KeptRegion.eighth_lt_supDist hd hz1 hz2 hZ' hw hu)
  have hrest : G.groundSetting.restSet G.settingCore = G.region := by
    unfold ChartSetting.restSet
    have h1 : G.settingCore.core ∩ torusHotSites R.params G.groundSetting.coarse = torusHotSites R.params V :=
      Finset.inter_eq_right.mpr (torusHotSites_subset_hotCoreSites V)
    rw [h1]
    rfl
  rw [hrest] at e0
  have hLHS : ∑ z ∈ Near, groundDensity R G T.lam z =
      ∑ z ∈ Near, (G.groundSetting.blockActivity T.lam z + G.blockDensity z +
        R.nextCoupling * levelShare R.params.coupling R.params.side (R.depth + 1) G.region z G.coarse -
        ((coldCaseGround R (trivialField n)).groundSetting.blockActivity T.lam z +
          (coldCaseGround R (trivialField n)).blockDensity z)) :=
    Finset.sum_congr rfl fun z _ => by simp only [groundDensity, GasGround.totalDensity]
  rw [hLHS]
  have hx0 : 0 ≤ R.coupling := by linarith
  have hκ := hfit.κ_pos
  have hσ := hfit.σ_pos
  have hr4 : 0 ≤ (R.range : ℝ) ^ 4 := by positivity
  have hNR : (N.card : ℝ) ≤ (Near.card : ℝ) := by exact_mod_cast Finset.card_le_card hNsub
  have hN0 : (0 : ℝ) ≤ (N.card : ℝ) := by positivity
  have hR0 : (0 : ℝ) ≤ (Near.card : ℝ) := le_trans hN0 hNR
  have htop : (((open Classical in (torusHotLumps R.params V).filter (· ⊆ P.biUnion id)).card : ℕ) : ℝ) ≤
      ((G.groundSetting.coarseLumpsInPiece G.settingCore K).card : ℝ) := by
    have : ((torusHotLumps R.params V).filter (· ⊆ P.biUnion id)) ⊆
        G.groundSetting.coarseLumpsInPiece G.settingCore K := by
      intro l hl
      obtain ⟨hl1, hl2⟩ := Finset.mem_filter.mp hl
      have hlC : l ⊆ hotCoreSites R V := fun z hz =>
        torusHotSites_subset_hotCoreSites V (Finset.mem_biUnion.mpr ⟨l, hl1, hz⟩)
      refine Finset.mem_filter.mpr ⟨hl1, hlC, fun u hu => ?_⟩
      have hb : parentBlock R.params.side u ∈ l := by simpa [sitesInBlocks] using hu
      refine (KeptRegion.mem_attachedInBlocks_iff hd).mpr ⟨?_, hl2 hb⟩
      unfold KeptRegion.clusterSites
      refine Finset.mem_union_right _ ?_
      simpa [sitesInBlocks] using hlC hb
    exact_mod_cast Finset.card_le_card this
  have hnf := card_freeNear_le G.groundSetting N hfit.L_odd
  have hD : 0 ≤ |Real.log (liePointBallVolume R.ballRadius)| := abs_nonneg _
  have hnfD : ((G.groundSetting.freeNear N).card : ℝ) * |Real.log (liePointBallVolume R.ballRadius)| ≤
      4 * (R.params.side : ℝ) ^ 4 * |Real.log (liePointBallVolume R.ballRadius)| * (Near.card : ℝ) := by
    calc _ ≤ (4 * (R.params.side : ℝ) ^ 4 * (N.card : ℝ)) * |Real.log (liePointBallVolume R.ballRadius)| :=
          mul_le_mul_of_nonneg_right hnf hD
      _ = 4 * (R.params.side : ℝ) ^ 4 * |Real.log (liePointBallVolume R.ballRadius)| * (N.card : ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hNR (by positivity)
  have hbd : Cd * (R.range : ℝ) ^ 4 * Real.log R.coupling * (N.card : ℝ) ≤
      Cd * (R.range : ℝ) ^ 4 * Real.log R.coupling * (Near.card : ℝ) :=
    mul_le_mul_of_nonneg_left hNR (by positivity)
  have hbp : Cp * (R.range : ℝ) ^ 4 * Real.log R.coupling * (N.card : ℝ) ≤
      Cp * (R.range : ℝ) ^ 4 * Real.log R.coupling * (Near.card : ℝ) :=
    mul_le_mul_of_nonneg_left hNR (by positivity)
  have hbe : R.coupling ^ Cg * Real.exp (-(cg * R.range)) * (N.card : ℝ) ≤ (Near.card : ℝ) :=
    (mul_le_mul_of_nonneg_right hsmall hN0).trans (by linarith)
  have hcoef : 0 ≤ 6 * R.params.κ * R.params.threshold ^ 2 := by positivity
  have h6x : R.coupling * (6 * R.params.κ * R.params.threshold ^ 2 *
        (((open Classical in (torusHotLumps R.params V).filter (· ⊆ P.biUnion id)).card : ℕ) : ℝ)) ≤
      R.coupling * (6 * R.params.κ * R.params.threshold ^ 2 *
        ((G.groundSetting.coarseLumpsInPiece G.settingCore K).card : ℝ)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htop hcoef) hx0
  have hhk : (hotLumpsInAttached R.params R.range G.groundSetting.fine G.recordedBad G.groundSetting.support
        (hotCoreSites R V) (P.biUnion id) : ℝ) =
      ((G.groundSetting.lumpsInPiece K).card : ℝ) := rfl
  have hbk : (badBlocksInAttached R.params R.range G.recordedBad G.groundSetting.support (hotCoreSites R V)
        (P.biUnion id) : ℝ) =
      ((badBlocksOff R.params.side G.recordedBad (hotCoreSites R V) K).card : ℝ) := rfl
  rw [hhk, hbk]
  have hsum : R.coupling * ∑ Y ∈ N, levelShare R.params.coupling R.params.side (R.depth + 1) G.region Y G.coarse =
      R.coupling * ∑ Y ∈ N, levelShare R.params.coupling R.params.side (R.depth + 1) G.region Y
        G.groundSetting.coarse := rfl
  have hfinal : ((Cd + Cp) * (R.range : ℝ) ^ 4 * Real.log R.coupling +
      4 * (R.params.side : ℝ) ^ 4 * |Real.log (liePointBallVolume R.ballRadius)| + 2 + 2 * T.B * A +
      2 * (Ca * Real.log R.coupling)) * (Near.card : ℝ) =
      Cd * (R.range : ℝ) ^ 4 * Real.log R.coupling * (Near.card : ℝ) +
        Cp * (R.range : ℝ) ^ 4 * Real.log R.coupling * (Near.card : ℝ) +
        4 * (R.params.side : ℝ) ^ 4 * |Real.log (liePointBallVolume R.ballRadius)| * (Near.card : ℝ) +
        (Near.card : ℝ) + (Near.card : ℝ) * (1 + 2 * T.B * A + 2 * (Ca * Real.log R.coupling)) := by ring
  rw [hfinal]
  simp only [mul_add] at e0 hnear ⊢
  linarith
theorem le_clusterRange_of_pow_le {x : ℝ} (A : ℕ) (hx : (A : ℝ) ^ 100 ≤ x) : A ≤ clusterRange x := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.NearPotentialBound.le_clusterRange_of_pow_le <;> assumption
theorem surplus_le {Cd Cp D Bb Ca l r lg : ℝ} (hCd : 0 ≤ Cd) (hCp : 0 ≤ Cp) (hD : 0 ≤ D) (hBb : 0 ≤ Bb)
    (hCa : 0 ≤ Ca) (hr : 1 ≤ r) (hlg : 1 ≤ lg) :
    ((Cd + Cp) * r ^ 4 * lg + D + 2 + Bb + 2 * (Ca * lg)) + l ≤
      (Cd + Cp + D + 2 + Bb + 2 * Ca + |l|) * r ^ 8 * lg := by
  have hr48 : r ^ 4 ≤ r ^ 8 := pow_le_pow_right₀ hr (by norm_num)
  have hr8 : 1 ≤ r ^ 8 := one_le_pow₀ hr
  obtain ⟨b, hb⟩ : ∃ b, b = r ^ 8 * lg := ⟨_, rfl⟩
  have hb1 : 1 ≤ b := by rw [hb]; nlinarith
  have hb4 : r ^ 4 * lg ≤ b := by rw [hb]; exact mul_le_mul_of_nonneg_right hr48 (by linarith)
  have hblog : lg ≤ b := by rw [hb]; nlinarith
  have e1 : (Cd + Cp + D + 2 + Bb + 2 * Ca + |l|) * r ^ 8 * lg = (Cd + Cp + D + 2 + Bb + 2 * Ca + |l|) * b := by
    rw [hb]; ring
  have e2 : (Cd + Cp) * r ^ 4 * lg = (Cd + Cp) * (r ^ 4 * lg) := by ring
  rw [e1, e2]
  have t1 : (Cd + Cp) * (r ^ 4 * lg) ≤ (Cd + Cp) * b := mul_le_mul_of_nonneg_left hb4 (by positivity)
  have t2 : D * 1 ≤ D * b := mul_le_mul_of_nonneg_left hb1 hD
  have t3 : Bb * 1 ≤ Bb * b := mul_le_mul_of_nonneg_left hb1 hBb
  have t4 : Ca * lg ≤ Ca * b := mul_le_mul_of_nonneg_left hblog hCa
  have t5 : |l| * 1 ≤ |l| * b := mul_le_mul_of_nonneg_left hb1 (abs_nonneg _)
  have t6 : l ≤ |l| := le_abs_self _
  nlinarith
theorem exponent_le_sub {a ClassCost l CE' nR M : ℝ} (hn : 0 ≤ nR) (hb : ClassCost + l ≤ CE') (h : a + CE' * nR ≤ M) :
    a + ClassCost * nR ≤ M - l * nR := by
  have := mul_le_mul_of_nonneg_right hb hn
  nlinarith
theorem natPow_mul_ofReal_exp_le {lc k : ℕ} (hlc : 1 ≤ lc) {nR M : ℝ} (hk : (k : ℝ) ≤ nR) :
    ((lc ^ k : ℕ) : ENNReal) * ENNReal.ofReal (Real.exp (M - Real.log (lc : ℝ) * nR)) ≤
      ENNReal.ofReal (Real.exp M) := by
  have hlcR : (1 : ℝ) ≤ (lc : ℝ) := by exact_mod_cast hlc
  have hlog0 : 0 ≤ Real.log (lc : ℝ) := Real.log_nonneg hlcR
  have hpow : (((lc ^ k : ℕ) : ENNReal)) = ENNReal.ofReal ((lc : ℝ) ^ k) := by
    rw [← ENNReal.ofReal_natCast]
    push_cast
    rfl
  rw [hpow, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hpos : (0 : ℝ) < (lc : ℝ) := by linarith
  have hlp : (lc : ℝ) ^ k ≤ Real.exp (Real.log (lc : ℝ) * nR) := by
    calc (lc : ℝ) ^ k = Real.exp (Real.log (lc : ℝ) * (k : ℝ)) := by
          rw [Real.exp_mul, Real.exp_log hpos, Real.rpow_natCast]
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hk hlog0)
  calc (lc : ℝ) ^ k * Real.exp (M - Real.log (lc : ℝ) * nR)
      ≤ Real.exp (Real.log (lc : ℝ) * nR) * Real.exp (M - Real.log (lc : ℝ) * nR) :=
        mul_le_mul_of_nonneg_right hlp (Real.exp_pos _).le
    _ = Real.exp M := by
        rw [← Real.exp_add]
        congr 1
        ring
theorem isBlockTorusSide_mul {R : StepSetup} {n : ℕ} (hfit : R.params.Admissible)
    (hn : IsBlockTorusSide R.params n) :
    IsBlockTorusSide R.params (n * R.params.side) :=
  ⟨Dvd.intro_left n rfl, by
    have h1 := hn.2
    have h2 : R.params.n₀ ≤ n := by
      have := hfit.L_ge
      nlinarith
    have h3 : R.params.side * R.params.n₀ ≤ R.params.side * n := Nat.mul_le_mul_left _ h2
    linarith [Nat.mul_comm n R.params.side]⟩
theorem coarseFactor_congr {V : TorusField n} {q q' : CoarseState R n} {X : Finset (TorusSite n)}
    (h : q.restrict X = q'.restrict X) :
    coarseFactor V q X = coarseFactor V q' X := by
  simp only [coarseFactor, admissibilityIndicator, clusterFactorProduct, markFactorProduct, baseFactorProduct]
  generalize q.restrict X = p at h ⊢
  subst h
  rfl
theorem coarseFactorExpansion_eq (V : TorusField n) (Y : Finset (TorusSite n))
    (ω : Y → CoarseLabel R.labels.Ω R.params.side) (X : Finset (TorusSite n)) :
    coarseFactorExpansion R n V Y ω X = coarseFactor V (⟨Y, ω⟩ : CoarseState R n) X := by
  unfold coarseFactorExpansion
  rw [dif_neg (NeZero.ne n)]
theorem stateDensity_eq (lam : ℝ) (z : TorusSite n) (V : TorusField n) (Y : Finset (TorusSite n))
    (ω : Y → CoarseLabel R.labels.Ω R.params.side) :
    R.stateDensity lam n z V Y ω = groundDensity R (hotCaseGround R V (⟨Y, ω⟩ : CoarseState R n)) lam z := by
  unfold StepSetup.stateDensity
  rw [dif_neg (NeZero.ne n)]
theorem sigma_mk_eq_of_labels {α : Type} {Ω : Type} {Y₁ Y₂ : Finset α} {f : Y₁ → Ω} {g : Y₂ → Ω} (hY : Y₁ = Y₂)
    (h : ∀ z (h₁ : z ∈ Y₁) (h₂ : z ∈ Y₂), f ⟨z, h₁⟩ = g ⟨z, h₂⟩) :
    (⟨Y₁, f⟩ : Σ Y : Finset α, (Y → Ω)) = ⟨Y₂, g⟩ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HotGround.sigma_mk_eq_of_eq <;> assumption
theorem restrict_glueState_of_disjoint {Y YP X : Finset (TorusSite n)}
    (ω : Y → CoarseLabel R.labels.Ω R.params.side) (ν : YP → CoarseLabel R.labels.Ω R.params.side)
    (hX : Disjoint X YP) :
    (glueState ω ν).restrict X = CoarseState.restrict (⟨Y, ω⟩ : CoarseState R n) X := by
  classical
  unfold CoarseState.restrict glueState
  refine sigma_mk_eq_of_labels rfl fun z h₁ h₂ => ?_
  have hzX : z ∈ X := (Finset.mem_inter.mp h₁).2
  have hz : z ∉ YP := Finset.disjoint_left.mp hX hzX
  simp only [glueLabel, hz, dif_neg, not_false_eq_true]
theorem lintegral_comp_equiv_pi {ι κ Ω : Type} [Fintype ι] [Fintype κ] [MeasurableSpace Ω] (μ : Measure Ω)
    [SigmaFinite μ] (e : κ ≃ ι) (Gf : (κ → Ω) → ENNReal) :
    ∫⁻ u : ι → Ω, Gf (fun z => u (e z)) ∂(Measure.pi fun _ => μ) = ∫⁻ v, Gf v ∂(Measure.pi fun _ => μ) := by
  classical
  have hmp := measurePreserving_piCongrLeft (α := fun _ : κ => Ω) (fun _ : κ => μ) e.symm
  have h1 : ∀ u : ι → Ω, (fun z => u (e z)) = (MeasurableEquiv.piCongrLeft (fun _ : κ => Ω) e.symm) u := by
    intro u
    funext z
    have := Equiv.piCongrLeft_apply_apply (fun _ : κ => Ω) e.symm u (e z)
    show u (e z) = (Equiv.piCongrLeft (fun _ : κ => Ω) e.symm) u z
    simpa using this.symm
  simp only [h1]
  rw [← hmp.map_eq, lintegral_map_equiv]
def priceIntegrand (R : StepSetup) (lam : ℝ) (n : ℕ) [NeZero n] (V : TorusField n) (Y : Finset (TorusSite n))
    (ω : Y → CoarseLabel R.labels.Ω R.params.side) (P : Finset (Finset (TorusSite n)))
    (ν : ↥(P.biUnion id) → CoarseLabel R.labels.Ω R.params.side) : ENNReal :=
  open Classical in
  if ∃ X ∈ P, coarseFactorExpansion R n V Y (glueLabel Y (P.biUnion id) ω ν) X = 0 then 0 else
    ENNReal.ofReal ((∏ X ∈ P, coarseFactorExpansion R n V Y (glueLabel Y (P.biUnion id) ω ν) X) *
      Real.exp (∑ z ∈ Finset.univ.filter (fun z : TorusSite n =>
          ∃ u ∈ P.biUnion id, (supDist z u : ℝ) < (R.nextRange : ℝ) / 4),
        R.stateDensity lam n z V Y (glueLabel Y (P.biUnion id) ω ν)))
theorem coarseFactor_ne_zero_of_priceIntegrand_ne_zero {lam : ℝ} {V : TorusField n} {Y : Finset (TorusSite n)}
    {ω : Y → CoarseLabel R.labels.Ω R.params.side}
    {P : Finset (Finset (TorusSite n))} (hP : P ⊆ chainComponents R.nextRange Y)
    (hoth : ∀ X ∈ chainComponents R.nextRange Y \ P, coarseFactorExpansion R n V Y ω X ≠ 0)
    {ν : ↥(P.biUnion id) → CoarseLabel R.labels.Ω R.params.side} (hν : priceIntegrand R lam n V Y ω P ν ≠ 0) :
    ∀ X ∈ chainComponents R.nextRange (glueState ω ν).1, coarseFactor V (glueState ω ν) X ≠ 0 := by
  classical
  intro X hX
  by_cases hXP : X ∈ P
  · intro h0
    apply hν
    unfold priceIntegrand
    rw [if_pos]
    exact ⟨X, hXP, by rw [coarseFactorExpansion_eq]; exact h0⟩
  · have hd : Disjoint X (P.biUnion id) := by
      rw [Finset.disjoint_left]
      intro z hz hz'
      obtain ⟨X', hX', hzX'⟩ := Finset.mem_biUnion.mp hz'
      have := eq_of_chainConnected_of_mem_chainComponents hX (hP hX') hz hzX' Relation.ReflTransGen.refl
      exact hXP (this ▸ hX')
    rw [coarseFactor_congr (restrict_glueState_of_disjoint ω ν hd), ← coarseFactorExpansion_eq]
    exact hoth X (Finset.mem_sdiff.mpr ⟨hX, hXP⟩)
section Slice
variable {lam cE ClassCost : ℝ}
def sliceWeightedIntegrand (R : StepSetup) (lam : ℝ) (qScore : CoarseLabel R.labels.Ω R.params.side → ℝ) (n : ℕ) [NeZero n]
    (V : TorusField n) (Y : Finset (TorusSite n))
    (ω : Y → CoarseLabel R.labels.Ω R.params.side) (P : Finset (Finset (TorusSite n)))
    (ν : ↥(P.biUnion id) → CoarseLabel R.labels.Ω R.params.side) :
    ENNReal :=
  priceIntegrand R lam n V Y ω P ν *
    ENNReal.ofReal (Real.exp (∑ y : ↥(P.biUnion id), qScore (ν y)))

open BlockAverages LumpContours ColdStepAtMirrorFrames KeptRegion StepEnergy StepFactors StepFloors BlockPlaces BlockOffsets in
theorem lintegral_slice_weighted_le (s₁ : ℝ) (s : R.labels.Ω → ℝ)
    (qScore : CoarseLabel R.labels.Ω R.params.side → ℝ)
    (hpriceBound : ∀ n [NeZero n], IsBlockTorusSide R.params n → ∀ (W : TorusField n) (Y : Finset (TorusSite n)) (ω : Y → R.labels.Ω)
    (P : Finset (Finset (TorusSite n))), IsHullState R.params (clusterRange R.coupling) W Y →
    P ⊆ chainComponents (clusterRange R.coupling) Y →
    (∀ X ∈ chainComponents (clusterRange R.coupling) Y \ P, R.clusterFactor n W Y ω X ≠ 0) →
    (open Classical in
      ∫⁻ ν, (if ∃ X ∈ P, R.clusterFactor n W Y (glueLabel Y (P.biUnion id) ω ν) X = 0 then 0 else
        ENNReal.ofReal ((∏ X ∈ P, R.clusterFactor n W Y (glueLabel Y (P.biUnion id) ω ν) X) *
          Real.exp (∑ y ∈ Finset.univ.filter (fun y : TorusSite n =>
              ∃ z ∈ P.biUnion id, (supDist y z : ℝ) < (clusterRange R.coupling : ℝ) / 4),
            R.siteDensity n y W Y (glueLabel Y (P.biUnion id) ω ν)) *
          Real.exp (∑ y : (P.biUnion id : Finset (TorusSite n)), s (ν y))))
        ∂(Measure.pi fun _ : (P.biUnion id : Finset (TorusSite n)) => R.labels.μ)) ≤
      ENNReal.ofReal (Real.exp (-(R.coupling * R.params.κ * R.params.threshold ^ 2 *
          ((open Classical in (torusHotLumps R.params W).filter (· ⊆ P.biUnion id)).card : ℝ)) -
        R.params.κ₁ * R.coupling * R.params.threshold ^ 2 * (excessLength R.params (clusterRange R.coupling) (P.biUnion id) W : ℝ))))
    (hrow : R.HasExpansions) (hfit : R.params.Admissible) (hr8 : 8 * R.params.side ≤ R.range)
    (hr16 : 2 ^ 16 ≤ R.range)
    (hnear : R.range ≤ R.nextRange + 1) (hx : 0 ≤ R.coupling) (hnb : NearDensityBound R lam cE ClassCost)
    (hof : IsBlockTorusSide R.params n → ∀ (V : TorusField n) (q : CoarseState R n),
      IsHullState R.params R.nextRange V q.1 →
      (∀ X ∈ chainComponents R.nextRange q.1, coarseFactor V q X ≠ 0) → (hotCaseGround R V q).IsOverState)
    (hset : ∀ G : GasGround R n, G.IsAdmissibleGround → G.groundSetting.IsAdmissible)
    (hfac : IsBlockTorusSide R.params n → ∀ (V : TorusField n) (q : CoarseState R n)
      (W : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω)
      (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n)
      (P : Finset (Finset (TorusSite n))),
      IsHullState R.params R.nextRange V q.1 → IsHullState R.params R.range W Yt →
      coarseStateOf R (hotCoreSites R V) W Yt ωt bad b = q →
      attachedSites R.params.side R.range bad Yt (hotCoreSites R V) =
        _root_.YangMills.Construction.KeptRegion.clusterSites R.params.side bad Yt (hotCoreSites R V) →
      P ⊆ chainComponents R.nextRange q.1 → (∀ X ∈ chainComponents R.nextRange q.1, coarseFactor V q X ≠ 0) →
      ∏ X ∈ P, coarseFactor V q X ≤
        ∏ Xc ∈ (open Classical in (chainComponents R.range Yt).filter
            (· ⊆ attachedInBlocks R.params.side R.range bad Yt (hotCoreSites R V) (P.biUnion id))),
          R.clusterFactor (n * R.params.side) W Yt ωt Xc)
    (hn : IsBlockTorusSide R.params n) (hbn : IsBlockTorusSide R.params (n * R.params.side)) (V : TorusField n)
    (Y : Finset (TorusSite n))
    (ω : Y → CoarseLabel R.labels.Ω R.params.side) (P : Finset (Finset (TorusSite n)))
    (hhull : IsHullState R.params R.nextRange V Y) (hP : P ⊆ chainComponents R.nextRange Y)
    (hoth : ∀ X ∈ chainComponents R.nextRange Y \ P, coarseFactorExpansion R n V Y ω X ≠ 0) (Mc : ℝ)
    (hM : ∀ (ν : ↥(P.biUnion id) → CoarseLabel R.labels.Ω R.params.side) (W : TorusField (n * R.params.side))
      (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω)
      (bad : Finset (TorusBond (n * R.params.side)))
      (b : BaseChoice R.params.side n), IsHullState R.params R.range W Yt →
      coarseStateOf R (hotCoreSites R V) W Yt ωt bad b = ⟨Y, glueLabel Y (P.biUnion id) ω ν⟩ →
      -R.coupling * (6 * R.params.κ * R.params.threshold ^ 2 *
          ((open Classical in (torusHotLumps R.params V).filter (· ⊆ P.biUnion id)).card : ℝ) +
        R.params.κ / 4 * R.params.threshold ^ 2 *
          (hotLumpsInAttached R.params R.range W bad Yt (hotCoreSites R V) (P.biUnion id) : ℝ) +
        cE * (badBlocksInAttached R.params R.range bad Yt (hotCoreSites R V) (P.biUnion id) : ℝ) +
        R.params.κ₁ * R.params.threshold ^ 2 *
          (lengthInAttached R.params R.range W bad Yt (hotCoreSites R V) (P.biUnion id) : ℝ)) +
      ClassCost * ((nearSites R.nextRange (P.biUnion id)).card : ℝ) ≤ Mc)
    (Z : Finset ↥(P.biUnion id)) (a : Z → Bool) (bd : Z → BlockBond R.params.side → Bool)
    (o : Z → BlockOffset R.params.side)
    (A : Finset (Z × BlockOffset R.params.side)) (B : Finset (Z × BlockBond R.params.side))
    (g : B → UnitQuaternion)
    (hscore : ∀ u : A → R.labels.Ω,
      (∑ y : ↥(P.biUnion id), qScore (sliceLabel Z a bd o A B g u y)) =
        s₁ * (Fintype.card ↥(P.biUnion id) : ℝ) + ∑ p : A, s (u p)) :
    ∫⁻ u : A → R.labels.Ω, sliceWeightedIntegrand R lam qScore n V Y ω P (sliceLabel Z a bd o A B g u)
        ∂(Measure.pi fun _ => R.labels.μ) ≤
      ENNReal.ofReal (Real.exp (Mc + s₁ * (Fintype.card ↥(P.biUnion id) : ℝ))) := by
  classical
  have hYP : P.biUnion id ⊆ Y := by
    intro z hz
    obtain ⟨X, hX, hzX⟩ := Finset.mem_biUnion.mp hz
    exact subset_of_mem_chainComponents (hP hX) hzX
  by_cases hzero : ∀ u, priceIntegrand R lam n V Y ω P (sliceLabel Z a bd o A B g u) = 0
  · simp [sliceWeightedIntegrand, hzero]
  push Not at hzero
  obtain ⟨u₀, hu₀⟩ := hzero
  set q₀ : CoarseState R n := sliceState ω Z a bd o A B g u₀ with hq₀
  have hall₀ := coarseFactor_ne_zero_of_priceIntegrand_ne_zero hP hoth hu₀
  have hG₀ := hof hn V q₀ hhull hall₀
  set G₀ := hotCaseGround R V q₀ with hG₀def
  have hs₀ : G₀.groundSetting.IsAdmissible := hset G₀ (Or.inr hG₀.isHot)
  have hd : KeptPartData R.params.side R.range R.nextRange G₀.recordedBad G₀.groundSetting.support
      (hotCoreSites R V) P :=
    { attached_eq := hG₀.attached_eq
      subset_components := by
        have h1 : coarseHull R.params.side R.range R.nextRange G₀.recordedBad G₀.groundSetting.support
            (hotCoreSites R V) = Y :=
          congrArg Sigma.fst hG₀.state_eq
        rw [h1]
        exact hP
      side_ge := hfit.L_ge
      side_odd := hfit.L_odd
      range_ge := hr8
      range_floor := hr16
      range_le := hnear }
  set W₀ := G₀.groundSetting.fine with hW₀
  set Yt₀ := G₀.groundSetting.support with hYt₀
  set ωt₀ := G₀.groundSetting.labelling with hωt₀
  set bad₀ := G₀.recordedBad with hbad₀
  set K₀ := attachedInBlocks R.params.side R.range bad₀ Yt₀ (hotCoreSites R V) (P.biUnion id) with hK₀
  set Pk := (chainComponents R.range Yt₀).filter (· ⊆ K₀) with hPk
  set Yk := componentsWithin R.params.side R.range Yt₀ K₀ with hYk
  have hinY : ∀ z ∈ Yk, parentBlock R.params.side z ∈ P.biUnion id := fun z hz =>
    ((mem_attachedInBlocks_iff hd).mp (componentsWithin_subset_attached hd hz)).2
  have hl₀ : ∀ z (hz : z ∈ Yt₀), q₀.labelAt z = Sum.inr (ωt₀ ⟨z, hz⟩) := fun z hz =>
    labelAt_of_mem_groundSetting_support G₀ z hz
  have hinZ : ∀ z (hz : z ∈ Yk), (⟨parentBlock R.params.side z, hinY z hz⟩ : ↥(P.biUnion id)) ∈ Z := by
    intro z hz
    by_contra hZ
    have h1 : q₀.labelAt z = Sum.inl () := labelAt_sliceState_of_not_mem_blocks hYP u₀ rfl (hinY z hz) hZ
    have h2 := hl₀ z (componentsWithin_subset_support hd hz)
    rw [h1] at h2
    simp at h2
  have hinA : ∀ z (hz : z ∈ Yk),
      (((⟨⟨parentBlock R.params.side z, hinY z hz⟩, hinZ z hz⟩ : Z), siteOffset z) :
        Z × BlockOffset R.params.side) ∈ A := by
    intro z hz
    by_contra hA
    have h1 : q₀.labelAt z = fillOn A u₀ (⟨⟨parentBlock R.params.side z, hinY z hz⟩, hinZ z hz⟩, siteOffset z) :=
      labelAt_sliceState_of_mem hYP u₀ rfl (hinY z hz) (hinZ z hz)
    have h2 := hl₀ z (componentsWithin_subset_support hd hz)
    rw [h1] at h2
    simp [fillOn, hA] at h2
  have hmem : ∀ p : ↥A, (blockSite (L := R.params.side) p.1.1.1.1 p.1.2 : TorusSite (n * R.params.side)) ∈ Yk := by
    intro p
    have hy : p.1.1.1.1 ∈ P.biUnion id := p.1.1.1.2
    have hZ : (⟨p.1.1.1.1, hy⟩ : ↥(P.biUnion id)) ∈ Z := p.1.1.2
    have hb : parentBlock R.params.side (blockSite (L := R.params.side) p.1.1.1.1 p.1.2 :
        TorusSite (n * R.params.side)) = p.1.1.1.1 :=
      parentBlock_blockSite _ _
    have hpl : siteOffset (blockSite (L := R.params.side) p.1.1.1.1 p.1.2 : TorusSite (n * R.params.side)) =
        p.1.2 := siteOffset_blockSite _ _
    have h1 : q₀.labelAt (blockSite (L := R.params.side) p.1.1.1.1 p.1.2) =
        fillOn A u₀ (⟨⟨p.1.1.1.1, hy⟩, hZ⟩, _) :=
      labelAt_sliceState_of_mem hYP u₀ hb hy hZ
    rw [hpl] at h1
    have h2 : q₀.labelAt (blockSite (L := R.params.side) p.1.1.1.1 p.1.2) = Sum.inr (u₀ p) := by
      rw [h1]
      have : ((⟨⟨p.1.1.1.1, hy⟩, hZ⟩, p.1.2) : Z × BlockOffset R.params.side) = p.1 := rfl
      simp only [fillOn, this, p.2, dif_pos]
    have hzY : (blockSite (L := R.params.side) p.1.1.1.1 p.1.2 : TorusSite (n * R.params.side)) ∈ Yt₀ := by
      rw [hYt₀, groundSetting_support]
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      show (q₀.labelAt _).isRight = true
      rw [h2]
      rfl
    exact mem_componentsWithin hd hzY (by rw [hb]; exact hy)
  let e : ↥Yk ≃ ↥A :=
    { toFun := fun z => ⟨(⟨⟨parentBlock R.params.side z.1, hinY z.1 z.2⟩, hinZ z.1 z.2⟩, siteOffset z.1),
        hinA z.1 z.2⟩
      invFun := fun p => ⟨blockSite (L := R.params.side) p.1.1.1.1 p.1.2, hmem p⟩
      left_inv := fun z => Subtype.ext (blockSite_parentBlock_siteOffset z.1)
      right_inv := fun p => by
        apply Subtype.ext
        apply Prod.ext
        · apply Subtype.ext
          apply Subtype.ext
          exact parentBlock_blockSite _ _
        · exact siteOffset_blockSite _ _ }
  set hk : ℕ := hotLumpsInAttached R.params R.range W₀ bad₀ Yt₀ (hotCoreSites R V) (P.biUnion id) with hhk
  set bk : ℕ := badBlocksInAttached R.params R.range bad₀ Yt₀ (hotCoreSites R V) (P.biUnion id) with hbk
  set nR : ℝ := ((nearSites R.nextRange (P.biUnion id)).card : ℝ) with hnR
  set hp : ℝ := (((torusHotLumps R.params V).filter (· ⊆ P.biUnion id)).card : ℝ) with hhp
  set Hs : (Σ Y' : Finset (TorusSite (n * R.params.side)), (Y' → R.labels.Ω)) → ENNReal := fun st =>
    if ∃ X ∈ Pk, R.clusterFactor (n * R.params.side) W₀ st.1 st.2 X = 0 then 0 else
      ENNReal.ofReal ((∏ X ∈ Pk, R.clusterFactor (n * R.params.side) W₀ st.1 st.2 X) *
        Real.exp (∑ w ∈ nearSites R.range Yk, R.siteDensity (n * R.params.side) w W₀ st.1 st.2)) with hHs
  set E : ℝ := -(R.coupling * (6 * R.params.κ * R.params.threshold ^ 2 * hp +
      R.params.κ / 4 * R.params.threshold ^ 2 * (hk : ℝ) + cE * (bk : ℝ))) +
    R.coupling * (R.params.κ * R.params.threshold ^ 2 * (hk : ℝ)) + ClassCost * nR with hE
  have hpt : ∀ u : A → R.labels.Ω, priceIntegrand R lam n V Y ω P (sliceLabel Z a bd o A B g u) ≤
      ENNReal.ofReal (Real.exp E) * Hs ⟨Yt₀, glueLabel Yt₀ Yk ωt₀ fun z => u (e z)⟩ := by
    intro u
    by_cases hF : priceIntegrand R lam n V Y ω P (sliceLabel Z a bd o A B g u) = 0
    · rw [hF]
      exact zero_le
    set q : CoarseState R n := sliceState ω Z a bd o A B g u with hq
    have hall := coarseFactor_ne_zero_of_priceIntegrand_ne_zero hP hoth hF
    have hG := hof hn V q hhull hall
    set G := hotCaseGround R V q with hGdef
    have hs : G.groundSetting.IsAdmissible := hset G (Or.inr hG.isHot)
    have hsame : q₀.AgreeUpToLabels q := sliceState_agreeUpToLabels hYP u₀ u
    have hbase : G.groundSetting.fine = W₀ := (groundSetting_fine_eq_of_agree hsame _ _ _).symm
    have hYt : G.groundSetting.support = Yt₀ := by
      rw [hYt₀, groundSetting_support, groundSetting_support]
      exact (recordedSites_eq_of_agree hsame _ _ _).symm
    have hbad : G.recordedBad = bad₀ := (recordedBad_eq_of_agree hsame _ _ _).symm
    have hsig : (⟨G.groundSetting.support, G.groundSetting.labelling⟩ :
        Σ Y' : Finset (TorusSite (n * R.params.side)), (Y' → R.labels.Ω)) =
        ⟨Yt₀, glueLabel Yt₀ Yk ωt₀ fun z => u (e z)⟩ := by
      refine _root_.YangMills.Construction.ClusterExpansionOfAStep.HotGround.sigma_mk_eq_of_eq hYt fun z h₁ h₂ => ?_
      have hql := labelAt_of_mem_groundSetting_support G z h₁
      by_cases hzk : z ∈ Yk
      · have h3 : q.labelAt z =
            fillOn A u (⟨⟨parentBlock R.params.side z, hinY z hzk⟩, hinZ z hzk⟩, siteOffset z) :=
          labelAt_sliceState_of_mem hYP u rfl (hinY z hzk) (hinZ z hzk)
        have h4 : q.labelAt z = Sum.inr (u (e ⟨z, hzk⟩)) := by
          rw [h3]
          simp only [fillOn, hinA z hzk, dif_pos]
          rfl
        have h5 : (Sum.inr (G.groundSetting.labelling ⟨z, h₁⟩) : WithNone R.labels.Ω) =
            Sum.inr (u (e ⟨z, hzk⟩)) :=
          hql.symm.trans h4
        simp only [glueLabel, hzk, dif_pos]
        exact Sum.inr.inj h5
      · have hb : parentBlock R.params.side z ∉ P.biUnion id := fun hb => hzk (mem_componentsWithin hd h₂ hb)
        have h3 : q.labelAt z = q₀.labelAt z := labelAt_sliceState_of_not_mem u u₀ hb
        have h4 := hl₀ z h₂
        have h5 : (Sum.inr (G.groundSetting.labelling ⟨z, h₁⟩) : WithNone R.labels.Ω) = Sum.inr (ωt₀ ⟨z, h₂⟩) :=
          hql.symm.trans (h3.trans h4)
        simp only [glueLabel, hzk, dif_neg, not_false_eq_true]
        exact Sum.inr.inj h5
    have hb := hnb n hn V q P hhull hall hP
    have hYkEq : componentsWithin R.params.side R.range G.groundSetting.support
        (attachedInBlocks R.params.side R.range G.recordedBad G.groundSetting.support (hotCoreSites R V)
          (P.biUnion id)) = Yk := by
      rw [hYt, hbad]
    have hkEq : hotLumpsInAttached R.params R.range G.groundSetting.fine G.recordedBad G.groundSetting.support
        (hotCoreSites R V) (P.biUnion id) = hk := by
      rw [hbase, hYt, hbad]
    have bkEq : badBlocksInAttached R.params R.range G.recordedBad G.groundSetting.support (hotCoreSites R V)
        (P.biUnion id) = bk := by
      rw [hYt, hbad]
    rw [hYkEq, hkEq, bkEq, hbase] at hb
    have hfu := hfac hn V q G.groundSetting.fine G.groundSetting.support G.groundSetting.labelling G.recordedBad
      G.groundSetting.bases P hhull hG.isHull hG.state_eq hG.attached_eq hP hall
    have hPkEq : (chainComponents R.range G.groundSetting.support).filter
        (· ⊆ attachedInBlocks R.params.side R.range G.recordedBad G.groundSetting.support (hotCoreSites R V)
          (P.biUnion id)) = Pk := by
      rw [hYt, hbad]
    rw [hPkEq, hbase] at hfu
    have hρ : 0 ≤ R.ballRadius := by
      have := hfit.σ_pos
      unfold StepSetup.ballRadius
      positivity
    have hzero0 : G.groundSetting.InBalls 0 := by
      intro b
      rw [show (0 : FreeCoords G.groundSetting.free) b = 0 from rfl, coordNorm_zero]
      exact hρ
    have hfac0 : ∀ X ∈ Pk, R.clusterFactor (n * R.params.side) W₀ G.groundSetting.support
        G.groundSetting.labelling X ≠ 0 := by
      intro X hX
      have h1 : X ∈ chainComponents R.range G.groundSetting.support := by
        rw [hYt]
        exact (Finset.mem_filter.mp hX).1
      have h2 := hs.factor_ne_zero 0 hzero0 X h1
      rwa [hG.field_zero, hbase] at h2
    have hval : Hs ⟨G.groundSetting.support, G.groundSetting.labelling⟩ =
        ENNReal.ofReal ((∏ X ∈ Pk, R.clusterFactor (n * R.params.side) W₀ G.groundSetting.support
            G.groundSetting.labelling X) *
          Real.exp (∑ w ∈ nearSites R.range Yk, R.siteDensity (n * R.params.side) w W₀ G.groundSetting.support
            G.groundSetting.labelling)) := by
      simp only [hHs]
      rw [if_neg]
      rintro ⟨X, hX, h0⟩
      exact hfac0 X hX h0
    rw [← hsig, hval, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    have hne : ¬ ∃ X ∈ P,
        coarseFactorExpansion R n V Y (glueLabel Y (P.biUnion id) ω (sliceLabel Z a bd o A B g u)) X = 0 := by
      intro h
      apply hF
      unfold priceIntegrand
      rw [if_pos h]
    unfold priceIntegrand
    rw [if_neg hne]
    refine ENNReal.ofReal_le_ofReal ?_
    have hprod : ∏ X ∈ P, coarseFactorExpansion R n V Y (glueLabel Y (P.biUnion id) ω (sliceLabel Z a bd o A B g u)) X =
        ∏ X ∈ P, coarseFactor V q X := Finset.prod_congr rfl fun X _ => coarseFactorExpansion_eq V Y _ X
    have hsum : ∑ z ∈ Finset.univ.filter (fun z : TorusSite n =>
            ∃ u' ∈ P.biUnion id, (supDist z u' : ℝ) < (R.nextRange : ℝ) / 4),
          R.stateDensity lam n z V Y (glueLabel Y (P.biUnion id) ω (sliceLabel Z a bd o A B g u)) =
        ∑ z ∈ nearSites R.nextRange (P.biUnion id), groundDensity R G lam z :=
      Finset.sum_congr rfl fun z _ => stateDensity_eq lam z V Y _
    rw [hprod, hsum]
    have hPiNN : 0 ≤ ∏ X ∈ Pk, R.clusterFactor (n * R.params.side) W₀ G.groundSetting.support
        G.groundSetting.labelling X :=
      Finset.prod_nonneg fun X _ => hrow.2.factor_nonneg (n * R.params.side) hbn _ _ _ _
    have hS : ∑ z ∈ nearSites R.nextRange (P.biUnion id), groundDensity R G lam z ≤
        ∑ w ∈ nearSites R.range Yk, R.siteDensity (n * R.params.side) w W₀ G.groundSetting.support
          G.groundSetting.labelling + E := by
      rw [hE]
      simp only [hnR, hhp]
      linarith
    calc _ ≤ (∏ X ∈ Pk, R.clusterFactor (n * R.params.side) W₀ G.groundSetting.support
            G.groundSetting.labelling X) *
          Real.exp (∑ z ∈ nearSites R.nextRange (P.biUnion id), groundDensity R G lam z) :=
          mul_le_mul_of_nonneg_right hfu (Real.exp_pos _).le
      _ ≤ (∏ X ∈ Pk, R.clusterFactor (n * R.params.side) W₀ G.groundSetting.support
            G.groundSetting.labelling X) *
          Real.exp (∑ w ∈ nearSites R.range Yk, R.siteDensity (n * R.params.side) w W₀ G.groundSetting.support
            G.groundSetting.labelling + E) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hS) hPiNN
      _ = _ := by rw [Real.exp_add]; ring
  have hρ₀ : 0 ≤ R.ballRadius := by
    have := hfit.σ_pos
    unfold StepSetup.ballRadius
    positivity
  have hzero₀ : G₀.groundSetting.InBalls 0 := by
    intro b
    rw [show (0 : FreeCoords G₀.groundSetting.free) b = 0 from rfl, coordNorm_zero]
    exact hρ₀
  have hoth₀ : ∀ X ∈ chainComponents (clusterRange R.coupling) Yt₀ \ Pk,
      R.clusterFactor (n * R.params.side) W₀ Yt₀ ωt₀ X ≠ 0 := by
    intro X hX
    have h2 := hs₀.factor_ne_zero 0 hzero₀ X (Finset.mem_sdiff.mp hX).1
    rwa [hG₀.field_zero] at h2
  have hprice := hpriceBound (n * R.params.side) hbn W₀ Yt₀ ωt₀ Pk hG₀.isHull (Finset.filter_subset _ _) hoth₀
  have hhot : ((torusHotLumps R.params W₀).filter (· ⊆ Pk.biUnion id)) =
      ((torusHotLumps R.params W₀).filter (· ⊆ K₀)) := by
    ext l
    simp only [Finset.mem_filter]
    refine and_congr_right fun hl => ⟨fun h => h.trans (componentsWithin_subset_attached hd), fun h z hz => ?_⟩
    have hzh : z ∈ torusHotSites R.params W₀ := Finset.mem_biUnion.mpr ⟨l, hl, hz⟩
    have hzY : z ∈ Yt₀ := hG₀.isHull.1 ((mem_thickening _ _ _).mpr ⟨z, hzh, by simp [supDist_self]⟩)
    exact mem_componentsWithin hd hzY ((mem_attachedInBlocks_iff hd).mp (h hz)).2
  have hfin : E + (-(R.coupling * R.params.κ * R.params.threshold ^ 2 *
        (((torusHotLumps R.params W₀).filter (· ⊆ Pk.biUnion id)).card : ℝ)) -
      R.params.κ₁ * R.coupling * R.params.threshold ^ 2 *
        (excessLength R.params (clusterRange R.coupling) (Pk.biUnion id) W₀ : ℝ)) ≤ Mc := by
    have hm := hM (sliceLabel Z a bd o A B g u₀) W₀ Yt₀ ωt₀ bad₀ G₀.groundSetting.bases hG₀.isHull hG₀.state_eq
    rw [hhot]
    have e1 : ((((torusHotLumps R.params W₀).filter (· ⊆ K₀)).card : ℕ) : ℝ) = (hk : ℝ) := rfl
    have e2 : (excessLength R.params (clusterRange R.coupling) (Pk.biUnion id) W₀ : ℝ) =
        (lengthInAttached R.params R.range W₀ bad₀ Yt₀ (hotCoreSites R V) (P.biUnion id) : ℝ) := rfl
    rw [e1, e2, hE]
    nlinarith
  set c₁ : ℝ := s₁ * (Fintype.card ↥(P.biUnion id) : ℝ) with hc₁
  set Hv : (Yk → R.labels.Ω) → ENNReal := fun v =>
    Hs ⟨Yt₀, glueLabel Yt₀ Yk ωt₀ v⟩ * ENNReal.ofReal (Real.exp (∑ y : Yk, s (v y))) with hHv
  have hst : ∀ u : A → R.labels.Ω, sliceWeightedIntegrand R lam qScore n V Y ω P (sliceLabel Z a bd o A B g u) ≤
      ENNReal.ofReal (Real.exp (E + c₁)) * Hv fun z => u (e z) := by
    intro u
    have hsum : ∑ y : ↥(P.biUnion id), qScore (sliceLabel Z a bd o A B g u y) =
        c₁ + ∑ y : Yk, s (u (e y)) := by
      rw [hscore, Equiv.sum_comp e fun p => s (u p)]
    unfold sliceWeightedIntegrand
    rw [hsum, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
    simp only [hHv]
    rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
    calc priceIntegrand R lam n V Y ω P (sliceLabel Z a bd o A B g u) *
          (ENNReal.ofReal (Real.exp c₁) * ENNReal.ofReal (Real.exp (∑ y : Yk, s (u (e y)))))
        ≤ (ENNReal.ofReal (Real.exp E) * Hs ⟨Yt₀, glueLabel Yt₀ Yk ωt₀ fun z => u (e z)⟩) *
          (ENNReal.ofReal (Real.exp c₁) * ENNReal.ofReal (Real.exp (∑ y : Yk, s (u (e y))))) := by
          gcongr
          exact hpt u
      _ = _ := by ring
  have hvi : ∫⁻ v : Yk → R.labels.Ω, Hv v ∂(Measure.pi fun _ => R.labels.μ) ≤ ENNReal.ofReal (Real.exp
      (-(R.coupling * R.params.κ * R.params.threshold ^ 2 *
          (((torusHotLumps R.params W₀).filter (· ⊆ Pk.biUnion id)).card : ℝ)) -
        R.params.κ₁ * R.coupling * R.params.threshold ^ 2 *
          (excessLength R.params (clusterRange R.coupling) (Pk.biUnion id) W₀ : ℝ))) := by
    refine le_trans (le_of_eq ?_) hprice
    refine lintegral_congr fun v => ?_
    simp only [hHv, hHs]
    by_cases h0 : ∃ X ∈ Pk, R.clusterFactor (n * R.params.side) W₀ Yt₀ (glueLabel Yt₀ Yk ωt₀ v) X = 0
    · rw [if_pos h0, zero_mul]
      exact (if_pos h0).symm
    · rw [if_neg h0, ← ENNReal.ofReal_mul' (Real.exp_pos _).le]
      exact (if_neg h0).symm
  calc ∫⁻ u : A → R.labels.Ω, sliceWeightedIntegrand R lam qScore n V Y ω P (sliceLabel Z a bd o A B g u)
        ∂(Measure.pi fun _ => R.labels.μ)
      ≤ ∫⁻ u : A → R.labels.Ω, ENNReal.ofReal (Real.exp (E + c₁)) * Hv (fun z => u (e z))
          ∂(Measure.pi fun _ => R.labels.μ) := lintegral_mono hst
    _ = ENNReal.ofReal (Real.exp (E + c₁)) * ∫⁻ u : A → R.labels.Ω, Hv (fun z => u (e z))
          ∂(Measure.pi fun _ => R.labels.μ) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (Real.exp (E + c₁)) * ∫⁻ v : Yk → R.labels.Ω, Hv v
          ∂(Measure.pi fun _ => R.labels.μ) := by
        rw [lintegral_comp_equiv_pi R.labels.μ e Hv]
    _ ≤ ENNReal.ofReal (Real.exp (E + c₁)) * ENNReal.ofReal (Real.exp
          (-(R.coupling * R.params.κ * R.params.threshold ^ 2 *
              (((torusHotLumps R.params W₀).filter (· ⊆ Pk.biUnion id)).card : ℝ)) -
            R.params.κ₁ * R.coupling * R.params.threshold ^ 2 *
              (excessLength R.params (clusterRange R.coupling) (Pk.biUnion id) W₀ : ℝ))) := by
        gcongr
    _ = ENNReal.ofReal (Real.exp (E + c₁ + (-(R.coupling * R.params.κ * R.params.threshold ^ 2 *
              (((torusHotLumps R.params W₀).filter (· ⊆ Pk.biUnion id)).card : ℝ)) -
            R.params.κ₁ * R.coupling * R.params.threshold ^ 2 *
              (excessLength R.params (clusterRange R.coupling) (Pk.biUnion id) W₀ : ℝ)))) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith))

theorem lintegral_slice_le (hrow : R.HasExpansions) (hfit : R.params.Admissible) (hr8 : 8 * R.params.side ≤ R.range)
    (hr16 : 2 ^ 16 ≤ R.range) (hnear : R.range ≤ R.nextRange + 1) (hx : 0 ≤ R.coupling)
    (hnb : NearDensityBound R lam cE ClassCost)
    (hof : IsBlockTorusSide R.params n → ∀ (V : TorusField n) (q : CoarseState R n),
      IsHullState R.params R.nextRange V q.1 →
      (∀ X ∈ chainComponents R.nextRange q.1, coarseFactor V q X ≠ 0) → (hotCaseGround R V q).IsOverState)
    (hset : ∀ G : GasGround R n, G.IsAdmissibleGround → G.groundSetting.IsAdmissible)
    (hfac : IsBlockTorusSide R.params n → ∀ (V : TorusField n) (q : CoarseState R n)
      (W : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω)
      (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n)
      (P : Finset (Finset (TorusSite n))),
      IsHullState R.params R.nextRange V q.1 → IsHullState R.params R.range W Yt →
      coarseStateOf R (hotCoreSites R V) W Yt ωt bad b = q →
      attachedSites R.params.side R.range bad Yt (hotCoreSites R V) =
        KeptRegion.clusterSites R.params.side bad Yt (hotCoreSites R V) →
      P ⊆ chainComponents R.nextRange q.1 → (∀ X ∈ chainComponents R.nextRange q.1, coarseFactor V q X ≠ 0) →
      ∏ X ∈ P, coarseFactor V q X ≤
        ∏ Xc ∈ (open Classical in (chainComponents R.range Yt).filter
            (· ⊆ attachedInBlocks R.params.side R.range bad Yt (hotCoreSites R V) (P.biUnion id))),
          R.clusterFactor (n * R.params.side) W Yt ωt Xc)
    (hn : IsBlockTorusSide R.params n) (hbn : IsBlockTorusSide R.params (n * R.params.side)) (V : TorusField n)
    (Y : Finset (TorusSite n)) (ω : Y → CoarseLabel R.labels.Ω R.params.side) (P : Finset (Finset (TorusSite n)))
    (hhull : IsHullState R.params R.nextRange V Y) (hP : P ⊆ chainComponents R.nextRange Y)
    (hoth : ∀ X ∈ chainComponents R.nextRange Y \ P, coarseFactorExpansion R n V Y ω X ≠ 0) (Mc : ℝ)
    (hM : ∀ (ν : ↥(P.biUnion id) → CoarseLabel R.labels.Ω R.params.side) (W : TorusField (n * R.params.side))
      (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω)
      (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n),
      IsHullState R.params R.range W Yt →
      coarseStateOf R (hotCoreSites R V) W Yt ωt bad b = ⟨Y, glueLabel Y (P.biUnion id) ω ν⟩ →
      -R.coupling * (6 * R.params.κ * R.params.threshold ^ 2 *
          ((open Classical in (torusHotLumps R.params V).filter (· ⊆ P.biUnion id)).card : ℝ) +
        R.params.κ / 4 * R.params.threshold ^ 2 *
          (hotLumpsInAttached R.params R.range W bad Yt (hotCoreSites R V) (P.biUnion id) : ℝ) +
        cE * (badBlocksInAttached R.params R.range bad Yt (hotCoreSites R V) (P.biUnion id) : ℝ) +
        R.params.κ₁ * R.params.threshold ^ 2 *
          (lengthInAttached R.params R.range W bad Yt (hotCoreSites R V) (P.biUnion id) : ℝ)) +
      ClassCost * ((nearSites R.nextRange (P.biUnion id)).card : ℝ) ≤ Mc)
    (Z : Finset ↥(P.biUnion id)) (a : Z → Bool) (bd : Z → BlockBond R.params.side → Bool)
    (o : Z → BlockOffset R.params.side) (A : Finset (Z × BlockOffset R.params.side))
    (B : Finset (Z × BlockBond R.params.side)) (g : B → BlockAverages.UnitQuaternion) :
    ∫⁻ u : A → R.labels.Ω, priceIntegrand R lam n V Y ω P (sliceLabel Z a bd o A B g u)
        ∂(Measure.pi fun _ => R.labels.μ) ≤ ENNReal.ofReal (Real.exp Mc) := by
  classical
  simpa [sliceWeightedIntegrand] using
    (lintegral_slice_weighted_le (R := R) (lam := lam) (cE := cE) (ClassCost := ClassCost)
      0 (fun _ => 0) (fun _ => 0) (by
        intro m _ hm W Yt ωt Pc hW hPc hoth
        simpa using hrow.2.price m hm W Yt ωt Pc hW hPc hoth)
      hrow hfit hr8 hr16 hnear hx hnb hof hset hfac hn hbn V Y ω P hhull hP hoth Mc hM Z a bd o A B g (by intro u; simp))
end Slice
end ComponentPrice
set_option maxHeartbeats 1600000 in
open ComponentPrice in
theorem componentPriceBound_proof (hLab : SliceBoundStatement)
    (hDens : DensitySumNearComponentsBound) (hPot : NearPotentialLeEnergy)
    (hint : LocalIntegralLeBallVolume) (hE : StepEnergy.EnergyNearPieceBound)
    (hSize : ActivityNearLevelShare) (hgas : LogPartitionEqSumDensities)
    (hsh : LevelShareBounded) (hfl : StepFloors.EventuallyFloorConditions)
    (hA : coarseStateGasStatement) (hB : HullStateIsHotCase) (hH : HotGroundIsOverState)
    (hC : StepFactors.AttachedUnionFactorBound)
    (hD : TrivialFieldColdGround) : ComponentPriceBound := by
  classical
  obtain ⟨rDe, hrDe, HDe⟩ := hDens
  obtain ⟨rSz, hrSz, HSz⟩ := hSize
  obtain ⟨rg, hrg, Hg⟩ := hgas
  obtain ⟨rA, hrA, HA⟩ := hA
  refine ⟨fun c => min (rDe c) (min (rSz c) (min (rg c) (rA c))),
    fun c => lt_min (hrDe c) (lt_min (hrSz c) (lt_min (hrg c) (hrA c))), ?_⟩
  intro T hT hrt
  have hrtDe : T.rt ≤ rDe T.toChainParameters := hrt.trans (min_le_left _ _)
  have hrtSz : T.rt ≤ rSz T.toChainParameters := hrt.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrtg : T.rt ≤ rg T.toChainParameters :=
    hrt.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hrtA : T.rt ≤ rA T.toChainParameters :=
    hrt.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨Cd, yd, hCd, Fd⟩ := HDe T hT hrtDe
  obtain ⟨Cp, yp, hCp, Fp⟩ := hPot T hT
  obtain ⟨Cg, cg, hcg, yE, FE⟩ := hE T hT
  obtain ⟨Ca, ya, hCa, Fa⟩ := HSz T hT hrtSz
  obtain ⟨yG, FG⟩ := Hg T hT hrtg
  obtain ⟨yA, FA⟩ := HA T hT hrtA
  obtain ⟨Ash, hAsh, FS⟩ := hsh T hT
  obtain ⟨yB, FB⟩ := hB T hT
  obtain ⟨yC, FC⟩ := hC T hT
  obtain ⟨yD, FD⟩ := hD T hT
  obtain ⟨yF, FF⟩ := hfl T hT (max Cg 1) cg (lt_of_lt_of_le one_pos (le_max_right _ _)) hcg
  have hBpos : 1 ≤ T.B := hT.B_ge
  set lc : ℕ := blockDataCount T.side with hlc
  set CE : ℝ := Cd + Cp + 4 * (T.side : ℝ) ^ 4 * |Real.log (liePointBallVolume T.ballRadius)| + 2 +
    2 * T.B * Ash + 2 * Ca + |Real.log (lc : ℝ)| with hCE
  refine ⟨CE, max (max (max yd yp) (max yE ya)) (max (max yG yA) (max (max yB yC) (max yD (max yF
    (max T.floorMin (max 3 (((8 * T.side + 2 ^ 16 : ℕ) : ℝ) ^ 100))))))), by positivity, ?_⟩
  intro y hy R hOn hforms hx'eq hmv n _ hn V Y ω P hhull hP hoth M hM
  have hlet := hOn.params_eq
  have hxy := hOn.le_coupling
  have hrow := hOn.isStep.1
  simp only [max_le_iff] at hy
  obtain ⟨⟨⟨ad, ap⟩, aE, aa⟩, ⟨aG, aA⟩, ⟨aB, aC⟩, aD, aF, a0, a3, aBig⟩ := hy
  have hxF := FF R.coupling (aF.trans hxy)
  have hBe : R.params.B = T.B := by rw [hlet]; rfl
  have hLe : R.params.side = T.side := by rw [hlet]; rfl
  have hmv' : |R.nextCoupling - R.coupling| ≤ 2 * T.B := by rw [← hBe]; exact hmv
  have hStable := hxF.stable_nearby.2 R.nextCoupling hmv'
  have hx3 : (3 : ℝ) ≤ R.coupling := a3.trans hxy
  have hbig : 8 * T.side + 2 ^ 16 ≤ R.range := le_clusterRange_of_pow_le _ (aBig.trans hxy)
  have hfit : R.params.Admissible := hlet ▸ hT.fits y a0
  have hr8 : 8 * R.params.side ≤ R.range := by rw [hLe]; omega
  have hr16 : 2 ^ 16 ≤ R.range := by omega
  have hlog1 : 1 ≤ Real.log R.coupling := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hsmall : R.coupling ^ Cg * Real.exp (-(cg * R.range)) ≤ 1 := by
    have h1 := hxF.stretched_tail.1
    have h2 : R.coupling ^ Cg ≤ R.coupling ^ (max Cg 1) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_left _ _)
    have h3 : (1 : ℝ) ≤ max Cg 1 := le_max_right _ _
    have h4 : 0 < Real.exp (-(cg * R.range)) := Real.exp_pos _
    have h5 : (0 : ℝ) < R.coupling ^ (max Cg 1) := Real.rpow_pos_of_pos (by linarith) _
    have h6 : R.coupling ^ (max Cg 1) * Real.exp (-(cg * R.range)) ≤
        max Cg 1 * R.coupling ^ (max Cg 1) * Real.exp (-(cg * R.range)) := by
      have := mul_le_mul_of_nonneg_right h3 (mul_pos h5 h4).le
      nlinarith
    have h7 : Real.exp (-(R.coupling ^ ((1 : ℝ) / 200))) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have : 0 ≤ R.coupling ^ ((1 : ℝ) / 200) := by positivity
      linarith
    calc _ ≤ R.coupling ^ (max Cg 1) * Real.exp (-(cg * R.range)) := mul_le_mul_of_nonneg_right h2 h4.le
      _ ≤ _ := h6
      _ ≤ _ := h1
      _ ≤ 1 := h7
  have hch : 0 ≤ T.gasRate := by
    have h1 := hT.cE_pos
    have h2 := hT.κ_pos
    have h3 := hT.σ_pos
    have h4 : 0 ≤ T.κ₁ := by
      unfold ParameterAssignment.κ₁
      exact le_min (by positivity) (by positivity)
    unfold ParameterAssignment.gasRate
    refine mul_nonneg (by positivity) (le_min h1.le (le_min (by positivity) (by positivity)))
  have hset : ∀ (n : ℕ) [NeZero n] (G : GasGround R n), G.IsAdmissibleGround → G.groundSetting.IsAdmissible :=
    fun n _ G hG => (FA y aA R hOn hStable.2.1 n G hG).1
  have hof : ∀ (n : ℕ) [NeZero n], IsBlockTorusSide R.params n → ∀ (V : TorusField n) (q : CoarseState R n),
      IsHullState R.params R.nextRange V q.1 →
      (∀ X ∈ chainComponents R.nextRange q.1, coarseFactor V q X ≠ 0) → (hotCaseGround R V q).IsOverState :=
    fun n _ hb V q hh hΦ => by
      have hhot := FB y aB R hOn hforms n hb V q hh hΦ
      exact hH R hforms n V q hhot (hset n _ (Or.inr hhot))
  have hnb := nearDensityBound_of hT hOn a0 hmv' hr8 hr16 (by linarith) (by linarith) hint hCd.le hCp.le hCa.le
    hAsh.le
    (fun n _ hn s c hs hc hm K hK => Fd y ad R hOn n hn s c hs hc hm K hK)
    (fun n _ hn s c hs hc K hK Yk h1 h2 h3 η hη => Fp y ap R hOn n hn s c hs hc K hK Yk h1 h2 h3 η hη)
    (FE y aE R hOn) hsmall hof hset
    (fun n _ G hG Y => by
      have h := (FG y aG R hOn hStable.2.1 n G hG).2 Y
      refine ⟨h.1, h.2.trans (Real.exp_le_one_iff.mpr ?_)⟩
      have : 0 ≤ T.gasRate * R.coupling := mul_nonneg hch (by linarith)
      linarith)
    (fun n _ hn s hs Y => FS y R a0 hlet n hn s hs Y)
    (fun n _ hn s hs c Y hc hm ho => ((Fa y aa R hOn n hn s hs).1 c Y hc hm ho).1)
    (fun n _ hn => by
      have hd := FD y aD R hOn n hn
      refine ⟨Or.inl hd.1, fun Y => ?_⟩
      have hss := hset n _ (Or.inl hd.1)
      exact (Fa y aa R hOn n hn _ hss).2 hd.2.1 (hd.2.2.1 hss) hd.2.2.2.1 hd.2.2.2.2 Y)
  have hlcpos : 1 ≤ lc := by
    have hL : 0 < Fintype.card (BlockOffset T.side) := Fintype.card_pos
    exact show 0 < lc from by
      rw [hlc]
      unfold blockDataCount
      positivity
  have hρe : R.ballRadius = T.ballRadius := by
    unfold StepSetup.ballRadius ParameterAssignment.ballRadius
    rw [hlet]; rfl
  have hLr : (R.params.side : ℝ) = T.side := by rw [hLe]
  have hrR : (1 : ℝ) ≤ (R.range : ℝ) := by
    have : 1 ≤ R.range := by omega
    exact_mod_cast this
  have hclasscost := surplus_le (Cd := Cd) (Cp := Cp)
    (D := 4 * (T.side : ℝ) ^ 4 * |Real.log (liePointBallVolume T.ballRadius)|)
    (Bb := 2 * T.B * Ash) (Ca := Ca) (l := Real.log (lc : ℝ)) hCd.le hCp.le (by positivity) (by positivity) hCa.le
    hrR hlog1
  have hDe : 4 * (R.params.side : ℝ) ^ 4 * |Real.log (liePointBallVolume R.ballRadius)| =
      4 * (T.side : ℝ) ^ 4 * |Real.log (liePointBallVolume T.ballRadius)| := by
    rw [hLr, hρe]
  have hbn : IsBlockTorusSide R.params (n * R.params.side) := isBlockTorusSide_mul hfit hn
  have hM' : ∀ (ν : ↥(P.biUnion id) → CoarseLabel R.labels.Ω R.params.side) (W : TorusField (n * R.params.side))
      (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω)
      (bad : Finset (TorusBond (n * R.params.side))) (b' : BaseChoice R.params.side n),
      IsHullState R.params R.range W Yt →
      coarseStateOf R (hotCoreSites R V) W Yt ωt bad b' = ⟨Y, glueLabel Y (P.biUnion id) ω ν⟩ →
      -R.coupling * (6 * R.params.κ * R.params.threshold ^ 2 *
          ((open Classical in (torusHotLumps R.params V).filter (· ⊆ P.biUnion id)).card : ℝ) +
        R.params.κ / 4 * R.params.threshold ^ 2 *
          (hotLumpsInAttached R.params R.range W bad Yt (hotCoreSites R V) (P.biUnion id) : ℝ) +
        T.cE * (badBlocksInAttached R.params R.range bad Yt (hotCoreSites R V) (P.biUnion id) : ℝ) +
        R.params.κ₁ * R.params.threshold ^ 2 *
          (lengthInAttached R.params R.range W bad Yt (hotCoreSites R V) (P.biUnion id) : ℝ)) +
      ((Cd + Cp) * (R.range : ℝ) ^ 4 * Real.log R.coupling +
        4 * (R.params.side : ℝ) ^ 4 * |Real.log (liePointBallVolume R.ballRadius)| + 2 +
        2 * T.B * Ash + 2 * (Ca * Real.log R.coupling)) * ((nearSites R.nextRange (P.biUnion id)).card : ℝ) ≤
      M - Real.log (lc : ℝ) * ((nearSites R.nextRange (P.biUnion id)).card : ℝ) := by
    intro ν W Yt ωt bad b' hh hst
    have h := hM ν W Yt ωt bad b' hh hst
    unfold componentExponent at h
    rw [hDe]
    exact exponent_le_sub (by positivity) hclasscost h
  have hlab := hLab R.labels.Ω R.labels.μ R.params.side ↥(P.biUnion id) (priceIntegrand R T.lam n V Y ω P)
    (ENNReal.ofReal (Real.exp (M - Real.log (lc : ℝ) * ((nearSites R.nextRange (P.biUnion id)).card : ℝ))))
    (fun Z a bd o A B g =>
      lintegral_slice_le hrow hfit hr8 hr16 hStable.2.2.1 (by linarith) hnb (hof n) (hset n)
        (fun hb V q W Yt ωt bad b' P h1 h2 h3 h4 h5 h6 =>
          FC y aC R hOn n hb V q W Yt ωt bad b' P h1 h2 h3 h4 h5 h6)
        hn hbn V Y ω P hhull hP hoth _ hM' Z a bd o A B g)
  show ∫⁻ ν, priceIntegrand R T.lam n V Y ω P ν
      ∂(Measure.pi fun _ : ↥(P.biUnion id) => coarseLabelMeasure R.labels.μ R.params.side) ≤ _
  refine hlab.trans ?_
  have hlcE : blockDataCount R.params.side = lc := by rw [hlc, hLe]
  rw [hlcE]
  refine natPow_mul_ofReal_exp_le hlcpos ?_
  have hsub : P.biUnion id ⊆ nearSites R.nextRange (P.biUnion id) := by
    intro z hz
    simp only [nearSites, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨z, hz, ?_⟩
    rw [supDist_self]
    have h2 : R.range ≤ R.nextRange + 1 := hStable.2.2.1
    have : 0 < R.nextRange := by omega
    have h3 : (0 : ℝ) < (R.nextRange : ℝ) := by exact_mod_cast this
    simpa using (by positivity : (0 : ℝ) < (R.nextRange : ℝ) / 4)
  rw [Fintype.card_coe]
  exact_mod_cast Finset.card_le_card hsub
end YangMills.Construction.ClusterExpansionOfAStep
