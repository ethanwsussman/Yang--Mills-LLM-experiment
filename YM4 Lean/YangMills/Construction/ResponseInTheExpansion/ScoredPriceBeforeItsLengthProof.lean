import YangMills.Construction.ClusterExpansionOfAStep.PriceOfAClassBeforeItsLengthProof
import YangMills.Construction.ResponseInTheExpansion.ScoredPriceBeforeItsLength
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open ClusterExpansionOfAStep BlockAverages LumpContours ColdStepAtMirrorFrames StepSettings TorusLumps TorusFields StepGas
  KeptRegion RenormalizationStepParameters StepCosts StepEnergy StepFactors StepFloors ImageDensities SlicedLabels SliceStates
  BlockPlaces BlockOffsets WeightedResponses
namespace ComponentPrice
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem coordNorm_zero : coordNorm (0 : EuclideanSpace ℝ (Fin 3)) = 0 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.DeepCutoff.coordNorm_zero <;> assumption
theorem sum_blockActivity_le_of_localIntegral (s : ChartSetting R n) (N : Finset (TorusSite n))
    (hρ : 0 < R.ballRadius) (hp : ColdStepAtMirrorFrames.IsCutoff R.ballRadius R.barrierFn)
    (hint : LocalIntegralLeBallVolume)
    (S B₅ B₆ B₇ Sφ A Lk : ℝ) (hpos : 0 < s.localIntegral N)
    (h5 : S ≤ Real.log (s.localIntegral N) + B₅)
    (h6 : ∀ η : FreeCoords s.free, s.InBalls η →
      -(s.localPotential N fun b => η b.1) ≤ -(R.coupling * s.energyNear N η) + Sφ + B₆)
    (hE : ∀ η : FreeCoords s.free, s.InBalls η →
      R.coupling * A - B₇ ≤ R.coupling * (s.energyNear N η + Lk)) :
    S ≤ B₅ + ((s.freeNear N).card : ℝ) * |Real.log (liePointBallVolume R.ballRadius)| + Sφ + B₆ + B₇ -
      R.coupling * A + R.coupling * Lk := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ComponentPrice.sum_blockActivity_near_le <;> assumption
theorem sum_le_of_blockwise_bounds {ι : Type} [DecidableEq ι] (Near N : Finset ι) (hsub : N ⊆ Near)
    (ζ g a ζ₁ g₁ : ι → ℝ) (x x' Bm A c : ℝ) (hx' : |x' - x| ≤ Bm)
    (hg : ∀ z, g z ≤ 1) (hg₁ : ∀ z, 0 ≤ g₁ z) (hz₁ : ∀ z, |ζ₁ z| ≤ c)
    (ha : ∀ z, 0 ≤ a z ∧ a z ≤ A) (hoff : ∀ z ∈ Near \ N, |ζ z + x * a z| ≤ c) :
    ∑ z ∈ Near, (ζ z + g z + x' * a z - (ζ₁ z + g₁ z)) ≤
      ∑ z ∈ N, ζ z + x * ∑ z ∈ N, a z + (Near.card : ℝ) * (1 + Bm * A + 2 * c) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ComponentPrice.sum_near_le_of_bounds <;> assumption
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
theorem torusHotSites_subset_hotCoreSites (V : TorusField n) : torusHotSites R.params V ⊆ hotCoreSites R V := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ComponentPrice.torusHotSites_subset_hotCoreSites <;> assumption
theorem card_freeNear_le (s : ChartSetting R n) (N : Finset (TorusSite n)) (hodd : Odd R.params.side) :
    ((s.freeNear N).card : ℝ) ≤ 4 * (R.params.side : ℝ) ^ 4 * (N.card : ℝ) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ComponentPrice.card_freeNear_le <;> assumption
theorem nearDensityBound_of_estimates {T : ParameterAssignment} {y : ℝ} {R : StepSetup} (hT : T.Admissible)
    (hR : R.OnParameters T y)
    (hy0 : T.floorMin ≤ y) (hmv : |R.nextCoupling - R.coupling| ≤ 2 * T.B) (hr8 : 8 * R.params.side ≤ R.range)
    (hr16 : 2 ^ 16 ≤ R.range)
    (hx : 1 ≤ R.coupling) (hlog : 0 ≤ Real.log R.coupling)
    (hint : LocalIntegralLeBallVolume) {C5 C6 C8 A Cg cg : ℝ} (hC5 : 0 ≤ C5) (hC6 : 0 ≤ C6) (hC8 : 0 ≤ C8)
    (hA : 0 ≤ A)
    (h5 : ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n → ∀ (s : ChartSetting R n) (c : SettingCore R n), s.IsAdmissible →
      s.IsCoreOf c → s.IsMarked c → ∀ K ⊆ s.storedComponents c,
        0 < s.localIntegral (blocksNear R.params.side R.range (K.biUnion id)) ∧
        |∑ Y ∈ blocksNear R.params.side R.range (K.biUnion id), s.blockActivity T.lam Y -
            Real.log (s.localIntegral (blocksNear R.params.side R.range (K.biUnion id)))| ≤
          C5 * (R.range : ℝ) ^ 4 * Real.log R.coupling *
            ((blocksNear R.params.side R.range (K.biUnion id)).card : ℝ))
    (h6 : ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n → ∀ (s : ChartSetting R n) (c : SettingCore R n), s.IsAdmissible →
      s.IsCoreOf c →
      ∀ K ⊆ s.storedComponents c, ∀ Yk : Finset (TorusSite (n * R.params.side)), Yk ⊆ s.support →
        Yk ⊆ K.biUnion id →
        (∀ z ∈ s.support \ Yk, ∀ y ∈ sitesInBlocks R.params.side (blocksNear R.params.side R.range (K.biUnion id)),
          (R.range : ℝ) / 4 ≤ supDist y z) →
        ∀ η : FreeCoords s.free, s.InBalls η →
          -(s.localPotential (blocksNear R.params.side R.range (K.biUnion id)) fun b => η b.1) ≤
            -(R.coupling * s.energyNear (blocksNear R.params.side R.range (K.biUnion id)) η) +
              ∑ z ∈ nearSites R.range Yk, R.siteDensity (n * R.params.side) z (s.field 0) s.support s.labelling +
              C6 * (R.range : ℝ) ^ 4 * Real.log R.coupling *
                ((blocksNear R.params.side R.range (K.biUnion id)).card : ℝ))
    (hEn : EnergyNearPieceAt R T.cE Cg cg) (hsmall : R.coupling ^ Cg * Real.exp (-(cg * R.range)) ≤ 1)
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
        |s.blockActivity T.lam Y + R.coupling * levelShare R.params.coupling R.params.side (R.depth + 1)
          s.region Y s.coarse| ≤ C8 * Real.log R.coupling)
    (hcold : ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n → (coldCaseGround R (trivialField n)).IsAdmissibleGround ∧
      ∀ Y : TorusSite n,
      |(coldCaseGround R (trivialField n)).groundSetting.blockActivity T.lam Y| ≤ C8 * Real.log R.coupling) :
    NearDensityBound R T.lam T.cE ((C5 + C6) * (R.range : ℝ) ^ 4 * Real.log R.coupling +
      4 * (R.params.side : ℝ) ^ 4 * |Real.log (liePointBallVolume R.ballRadius)| + 2 + 2 * T.B * A +
      2 * (C8 * Real.log R.coupling)) := by
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
  have hd : KeptPartData R.params.side R.range R.nextRange G.recordedBad G.groundSetting.support
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
  obtain ⟨K', hK'sub, hK'⟩ := exists_clusters_eq_attachedInBlocks hd
  set N := blocksNear R.params.side R.range K with hNdef
  set Yk := componentsWithin R.params.side R.range G.groundSetting.support K with hYkdef
  set Near := nearSites R.nextRange (P.biUnion id) with hNeardef
  have hNsub : N ⊆ Near := fun Y hY => mem_nearSites_of_mem_blocksNear hd hY
  have e5 := h5 n hn₀ G.groundSetting G.settingCore hs hG.isCore hG.isMarked K' hK'sub
  rw [hK'] at e5
  obtain ⟨hIpos, hI5⟩ := e5
  have h5' : ∑ Y ∈ N, G.groundSetting.blockActivity T.lam Y ≤ Real.log (G.groundSetting.localIntegral N) +
      C5 * (R.range : ℝ) ^ 4 * Real.log R.coupling * (N.card : ℝ) := by
    have := (abs_le.mp hI5).2
    linarith
  have h6' : ∀ η : FreeCoords G.groundSetting.free, G.groundSetting.InBalls η →
      -(G.groundSetting.localPotential N fun b => η b.1) ≤ -(R.coupling * G.groundSetting.energyNear N η) +
        ∑ w ∈ nearSites R.range Yk, R.siteDensity (n * R.params.side) w G.groundSetting.fine
          G.groundSetting.support G.groundSetting.labelling +
        C6 * (R.range : ℝ) ^ 4 * Real.log R.coupling * (N.card : ℝ) := by
    intro η hη
    have := h6 n hn₀ G.groundSetting G.settingCore hs hG.isCore K' hK'sub Yk
      (componentsWithin_subset_support hd)
      (by rw [hK']; exact componentsWithin_subset_attached hd)
      (fun z hz w hw => by
        rw [hK'] at hw
        exact quarter_le_supDist hd (Finset.mem_sdiff.mp hz).1 (Finset.mem_sdiff.mp hz).2 hw)
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
      (Or.inr ⟨P, hd.subset_components, rfl⟩) hη
      (fun b hb _ => hG.bad_far b hb)
  have e0 := sum_blockActivity_le_of_localIntegral G.groundSetting N hρ hcut hint _ _ _ _ _ _ _ hIpos h5' h6' hE'
  obtain ⟨hG₁, hz₁⟩ := hcold n hn₀
  have hnear := sum_le_of_blockwise_bounds Near N hNsub (fun z => G.groundSetting.blockActivity T.lam z)
    (fun z => G.blockDensity z)
    (fun z => levelShare R.params.coupling R.params.side (R.depth + 1) G.region z G.coarse)
    (fun z => (coldCaseGround R (trivialField n)).groundSetting.blockActivity T.lam z)
    (fun z => (coldCaseGround R (trivialField n)).blockDensity z)
    R.coupling R.nextCoupling (2 * T.B) A (C8 * Real.log R.coupling) hmv
    (fun z => (hgas n G (Or.inr hG.isHot) z).2)
    (fun z => (hgas n _ hG₁ z).1) hz₁ (fun z => hsh n hn₀ G.groundSetting hs z)
    (fun z hz => by
      obtain ⟨hz1, hz2⟩ := Finset.mem_sdiff.mp hz
      refine hoff n hn₀ G.groundSetting hs G.settingCore z hG.isCore hG.isMarked ?_
      intro Z hZ w hw u hu
      have hZ' : Z ∈ storedBlocks R.params.side R.range G.recordedBad G.groundSetting.support
          (hotCoreSites R V) := by
        have h1 : (G.groundSetting.storedComponents G.settingCore).biUnion id =
            attachedSites R.params.side R.range G.recordedBad G.groundSetting.support (hotCoreSites R V) := by
          rw [hd.attached_eq]
          exact biUnion_chainComponents
        unfold ChartSetting.storedBlockSet at hZ
        rw [h1] at hZ
        exact hZ
      exact eighth_lt_supDist hd hz1 hz2 hZ' hw hu)
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
      refine (mem_attachedInBlocks_iff hd).mpr ⟨?_, hl2 hb⟩
      unfold _root_.YangMills.Construction.KeptRegion.clusterSites
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
  have hb5 : C5 * (R.range : ℝ) ^ 4 * Real.log R.coupling * (N.card : ℝ) ≤
      C5 * (R.range : ℝ) ^ 4 * Real.log R.coupling * (Near.card : ℝ) :=
    mul_le_mul_of_nonneg_left hNR (by positivity)
  have hb6 : C6 * (R.range : ℝ) ^ 4 * Real.log R.coupling * (N.card : ℝ) ≤
      C6 * (R.range : ℝ) ^ 4 * Real.log R.coupling * (Near.card : ℝ) :=
    mul_le_mul_of_nonneg_left hNR (by positivity)
  have hb7 : R.coupling ^ Cg * Real.exp (-(cg * R.range)) * (N.card : ℝ) ≤ (Near.card : ℝ) :=
    (mul_le_mul_of_nonneg_right hsmall hN0).trans (by linarith)
  have hcoef : 0 ≤ 6 * R.params.κ * R.params.threshold ^ 2 := by positivity
  have h6x : R.coupling * (6 * R.params.κ * R.params.threshold ^ 2 *
        (((open Classical in (torusHotLumps R.params V).filter (· ⊆ P.biUnion id)).card : ℕ) : ℝ)) ≤
      R.coupling * (6 * R.params.κ * R.params.threshold ^ 2 *
        ((G.groundSetting.coarseLumpsInPiece G.settingCore K).card : ℝ)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htop hcoef) hx0
  have hhk : (hotLumpsInAttached R.params R.range G.groundSetting.fine G.recordedBad G.groundSetting.support
      (hotCoreSites R V) (P.biUnion id) : ℝ) = ((G.groundSetting.lumpsInPiece K).card : ℝ) := rfl
  have hbk : (badBlocksInAttached R.params R.range G.recordedBad G.groundSetting.support (hotCoreSites R V)
      (P.biUnion id) : ℝ) = ((badBlocksOff R.params.side G.recordedBad (hotCoreSites R V) K).card : ℝ) := rfl
  rw [hhk, hbk]
  have hsum : R.coupling * ∑ Y ∈ N, levelShare R.params.coupling R.params.side (R.depth + 1) G.region Y G.coarse =
      R.coupling * ∑ Y ∈ N, levelShare R.params.coupling R.params.side (R.depth + 1) G.region Y
        G.groundSetting.coarse := rfl
  have hfinal : ((C5 + C6) * (R.range : ℝ) ^ 4 * Real.log R.coupling +
      4 * (R.params.side : ℝ) ^ 4 * |Real.log (liePointBallVolume R.ballRadius)| + 2 + 2 * T.B * A +
      2 * (C8 * Real.log R.coupling)) * (Near.card : ℝ) =
      C5 * (R.range : ℝ) ^ 4 * Real.log R.coupling * (Near.card : ℝ) +
        C6 * (R.range : ℝ) ^ 4 * Real.log R.coupling * (Near.card : ℝ) +
        4 * (R.params.side : ℝ) ^ 4 * |Real.log (liePointBallVolume R.ballRadius)| * (Near.card : ℝ) +
        (Near.card : ℝ) +
        (Near.card : ℝ) * (1 + 2 * T.B * A + 2 * (C8 * Real.log R.coupling)) := by ring
  rw [hfinal]
  simp only [mul_add] at e0 hnear ⊢
  linarith
theorem le_clusterRange_of_pow_le {x : ℝ} (A : ℕ) (hx : (A : ℝ) ^ 100 ≤ x) : A ≤ clusterRange x := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.NearPotentialBound.le_clusterRange_of_pow_le <;> assumption
theorem sum_coeffs_le_mul {C5 C6 D Bb C8 l r lg : ℝ} (hC5 : 0 ≤ C5) (hC6 : 0 ≤ C6) (hD : 0 ≤ D) (hBb : 0 ≤ Bb)
    (hC8 : 0 ≤ C8) (hr : 1 ≤ r) (hlg : 1 ≤ lg) :
    ((C5 + C6) * r ^ 4 * lg + D + 2 + Bb + 2 * (C8 * lg)) + l ≤
      (C5 + C6 + D + 2 + Bb + 2 * C8 + |l|) * r ^ 8 * lg := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ComponentPrice.surplus_le <;> assumption
theorem exponent_shift {a ClassCost l CE' nR M : ℝ} (hn : 0 ≤ nR) (hb : ClassCost + l ≤ CE') (h : a + CE' * nR ≤ M) :
    a + ClassCost * nR ≤ M - l * nR := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ComponentPrice.exponent_le_sub <;> assumption
theorem natPow_mul_ofReal_exp_le {lc k : ℕ} (hlc : 1 ≤ lc) {nR M : ℝ} (hk : (k : ℝ) ≤ nR) :
    ((lc ^ k : ℕ) : ENNReal) * ENNReal.ofReal (Real.exp (M - Real.log (lc : ℝ) * nR)) ≤
      ENNReal.ofReal (Real.exp M) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ComponentPrice.natPow_mul_ofReal_exp_le <;> assumption
theorem isBlockTorusSide_mul_side {R : StepSetup} {n : ℕ} (hfit : R.params.Admissible)
    (hn : IsBlockTorusSide R.params n) :
    IsBlockTorusSide R.params (n * R.params.side) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ComponentPrice.isBlockTorusSide_mul <;> assumption
theorem coarseFactor_congr {V : TorusField n} {q q' : CoarseState R n} {X : Finset (TorusSite n)}
    (h : q.restrict X = q'.restrict X) :
    coarseFactor V q X = coarseFactor V q' X := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ComponentPrice.coarseFactor_congr <;> assumption
theorem coarseFactorExpansion_eq (V : TorusField n) (Y : Finset (TorusSite n))
    (ω : Y → CoarseLabel R.labels.Ω R.params.side) (X : Finset (TorusSite n)) :
    coarseFactorExpansion R n V Y ω X = coarseFactor V (⟨Y, ω⟩ : CoarseState R n) X := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ComponentPrice.coarseFactorExpansion_eq <;> assumption
theorem stateDensity_eq (lam : ℝ) (z : TorusSite n) (V : TorusField n) (Y : Finset (TorusSite n))
    (ω : Y → CoarseLabel R.labels.Ω R.params.side) :
    R.stateDensity lam n z V Y ω = groundDensity R (hotCaseGround R V (⟨Y, ω⟩ : CoarseState R n)) lam z := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ComponentPrice.stateDensity_eq <;> assumption
theorem sigma_mk_eq_of_forall {α : Type} {Ω : Type} {Y₁ Y₂ : Finset α} {f : Y₁ → Ω} {g : Y₂ → Ω}
    (hY : Y₁ = Y₂)
    (h : ∀ z (h₁ : z ∈ Y₁) (h₂ : z ∈ Y₂), f ⟨z, h₁⟩ = g ⟨z, h₂⟩) :
    (⟨Y₁, f⟩ : Σ Y : Finset α, (Y → Ω)) = ⟨Y₂, g⟩ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HotGround.sigma_mk_eq_of_eq <;> assumption
theorem restrict_glueState_of_disjoint {Y YP X : Finset (TorusSite n)}
    (ω : Y → CoarseLabel R.labels.Ω R.params.side) (ν : YP → CoarseLabel R.labels.Ω R.params.side)
    (hX : Disjoint X YP) :
    (glueState ω ν).restrict X = CoarseState.restrict (⟨Y, ω⟩ : CoarseState R n) X := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ComponentPrice.restrict_glueState_of_disjoint <;> assumption
theorem lintegral_pi_comp_equiv {ι κ Ω : Type} [Fintype ι] [Fintype κ] [MeasurableSpace Ω] (μ : Measure Ω)
    [SigmaFinite μ] (e : κ ≃ ι) (Gf : (κ → Ω) → ENNReal) :
    ∫⁻ u : ι → Ω, Gf (fun z => u (e z)) ∂(Measure.pi fun _ => μ) = ∫⁻ v, Gf v ∂(Measure.pi fun _ => μ) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ComponentPrice.lintegral_comp_equiv_pi <;> assumption
def componentPriceIntegrand (R : StepSetup) (lam : ℝ) (n : ℕ) [NeZero n] (V : TorusField n)
    (Y : Finset (TorusSite n))
    (ω : Y → CoarseLabel R.labels.Ω R.params.side) (P : Finset (Finset (TorusSite n)))
    (ν : ↥(P.biUnion id) → CoarseLabel R.labels.Ω R.params.side) :
    ENNReal :=
  open Classical in
  if ∃ X ∈ P, coarseFactorExpansion R n V Y (glueLabel Y (P.biUnion id) ω ν) X = 0 then 0 else
    ENNReal.ofReal ((∏ X ∈ P, coarseFactorExpansion R n V Y (glueLabel Y (P.biUnion id) ω ν) X) *
      Real.exp (∑ z ∈ Finset.univ.filter (fun z : TorusSite n =>
          ∃ u ∈ P.biUnion id, (supDist z u : ℝ) < (R.nextRange : ℝ) / 4),
        R.stateDensity lam n z V Y (glueLabel Y (P.biUnion id) ω ν)))
def scoredPriceIntegrand (R : StepSetup) (lam s₁ : ℝ) (s : R.labels.Ω → ℝ) (n : ℕ) [NeZero n]
    (V : TorusField n) (Y : Finset (TorusSite n))
    (ω : Y → CoarseLabel R.labels.Ω R.params.side) (P : Finset (Finset (TorusSite n)))
    (ν : ↥(P.biUnion id) → CoarseLabel R.labels.Ω R.params.side) :
    ENNReal :=
  componentPriceIntegrand R lam n V Y ω P ν *
    ENNReal.ofReal (Real.exp (∑ y : ↥(P.biUnion id), coarseLabelScore s₁ s (ν y)))
theorem sum_coarseLabelScore_sliceLabel {ι Ω : Type} {L : ℕ} [NeZero L] [Fintype ι] (s₁ : ℝ) (s : Ω → ℝ)
    (Z : Finset ι) (a : Z → Bool)
    (bd : Z → BlockBond L → Bool) (o : Z → BlockOffset L) (A : Finset (Z × BlockOffset L))
    (B : Finset (Z × BlockBond L)) (g : B → UnitQuaternion) (u : A → Ω) :
    ∑ y : ι, coarseLabelScore s₁ s (sliceLabel Z a bd o A B g u y) =
      s₁ * (Fintype.card ι : ℝ) + ∑ p : A, s (u p) := by
  classical
  set G : Z × BlockOffset L → ℝ := fun p => Sum.elim (fun _ => 0) s (fillOn A u p) with hG
  have h1 : ∀ y : ι, coarseLabelScore s₁ s (sliceLabel Z a bd o A B g u y) =
      s₁ + (if h : y ∈ Z then ∑ k, G (⟨y, h⟩, k) else 0) := by
    intro y
    by_cases h : y ∈ Z
    · simp only [sliceLabel, fillOn, h, dif_pos, coarseLabelScore, hG]
    · simp only [sliceLabel, fillOn, h, dif_neg, not_false_eq_true, coarseLabelScore, add_zero]
  have h2 : ∑ y : ι, (if h : y ∈ Z then ∑ k, G (⟨y, h⟩, k) else 0) = ∑ z : Z, ∑ k, G (z, k) := by
    have e : ∀ z : Z, ∑ k, G (z, k) =
        (fun y : ι => if h : y ∈ Z then ∑ k, G (⟨y, h⟩, k) else 0) z.1 := by
      intro z
      simp only [z.2, dif_pos]
    rw [Finset.sum_congr rfl fun z _ => e z,
      Finset.sum_coe_sort Z (fun y : ι => if h : y ∈ Z then ∑ k, G (⟨y, h⟩, k) else 0)]
    refine (Finset.sum_subset (Finset.subset_univ Z) fun y _ hy => ?_).symm
    simp only [hy, dif_neg, not_false_eq_true]
  have h3 : ∑ z : Z, ∑ k, G (z, k) = ∑ p : A, s (u p) := by
    rw [← Fintype.sum_prod_type' (f := fun z k => G (z, k))]
    have e : ∀ p : A, s (u p) = G p.1 := by
      intro p
      simp only [hG, fillOn, p.2, dif_pos, Sum.elim_inr]
    rw [Finset.sum_congr rfl fun p _ => e p, Finset.sum_coe_sort A G]
    refine (Finset.sum_subset (Finset.subset_univ A) fun p _ hp => ?_).symm
    simp only [hG, fillOn, hp, dif_neg, not_false_eq_true, Sum.elim_inl]
  rw [Finset.sum_congr rfl fun y _ => h1 y, Finset.sum_add_distrib, h2, h3, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_comm]
theorem coarseFactor_ne_zero_of_integrand_ne_zero {lam : ℝ} {V : TorusField n} {Y : Finset (TorusSite n)}
    {ω : Y → CoarseLabel R.labels.Ω R.params.side}
    {P : Finset (Finset (TorusSite n))} (hP : P ⊆ chainComponents R.nextRange Y)
    (hoth : ∀ X ∈ chainComponents R.nextRange Y \ P, coarseFactorExpansion R n V Y ω X ≠ 0)
    {ν : ↥(P.biUnion id) → CoarseLabel R.labels.Ω R.params.side}
    (hν : componentPriceIntegrand R lam n V Y ω P ν ≠ 0) :
    ∀ X ∈ chainComponents R.nextRange (glueState ω ν).1, coarseFactor V (glueState ω ν) X ≠ 0 := by
  classical
  intro X hX
  by_cases hXP : X ∈ P
  · intro h0
    apply hν
    unfold componentPriceIntegrand
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
theorem lintegral_slice_le (s₁ : ℝ) (s : R.labels.Ω → ℝ)
    (hsc : PriceBoundsScore R.params R.coupling R.labels R.clusterFactor R.siteDensity s)
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
    (g : B → UnitQuaternion) :
    ∫⁻ u : A → R.labels.Ω, scoredPriceIntegrand R lam s₁ s n V Y ω P (sliceLabel Z a bd o A B g u)
        ∂(Measure.pi fun _ => R.labels.μ) ≤
      ENNReal.ofReal (Real.exp (Mc + s₁ * (Fintype.card ↥(P.biUnion id) : ℝ))) := by
  classical
  simpa only [scoredPriceIntegrand, ClusterExpansionOfAStep.ComponentPrice.sliceWeightedIntegrand,
    componentPriceIntegrand, ClusterExpansionOfAStep.ComponentPrice.priceIntegrand] using
    (ClusterExpansionOfAStep.ComponentPrice.lintegral_slice_weighted_le
      s₁ s (coarseLabelScore s₁ s) hsc.price
      hrow hfit hr8 hr16 hnear hx hnb hof hset hfac hn hbn V Y ω P hhull hP hoth Mc hM Z a bd o A B g
      (fun u => sum_coarseLabelScore_sliceLabel s₁ s Z a bd o A B g u))
end Slice
end ComponentPrice
set_option maxHeartbeats 1600000 in
open ComponentPrice in
theorem scoredComponentPriceBound_proof (hLab : SlicedLabels.SliceBoundStatement)
    (h5 : StepSettings.DensitySumNearComponentsBound) (h6 : ClusterExpansionOfAStep.NearPotentialLeEnergy)
    (hint : ClusterExpansionOfAStep.LocalIntegralLeBallVolume) (hE : StepEnergy.EnergyNearPieceBound)
    (h72 : ClusterExpansionOfAStep.ActivityNearLevelShare) (hgas : StepGas.LogPartitionEqSumDensities)
    (hsh : ClusterExpansionOfAStep.LevelShareBounded) (hfl : StepFloors.EventuallyFloorConditions)
    (hA : StepSettings.coarseStateGasStatement) (hB : StepGas.HullStateIsHotCase)
    (hH : ClusterExpansionOfAStep.HotGroundIsOverState)
    (hC : StepFactors.AttachedUnionFactorBound)
    (hD : ClusterExpansionOfAStep.TrivialFieldColdGround) : scoredComponentPriceBound := by
  classical
  obtain ⟨r5, hr5, H5⟩ := h5
  obtain ⟨r72, hr72, H72⟩ := h72
  obtain ⟨rg, hrg, Hg⟩ := hgas
  obtain ⟨rA, hrA, HA⟩ := hA
  refine ⟨fun c => min (r5 c) (min (r72 c) (min (rg c) (rA c))),
    fun c => lt_min (hr5 c) (lt_min (hr72 c) (lt_min (hrg c) (hrA c))), ?_⟩
  intro T hT hrt s₁ hs₁
  have hrt5 : T.rt ≤ r5 T.toChainParameters := hrt.trans (min_le_left _ _)
  have hrt72 : T.rt ≤ r72 T.toChainParameters := hrt.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrtg : T.rt ≤ rg T.toChainParameters :=
    hrt.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hrtA : T.rt ≤ rA T.toChainParameters :=
    hrt.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨C5, y5, hC5, F5⟩ := H5 T hT hrt5
  obtain ⟨C6, y6, hC6, F6⟩ := h6 T hT
  obtain ⟨Cg, cg, hcg, yE, FE⟩ := hE T hT
  obtain ⟨C8, y8, hC8, F8⟩ := H72 T hT hrt72
  obtain ⟨yG, FG⟩ := Hg T hT hrtg
  obtain ⟨yA, FA⟩ := HA T hT hrtA
  obtain ⟨Ash, hAsh, FS⟩ := hsh T hT
  obtain ⟨yB, FB⟩ := hB T hT
  obtain ⟨yC, FC⟩ := hC T hT
  obtain ⟨yD, FD⟩ := hD T hT
  obtain ⟨yF, FF⟩ := hfl T hT (max Cg 1) cg (lt_of_lt_of_le one_pos (le_max_right _ _)) hcg
  have hBpos : 1 ≤ T.B := hT.B_ge
  set lc : ℕ := blockDataCount T.side with hlc
  set CE : ℝ := C5 + C6 + 4 * (T.side : ℝ) ^ 4 * |Real.log (liePointBallVolume T.ballRadius)| + 2 +
    2 * T.B * Ash + 2 * C8 + |Real.log (lc : ℝ) + s₁| with hCE
  refine ⟨CE, max (max (max y5 y6) (max yE y8)) (max (max yG yA) (max (max yB yC) (max yD (max yF
    (max T.floorMin (max 3 (((8 * T.side + 2 ^ 16 : ℕ) : ℝ) ^ 100))))))), by positivity, ?_⟩
  intro y hy R hOn hforms hx'eq hmv s hsc n _ hn V Y ω P hhull hP hoth M hM
  have hlet := hOn.params_eq
  have hxy := hOn.le_coupling
  have hrow := hOn.isStep.1
  simp only [max_le_iff] at hy
  obtain ⟨⟨⟨a5, a6⟩, aE, a8⟩, ⟨aG, aA⟩, ⟨aB, aC⟩, aD, aF, a0, a3, aBig⟩ := hy
  have hxF := FF R.coupling (aF.trans hxy)
  have hBe : R.params.B = T.B := by rw [hlet]; rfl
  have hLe : R.params.side = T.side := by rw [hlet]; rfl
  have hmv' : |R.nextCoupling - R.coupling| ≤ 2 * T.B := by rw [← hBe]; exact hmv
  have y9 := hxF.stable_nearby.2 R.nextCoupling hmv'
  have hx3 : (3 : ℝ) ≤ R.coupling := a3.trans hxy
  have hbig : 8 * T.side + 2 ^ 16 ≤ R.range := _root_.YangMills.Construction.ResponseInTheExpansion.ComponentPrice.le_clusterRange_of_pow_le _ (aBig.trans hxy)
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
    fun n _ G hG => (FA y aA R hOn y9.2.1 n G hG).1
  have hof : ∀ (n : ℕ) [NeZero n], IsBlockTorusSide R.params n → ∀ (V : TorusField n) (q : CoarseState R n),
      IsHullState R.params R.nextRange V q.1 →
      (∀ X ∈ chainComponents R.nextRange q.1, coarseFactor V q X ≠ 0) → (hotCaseGround R V q).IsOverState :=
    fun n _ hb V q hh hΦ => by
      have hhot := FB y aB R hOn hforms n hb V q hh hΦ
      exact hH R hforms n V q hhot (hset n _ (Or.inr hhot))
  have hnb := nearDensityBound_of_estimates hT hOn a0 hmv' hr8 hr16 (by linarith) (by linarith) hint hC5.le
    hC6.le hC8.le hAsh.le
    (fun n _ hn s c hs hc hm K hK => F5 y a5 R hOn n hn s c hs hc hm K hK)
    (fun n _ hn s c hs hc K hK Yk h1 h2 h3 η hη => F6 y a6 R hOn n hn s c hs hc K hK Yk h1 h2 h3 η hη)
    (FE y aE R hOn) hsmall hof hset
    (fun n _ G hG Y => by
      have h := (FG y aG R hOn y9.2.1 n G hG).2 Y
      refine ⟨h.1, h.2.trans (Real.exp_le_one_iff.mpr ?_)⟩
      have : 0 ≤ T.gasRate * R.coupling := mul_nonneg hch (by linarith)
      linarith)
    (fun n _ hn s hs Y => FS y R a0 hlet n hn s hs Y)
    (fun n _ hn s hs c Y hc hm ho => ((F8 y a8 R hOn n hn s hs).1 c Y hc hm ho).1)
    (fun n _ hn => by
      have hd := FD y aD R hOn n hn
      refine ⟨Or.inl hd.1, fun Y => ?_⟩
      have hss := hset n _ (Or.inl hd.1)
      exact (F8 y a8 R hOn n hn _ hss).2 hd.2.1 (hd.2.2.1 hss) hd.2.2.2.1 hd.2.2.2.2 Y)
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
  have hclasscost := sum_coeffs_le_mul (C5 := C5) (C6 := C6)
    (D := 4 * (T.side : ℝ) ^ 4 * |Real.log (liePointBallVolume T.ballRadius)|)
    (Bb := 2 * T.B * Ash) (C8 := C8) (l := Real.log (lc : ℝ) + s₁) hC5.le hC6.le (by positivity) (by positivity)
    hC8.le hrR hlog1
  have hDe : 4 * (R.params.side : ℝ) ^ 4 * |Real.log (liePointBallVolume R.ballRadius)| =
      4 * (T.side : ℝ) ^ 4 * |Real.log (liePointBallVolume T.ballRadius)| := by
    rw [hLr, hρe]
  have hbn : IsBlockTorusSide R.params (n * R.params.side) := isBlockTorusSide_mul_side hfit hn
  have hM' : ∀ (ν : ↥(P.biUnion id) → CoarseLabel R.labels.Ω R.params.side) (W : TorusField (n * R.params.side))
      (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω)
      (bad : Finset (TorusBond (n * R.params.side)))
      (b' : BaseChoice R.params.side n), IsHullState R.params R.range W Yt →
      coarseStateOf R (hotCoreSites R V) W Yt ωt bad b' = ⟨Y, glueLabel Y (P.biUnion id) ω ν⟩ →
      -R.coupling * (6 * R.params.κ * R.params.threshold ^ 2 *
          ((open Classical in (torusHotLumps R.params V).filter (· ⊆ P.biUnion id)).card : ℝ) +
        R.params.κ / 4 * R.params.threshold ^ 2 *
          (hotLumpsInAttached R.params R.range W bad Yt (hotCoreSites R V) (P.biUnion id) : ℝ) +
        T.cE * (badBlocksInAttached R.params R.range bad Yt (hotCoreSites R V) (P.biUnion id) : ℝ) +
        R.params.κ₁ * R.params.threshold ^ 2 *
          (lengthInAttached R.params R.range W bad Yt (hotCoreSites R V) (P.biUnion id) : ℝ)) +
      ((C5 + C6) * (R.range : ℝ) ^ 4 * Real.log R.coupling +
        4 * (R.params.side : ℝ) ^ 4 * |Real.log (liePointBallVolume R.ballRadius)| + 2 +
        2 * T.B * Ash + 2 * (C8 * Real.log R.coupling)) * ((nearSites R.nextRange (P.biUnion id)).card : ℝ) ≤
      M - (Real.log (lc : ℝ) + s₁) * ((nearSites R.nextRange (P.biUnion id)).card : ℝ) := by
    intro ν W Yt ωt bad b' hh hst
    have h := hM ν W Yt ωt bad b' hh hst
    unfold componentExponent at h
    rw [hDe]
    exact exponent_shift (by positivity) hclasscost h
  have hsub : P.biUnion id ⊆ nearSites R.nextRange (P.biUnion id) := by
    intro z hz
    simp only [nearSites, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨z, hz, ?_⟩
    rw [supDist_self]
    have h2 : R.range ≤ R.nextRange + 1 := y9.2.2.1
    have : 0 < R.nextRange := by omega
    have h3 : (0 : ℝ) < (R.nextRange : ℝ) := by exact_mod_cast this
    simpa using (by positivity : (0 : ℝ) < (R.nextRange : ℝ) / 4)
  have hcard : (Fintype.card ↥(P.biUnion id) : ℝ) ≤ ((nearSites R.nextRange (P.biUnion id)).card : ℝ) := by
    rw [Fintype.card_coe]
    exact_mod_cast Finset.card_le_card hsub
  have hlab := hLab R.labels.Ω R.labels.μ R.params.side ↥(P.biUnion id)
    (scoredPriceIntegrand R T.lam s₁ s n V Y ω P)
    (ENNReal.ofReal (Real.exp (M - Real.log (lc : ℝ) * ((nearSites R.nextRange (P.biUnion id)).card : ℝ))))
    (fun Z a bd o A B g =>
      (lintegral_slice_le s₁ s hsc hrow hfit hr8 hr16 y9.2.2.1 (by linarith) hnb (hof n) (hset n)
        (fun hb V q W Yt ωt bad b' P h1 h2 h3 h4 h5 h6 =>
          FC y aC R hOn n hb V q W Yt ωt bad b' P h1 h2 h3 h4 h5 h6)
        hn hbn V Y ω P hhull hP hoth _ hM' Z a bd o A B g).trans
        (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by
          have := mul_le_mul_of_nonneg_left hcard hs₁
          linarith))))
  have hint' : (fun ν : ↥(P.biUnion id) → CoarseLabel R.labels.Ω R.params.side =>
      if ∃ X ∈ P, coarseFactorExpansion R n V Y (glueLabel Y (P.biUnion id) ω ν) X = 0 then (0 : ENNReal) else
        ENNReal.ofReal ((∏ X ∈ P, coarseFactorExpansion R n V Y (glueLabel Y (P.biUnion id) ω ν) X) *
          Real.exp (∑ z ∈ Finset.univ.filter (fun z : TorusSite n =>
              ∃ u ∈ P.biUnion id, (supDist z u : ℝ) < (R.nextRange : ℝ) / 4),
            R.stateDensity T.lam n z V Y (glueLabel Y (P.biUnion id) ω ν)) *
          Real.exp (∑ y : (P.biUnion id : Finset (TorusSite n)), coarseLabelScore s₁ s (ν y)))) =
      scoredPriceIntegrand R T.lam s₁ s n V Y ω P := by
    funext ν
    unfold scoredPriceIntegrand componentPriceIntegrand
    split_ifs with h0
    · rw [zero_mul]
    · rw [ENNReal.ofReal_mul' (Real.exp_pos _).le]
  rw [hint']
  refine hlab.trans ?_
  have hlcE : blockDataCount R.params.side = lc := by rw [hlc, hLe]
  rw [hlcE]
  refine _root_.YangMills.Construction.ResponseInTheExpansion.ComponentPrice.natPow_mul_ofReal_exp_le hlcpos ?_
  rw [Fintype.card_coe]
  exact_mod_cast Finset.card_le_card hsub
end YangMills.Construction.ResponseInTheExpansion
end
