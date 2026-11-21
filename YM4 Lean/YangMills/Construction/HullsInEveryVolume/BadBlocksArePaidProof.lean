import YangMills.Construction.ClusterExpansionOfAStep.AttachedClustersOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.FrameAgainstTheLeastFieldOfTheCut
import YangMills.Construction.ClusterExpansionOfAStep.PlaquettesUnderGaugesAndMoves
import YangMills.Construction.HoleBesideASecondHole.HotLumpsOfAStep
import YangMills.Construction.HoleBesideASecondHole.WhatAHoleSavesInTheBound
import YangMills.Construction.HullsInEveryVolume.BadBlocksArePaid
import YangMills.Construction.HullsInEveryVolume.LeastFieldOfACut
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.HullsInEveryVolume
open ClusterExpansionOfAStep WeightedResponses BlockAverages TorusFields TorusLumps TorusBalls StepSettings StepMarks RenormalizationStepParameters
  StepFrames HoleOnTori LumpContours TorusFrames ColdStepAtMirrorFrames
open StepCosts (chartCoord frameCoord)
private theorem minimalAction_nonneg_aux {F : BlockFrame} {a : ℝ} (ha : 0 ≤ a) (S : Finset F.Cell) :
    ∀ (j : ℕ) (X : F.GaugeField j), 0 ≤ minimalAction a S j X
  | 0, U => by
    unfold minimalAction BlockAverages.wilsonAction
    refine Finset.sum_nonneg fun p _ => ?_
    have h := sq_norm_unitQuaternion_sub_one (plaquetteHolonomy U p)
    nlinarith [sq_nonneg ‖((plaquetteHolonomy U p : UnitQuaternion) : ℍ[ℝ]) - 1‖]
  | j + 1, V => by
    refine Real.iInf_nonneg fun W => ?_
    refine add_nonneg (minimalAction_nonneg_aux ha S j W)
      (mul_nonneg ha (Finset.sum_nonneg fun c _ => ?_))
    unfold blockFit
    have h1 : (contourAverage W c * ((V c.1 c.2)⁻¹ : UnitQuaternion)).re ≤
        ‖contourAverage W c * ((V c.1 c.2)⁻¹ : UnitQuaternion)‖ := by
      have h2 : (contourAverage W c * ((V c.1 c.2)⁻¹ : UnitQuaternion)).re ^ 2 ≤
          ‖contourAverage W c * ((V c.1 c.2)⁻¹ : UnitQuaternion)‖ ^ 2 := by
        rw [sq ‖_‖, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
        nlinarith [sq_nonneg (contourAverage W c * ((V c.1 c.2)⁻¹ : UnitQuaternion)).imI,
          sq_nonneg (contourAverage W c * ((V c.1 c.2)⁻¹ : UnitQuaternion)).imJ,
          sq_nonneg (contourAverage W c * ((V c.1 c.2)⁻¹ : UnitQuaternion)).imK]
      exact (abs_le_of_sq_le_sq' h2 (norm_nonneg _)).2
    rw [norm_mul, norm_unitQuaternion, mul_one] at h1
    linarith
private theorem actionAtLevel_nonneg_aux {n : ℕ} [NeZero n] {a : ℝ} (ha : 0 ≤ a) (L : ℕ) :
    ∀ (t : ℕ) (S : Finset (TorusSite n)) (W : TorusField n), 0 ≤ actionAtLevel a L t S W
  | 0, _, W => Finset.sum_nonneg fun _ _ => plaquetteEnergy_nonneg W _ _ _
  | _ + 1, _, _ => minimalAction_nonneg_aux ha _ _ _
theorem badBlocksPaidByEnergy_holds (hF : FrameNearMinimizer) (hLF : minimizingFieldOfCutoff)
    (hTab : HoleSavingAtFixedParameters) (hH : hotLumpsOfStepStatement) : badBlocksPaidByEnergy := by
  classical
  intro Tb y hD hfit c hρ hcut hrf hgap n _ hB V W b bad hb hmark
  have hσ : 0 < (Tb.stepParameters y).threshold := hfit.σ_pos
  have hLn : (Tb.stepParameters y).side ∣ n := hB.1
  have hLge : 2 ^ 16 ≤ (Tb.stepParameters y).side := hfit.L_ge
  have hn₀ : 4096 ≤ (Tb.stepParameters y).n₀ := hfit.n₀_ge
  have h4096 : 4096 ≤ n := by
    have h1 := hB.2
    nlinarith
  have hn64 : 64 ≤ n := by omega
  have hNe : NeZero (n * (Tb.stepParameters y).side) :=
    ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne (Tb.stepParameters y).side)⟩
  have hmark' := hmark
  unfold markLaw at hmark'
  rw [if_pos ⟨hLn, hn64⟩] at hmark'
  by_cases hsub : bad ⊆ markedBonds c.toStepSetup (hotCoreSites c.toStepSetup V)
  swap
  · rw [if_neg hsub] at hmark'
    exact absurd rfl hmark'
  rw [if_pos hsub] at hmark'
  have hfar : ∀ e ∈ bad, 5 * ((Tb.stepParameters y).threshold / 64) / 8 <
      ‖((chartCoord (Tb.stepParameters y) V W e : imaginaryQuaternions) : ℍ[ℝ]) -
        ((frameCoord (Tb.stepParameters y) c.anchorRadius c.depth (clusterRange c.coupling / 2 ^ 11) V e :
          imaginaryQuaternions) : ℍ[ℝ])‖ := by
    intro e he
    by_contra hle
    push Not at hle
    apply hmark'
    unfold markProduct
    refine Finset.prod_eq_zero (hsub he) ?_
    rw [if_pos he]
    have hlt : ‖((chartCoord (Tb.stepParameters y) V W e : imaginaryQuaternions) : ℍ[ℝ]) -
        ((frameCoord (Tb.stepParameters y) c.anchorRadius c.depth (clusterRange c.coupling / 2 ^ 11) V e :
          imaginaryQuaternions) : ℍ[ℝ])‖ < (Tb.stepParameters y).threshold / 64 := by linarith
    have hm : bondMark c.toStepSetup V W e = 1 := by
      unfold bondMark cutoffFactor
      have hlt' : ‖((chartCoord c.toStepSetup.params V W e : imaginaryQuaternions) : ℍ[ℝ]) -
        ((frameCoord c.toStepSetup.params c.toStepSetup.anchorRadius c.toStepSetup.depth c.toStepSetup.frameReach V e :
          imaginaryQuaternions) : ℍ[ℝ])‖ < c.toStepSetup.ballRadius := hlt
      rw [if_pos hlt']
      have hz := hcut.vanish_small _ (norm_nonneg _) hle
      have hz' : c.toStepSetup.barrierFn ‖((chartCoord c.toStepSetup.params V W e : imaginaryQuaternions) : ℍ[ℝ]) -
        ((frameCoord c.toStepSetup.params c.toStepSetup.anchorRadius c.toStepSetup.depth c.toStepSetup.frameReach V e :
          imaginaryQuaternions) : ℍ[ℝ])‖ = 0 := hz
      rw [hz']
      simp
    rw [hm]
    ring
  set S : Finset (TorusSite n) :=
    Finset.univ \ TorusLumps.thickening lumpRange (torusHotSites (Tb.stepParameters y) V) with hS
  have hsit : IsStepSituation (Tb.stepParameters y) (clusterRange c.nextCoupling) V S
      (minimalHull (Tb.stepParameters y) (clusterRange c.nextCoupling) V) (Tb.stepParameters y).threshold :=
    Or.inl ⟨hB, rfl, rfl, rfl⟩
  obtain ⟨hleast, hchart⟩ := hLF (Tb.stepParameters y) Tb.δ₁ Tb.lam Tb.ρA Tb.σA Tb.cg Tb.N hfit hD.chain hD.σ_le
    c.depth (clusterRange c.nextCoupling) n V S _ (Tb.stepParameters y).threshold hsit
  set Wl := minimizingField (Tb.stepParameters y).coupling Tb.ρA (Tb.stepParameters y).side c.depth S V with hWl
  have hframes := (hF (Tb.stepParameters y) Tb.δ₁ Tb.lam Tb.ρA Tb.σA Tb.cg Tb.N hfit hD.chain hD.σ_le).2 c.depth
    (clusterRange c.coupling) (clusterRange c.nextCoupling) n V S _ (Tb.stepParameters y).threshold hrf hsit
  have hsv : HoleSavingBounds (Tb.stepParameters y) Tb.cE := (hTab Tb hD).2 y
  have hoff : awayFromLumps (∅ : Finset (Finset (TorusSite n))) = Finset.univ := by
    simp [awayFromLumps, TorusLumps.thickening]
  have hhotV : torusHotLumps (Tb.stepParameters y) V = topHotLumps (Tb.stepParameters y) Finset.univ V :=
    (hH (Tb.stepParameters y) n).2 hLn V
  have hS' : awayFromLumps (∅ : Finset (Finset (TorusSite n))) \
      TorusLumps.thickening lumpRange
        ((topHotLumps (Tb.stepParameters y) (awayFromLumps (∅ : Finset (Finset (TorusSite n)))) V).biUnion id) = S := by
    rw [hoff, ← hhotV]
    rfl
  obtain ⟨hW1, hW2, hW3, hW4⟩ := (hH (Tb.stepParameters y) n).1 W
  have hbs : sitesInBlocks (Tb.stepParameters y).side (Finset.univ : Finset (TorusSite n)) = Finset.univ := by
    ext x
    simp [mem_sitesInBlocks]
  have hbases : IsBaseChoice (Tb.stepParameters y).baseDepth
      (HoleOnTori.stepHotLumps (Tb.stepParameters y)
        (sitesInBlocks (Tb.stepParameters y).side (awayFromLumps (∅ : Finset (Finset (TorusSite n))))) W) b := by
    rw [hoff, ← hW4]
    exact (Finset.mem_filter.mp hb).2
  have hres := hsv.holed c.depth n hLn h4096 ∅ (by simp) V W Wl b
    (fun _ _ z hz => by simp [TorusLumps.thickening] at hz) (by rw [hS']; exact hleast)
    (fun _ _ z hz => by simp [TorusLumps.thickening] at hz) hbases
  unfold HoleSavingOnTorus at hres
  have hW4' := hW4
  rw [hbs] at hW4'
  rw [hS', hoff, hbs, ← hW4', ← hW2, ← hW3] at hres
  have hsubset : bad.image (fun e => parentBlock (Tb.stepParameters y).side e.1) ⊆
      chartDeviationSites (Tb.stepParameters y) ((Tb.stepParameters y).threshold / 128) S V W Wl := by
    intro Y hY
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hY
    obtain ⟨hcb, hoffC⟩ := Finset.mem_filter.mp (hsub he)
    have hC : parentBlock (Tb.stepParameters y).side e.1 ∉
        minimalHull (Tb.stepParameters y) (clusterRange c.nextCoupling) V := hoffC
    have hlarge := hrf.large
    have hnext : ∀ Z, supDist Z (parentBlock (Tb.stepParameters y).side e.1) ≤ 1 → Z ∈ S := by
      intro Z hZ
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => hC ?_⟩
      obtain ⟨x, hx, hdx⟩ := (mem_thickening _ _ _).mp h
      refine (mem_thickening _ _ _).mpr ⟨x, hx, ?_⟩
      have h3 := supDist_triangle (parentBlock (Tb.stepParameters y).side e.1) Z x
      rw [supDist_comm (parentBlock (Tb.stepParameters y).side e.1) Z] at h3
      have hr : lumpRange = 2 ^ 12 := rfl
      omega
    have hself : parentBlock (Tb.stepParameters y).side e.1 ∈ S := hnext _ (by rw [supDist_self]; omega)
    have hnb : supDist (parentBlock (Tb.stepParameters y).side (e.1 + TorusFields.unitStep (n * (Tb.stepParameters y).side) e.2))
        (parentBlock (Tb.stepParameters y).side e.1) ≤ 1 := by
      have h1 := supDist_parentBlock_le_div_add_one (Tb.stepParameters y).side
        (e.1 + TorusFields.unitStep (n * (Tb.stepParameters y).side) e.2) e.1
      have h2 := supDist_add_unitStep_le e.1 e.2
      rw [supDist_comm] at h2
      have h3 : supDist (e.1 + TorusFields.unitStep (n * (Tb.stepParameters y).side) e.2) e.1 / (Tb.stepParameters y).side = 0 :=
        Nat.div_eq_of_lt (by omega)
      omega
    refine Finset.mem_filter.mpr ⟨hself, e, ?_, rfl, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, mem_sitesInBlocks.mpr hself, mem_sitesInBlocks.mpr (hnext _ hnb)⟩
    · rw [hchart e]
      have hfr := (hframes e hcb hC).2
      have hρ' : c.anchorRadius = Tb.ρA := hρ
      have hfe := hfar e he
      rw [hρ'] at hfe
      have hgap' : ‖((frameCoord (Tb.stepParameters y) Tb.ρA c.depth (clusterRange c.coupling / 2 ^ 11) V e :
            imaginaryQuaternions) : ℍ[ℝ]) -
          ((minimizerCoord (Tb.stepParameters y).coupling Tb.ρA (Tb.stepParameters y).side c.depth S V e :
            imaginaryQuaternions) : ℍ[ℝ])‖ ≤ (Tb.stepParameters y).threshold / 512 := hfr.trans hgap
      have h3 : ((chartCoord (Tb.stepParameters y) V W e : imaginaryQuaternions) : ℍ[ℝ]) -
          ((frameCoord (Tb.stepParameters y) Tb.ρA c.depth (clusterRange c.coupling / 2 ^ 11) V e :
            imaginaryQuaternions) : ℍ[ℝ]) =
          (((chartCoord (Tb.stepParameters y) V W e : imaginaryQuaternions) : ℍ[ℝ]) -
            ((minimizerCoord (Tb.stepParameters y).coupling Tb.ρA (Tb.stepParameters y).side c.depth S V e :
              imaginaryQuaternions) : ℍ[ℝ])) -
          (((frameCoord (Tb.stepParameters y) Tb.ρA c.depth (clusterRange c.coupling / 2 ^ 11) V e :
              imaginaryQuaternions) : ℍ[ℝ]) -
            ((minimizerCoord (Tb.stepParameters y).coupling Tb.ρA (Tb.stepParameters y).side c.depth S V e :
              imaginaryQuaternions) : ℍ[ℝ])) := by abel
      rw [h3] at hfe
      have h4 := norm_sub_le (((chartCoord (Tb.stepParameters y) V W e : imaginaryQuaternions) : ℍ[ℝ]) -
          ((minimizerCoord (Tb.stepParameters y).coupling Tb.ρA (Tb.stepParameters y).side c.depth S V e :
            imaginaryQuaternions) : ℍ[ℝ]))
        (((frameCoord (Tb.stepParameters y) Tb.ρA c.depth (clusterRange c.coupling / 2 ^ 11) V e :
            imaginaryQuaternions) : ℍ[ℝ]) -
          ((minimizerCoord (Tb.stepParameters y).coupling Tb.ρA (Tb.stepParameters y).side c.depth S V e :
            imaginaryQuaternions) : ℍ[ℝ]))
      linarith
  have hcard : ((bad.image (fun e => parentBlock (Tb.stepParameters y).side e.1)).card : ℝ) ≤
      ((chartDeviationSites (Tb.stepParameters y) ((Tb.stepParameters y).threshold / 128) S V W Wl).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsubset
  have hcE : 0 ≤ Tb.cE := hD.cE_pos.le
  have ha : 0 ≤ (Tb.stepParameters y).coupling := by have := hfit.a_ge; linarith
  have hκ : 0 ≤ (Tb.stepParameters y).κ := hfit.κ_pos.le
  have hA : 0 ≤ actionAtLevel (Tb.stepParameters y).coupling (Tb.stepParameters y).side (c.depth + 1) S V :=
    actionAtLevel_nonneg_aux ha _ _ _ _
  have h1 : 0 ≤ 6 * (Tb.stepParameters y).κ * (Tb.stepParameters y).threshold ^ 2 *
      ((topHotLumps (Tb.stepParameters y) Finset.univ V).card : ℝ) := by positivity
  have h2 : 0 ≤ (Tb.stepParameters y).κ / 4 * (Tb.stepParameters y).threshold ^ 2 *
      ((torusHotLumps (Tb.stepParameters y) W).card : ℝ) := by positivity
  have h3 : Tb.cE * ((bad.image (fun e => parentBlock (Tb.stepParameters y).side e.1)).card : ℝ) ≤
      Tb.cE * ((chartDeviationSites (Tb.stepParameters y) ((Tb.stepParameters y).threshold / 128) S V W Wl).card : ℝ) :=
    mul_le_mul_of_nonneg_left hcard hcE
  have hbonds : bondsWithin (Finset.univ : Finset (TorusSite n)) = Finset.univ := by
    ext e
    simp [HoleOnTori.bondsWithin]
  have hfitsum : ∑ e ∈ bondsWithin (Finset.univ : Finset (TorusSite n)),
        HoleOnTori.bondFit (Tb.stepParameters y) (StepCosts.stepHotLumps (Tb.stepParameters y) W) W V b e =
      ∑ e : TorusBond n, StepCosts.bondFit (Tb.stepParameters y) W V b e := by
    rw [hbonds]
    rfl
  rw [hfitsum] at hres
  exact show Tb.cE * ((bad.image (fun e => parentBlock (Tb.stepParameters y).side e.1)).card : ℝ) ≤
      actionAtLevel (Tb.stepParameters y).coupling (Tb.stepParameters y).side c.depth
          (Finset.univ \ TorusLumps.thickening lumpRange (torusHotSites (Tb.stepParameters y) W)) W +
        (Tb.stepParameters y).κ * (Tb.stepParameters y).threshold ^ 2 * ((torusHotLumps (Tb.stepParameters y) W).card : ℝ) +
        (Tb.stepParameters y).coupling * ∑ e : TorusBond n, StepCosts.bondFit (Tb.stepParameters y) W V b e from by
    linarith
end YangMills.Construction.HullsInEveryVolume
end
