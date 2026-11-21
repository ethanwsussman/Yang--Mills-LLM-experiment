import YangMills.Construction.ClusterExpansionOfAStep.FloorsOfTheParameters
import YangMills.Construction.HullsInEveryVolume.LevelsFromAnExpansionWhereTheResponseReturns
import YangMills.Construction.LawByMomentsOfTheFlow.PointsOfTheLawAtTheHulls
import YangMills.Construction.ResponseInTheExpansion.CoinsOfAStepAreBorel
import YangMills.Construction.ResponseInTheExpansion.WilsonWeightAtOneLabel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
open RenormalizationStepParameters StepSettings TorusLumps TorusFields WeightedResponses ResponseInTheExpansion HullTrees LevelTestFunctions
  ColdStepAtMirrorFrames ClusterExpansionOfAStep StepFloors
namespace MomentLaw
namespace MomentPointsConstruction
variable {ℓ : TorusLumps.StepParameters}
private theorem stagesFrom_congr (hL : ∀ c : ChainStage ℓ, CoarseLabelFacts c.toStepSetup) (lam : ℝ) {x x' : ℕ → ℝ}
    (z₀ : StageWithResponse ℓ) : ∀ t, (∀ j ≤ t + 1, x j = x' j) → stagesFrom hL lam x z₀ t = stagesFrom hL lam x' z₀ t
  | 0, _ => rfl
  | t + 1, h => by
    show nextStageWithResponse hL lam (x (t + 2)) (stagesFrom hL lam x z₀ t) =
      nextStageWithResponse hL lam (x' (t + 2)) (stagesFrom hL lam x' z₀ t)
    rw [h (t + 2) le_rfl, stagesFrom_congr hL lam z₀ t fun j hj => h j (by omega)]
private def stageTower (hL : ∀ c : ChainStage ℓ, CoarseLabelFacts c.toStepSetup) (facts : CoarseLabelsStandard)
    (h2 : 2 ≤ ℓ.side) (lam : ℝ) (x : ℕ → ℝ) (z₀ : StageWithResponse ℓ) (pt : z₀.1.labels.Ω) : StageTower ℓ where
  base := z₀.1
  basePoint := pt
  couplings := fun i => x (i + 2)
  densities := fun j => (stagesFrom hL lam x z₀ j).1.toStepSetup.renormalizedDensity lam
  siteDensities := fun R => R.stateDensity lam
  labelFacts := facts
  two_le_side := h2
private theorem stage_stageTower (hL : ∀ c : ChainStage ℓ, CoarseLabelFacts c.toStepSetup) (facts : CoarseLabelsStandard)
    (h2 : 2 ≤ ℓ.side) (lam : ℝ) (x : ℕ → ℝ) (z₀ : StageWithResponse ℓ) (pt : z₀.1.labels.Ω) :
    ∀ j, (stageTower hL facts h2 lam x z₀ pt).stage j = (stagesFrom hL lam x z₀ j).1
  | 0 => rfl
  | j + 1 => by
    have key : ∀ c : ChainStage ℓ, c = (stagesFrom hL lam x z₀ j).1 →
        c.next (facts _ h2) (x (j + 2)) ((stagesFrom hL lam x z₀ j).1.toStepSetup.renormalizedDensity lam)
          (c.toStepSetup.stateDensity lam) = (stagesFrom hL lam x z₀ (j + 1)).1 := by
      rintro c rfl
      rfl
    exact key _ (stage_stageTower hL facts h2 lam x z₀ pt j)
private theorem stagesFrom_anchorRadius (hL : ∀ c : ChainStage ℓ, CoarseLabelFacts c.toStepSetup) (lam : ℝ)
    (x : ℕ → ℝ) (z₀ : StageWithResponse ℓ) :
    ∀ j, (stagesFrom hL lam x z₀ j).1.anchorRadius = z₀.1.anchorRadius
  | 0 => rfl
  | j + 1 => stagesFrom_anchorRadius hL lam x z₀ j
private theorem stagesFrom_barrierFn (hL : ∀ c : ChainStage ℓ, CoarseLabelFacts c.toStepSetup) (lam : ℝ)
    (x : ℕ → ℝ) (z₀ : StageWithResponse ℓ) :
    ∀ j, (stagesFrom hL lam x z₀ j).1.barrierFn = z₀.1.barrierFn
  | 0 => rfl
  | j + 1 => stagesFrom_barrierFn hL lam x z₀ j
private theorem stagesFrom_coupling (hL : ∀ c : ChainStage ℓ, CoarseLabelFacts c.toStepSetup) (lam : ℝ)
    (x : ℕ → ℝ) (z₀ : StageWithResponse ℓ) (h0 : z₀.1.coupling = x 0) (h1 : z₀.1.nextCoupling = x 1) :
    ∀ j, (stagesFrom hL lam x z₀ j).1.coupling = x j ∧ (stagesFrom hL lam x z₀ j).1.nextCoupling = x (j + 1)
  | 0 => ⟨h0, h1⟩
  | j + 1 => ⟨(stagesFrom_coupling hL lam x z₀ h0 h1 j).2, rfl⟩
private def transport {c c' : ChainStage ℓ} (h : c' = c) (A : ResponseSetup c.toStepSetup) :
    ResponseSetup c'.toStepSetup := h ▸ A
private theorem sigma_transport {c c' : ChainStage ℓ} (h : c' = c) (A : ResponseSetup c.toStepSetup) :
    (⟨c', transport h A⟩ : StageWithResponse ℓ) = ⟨c, A⟩ := by
  subst h
  rfl
end MomentPointsConstruction
open MomentPointsConstruction in
theorem momentPointsExist (hR : stagesFromReturningExpansionStatement)
    (hW : wilsonWeightSingleLabelStatement)
    (hCo : MarkLawMeasurable) (hLab : CoarseLabelsStandard) (hFlr : EventuallyFloorConditions) :
    momentPointsExistStatement := by
  classical
  obtain ⟨C₀, hW⟩ := hW
  intro a ha
  obtain ⟨L₀, rt₀, hrt₀, hR⟩ := hR a ha
  refine ⟨L₀, rt₀, C₀, hrt₀, fun L hLo hL Tb hTa hTL hT hCS hOn hrt hC => ?_⟩
  obtain ⟨M, hR⟩ := hR L hLo hL Tb hTa hTL hT hCS hrt
  refine ⟨M, fun K hM _ hN hFit hReturns => ?_⟩
  obtain ⟨y₁, hR⟩ := hR K hM hN hFit hReturns
  obtain ⟨yF, hyF⟩ := hFlr Tb hT (2 ^ 40) 1 (by norm_num) one_pos
  refine ⟨max (max y₁ yF) Tb.floorMin,
    fun y hy hRet hRow g hg hyg k _ hk2 hk8 R d hd P β hpage hside hβ hpass => ?_⟩
  have e₁ : y₁ ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hy
  have e₂ : yF ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hy
  have e₃ : Tb.floorMin ≤ y := le_trans (le_max_right _ _) hy
  have hfit : (Tb.stepParameters y).Admissible := hT.fits y e₃
  have h2 : 2 ≤ (Tb.stepParameters y).side := by
    have := hfit.L_ge
    omega
  have hLf : ∀ c : ChainStage (Tb.stepParameters y), CoarseLabelFacts c.toStepSetup := fun c => hLab c.toStepSetup h2
  have hB : 0 < (Tb.stepParameters y).B := hfit.B_pos
  have hyW : y ≤ couplingWindowTop (Tb.stepParameters y) g := by
    show y ≤ (g ^ 2)⁻¹ + 2 * (Tb.stepParameters y).B
    linarith
  have hyβ : y ≤ β := hyW.trans hβ
  obtain ⟨Λ, pt, Dq, Φ, hone, hmass, hden, hc0, hh0⟩ := hW (Tb.stepParameters y) hfit hC β hyβ
  let z₀ : StageWithResponse (Tb.stepParameters y) :=
    initialStage Tb y β K (fun _ _ _ => 0) Λ Dq Φ (fun _ _ _ _ _ => 0)
  have hfirst : IsInitialStage Tb y β z₀ :=
    ⟨⟨K, _, Λ, Dq, Φ, _, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, rfl⟩
  have hrow : z₀.1.toStepSetup.HasExpansions := ⟨hc0, hh0⟩
  have hst := hR y e₁ hRet hRow β hLf z₀ hyβ hfirst rfl hrow
  have hmove : ∀ t, FlowStaysAbove (Tb.stepParameters y) β (t + 1) →
      |couplingsAlongFlow (Tb.stepParameters y) β (t + 1) - couplingsAlongFlow (Tb.stepParameters y) β t| ≤ 2 * Tb.B := by
    intro t ht
    have s := hst t ht
    have h := s.onFamily.abs_sub_le
    have e₁ : (stagesFrom hLf Tb.lam (couplingsAlongFlow (Tb.stepParameters y) β) z₀ t).1.toStepSetup.nextCoupling = _ :=
      s.nextCoupling_eq
    have e₂ : (stagesFrom hLf Tb.lam (couplingsAlongFlow (Tb.stepParameters y) β) z₀ t).1.toStepSetup.coupling = _ :=
      s.coupling_eq
    rwa [e₁, e₂] at h
  have hrun0 : couplingsAlongFlow (Tb.stepParameters y) β 0 = β := rfl
  have hab : FlowStaysAbove (Tb.stepParameters y) β (P.windowLevel + 1) := by
    have hbelow : ∀ k < P.windowLevel, y ≤ couplingsAlongFlow (Tb.stepParameters y) β k := fun k hk =>
      hyW.trans (hpass.2 k hk).le
    intro j hj
    show y ≤ couplingsAlongFlow (Tb.stepParameters y) β j
    rcases Nat.lt_or_ge j P.windowLevel with h | h
    · exact hbelow j h
    · have hjK : j = P.windowLevel := by omega
      rw [hjK]
      rcases Nat.eq_zero_or_pos P.windowLevel with h0 | h0
      · rw [h0, hrun0]
        exact hyβ
      · obtain ⟨n, hn⟩ : ∃ n, P.windowLevel = n + 1 := ⟨P.windowLevel - 1, by omega⟩
        have hmv := hmove n fun i hi => hbelow i (by omega)
        have hlt : couplingWindowTop (Tb.stepParameters y) g < couplingsAlongFlow (Tb.stepParameters y) β n :=
          hpass.2 n (by omega)
        have hlt' : (g ^ 2)⁻¹ + 2 * Tb.B < couplingsAlongFlow (Tb.stepParameters y) β n := hlt
        rw [hn]
        have := (abs_le.mp hmv).1
        linarith
  have hstand : ∀ t ≤ P.windowLevel, StageOnFlow Tb K y β t (flowStages Tb y β hLf z₀ t) :=
    fun t ht => hst t fun j hj => hab j (by omega)
  let cp : ℕ → ℝ := fun j => couplingsAlongFlow (Tb.stepParameters y) β (min j (P.windowLevel + 1))
  have hcp : ∀ j, j ≤ P.windowLevel + 1 → cp j = couplingsAlongFlow (Tb.stepParameters y) β j := fun j hj => by
    show couplingsAlongFlow (Tb.stepParameters y) β (min j (P.windowLevel + 1)) = _
    rw [min_eq_left hj]
  have hcp' : ∀ j, P.windowLevel + 1 ≤ j →
      cp j = couplingsAlongFlow (Tb.stepParameters y) β (P.windowLevel + 1) := fun j hj => by
    show couplingsAlongFlow (Tb.stepParameters y) β (min j (P.windowLevel + 1)) = _
    rw [min_eq_right hj]
  let lev : ℕ → StageWithResponse (Tb.stepParameters y) := stagesFrom hLf Tb.lam cp z₀
  have hlevK : ∀ t ≤ P.windowLevel, lev t = flowStages Tb y β hLf z₀ t := fun t ht =>
    stagesFrom_congr hLf Tb.lam z₀ t fun j hj => hcp j (by omega)
  have hx : ∀ j, (lev j).1.coupling = cp j ∧ (lev j).1.nextCoupling = cp (j + 1) :=
    stagesFrom_coupling hLf Tb.lam cp z₀ (hcp 0 (by omega)).symm (hcp 1 (by omega)).symm
  have hρ : ∀ j, (lev j).1.anchorRadius = Tb.ρA := stagesFrom_anchorRadius hLf Tb.lam cp z₀
  have hp : ∀ j, (lev j).1.barrierFn = Tb.cutoff := stagesFrom_barrierFn hLf Tb.lam cp z₀
  let Tw : StageTower (Tb.stepParameters y) := stageTower hLf hLab h2 Tb.lam cp z₀ pt
  have hlev : ∀ j, Tw.stage j = (lev j).1 := stage_stageTower hLf hLab h2 Tb.lam cp z₀ pt
  have hge : ∀ x : ℝ, y ≤ x → 2 ^ 40 ≤ clusterRange x := fun x hx' => by
    have h : (2 : ℝ) ^ 40 ≤ clusterRange x := (hyF x (e₂.trans hx')).range_ge
    exact_mod_cast h
  have hrr' : ∀ x x' : ℝ, y ≤ x → |x' - x| ≤ 2 * Tb.B → clusterRange x ≤ clusterRange x' + 1 :=
    fun x x' hx' hm => by
    obtain ⟨-, -, p₃, -⟩ := (hyF x (e₂.trans hx')).stable_nearby.2 x' hm
    exact p₃
  have hnext : ∀ j ≤ P.windowLevel, clusterRange (couplingsAlongFlow (Tb.stepParameters y) β j) ≤
      clusterRange (couplingsAlongFlow (Tb.stepParameters y) β (j + 1)) + 1 := fun j hj =>
    hrr' _ _ (hab j (by omega)) (hmove j fun i hi => hab i (by omega))
  have hcpge : ∀ j, 2 ^ 39 ≤ clusterRange (cp j) := by
    intro j
    rcases Nat.lt_or_ge P.windowLevel j with h | h
    · rw [hcp' j h]
      have h₁ := hnext P.windowLevel le_rfl
      have h₂ := hge (couplingsAlongFlow (Tb.stepParameters y) β P.windowLevel) (hab P.windowLevel (by omega))
      norm_num at h₂ ⊢
      omega
    · rw [hcp j (by omega)]
      have h₂ := hge (couplingsAlongFlow (Tb.stepParameters y) β j) (hab j (by omega))
      norm_num at h₂ ⊢
      omega
  have hcpstep : ∀ j, clusterRange (cp j) ≤ clusterRange (cp (j + 1)) + 1 := by
    intro j
    rcases Nat.lt_or_ge P.windowLevel j with h | h
    · rw [hcp' j h, hcp' (j + 1) (by omega)]
      omega
    · rw [hcp j (by omega), hcp (j + 1) (by omega)]
      exact hnext j h
  have hcoins : Tw.MarksMeasurable := by
    intro s n _ bad
    by_cases hg : (Tb.stepParameters y).side ∣ n ∧ 64 ≤ n
    · rw [hlev s]
      have hm : (lev s).1.toStepSetup.frameReach = clusterRange (cp s) / 2 ^ 11 := by
        show clusterRange (lev s).1.coupling / 2 ^ 11 = _
        rw [(hx s).1]
      have hr' : (lev s).1.toStepSetup.nextRange = clusterRange (cp (s + 1)) := by
        show clusterRange (lev s).1.nextCoupling = _
        rw [(hx s).2]
      have h₁ := hcpge s
      have h₂ := hcpstep s
      refine hCo Tb hT y (lev s).1.toStepSetup rfl hfit (hρ s) ?_ ?_ ?_ n hg.1 hg.2 bad
      · show IsCutoff Tb.ballRadius (lev s).1.barrierFn
        rw [hp s]
        exact hT.cut
      · rw [hm]
        norm_num at h₁ ⊢
        omega
      · rw [hm, hr']
        norm_num at h₁ ⊢
        omega
    · have hg' : ¬ ((Tw.stage s).toStepSetup.params.side ∣ n ∧ 64 ≤ n) := hg
      have e : (fun p : TorusField (n * (Tb.stepParameters y).side) × TorusField n =>
          markLaw (Tw.stage s).toStepSetup p.1 p.2 bad) = fun _ => if bad = ∅ then 1 else 0 := by
        funext p
        unfold markLaw
        rw [if_neg hg']
      rw [e]
      exact measurable_const
  refine ⟨⟨P, β, Tw, fun t => transport (hlev t) (lev t).2, hLf, z₀, hpage, hside, hβ, hpass, hfirst, hstand,
    ⟨rfl, rfl, hone, hmass, hden⟩, hT.cut, hcoins,
    fun t ht => (sigma_transport (hlev t) (lev t).2).trans (hlevK t ht), ?_, ?_⟩, rfl, rfl⟩
  · intro n _ x W h h' hh
    have e : h = h' := eq_of_heq hh
    subst e
    rfl
  · intro n _ x W Y ω h h' hh
    have e : h = h' := eq_of_heq hh
    subst e
    rfl
end MomentLaw
end YangMills.Construction
end
