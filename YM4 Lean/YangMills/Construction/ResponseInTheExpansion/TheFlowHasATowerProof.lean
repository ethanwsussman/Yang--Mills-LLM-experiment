import YangMills.Construction.ClusterExpansionOfAStep.ColdExpansionHasOneCoupling
import YangMills.Construction.ClusterExpansionOfAStep.ColdExpansionOfTheImage
import YangMills.Construction.ClusterExpansionOfAStep.FloorsOfTheParameters
import YangMills.Construction.ClusterExpansionOfAStep.PriceOfTheImage
import YangMills.Construction.ClusterExpansionOfAStep.RegularityOfTheImage
import YangMills.Construction.ClusterExpansionOfAStep.StatesOfAStepFormAnExpansion
import YangMills.Construction.ClusterExpansionOfAStep.TheImageIsAnArray
import YangMills.Construction.ResponseInTheExpansion.CoinsOfAStepAreBorel
import YangMills.Construction.ResponseInTheExpansion.TheFlowHasATower
import YangMills.Construction.ResponseInTheExpansion.WilsonWeightAtOneLabel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
namespace TowerAlongFlow
private structure AboveFloorFacts (T : RenormalizationStepParameters.ParameterAssignment) (y : ℝ) : Prop where
  admissible : T.Admissible
  floor_le : T.floorMin ≤ y
  floorConditions : ∀ x : ℝ, y ≤ x → T.FloorConditions ((2 : ℝ) ^ 40 * T.side + 4 * T.n₀ + 2 ^ 17) 1 x
  cold : ∀ R : StepSettings.StepSetup, R.OnParameters T y → R.IsSymmetricWeight →
    TorusLumps.ColdExpansion R.params (R.depth + 1) (R.shiftedCoupling T.lam)
        (TorusLumps.kernelImage R.params R.coupling R.functional) (R.renormalizedDensity T.lam) ∧
      |R.shiftedCoupling T.lam - R.coupling| ≤ 2 * R.params.B
  display : ∀ R : StepSettings.StepSetup, R.OnParameters T y → R.IsWellPosed → R.nextCoupling = R.shiftedCoupling T.lam →
    |R.nextCoupling - R.coupling| ≤ 2 * R.params.B → ∀ h : ClusterExpansionOfAStep.CoarseLabelFacts R,
      TorusLumps.HullExpansionDisplay R.params (R.depth + 1) R.nextCoupling
        (TorusLumps.kernelImage R.params R.coupling R.functional) (R.renormalizedDensity T.lam)
        (ClusterExpansionOfAStep.coarseLabelSpace R h)
        (StepSettings.coarseWeightExpansion R) (StepSettings.coarseFactorExpansion R) (R.stateDensity T.lam)
  regular : ∀ R : StepSettings.StepSetup, R.params = T.stepParameters y → R.anchorRadius = T.ρA →
    R.barrierFn = T.cutoff → y ≤ R.coupling → R.HasExpansions → R.IsSymmetricWeight →
    R.nextCoupling = R.shiftedCoupling T.lam → |R.nextCoupling - R.coupling| ≤ 2 * R.params.B →
    ∀ h : ClusterExpansionOfAStep.CoarseLabelFacts R,
      TorusLumps.HullExpansionRegularity R.params R.nextCoupling (ClusterExpansionOfAStep.coarseLabelSpace R h)
        (StepSettings.coarseWeightExpansion R) (StepSettings.coarseFactorExpansion R) (R.stateDensity T.lam)
  price : ∀ R : StepSettings.StepSetup, R.OnParameters T y → R.IsWellPosed → R.nextCoupling = R.shiftedCoupling T.lam →
    |R.nextCoupling - R.coupling| ≤ 2 * R.params.B → ∀ h : ClusterExpansionOfAStep.CoarseLabelFacts R,
      TorusLumps.HullExpansionPrice R.params R.nextCoupling (ClusterExpansionOfAStep.coarseLabelSpace R h)
        (StepSettings.coarseFactorExpansion R) (R.stateDensity T.lam)
  states : ClusterExpansionOfAStep.CoarseStatesFormHullExpansion
  uniqueCoupling : CouplingUniqueness.ColdExpansionCouplingUnique
  labels : ClusterExpansionOfAStep.CoarseLabelsStandard
  image : TorusLumps.KernelImageIsDensity
variable {T : RenormalizationStepParameters.ParameterAssignment} {y : ℝ}
private theorem two_le_side (A : AboveFloorFacts T y) : 2 ≤ (T.stepParameters y).side := by
  have := (A.admissible.fits y A.floor_le).L_ge
  omega
private theorem clusterRange_ge (A : AboveFloorFacts T y) {x : ℝ} (hx : y ≤ x) :
    2 ^ 40 * T.side + 4 * T.n₀ + 2 ^ 17 ≤ TorusLumps.clusterRange x := by
  have hr : (2 : ℝ) ^ 40 * T.side + 4 * T.n₀ + 2 ^ 17 ≤ TorusLumps.clusterRange x :=
    (A.floorConditions x hx).range_ge
  exact_mod_cast hr
private theorem stage_step (A : AboveFloorFacts T y) {c : WeightedResponses.ChainStage (T.stepParameters y)}
    (hx : y ≤ c.coupling) (hrow : c.toStepSetup.HasExpansions)
    (hA : c.toStepSetup.IsSymmetricWeight) (hρ : c.anchorRadius = T.ρA) (hp : c.barrierFn = T.cutoff)
    (hx' : c.nextCoupling = c.toStepSetup.shiftedCoupling T.lam) :
    c.toStepSetup.OnParameters T y ∧ ∀ (h : ClusterExpansionOfAStep.CoarseLabelFacts c.toStepSetup) (x'' : ℝ),
      (c.next h x'' (c.toStepSetup.renormalizedDensity T.lam)
          (c.toStepSetup.stateDensity T.lam)).toStepSetup.HasExpansions ∧
      (c.next h x'' (c.toStepSetup.renormalizedDensity T.lam)
          (c.toStepSetup.stateDensity T.lam)).toStepSetup.IsSymmetricWeight := by
  have hT := A.admissible
  have hfit : (T.stepParameters y).Admissible := hT.fits y A.floor_le
  have hxpos : 0 < c.coupling := lt_of_lt_of_le (lt_of_lt_of_le one_pos hfit.y₁_ge) hx
  let R₀ : StepSettings.StepSetup :=
    ⟨T.stepParameters y, c.depth, c.coupling, c.coupling, c.functional, c.density, c.labels, c.labelWeight,
      c.clusterFactor, c.siteDensity, c.anchorRadius, c.barrierFn⟩
  have hstep₀ : R₀.OnParameters T y := ⟨rfl, hρ, hp, hx, ⟨hrow, by
    show c.coupling ≤ 1.01 * c.coupling
    nlinarith, by
    show TorusLumps.clusterRange c.coupling ≤ TorusLumps.clusterRange c.coupling + 1
    omega⟩⟩
  obtain ⟨hcold, hmove⟩ := A.cold R₀ hstep₀ hA
  have e : R₀.shiftedCoupling T.lam = c.nextCoupling := hx'.symm
  rw [e] at hcold hmove
  have hF := A.floorConditions c.coupling hx
  obtain ⟨_, hy9⟩ := hF.stable_nearby
  obtain ⟨hx1, _, hr1, hr2⟩ := hy9 c.nextCoupling hmove
  have hr' := clusterRange_ge A hx
  have hforms : c.toStepSetup.IsWellPosed := by
    refine ⟨hrow, hfit, ?_, hr1, hr2, ?_, ?_, ?_, hxpos, hA⟩
    · show ColdStepAtMirrorFrames.IsCutoff T.ballRadius c.barrierFn
      rw [hp]
      exact hT.cut
    · show 2 ^ 16 ≤ TorusLumps.clusterRange c.nextCoupling
      have h3 : TorusLumps.clusterRange c.coupling ≤ TorusLumps.clusterRange c.nextCoupling + 1 := hr1
      omega
    · show 2 ^ 40 * T.side ≤ TorusLumps.clusterRange c.coupling
      omega
    · show 4 * T.n₀ + 2 ^ 16 ≤ TorusLumps.clusterRange c.coupling
      omega
  have hframes : c.toStepSetup.ColdChainFits :=
    ⟨T.δ₁, T.lam, T.σA, T.cg, T.N, by
      show ColdChain.ColdChainConstants T.coupling T.δ₁ T.side T.lam c.anchorRadius T.σA T.cg T.N
      rw [hρ]
      exact hT.chain, hT.σ_le, hT.σ_one⟩
  have hstep : c.toStepSetup.OnParameters T y := ⟨rfl, hρ, hp, hx, ⟨hrow, hx1, hr1⟩⟩
  refine ⟨hstep, fun h x'' => ⟨⟨hcold, ?_⟩, ?_⟩⟩
  · exact TorusLumps.hullExpansion_of_parts (A.states c.toStepSetup hforms hframes h)
      (A.display c.toStepSetup hstep hforms hx' hmove h)
      (A.regular c.toStepSetup rfl hρ hp hx hrow hA hx' hmove h) (A.price c.toStepSetup hstep hforms hx' hmove h)
  · intro n _ hn
    obtain ⟨_, hm, hnn, hg, hi⟩ := A.image (T.stepParameters y) hfit c.depth c.coupling c.functional hxpos (by
      show 4 * T.n₀ + 2 ^ 16 ≤ TorusLumps.clusterRange c.coupling
      omega) ⟨hA, c.density, hrow.1, c.labels, c.labelWeight, c.clusterFactor, c.siteDensity, hrow.2⟩ n hn
    exact ⟨hm, hnn, hg, hi⟩
private theorem expansionCoupling_eq (A : AboveFloorFacts T y)
    {c : WeightedResponses.ChainStage (T.stepParameters y)} (hx : y ≤ c.coupling)
    (hrow : c.toStepSetup.HasExpansions) (hA : c.toStepSetup.IsSymmetricWeight) (hρ : c.anchorRadius = T.ρA)
    (hp : c.barrierFn = T.cutoff) :
    TorusLumps.expansionCoupling (T.stepParameters y) c.depth c.coupling c.functional =
      c.toStepSetup.shiftedCoupling T.lam := by
  let c' : WeightedResponses.ChainStage (T.stepParameters y) :=
    ⟨c.depth, c.coupling, c.toStepSetup.shiftedCoupling T.lam, c.functional, c.density, c.labels, c.labelWeight,
      c.clusterFactor, c.siteDensity, c.anchorRadius, c.barrierFn⟩
  obtain ⟨_, hup⟩ := stage_step A (c := c') hx hrow hA hρ hp rfl
  obtain ⟨hr, ha⟩ := hup (A.labels c'.toStepSetup (two_le_side A)) 0
  have hex : ∃ x' : ℝ, TorusLumps.HasExpansion (T.stepParameters y) (c.depth + 1) x'
      (TorusLumps.kernelImage (T.stepParameters y) c.coupling c.functional) :=
    ⟨c.toStepSetup.shiftedCoupling T.lam, ha, _, hr.1, _, _, _, _, hr.2⟩
  unfold TorusLumps.expansionCoupling
  rw [dif_pos hex]
  obtain ⟨_, f, hf, _⟩ := hex.choose_spec
  exact A.uniqueCoupling T A.admissible y A.floor_le c.depth _ _ _ _ _ hf hr.1
private def stages (T : RenormalizationStepParameters.ParameterAssignment) (y : ℝ) (facts : ClusterExpansionOfAStep.CoarseLabelsStandard)
    (h2 : 2 ≤ (T.stepParameters y).side)
    (bot : WeightedResponses.ChainStage (T.stepParameters y)) (xs : ℕ → ℝ) :
    ℕ → WeightedResponses.ChainStage (T.stepParameters y)
  | 0 => bot
  | j + 1 => (stages T y facts h2 bot xs j).next (facts _ h2) (xs j)
      ((stages T y facts h2 bot xs j).toStepSetup.renormalizedDensity T.lam)
      ((stages T y facts h2 bot xs j).toStepSetup.stateDensity T.lam)
private def towerOfStages (T : RenormalizationStepParameters.ParameterAssignment) (y : ℝ) (facts : ClusterExpansionOfAStep.CoarseLabelsStandard)
    (h2 : 2 ≤ (T.stepParameters y).side)
    (bot : WeightedResponses.ChainStage (T.stepParameters y)) (pt : bot.labels.Ω) (xs : ℕ → ℝ) :
    WeightedResponses.StageTower (T.stepParameters y) where
  base := bot
  basePoint := pt
  couplings := xs
  densities := fun j => (stages T y facts h2 bot xs j).toStepSetup.renormalizedDensity T.lam
  siteDensities := fun R => R.stateDensity T.lam
  labelFacts := facts
  two_le_side := h2
private theorem stage_towerOfStages (facts : ClusterExpansionOfAStep.CoarseLabelsStandard) (h2 : 2 ≤ (T.stepParameters y).side)
    (bot : WeightedResponses.ChainStage (T.stepParameters y)) (pt : bot.labels.Ω) (xs : ℕ → ℝ) :
    ∀ j, (towerOfStages T y facts h2 bot pt xs).stage j = stages T y facts h2 bot xs j
  | 0 => rfl
  | j + 1 => by
    have key : ∀ c : WeightedResponses.ChainStage (T.stepParameters y), c = stages T y facts h2 bot xs j →
        c.next (facts _ h2) (xs j) ((stages T y facts h2 bot xs j).toStepSetup.renormalizedDensity T.lam)
          (c.toStepSetup.stateDensity T.lam) = stages T y facts h2 bot xs (j + 1) := by
      rintro c rfl
      rfl
    exact key _ (stage_towerOfStages facts h2 bot pt xs j)
private theorem stages_depth (facts : ClusterExpansionOfAStep.CoarseLabelsStandard) (h2 : 2 ≤ (T.stepParameters y).side)
    (bot : WeightedResponses.ChainStage (T.stepParameters y)) (xs : ℕ → ℝ) (hb : bot.depth = 0) :
    ∀ j, (stages T y facts h2 bot xs j).depth = j
  | 0 => hb
  | j + 1 => congrArg (· + 1) (stages_depth facts h2 bot xs hb j)
private theorem stages_anchorRadius (facts : ClusterExpansionOfAStep.CoarseLabelsStandard) (h2 : 2 ≤ (T.stepParameters y).side)
    (bot : WeightedResponses.ChainStage (T.stepParameters y)) (xs : ℕ → ℝ) :
    ∀ j, (stages T y facts h2 bot xs j).anchorRadius = bot.anchorRadius
  | 0 => rfl
  | j + 1 => stages_anchorRadius facts h2 bot xs j
private theorem stages_barrierFn (facts : ClusterExpansionOfAStep.CoarseLabelsStandard) (h2 : 2 ≤ (T.stepParameters y).side)
    (bot : WeightedResponses.ChainStage (T.stepParameters y)) (xs : ℕ → ℝ) :
    ∀ j, (stages T y facts h2 bot xs j).barrierFn = bot.barrierFn
  | 0 => rfl
  | j + 1 => stages_barrierFn facts h2 bot xs j
private theorem stages_coupling (facts : ClusterExpansionOfAStep.CoarseLabelsStandard) (h2 : 2 ≤ (T.stepParameters y).side)
    (bot : WeightedResponses.ChainStage (T.stepParameters y)) (cp : ℕ → ℝ) (h0 : bot.coupling = cp 0)
    (h1 : bot.nextCoupling = cp 1) :
    ∀ j, (stages T y facts h2 bot (fun i => cp (i + 2)) j).coupling = cp j ∧
      (stages T y facts h2 bot (fun i => cp (i + 2)) j).nextCoupling = cp (j + 1)
  | 0 => ⟨h0, h1⟩
  | j + 1 => ⟨(stages_coupling facts h2 bot cp h0 h1 j).2, rfl⟩
private theorem tower_of_flow (A : AboveFloorFacts T y) (hco : ResponseInTheExpansion.MarkLawMeasurable)
    {β : ℝ} {k : ℕ} (hfl : ∀ j ≤ k + 1, y ≤ (TorusLumps.couplingFlow (T.stepParameters y) β j).1)
    (Λ : TorusLumps.LabelSpace) (pt : Λ.Ω)
    (Dq : (n : ℕ) → TorusFields.TorusField n → (Y : Finset (TorusFields.TorusSite n)) → (Y → Λ.Ω) → ℝ)
    (Φ : (n : ℕ) → TorusFields.TorusField n → (Y : Finset (TorusFields.TorusSite n)) → (Y → Λ.Ω) →
      Finset (TorusFields.TorusSite n) → ℝ)
    (hone : ∀ ω : Λ.Ω, ω = pt) (hmass : Λ.μ {pt} = 1)
    (hden : ∀ (n : ℕ) [NeZero n] (W : TorusFields.TorusField n) (Y : Finset (TorusFields.TorusSite n))
      (ω : Y → Λ.Ω),
      Dq n W Y ω = open Classical in
        if Y = TorusLumps.thickening (2 * TorusLumps.clusterRange β)
            (TorusLumps.torusHotSites (T.stepParameters y) W)
        then TorusLumps.wilsonWeight β n W else 0)
    (hc0 : TorusLumps.ColdExpansion (T.stepParameters y) 0 β (TorusLumps.wilsonWeight β) (fun _ _ _ => 0))
    (hh0 : TorusLumps.HullExpansion (T.stepParameters y) 0 β (TorusLumps.wilsonWeight β) (fun _ _ _ => 0)
      Λ Dq Φ (fun _ _ _ _ _ => 0))
    (ha0 : ∀ n [NeZero n], (T.stepParameters y).n₀ ≤ n → Measurable (TorusLumps.wilsonWeight β n) ∧
      (∀ W, 0 ≤ TorusLumps.wilsonWeight β n W) ∧
      (∀ (g : TorusFields.TorusSite n → BlockAverages.UnitQuaternion) (W : TorusFields.TorusField n),
        TorusLumps.wilsonWeight β n (TorusFields.gaugeTransform g W) = TorusLumps.wilsonWeight β n W) ∧
      ∀ (g : TorusFields.TorusIsometry) (W W' : TorusFields.TorusField n), g.Transports W W' →
        TorusLumps.wilsonWeight β n W' = TorusLumps.wilsonWeight β n W) :
    ∃ Tw : WeightedResponses.StageTower (T.stepParameters y), ResponseInTheExpansion.IsTowerAtParameters T y Tw β k ∧
      ColdStepAtMirrorFrames.IsCutoff ((T.stepParameters y).threshold / 64) Tw.base.barrierFn ∧
      ∀ (s n : ℕ) [NeZero n], (T.stepParameters y).side ∣ n → 64 ≤ n →
        ∀ bad : Finset (TorusFields.TorusBond (n * (T.stepParameters y).side)),
        Measurable fun p : TorusFields.TorusField (n * (T.stepParameters y).side) × TorusFields.TorusField n =>
          WeightedResponses.markLaw (Tw.stage s).toStepSetup p.1 p.2 bad := by
  have hfit : (T.stepParameters y).Admissible := A.admissible.fits y A.floor_le
  let run := TorusLumps.couplingFlow (T.stepParameters y) β
  let cp : ℕ → ℝ := fun j => (run (min j (k + 1))).1
  have hcp : ∀ j, j ≤ k + 1 → cp j = (run j).1 := fun j hj => by
    show (run (min j (k + 1))).1 = _
    rw [min_eq_left hj]
  have hcpy : ∀ j, y ≤ cp j := fun j => hfl _ (min_le_right _ _)
  let bot : WeightedResponses.ChainStage (T.stepParameters y) :=
    ⟨0, β, cp 1, TorusLumps.wilsonWeight β, fun _ _ _ => 0, Λ, Dq, Φ, fun _ _ _ _ _ => 0, T.ρA, T.cutoff⟩
  let xs : ℕ → ℝ := fun i => cp (i + 2)
  have h2 := two_le_side A
  let lev := stages T y A.labels h2 bot xs
  have hx : ∀ j, (lev j).coupling = cp j ∧ (lev j).nextCoupling = cp (j + 1) :=
    stages_coupling A.labels h2 bot cp (by
      show β = (run (min 0 (k + 1))).1
      simp [run, TorusLumps.couplingFlow]) rfl
  have ht : ∀ j, (lev j).depth = j := stages_depth A.labels h2 bot xs rfl
  have hρ : ∀ j, (lev j).anchorRadius = T.ρA := stages_anchorRadius A.labels h2 bot xs
  have hp : ∀ j, (lev j).barrierFn = T.cutoff := stages_barrierFn A.labels h2 bot xs
  have good : ∀ j, j ≤ k + 1 → (lev j).functional = (run j).2 ∧ (lev j).toStepSetup.HasExpansions ∧
      (lev j).toStepSetup.IsSymmetricWeight := by
    intro j
    induction j with
    | zero => exact fun _ => ⟨rfl, ⟨hc0, hh0⟩, ha0⟩
    | succ j ih =>
      intro hj
      obtain ⟨hD, hrow, hA⟩ := ih (by omega)
      have hxj : (lev j).coupling = (run j).1 := (hx j).1.trans (hcp j (by omega))
      have hy : y ≤ (lev j).coupling := (hx j).1 ▸ hcpy j
      have hrs := expansionCoupling_eq A hy hrow hA (hρ j) (hp j)
      have hx' : (lev j).nextCoupling = (lev j).toStepSetup.shiftedCoupling T.lam := by
        rw [← hrs, ht j, hxj, hD, (hx j).2, hcp (j + 1) hj]
        rfl
      obtain ⟨_, hup⟩ := stage_step A hy hrow hA (hρ j) (hp j) hx'
      obtain ⟨hr, ha⟩ := hup (A.labels _ h2) (xs j)
      refine ⟨?_, hr, ha⟩
      show TorusLumps.kernelImage (T.stepParameters y) (lev j).coupling (lev j).functional =
        TorusLumps.kernelImage (T.stepParameters y) (run j).1 (run j).2
      rw [hxj, hD]
  have table : ∀ j, j ≤ k → (lev j).toStepSetup.OnParameters T y := by
    intro j hj
    obtain ⟨hD, hrow, hA⟩ := good j (by omega)
    have hxj : (lev j).coupling = (run j).1 := (hx j).1.trans (hcp j (by omega))
    have hy : y ≤ (lev j).coupling := (hx j).1 ▸ hcpy j
    have hrs := expansionCoupling_eq A hy hrow hA (hρ j) (hp j)
    have hx' : (lev j).nextCoupling = (lev j).toStepSetup.shiftedCoupling T.lam := by
      rw [← hrs, ht j, hxj, hD, (hx j).2, hcp (j + 1) (by omega)]
      rfl
    exact (stage_step A hy hrow hA (hρ j) (hp j) hx').1
  have hlevel := stage_towerOfStages (T := T) (y := y) A.labels h2 bot pt xs
  refine ⟨towerOfStages T y A.labels h2 bot pt xs, ⟨⟨rfl, rfl, hone, hmass, ?_⟩, fun j hj => ?_, fun j hj => ?_⟩,
    A.admissible.cut, fun s n _ hLn h64 bad => ?_⟩
  · exact hden
  · rw [hlevel j]
    exact (hx j).1.trans (hcp j hj)
  · rw [hlevel j]
    exact table j hj
  · rw [hlevel s]
    have hrr : TorusLumps.clusterRange (cp s) ≤ TorusLumps.clusterRange (cp (s + 1)) + 1 := by
      by_cases hs : s ≤ k
      · have h := (table s hs).isStep.2.2
        have e1 : (lev s).toStepSetup.range = TorusLumps.clusterRange (cp s) := by
          show TorusLumps.clusterRange (lev s).coupling = _
          rw [(hx s).1]
        have e2 : (lev s).toStepSetup.nextRange = TorusLumps.clusterRange (cp (s + 1)) := by
          show TorusLumps.clusterRange (lev s).nextCoupling = _
          rw [(hx s).2]
        rw [e1, e2] at h
        exact h
      · have e : cp s = cp (s + 1) := by
          show (run (min s (k + 1))).1 = (run (min (s + 1) (k + 1))).1
          rw [min_eq_right (by omega), min_eq_right (by omega)]
        rw [e]
        omega
    have hge := clusterRange_ge A (hcpy s)
    have hm : (lev s).toStepSetup.frameReach = TorusLumps.clusterRange (cp s) / 2 ^ 11 := by
      show TorusLumps.clusterRange (lev s).coupling / 2 ^ 11 = _
      rw [(hx s).1]
    have hr' : (lev s).toStepSetup.nextRange = TorusLumps.clusterRange (cp (s + 1)) := by
      show TorusLumps.clusterRange (lev s).nextCoupling = _
      rw [(hx s).2]
    have hL : 0 < T.side := Nat.pos_of_ne_zero (NeZero.ne _)
    have hge' : 2 ^ 40 ≤ TorusLumps.clusterRange (cp s) := by
      have : 2 ^ 40 * 1 ≤ 2 ^ 40 * T.side := Nat.mul_le_mul_left _ hL
      omega
    refine hco T A.admissible y (lev s).toStepSetup rfl hfit (hρ s) ?_ ?_ ?_ n hLn h64 bad
    · show ColdStepAtMirrorFrames.IsCutoff T.ballRadius (lev s).barrierFn
      rw [hp s]
      exact A.admissible.cut
    · rw [hm]
      norm_num at hge' ⊢
      omega
    · rw [hm, hr']
      norm_num at hge' ⊢
      omega
end TowerAlongFlow
open TowerAlongFlow in
theorem towerAlongFlow_holds (hS : ClusterExpansionOfAStep.CoarseStatesFormHullExpansion)
    (hC : ImageColdExpansion.ImageHasColdExpansion)
    (hOne : CouplingUniqueness.ColdExpansionCouplingUnique) (hLab : ClusterExpansionOfAStep.CoarseLabelsStandard)
    (hImg : TorusLumps.KernelImageIsDensity) (hD : ImageDensities.ImageHasHullExpansion)
    (hReg : ClusterExpansionOfAStep.ImageHasHullExpansionRegularity)
    (hP : ClusterExpansionOfAStep.ImageHasHullExpansionPrice) (hFl : StepFloors.EventuallyFloorConditions)
    (hW : WeightedResponses.wilsonWeightSingleLabelStatement)
    (hCo : ResponseInTheExpansion.MarkLawMeasurable) : ResponseInTheExpansion.TowerAlongFlowStatement := by
  classical
  obtain ⟨rt₀, hrt₀, hC⟩ := hC
  obtain ⟨rt₁, hrt₁, hP⟩ := hP
  obtain ⟨rt₂, hrt₂, hD⟩ := hD
  obtain ⟨C₀, hW⟩ := hW
  intro a _
  refine ⟨0, fun c => min (min (rt₀ c) (rt₁ c)) (rt₂ c), C₀,
    fun c => lt_min (lt_min (hrt₀ c) (hrt₁ c)) (hrt₂ c), fun L _ _ T _ _ hT hCold _ hrt hCder => ?_⟩
  obtain ⟨yC, hyC⟩ := hC T hT hCold ((hrt.trans (min_le_left _ _)).trans (min_le_left _ _))
  obtain ⟨yD, hyD⟩ := hD T hT hCold (hrt.trans (min_le_right _ _))
  obtain ⟨yR, hyR⟩ := hReg T hT
  obtain ⟨yP, hyP⟩ := hP T hT ((hrt.trans (min_le_left _ _)).trans (min_le_right _ _))
  have hCpos : (0 : ℝ) < 2 ^ 40 * T.side + 4 * T.n₀ + 2 ^ 17 := by positivity
  obtain ⟨yF, hyF⟩ := hFl T hT _ 1 hCpos one_pos
  refine ⟨max (max (max yC yD) (max yR yP)) (max yF T.floorMin), fun y hy _ hrow₀ => ?_⟩
  have h1 : yC ≤ y := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hy
  have h2 : yD ≤ y := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hy
  have h3 : yR ≤ y := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)) hy
  have h4 : yP ≤ y := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)) hy
  have h5 : yF ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hy
  have h6 : T.floorMin ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hy
  have hfit : (T.stepParameters y).Admissible := hT.fits y h6
  have A : AboveFloorFacts T y := ⟨hT, h6, fun x hx => hyF x (h5.trans hx), hyC y h1, hyD y h2, hyR y h3,
    hyP y h4, hS, hOne, hLab, hImg⟩
  refine ⟨hfit, hT.L_gt, fun β k hfl => ?_⟩
  have hβ : y ≤ β := hfl 0 (Nat.zero_le _)
  obtain ⟨Λ, pt, Dq, Φ, g1, g2, g3, g4, g5⟩ := hW (T.stepParameters y) hfit hCder β hβ
  obtain ⟨Tw, hst, hcut, hco⟩ := tower_of_flow A hCo hfl Λ pt Dq Φ g1 g2 g3 g4 g5 (hrow₀ β hβ).1
  refine ⟨Tw, hst, hcut, fun s n _ bad => ?_⟩
  by_cases hg : (T.stepParameters y).side ∣ n ∧ 64 ≤ n
  · exact hco s n hg.1 hg.2 bad
  · have hg' : ¬ ((Tw.stage s).toStepSetup.params.side ∣ n ∧ 64 ≤ n) := hg
    have e : (fun p : TorusFields.TorusField (n * (T.stepParameters y).side) × TorusFields.TorusField n =>
        WeightedResponses.markLaw (Tw.stage s).toStepSetup p.1 p.2 bad) =
        fun _ => if bad = ∅ then 1 else 0 := by
      funext p
      unfold WeightedResponses.markLaw
      rw [if_neg hg']
    rw [e]
    exact measurable_const
end YangMills.Construction.ResponseInTheExpansion
end
