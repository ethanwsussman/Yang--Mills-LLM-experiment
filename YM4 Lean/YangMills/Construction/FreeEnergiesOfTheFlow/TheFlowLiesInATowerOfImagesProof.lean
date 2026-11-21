import YangMills.Construction.ClusterExpansionOfAStep.ColdExpansionHasOneCoupling
import YangMills.Construction.ClusterExpansionOfAStep.ColdExpansionOfTheImage
import YangMills.Construction.ClusterExpansionOfAStep.FloorsOfTheParameters
import YangMills.Construction.ClusterExpansionOfAStep.PriceOfTheImage
import YangMills.Construction.ClusterExpansionOfAStep.RegularityOfTheImage
import YangMills.Construction.ClusterExpansionOfAStep.StatesOfAStepFormAnExpansion
import YangMills.Construction.ClusterExpansionOfAStep.TheImageIsAnArray
import YangMills.Construction.FreeEnergiesOfTheFlow.TheFlowLiesInATowerOfImages
import YangMills.Construction.ResponseInTheExpansion.CoinsOfAStepAreBorel
import YangMills.Construction.ResponseInTheExpansion.WilsonWeightAtOneLabel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.FreeEnergies
open TorusFields TorusLumps StepSettings RenormalizationStepParameters WeightedResponses ClusterExpansionOfAStep ResponseInTheExpansion
  CouplingUniqueness ImageColdExpansion ImageDensities StepFloors BlockAverages ColdChain ColdStepAtMirrorFrames
namespace FlowInImageTower
private structure Ingredients (T : ParameterAssignment) (y : ℝ) : Prop where
  drawn : T.Admissible
  floor : T.floorMin ≤ y
  floors : ∀ x : ℝ, y ≤ x → T.FloorConditions ((2 : ℝ) ^ 40 * T.side + 4 * T.n₀ + 2 ^ 17) 1 x
  cold : ∀ R : StepSetup, R.OnParameters T y → R.IsSymmetricWeight →
    ColdExpansion R.params (R.depth + 1) (R.shiftedCoupling T.lam) (kernelImage R.params R.coupling R.functional)
        (R.renormalizedDensity T.lam) ∧
      |R.shiftedCoupling T.lam - R.coupling| ≤ 2 * R.params.B
  display : ∀ R : StepSetup, R.OnParameters T y → R.IsWellPosed → R.nextCoupling = R.shiftedCoupling T.lam →
    |R.nextCoupling - R.coupling| ≤ 2 * R.params.B → ∀ h : CoarseLabelFacts R,
      HullExpansionDisplay R.params (R.depth + 1) R.nextCoupling (kernelImage R.params R.coupling R.functional)
        (R.renormalizedDensity T.lam) (coarseLabelSpace R h)
        (coarseWeightExpansion R) (coarseFactorExpansion R) (R.stateDensity T.lam)
  regular : ∀ R : StepSetup, R.params = T.stepParameters y → R.anchorRadius = T.ρA → R.barrierFn = T.cutoff →
    y ≤ R.coupling → R.HasExpansions → R.IsSymmetricWeight →
    R.nextCoupling = R.shiftedCoupling T.lam → |R.nextCoupling - R.coupling| ≤ 2 * R.params.B →
    ∀ h : CoarseLabelFacts R,
      HullExpansionRegularity R.params R.nextCoupling (coarseLabelSpace R h) (coarseWeightExpansion R) (coarseFactorExpansion R)
        (R.stateDensity T.lam)
  price : ∀ R : StepSetup, R.OnParameters T y → R.IsWellPosed → R.nextCoupling = R.shiftedCoupling T.lam →
    |R.nextCoupling - R.coupling| ≤ 2 * R.params.B → ∀ h : CoarseLabelFacts R,
      HullExpansionPrice R.params R.nextCoupling (coarseLabelSpace R h) (coarseFactorExpansion R) (R.stateDensity T.lam)
  states : CoarseStatesFormHullExpansion
  one : ColdExpansionCouplingUnique
  labels : CoarseLabelsStandard
  image : KernelImageIsDensity
variable {T : ParameterAssignment} {y : ℝ}
private theorem two_le_side_of (A : Ingredients T y) : 2 ≤ (T.stepParameters y).side := by
  have := (A.drawn.fits y A.floor).L_ge
  omega
private theorem clusterRange_ge (A : Ingredients T y) {x : ℝ} (hx : y ≤ x) :
    2 ^ 40 * T.side + 4 * T.n₀ + 2 ^ 17 ≤ clusterRange x := by
  have hr : (2 : ℝ) ^ 40 * T.side + 4 * T.n₀ + 2 ^ 17 ≤ clusterRange x := (A.floors x hx).range_ge
  exact_mod_cast hr
private theorem next_stage_spec (A : Ingredients T y) {c : ChainStage (T.stepParameters y)} (hx : y ≤ c.coupling)
    (hrow : c.toStepSetup.HasExpansions) (hA : c.toStepSetup.IsSymmetricWeight) (hρ : c.anchorRadius = T.ρA)
    (hp : c.barrierFn = T.cutoff) (hx' : c.nextCoupling = c.toStepSetup.shiftedCoupling T.lam) :
    c.toStepSetup.OnParameters T y ∧ ∀ (h : CoarseLabelFacts c.toStepSetup) (x'' : ℝ),
      (c.next h x'' (c.toStepSetup.renormalizedDensity T.lam)
        (c.toStepSetup.stateDensity T.lam)).toStepSetup.HasExpansions ∧
      (c.next h x'' (c.toStepSetup.renormalizedDensity T.lam)
        (c.toStepSetup.stateDensity T.lam)).toStepSetup.IsSymmetricWeight := by
  have hT := A.drawn
  have hfit : (T.stepParameters y).Admissible := hT.fits y A.floor
  have hxpos : 0 < c.coupling := lt_of_lt_of_le (lt_of_lt_of_le one_pos hfit.y₁_ge) hx
  let R₀ : StepSetup := ⟨T.stepParameters y, c.depth, c.coupling, c.coupling, c.functional, c.density, c.labels,
    c.labelWeight, c.clusterFactor, c.siteDensity, c.anchorRadius, c.barrierFn⟩
  have hstep₀ : R₀.OnParameters T y := ⟨rfl, hρ, hp, hx, ⟨hrow, by
    show c.coupling ≤ 1.01 * c.coupling
    nlinarith, by
    show clusterRange c.coupling ≤ clusterRange c.coupling + 1
    omega⟩⟩
  obtain ⟨hcold, hmove⟩ := A.cold R₀ hstep₀ hA
  have e : R₀.shiftedCoupling T.lam = c.nextCoupling := hx'.symm
  rw [e] at hcold hmove
  have hF := A.floors c.coupling hx
  obtain ⟨_, hstab⟩ := hF.stable_nearby
  obtain ⟨hx1, _, hr1, hr2⟩ := hstab c.nextCoupling hmove
  have hr' := clusterRange_ge A hx
  have hforms : c.toStepSetup.IsWellPosed := by
    refine ⟨hrow, hfit, ?_, hr1, hr2, ?_, ?_, ?_, hxpos, hA⟩
    · show IsCutoff T.ballRadius c.barrierFn
      rw [hp]
      exact hT.cut
    · show 2 ^ 16 ≤ clusterRange c.nextCoupling
      have h3 : clusterRange c.coupling ≤ clusterRange c.nextCoupling + 1 := hr1
      omega
    · show 2 ^ 40 * T.side ≤ clusterRange c.coupling
      omega
    · show 4 * T.n₀ + 2 ^ 16 ≤ clusterRange c.coupling
      omega
  have hframes : c.toStepSetup.ColdChainFits :=
    ⟨T.δ₁, T.lam, T.σA, T.cg, T.N, by
      show ColdChainConstants T.coupling T.δ₁ T.side T.lam c.anchorRadius T.σA T.cg T.N
      rw [hρ]
      exact hT.chain, hT.σ_le, hT.σ_one⟩
  have hstep : c.toStepSetup.OnParameters T y := ⟨rfl, hρ, hp, hx, ⟨hrow, hx1, hr1⟩⟩
  refine ⟨hstep, fun h x'' => ⟨⟨hcold, ?_⟩, ?_⟩⟩
  · exact hullExpansion_of_parts (A.states c.toStepSetup hforms hframes h)
      (A.display c.toStepSetup hstep hforms hx' hmove h)
      (A.regular c.toStepSetup rfl hρ hp hx hrow hA hx' hmove h) (A.price c.toStepSetup hstep hforms hx' hmove h)
  · intro n _ hn
    obtain ⟨_, hm, hnn, hg, hi⟩ := A.image (T.stepParameters y) hfit c.depth c.coupling c.functional hxpos (by
      show 4 * T.n₀ + 2 ^ 16 ≤ clusterRange c.coupling
      omega) ⟨hA, c.density, hrow.1, c.labels, c.labelWeight, c.clusterFactor, c.siteDensity, hrow.2⟩ n hn
    exact ⟨hm, hnn, hg, hi⟩
private theorem expansionCoupling_eq_shifted (A : Ingredients T y) {c : ChainStage (T.stepParameters y)}
    (hx : y ≤ c.coupling) (hrow : c.toStepSetup.HasExpansions) (hA : c.toStepSetup.IsSymmetricWeight)
    (hρ : c.anchorRadius = T.ρA) (hp : c.barrierFn = T.cutoff) :
    expansionCoupling (T.stepParameters y) c.depth c.coupling c.functional =
      c.toStepSetup.shiftedCoupling T.lam := by
  let c' : ChainStage (T.stepParameters y) :=
    ⟨c.depth, c.coupling, c.toStepSetup.shiftedCoupling T.lam, c.functional, c.density, c.labels, c.labelWeight,
      c.clusterFactor, c.siteDensity, c.anchorRadius, c.barrierFn⟩
  obtain ⟨_, hup⟩ := next_stage_spec A (c := c') hx hrow hA hρ hp rfl
  obtain ⟨hr, ha⟩ := hup (A.labels c'.toStepSetup (two_le_side_of A)) 0
  have hex : ∃ x' : ℝ, HasExpansion (T.stepParameters y) (c.depth + 1) x'
      (kernelImage (T.stepParameters y) c.coupling c.functional) :=
    ⟨c.toStepSetup.shiftedCoupling T.lam, ha, _, hr.1, _, _, _, _, hr.2⟩
  unfold expansionCoupling
  rw [dif_pos hex]
  obtain ⟨_, f, hf, _⟩ := hex.choose_spec
  exact A.one T A.drawn y A.floor c.depth _ _ _ _ _ hf hr.1
private def stages (T : ParameterAssignment) (y : ℝ) (facts : CoarseLabelsStandard)
    (h2 : 2 ≤ (T.stepParameters y).side) (bot : ChainStage (T.stepParameters y)) (xs : ℕ → ℝ) :
    ℕ → ChainStage (T.stepParameters y)
  | 0 => bot
  | j + 1 => (stages T y facts h2 bot xs j).next (facts _ h2) (xs j)
      ((stages T y facts h2 bot xs j).toStepSetup.renormalizedDensity T.lam)
      ((stages T y facts h2 bot xs j).toStepSetup.stateDensity T.lam)
private def stageTowerOf (T : ParameterAssignment) (y : ℝ) (facts : CoarseLabelsStandard)
    (h2 : 2 ≤ (T.stepParameters y).side) (bot : ChainStage (T.stepParameters y)) (pt : bot.labels.Ω)
    (xs : ℕ → ℝ) : StageTower (T.stepParameters y) where
  base := bot
  basePoint := pt
  couplings := xs
  densities := fun j => (stages T y facts h2 bot xs j).toStepSetup.renormalizedDensity T.lam
  siteDensities := fun R => R.stateDensity T.lam
  labelFacts := facts
  two_le_side := h2
private theorem stage_stageTowerOf (facts : CoarseLabelsStandard) (h2 : 2 ≤ (T.stepParameters y).side)
    (bot : ChainStage (T.stepParameters y)) (pt : bot.labels.Ω) (xs : ℕ → ℝ) :
    ∀ j, (stageTowerOf T y facts h2 bot pt xs).stage j = stages T y facts h2 bot xs j
  | 0 => rfl
  | j + 1 => by
    have key : ∀ c : ChainStage (T.stepParameters y), c = stages T y facts h2 bot xs j →
        c.next (facts _ h2) (xs j) ((stages T y facts h2 bot xs j).toStepSetup.renormalizedDensity T.lam)
          (c.toStepSetup.stateDensity T.lam) = stages T y facts h2 bot xs (j + 1) := by
      rintro c rfl
      rfl
    exact key _ (stage_stageTowerOf facts h2 bot pt xs j)
private theorem stages_depth (facts : CoarseLabelsStandard) (h2 : 2 ≤ (T.stepParameters y).side)
    (bot : ChainStage (T.stepParameters y)) (xs : ℕ → ℝ) (hb : bot.depth = 0) :
    ∀ j, (stages T y facts h2 bot xs j).depth = j
  | 0 => hb
  | j + 1 => congrArg (· + 1) (stages_depth facts h2 bot xs hb j)
private theorem stages_anchorRadius (facts : CoarseLabelsStandard) (h2 : 2 ≤ (T.stepParameters y).side)
    (bot : ChainStage (T.stepParameters y)) (xs : ℕ → ℝ) :
    ∀ j, (stages T y facts h2 bot xs j).anchorRadius = bot.anchorRadius
  | 0 => rfl
  | j + 1 => stages_anchorRadius facts h2 bot xs j
private theorem stages_barrierFn (facts : CoarseLabelsStandard) (h2 : 2 ≤ (T.stepParameters y).side)
    (bot : ChainStage (T.stepParameters y)) (xs : ℕ → ℝ) :
    ∀ j, (stages T y facts h2 bot xs j).barrierFn = bot.barrierFn
  | 0 => rfl
  | j + 1 => stages_barrierFn facts h2 bot xs j
private theorem stages_coupling (facts : CoarseLabelsStandard) (h2 : 2 ≤ (T.stepParameters y).side)
    (bot : ChainStage (T.stepParameters y)) (cp : ℕ → ℝ) (h0 : bot.coupling = cp 0)
    (h1 : bot.nextCoupling = cp 1) :
    ∀ j, (stages T y facts h2 bot (fun i => cp (i + 2)) j).coupling = cp j ∧
      (stages T y facts h2 bot (fun i => cp (i + 2)) j).nextCoupling = cp (j + 1)
  | 0 => ⟨h0, h1⟩
  | j + 1 => ⟨(stages_coupling facts h2 bot cp h0 h1 j).2, rfl⟩
private theorem exists_tower_along_flow (A : Ingredients T y) (hco : MarkLawMeasurable)
    {β : ℝ} {k : ℕ} (hfl : ∀ j ≤ k, y ≤ (couplingFlow (T.stepParameters y) β j).1)
    (Λ : LabelSpace) (pt : Λ.Ω)
    (Dq : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ)
    (Φ : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → Finset (TorusSite n) → ℝ)
    (hone : ∀ ω : Λ.Ω, ω = pt) (hmass : Λ.μ {pt} = 1)
    (hden : ∀ (n : ℕ) [NeZero n] (W : TorusField n) (Y : Finset (TorusSite n)) (ω : Y → Λ.Ω),
      Dq n W Y ω = open Classical in
        if Y = thickening (2 * clusterRange β) (torusHotSites (T.stepParameters y) W) then wilsonWeight β n W
        else 0)
    (hc0 : ColdExpansion (T.stepParameters y) 0 β (wilsonWeight β) (fun _ _ _ => 0))
    (hh0 : HullExpansion (T.stepParameters y) 0 β (wilsonWeight β) (fun _ _ _ => 0) Λ Dq Φ
      (fun _ _ _ _ _ => 0))
    (ha0 : ∀ n [NeZero n], (T.stepParameters y).n₀ ≤ n → Measurable (wilsonWeight β n) ∧
      (∀ W, 0 ≤ wilsonWeight β n W) ∧
      (∀ (g : TorusSite n → UnitQuaternion) (W : TorusField n),
        wilsonWeight β n (gaugeTransform g W) = wilsonWeight β n W) ∧
      ∀ (g : TorusIsometry) (W W' : TorusField n), g.Transports W W' → wilsonWeight β n W' = wilsonWeight β n W) :
    ∃ Tw : StageTower (T.stepParameters y), IsImageTower T y Tw β k ∧
      ∀ (s n : ℕ) [NeZero n], (T.stepParameters y).side ∣ n → 64 ≤ n →
        ∀ bad : Finset (TorusBond (n * (T.stepParameters y).side)),
        Measurable fun p : TorusField (n * (T.stepParameters y).side) × TorusField n =>
          markLaw (Tw.stage s).toStepSetup p.1 p.2 bad := by
  have hfit : (T.stepParameters y).Admissible := A.drawn.fits y A.floor
  let flow := couplingFlow (T.stepParameters y) β
  let cp : ℕ → ℝ := fun j => (flow (min j (k + 1))).1
  have hcp : ∀ j, j ≤ k + 1 → cp j = (flow j).1 := fun j hj => by
    show (flow (min j (k + 1))).1 = _
    rw [min_eq_left hj]
  have hcpy : ∀ j, j ≤ k → y ≤ cp j := fun j hj => by
    rw [hcp j (by omega)]
    exact hfl j hj
  let bot : ChainStage (T.stepParameters y) :=
    ⟨0, β, cp 1, wilsonWeight β, fun _ _ _ => 0, Λ, Dq, Φ, fun _ _ _ _ _ => 0, T.ρA, T.cutoff⟩
  let xs : ℕ → ℝ := fun i => cp (i + 2)
  have h2 := two_le_side_of A
  let lev := stages T y A.labels h2 bot xs
  have hx : ∀ j, (lev j).coupling = cp j ∧ (lev j).nextCoupling = cp (j + 1) :=
    stages_coupling A.labels h2 bot cp (by
      show β = (flow (min 0 (k + 1))).1
      simp [flow, couplingFlow]) rfl
  have ht : ∀ j, (lev j).depth = j := stages_depth A.labels h2 bot xs rfl
  have hρ : ∀ j, (lev j).anchorRadius = T.ρA := stages_anchorRadius A.labels h2 bot xs
  have hp : ∀ j, (lev j).barrierFn = T.cutoff := stages_barrierFn A.labels h2 bot xs
  have good : ∀ j, j ≤ k + 1 → (lev j).functional = (flow j).2 ∧ (lev j).toStepSetup.HasExpansions ∧
      (lev j).toStepSetup.IsSymmetricWeight := by
    intro j
    induction j with
    | zero => exact fun _ => ⟨rfl, ⟨hc0, hh0⟩, ha0⟩
    | succ j ih =>
      intro hj
      obtain ⟨hD, hrow, hA⟩ := ih (by omega)
      have hxj : (lev j).coupling = (flow j).1 := (hx j).1.trans (hcp j (by omega))
      have hy : y ≤ (lev j).coupling := (hx j).1 ▸ hcpy j (by omega)
      have hrs := expansionCoupling_eq_shifted A hy hrow hA (hρ j) (hp j)
      have hx' : (lev j).nextCoupling = (lev j).toStepSetup.shiftedCoupling T.lam := by
        rw [← hrs, ht j, hxj, hD, (hx j).2, hcp (j + 1) hj]
        rfl
      obtain ⟨_, hup⟩ := next_stage_spec A hy hrow hA (hρ j) (hp j) hx'
      obtain ⟨hr, ha⟩ := hup (A.labels _ h2) (xs j)
      refine ⟨?_, hr, ha⟩
      show kernelImage (T.stepParameters y) (lev j).coupling (lev j).functional =
        kernelImage (T.stepParameters y) (flow j).1 (flow j).2
      rw [hxj, hD]
  have table : ∀ j, j ≤ k → (lev j).toStepSetup.OnParameters T y := by
    intro j hj
    obtain ⟨hD, hrow, hA⟩ := good j (by omega)
    have hxj : (lev j).coupling = (flow j).1 := (hx j).1.trans (hcp j (by omega))
    have hy : y ≤ (lev j).coupling := (hx j).1 ▸ hcpy j hj
    have hrs := expansionCoupling_eq_shifted A hy hrow hA (hρ j) (hp j)
    have hx' : (lev j).nextCoupling = (lev j).toStepSetup.shiftedCoupling T.lam := by
      rw [← hrs, ht j, hxj, hD, (hx j).2, hcp (j + 1) (by omega)]
      rfl
    exact (next_stage_spec A hy hrow hA (hρ j) (hp j) hx').1
  have hstage := stage_stageTowerOf (T := T) (y := y) A.labels h2 bot pt xs
  have hrange : ∀ j, j ≤ k → clusterRange (cp j) ≤ clusterRange (cp (j + 1)) + 1 := by
    intro j hj
    have h := (table j hj).isStep.2.2
    have e1 : (lev j).toStepSetup.range = clusterRange (cp j) := by
      show clusterRange (lev j).coupling = _
      rw [(hx j).1]
    have e2 : (lev j).toStepSetup.nextRange = clusterRange (cp (j + 1)) := by
      show clusterRange (lev j).nextCoupling = _
      rw [(hx j).2]
    rw [e1, e2] at h
    exact h
  refine ⟨stageTowerOf T y A.labels h2 bot pt xs, ⟨⟨⟨rfl, rfl, hone, hmass, ?_⟩, fun j hj => ?_, fun j hj => ?_⟩,
    fun j _ => rfl, fun j _ => ?_⟩, fun s n _ hLn h64 bad => ?_⟩
  · exact hden
  · rw [hstage j]
    exact (hx j).1.trans (hcp j hj)
  · rw [hstage j]
    exact table j hj
  · show (stages T y A.labels h2 bot xs j).toStepSetup.renormalizedDensity T.lam = _
    rw [hstage j]
  · rw [hstage s]
    have hrr : clusterRange (cp s) ≤ clusterRange (cp (s + 1)) + 1 := by
      by_cases hs : s ≤ k
      · exact hrange s hs
      · have e : cp s = cp (s + 1) := by
          show (flow (min s (k + 1))).1 = (flow (min (s + 1) (k + 1))).1
          rw [min_eq_right (by omega), min_eq_right (by omega)]
        rw [e]
        omega
    have hm : (lev s).toStepSetup.frameReach = clusterRange (cp s) / 2 ^ 11 := by
      show clusterRange (lev s).coupling / 2 ^ 11 = _
      rw [(hx s).1]
    have hr' : (lev s).toStepSetup.nextRange = clusterRange (cp (s + 1)) := by
      show clusterRange (lev s).nextCoupling = _
      rw [(hx s).2]
    have hL : 0 < T.side := Nat.pos_of_ne_zero (NeZero.ne _)
    have hge' : 2 ^ 40 ≤ clusterRange (cp s) := by
      by_cases hs : s ≤ k
      · have hge := clusterRange_ge A (hcpy s hs)
        omega
      · have hge := clusterRange_ge A (hcpy k le_rfl)
        have h2' := hrange k le_rfl
        have e : cp s = cp (k + 1) := by
          show (flow (min s (k + 1))).1 = (flow (min (k + 1) (k + 1))).1
          rw [min_eq_right (by omega), min_eq_left (by omega)]
        rw [e]
        omega
    refine hco T A.drawn y (lev s).toStepSetup rfl hfit (hρ s) ?_ ?_ ?_ n hLn h64 bad
    · show IsCutoff T.ballRadius (lev s).barrierFn
      rw [hp s]
      exact A.drawn.cut
    · rw [hm]
      norm_num at hge' ⊢
      omega
    · rw [hm, hr']
      norm_num at hge' ⊢
      omega
end FlowInImageTower
open FlowInImageTower in
theorem flowInImageTower (hS : CoarseStatesFormHullExpansion) (hC : ImageHasColdExpansion)
    (hOne : ColdExpansionCouplingUnique) (hLab : CoarseLabelsStandard)
    (hImg : KernelImageIsDensity) (hD : ImageHasHullExpansion) (hReg : ImageHasHullExpansionRegularity)
    (hP : ImageHasHullExpansionPrice) (hFl : EventuallyFloorConditions) (hW : wilsonWeightSingleLabelStatement)
    (hCo : MarkLawMeasurable) : flowInImageTowerStatement := by
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
  have A : Ingredients T y := ⟨hT, h6, fun x hx => hyF x (h5.trans hx), hyC y h1, hyD y h2, hyR y h3, hyP y h4,
    hS, hOne, hLab, hImg⟩
  refine fun β k hfl => ?_
  have hβ : y ≤ β := hfl 0 (Nat.zero_le _)
  obtain ⟨Λ, pt, Dq, Φ, g1, g2, g3, g4, g5⟩ := hW (T.stepParameters y) hfit hCder β hβ
  obtain ⟨Tw, hst, hco⟩ := exists_tower_along_flow A hCo hfl Λ pt Dq Φ g1 g2 g3 g4 g5 (hrow₀ β hβ).1
  refine ⟨Tw, hst, fun s n _ bad => ?_⟩
  by_cases hg : (T.stepParameters y).side ∣ n ∧ 64 ≤ n
  · exact hco s n hg.1 hg.2 bad
  · have hg' : ¬ ((Tw.stage s).toStepSetup.params.side ∣ n ∧ 64 ≤ n) := hg
    have e : (fun p : TorusField (n * (T.stepParameters y).side) × TorusField n =>
        markLaw (Tw.stage s).toStepSetup p.1 p.2 bad) = fun _ => if bad = ∅ then 1 else 0 := by
      funext p
      unfold markLaw
      rw [if_neg hg']
    rw [e]
    exact measurable_const
end YangMills.Construction.FreeEnergies
end
