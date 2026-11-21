import YangMills.Construction.ClusterExpansionOfAStep.ColdSettingIsCold
import YangMills.Construction.ResponseInTheExpansion.BlockRemainderAboveTheFrameProof
import YangMills.Construction.ResponseInTheExpansion.ColdLawOfAStepIsALaw
import YangMills.Construction.ResponseInTheExpansion.ImageOfOneAtABlock
import YangMills.Construction.ResponseInTheExpansion.ScoresAboveTheFrames
import YangMills.Construction.ResponseInTheExpansion.SharesOfALevelAreBounded
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.ResponseInTheExpansion
namespace BlockImageOfOne
open TorusFields TorusLumps StepSettings StepCosts StepGas RenormalizationStepParameters ColdStepAtMirrorFrames
  Interpolation WeightedResponses
open BlockAverages hiding unitStep
section LawMeans
open MeasureTheory _root_.YangMills.Construction.Dilation
variable {R : StepSetup} {A : ResponseSetup R} {n : ℕ} [NeZero n]
abbrev topCells (R : StepSetup) (n : ℕ) := finiteCells (torusFrame R.params.side R.depth n)
abbrev topCellOfBlock (R : StepSetup) (Y : TorusSite n) : (torusFrame R.params.side R.depth n).Cell :=
  torusSiteInFrame (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top Y
abbrev lawMean (R : StepSetup) (V : TorusField n) (H : StepVariable (topCells R n) → ℝ) : ℝ :=
  ballExpectation (coldHalfLawOf R).radialWeight ((coldHalfLawOf R).exponent (coldTopField R V)) H
abbrev LawIntegrable (R : StepSetup) (V : TorusField n) (H : StepVariable (topCells R n) → ℝ) : Prop :=
  Integrable fun k => H k * coldHalfDensity R V k
structure BlockIdentityData (R : StepSetup) (A : ResponseSetup R) (n : ℕ) [NeZero n] (V : TorusField n) : Prop where
  isBallLaw : IsBallLaw (coldHalfLawOf R).ballRadius (coldHalfLawOf R).radialWeight
    ((coldHalfLawOf R).exponent (coldTopField R V))
  isCold_above : ∀ k : StepVariable (topCells R n), (∀ b, ‖k b‖ < R.ballRadius) →
    IsCold R.params.threshold (coldFieldAboveFrames R V k)
  share_integrable : ∀ y : TorusSite (n * R.params.side), LawIntegrable R V fun k =>
    levelShare R.params.coupling R.params.side R.depth Finset.univ y (coldFieldAboveFrames R V k)
  remainder_integrable : ∀ y : TorusSite (n * R.params.side), LawIntegrable R V fun k =>
    centered A.siteRemainder (n * R.params.side) y (coldFieldAboveFrames R V k)
  cost_eq : ∀ (k : StepVariable (topCells R n)) (Y : TorusSite n), (∀ b, ‖k b‖ < R.ballRadius) →
    ∑ y ∈ sitesInBlocks R.params.side {Y},
        levelShare R.params.coupling R.params.side R.depth Finset.univ y (coldFieldAboveFrames R V k) +
        R.params.coupling / 2 * ∑ i : Fin 4,
          (bondFit R.params (coldFieldAboveFrames R V k) V (coldChartSetting R V).bases (Y, i) +
          bondFit R.params (coldFieldAboveFrames R V k) V (coldChartSetting R V).bases (Y - unitStep n i, i)) =
      (coldHalfLawOf R).blockCost (topCellOfBlock R Y) k (coldTopField R V)
  expansion_eq : ∀ (k : StepVariable (topCells R n)) (Y : TorusSite n),
    cellCentredExpansion false R.params.coupling R.anchorRadius R.frameReach (localFamilyOfDensity A.siteRemainder)
        (topCellOfBlock R Y) k (coldTopField R V) =
      ∑ y ∈ sitesInBlocks R.params.side {Y}, centered A.siteRemainder (n * R.params.side) y (coldFieldAboveFrames R V k)
  top_share_eq : ∀ Y : TorusSite n, levelShare R.params.coupling R.params.side (R.depth + 1) Finset.univ Y V =
    minimalCellShare R.params.coupling (topCells R n) (topCellOfBlock R Y) (coldTopField R V)
  bond_eq : ∀ (Y : TorusSite n) (i : Fin 4) (back : Bool),
    cellBond (topCellOfBlock R Y) i back = torusBondInFrame R (if back then Y - unitStep n i else Y, i)
  score_above : ∀ c : TorusBond n, BondScoreAboveCold R V c
  blockMean_one : ∀ Y : TorusSite n, blockMean R.params.side (R.depth + 1) n Y (constOneWeight _) = 1
  response_eq : ∀ (y : TorusSite (n * R.params.side)) (W : TorusField (n * R.params.side)),
    IsCold R.params.threshold W →
    centeredResponse A.cold (n * R.params.side) y W (constOneWeight _) =
      A.coeff * levelShare R.params.coupling R.params.side R.depth Finset.univ y W +
        centered A.siteRemainder (n * R.params.side) y W
  image_eq : ∀ Y : TorusSite n, A.coldStep n Y V (constOneWeight _) =
    coldTermAbove A V Y (constOneWeight _) + gasTermAtBlock A (coldCaseGround R V) Y (constOneWeight _) +
      ∑ y ∈ sitesInBlocks R.params.side {Y},
        A.cold (n * R.params.side) y (trivialField (n * R.params.side)) (constOneWeight _)
  coupling_pos : 0 < R.coupling
  params_coupling_pos : 0 < R.params.coupling
  ne_zero : n ≠ 0
theorem lawMean_congr {V : TorusField n} (f : BlockIdentityData R A n V) {H H' : StepVariable (topCells R n) → ℝ}
    (h : ∀ k, (∀ b, ‖k b‖ < R.ballRadius) → H k = H' k) : lawMean R V H = lawMean R V H' := by
  unfold lawMean ballExpectation
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  by_cases hk : ∀ b, ‖k b‖ < R.ballRadius
  · show H k * _ = H' k * _
    rw [h k hk]
  · show H k * _ = H' k * _
    rw [f.isBallLaw.eq_zero_outside k hk]
    simp
theorem lawIntegrable_congr {V : TorusField n} (f : BlockIdentityData R A n V)
    {H H' : StepVariable (topCells R n) → ℝ}
    (h : ∀ k, (∀ b, ‖k b‖ < R.ballRadius) → H k = H' k) (hH : LawIntegrable R V H') : LawIntegrable R V H := by
  refine hH.congr (Filter.Eventually.of_forall fun k => ?_)
  by_cases hk : ∀ b, ‖k b‖ < R.ballRadius
  · show H' k * _ = H k * _
    rw [h k hk]
  · show H' k * _ = H k * _
    have := f.isBallLaw.eq_zero_outside k hk
    unfold coldHalfDensity
    rw [this]
    simp
theorem lawIntegrable_add {V : TorusField n} {H H' : StepVariable (topCells R n) → ℝ}
    (h : LawIntegrable R V H) (h' : LawIntegrable R V H') :
    LawIntegrable R V fun k => H k + H' k := by
  refine (h.add h').congr (Filter.Eventually.of_forall fun k => ?_)
  show H k * _ + H' k * _ = (H k + H' k) * _
  ring
theorem lawIntegrable_const_mul {V : TorusField n} (c : ℝ) {H : StepVariable (topCells R n) → ℝ}
    (h : LawIntegrable R V H) : LawIntegrable R V fun k => c * H k := by
  refine (h.const_mul c).congr (Filter.Eventually.of_forall fun k => ?_)
  show c * (H k * _) = c * H k * _
  ring
theorem lawIntegrable_const {V : TorusField n} (f : BlockIdentityData R A n V) (c : ℝ) :
    LawIntegrable R V fun _ => c :=
  f.isBallLaw.integrable.const_mul c
theorem lawIntegrable_sum {V : TorusField n} {J : Type} (s : Finset J)
    {H : J → StepVariable (topCells R n) → ℝ}
    (h : ∀ j ∈ s, LawIntegrable R V (H j)) : LawIntegrable R V fun k => ∑ j ∈ s, H j k := by
  refine (integrable_finsetSum s h).congr (Filter.Eventually.of_forall fun k => ?_)
  simp only [Finset.sum_mul]
theorem lawMean_add {V : TorusField n} (f : BlockIdentityData R A n V) {H H' : StepVariable (topCells R n) → ℝ}
    (h : LawIntegrable R V H) (h' : LawIntegrable R V H') :
    lawMean R V (fun k => H k + H' k) = lawMean R V H + lawMean R V H' :=
  ballExpectation_add f.isBallLaw h h'
theorem lawMean_const {V : TorusField n} (f : BlockIdentityData R A n V) (c : ℝ) :
    lawMean R V (fun _ => c) = c :=
  ballExpectation_const f.isBallLaw c
theorem lawMean_sum {V : TorusField n} (f : BlockIdentityData R A n V) {J : Type} (s : Finset J)
    {H : J → StepVariable (topCells R n) → ℝ} (h : ∀ j ∈ s, LawIntegrable R V (H j)) :
    lawMean R V (fun k => ∑ j ∈ s, H j k) = ∑ j ∈ s, lawMean R V (H j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using ballExpectation_const f.isBallLaw 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [lawMean_add f (h a (Finset.mem_insert_self a s))
      (lawIntegrable_sum s fun j hj => h j (Finset.mem_insert_of_mem hj)),
      ih fun j hj => h j (Finset.mem_insert_of_mem hj)]
end LawMeans
section Frames
variable {F : BlockFrame} (a ρA x : ℝ) (m : ℕ) (W : F.GaugeField F.top) (k : StepVariable (finiteCells F))
theorem interpolatedFrame_one (b : F.Site F.depth × Fin 4) :
    interpolatedFrame 1 a ρA m b W = stepFrame false a ρA m b W := by
  unfold interpolatedFrame
  simp
theorem interpolatedCoords_one : interpolatedCoords 1 a ρA m W k = coordsAboveFrame false a ρA m W k := by
  funext z i
  unfold interpolatedCoords coordsAboveFrame
  rw [interpolatedFrame_one]
theorem interpolatedField_one : interpolatedField 1 a ρA m W k = fieldAboveFrame false a ρA m W k := by apply _root_.YangMills.SharedProofs.p24311 <;> assumption
theorem familyLawExponent_one (f : LocalFamily) :
    familyLawExponent 1 a ρA x m f W k = stepExponent false a ρA x m f 1 W k := by
  unfold familyLawExponent interpolatedExponent stepExponent interpolatedExpansion centredExpansion
  simp only [interpolatedCoords_one, interpolatedField_one, one_mul]
theorem interpolatedCoords_one_zero :
    interpolatedCoords 1 a ρA m W 0 = fun z i => stepFrame false a ρA m (z, i) W := by
  funext z i
  unfold interpolatedCoords stepCoordinates
  rw [interpolatedFrame_one]
  by_cases h : (z, i) ∈ chordBonds (finiteCells F)
  · have : toImaginary (0 : EuclideanSpace ℝ (Fin 3)) = 0 := by
      apply Subtype.ext
      ext <;> simp [toImaginary] <;> rfl
    simp [h, this]
  · simp [h]
end Frames
section BlockIdentity
open MeasureTheory _root_.YangMills.Construction.Dilation
variable {R : StepSetup} {A : ResponseSetup R} {n : ℕ} [NeZero n]
abbrev shareAbove (R : StepSetup) (V : TorusField n) (y : TorusSite (n * R.params.side))
    (k : StepVariable (topCells R n)) : ℝ :=
  levelShare R.params.coupling R.params.side R.depth Finset.univ y (coldFieldAboveFrames R V k)
abbrev remainderAbove (A : ResponseSetup R) (V : TorusField n) (y : TorusSite (n * R.params.side))
    (k : StepVariable (topCells R n)) : ℝ :=
  centered A.siteRemainder (n * R.params.side) y (coldFieldAboveFrames R V k)
abbrev fitAbove (R : StepSetup) (V : TorusField n) (c : TorusBond n) (k : StepVariable (topCells R n)) : ℝ :=
  bondFit R.params (coldFieldAboveFrames R V k) V (coldChartSetting R V).bases c
abbrev scoreTailAbove (R : StepSetup) (V : TorusField n) (c : TorusBond n) (k : StepVariable (topCells R n)) : ℝ :=
  (coldHalfLawOf R).scoreRemainderAt (torusBondInFrame R c) k (coldTopField R V)
theorem coldExpectationAbove_response {V : TorusField n} (f : BlockIdentityData R A n V)
    (y : TorusSite (n * R.params.side)) :
    coldExpectationAbove R V (fun W => centeredResponse A.cold (n * R.params.side) y W (constOneWeight _)) =
      A.coeff * lawMean R V (shareAbove R V y) + lawMean R V (remainderAbove A V y) := by
  show lawMean R V (fun k => centeredResponse A.cold (n * R.params.side) y (coldFieldAboveFrames R V k)
    (constOneWeight _)) = _
  rw [lawMean_congr f (H' := fun k => A.coeff * shareAbove R V y k + remainderAbove A V y k)
      (fun k hk => f.response_eq y _ (f.isCold_above k hk)),
    lawMean_add f (lawIntegrable_const_mul _ (f.share_integrable y)) (f.remainder_integrable y)]
  congr 1
  exact ballExpectation_const_mul _ _
theorem coldExpectationAbove_score {V : TorusField n} (f : BlockIdentityData R A n V) (c : TorusBond n) :
    coldExpectationAbove R V (fun W => bondScore R.params R.coupling W V (coldChartSetting R V).bases c) =
      lawMean R V (fitAbove R V c) - 3 / (2 * R.params.coupling * R.coupling) -
        (R.coupling ^ 2)⁻¹ * lawMean R V (scoreTailAbove R V c) := by
  have hs := f.score_above c
  show lawMean R V (fun k => bondScore R.params R.coupling (coldFieldAboveFrames R V k) V
    (coldChartSetting R V).bases c) = _
  rw [lawMean_congr f (H' := fun k => fitAbove R V c k +
      (-(3 / (2 * R.params.coupling * R.coupling)) + -(R.coupling ^ 2)⁻¹ * scoreTailAbove R V c k))
    (fun k hk => by
      rw [hs.eq_at_point k hk]
      ring)]
  have i1 : LawIntegrable R V (fitAbove R V c) := hs.fit_integrable
  have i2 : LawIntegrable R V (scoreTailAbove R V c) := hs.remainder_integrable
  rw [lawMean_add f i1 (lawIntegrable_add (lawIntegrable_const f _) (lawIntegrable_const_mul _ i2)),
    lawMean_add f (lawIntegrable_const f _) (lawIntegrable_const_mul _ i2), lawMean_const f,
    show lawMean R V (fun k => -(R.coupling ^ 2)⁻¹ * scoreTailAbove R V c k) =
      -(R.coupling ^ 2)⁻¹ * lawMean R V (scoreTailAbove R V c) from ballExpectation_const_mul _ _]
  ring
theorem blockCost_integrable {V : TorusField n} (f : BlockIdentityData R A n V) (Y : TorusSite n) :
    LawIntegrable R V fun k => (coldHalfLawOf R).blockCost (topCellOfBlock R Y) k (coldTopField R V) := by
  have iF : ∀ c, LawIntegrable R V (fitAbove R V c) := fun c => (f.score_above c).fit_integrable
  have iS : LawIntegrable R V fun k => ∑ y ∈ sitesInBlocks R.params.side {Y}, shareAbove R V y k :=
    lawIntegrable_sum _ fun y _ => f.share_integrable y
  have iB : LawIntegrable R V fun k =>
      ∑ i : Fin 4, (fitAbove R V (Y, i) k + fitAbove R V (Y - unitStep n i, i) k) :=
    lawIntegrable_sum _ fun i _ => lawIntegrable_add (iF _) (iF _)
  exact lawIntegrable_congr f (fun k hk => (f.cost_eq k Y hk).symm)
    (lawIntegrable_add iS (lawIntegrable_const_mul _ iB))
theorem lawMean_blockCost {V : TorusField n} (f : BlockIdentityData R A n V) (Y : TorusSite n) :
    ∑ y ∈ sitesInBlocks R.params.side {Y}, lawMean R V (shareAbove R V y) +
      R.params.coupling / 2 * ∑ i : Fin 4,
        (lawMean R V (fitAbove R V (Y, i)) + lawMean R V (fitAbove R V (Y - unitStep n i, i))) =
      lawMean R V fun k => (coldHalfLawOf R).blockCost (topCellOfBlock R Y) k (coldTopField R V) := by
  have iF : ∀ c, LawIntegrable R V (fitAbove R V c) := fun c => (f.score_above c).fit_integrable
  have iS : LawIntegrable R V fun k => ∑ y ∈ sitesInBlocks R.params.side {Y}, shareAbove R V y k :=
    lawIntegrable_sum _ fun y _ => f.share_integrable y
  have iB : LawIntegrable R V fun k =>
      ∑ i : Fin 4, (fitAbove R V (Y, i) k + fitAbove R V (Y - unitStep n i, i) k) :=
    lawIntegrable_sum _ fun i _ => lawIntegrable_add (iF _) (iF _)
  rw [lawMean_congr f (fun k hk => (f.cost_eq k Y hk).symm)]
  show _ = lawMean R V (fun k => (∑ y ∈ sitesInBlocks R.params.side {Y}, shareAbove R V y k) +
    R.params.coupling / 2 * ∑ i : Fin 4, (fitAbove R V (Y, i) k + fitAbove R V (Y - unitStep n i, i) k))
  rw [lawMean_add f iS (lawIntegrable_const_mul _ iB), lawMean_sum f _ fun y _ => f.share_integrable y,
    show lawMean R V (fun k => R.params.coupling / 2 *
        ∑ i : Fin 4, (fitAbove R V (Y, i) k + fitAbove R V (Y - unitStep n i, i) k)) =
      R.params.coupling / 2 * lawMean R V (fun k =>
        ∑ i : Fin 4, (fitAbove R V (Y, i) k + fitAbove R V (Y - unitStep n i, i) k)) from
      ballExpectation_const_mul _ _,
    lawMean_sum f _ fun i _ => lawIntegrable_add (iF _) (iF _)]
  congr 2
  exact Finset.sum_congr rfl fun i _ => (lawMean_add f (iF _) (iF _)).symm
theorem lawMean_blockCost_eq {V : TorusField n} (f : BlockIdentityData R A n V) (Y : TorusSite n) :
    (lawMean R V fun k => (coldHalfLawOf R).blockCost (topCellOfBlock R Y) k (coldTopField R V)) =
      (coldHalfLawOf R).expectationOf ((coldHalfLawOf R).blockIncrement (topCellOfBlock R Y)) (coldTopField R V) +
        (coldHalfLawOf R).blockCost (topCellOfBlock R Y) 0 (coldTopField R V) := by
  set C0 : ℝ := (coldHalfLawOf R).blockCost (topCellOfBlock R Y) 0 (coldTopField R V) with hC0
  have iM : LawIntegrable R V fun k =>
      (coldHalfLawOf R).blockIncrement (topCellOfBlock R Y) k (coldTopField R V) := by
    refine lawIntegrable_congr f (fun k _ => ?_) (lawIntegrable_add (blockCost_integrable f Y)
      (lawIntegrable_const f (-C0)))
    unfold ColdHalfLaw.blockIncrement
    ring
  have e : (fun k => (coldHalfLawOf R).blockCost (topCellOfBlock R Y) k (coldTopField R V)) =
      fun k => (coldHalfLawOf R).blockIncrement (topCellOfBlock R Y) k (coldTopField R V) + C0 := by
    funext k
    unfold ColdHalfLaw.blockIncrement
    ring
  rw [e, lawMean_add f iM (lawIntegrable_const f _), lawMean_const f]
  rfl
theorem densityOfTopFamily_eq {V : TorusField n} (f : BlockIdentityData R A n V) (Y : TorusSite n) :
    densityOfTopFamily R.params.side R.depth (blockConditionalMean R A.siteRemainder) n Y V =
      ∑ y ∈ sitesInBlocks R.params.side {Y}, lawMean R V (remainderAbove A V y) := by
  rw [← lawMean_sum f _ fun y _ => f.remainder_integrable y]
  have e : (coldHalfLawOf R).exponent (coldTopField R V) =
      stepExponent false R.params.coupling R.anchorRadius R.coupling R.frameReach
        (localFamilyOfDensity R.density) 1 (coldTopField R V) :=
    funext fun k => familyLawExponent_one _ _ _ _ _ _ _
  show cutoffMean R.ballRadius R.barrierFn (stepExponent false R.params.coupling R.anchorRadius R.coupling
      R.frameReach (localFamilyOfDensity R.density) 1 (coldTopField R V))
    (fun η => cellCentredExpansion false R.params.coupling R.anchorRadius R.frameReach
      (localFamilyOfDensity A.siteRemainder) (topCellOfBlock R Y) η (coldTopField R V)) = _
  show _ = ballExpectation (coldHalfLawOf R).radialWeight ((coldHalfLawOf R).exponent (coldTopField R V)) _
  rw [e]
  show ballExpectation (coldHalfLawOf R).radialWeight _ _ = _
  simp only [f.expansion_eq]
theorem scoreTail_split {V : TorusField n} (f : BlockIdentityData R A n V) (c : TorusBond n) :
    (coldHalfLawOf R).scoreRemainderAt (torusBondInFrame R c) 0 (coldTopField R V) +
        (coldHalfLawOf R).expectationOf ((coldHalfLawOf R).scoreRemainderIncrement (torusBondInFrame R c))
          (coldTopField R V) =
      lawMean R V (scoreTailAbove R V c) := by
  set c₀ : ℝ := (coldHalfLawOf R).scoreRemainderAt (torusBondInFrame R c) 0 (coldTopField R V) with hc₀
  have i2 : LawIntegrable R V (scoreTailAbove R V c) := (f.score_above c).remainder_integrable
  have iM : LawIntegrable R V fun k =>
      (coldHalfLawOf R).scoreRemainderIncrement (torusBondInFrame R c) k (coldTopField R V) := by
    refine lawIntegrable_congr f (fun k _ => ?_) (lawIntegrable_add i2 (lawIntegrable_const f (-c₀)))
    unfold ColdHalfLaw.scoreRemainderIncrement
    ring
  have e : scoreTailAbove R V c = fun k =>
      (coldHalfLawOf R).scoreRemainderIncrement (torusBondInFrame R c) k (coldTopField R V) + c₀ := by
    funext k
    unfold ColdHalfLaw.scoreRemainderIncrement
    ring
  rw [e, lawMean_add f iM (lawIntegrable_const f _), lawMean_const f, add_comm]
  rfl
theorem blockMeanScoreTails_eq {V : TorusField n} (f : BlockIdentityData R A n V) (Y : TorusSite n) :
    blockMeanScoreTails R (torusFrame R.params.side R.depth n) (topCellOfBlock R Y) (coldTopField R V) =
      ∑ i : Fin 4, (lawMean R V (scoreTailAbove R V (Y, i)) +
        lawMean R V (scoreTailAbove R V (Y - unitStep n i, i))) := by
  unfold blockMeanScoreTails
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_bool, f.bond_eq, f.bond_eq, add_comm]
  exact congrArg₂ (· + ·) (scoreTail_split f _) (scoreTail_split f _)
theorem scoreTailTerm_eq {V : TorusField n} (f : BlockIdentityData R A n V) (Y : TorusSite n) :
    scoreTailTerm A n Y V = -(R.params.coupling / 2 * A.coeff * (R.coupling ^ 2)⁻¹) *
      ∑ i : Fin 4, (lawMean R V (scoreTailAbove R V (Y, i)) +
        lawMean R V (scoreTailAbove R V (Y - unitStep n i, i))) := by
  rw [← blockMeanScoreTails_eq f Y]
  rfl
theorem frameTerm_eq {V : TorusField n} (f : BlockIdentityData R A n V) (Y : TorusSite n) :
    frameTerm A n Y V = A.coeff * ((coldHalfLawOf R).blockCost (topCellOfBlock R Y) 0 (coldTopField R V) -
      levelShare R.params.coupling R.params.side (R.depth + 1) Finset.univ Y V) := by
  have hx : R.coupling ≠ 0 := f.coupling_pos.ne'
  have e : frameTerm A n Y V =
      -(A.coeff / R.coupling) * frameDensity false R.params.coupling R.anchorRadius R.coupling R.frameReach
        (topCellOfBlock R Y) (coldTopField R V) := rfl
  rw [e, f.top_share_eq Y]
  unfold frameDensity ColdHalfLaw.blockCost
  rw [show interpolatedCoords 1 (coldHalfLawOf R).a (coldHalfLawOf R).chartRadius (coldHalfLawOf R).mirrorRadius
      (coldTopField R V) 0 =
    fun z i => stepFrame false R.params.coupling R.anchorRadius R.frameReach (z, i) (coldTopField R V) from
      interpolatedCoords_one_zero _ _ _ _]
  show _ = A.coeff * (cellEnergyShare R.params.coupling (topCellOfBlock R Y) _ (coldTopField R V) - _)
  field_simp
omit [NeZero n] in
theorem sum_scores_split (c₀ u : ℝ) (F Th : TorusBond n → ℝ) (Y : TorusSite n) :
    ∑ i : Fin 4, (F (Y, i) - c₀ - u * Th (Y, i) +
        (F (Y - unitStep n i, i) - c₀ - u * Th (Y - unitStep n i, i))) =
      ∑ i : Fin 4, (F (Y, i) + F (Y - unitStep n i, i)) - 8 * c₀ -
        u * ∑ i : Fin 4, (Th (Y, i) + Th (Y - unitStep n i, i)) := by
  have e : ∀ i : Fin 4, F (Y, i) - c₀ - u * Th (Y, i) +
      (F (Y - unitStep n i, i) - c₀ - u * Th (Y - unitStep n i, i)) =
      (F (Y, i) + F (Y - unitStep n i, i)) - 2 * c₀ - u * (Th (Y, i) + Th (Y - unitStep n i, i)) :=
    fun i => by ring
  simp only [e, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  push_cast
  ring
theorem coldStep_one_eq {V : TorusField n} (f : BlockIdentityData R A n V) (Y : TorusSite n) :
    A.coldStep n Y V (constOneWeight _) =
      A.coeff * levelShare R.params.coupling R.params.side (R.depth + 1) Finset.univ Y V +
        frameTerm A n Y V + incrementTerm A n Y V +
        densityOfTopFamily R.params.side R.depth (blockConditionalMean R A.siteRemainder) n Y V +
        scoreTailTerm A n Y V + gasTerm A n Y V + blockConstantTerm A n Y := by
  have hx : R.coupling ≠ 0 := f.coupling_pos.ne'
  have ha : R.params.coupling ≠ 0 := f.params_coupling_pos.ne'
  have hGas : gasTerm A n Y V = gasTermAtBlock A (coldCaseGround R V) Y (constOneWeight _) := by
    unfold gasTerm
    rw [dif_neg f.ne_zero]
  have hConst : blockConstantTerm A n Y = ∑ y ∈ sitesInBlocks R.params.side {Y},
      A.cold (n * R.params.side) y (trivialField (n * R.params.side)) (constOneWeight _) -
      6 * A.coeff / R.coupling := by
    unfold blockConstantTerm
    rw [dif_neg f.ne_zero]
  have hIncr : incrementTerm A n Y V = A.coeff *
      (coldHalfLawOf R).expectationOf ((coldHalfLawOf R).blockIncrement (topCellOfBlock R Y))
        (coldTopField R V) := rfl
  rw [f.image_eq Y, scoreTailTerm_eq f Y, frameTerm_eq f Y, hGas, hConst, densityOfTopFamily_eq f Y, hIncr]
  unfold coldTermAbove
  rw [f.blockMean_one Y]
  have hresp : (∑ y ∈ sitesInBlocks R.params.side {Y},
      coldExpectationAbove R V fun W => centeredResponse A.cold (n * R.params.side) y W
        (constOneWeight (fineSide R.params.side (R.depth + 1) n))) =
      A.coeff * ∑ y ∈ sitesInBlocks R.params.side {Y}, lawMean R V (shareAbove R V y) +
        ∑ y ∈ sitesInBlocks R.params.side {Y}, lawMean R V (remainderAbove A V y) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y _ => coldExpectationAbove_response f y
  rw [hresp]
  simp only [coldExpectationAbove_score f]
  rw [sum_scores_split (3 / (2 * R.params.coupling * R.coupling)) (R.coupling ^ 2)⁻¹
    (fun c => lawMean R V (fitAbove R V c)) (fun c => lawMean R V (scoreTailAbove R V c)) Y]
  have h6 : R.params.coupling / 2 * A.coeff * (8 * (3 / (2 * R.params.coupling * R.coupling))) =
      6 * A.coeff / R.coupling := by
    field_simp
    ring
  have hCost := (lawMean_blockCost f Y).trans (lawMean_blockCost_eq f Y)
  linear_combination A.coeff * hCost - h6
end BlockIdentity
section ColdBounds
open MeasureTheory _root_.YangMills.Construction.Dilation
variable {R : StepSetup} {n : ℕ} [NeZero n]
omit [NeZero n] in
theorem mixedDeriv_order_zero (G : TorusField n → ℝ) (W : TorusField n) (c : Fin 0 → TorusBond n)
    (X : Fin 0 → imaginaryQuaternions) :
    mixedDeriv G W c X = G W := by apply _root_.YangMills.Construction.TorusLumps.mixedDeriv_of_fin_zero <;> assumption
omit [NeZero n] in
theorem fieldsAgreeNear_zero {n' : ℕ} (W : TorusField n) (W' : TorusField n') (y : TorusSite n)
    (y' : TorusSite n') : FieldsAgreeNear W W' y y' 0 := by
  rintro ⟨z, i⟩ ⟨h1, h2⟩
  exfalso
  have a1 := h1 i
  have a2 := h2 i
  simp only [Pi.add_apply, Pi.single_eq_same, CharP.cast_eq_zero, abs_nonpos_iff] at a1 a2
  omega
theorem abs_centered_le_of_isCold {ℓ : TorusLumps.StepParameters} {E E₃ : ℝ} {h : LocalDensity}
    (hf : ColdDensityBounds ℓ E E₃ h) (hσ : 0 < ℓ.threshold) {m : ℕ} [NeZero m]
    (hm : ℓ.n₀ ≤ m) (hm2 : 2 < m) (y : TorusSite m) {W : TorusField m} (hW : IsCold ℓ.threshold W) :
    |centered h m y W| ≤ E / ℓ.weight 0 := by
  have hflat : IsCold ℓ.threshold (trivialField m) := fun x μ ν _ => by
    simpa [curvature, holonomy, trivialField] using hσ
  have e := hf.local_density m m hm hm y y W (trivialField m) 0 (by omega) (by omega) hW hflat
    (fieldsAgreeNear_zero _ _ _ _) 0
    (fun l => l.elim0) (fun l => l.elim0) (by omega) (fun l => l.elim0) (fun l => l.elim0)
  rw [mixedDeriv_order_zero, mixedDeriv_order_zero] at e
  have h0 : centered h m y (trivialField m) = 0 := by
    unfold centered
    ring
  rwa [h0, sub_zero] at e
end ColdBounds
end BlockImageOfOne
open TorusFields TorusLumps StepSettings StepCosts StepGas RenormalizationStepParameters BlockAverages ColdStepAtMirrorFrames
  Interpolation WeightedResponses LevelShares _root_.YangMills.Construction.Dilation BlockImageOfOne MeasureTheory in
theorem imageOfOneAtBlockStatement_holds (himage : coldStepAboveFramesStatement)
    (hscores : scoresAboveFramesStatement) (hlaw : coldHalfLawIsLawStatement)
    (hcs : ColdChartSettingIsCold) (hsb : LevelShareBoundedContinuous) (hw : BlockMeanIsLinearAndLocal) :
    imageOfOneAtBlockStatement := by
  obtain ⟨rt₀, hr, g⟩ := himage
  refine ⟨rt₀, hr, fun T hT hrt K => ?_⟩
  obtain ⟨y₀, g⟩ := g T hT hrt K
  by_cases hC : T.ColdStepHolds
  swap
  · exact ⟨0, fun y _ R A _ _ h => absurd h hC⟩
  obtain ⟨y₁, hs⟩ := hscores T hT hC
  obtain ⟨y₂, hl⟩ := hlaw T hT hC
  obtain ⟨y₃, hc3⟩ := hcs T hT
  refine ⟨max y₀ (max y₁ (max y₂ (max y₃ (max T.floorMin 1)))), fun y hy R A hK hA _ n _ hn Y V hV => ?_⟩
  have e₀ : y₀ ≤ y := le_trans (le_max_left _ _) hy
  have u₁ := le_trans (le_max_right _ _) hy
  have e₁ : y₁ ≤ y := le_trans (le_max_left _ _) u₁
  have u₂ := le_trans (le_max_right _ _) u₁
  have e₂ : y₂ ≤ y := le_trans (le_max_left _ _) u₂
  have u₃ := le_trans (le_max_right _ _) u₂
  have e₃ : y₃ ≤ y := le_trans (le_max_left _ _) u₃
  have u₄ := le_trans (le_max_right _ _) u₃
  have e₄ : T.floorMin ≤ y := le_trans (le_max_left _ _) u₄
  have e₅ : 1 ≤ y := le_trans (le_max_right _ _) u₄
  have hOn := hA.onFamily
  have hσ : R.params.threshold = T.threshold := by rw [hOn.params_eq]; rfl
  have hn₀ : R.params.n₀ = T.n₀ := by rw [hOn.params_eq]; rfl
  have hLL : R.params.side = T.side := by rw [hOn.params_eq]; rfl
  have haa : R.params.coupling = T.coupling := by rw [hOn.params_eq]; rfl
  have hn' : T.n₀ ≤ n := by omega
  have hσ0 : 0 < T.threshold := hT.σ_pos
  have hσR : 0 < R.params.threshold := by rw [hσ]; exact hσ0
  have hV' : IsCold (9 / 8 * T.threshold) V := fun x μ ν hμ => by
    have := hV x μ ν hμ
    rw [hσ] at this
    linarith
  have hodd : Odd R.params.side := by rw [hLL]; exact hT.L_odd
  have hL0 : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hnL : n ≤ n * R.params.side := Nat.le_mul_of_pos_right n hL0
  have hn4 : 4096 ≤ T.n₀ := hT.n₀_ge
  obtain ⟨hL, hcF, hpt, hG, -⟩ := hl y e₂ R hOn n hn' V hV'
  obtain ⟨hcost, hrow, htop, hbond, hsc⟩ := hs y e₁ R hOn n hn' V hV'
  have hcold : ∀ k : StepVariable (topCells R n), (∀ b, ‖k b‖ < R.ballRadius) →
      IsCold R.params.threshold (coldFieldAboveFrames R V k) := by
    intro k hk x μ ν hμ
    obtain ⟨η, hη, e⟩ := hpt k hk
    have := hc3 y e₃ R hOn n hn' V hV' η (fun b => (hη b).le) x μ ν hμ
    rw [← e, hσ]
    linarith
  have key : ∀ (m : ℕ) [NeZero m], T.n₀ ≤ m → ∀ z : TorusSite m, ∃ C : ℝ, ∀ W : TorusField m,
      IsCold R.params.threshold W →
      |levelShare R.params.coupling R.params.side R.depth Finset.univ z W| ≤ C ∧
        ContinuousAt (fun W' : TorusField m =>
          levelShare R.params.coupling R.params.side R.depth Finset.univ z W') W := by
    intro m _ hm z
    rw [haa, hLL, hσ]
    exact hsb T hT y e₄ R.depth m hm z
  have hrs := hA.admissible
  have f : BlockIdentityData R A n V :=
    { isBallLaw := hL
      isCold_above := hcold
      share_integrable := fun y' => by
        obtain ⟨C, hCb⟩ := key (n * R.params.side) (by omega) y'
        refine integrable_mul_density_of_bounded hL (R := C) (fun k hk => ?_)
          fun k hk => (hCb _ (hcold k hk)).1
        exact ((hCb _ (hcold k hk)).2.comp hcF.continuousAt).continuousWithinAt
      remainder_integrable := fun y' => by
        have hsf := hrs.bounds.site_family
        have hc := hG (fun W => centered A.siteRemainder (n * R.params.side) y' W) fun W hW k c X =>
          (hsf.smooth (n * R.params.side) (by omega) y' W hW k c X).sub contDiffAt_const
        exact integrable_mul_density_of_bounded hL hc fun k hk =>
          abs_centered_le_of_isCold hsf hσR (by omega) (by omega) y' (hcold k hk)
      cost_eq := hcost
      expansion_eq := fun k Y => hrow A.siteRemainder k Y
      top_share_eq := htop
      bond_eq := hbond
      score_above := hsc
      blockMean_one := fun Y => (hw R.params.side hodd (R.depth + 1) n Y).1
      response_eq := fun y' W hW => hrs.bounds.share_site (n * R.params.side) (by omega) y' W hW
      image_eq := fun Y => g y e₀ R A hK hA hC n hn Y V hV (constOneWeight _)
      coupling_pos := by
        have := hOn.le_coupling
        linarith
      params_coupling_pos := by
        have := hT.a_ge
        rw [haa]
        linarith
      ne_zero := NeZero.ne n }
  exact coldStep_one_eq f Y
end YangMills.Construction.ResponseInTheExpansion
end
