import YangMills.Construction.ClusterExpansionOfAStep.ChartOnTheTorus
import YangMills.Construction.ClusterExpansionOfAStep.FieldOfASettingAtItsFrames
import YangMills.Construction.ClusterExpansionOfAStep.FloorsOfTheParameters
import YangMills.Construction.ClusterExpansionOfAStep.FrameAgainstTheLeastFieldOfTheCut
import YangMills.Construction.ClusterExpansionOfAStep.TopFrameOfATorus
import YangMills.Construction.ClusterExpansionOfAStep.TreesOfABlock
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages TorusFields TorusLumps TorusCharts TopLevelSites StepSettings StepCosts StepMarks
  RenormalizationStepParameters StepFrames StepFloors BlockOffsets ColdChain ColdStepAtMirrorFrames
namespace FrameField
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem pathHolonomy_eq_one_of_trivial {F : BlockFrame} {j : ℕ} (X : F.GaugeField j)
    (hX : ∀ x i, X x i = 1) :
    ∀ (l : List PathStep) (x : F.Site j), pathHolonomy X x l = 1 := by apply _root_.YangMills.Construction.BlockTrees.pathHolonomy_of_forall_eq_one <;> assumption
theorem gaugeAt_fine_eq_one_of_not_mem_stored (s : ChartSetting R n) (c : SettingCore R n)
    (hodd : Odd R.params.side) (hn : 2 ≤ n)
    (hmk : s.IsMarked c) {x : TorusSite (n * R.params.side)}
    (hx : parentBlock R.params.side x ∉ s.storedBlockSet c) :
    gaugeAt (R := R) s.fine x = 1 := by
  obtain ⟨o, ho, hxo⟩ := exists_fineSite_of_parentBlock hodd (parentBlock R.params.side x) x rfl
  set Y := parentBlock R.params.side x with hY
  set A : Fin 4 → ℤ := fun i => ((Y i).cast : ℤ) + (0 : Fin 4 → ℤ) i with hA
  have hx' : x = siteOfInt (blockPoint R.params.side A o) := hxo
  rw [hx', gaugeAt_blockPoint hodd _ A o ho]
  have hc := (BlockOffsets.mem_centredCube_iff o).mp ho
  have key := pathHolonomy_congr (L := R.params.side) (n' := n) s.fine (trivialField (n * R.params.side))
    (fun i => (R.params.side : ℤ) * A i) (fun i => (R.params.side : ℤ) * A i) (axisPath o 1) 0 ?_
  · have k2 : pathHolonomy (readAtLevel (stepBlockFrame R.params.side n) 0 s.fine)
        (siteOfCoords 0 fun i => (R.params.side : ℤ) * A i) (axisPath o 1) =
        pathHolonomy (readAtLevel (stepBlockFrame R.params.side n) 0 (trivialField (n * R.params.side)))
          (siteOfCoords 0 fun i => (R.params.side : ℤ) * A i) (axisPath o 1) := by
      simpa only [add_zero] using key
    rw [k2]
    exact pathHolonomy_eq_one_of_trivial (F := stepBlockFrame R.params.side n) _ (fun _ _ => rfl) _ _
  · intro b hb
    obtain ⟨g1, g2, g3⟩ := isAxialBond_of_mem_axisPath hc b hb
    have hb1 : b.1 ∈ centredCube R.params.side := (BlockOffsets.mem_centredCube_iff _).mpr g1
    have hb2 : b.1 + Pi.single b.2 1 ∈ centredCube R.params.side :=
      (BlockOffsets.mem_centredCube_iff _).mpr g2
    have htree := isAxialTreeBond_blockPoint (n := n) hodd hn A b.1 hb1 b.2 hb2 g3
    have hblk : parentBlock R.params.side
        (siteOfInt (blockPoint R.params.side A b.1) : TorusSite (n * R.params.side)) = Y := by
      rw [parentBlock_blockPoint hodd _ _ hb1]
      exact siteOfInt_cast_add Y 0 |>.trans (by
        have : (siteOfInt (0 : Fin 4 → ℤ) : TorusSite n) = 0 := by
          funext k
          simp [siteOfInt]
        rw [this, add_zero])
    have h1 := hmk.fine_on_trees (siteOfInt (blockPoint R.params.side A b.1), b.2) (by
      show parentBlock R.params.side
        (siteOfInt (blockPoint R.params.side A b.1) : TorusSite (n * R.params.side)) ∉ _
      rw [hblk]
      exact hx) (by dsimp only; rw [BlockOffsets.torusSiteInFrame_siteOfInt]; exact htree)
    exact h1
theorem norm_frame_sub_minimizerCoord_le (hFr : FrameNearMinimizer) {T : ParameterAssignment}
    (hT : T.Admissible) {y : ℝ}
    (hR : R.OnParameters T y) (hfit : R.params.Admissible) (hn₀ : T.n₀ ≤ n)
    (hrg : RangesAdmissible R.range (clusterRange R.nextCoupling))
    (hrL : R.params.side + 1 < 4 * R.range) (s : ChartSetting R n)
    (hs : s.IsAdmissible) {b : TorusBond (n * R.params.side)} (hb : b ∈ s.free) :
    ‖((s.frame b : imaginaryQuaternions) : ℍ[ℝ]) -
        (minimizerCoord R.params.coupling R.anchorRadius R.params.side R.depth s.region s.coarse b : ℍ[ℝ])‖ ≤
      2 * T.N 0 * T.threshold * Real.exp (-(T.δ₁ * (R.frameReach : ℝ))) := by
  have haR : R.params.coupling = T.coupling := by rw [hR.params_eq]; rfl
  have hLe : R.params.side = T.side := by rw [hR.params_eq]; rfl
  have hσe : R.params.threshold = T.threshold := by rw [hR.params_eq]; rfl
  have hn₀e : R.params.n₀ = T.n₀ := by rw [hR.params_eq]; rfl
  have hchain : ColdChainConstants R.params.coupling T.δ₁ R.params.side T.lam T.ρA T.σA T.cg T.N := by
    rw [haR, hLe]
    exact hT.chain
  have hσ2 : 2 * R.params.threshold ≤ T.σA := by rw [hσe]; exact hT.σ_le
  obtain ⟨_, hfr⟩ := hFr R.params T.δ₁ T.lam T.ρA T.σA T.cg T.N hfit hchain hσ2
  have hbc : b ∈ chartBonds R.params.side n := hs.subset_chart hb
  obtain ⟨hpos₀, -, -, -, -, -, -, hNp, -⟩ := hT.chain
  have hN0 : 0 < T.N 0 := hNp 0
  have hσT := hT.σ_pos
  have key : ∀ (C : Finset (TorusSite n)) (s₂ : ℝ),
      IsStepSituation R.params (clusterRange R.nextCoupling) s.coarse s.region C s₂ → 0 ≤ s₂ →
      s₂ ≤ 2 * T.threshold → parentBlock R.params.side b.1 ∉ C →
      ‖((s.frame b : imaginaryQuaternions) : ℍ[ℝ]) -
          (minimizerCoord R.params.coupling R.anchorRadius R.params.side R.depth s.region s.coarse b : ℍ[ℝ])‖ ≤
        2 * T.N 0 * T.threshold * Real.exp (-(T.δ₁ * (R.frameReach : ℝ))) := by
    intro C s₂ hsit h0 h2 hbC
    have h1 := (hfr R.depth R.range (clusterRange R.nextCoupling) n s.coarse s.region C s₂ hrg hsit b hbc hbC).2
    have e1 : R.anchorRadius = T.ρA := hR.anchorRadius_eq
    have hm : (R.frameReach : ℝ) = ((R.range / 2 ^ 11 : ℕ) : ℝ) := rfl
    show ‖((frameCoord R.params R.anchorRadius R.depth R.frameReach s.coarse b : imaginaryQuaternions) : ℍ[ℝ]) - _‖ ≤ _
    rw [e1, hm]
    refine h1.trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    nlinarith
  rcases hs.region_spec with ⟨hreg, hcold⟩ | ⟨hblk, hreg, hfar⟩
  · refine key ∅ (9 / 8 * R.params.threshold)
      (Or.inr ⟨by rw [hn₀e]; exact hn₀, hcold, hreg, rfl, rfl⟩) ?_ ?_ (by simp)
    · rw [hσe]
      positivity
    · rw [hσe]
      linarith
  · refine key (minimalHull R.params (clusterRange R.nextCoupling) s.coarse) R.params.threshold
      (Or.inl ⟨hblk, hreg, rfl, rfl⟩) ?_ ?_ ?_
    · rw [hσe]
      exact hσT.le
    · rw [hσe]
      linarith
    · intro hin
      have h1 := hfar b hb b.1 hin
      rw [supDist_self] at h1
      omega
end FrameField
open FrameField in
theorem frameFieldNearMinimizer_holds (hFr : FrameNearMinimizer)
    (hFl : EventuallyFloorConditions) : FrameFieldNearMinimizer := by
  intro T hT
  obtain ⟨yf, hF⟩ := hFl T hT ((T.side : ℝ) + 2 ^ 17) 1 (by positivity) one_pos
  refine ⟨max yf T.floorMin, fun y hy R hR n _ hn s hs c hst hmk x i hx hx' => ?_⟩
  simp only [max_le_iff] at hy
  obtain ⟨hyf, hyT⟩ := hy
  have hxR : y ≤ R.coupling := hR.le_coupling
  have hfit : R.params.Admissible := by
    rw [hR.params_eq]
    exact hT.fits y hyT
  have hLe : R.params.side = T.side := by rw [hR.params_eq]; rfl
  have hFx := hF R.coupling (hyf.trans hxR)
  have hr1 : ((T.side : ℝ) + 2 ^ 17) ≤ (R.range : ℝ) := hFx.range_ge
  have hr2 : T.side + 2 ^ 17 ≤ R.range := by exact_mod_cast hr1
  have hodd : Odd R.params.side := hfit.L_odd
  have hn₀ := hfit.n₀_ge
  have hn₀e : R.params.n₀ = T.n₀ := by rw [hR.params_eq]; rfl
  have hn2 : 2 ≤ n := by omega
  have hrg : RangesAdmissible R.range (clusterRange R.nextCoupling) := by
    refine ⟨hR.isStep.2.2, ?_, ?_⟩
    · have := hR.isStep.2.2
      have h3 : R.range ≤ clusterRange R.nextCoupling + 1 := this
      omega
    · have : (2 : ℕ) ^ 17 / 2 ^ 11 ≤ R.range / 2 ^ 11 := Nat.div_le_div_right (by omega)
      norm_num at this
      omega
  have hrL : R.params.side + 1 < 4 * R.range := by
    rw [hLe]
    omega
  have hbd := fun {b} (hb : b ∈ s.free) =>
    norm_frame_sub_minimizerCoord_le hFr hT hR hfit hn hrg hrL s hs hb
  have : NeZero (n * (torusFrame R.params.side R.depth n).blockSide) :=
    inferInstanceAs (NeZero (n * R.params.side))
  have : NeZero (n * (stepBlockFrame R.params.side n).blockSide) :=
    inferInstanceAs (NeZero (n * R.params.side))
  have hsd : ∀ k, (torusFrame R.params.side R.depth n).extent k = n := fun _ => rfl
  have hsd' : ∀ k, (stepBlockFrame R.params.side n).extent k = n := fun _ => rfl
  set w := minimizingCoordinates R.params.coupling (cellsOfSites (torusFrame R.params.side R.depth n) s.region)
    (readAtLevel (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top s.coarse)
    R.anchorRadius with hw
  have hleast : minimizingField R.params.coupling R.anchorRadius R.params.side R.depth s.region s.coarse x i =
      torusChart R.params.side (fun b => w (torusSiteInFrame (torusFrame R.params.side R.depth n)
        (torusFrame R.params.side R.depth n).depth b.1) b.2) s.coarse x i :=
    chartedField_readAtLevel (F := torusFrame R.params.side R.depth n) hsd hodd hn2 w s.coarse x i
  have hcr : IsCrossingBond (F := stepBlockFrame R.params.side n)
      (torusSiteInFrame (stepBlockFrame R.params.side n) 0 x, i) ↔ IsBlockEndBond R.params.side x i :=
    isCrossingBond_torusSiteInFrame_iff (F := stepBlockFrame R.params.side n) hsd' hodd hn2 x i
  have htr : IsAxialTreeBond (F := stepBlockFrame R.params.side n)
      (torusSiteInFrame (stepBlockFrame R.params.side n) 0 x, i) ↔ IsBlockTreeBond R.params.side x i :=
    isAxialTreeBond_torusSiteInFrame_iff (F := stepBlockFrame R.params.side n) hsd' hodd hn2 x i
  have hbound0 : 0 ≤ 2 * T.N 0 * T.threshold * Real.exp (-(T.δ₁ * (R.frameReach : ℝ))) := by
    obtain ⟨-, -, -, -, -, -, -, hNp, -⟩ := hT.chain
    have := hNp 0
    have := hT.σ_pos
    positivity
  have h1 := gaugeAt_fine_eq_one_of_not_mem_stored s c hodd hn2 hmk hx
  have h2 := gaugeAt_fine_eq_one_of_not_mem_stored s c hodd hn2 hmk hx'
  rw [hleast]
  unfold torusChart
  by_cases htree : IsAxialTreeBond (F := stepBlockFrame R.params.side n)
      (torusSiteInFrame (stepBlockFrame R.params.side n) 0 x, i)
  · have hnc : ¬ IsBlockEndBond R.params.side x i := fun h => htree.1 (hcr.mpr h)
    have hnf : (x, i) ∉ s.free := fun h => by
      have := hs.subset_chart h
      simp only [chartBonds, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this htree
    have e1 : s.field 0 x i = s.fine x i := dif_neg hnf
    have e2 : s.fine x i = 1 := hmk.fine_on_trees (x, i) hx htree
    rw [if_neg hnc, if_pos (htr.mp htree), e1, e2]
    simpa using hbound0
  · have hfree : (x, i) ∈ s.free := by
      rw [hst.free_eq]
      refine Finset.mem_filter.mpr ⟨?_, ?_, ?_⟩
      · simp only [chartBonds, Finset.mem_filter, Finset.mem_univ, true_and]
        exact htree
      · intro hC
        exact hx (Finset.mem_union_left _ hC)
      · intro hboth
        exact hx hboth.1
    have hfb := hbd hfree
    have hlz : (0 : FreeCoords s.free) ⟨(x, i), hfree⟩ = 0 := rfl
    have hlie : toImaginary (0 : EuclideanSpace ℝ (Fin 3)) = 0 := by
      apply Subtype.ext
      ext <;> simp [toImaginary]
    have e1 : s.field 0 x i = chartLink s x i (s.frame (x, i)) := by
      have : s.field 0 x i =
          chartLink s x i (s.frame (x, i) + toImaginary ((0 : FreeCoords s.free) ⟨(x, i), hfree⟩)) :=
        dif_pos hfree
      rw [this, hlz, hlie, add_zero]
    rw [e1]
    unfold chartLink
    rw [h1, h2, inv_one, one_mul, mul_one]
    set f := s.frame (x, i) with hf
    have hwf : ‖(f : ℍ[ℝ]) - (w (torusSiteInFrame (torusFrame R.params.side R.depth n)
        (torusFrame R.params.side R.depth n).depth x) i : ℍ[ℝ])‖ ≤
        2 * T.N 0 * T.threshold * Real.exp (-(T.δ₁ * (R.frameReach : ℝ))) := hfb
    have hlip := norm_expUnit_sub_le f (w (torusSiteInFrame (torusFrame R.params.side R.depth n)
      (torusFrame R.params.side R.depth n).depth x) i)
    by_cases hc : IsBlockEndBond R.params.side x i
    · rw [if_pos (hcr.mpr hc), if_pos hc]
      refine (TorusFrame.norm_mul_sub_mul_le _ _ _ _).trans ?_
      simp only [sub_self, norm_zero, add_zero]
      exact hlip.trans hwf
    · rw [if_neg (fun h => hc (hcr.mp h)), if_neg hc, if_neg (fun h => htree (htr.mpr h))]
      exact hlip.trans hwf
end YangMills.Construction.ClusterExpansionOfAStep
end
