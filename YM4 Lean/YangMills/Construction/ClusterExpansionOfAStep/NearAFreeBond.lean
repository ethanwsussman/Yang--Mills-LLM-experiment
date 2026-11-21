import YangMills.Construction.ClusterExpansionOfAStep.AllowedStatesReadTheirBoxProof
import YangMills.Construction.ClusterExpansionOfAStep.GoodBondsMakeAColdPlaquette
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.FreeBondNeighborhood
open BlockAverages LumpContours HoleSites GaugeFixing ColdStepAtMirrorFrames BlockTrees BlockZones TorusFields
  TorusLumps StepSettings StepCosts StepMarks StepGas RenormalizationStepParameters StepFrames ColdChain
def NonzeroMarksOffFree {R : StepSetup} {n : ℕ} [NeZero n] (G : GasGround R n) (γ : GasFamily R n)
    (η : FreeCoords (G.settingOf γ).free) : Prop :=
  ∀ b ∈ chartBonds R.params.side n, b ∉ (G.settingOf γ).free → b ∉ (G.settingOf γ).bad →
    bondMark R G.coarse ((G.settingOf γ).field η) b ≠ 0
variable {R : StepSetup} {n : ℕ} [NeZero n]
structure StepHypotheses (R : StepSetup) (δ lam σA cg : ℝ) (N : ℕ → ℝ) (G : GasGround R n) (γ : GasFamily R n)
    (Z S : Finset (TorusSite n)) (s₀ : ℝ) : Prop where
  admissible : R.params.Admissible
  hasExpansions : R.HasExpansions
  chainConstants : ColdChainConstants R.params.coupling δ R.params.side lam R.anchorRadius σA cg N
  two_threshold_le : 2 * R.params.threshold ≤ σA
  rangesAdmissible : RangesAdmissible R.range R.nextRange
  situation : IsStepSituation R.params R.nextRange G.coarse S G.cut s₀
  decay_gap : N 0 * s₀ * Real.exp (-(δ * ((R.range / 2 ^ 11 : ℕ) : ℝ))) ≤ R.params.threshold / 128
  side_le_range : 64 * R.params.side ≤ R.range
  size_bound : 16 * (R.params.side : ℝ) * (N 0 * s₀ + R.ballRadius) ≤ 1
  s₀_pos : 0 < s₀
  two_le : 2 ≤ n
  admissibleGround : G.IsAdmissibleGround
  markedZone : IsRetainedZone G Z
  gasFamily : G.IsGasFamily γ
variable {δ lam σA cg : ℝ} {N : ℕ → ℝ} {G : GasGround R n} {γ : GasFamily R n} {Z S : Finset (TorusSite n)}
  {s₀ : ℝ}
theorem free_subset_chartBonds : (G.settingOf γ).free ⊆ chartBonds R.params.side n := by apply _root_.YangMills.Construction.InBoxTransfer.free_subset_chartBonds <;> assumption
theorem fine_eq_field_zero (hL : Odd R.params.side) (hn : 2 ≤ n) :
    (G.settingOf γ).fine = (G.settingOf γ).field 0 := by apply _root_.YangMills.Construction.InBoxTransfer.fine_eq_field_zero <;> assumption
theorem supDist_le_of_parentBlock_eq {L : ℕ} [NeZero L] {x z : TorusSite (n * L)}
    (h : parentBlock L x = parentBlock L z) : _root_.YangMills.Construction.TorusFields.supDist x z ≤ L := by apply _root_.YangMills.Construction.TorusLumps.supDist_le_of_parentBlock_eq <;> assumption
theorem supDist_le_two_of_mem_plaquetteVertices {m : ℕ} [NeZero m] {x z : TorusSite m} {μ ν : Fin 4}
    (hz : z ∈ plaquetteVertices x μ ν) : _root_.YangMills.Construction.TorusFields.supDist x z ≤ 2 := by apply _root_.YangMills.Construction.InBoxTransfer.supDist_le_two_of_mem_plaquetteVertices <;> assumption
theorem deviation_lt_of_bondMark_ne_zero {V : TorusField n} {W : TorusField (n * R.params.side)}
    {b : TorusBond (n * R.params.side)} (h : bondMark R V W b ≠ 0) :
    ‖((chartCoord R.params V W b : imaginaryQuaternions) : ℍ[ℝ]) -
      ((frameCoord R.params R.anchorRadius R.depth R.frameReach V b : imaginaryQuaternions) : ℍ[ℝ])‖ <
        R.ballRadius := by
  by_contra hn
  apply h
  unfold StepSettings.bondMark cutoffFactor
  rw [if_neg hn]
theorem hotLumps_congr {F : BlockFrame} {L : ℕ} (g : LumpGrid L) (s : ℝ) {j : ℕ} (X : Finset (F.Site j))
    (W W' : F.GaugeField j) (h : ∀ p ∈ cutPlaquettes X, (s ≤ plaquetteDefect W p ↔ s ≤ plaquetteDefect W' p)) :
    hotLumps g s X W = hotLumps g s X W' := by
  classical
  unfold hotLumps
  rw [Finset.filter_congr h]
theorem lt_of_mem_cutPlaquettes {F : BlockFrame} {j : ℕ} {X : Finset (F.Site j)} {p : F.Site j × Fin 4 × Fin 4}
    (hp : p ∈ cutPlaquettes X) : p.2.1 < p.2.2 := by apply _root_.YangMills.Construction.InBoxTransfer.lt_of_mem_cutPlaquettes <;> assumption
theorem eq_of_mem_plaquetteCorners {F : BlockFrame} {j : ℕ} {p : F.Site j × Fin 4 × Fin 4} {x : F.Site j}
    (h : x ∈ plaquetteCorners p) :
    x = p.1 ∨ x = p.1 + BlockAverages.unitStep j p.2.1 ∨ x = p.1 + BlockAverages.unitStep j p.2.2 ∨
      x = p.1 + BlockAverages.unitStep j p.2.1 + BlockAverages.unitStep j p.2.2 := by
  simpa [plaquetteCorners] using h
theorem enclosingCell_mem_of_subset_cutBelow {F : BlockFrame} (hodd : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i)
    {X : Finset F.Cell} {l : Finset (F.Site F.depth)} (h : l ⊆ cutBelow F.depth X) {x : F.Site F.depth}
    (hx : x ∈ l) : enclosingCell x ∈ X :=
  (GaugeFixing.mem_cutBelow_depth hs hodd _ _).1 (h hx)
theorem mem_and_enclosingCell_mem_of_mem_nearbyLumps {F : BlockFrame} (hodd : Odd F.blockSide)
    (hs : ∀ i, 0 < F.extent i) {h : Finset (Finset (F.Site F.depth))} {y : F.Cell}
    {l : Finset (F.Site F.depth)} (hl : l ∈ nearbyLumps h y) :
    l ∈ h ∧ ∀ x ∈ l, enclosingCell x ∈ cellBall y 2 := by
  classical
  unfold nearbyLumps at hl
  rw [Finset.mem_filter] at hl
  exact ⟨hl.1, fun x hx => enclosingCell_mem_of_subset_cutBelow hodd hs hl.2 hx⟩
theorem exists_hot_plaquette_of_mem_hotLumps {F : BlockFrame} {L : ℕ} (g : LumpGrid L) (s : ℝ) {j : ℕ}
    (X : Finset (F.Site j)) (W : F.GaugeField j) {l : Finset (F.Site j)} (hl : l ∈ hotLumps g s X W) :
    ∃ p ∈ cutPlaquettes X, s ≤ plaquetteDefect W p ∧ ∃ x ∈ plaquetteCorners p, l = lumpOf g x := by
  classical
  unfold hotLumps at hl
  obtain ⟨p, hp, hlp⟩ := Finset.mem_biUnion.mp hl
  obtain ⟨hpc, hhot⟩ := Finset.mem_filter.mp hp
  obtain ⟨x, hx, hlx⟩ := Finset.mem_image.mp hlp
  exact ⟨p, hpc, hhot, x, hx, hlx.symm⟩
theorem exists_hot_corner_of_mem_nearbyLumps {F : BlockFrame} {L : ℕ} (g : LumpGrid L) (hL : Odd L)
    (hodd : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) (s : ℝ) (X : Finset (F.Site F.depth))
    (W : F.GaugeField F.depth) (y : F.Cell) (l : Finset (F.Site F.depth))
    (hl : l ∈ nearbyLumps (hotLumps g s X W) y) :
    ∃ p ∈ cutPlaquettes X, s ≤ plaquetteDefect W p ∧ ∃ x ∈ plaquetteCorners p, enclosingCell x ∈ cellBall y 2 := by
  obtain ⟨h1, h2⟩ := mem_and_enclosingCell_mem_of_mem_nearbyLumps hodd hs hl
  obtain ⟨p, hp, hh, x, hx, rfl⟩ := exists_hot_plaquette_of_mem_hotLumps g s X W h1
  exact ⟨p, hp, hh, x, hx, h2 x (mem_lumpOf hL.pos hL g x)⟩
section Frames
variable {L : ℕ} [NeZero L]
theorem torusSiteInFrame_one_add (x y : TorusSite n) :
    torusSiteInFrame (stepBlockFrame L n) 1 (x + y) =
      torusSiteInFrame (stepBlockFrame L n) 1 x + torusSiteInFrame (stepBlockFrame L n) 1 y := by apply _root_.YangMills.Construction.InBoxTransfer.torusSiteInFrame_one_add <;> assumption
theorem torusSiteInFrame_one_unitStep (i : Fin 4) :
    torusSiteInFrame (stepBlockFrame L n) 1 (TorusFields.unitStep n i) =
      BlockAverages.unitStep (F := stepBlockFrame L n) 1 i := by
  funext k
  have e : (TorusFields.unitStep n i) k = (((Pi.single i 1 : Fin 4 → ℤ) k : ℤ) : ZMod n) := by
    by_cases hk : k = i
    · subst hk
      simp [TorusFields.unitStep]
    · simp [TorusFields.unitStep, Pi.single_eq_of_ne hk]
  show ((ZMod.cast (TorusFields.unitStep n i k) : ℤ) : ZMod ((stepBlockFrame L n).period 1 k)) = _
  rw [e]
  exact intCast_cast_intCast (stepBlockFrame_period_one k) _
theorem torusSiteInFrame_one_add_siteOfCoords (x : TorusSite n) (h : Fin 4 → ℤ) :
    torusSiteInFrame (stepBlockFrame L n) 1 x + siteOfCoords 1 h =
      torusSiteInFrame (stepBlockFrame L n) 1 (x + siteOfInt h) := by apply _root_.YangMills.Construction.InBoxTransfer.torusSiteInFrame_one_add_siteOfInt <;> assumption
theorem plaquetteDefect_readAtLevel_zero (W : TorusField (n * L)) (x : TorusSite (n * L)) (μ ν : Fin 4) :
    plaquetteDefect (readAtLevel (stepBlockFrame L n) 0 W) (torusSiteInFrame (stepBlockFrame L n) 0 x, μ, ν) =
      curvature W x μ ν := by apply _root_.YangMills.Construction.InBoxTransfer.plaquetteDefect_readAtLevel <;> assumption
theorem mem_plaquetteVertices_of_mem_plaquetteCorners {x₁ p₁ : TorusSite (n * L)} {μ ν : Fin 4}
    (hx : torusSiteInFrame (stepBlockFrame L n) 0 x₁ ∈
      plaquetteCorners (F := stepBlockFrame L n) (torusSiteInFrame (stepBlockFrame L n) 0 p₁, μ, ν)) :
    x₁ ∈ plaquetteVertices p₁ μ ν := by
  have e1 : torusSiteInFrame (stepBlockFrame L n) 0 p₁ + BlockAverages.unitStep 0 μ =
      torusSiteInFrame (stepBlockFrame L n) 0 (p₁ + TorusFields.unitStep (n * L) μ) := by
    rw [torusSiteInFrame_add, torusSiteInFrame_unitStep]
  have e2 : torusSiteInFrame (stepBlockFrame L n) 0 p₁ + BlockAverages.unitStep 0 ν =
      torusSiteInFrame (stepBlockFrame L n) 0 (p₁ + TorusFields.unitStep (n * L) ν) := by
    rw [torusSiteInFrame_add, torusSiteInFrame_unitStep]
  have e3 : torusSiteInFrame (stepBlockFrame L n) 0 p₁ + BlockAverages.unitStep 0 μ + BlockAverages.unitStep 0 ν =
      torusSiteInFrame (stepBlockFrame L n) 0 (p₁ + TorusFields.unitStep (n * L) μ + TorusFields.unitStep (n * L) ν) := by
    rw [torusSiteInFrame_add, torusSiteInFrame_add, torusSiteInFrame_unitStep, torusSiteInFrame_unitStep]
  have hi := torusSiteInFrame_injective (m := n * L) (stepBlockFrame L n) 0 stepBlockFrame_period_zero
  simp only [plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false]
  rcases eq_of_mem_plaquetteCorners hx with h1 | h1 | h1 | h1
  · exact Or.inl (hi h1)
  · exact Or.inr (Or.inl (hi (h1.trans e1)))
  · exact Or.inr (Or.inr (Or.inl (hi (h1.trans e2))))
  · exact Or.inr (Or.inr (Or.inr (hi (h1.trans e3))))
theorem supDist_le_of_parentBlock (x z : TorusSite (n * L)) :
    _root_.YangMills.Construction.TorusFields.supDist x z ≤ L * (_root_.YangMills.Construction.TorusFields.supDist (parentBlock L x) (parentBlock L z) + 2) := by apply _root_.YangMills.Construction.InBoxTransfer.supDist_le_parentBlock <;> assumption
end Frames
section Requirements
variable (hS : StepHypotheses R δ lam σA cg N G γ Z S s₀) {η : FreeCoords (G.settingOf γ).free}
include hS
theorem side_odd : Odd R.params.side := hS.admissible.L_odd
theorem ballRadius_pos : 0 < R.ballRadius := by
  have := hS.admissible.σ_pos
  unfold StepSetup.ballRadius
  positivity
theorem one_le_side : 1 ≤ R.params.side := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
theorem anchorRadius_le_one_and_pos : R.anchorRadius ≤ 1 ∧ 0 < R.anchorRadius := by
  obtain ⟨_, _, _, h1, h2, _⟩ := hS.chainConstants
  exact ⟨h2, h1⟩
theorem ballRadius_le_one : R.ballRadius ≤ 1 := by
  have h := hS.size_bound
  have h1 : (1 : ℝ) ≤ R.params.side := by exact_mod_cast one_le_side hS
  have h2 : 0 < N 0 := by
    obtain ⟨_, _, _, _, _, _, _, h3, _⟩ := hS.chainConstants
    exact h3 0
  have h3 := hS.s₀_pos
  have h4 : 0 ≤ N 0 * s₀ := by positivity
  nlinarith
theorem norm_frameCoord_le (b : TorusBond (n * R.params.side)) :
    ‖((frameCoord R.params R.anchorRadius R.depth R.frameReach G.coarse b : imaginaryQuaternions) : ℍ[ℝ])‖ ≤
      R.anchorRadius := by
  unfold frameCoord bondFrameCoord reflectedBondCoord
  have hρ := (anchorRadius_le_one_and_pos hS).2.le
  have key : ∀ {F : BlockFrame} (a : ℝ) (Q : Finset F.Cell) (V : F.GaugeField F.top)
      (c : F.Site F.depth × Fin 4),
      ‖(minimizingBondCoordinate a R.anchorRadius Q c V : ℍ[ℝ])‖ ≤ R.anchorRadius := by
    intro F a Q V c
    classical
    unfold minimizingBondCoordinate minimizingCoordinates
    split_ifs with h
    · have hs := h.choose_spec
      by_cases hb : c ∈ chordBonds Q
      · exact hs.2.1 c hb
      · rw [hs.1 c hb]
        simpa using hρ
    · simpa using hρ
  split_ifs
  · exact key _ _ _ _
  · exact key _ _ _ _
theorem chartCoord_field_eq_of_not_mem_free (η' η'' : FreeCoords (G.settingOf γ).free)
    {b : TorusBond (n * R.params.side)} (hb : b ∉ (G.settingOf γ).free) :
    chartCoord R.params G.coarse ((G.settingOf γ).field η') b =
      chartCoord R.params G.coarse ((G.settingOf γ).field η'') b := by
  have h1 := chartCoord_field_of_not_mem_free (s := G.settingOf γ) free_subset_chartBonds (side_odd hS)
    hS.two_le η' hb
  have h2 := chartCoord_field_of_not_mem_free (s := G.settingOf γ) free_subset_chartBonds (side_odd hS)
    hS.two_le η'' hb
  exact h1.trans h2.symm
theorem deviation_lt_of_not_mem_free (hw : NonzeroMarksOffFree G γ η) (η' : FreeCoords (G.settingOf γ).free)
    {b : TorusBond (n * R.params.side)} (hc : b ∈ chartBonds R.params.side n) (hb : b ∉ (G.settingOf γ).free)
    (hbad : b ∉ (G.settingOf γ).bad) :
    ‖((chartCoord R.params G.coarse ((G.settingOf γ).field η') b : imaginaryQuaternions) : ℍ[ℝ]) -
      ((frameCoord R.params R.anchorRadius R.depth R.frameReach G.coarse b : imaginaryQuaternions) : ℍ[ℝ])‖ <
        R.ballRadius := by
  rw [chartCoord_field_eq_of_not_mem_free hS η' η hb]
  exact deviation_lt_of_bondMark_ne_zero (hw b hc hb hbad)
theorem deviation_le_of_mem_free (η' : FreeCoords (G.settingOf γ).free) (hη' : (G.settingOf γ).InBalls η')
    (b : (G.settingOf γ).free) :
    ‖((chartCoord R.params G.coarse ((G.settingOf γ).field η') b.1 : imaginaryQuaternions) : ℍ[ℝ]) -
      ((frameCoord R.params R.anchorRadius R.depth R.frameReach G.coarse b.1 : imaginaryQuaternions) : ℍ[ℝ])‖ ≤
        R.ballRadius := by
  have hb := hη' b
  have hfr := norm_frameCoord_le hS b.1
  have hn : ‖((((G.settingOf γ).frame b.1 + toImaginary (η' b) : imaginaryQuaternions)) : ℍ[ℝ])‖ <
      Real.pi := by
    have h1 : ‖((((G.settingOf γ).frame b.1 + toImaginary (η' b) : imaginaryQuaternions)) : ℍ[ℝ])‖ ≤
        ‖(((G.settingOf γ).frame b.1 : imaginaryQuaternions) : ℍ[ℝ])‖ +
          ‖((toImaginary (η' b) : imaginaryQuaternions) : ℍ[ℝ])‖ := norm_add_le _ _
    have h2 := ballRadius_le_one hS
    have h3 := (anchorRadius_le_one_and_pos hS).1
    have h4 : ‖(((G.settingOf γ).frame b.1 : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ R.anchorRadius := hfr
    have h5 : ‖((toImaginary (η' b) : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ R.ballRadius := hb
    have := Real.pi_gt_three
    linarith
  have hc := chartCoord_field_of_mem_free (s := G.settingOf γ) free_subset_chartBonds (side_odd hS) hS.two_le
    η' b hn
  have hc' : chartCoord R.params G.coarse ((G.settingOf γ).field η') b.1 =
      (G.settingOf γ).frame b.1 + toImaginary (η' b) := hc
  rw [hc']
  have e : ((((G.settingOf γ).frame b.1 + toImaginary (η' b) : imaginaryQuaternions)) : ℍ[ℝ]) -
      ((frameCoord R.params R.anchorRadius R.depth R.frameReach G.coarse b.1 : imaginaryQuaternions) : ℍ[ℝ]) =
        ((toImaginary (η' b) : imaginaryQuaternions) : ℍ[ℝ]) := by
    show (((G.settingOf γ).frame b.1 : imaginaryQuaternions) : ℍ[ℝ]) +
      ((toImaginary (η' b) : imaginaryQuaternions) : ℍ[ℝ]) -
        (((G.settingOf γ).frame b.1 : imaginaryQuaternions) : ℍ[ℝ]) = _
    abel
  rw [e]
  exact hb
theorem deviation_le_of_near_free (hw : NonzeroMarksOffFree G γ η) (η' : FreeCoords (G.settingOf γ).free)
    (hη' : (G.settingOf γ).InBalls η') {b b' : TorusBond (n * R.params.side)} (hb : b ∈ (G.settingOf γ).free)
    (hc : b' ∈ chartBonds R.params.side n) (hd : _root_.YangMills.Construction.TorusFields.supDist b.1 b'.1 + R.params.side + 1 < 4 * R.range) :
    ‖((chartCoord R.params G.coarse ((G.settingOf γ).field η') b' : imaginaryQuaternions) : ℍ[ℝ]) -
      ((frameCoord R.params R.anchorRadius R.depth R.frameReach G.coarse b' : imaginaryQuaternions) : ℍ[ℝ])‖ ≤
        R.ballRadius := by
  by_cases hf : b' ∈ (G.settingOf γ).free
  · exact deviation_le_of_mem_free hS η' hη' ⟨b', hf⟩
  · have hbad : b' ∉ (G.settingOf γ).bad := fun h => by
      have := far_of_mem_bad hS.markedZone hb h
      omega
    exact (deviation_lt_of_not_mem_free hS hw η' hc hf hbad).le
theorem curvature_lt_of_near_free (hGood : coldPlaquette_of_small_frameDeviation) (hw : NonzeroMarksOffFree G γ η)
    (η' : FreeCoords (G.settingOf γ).free) (hη' : (G.settingOf γ).InBalls η') {b : TorusBond (n * R.params.side)}
    (hb : b ∈ (G.settingOf γ).free) (x : TorusSite (n * R.params.side)) (μ ν : Fin 4) (hμ : μ < ν)
    (hd : _root_.YangMills.Construction.TorusFields.supDist x b.1 ≤ 3 * R.range) :
    curvature ((G.settingOf γ).field η') x μ ν < R.params.threshold / 4 := by
  have hfar := hS.side_le_range
  have hL1 := one_le_side hS
  refine hGood R.params δ lam R.anchorRadius σA cg N hS.admissible hS.chainConstants hS.two_threshold_le R.depth
    R.range R.nextRange n G.coarse S G.cut s₀ hS.rangesAdmissible hS.situation hS.decay_gap _ x μ ν hμ ?_ ?_
  · intro z hz hzC
    have h1 := far_of_parentBlock_mem_cut hS.markedZone hb hzC
    have h2 := supDist_le_two_of_mem_plaquetteVertices hz
    have h3 := supDist_triangle b.1 x z
    rw [supDist_comm b.1 x] at h3
    omega
  · rintro b' hc ⟨z, hz, hbz⟩
    have h1 := _root_.YangMills.Construction.FreeBondNeighborhood.supDist_le_of_parentBlock_eq hbz
    have h2 := supDist_le_two_of_mem_plaquetteVertices hz
    have h3 := supDist_triangle b.1 x z
    rw [supDist_comm b.1 x] at h3
    have h4 := _root_.YangMills.Construction.TorusFields.supDist_triangle b.1 z b'.1
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm z b'.1] at h4
    have h5 := deviation_le_of_near_free hS hw η' hη' hb hc (by omega)
    have e : ((frameDeviation R.params R.anchorRadius R.depth (R.range / 2 ^ 11) G.coarse
        ((G.settingOf γ).field η') b' : imaginaryQuaternions) : ℍ[ℝ]) =
        ((chartCoord R.params G.coarse ((G.settingOf γ).field η') b' : imaginaryQuaternions) : ℍ[ℝ]) -
          ((frameCoord R.params R.anchorRadius R.depth R.frameReach G.coarse b' : imaginaryQuaternions) :
            ℍ[ℝ]) := rfl
    rw [e]
    exact h5
theorem inBalls_zero : (G.settingOf γ).InBalls 0 := fun b => by
  have := ballRadius_pos hS
  simpa [coordNorm, norm_toImaginary, Pi.zero_apply] using this.le
theorem threshold_le_curvature_iff (hGood : coldPlaquette_of_small_frameDeviation) (hw : NonzeroMarksOffFree G γ η)
    (η' η'' : FreeCoords (G.settingOf γ).free) (h' : (G.settingOf γ).InBalls η')
    (h'' : (G.settingOf γ).InBalls η'') (x : TorusSite (n * R.params.side)) (μ ν : Fin 4) (hμ : μ < ν) :
    R.params.threshold ≤ curvature ((G.settingOf γ).field η') x μ ν ↔
      R.params.threshold ≤ curvature ((G.settingOf γ).field η'') x μ ν := by
  classical
  have hσ := hS.admissible.σ_pos
  have hfar := hS.side_le_range
  have hL1 := one_le_side hS
  by_cases hf : ∃ b ∈ (G.settingOf γ).free, _root_.YangMills.Construction.TorusFields.supDist x b.1 ≤ 2
  · obtain ⟨b, hb, hd⟩ := hf
    have h1 := curvature_lt_of_near_free hS hGood hw η' h' hb x μ ν hμ (by omega)
    have h2 := curvature_lt_of_near_free hS hGood hw η'' h'' hb x μ ν hμ (by omega)
    constructor <;> intro h <;> linarith
  · rw [not_exists] at hf
    have hoff : ∀ (z : TorusSite (n * R.params.side)) (i : Fin 4), _root_.YangMills.Construction.TorusFields.supDist x z ≤ 2 →
        (z, i) ∉ (G.settingOf γ).free := by
      intro z i hz hmem
      exact hf (z, i) ⟨hmem, hz⟩
    have hval : ∀ (z : TorusSite (n * R.params.side)) (i : Fin 4), _root_.YangMills.Construction.TorusFields.supDist x z ≤ 2 →
        (G.settingOf γ).field η' z i = (G.settingOf γ).field η'' z i := by
      intro z i hz
      have a := field_of_not_mem_free (s := G.settingOf γ) (η := η') (b := (z, i)) (hoff z i hz)
      have b := field_of_not_mem_free (s := G.settingOf γ) (η := η'') (b := (z, i)) (hoff z i hz)
      exact a.trans b.symm
    have e1 := _root_.YangMills.Construction.TorusFields.supDist_add_unitStep_le (n := n * R.params.side) x μ
    have e2 := _root_.YangMills.Construction.TorusFields.supDist_add_unitStep_le (n := n * R.params.side) x ν
    have e : curvature ((G.settingOf γ).field η') x μ ν = curvature ((G.settingOf γ).field η'') x μ ν := by
      unfold curvature holonomy
      rw [hval x μ (by rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega), hval x ν (by rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega),
        hval (x + TorusFields.unitStep (n * R.params.side) μ) ν (by omega),
        hval (x + TorusFields.unitStep (n * R.params.side) ν) μ (by omega)]
    rw [e]
theorem side_dvd : R.params.side ∣ n * R.params.side := Dvd.intro_left n rfl
theorem torusHotLumps_field_eq (hGood : coldPlaquette_of_small_frameDeviation) (hw : NonzeroMarksOffFree G γ η)
    (η' η'' : FreeCoords (G.settingOf γ).free) (h' : (G.settingOf γ).InBalls η')
    (h'' : (G.settingOf γ).InBalls η'') :
    torusHotLumps R.params ((G.settingOf γ).field η') = torusHotLumps R.params ((G.settingOf γ).field η'') := by
  ext l
  rw [mem_torusHotLumps_iff R.params hS.admissible (side_dvd hS),
    mem_torusHotLumps_iff R.params hS.admissible (side_dvd hS)]
  constructor
  · rintro ⟨x, μ, ν, hμ, h, hl⟩
    exact ⟨x, μ, ν, hμ, (threshold_le_curvature_iff hS hGood hw η' η'' h' h'' x μ ν hμ).mp h, hl⟩
  · rintro ⟨x, μ, ν, hμ, h, hl⟩
    exact ⟨x, μ, ν, hμ, (threshold_le_curvature_iff hS hGood hw η' η'' h' h'' x μ ν hμ).mpr h, hl⟩
theorem stepHotLumps_field_eq (hGood : coldPlaquette_of_small_frameDeviation) (hw : NonzeroMarksOffFree G γ η)
    (η' η'' : FreeCoords (G.settingOf γ).free) (h' : (G.settingOf γ).InBalls η')
    (h'' : (G.settingOf γ).InBalls η'') :
    stepHotLumps R.params ((G.settingOf γ).field η') = stepHotLumps R.params ((G.settingOf γ).field η'') := by
  refine hotLumps_congr _ _ _ _ _ fun p hp => ?_
  obtain ⟨x, μ, ν⟩ := p
  obtain ⟨x₀, rfl⟩ := torusSiteInFrame_surjective (stepBlockFrame R.params.side n) 0 stepBlockFrame_period_zero x
  rw [plaquetteDefect_readAtLevel_zero, plaquetteDefect_readAtLevel_zero]
  exact threshold_le_curvature_iff hS hGood hw η' η'' h' h'' x₀ μ ν (lt_of_mem_cutPlaquettes hp)
end Requirements
theorem exists_stepHypotheses_of_admissible (T : ParameterAssignment) (hT : T.Admissible) :
    ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y →
      ∀ (n : ℕ) [NeZero n] (G : GasGround R n), G.IsAdmissibleGround → ∀ γ : GasFamily R n, G.IsGasFamily γ →
        ∃ (Z S : Finset (TorusSite n)) (s₀ : ℝ), StepHypotheses R T.δ₁ T.lam T.σA T.cg T.N G γ Z S s₀ ∧
          IsBlockTorusSide R.params (n * R.params.side) := by
  classical
  obtain ⟨hδ, _⟩ := hT.chain
  have hNpos : 0 < T.N 0 := by
    obtain ⟨_, _, _, _, _, _, _, h3, _⟩ := hT.chain
    exact h3 0
  have hδ₁ := hδ
  set m₁ : ℕ := ⌈Real.log (256 * T.N 0 + 1) / T.δ₁⌉₊ with hm₁
  set A : ℕ := max (2 ^ 16 + 1) (max (2 ^ 11 * (max 16 m₁ + 1)) (64 * T.side)) with hA
  refine ⟨max T.floorMin ((A : ℝ) ^ 100 + 1), fun y hy R hOn n _ G hG γ hγ => ?_⟩
  have hy1 : T.floorMin ≤ y := le_trans (le_max_left _ _) hy
  have hy2 : (A : ℝ) ^ 100 ≤ y := by
    have := le_trans (le_max_right _ _) hy
    linarith
  have hfit : R.params.Admissible := by
    rw [hOn.params_eq]
    exact hT.fits y hy1
  have eσ : R.params.threshold = T.threshold := by rw [hOn.params_eq]; rfl
  have eL : R.params.side = T.side := by rw [hOn.params_eq]; rfl
  have ea : R.params.coupling = T.coupling := by rw [hOn.params_eq]; rfl
  have en : R.params.n₀ = T.n₀ := by rw [hOn.params_eq]; rfl
  have hσ : 0 < T.threshold := hT.σ_pos
  have hxA : (A : ℝ) ≤ R.coupling ^ ((1 : ℝ) / 100) := by
    have e : ((A : ℝ) ^ 100) ^ ((1 : ℝ) / 100) = A := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg A)]
      norm_num
    calc (A : ℝ) = ((A : ℝ) ^ 100) ^ ((1 : ℝ) / 100) := e.symm
      _ ≤ R.coupling ^ ((1 : ℝ) / 100) :=
        Real.rpow_le_rpow (by positivity) (hy2.trans hOn.le_coupling) (by norm_num)
  have hr : A ≤ R.range := by
    have h1 : (A : ℝ) ≤ (R.range : ℝ) := hxA.trans (Nat.le_ceil _)
    exact_mod_cast h1
  have hr1 : 2 ^ 16 + 1 ≤ R.range := le_trans (le_max_left _ _) hr
  have hr2 : 2 ^ 11 * (max 16 m₁ + 1) ≤ R.range := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hr
  have hr3 : 64 * T.side ≤ R.range := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hr
  have hstep := hOn.isStep
  have hm : max 16 m₁ ≤ R.range / 2 ^ 11 := by
    rw [Nat.le_div_iff_mul_le (by positivity)]
    nlinarith
  have hranges : RangesAdmissible R.range R.nextRange :=
    ⟨hstep.2.2, by have := hstep.2.2; omega, le_trans (le_max_left _ _) hm⟩
  have hchain : ColdChainConstants R.params.coupling T.δ₁ R.params.side T.lam R.anchorRadius T.σA T.cg T.N := by
    rw [ea, eL, hOn.anchorRadius_eq]
    exact hT.chain
  have hexp : Real.exp (-(T.δ₁ * ((R.range / 2 ^ 11 : ℕ) : ℝ))) ≤ 1 / (256 * T.N 0 + 1) := by
    have hm₂ : Real.log (256 * T.N 0 + 1) / T.δ₁ ≤ ((R.range / 2 ^ 11 : ℕ) : ℝ) := by
      refine (Nat.le_ceil _).trans ?_
      exact_mod_cast le_trans (le_max_right _ _) hm
    have hm₃ : Real.log (256 * T.N 0 + 1) ≤ T.δ₁ * ((R.range / 2 ^ 11 : ℕ) : ℝ) := by
      rw [div_le_iff₀ hδ₁] at hm₂
      linarith
    have hp : (0 : ℝ) < 256 * T.N 0 + 1 := by positivity
    rw [one_div, ← Real.exp_log (inv_pos.mpr hp), Real.log_inv]
    exact Real.exp_le_exp.mpr (by linarith)
  have build : ∀ (S : Finset (TorusSite n)) (s₀ : ℝ), IsStepSituation R.params R.nextRange G.coarse S G.cut s₀ →
      0 < s₀ → s₀ ≤ 2 * T.threshold → 2 ≤ n → T.n₀ ≤ n → ∃ (Z S' : Finset (TorusSite n)) (s₁ : ℝ),
        StepHypotheses R T.δ₁ T.lam T.σA T.cg T.N G γ Z S' s₁ ∧ IsBlockTorusSide R.params (n * R.params.side) := by
    intro S s₀ hsit hs₀ hs₂ hn₂ hn₀
    obtain ⟨Z, hZ⟩ := exists_isAdmissibleZone G hG
    have hgap : T.N 0 * s₀ * Real.exp (-(T.δ₁ * ((R.range / 2 ^ 11 : ℕ) : ℝ))) ≤ R.params.threshold / 128 := by
      rw [eσ]
      have hp : (0 : ℝ) < 256 * T.N 0 + 1 := by positivity
      calc T.N 0 * s₀ * Real.exp (-(T.δ₁ * ((R.range / 2 ^ 11 : ℕ) : ℝ)))
          ≤ T.N 0 * (2 * T.threshold) * (1 / (256 * T.N 0 + 1)) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left hs₂ hNpos.le) hexp (Real.exp_pos _).le (by positivity)
        _ ≤ T.threshold / 128 := by
            rw [mul_one_div, div_le_div_iff₀ hp (by norm_num)]
            nlinarith
    have hsize : 16 * (R.params.side : ℝ) * (T.N 0 * s₀ + R.ballRadius) ≤ 1 := by
      have h1 := hT.σ_L
      have hρe : R.ballRadius = T.threshold / 64 := by
        unfold StepSetup.ballRadius
        rw [eσ]
      rw [eL, hρe]
      have hLp : (0 : ℝ) < T.side := by exact_mod_cast hT.L_odd.pos
      have h2 : T.N 0 * s₀ + T.threshold / 64 ≤ 2 * (T.N 0 + 1) * T.threshold := by nlinarith
      have h3 : 16 * (T.side : ℝ) * (T.N 0 * s₀ + T.threshold / 64) ≤
          16 * (T.side : ℝ) * (2 * (T.N 0 + 1) * T.threshold) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      nlinarith
    have hS : StepHypotheses R T.δ₁ T.lam T.σA T.cg T.N G γ Z S s₀ :=
      { admissible := hfit, hasExpansions := hstep.1, chainConstants := hchain,
        two_threshold_le := by rw [eσ]; exact hT.σ_le, rangesAdmissible := hranges, situation := hsit,
        decay_gap := hgap, side_le_range := by rw [eL]; exact hr3, size_bound := hsize, s₀_pos := hs₀,
        two_le := hn₂, admissibleGround := hG, markedZone := hZ, gasFamily := hγ }
    have hside : IsBlockTorusSide R.params (n * R.params.side) := by
      refine ⟨Dvd.intro_left n rfl, ?_⟩
      rw [en, Nat.mul_comm n]
      exact Nat.mul_le_mul_left _ hn₀
    exact ⟨Z, S, s₀, hS, hside⟩
  have hn₀g : 4096 ≤ T.n₀ := hT.n₀_ge
  rcases hG with hc | hc
  · have hside := hc.n₀_le
    rw [en] at hside
    exact build Finset.univ (9 / 8 * R.params.threshold)
      (Or.inr ⟨by rw [en]; exact hside, hc.coarse_cold, rfl, hc.cut_eq, rfl⟩)
      (by rw [eσ]; positivity) (by rw [eσ]; linarith) (by omega) hside
  · have hside := hc.isBlockSide
    have h1 : T.n₀ ≤ n := by
      have h2 := hside.2
      rw [en] at h2
      exact le_trans (Nat.le_mul_of_pos_left _ (NeZero.pos _)) h2
    exact build G.region R.params.threshold (Or.inl ⟨hside, hc.region_eq, hc.cut_eq, rfl⟩)
      (by rw [eσ]; exact hσ) (by rw [eσ]; linarith) (by omega) h1
end YangMills.Construction.FreeBondNeighborhood
end
