import YangMills.Construction.ChessboardTori.DistanceToFacePlanesAndOpenCellsProof
import YangMills.Construction.ReflectionPositivity.ApproximationWithALimitOnEveryTupleIsBoundedProof
import YangMills.Construction.SixteenPointsOnASmallTorus.ArrayMeanIsTheMeanOfTheCopies
import YangMills.Construction.SixteenPointsOnASmallTorus.SixteenCopiesAtEveryDatum
import YangMills.Construction.SixteenPointsOnASmallTorus.SixteenCopiesOnTheLeastTorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SmallTorusCopies
open TorusLumps TorusFields RenormalizationStepParameters WeightedResponses TestFunctions
open ChessboardTori ReflectedCopies
private theorem lipConstR4_nonneg (f : InfiniteLattice.AmbientSpace → ℝ) : 0 ≤ TestFunctions.lipConstR4 f := by apply _root_.YangMills.Construction.ReflectionPositivity.ApproximatingSequences.BoundedOfLimits.lipConstR4_nonneg <;> assumption
private theorem abs_sub_le_lipConstR4_mul {f : InfiniteLattice.AmbientSpace → ℝ}
    (hf : TestFunctions.IsLipschitzFor TestFunctions.euclidDistR4 f) (x y : InfiniteLattice.AmbientSpace) :
    |f x - f y| ≤ TestFunctions.lipConstR4 f * TestFunctions.euclidDistR4 x y := by
  obtain ⟨C, hC0, hC⟩ := hf
  have hne : ({C : ℝ | 0 ≤ C ∧ ∀ x y, ‖f x - f y‖ ≤ C * TestFunctions.euclidDistR4 x y}).Nonempty :=
    ⟨C, hC0, hC⟩
  have hd : 0 ≤ TestFunctions.euclidDistR4 x y := Real.sqrt_nonneg _
  rcases hd.eq_or_lt with hzero | hpos
  · have hz := hC x y
    rw [← hzero, mul_zero] at hz
    rw [← hzero, mul_zero]
    simpa using hz
  · have hq : |f x - f y| / TestFunctions.euclidDistR4 x y ≤ TestFunctions.lipConstR4 f :=
      le_csInf hne fun C' hC' => (div_le_iff₀ hpos).2 (hC'.2 x y)
    exact (div_le_iff₀ hpos).1 hq
abbrev _root_.YangMills.DeltaSharedProofs.p2429 := @abs_sub_le_lipConstR4_mul
private theorem abs_le_uniformNorm_of_supported {f : InfiniteLattice.AmbientSpace → ℝ} {r : ℝ} (hr : 0 < r)
    (hf : TestFunctions.IsLipschitzFor TestFunctions.euclidDistR4 f)
    (hb : ∃ y : InfiniteLattice.AmbientSpace, ∀ x, f x ≠ 0 → x ∈ TestFunctions.closedBallR4 y r)
    (x : InfiniteLattice.AmbientSpace) : |f x| ≤ TestFunctions.uniformNorm f := by
  obtain ⟨y, hy⟩ := hb
  have hlip := lipConstR4_nonneg f
  have hbdd : BddAbove (Set.range fun x => ‖f x‖) := by
    refine ⟨|f y| + TestFunctions.lipConstR4 f * r, ?_⟩
    rintro _ ⟨w, rfl⟩
    by_cases hw : f w = 0
    · simp only [hw, norm_zero]
      positivity
    · have e1 := abs_sub_le_lipConstR4_mul hf w y
      have e2 : TestFunctions.euclidDistR4 w y ≤ r := hy w hw
      have e3 : TestFunctions.lipConstR4 f * TestFunctions.euclidDistR4 w y ≤ TestFunctions.lipConstR4 f * r :=
        mul_le_mul_of_nonneg_left e2 hlip
      have e4 : |f w| ≤ |f w - f y| + |f y| := by
        simpa using abs_add_le (f w - f y) (f y)
      show |f w| ≤ _
      linarith
  exact le_ciSup hbdd x
private theorem euclidNormVec_sub_update (x : Fin 4 → ℝ) (μ : Fin 4) (t : ℝ) :
    TorusMetric.euclidNormVec (x - Function.update x μ t) = |x μ - t| := by apply _root_.YangMills.Construction.ChessboardTori.WallDistance.euclidNormVec_sub_update <;> assumption
abbrev _root_.YangMills.SharedProofs.p26106 := @euclidNormVec_sub_update
variable {D : ChessboardSetup}
private theorem far_from_both_walls {c : GridCell D} {r : ℝ} {f : InfiniteLattice.AmbientSpace → ℝ}
    (hs : SupportedInCell c r f) {x : InfiniteLattice.AmbientSpace} (hx : f x ≠ 0) (μ : Fin 4) :
    c.grid.origin μ + c.side * (c.index μ : ℝ) + r ≤ x μ ∧
      x μ + r ≤ c.grid.origin μ + c.side * (c.index μ : ℝ) + c.side := by
  have hc : x μ - (c.grid.origin μ + c.grid.cellSide * (c.index μ : ℝ)) ∈ Set.Icc 0 c.grid.cellSide :=
    hs.support_in_cell x hx μ
  have hlow := hs.far_from_walls x hx (Function.update x μ (c.grid.origin μ + (c.index μ : ℝ) * c.grid.cellSide))
    (Set.mem_iUnion₂.2 ⟨μ, c.index μ, by simp [ReflectionGrid.wall]⟩)
  have hup := hs.far_from_walls x hx
    (Function.update x μ (c.grid.origin μ + ((c.index μ + 1 : ℤ) : ℝ) * c.grid.cellSide))
    (Set.mem_iUnion₂.2 ⟨μ, c.index μ + 1, by simp [ReflectionGrid.wall]⟩)
  rw [euclidNormVec_sub_update] at hlow hup
  have e1 := hc.1
  have e2 := hc.2
  push_cast at hup
  rw [abs_of_nonneg (by linarith)] at hlow
  rw [abs_of_nonpos (by nlinarith)] at hup
  constructor
  · show _ + c.grid.cellSide * _ + _ ≤ _
    linarith
  · show _ ≤ _ + c.grid.cellSide * _ + c.grid.cellSide
    linarith
private theorem mem_interior_cell {c : GridCell D} {r : ℝ} {f : InfiniteLattice.AmbientSpace → ℝ}
    (hs : SupportedInCell c r f) (x : InfiniteLattice.AmbientSpace) (hx : f x ≠ 0) : x ∈ interior c.cell := by
  have hopen : IsOpen {x : InfiniteLattice.AmbientSpace | ∀ μ, 0 < x μ - (c.grid.origin μ + c.grid.cellSide * (c.index μ : ℝ)) ∧
      x μ - (c.grid.origin μ + c.grid.cellSide * (c.index μ : ℝ)) < c.grid.cellSide} := by
    have hcont : ∀ μ, Continuous fun x : InfiniteLattice.AmbientSpace =>
        x μ - (c.grid.origin μ + c.grid.cellSide * (c.index μ : ℝ)) := fun μ => by fun_prop
    have hset : {x : InfiniteLattice.AmbientSpace | ∀ μ, 0 < x μ - (c.grid.origin μ + c.grid.cellSide * (c.index μ : ℝ)) ∧
        x μ - (c.grid.origin μ + c.grid.cellSide * (c.index μ : ℝ)) < c.grid.cellSide} =
        ⋂ μ, ({x : InfiniteLattice.AmbientSpace | 0 < x μ - (c.grid.origin μ + c.grid.cellSide * (c.index μ : ℝ))} ∩
          {x : InfiniteLattice.AmbientSpace | x μ - (c.grid.origin μ + c.grid.cellSide * (c.index μ : ℝ)) < c.grid.cellSide}) := by
      ext x
      simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_ofPred_eq]
    rw [hset]
    exact isOpen_iInter_of_finite fun μ =>
      (isOpen_lt continuous_const (hcont μ)).inter (isOpen_lt (hcont μ) continuous_const)
  refine interior_maximal (fun y hy μ => ⟨(hy μ).1.le, (hy μ).2.le⟩) hopen ?_
  intro μ
  have e1 := far_from_both_walls hs hx μ
  have e2 := hs.radius_pos
  have e3 : c.side = c.grid.cellSide := rfl
  rw [e3] at e1
  constructor <;> linarith [e1.1, e1.2]
private theorem dist_eq_euclidNormVec (x y : TestFunctions.EuclideanFourSpace) :
    dist x y = TorusMetric.euclidNormVec fun μ => x μ - y μ := by
  rw [EuclideanSpace.dist_eq]
  simp [TorusMetric.euclidNormVec, Real.dist_eq, sq_abs]
private theorem isLocalizedSource_recentredAt {c : GridCell D} {r : ℝ} {f : InfiniteLattice.AmbientSpace → ℝ}
    (hs : SupportedInCell c r f) (Λ : NNReal) (hΛ : (Λ : ℝ) = TestFunctions.lipConstR4 f) :
    IsLocalizedSource c.side r (TestFunctions.uniformNorm f) Λ (recentredAt c f) where
  lipschitz := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have e1 := abs_sub_le_lipConstR4_mul hs.lipschitz (fun μ => gridCellCentre c μ + x μ) (fun μ => gridCellCentre c μ + y μ)
    have e2 : TestFunctions.euclidDistR4 (fun μ => gridCellCentre c μ + x μ) (fun μ => gridCellCentre c μ + y μ) =
        dist x y := by
      rw [dist_eq_euclidNormVec]
      simp only [TestFunctions.euclidDistR4]
      congr 1
      funext μ
      simp
    rw [e2, ← hΛ] at e1
    rw [Real.dist_eq]
    exact e1
  abs_le x := abs_le_uniformNorm_of_supported hs.radius_pos hs.lipschitz hs.support_in_ball _
  exists_ball := by
    obtain ⟨y, hy⟩ := hs.support_in_ball
    refine ⟨WithLp.toLp 2 fun μ => y μ - gridCellCentre c μ, fun x hx => ?_⟩
    have e1 : TorusMetric.euclidNormVec ((fun μ => gridCellCentre c μ + x μ) - y) ≤ r := hy _ hx
    rw [dist_eq_euclidNormVec]
    convert e1 using 2
    funext μ
    simp
    ring
  away_from_faces x hx μ := by
    have e1 := far_from_both_walls hs hx μ
    have e2 : gridCellCentre c μ = c.grid.origin μ + c.side * (c.index μ : ℝ) + c.side / 2 := rfl
    simp only [e2] at e1
    rcases abs_cases (x μ) with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> linarith [e1.1, e1.2]
private theorem two_le_cellExponent (c : GridCell D) : 2 ≤ c.grid.q + ((D.K : ℕ) : ℤ) := by
  have hL := D.one_lt_factor
  have hL0 : (D.L : ℝ) ≠ 0 := by linarith
  have ha : D.mesh ≤ c.grid.cellSide / (D.L : ℝ) ^ 2 := c.hasAdmissibleSide.2
  simp only [ChessboardSetup.mesh, PeriodicLattice.meshSize, ReflectionGrid.cellSide] at ha
  rw [← zpow_natCast (D.L : ℝ) 2, ← zpow_sub₀ hL0] at ha
  have e1 := (zpow_le_zpow_iff_right₀ hL).1 ha
  push_cast at e1
  omega
private theorem side_eq_pow_mul_mesh (c : GridCell D) (κ : ℕ) (hκ : (κ : ℤ) = c.grid.q + ((D.K : ℕ) : ℤ)) :
    c.side = (D.L : ℝ) ^ κ * D.mesh := by
  have hL := D.one_lt_factor
  have hL0 : (D.L : ℝ) ≠ 0 := by linarith
  show (D.L : ℝ) ^ c.grid.q = _
  simp only [ChessboardSetup.mesh, PeriodicLattice.meshSize]
  rw [← zpow_natCast, ← zpow_add₀ hL0, hκ]
  simp
private theorem exists_site_eq_gridCellCentre (c : GridCell D) (κ : ℕ)
    (hκ : (κ : ℤ) = c.grid.q + ((D.K : ℕ) : ℤ)) (μ : Fin 4) :
    ∃ i : ℤ, D.mesh * (i : ℝ) = gridCellCentre c μ := by
  obtain ⟨i₀, hi⟩ := c.grid.origin_mem μ
  obtain ⟨m, hm⟩ : Odd (D.L ^ κ) := D.isAdmissible.1.pow
  refine ⟨i₀ + (D.L : ℤ) ^ κ * c.index μ + m + 1, ?_⟩
  have hm' : (D.L : ℝ) ^ κ = 2 * (m : ℝ) + 1 := by exact_mod_cast hm
  simp only [gridCellCentre, hi, side_eq_pow_mul_mesh c κ hκ]
  push_cast
  rw [hm']
  ring
private theorem sixteenCopyBound_of_admissibleFlow (ℓ : StepParameters) (Kr : ResponseParameters) (Ξ A₀ b₀ : ℝ)
    (hsrc : ForAllSources ℓ Kr Ξ fun β K κ al ρ H Λ f => ∀ z : TorusSite (2 * ℓ.side ^ κ),
      ReflectedMeanBounded ℓ β K κ 2 z f (centring ℓ β al K κ ρ f)
        (copySize A₀ b₀ (cellLength ℓ.side K κ) ρ * sourceNorm ρ H Λ))
    (hM : tiledMeanEqReflectedMeanStatement) (D : ChessboardSetup) (hDL : D.L = ℓ.side)
    (hdat : IsAdmissibleFlow ℓ Ξ D.β (D.K : ℕ)) : SixteenCopyBound D A₀ b₀ := by
  intro c r f hs
  obtain ⟨al, -, hall⟩ := hsrc D.β (D.K : ℕ) hdat
  have e2 := two_le_cellExponent c
  obtain ⟨κ, hκ⟩ : ∃ κ : ℕ, (κ : ℤ) = c.grid.q + ((D.K : ℕ) : ℤ) :=
    ⟨(c.grid.q + ((D.K : ℕ) : ℤ)).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hκ2 : 2 ≤ κ := by omega
  have ha : levelSpacing ℓ.side (D.K : ℕ) 0 = D.mesh := by
    simp [levelSpacing, ChessboardSetup.mesh, PeriodicLattice.meshSize, hDL]
  have hside : cellLength ℓ.side (D.K : ℕ) κ = c.side := by
    rw [side_eq_pow_mul_mesh c κ hκ, cellLength, ha, hDL]
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : NNReal, (Λ : ℝ) = TestFunctions.lipConstR4 f := ⟨⟨_, lipConstR4_nonneg f⟩, rfl⟩
  have hsource : IsLocalizedSource (cellLength ℓ.side (D.K : ℕ) κ) r (TestFunctions.uniformNorm f) Λ
      (recentredAt c f) := by
    rw [hside]
    exact isLocalizedSource_recentredAt hs Λ hΛ
  have hr : r ≤ cellLength ℓ.side (D.K : ℕ) κ / 4 := by
    rw [hside]
    exact hs.radius_le
  have hb := hall κ hκ2 r _ Λ _ hs.radius_pos hr hsource
  choose i hi using exists_site_eq_gridCellCentre c κ hκ
  let z : TorusSite (2 * ℓ.side ^ κ) := fun μ => ((i μ : ℤ) : ZMod (2 * ℓ.side ^ κ))
  refine ⟨centring ℓ D.β al (D.K : ℕ) κ r (recentredAt c f), ?_⟩
  have key : tiledMean c.grid (cubicCounts D 0) c.cell
      (centredSmeared D f (centring ℓ D.β al (D.K : ℕ) κ r (recentredAt c f))) =
      ((reflectedProductMean D.β D.mesh (ℓ.side ^ κ) 2 z (recentredAt c f)
        (centring ℓ D.β al (D.K : ℕ) κ r (recentredAt c f)) : ℝ) : ℂ) :=
    hM ℓ.side D c κ 0 f _ z hDL hκ (mem_interior_cell hs) fun μ => ⟨i μ, rfl, hi μ⟩
  obtain ⟨h0, h1⟩ := hb z
  rw [ha] at h0 h1
  show ‖tiledMean c.grid (cubicCounts D 0) c.cell _‖ ≤ _
  rw [key, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
  refine h1.trans_eq ?_
  simp only [copyBound, radiusNorm, sourceNorm, hΛ, hside]
  norm_num
theorem sixteenCopyBoundForAdmissibleFlows_of_twoCellTorus (hS : reflectedMeanBoundOnTwoCellTorus)
    (hM : tiledMeanEqReflectedMeanStatement) : sixteenCopyBoundForAdmissibleFlows := by
  intro a ha
  obtain ⟨L₀, rt₀, C₀, hrt, hT⟩ := hS a ha
  refine ⟨L₀, rt₀, C₀, hrt, fun L hLo hL T h1 h2 h3 h4 h5 h6 h7 => ?_⟩
  obtain ⟨y₀, hy⟩ := hT L hLo hL T h1 h2 h3 h4 h5 h6 h7
  refine ⟨y₀, fun y hy₀ hR hW Ξ hΞ => ?_⟩
  obtain ⟨Kr, -, hP⟩ := hy y hy₀ hR hW
  obtain ⟨A₀, b₀, hA, hb, hsrc⟩ := hP Ξ hΞ
  exact ⟨A₀, b₀, hA, hb, fun D hDL hdat =>
    sixteenCopyBound_of_admissibleFlow (T.stepParameters y) Kr Ξ A₀ b₀ hsrc hM D hDL hdat⟩
end YangMills.Construction.SmallTorusCopies
end
