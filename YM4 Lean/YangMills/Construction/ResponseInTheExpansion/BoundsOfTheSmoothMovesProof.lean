import YangMills.Construction.ResponseInTheExpansion.CalculusOfTheColdHalf
import YangMills.Construction.ResponseInTheExpansion.CalculusOfTheSmoothMoves
import YangMills.Construction.ResponseInTheExpansion.SmoothMovesAreSlots
import YangMills.Construction.RunningCouplingSlope.DensityOfTheStepIsAnalyticAtParametersProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheDensitiesAreNearTheirLimitsProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology Quaternion
namespace YangMills.Construction
open BlockAverages hiding bondSpread
open ColdStepAtMirrorFrames Interpolation WeightedResponses TorusComparison
namespace ResponseInTheExpansion
namespace SmoothIncrementBounds
variable {F : BlockFrame}
private theorem hasDerivAt_line_of_iteratedFDeriv {g : (Fin 1 → ℝ) → ℝ} (hg : DifferentiableAt ℝ g 0) :
    HasDerivAt (fun τ : ℝ => g fun _ => τ) (iteratedFDeriv ℝ 1 g 0 fun l => Pi.single l 1) 0 := by
  have hl : HasDerivAt (fun τ : ℝ => (fun _ => τ : Fin 1 → ℝ)) (fun _ => (1 : ℝ)) 0 :=
    hasDerivAt_pi.2 fun _ => hasDerivAt_id _
  have h0 : HasFDerivAt g (fderiv ℝ g 0) ((fun _ => (0 : ℝ)) : Fin 1 → ℝ) := hg.hasFDerivAt
  have h1 := h0.comp_hasDerivAt (0 : ℝ) hl
  have e : (Pi.single 0 1 : Fin 1 → ℝ) = fun _ => 1 := by
    funext i
    rw [Subsingleton.elim i 0]
    simp
  rw [iteratedFDeriv_one_apply, e]
  exact h1
private theorem abs_deriv_le_of_abs_sub_le {φ r : ℝ → ℝ} {φ' r' M : ℝ} (hφ : HasDerivAt φ φ' 0)
    (hr : HasDerivAt r r' 0)
    (h : ∀ᶠ τ in 𝓝 (0 : ℝ), |φ τ - φ 0| ≤ M * |r τ - r 0|) : |φ'| ≤ M * |r'| := by
  have h1 := (hasDerivAt_iff_tendsto_slope.1 hφ).abs
  have h2 := ((hasDerivAt_iff_tendsto_slope.1 hr).abs).const_mul M
  refine le_of_tendsto_of_tendsto h1 h2 ?_
  have h3 : ∀ᶠ τ in 𝓝[≠] (0 : ℝ), |φ τ - φ 0| ≤ M * |r τ - r 0| := h.filter_mono nhdsWithin_le_nhds
  filter_upwards [h3, self_mem_nhdsWithin] with τ hτ hne
  have e : ∀ g : ℝ → ℝ, |slope g 0 τ| = |g τ - g 0| / |τ| := fun g => by
    rw [slope_def_field, abs_div, sub_zero]
  rw [e, e, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right hτ (abs_nonneg _)
private theorem leftTranslate_zero (V : F.GaugeField F.top) :
    leftTranslate (fun _ _ => (0 : imaginaryQuaternions)) V = V := by apply _root_.YangMills.SharedProofs.p46723 <;> assumption
private theorem toImaginary_add_smul (u e : EuclideanSpace ℝ (Fin 3)) (τ : ℝ) :
    toImaginary (u + τ • e) = toImaginary u + τ • toImaginary e := by apply _root_.YangMills.SharedProofs.p23127 <;> assumption
private theorem toImaginary_zero : toImaginary (0 : EuclideanSpace ℝ (Fin 3)) = 0 := by apply _root_.YangMills.Construction.BondCoordinates.toImaginary_zero <;> assumption
private theorem norm_toImaginary (v : EuclideanSpace ℝ (Fin 3)) : ‖toImaginary v‖ = ‖v‖ := by apply _root_.YangMills.Construction.Interpolation.ExponentBoundSteps.norm_toImaginary <;> assumption
private def chordDirection (b : ↥(chordBonds (finiteCells F))) (e : EuclideanSpace ℝ (Fin 3)) :
    ChartDirection F :=
  Sum.inl (b.1.1, b.1.2, toImaginary e)
private theorem stepCoordinates_line (η : StepVariable (finiteCells F)) (b : ↥(chordBonds (finiteCells F)))
    (e : EuclideanSpace ℝ (Fin 3)) (τ : ℝ) (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (η + Pi.single b (τ • e)) x i =
      stepCoordinates η x i + τ • directionCoordinate (chordDirection b e) x i := by
  classical
  simp only [stepCoordinates, directionCoordinate, chordDirection]
  by_cases h : (x, i) ∈ chordBonds (finiteCells F)
  · simp only [dif_pos h]
    by_cases hb : b = ⟨(x, i), h⟩
    · subst hb
      simp [toImaginary_add_smul]
    · have h1 : ¬ (b.1.1 = x ∧ b.1.2 = i) := fun h2 => hb (Subtype.ext (Prod.ext h2.1 h2.2))
      have h3 : (⟨(x, i), h⟩ : ↥(chordBonds (finiteCells F))) ≠ b := fun h4 => hb h4.symm
      simp [h1, Pi.single_eq_of_ne h3]
  · simp only [dif_neg h, zero_add]
    have h1 : ¬ (b.1.1 = x ∧ b.1.2 = i) := fun h2 => h (by
      have h3 := b.2
      rwa [show b.1 = (x, i) from Prod.ext h2.1 h2.2] at h3)
    simp [h1]
private theorem interpolatedCoords_line (s a ρA : ℝ) (m : ℕ) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F))
    (b : ↥(chordBonds (finiteCells F))) (e : EuclideanSpace ℝ (Fin 3)) (τ : ℝ) :
    interpolatedCoords s a ρA m V (η + Pi.single b (τ • e)) =
      fun x i => interpolatedCoords s a ρA m V η x i + τ • directionCoordinate (chordDirection b e) x i := by
  funext x i
  simp only [interpolatedCoords]
  rw [stepCoordinates_line, add_assoc]
private structure SmallnessConditions (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) : Prop where
  one_le_a : 1 ≤ T.a
  odd_L : Odd T.L
  big_L : 2 ^ 40 ≤ T.L
  admissible : T.chainParams.Admissible T.a T.L
  Ct_nonneg : 0 ≤ T.Ct
  κ_pos : 0 < T.κ
  κ_le : 2 ^ 5 * T.κ ≤ T.chainParams.δ₁
  σ_pos : 0 < T.σ
  σ_chart : T.Ct * T.σ + T.σ / 64 ≤ 1 / (64 * (T.L : ℝ))
  σ_curvature : 3 / 4 * T.σ ≤ T.chainParams.σA
  σ_contour : T.Ct * T.σ + 5 * (T.L : ℝ) * (T.σ / 64) ≤ 1 / 2
  n₀_large : 64 ≤ T.n₀
  coupling_large : 2 ≤ T.coupling
private theorem eventually_smallnessConditions : EventuallyInParameters SmallnessConditions := by
  intro a ha
  refine ⟨2 ^ 40, fun L hL hL₀ c hc => ⟨0, fun Ct hCt => ?_⟩⟩
  have hδ := hc.positivity.1
  have hσA := hc.positivity.2.2.2.1
  have hLp : (0 : ℝ) < L := by
    have : 0 < L := lt_of_lt_of_le (by norm_num) hL₀
    exact_mod_cast this
  refine ⟨c.δ₁ / 2 ^ 5, by positivity, fun κ hκ0 hκ => ⟨1, one_pos, fun η₃ _ _ _ => ⟨0, fun k _ => ?_⟩⟩⟩
  have hκ' : 2 ^ 5 * κ ≤ c.δ₁ := by
    rw [le_div_iff₀ (by positivity)] at hκ
    linarith
  refine ⟨min c.σA (min (1 / (64 * L * (Ct + 1))) (1 / (2 * (Ct + 5 * L)))), ?_, fun σ hσ0 hσ p _ => ?_⟩
  · refine lt_min hσA (lt_min (by positivity) (by positivity))
  have h1 : σ ≤ c.σA := hσ.trans (min_le_left _ _)
  have h2 : σ ≤ 1 / (64 * L * (Ct + 1)) := hσ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have h3 : σ ≤ 1 / (2 * (Ct + 5 * L)) := hσ.trans ((min_le_right _ _).trans (min_le_right _ _))
  rw [le_div_iff₀ (by positivity)] at h2 h3
  have hLσ := mul_pos hLp hσ0
  have hCσ : 0 ≤ Ct * σ := by positivity
  refine ⟨0, fun Cs _ E _ => ⟨64, fun n₀ hn => ⟨0, fun CE _ => ⟨2, fun y hy => ?_⟩⟩⟩⟩
  refine ⟨ha, hL, hL₀, hc, hCt, hκ0, hκ', hσ0, ?_, ?_, ?_, hn, hy⟩
  · show Ct * σ + σ / 64 ≤ 1 / (64 * (L : ℝ))
    rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_nonneg hCσ hLp.le]
  · show 3 / 4 * σ ≤ c.σA
    linarith
  · show Ct * σ + 5 * (L : ℝ) * (σ / 64) ≤ 1 / 2
    nlinarith
private theorem isAdmissibleChartPoint_of_ball {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} (hT : SmallnessConditions T)
    (hM : ChartShiftLipschitz)
    {m : ℕ} {V : F.GaugeField F.top} (hL : F.blockSide = T.L)
    (hs : InterpolatedFrameSmall 1 T.a T.chainParams.ρA T.chainParams.δ₂ T.Ct T.σ m V)
    {η : StepVariable (finiteCells F)} (hη : ∀ b, ‖η b‖ ≤ T.ballRadius) :
    IsAdmissibleChartPoint T.L T.chainParams.σA (interpolatedCoords 1 T.a T.chainParams.ρA m V η) V := by
  have hρ : 0 ≤ T.ballRadius := by
    have := hT.σ_pos
    unfold StepParameters.ballRadius
    positivity
  have hodd : Odd F.blockSide := hL ▸ hT.odd_L
  have hc := (hM F V (fun z i => interpolatedFrame 1 T.a T.chainParams.ρA m (z, i) V) η T.ballRadius
    hodd hη hρ).1
  refine ⟨fun b hb => ?_, fun p hp => ?_⟩
  · have h1 := hs.norm_le b hb
    have h2 := hc b.1 b.2
    have h3 := hT.σ_chart
    calc ‖interpolatedCoords 1 T.a T.chainParams.ρA m V η b.1 b.2‖
        ≤ ‖interpolatedFrame 1 T.a T.chainParams.ρA m b V‖ + ‖stepCoordinates η b.1 b.2‖ := norm_add_le _ _
      _ ≤ T.Ct * T.σ + T.ballRadius := add_le_add h1 h2
      _ ≤ 1 / (64 * (T.L : ℝ)) := h3
  · exact lt_of_lt_of_le (hs.small_curvature_nearby η hη p hp) hT.σ_curvature
private theorem sum_single_direction (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (b : ↥(chordBonds (finiteCells F))) (e : EuclideanSpace ℝ (Fin 3)) (τ : ℝ) :
    (fun x i => w x i + ∑ l : Fin 1, (fun _ : Fin 1 => τ) l •
        directionCoordinate ((fun _ : Fin 1 => chordDirection b e) l) x i) =
      fun x i => w x i + τ • directionCoordinate (chordDirection b e) x i := by
  funext x i
  simp
private theorem leftTranslate_sum_directionMove (V : F.GaugeField F.top) (b : ↥(chordBonds (finiteCells F)))
    (e : EuclideanSpace ℝ (Fin 3)) (τ : ℝ) :
    leftTranslate (fun y i => ∑ l : Fin 1, (fun _ : Fin 1 => τ) l •
      directionMove ((fun _ : Fin 1 => chordDirection b e) l) y i) V = V := by
  have e1 : (fun y i => ∑ l : Fin 1, (fun _ : Fin 1 => τ) l •
      directionMove ((fun _ : Fin 1 => chordDirection b e) l) y i) =
      fun _ _ => (0 : imaginaryQuaternions) := by
    funext y i
    simp [directionMove, chordDirection]
  rw [e1, leftTranslate_zero]
private theorem directionReach_single (Y : F.Cell) (q : ChartDirection F) :
    directionReach Y (fun _ : Fin 1 => q) = cellSupDist Y (directionCell q) := by
  simp [directionReach]
private theorem norm_directionVector_chord {e : EuclideanSpace ℝ (Fin 3)} (he : ‖e‖ = 1)
    (b : ↥(chordBonds (finiteCells F))) :
    ‖directionVector (chordDirection b e)‖ = 1 := by
  show ‖toImaginary e‖ = 1
  rw [norm_toImaginary]
  exact he
private theorem cellEnergyShare_hasDerivAt_line {a δ₁ c₁ : ℝ} {w : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    {V : F.GaugeField F.top} {Y : F.Cell}
    {b : ↥(chordBonds (finiteCells F))} {e : EuclideanSpace ℝ (Fin 3)} (he : ‖e‖ = 1)
    (h₁ : AnalyticAt ℝ (cellEnergyAlong a Y w V fun _ : Fin 1 => chordDirection b e) 0)
    (h₂ : (∀ l : Fin 1, ‖directionVector ((fun _ : Fin 1 => chordDirection b e) l)‖ = 1) →
      |cellEnergyKernel a Y w V fun _ : Fin 1 => chordDirection b e| ≤
        c₁ * Real.exp (-(δ₁ * directionReach Y fun _ : Fin 1 => chordDirection b e))) :
    ∃ D, HasDerivAt (fun τ : ℝ => cellEnergyShare a Y
        (fun x i => w x i + τ • directionCoordinate (chordDirection b e) x i) V) D 0 ∧
      |D| ≤ c₁ * Real.exp (-(δ₁ * cellSupDist Y (enclosingCell b.1.1))) := by
  refine ⟨cellEnergyKernel a Y w V fun _ : Fin 1 => chordDirection b e, ?_, ?_⟩
  · have h := hasDerivAt_line_of_iteratedFDeriv h₁.differentiableAt
    have e1 : (fun τ : ℝ => cellEnergyAlong a Y w V (fun _ : Fin 1 => chordDirection b e) fun _ => τ) =
        fun τ : ℝ => cellEnergyShare a Y
          (fun x i => w x i + τ • directionCoordinate (chordDirection b e) x i) V := by
      funext τ
      unfold cellEnergyAlong
      rw [leftTranslate_sum_directionMove, sum_single_direction]
    rw [e1] at h
    exact h
  · have := h₂ fun _ => norm_directionVector_chord he b
    rw [directionReach_single] at this
    exact this
private theorem minimalSiteShare_hasDerivAt_line {a δ₁ c₁ : ℝ}
    {w : F.Site F.depth → Fin 4 → imaginaryQuaternions} {V : F.GaugeField F.top} {y : F.Site F.depth}
    {b : ↥(chordBonds (finiteCells F))} {e : EuclideanSpace ℝ (Fin 3)} (he : ‖e‖ = 1)
    (h₁ : AnalyticAt ℝ (siteShareAlong a y w V fun _ : Fin 1 => chordDirection b e) 0)
    (h₂ : (∀ l : Fin 1, ‖directionVector ((fun _ : Fin 1 => chordDirection b e) l)‖ = 1) →
      |siteShareMixedDeriv a y w V fun _ : Fin 1 => chordDirection b e| ≤
        c₁ * Real.exp (-(δ₁ * directionReach (enclosingCell y) fun _ : Fin 1 => chordDirection b e))) :
    ∃ D, HasDerivAt (fun τ : ℝ => minimalSiteShare a y
        (chartedField (fun x i => w x i + τ • directionCoordinate (chordDirection b e) x i) V)) D 0 ∧
      |D| ≤ c₁ * Real.exp (-(δ₁ * cellSupDist (enclosingCell y) (enclosingCell b.1.1))) := by
  refine ⟨siteShareMixedDeriv a y w V fun _ : Fin 1 => chordDirection b e, ?_, ?_⟩
  · have h := hasDerivAt_line_of_iteratedFDeriv h₁.differentiableAt
    have e1 : (fun τ : ℝ => siteShareAlong a y w V (fun _ : Fin 1 => chordDirection b e) fun _ => τ) =
        fun τ : ℝ => minimalSiteShare a y
          (chartedField (fun x i => w x i + τ • directionCoordinate (chordDirection b e) x i) V) := by
      funext τ
      unfold siteShareAlong
      rw [leftTranslate_sum_directionMove, sum_single_direction]
    rw [e1] at h
    exact h
  · have := h₂ fun _ => norm_directionVector_chord he b
    rw [directionReach_single] at this
    exact this
private theorem hasDerivAt_line_of_kernel {G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ}
    {B r : ℝ} {P : Finset F.Cell}
    {η : StepVariable (finiteCells F)} {V : F.GaugeField F.top} {b : ↥(chordBonds (finiteCells F))}
    {e : EuclideanSpace ℝ (Fin 3)} {c : Fin 0 → F.Site F.top × Fin 4} {X : Fin 0 → imaginaryQuaternions}
    (h : HasDecayingKernelAt (l := 1) (j := 0) G B r P η V (fun _ => b) (fun _ => e) c X) :
    ∃ D, HasDerivAt (fun τ : ℝ => G (η + Pi.single b (τ • e)) V) D 0 ∧
      |D| ≤ B * Real.exp (-(r * cellSetDiameter (P ∪ {enclosingCell b.1.1}))) := by
  obtain ⟨h₁, h₂⟩ := h
  have hd : DifferentiableAt ℝ (jointDisplacement G η V (fun _ : Fin 1 => b) (fun _ => e) c X) 0 :=
    h₁.differentiableAt (by norm_num)
  refine ⟨jointMixedDeriv (l := 1) (j := 0) G η V (fun _ => b) (fun _ => e) c X, ?_, ?_⟩
  · have h₃ := hasDerivAt_line_of_iteratedFDeriv
      (g := jointDisplacement G η V (fun _ : Fin 1 => b) (fun _ => e) c X) hd
    have e1 : (fun τ : ℝ => jointDisplacement G η V (fun _ : Fin 1 => b) (fun _ => e) c X fun _ => τ) =
        fun τ : ℝ => G (η + Pi.single b (τ • e)) V := by
      funext τ
      simp only [jointDisplacement, displacedPoint]
      have e2 : (fun i : Fin 0 => (fun _ : Fin (1 + 0) => τ) (Fin.natAdd 1 i)) = 0 := Subsingleton.elim _ _
      rw [e2, leftTranslate_bondSpread_zero]
      simp
    rw [e1] at h₃
    exact h₃
  · have e3 : chordBondCells (fun _ : Fin 1 => b) = {enclosingCell b.1.1} := by
      simp [chordBondCells]
    have e4 : topBondCells c = ∅ := by
      simp [topBondCells]
    rw [e3, e4, Finset.union_empty] at h₂
    exact h₂
private theorem cellSupDist_le_diameter (u v : F.Cell) (P : Finset F.Cell) (hu : u ∈ P) (hv : v ∈ P) :
    cellSupDist u v ≤ cellSetDiameter P := by
  unfold cellSetDiameter
  exact (Finset.le_sup (f := fun v' => cellSupDist u v') hv).trans
    (Finset.le_sup (f := fun u' => P.sup fun v' => cellSupDist u' v') hu)
private theorem contDiffAt_of_joint {r : WithTop ℕ∞} {K : AboveFrames F} {V : F.GaugeField F.top}
    {c : Fin 0 → F.Site F.top × Fin 4}
    {X : Fin 0 → imaginaryQuaternions} {η : StepVariable (finiteCells F)}
    (h : ContDiffAt ℝ r (fun q : (Fin 0 → ℝ) × StepVariable (finiteCells F) =>
      K q.2 (leftTranslate (bondSpread c X q.1) V)) (0, η)) : ContDiffAt ℝ r (fun ζ => K ζ V) η := by
  have hl : ContDiffAt ℝ r (fun ζ : StepVariable (finiteCells F) => ((0 : Fin 0 → ℝ), ζ)) η :=
    contDiffAt_const.prodMk contDiffAt_id
  have h₂ := ContDiffAt.comp (f := fun ζ : StepVariable (finiteCells F) => ((0 : Fin 0 → ℝ), ζ)) η h hl
  have e : (fun ζ => K ζ V) = (fun q : (Fin 0 → ℝ) × StepVariable (finiteCells F) =>
      K q.2 (leftTranslate (bondSpread c X q.1) V)) ∘ fun ζ => ((0 : Fin 0 → ℝ), ζ) := by
    funext ζ
    show K ζ V = K ζ (leftTranslate (bondSpread c X 0) V)
    rw [leftTranslate_bondSpread_zero]
  rw [e]
  exact h₂
private theorem exists_bound_on_ball {ρ : ℝ} {A : StepVariable (finiteCells F) → ℝ}
    (hc : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ ρ) → ContinuousAt A η) :
    ∃ M : ℝ, ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) → |A η| ≤ M := by
  have hK : IsCompact {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ ≤ ρ} := by
    have e : {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ ≤ ρ} =
        Set.pi Set.univ fun _ => Metric.closedBall 0 ρ := by
      ext η
      simp [Set.mem_pi]
    rw [e]
    exact isCompact_univ_pi fun _ => isCompact_closedBall _ _
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (f := A) fun η hη => (hc η hη).continuousWithinAt
  exact ⟨M, fun η hη => hM η fun b => (hη b).le⟩
private theorem isVanishingMove_of_slot {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {x : ℝ} {f : LocalFamily} {Cq : ℕ → ℝ}
    {C h g₀ g₁ : ℝ} {Y : F.Cell}
    {K : AboveFrames F} {V : F.GaugeField F.top} (hs : IsSmoothSlotOfSize T x f Cq C h Y K V) (h0 : K 0 V = 0)
    (hslope : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < T.ballRadius) →
      DifferentiableAt ℝ (fun ζ => K ζ V) η →
      ∀ b : ↥(chordBonds (finiteCells F)), bondGradNorm (fun ζ => K ζ V) b η ≤
        (g₀ + g₁ * (x * Real.sqrt (localSqNorm T.κ Y η))) *
          Real.exp (-(2 ^ 5 * T.κ * bondDistToCell Y b))) :
    IsVanishingMoveWithGradient T.ballRadius x T.κ g₀ g₁ Y fun η => K η V := by
  refine ⟨fun η hη => ?_, ?_, h0, fun η hη b => ?_⟩
  · exact ((hs.1.contDiffAt_two η hη).of_le one_le_two).contDiffWithinAt
  · exact exists_bound_on_ball fun η hη =>
      (contDiffAt_of_joint (hs.1.smoothBounded.smooth η 0 Fin.elim0 Fin.elim0 hη)).continuousAt
  · exact hslope η hη ((hs.1.contDiffAt_two η hη).differentiableAt (by norm_num)) b
private theorem card_centredCube (M : ℕ) (hM : Odd M) : ((centredCube M).card : ℝ) = (M : ℝ) ^ 4 := by apply _root_.YangMills.Construction.BlockAverages.GeneratorMeans.card_centredCube_real <;> assumption
private theorem norm_contourAverage_mem (hL : Odd F.blockSide) (W : F.GaugeField F.depth)
    (V : F.GaugeField F.top) (c : F.Site F.top × Fin 4)
    (h : ∀ (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)), h ∈ centredCube F.blockSide →
      ‖contourHolonomyDefect W V c h π - 1‖ ≤ 1 / 2) :
    1 / 2 ≤ ‖_root_.YangMills.Construction.BlockAverages.contourAverage W c‖ ∧ ‖_root_.YangMills.Construction.BlockAverages.contourAverage W c‖ ≤ 1 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GapTerms.norm_contourAverage_mem_shell <;> assumption
open Classical in
private theorem card_sites_in_cell_le (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (Y : F.Cell) :
    (((sitesOfCells (finiteCells F) F.depth).filter fun y => enclosingCell y = Y).card : ℝ) ≤
      (F.blockSide : ℝ) ^ 4 := by
  have hsub : ((sitesOfCells (finiteCells F) F.depth).filter fun y => enclosingCell y = Y) ⊆
      (centredCube F.blockSide).image fun h =>
        (cellCentre F.depth Y + siteOfCoords F.depth h : F.Site F.depth) := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
    simp only [sitesOfCells, Finset.mem_biUnion, Finset.mem_image, BlockOffsets.top_sub_depth,
      pow_one] at hx1
    obtain ⟨z, -, h, hh, rfl⟩ := hx1
    rw [BlockOffsets.enclosingCell_offset hL hs z h hh] at hx2
    subst hx2
    exact Finset.mem_image.mpr ⟨h, hh, rfl⟩
  have h1 := (Finset.card_le_card hsub).trans Finset.card_image_le
  rw [← card_centredCube _ hL]
  exact_mod_cast h1
private theorem norm_contourAverage_interpolated {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} (hT : SmallnessConditions T)
    (hM : ChartShiftLipschitz)
    {m : ℕ} {V : F.GaugeField F.top} (hL : F.blockSide = T.L)
    (hs : InterpolatedFrameSmall 1 T.a T.chainParams.ρA T.chainParams.δ₂ T.Ct T.σ m V)
    (c : F.Site F.top × Fin 4)
    {η : StepVariable (finiteCells F)} (hη : ∀ b, ‖η b‖ ≤ T.ballRadius) :
    ‖_root_.YangMills.Construction.BlockAverages.contourAverage (interpolatedField 1 T.a T.chainParams.ρA m V η) c‖ ∈ Set.Icc (1 / 2 : ℝ) 1 := by
  have hρ : 0 ≤ T.ballRadius := by
    have := hT.σ_pos
    unfold StepParameters.ballRadius
    positivity
  have hodd : Odd F.blockSide := hL ▸ hT.odd_L
  have hc := (hM F V (fun z i => interpolatedFrame 1 T.a T.chainParams.ρA m (z, i) V) η T.ballRadius
    hodd hη hρ).2.2
  refine norm_contourAverage_mem hodd _ V c fun h π hh => ?_
  have h1 := hc c h π hh
  have h2 := hs.contour_near_one c h π hh
  have h3 := hT.σ_contour
  rw [hL] at h1
  unfold StepParameters.ballRadius at h1
  refine le_trans ?_ h3
  exact h1.trans (by linarith)
private theorem scoreRemainder_lipschitz {Q : ColdHalfLaw} {M : ℝ}
    (h : ContDiffOn ℝ ((1 : ℕ) : ℕ∞) Q.scoreRemainder (Set.Icc (1 / 2) 1))
    (hb : ∀ r ∈ Set.Icc (1 / 2 : ℝ) 1, |iteratedDerivWithin 1 Q.scoreRemainder (Set.Icc (1 / 2) 1) r| ≤ M)
    {r r' : ℝ} (hr : r ∈ Set.Icc (1 / 2 : ℝ) 1) (hr' : r' ∈ Set.Icc (1 / 2 : ℝ) 1) :
    |Q.scoreRemainder r - Q.scoreRemainder r'| ≤ M * |r - r'| := by
  have hd : DifferentiableOn ℝ Q.scoreRemainder (Set.Icc (1 / 2) 1) := h.differentiableOn (by norm_num)
  have h1 := Convex.norm_image_sub_le_of_norm_derivWithin_le (f := Q.scoreRemainder) (C := M) hd
    (fun u hu => by
      have := hb u hu
      rw [iteratedDerivWithin_one] at this
      exact this) (convex_Icc _ _) hr' hr
  exact h1
private theorem hasDerivAt_bondPartialDeriv {A : StepVariable (finiteCells F) → ℝ}
    {η : StepVariable (finiteCells F)}
    (hd : DifferentiableAt ℝ A η) (b : ↥(chordBonds (finiteCells F))) (e : EuclideanSpace ℝ (Fin 3)) :
    HasDerivAt (fun τ : ℝ => A (η + Pi.single b (τ • e))) (bondPartialDeriv A b η e) 0 := by
  have hl : HasDerivAt (fun τ : ℝ => η + Pi.single b (τ • e)) (Pi.single b e) 0 := by
    have e1 : (fun τ : ℝ => η + Pi.single b (τ • e)) =
        fun τ : ℝ => η + τ • (Pi.single b e : StepVariable (finiteCells F)) := by
      funext τ
      rw [Pi.single_smul]
    rw [e1]
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single b e : StepVariable (finiteCells F))).const_add η
  have hd' : HasFDerivAt A (fderiv ℝ A η) (η + Pi.single b ((0 : ℝ) • e)) := by
    simpa using hd.hasFDerivAt
  exact hd'.comp_hasDerivAt (0 : ℝ) hl
private theorem exp_decay_bondDist {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} (hT : SmallnessConditions T) (Y : F.Cell)
    (b : ↥(chordBonds (finiteCells F))) :
    Real.exp (-(T.chainParams.δ₁ * (cellSupDist Y (enclosingCell b.1.1) : ℝ))) ≤
      Real.exp (-(2 ^ 5 * T.κ * bondDistToCell Y b)) := by
  unfold bondDistToCell
  rw [PatchLocality.cellSupDist_comm Y]
  exact Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right hT.κ_le (Nat.cast_nonneg _)))
private theorem exp_decay_near {κ : ℝ} (hκ : 0 < κ) {s d : ℕ} (h : d ≤ s + 1) :
    Real.exp (-(2 ^ 8 * κ * s)) ≤ Real.exp (2 ^ 5 * κ) * Real.exp (-(2 ^ 5 * κ * d)) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have h1 : (d : ℝ) ≤ s + 1 := by exact_mod_cast h
  have h2 := mul_le_mul_of_nonneg_left h1 hκ.le
  have h3 : 0 ≤ κ * s := by positivity
  nlinarith
private theorem exp_decay_diameter {κ : ℝ} (hκ : 0 < κ) {s d : ℕ} (h : d ≤ s) :
    Real.exp (-(2 ^ 8 * κ * s)) ≤ Real.exp (-(2 ^ 5 * κ * d)) := by
  refine Real.exp_le_exp.2 ?_
  have h1 : (d : ℝ) ≤ s := by exact_mod_cast h
  have h2 := mul_le_mul_of_nonneg_left h1 hκ.le
  have h3 : 0 ≤ κ * s := by positivity
  nlinarith
private theorem natAbs_valMinAbs_le_one (n : ℕ) (z : ℤ) (hz : z = 0 ∨ z = 1) :
    ((z : ZMod n).valMinAbs).natAbs ≤ 1 := by
  rcases hz with rfl | rfl
  · simp
  · cases n with
    | zero => simp [ZMod.valMinAbs]
    | succ k =>
      rw [ZMod.valMinAbs_natAbs_eq_min]
      refine (min_le_left _ _).trans ?_
      simp only [Int.cast_one]
      rw [ZMod.val_one_eq_one_mod]
      exact Nat.mod_le _ _
private theorem cellSupDist_cellBond_le (Y : F.Cell) (i : Fin 4) (back : Bool) :
    cellSupDist (cellBond Y i back).1 Y ≤ 1 := by
  cases back with
  | false =>
    simp only [cellBond]
    simp [PatchLocality.cellSupDist_self]
  | true =>
    refine Finset.sup_le fun l _ => ?_
    have e : (cellBond Y i true).1 l - Y l =
        -(((Pi.single i 1 : Fin 4 → ℤ) l : ℤ) : ZMod (F.period F.top l)) := by
      simp only [cellBond, if_true, Pi.sub_apply, unitStep, siteOfCoords]
      ring
    show (((cellBond Y i true).1 l - Y l).valMinAbs).natAbs ≤ 1
    rw [e, ZMod.natAbs_valMinAbs_neg]
    refine natAbs_valMinAbs_le_one _ _ ?_
    by_cases hl : l = i
    · subst hl
      simp
    · simp [Pi.single_eq_of_ne hl]
private theorem blockIncrement_line (Q : ColdHalfLaw) (Y : F.Cell) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F))
    (b : ↥(chordBonds (finiteCells F))) (e : EuclideanSpace ℝ (Fin 3)) (τ : ℝ) :
    Q.blockIncrement Y (η + Pi.single b (τ • e)) V =
      cellEnergyShare Q.a Y (fun x' i => interpolatedCoords 1 Q.a Q.chartRadius Q.mirrorRadius V η x' i +
        τ • directionCoordinate (chordDirection b e) x' i) V -
        Q.blockCost Y 0 V := by
  unfold ColdHalfLaw.blockIncrement ColdHalfLaw.blockCost
  rw [interpolatedCoords_line]
open Classical in
private theorem weightedShareIncrement_line (Q : ColdHalfLaw) (wt : F.Site F.depth → ℝ) (Y : F.Cell)
    (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) (b : ↥(chordBonds (finiteCells F))) (e : EuclideanSpace ℝ (Fin 3))
    (τ : ℝ) :
    Q.weightedShareIncrement wt Y (η + Pi.single b (τ • e)) V =
      ∑ y ∈ (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y),
        wt y * (minimalSiteShare Q.a y (chartedField
        (fun x' i => interpolatedCoords 1 Q.a Q.chartRadius Q.mirrorRadius V η x' i +
          τ • directionCoordinate (chordDirection b e) x' i) V) -
        minimalSiteShare Q.a y (interpolatedField 1 Q.a Q.chartRadius Q.mirrorRadius V 0)) := by
  unfold ColdHalfLaw.weightedShareIncrement interpolatedField
  rw [interpolatedCoords_line]
private theorem bondGradNorm_blockIncrement_le {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} (hT : SmallnessConditions T)
    (hM : ChartShiftLipschitz)
    {x : ℝ} {f : LocalFamily} {V : F.GaugeField F.top} {Y : F.Cell} (hL : F.blockSide = T.L)
    (hs : InterpolatedFrameSmall 1 T.a T.chainParams.ρA T.chainParams.δ₂ T.Ct T.σ (frameRadius x) V)
    {c₁ C : ℝ} (hC0 : 0 ≤ C)
    (hc : c₁ ≤ C)
    (hk : ∀ w : F.Site F.depth → Fin 4 → imaginaryQuaternions,
      IsAdmissibleChartPoint T.L T.chainParams.σA w V → ∀ q : Fin 1 → ChartDirection F,
      AnalyticAt ℝ (cellEnergyAlong T.a Y w V q) 0 ∧ ((∀ l, ‖directionVector (q l)‖ = 1) →
        |cellEnergyKernel T.a Y w V q| ≤ c₁ * Real.exp (-(T.chainParams.δ₁ * directionReach Y q))))
    {η : StepVariable (finiteCells F)} (hη : ∀ b, ‖η b‖ < T.ballRadius)
    (hd : DifferentiableAt ℝ (fun ζ => (coldHalfLawAt T x f).blockIncrement Y ζ V) η)
    (b : ↥(chordBonds (finiteCells F))) :
    bondGradNorm (fun ζ => (coldHalfLawAt T x f).blockIncrement Y ζ V) b η ≤
      (C + 0 * (x * Real.sqrt (localSqNorm T.κ Y η))) * Real.exp (-(2 ^ 5 * T.κ * bondDistToCell Y b)) := by
  have hsp := isAdmissibleChartPoint_of_ball hT hM hL hs fun b => (hη b).le
  refine bondGradNorm_le_of_line_derivs (by rw [zero_mul, add_zero]; positivity) hd fun e he => ?_
  obtain ⟨D, hD, hDb⟩ := cellEnergyShare_hasDerivAt_line he (hk _ hsp _).1 (hk _ hsp _).2
  have e1 : (fun τ : ℝ => (coldHalfLawAt T x f).blockIncrement Y (η + Pi.single b (τ • e)) V) =
      fun τ : ℝ => cellEnergyShare T.a Y (fun x' i =>
        interpolatedCoords 1 T.a T.chainParams.ρA (frameRadius x) V η x' i +
        τ • directionCoordinate (chordDirection b e) x' i) V - (coldHalfLawAt T x f).blockCost Y 0 V := by
    funext τ
    exact blockIncrement_line _ Y V η b e τ
  rw [e1, (hD.sub_const _).deriv, zero_mul, add_zero]
  exact hDb.trans (mul_le_mul hc (exp_decay_bondDist hT Y b) (Real.exp_pos _).le hC0)
open Classical in
private theorem bondGradNorm_weightedShareIncrement_le {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} (hT : SmallnessConditions T)
    (hM : ChartShiftLipschitz)
    {x : ℝ} {f : LocalFamily} {V : F.GaugeField F.top} {Y : F.Cell} (hL : F.blockSide = T.L)
    (hs : InterpolatedFrameSmall 1 T.a T.chainParams.ρA T.chainParams.δ₂ T.Ct T.σ (frameRadius x) V)
    {c₂ C N B : ℝ} (hc₂ : 0 ≤ c₂)
    (hC0 : 0 ≤ C)
    (hN : (((sitesOfCells (finiteCells F) F.depth).filter fun y => enclosingCell y = Y).card : ℝ) ≤ N)
    (hc : N * c₂ ≤ C) (hB : 0 < B) {wt : F.Site F.depth → ℝ} (hw : ∀ y, |wt y| ≤ B)
    (hk : ∀ w : F.Site F.depth → Fin 4 → imaginaryQuaternions,
      IsAdmissibleChartPoint T.L T.chainParams.σA w V → ∀ (y : F.Site F.depth)
      (q : Fin 1 → ChartDirection F), AnalyticAt ℝ (siteShareAlong T.a y w V q) 0 ∧
        ((∀ l, ‖directionVector (q l)‖ = 1) →
        |siteShareMixedDeriv T.a y w V q| ≤
          c₂ * Real.exp (-(T.chainParams.δ₁ * directionReach (enclosingCell y) q))))
    {η : StepVariable (finiteCells F)} (hη : ∀ b, ‖η b‖ < T.ballRadius)
    (hd : DifferentiableAt ℝ (fun ζ => (coldHalfLawAt T x f).weightedShareIncrement wt Y ζ V) η)
    (b : ↥(chordBonds (finiteCells F))) :
    bondGradNorm (fun ζ => (coldHalfLawAt T x f).weightedShareIncrement wt Y ζ V) b η ≤
      (C * B + 0 * (x * Real.sqrt (localSqNorm T.κ Y η))) *
        Real.exp (-(2 ^ 5 * T.κ * bondDistToCell Y b)) := by
  have hsp := isAdmissibleChartPoint_of_ball hT hM hL hs fun b => (hη b).le
  refine bondGradNorm_le_of_line_derivs (by rw [zero_mul, add_zero]; positivity) hd fun e he => ?_
  choose D hD hDb using fun y : F.Site F.depth =>
    minimalSiteShare_hasDerivAt_line (b := b) he (hk _ hsp y _).1 (hk _ hsp y _).2
  set S := (sitesOfCells (finiteCells F) F.depth).filter fun y => enclosingCell y = Y with hS
  have e1 : (fun τ : ℝ => (coldHalfLawAt T x f).weightedShareIncrement wt Y (η + Pi.single b (τ • e)) V) =
      fun τ : ℝ => ∑ y ∈ S, wt y * (minimalSiteShare T.a y (chartedField
        (fun x' i => interpolatedCoords 1 T.a T.chainParams.ρA (frameRadius x) V η x' i +
          τ • directionCoordinate (chordDirection b e) x' i) V) -
        minimalSiteShare T.a y (interpolatedField 1 T.a T.chainParams.ρA (frameRadius x) V 0)) := by
    funext τ
    exact weightedShareIncrement_line _ wt Y V η b e τ
  have hsum : HasDerivAt (fun τ : ℝ => ∑ y ∈ S, wt y * (minimalSiteShare T.a y (chartedField
        (fun x' i => interpolatedCoords 1 T.a T.chainParams.ρA (frameRadius x) V η x' i +
          τ • directionCoordinate (chordDirection b e) x' i) V) -
        minimalSiteShare T.a y (interpolatedField 1 T.a T.chainParams.ρA (frameRadius x) V 0)))
      (∑ y ∈ S, wt y * D y) 0 :=
    HasDerivAt.fun_sum fun y _ => ((hD y).sub_const _).const_mul (wt y)
  rw [e1, hsum.deriv, zero_mul, add_zero]
  set E := Real.exp (-(2 ^ 5 * T.κ * bondDistToCell Y b)) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hterm : ∀ y ∈ S, |wt y * D y| ≤ B * (c₂ * E) := by
    intro y hy
    have hy' : enclosingCell y = Y := (Finset.mem_filter.mp hy).2
    have h1 := hDb y
    rw [hy'] at h1
    rw [abs_mul]
    refine mul_le_mul (hw y) (h1.trans ?_) (abs_nonneg _) hB.le
    exact mul_le_mul_of_nonneg_left (exp_decay_bondDist hT Y b) hc₂
  have h2 : |∑ y ∈ S, wt y * D y| ≤ S.card • (B * (c₂ * E)) :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_card_nsmul _ _ _ hterm)
  rw [nsmul_eq_mul] at h2
  have h3 : 0 ≤ B * (c₂ * E) := by positivity
  refine h2.trans ((mul_le_mul_of_nonneg_right hN h3).trans ?_)
  have h4 := mul_le_mul_of_nonneg_right hc (mul_nonneg hB.le hE0)
  nlinarith
private theorem bondGradNorm_scoreRemainderIncrement_le {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} (hT : SmallnessConditions T)
    (hM : ChartShiftLipschitz)
    {x : ℝ} {f : LocalFamily} {V : F.GaugeField F.top} {Y : F.Cell} {i : Fin 4} {back : Bool}
    (hL : F.blockSide = T.L)
    (hs : InterpolatedFrameSmall 1 T.a T.chainParams.ρA T.chainParams.δ₂ T.Ct T.σ (frameRadius x) V)
    {Mt D₁ C : ℝ} (hMt : 0 ≤ Mt)
    (hD₁ : 0 ≤ D₁) (hc : Mt * D₁ * Real.exp (2 ^ 5 * T.κ) ≤ C)
    (hLip : ∀ {r r' : ℝ}, r ∈ Set.Icc (1 / 2 : ℝ) 1 → r' ∈ Set.Icc (1 / 2 : ℝ) 1 →
      |(coldHalfLawAt T x f).scoreRemainder r - (coldHalfLawAt T x f).scoreRemainder r'| ≤ Mt * |r - r'|)
    {η : StepVariable (finiteCells F)} (hη : ∀ b, ‖η b‖ < T.ballRadius)
    (hk : ∀ (b : ↥(chordBonds (finiteCells F))) (e : EuclideanSpace ℝ (Fin 3)), ‖e‖ = 1 →
      ∃ D, HasDerivAt (fun τ : ℝ => logContourNorm 1 T.a T.chainParams.ρA (frameRadius x) (cellBond Y i back)
          (η + Pi.single b (τ • e)) V) D 0 ∧
        |D| ≤ D₁ * Real.exp (-(2 ^ 8 * T.κ *
          cellSetDiameter ({(cellBond Y i back).1} ∪ {enclosingCell b.1.1}))))
    (hd : DifferentiableAt ℝ
      (fun ζ => (coldHalfLawAt T x f).scoreRemainderIncrement (cellBond Y i back) ζ V) η)
    (b : ↥(chordBonds (finiteCells F))) :
    bondGradNorm (fun ζ => (coldHalfLawAt T x f).scoreRemainderIncrement (cellBond Y i back) ζ V) b η ≤
      (C + 0 * (x * Real.sqrt (localSqNorm T.κ Y η))) * Real.exp (-(2 ^ 5 * T.κ * bondDistToCell Y b)) := by
  have hC0 : 0 ≤ C := le_trans (by positivity) hc
  refine bondGradNorm_le_of_line_derivs (by rw [zero_mul, add_zero]; positivity) hd fun e he => ?_
  obtain ⟨D, hD, hDb⟩ := hk b e he
  set c := cellBond Y i back with hcdef
  set line : ℝ → StepVariable (finiteCells F) := fun τ => η + Pi.single b (τ • e) with hline
  set r : ℝ → ℝ := fun τ =>
    ‖_root_.YangMills.Construction.BlockAverages.contourAverage (interpolatedField 1 T.a T.chainParams.ρA (frameRadius x) V (line τ)) c‖ with hr
  have hopen : IsOpen {ζ : StepVariable (finiteCells F) | ∀ b, ‖ζ b‖ < T.ballRadius} := by
    rw [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun b => isOpen_lt (by fun_prop) continuous_const
  have hl0 : line 0 = η := by simp [hline]
  have hlc : ContinuousAt line 0 := by
    have e1 : line = fun τ : ℝ => η + τ • (Pi.single b e : StepVariable (finiteCells F)) := by
      funext τ
      simp only [hline]
      rw [Pi.single_smul]
    rw [e1]
    fun_prop
  have hev : ∀ᶠ τ in 𝓝 (0 : ℝ),
      line τ ∈ {ζ : StepVariable (finiteCells F) | ∀ b, ‖ζ b‖ < T.ballRadius} :=
    hlc.eventually_mem (by rw [hl0]; exact hopen.mem_nhds hη)
  have hrI : ∀ᶠ τ in 𝓝 (0 : ℝ), r τ ∈ Set.Icc (1 / 2 : ℝ) 1 :=
    hev.mono fun τ h => norm_contourAverage_interpolated hT hM hL hs c fun b' => (h b').le
  have hr0 := hrI.self_of_nhds
  have hre : r =ᶠ[𝓝 0] fun τ => Real.exp (Real.log (r τ)) := hrI.mono fun τ h => by
    show r τ = Real.exp (Real.log (r τ))
    rw [Real.exp_log (by linarith [h.1])]
  have hrd : HasDerivAt r (Real.exp (Real.log (r 0)) * D) 0 := by
    have h1 : HasDerivAt (fun τ => Real.log (r τ)) D 0 := hD
    exact h1.exp.congr_of_eventuallyEq hre
  have hφ : HasDerivAt (fun τ : ℝ => (coldHalfLawAt T x f).scoreRemainderIncrement c (line τ) V) _ 0 :=
    hasDerivAt_bondPartialDeriv hd b e
  have hrate := abs_deriv_le_of_abs_sub_le (M := Mt) hφ hrd (by
    filter_upwards [hrI] with τ hτ
    have e2 : ∀ u : ℝ, (coldHalfLawAt T x f).scoreRemainderIncrement c (line u) V =
        (coldHalfLawAt T x f).scoreRemainder (r u) - (coldHalfLawAt T x f).scoreRemainderAt c 0 V :=
      fun _ => rfl
    rw [e2, e2, sub_sub_sub_cancel_right]
    exact hLip hτ hr0)
  have hφ' : deriv (fun τ : ℝ => (coldHalfLawAt T x f).scoreRemainderIncrement c
      (η + Pi.single b (τ • e)) V) 0 =
      bondPartialDeriv (fun ζ => (coldHalfLawAt T x f).scoreRemainderIncrement c ζ V) b η e := hφ.deriv
  rw [hφ', zero_mul, add_zero]
  have h4 : |Real.exp (Real.log (r 0)) * D| ≤ |D| := by
    rw [Real.exp_log (by linarith [hr0.1]), abs_mul, abs_of_nonneg (by linarith [hr0.1])]
    have := abs_nonneg D
    nlinarith [hr0.2]
  set s := cellSetDiameter ({c.1} ∪ {enclosingCell b.1.1} : Finset F.Cell) with hsdef
  have h5 : cellSupDist (enclosingCell b.1.1) Y ≤ s + 1 := by
    have h6 : cellSupDist (enclosingCell b.1.1) c.1 ≤ s :=
      cellSupDist_le_diameter _ _ _ (by simp) (by simp)
    have h7 : cellSupDist c.1 Y ≤ 1 := cellSupDist_cellBond_le Y i back
    have h8 := PatchLocality.cellSupDist_triangle (enclosingCell b.1.1) c.1 Y
    omega
  have h9 := exp_decay_near hT.κ_pos h5
  have hDb' : |D| ≤ D₁ * (Real.exp (2 ^ 5 * T.κ) * Real.exp (-(2 ^ 5 * T.κ * bondDistToCell Y b))) :=
    hDb.trans (mul_le_mul_of_nonneg_left h9 hD₁)
  calc _ ≤ Mt * |Real.exp (Real.log (r 0)) * D| := hrate
    _ ≤ Mt * |D| := mul_le_mul_of_nonneg_left h4 hMt
    _ ≤ Mt * (D₁ * (Real.exp (2 ^ 5 * T.κ) * Real.exp (-(2 ^ 5 * T.κ * bondDistToCell Y b)))) :=
      mul_le_mul_of_nonneg_left hDb' hMt
    _ = Mt * D₁ * Real.exp (2 ^ 5 * T.κ) * Real.exp (-(2 ^ 5 * T.κ * bondDistToCell Y b)) := by ring
    _ ≤ C * Real.exp (-(2 ^ 5 * T.κ * bondDistToCell Y b)) :=
      mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le
open Classical in
private theorem linearBlockPart_eq (Q : ColdHalfLaw) (Y : F.Cell) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) :
    Q.linearBlockPart Y η V = interpolatedBlockExponent 1 Q.a Q.chartRadius Q.coupling Q.mirrorRadius Y V η +
      (∑ c ∈ (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y),
        (contourHaarGap 1 Q.a Q.chartRadius Q.coupling Q.mirrorRadius c η V - haarGap (Q.a * Q.coupling))) +
      ∑ b : ↥(chordBonds (finiteCells F)), if enclosingCell b.1.1 = Y then
        interpolatedHaarLogRatio 1 Q.a Q.chartRadius Q.mirrorRadius b η V else 0 := by
  simp only [ColdHalfLaw.linearBlockPart, interpolatedBlockExponent, contourHaarGap, interpolatedHaarLogRatio,
    haarGapExcess]
  ring
private theorem bondDeriv_zero_order (G : F.GaugeField F.top → ℝ) (V : F.GaugeField F.top)
    (c : Fin 0 → F.Site F.top × Fin 4)
    (X : Fin 0 → imaginaryQuaternions) : bondDeriv G V c X = G V := by apply _root_.YangMills.SharedProofs.p1654 <;> assumption
private theorem cellSupDist_le_bondSpanWithCell (Y z : F.Cell) (c : Fin 0 → F.Site F.top × Fin 4) :
    cellSupDist Y z ≤ bondSpanWithCell Y z c := by
  unfold bondSpanWithCell bondSpan
  refine le_max_of_le_left ?_
  exact Finset.le_sup (f := fun l : Fin (0 + 1) =>
    siteSupDist Y ((Fin.cons (z, 0) c : Fin (0 + 1) → F.Site F.top × Fin 4) l).1) (Finset.mem_univ 0)
private theorem interpolatedHaarLogRatio_const (s a ρA : ℝ) (m : ℕ) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F))
    {b b₀ : ↥(chordBonds (finiteCells F))} (hb : b₀ ≠ b) (e : EuclideanSpace ℝ (Fin 3)) (τ : ℝ) :
    interpolatedHaarLogRatio s a ρA m b₀ (η + Pi.single b (τ • e)) V =
      interpolatedHaarLogRatio s a ρA m b₀ η V := by
  unfold interpolatedHaarLogRatio
  rw [interpolatedCoords_line]
  have h : directionCoordinate (chordDirection b e) b₀.1.1 b₀.1.2 = 0 := by
    simp only [directionCoordinate, chordDirection]
    rw [if_neg]
    intro h
    exact hb (Subtype.ext (Prod.ext h.1.symm h.2.symm))
  simp [h]
open Classical in
private theorem bondGradNorm_linearBlockPart_le {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} (hT : SmallnessConditions T) {x : ℝ}
    {f : LocalFamily} {V : F.GaugeField F.top}
    {Y : F.Cell} (hx : 0 < x)
    (hexp : InterpolatedExponentBounds 1 T.a T.chainParams.ρA T.ballRadius x T.κ T.Cs (frameRadius x) V)
    (hparts : InterpolatedPartsSmooth 1 T.a T.chainParams.ρA T.ballRadius x (frameRadius x) V)
    {D₁ C : ℝ} (hD₁ : 0 ≤ D₁)
    (hc : |T.Cs| + 5 * D₁ ≤ C) {η : StepVariable (finiteCells F)} (hη : ∀ b, ‖η b‖ < T.ballRadius)
    (hgap : ∀ (c : F.Site F.top × Fin 4) (b : ↥(chordBonds (finiteCells F))) (e : EuclideanSpace ℝ (Fin 3)),
      ‖e‖ = 1 →
      ∃ D, HasDerivAt (fun τ : ℝ => contourHaarGap 1 T.a T.chainParams.ρA x (frameRadius x) c
          (η + Pi.single b (τ • e)) V) D 0 ∧
        |D| ≤ D₁ * Real.exp (-(2 ^ 8 * T.κ * cellSetDiameter ({c.1} ∪ {enclosingCell b.1.1}))))
    (hhaar : ∀ (b : ↥(chordBonds (finiteCells F))) (e : EuclideanSpace ℝ (Fin 3)), ‖e‖ = 1 →
      ∃ D, HasDerivAt (fun τ : ℝ => interpolatedHaarLogRatio 1 T.a T.chainParams.ρA (frameRadius x) b
          (η + Pi.single b (τ • e)) V) D 0 ∧
        |D| ≤ D₁ * Real.exp (-(2 ^ 8 * T.κ *
          cellSetDiameter ({enclosingCell b.1.1} ∪ {enclosingCell b.1.1}))))
    (hd : DifferentiableAt ℝ (fun ζ => (coldHalfLawAt T x f).linearBlockPart Y ζ V) η)
    (b : ↥(chordBonds (finiteCells F))) :
    bondGradNorm (fun ζ => (coldHalfLawAt T x f).linearBlockPart Y ζ V) b η ≤
      (C + C * (x * Real.sqrt (localSqNorm T.κ Y η))) * Real.exp (-(2 ^ 5 * T.κ * bondDistToCell Y b)) := by
  have hC0 : 0 ≤ C := le_trans (by positivity) hc
  have hκ := hT.κ_pos
  set w := x * Real.sqrt (localSqNorm T.κ Y η) with hw
  have hw0 : 0 ≤ w := by positivity
  have hcl : ∀ b, ‖η b‖ ≤ T.ballRadius := fun b => (hη b).le
  refine bondGradNorm_le_of_line_derivs (by positivity) hd fun e he => ?_
  set Ee := Real.exp (-(2 ^ 5 * T.κ * bondDistToCell Y b)) with hEe
  have hE0 : 0 ≤ Ee := (Real.exp_pos _).le
  have hdE : DifferentiableAt ℝ
      (fun ζ => interpolatedBlockExponent 1 T.a T.chainParams.ρA x (frameRadius x) Y V ζ) η :=
    (contDiffAt_of_joint
      (K := fun ζ V' => interpolatedBlockExponent 1 T.a T.chainParams.ρA x (frameRadius x) Y V' ζ)
      (hparts.smooth Y η 0 Fin.elim0 Fin.elim0 hcl)).differentiableAt (by norm_num)
  have hE := hasDerivAt_bondPartialDeriv hdE b e
  have hEb : |bondPartialDeriv (fun ζ => interpolatedBlockExponent 1 T.a T.chainParams.ρA x (frameRadius x)
      Y V ζ) b η e| ≤ |T.Cs| * (w + 1) * Ee := by
    have h1 := hexp.deriv_top_partial Y η b e 0 Fin.elim0 Fin.elim0 hη (by norm_num) (fun l => l.elim0) he
    rw [bondDeriv_zero_order] at h1
    refine h1.trans ?_
    have h2 : Real.exp (-(2 ^ 6 * T.κ * bondSpanWithCell Y (enclosingCell b.1.1)
        (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4))) ≤ Ee := by
      refine Real.exp_le_exp.2 ?_
      have h3 : (cellSupDist (enclosingCell b.1.1) Y : ℝ) ≤
          bondSpanWithCell Y (enclosingCell b.1.1) (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) := by
        rw [PatchLocality.cellSupDist_comm]
        exact_mod_cast cellSupDist_le_bondSpanWithCell Y _ _
      have h4 := mul_le_mul_of_nonneg_left h3 hκ.le
      have h5 : (0 : ℝ) ≤ T.κ * bondSpanWithCell Y (enclosingCell b.1.1)
          (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) := by
        positivity
      unfold bondDistToCell
      nlinarith
    have h6 : T.Cs ≤ |T.Cs| := le_abs_self _
    calc T.Cs * (w + 1) * _ ≤ |T.Cs| * (w + 1) * Real.exp (-(2 ^ 6 * T.κ *
          bondSpanWithCell Y (enclosingCell b.1.1) (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4))) := by gcongr
      _ ≤ |T.Cs| * (w + 1) * Ee := by gcongr
  choose Dg hDg hDgb using fun c => hgap c b e he
  set S := (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y) with hS
  have hGs : HasDerivAt (fun τ : ℝ => ∑ c ∈ S, (contourHaarGap 1 T.a T.chainParams.ρA x (frameRadius x) c
      (η + Pi.single b (τ • e)) V - haarGap (T.a * x))) (∑ c ∈ S, Dg c) 0 :=
    HasDerivAt.fun_sum fun c _ => (hDg c).sub_const _
  have hcard : (S.card : ℝ) ≤ 4 := by
    have h1 : S.card ≤ (Finset.univ : Finset (Fin 4)).card :=
      Finset.card_le_card_of_injOn (fun c => c.2) (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
        fun c hc c' hc' h =>
          Prod.ext (((Finset.mem_filter.mp hc).2).trans ((Finset.mem_filter.mp hc').2).symm) h
    have h2 : S.card ≤ 4 := by simpa using h1
    exact_mod_cast h2
  have hGb : |∑ c ∈ S, Dg c| ≤ 4 * (D₁ * Ee) := by
    have hterm : ∀ c ∈ S, |Dg c| ≤ D₁ * Ee := by
      intro c hc
      have hY : c.1 = Y := (Finset.mem_filter.mp hc).2
      refine (hDgb c).trans (mul_le_mul_of_nonneg_left ?_ hD₁)
      exact exp_decay_diameter hκ (cellSupDist_le_diameter _ _ _ (by simp) (by simp [hY]))
    have h1 : |∑ c ∈ S, Dg c| ≤ S.card • (D₁ * Ee) :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_card_nsmul _ _ _ hterm)
    rw [nsmul_eq_mul] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right hcard (by positivity))
  obtain ⟨Dh, hDh, hDhb⟩ := hhaar b e he
  have hterm : ∀ b₀ : ↥(chordBonds (finiteCells F)), HasDerivAt (fun τ : ℝ =>
      if enclosingCell b₀.1.1 = Y then
        interpolatedHaarLogRatio 1 T.a T.chainParams.ρA (frameRadius x) b₀ (η + Pi.single b (τ • e)) V else 0)
      (if b₀ = b then (if enclosingCell b.1.1 = Y then Dh else 0) else 0) 0 := by
    intro b₀
    by_cases hb : b₀ = b
    · subst hb
      rw [if_pos rfl]
      by_cases hY : enclosingCell b₀.1.1 = Y
      · simp only [if_pos hY]
        exact hDh
      · simp only [if_neg hY]
        exact hasDerivAt_const _ _
    · rw [if_neg hb]
      have e2 : (fun τ : ℝ => if enclosingCell b₀.1.1 = Y then
          interpolatedHaarLogRatio 1 T.a T.chainParams.ρA (frameRadius x) b₀ (η + Pi.single b (τ • e)) V
            else 0) =
          fun _ => if enclosingCell b₀.1.1 = Y then
            interpolatedHaarLogRatio 1 T.a T.chainParams.ρA (frameRadius x) b₀ η V else 0 := by
        funext τ
        rw [interpolatedHaarLogRatio_const _ _ _ _ _ _ hb]
      rw [e2]
      exact hasDerivAt_const _ _
  have hHs := HasDerivAt.fun_sum (u := (Finset.univ : Finset ↥(chordBonds (finiteCells F))))
    fun b₀ _ => hterm b₀
  have hHe : ∑ b₀ : ↥(chordBonds (finiteCells F)),
      (if b₀ = b then (if enclosingCell b.1.1 = Y then Dh else 0) else 0) =
      if enclosingCell b.1.1 = Y then Dh else 0 := by
    rw [Finset.sum_ite_eq' Finset.univ b]
    simp
  rw [hHe] at hHs
  have hHb : |if enclosingCell b.1.1 = Y then Dh else 0| ≤ D₁ * Ee := by
    by_cases hY : enclosingCell b.1.1 = Y
    · rw [if_pos hY]
      refine hDhb.trans (mul_le_mul_of_nonneg_left ?_ hD₁)
      exact exp_decay_diameter hκ (cellSupDist_le_diameter _ _ _ (by simp) (by simp [hY]))
    · rw [if_neg hY, abs_zero]
      positivity
  have e1 : (fun τ : ℝ => (coldHalfLawAt T x f).linearBlockPart Y (η + Pi.single b (τ • e)) V) =
      fun τ : ℝ => interpolatedBlockExponent 1 T.a T.chainParams.ρA x (frameRadius x) Y V
          (η + Pi.single b (τ • e)) +
        (∑ c ∈ S, (contourHaarGap 1 T.a T.chainParams.ρA x (frameRadius x) c (η + Pi.single b (τ • e)) V -
          haarGap (T.a * x))) +
        ∑ b₀ : ↥(chordBonds (finiteCells F)), if enclosingCell b₀.1.1 = Y then
          interpolatedHaarLogRatio 1 T.a T.chainParams.ρA (frameRadius x) b₀ (η + Pi.single b (τ • e)) V
            else 0 := by
    funext τ
    exact linearBlockPart_eq _ Y V _
  rw [e1, ((hE.fun_add hGs).fun_add hHs).deriv]
  have h1 := abs_add_le (bondPartialDeriv (fun ζ => interpolatedBlockExponent 1 T.a T.chainParams.ρA x
    (frameRadius x) Y V ζ) b η e + ∑ c ∈ S, Dg c) (if enclosingCell b.1.1 = Y then Dh else 0)
  have h2 := abs_add_le (bondPartialDeriv (fun ζ => interpolatedBlockExponent 1 T.a T.chainParams.ρA x
    (frameRadius x) Y V ζ) b η e) (∑ c ∈ S, Dg c)
  have t1 : 0 ≤ (C - (|T.Cs| + 5 * D₁)) * Ee := mul_nonneg (sub_nonneg.2 hc) hE0
  have t2 : 0 ≤ (C - |T.Cs|) * w * Ee :=
    mul_nonneg (mul_nonneg (by linarith) hw0) hE0
  nlinarith
private theorem chartedSlope_zero (a : ℝ) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (V : F.GaugeField F.top) (b : F.Site F.depth × Fin 4) :
    chartedSlope a w V b (toImaginary (0 : EuclideanSpace ℝ (Fin 3))) = 0 := by
  unfold chartedSlope
  rw [toImaginary_zero]
  simp
private theorem linearBlockPart_zero (Q : ColdHalfLaw) (Y : F.Cell) (V : F.GaugeField F.top) :
    Q.linearBlockPart Y 0 V = 0 := by
  unfold ColdHalfLaw.linearBlockPart
  simp only [Pi.zero_apply, chartedSlope_zero, intervalIntegral.integral_zero, ite_self,
    Finset.sum_const_zero, mul_zero]
end SmoothIncrementBounds
open SmoothIncrementBounds in
theorem smoothIncrementBounds_holds (hS : SmoothIncrementsAreSlots) (hB : CellEnergyKernelBound)
    (hA : SiteShareKernelBound) (hK : interpolationKernelBoundsStatement) (hF : interpolatedFramesStatement)
    (hP : interpolatedPartsSmoothStatement) (hTl : ScoreRemainderExpansion)
    (hM : ChartShiftLipschitz) : smoothIncrementBounds := by
  obtain ⟨Cq, Cs', _, _, hSl⟩ := hS
  obtain ⟨Kf, Dk, _, hDk, hKt⟩ := hK
  obtain ⟨Cq', Cz, Cr, hFt⟩ := hF
  have exB : ∀ (a : ℝ) (L : ℕ) (c : ColdChainParameters), ∃ c₁ : ℝ, 1 ≤ a → Odd L → 2 ^ 40 ≤ L →
      c.Admissible a L →
      ∀ (F : BlockFrame) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top),
        IsBlockTorus L F →
        IsAdmissibleChartPoint L c.σA w V → ∀ (Y : F.Cell) (q : Fin 1 → ChartDirection F),
          AnalyticAt ℝ (cellEnergyAlong a Y w V q) 0 ∧ ((∀ l, ‖directionVector (q l)‖ = 1) →
            |cellEnergyKernel a Y w V q| ≤ c₁ * Real.exp (-(c.δ₁ * directionReach Y q))) := by
    intro a L c
    by_cases h : 1 ≤ a ∧ Odd L ∧ 2 ^ 40 ≤ L ∧ c.Admissible a L
    · obtain ⟨Ck, _, h1⟩ := hB a L c h.1 h.2.1 h.2.2.1 h.2.2.2
      exact ⟨Ck 1, fun _ _ _ _ F w V hc hp Y q =>
        ⟨(h1 F w V hc hp Y 1 q).1, (h1 F w V hc hp Y 1 q).2 le_rfl⟩⟩
    · exact ⟨0, fun h1 h2 h3 h4 => absurd ⟨h1, h2, h3, h4⟩ h⟩
  choose cB hcB using exB
  have exA : ∀ (a : ℝ) (L : ℕ) (c : ColdChainParameters), ∃ c₂ : ℝ, 0 ≤ c₂ ∧ (1 ≤ a → Odd L → 2 ^ 40 ≤ L →
      c.Admissible a L →
      ∀ (F : BlockFrame) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top),
        IsBlockTorus L F →
        IsAdmissibleChartPoint L c.σA w V → ∀ (y : F.Site F.depth) (q : Fin 1 → ChartDirection F),
          AnalyticAt ℝ (siteShareAlong a y w V q) 0 ∧ ((∀ l, ‖directionVector (q l)‖ = 1) →
            |siteShareMixedDeriv a y w V q| ≤ c₂ * Real.exp (-(c.δ₁ * directionReach (enclosingCell y) q)))) := by
    intro a L c
    by_cases h : 1 ≤ a ∧ Odd L ∧ 2 ^ 40 ≤ L ∧ c.Admissible a L
    · obtain ⟨Ck, hCk, h1⟩ := hA a L c h.1 h.2.1 h.2.2.1 h.2.2.2
      exact ⟨Ck 1, (hCk 1).le, fun _ _ _ _ F w V hc hp y q =>
        ⟨(h1 F w V hc hp y 1 q).1, (h1 F w V hc hp y 1 q).2 le_rfl⟩⟩
    · exact ⟨0, le_rfl, fun h1 h2 h3 h4 => absurd ⟨h1, h2, h3, h4⟩ h⟩
  choose cA hcA0 hcA using exA
  have exT : ∀ a : ℝ, ∃ M : ℝ, 0 ≤ M ∧ (1 ≤ a → ∀ Q : ColdHalfLaw, Q.a = a → 2 / a ≤ Q.coupling →
      ∀ {r r' : ℝ}, r ∈ Set.Icc (1 / 2 : ℝ) 1 → r' ∈ Set.Icc (1 / 2 : ℝ) 1 →
        |Q.scoreRemainder r - Q.scoreRemainder r'| ≤ M * |r - r'|) := by
    intro a
    by_cases h : 1 ≤ a
    · obtain ⟨M, h1⟩ := hTl.2 a h 1
      exact ⟨|M|, abs_nonneg _, fun _ Q hQ hx r r' hr hr' => scoreRemainder_lipschitz (h1 Q hQ hx).1
        (fun u hu => ((h1 Q hQ hx).2 u hu).trans (le_abs_self _)) hr hr'⟩
    · exact ⟨0, le_rfl, fun h1 => absurd h1 h⟩
  choose Mt hMt0 hMt using exT
  let C : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℝ := fun T => |cB T.a T.L T.chainParams| +
    (T.L : ℝ) ^ 4 * cA T.a T.L T.chainParams +
    Mt T.a * Dk (rateParameters T) 1 0 * Real.exp (2 ^ 5 * T.κ) + |T.Cs| + 5 * Dk (rateParameters T) 1 0
  have hC0 : ∀ T, 0 ≤ C T := by
    intro T
    have h1 := hcA0 T.a T.L T.chainParams
    have h2 := hMt0 T.a
    have h3 := (hDk (rateParameters T) 1 0).le
    simp only [C]
    positivity
  refine ⟨C, hC0, ?_⟩
  refine (eventually_smallnessConditions.and (hSl.and (hKt.and (hFt.and hP)))).mono fun T hall => ?_
  obtain ⟨hT, hsl, hkt, hft, hp⟩ := hall
  have hCT : C (parametersBeforeSide T) = C T := rfl
  rw [hCT]
  intro t x f F V Y hst hrow
  have hL : F.blockSide = T.L := hst.torus.1
  have hodd : Odd F.blockSide := hL ▸ hT.odd_L
  obtain ⟨n, hn, hn0⟩ := hst.torus.2.2
  have hn64 : 64 ≤ n := hT.n₀_large.trans hn0
  have hchain : IsBlockTorus T.L F := ⟨hL, n, hn64, hn⟩
  have hside : ∀ i, 2 ≤ F.extent i := fun i => by
    rw [hn i]
    omega
  have hx2 : 2 ≤ x := hT.coupling_large.trans hst.coupling_le
  have hx0 : 0 < x := by linarith
  have hone := (hft t x hst.coupling_le).one_torus F V 1 hst.torus hst.small_curvature zero_le_one le_rfl
  have hparts := hp t x F V 1 hst.coupling_le hst.torus hst.small_curvature zero_le_one le_rfl
  have hker : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ T.ballRadius) →
      HasInterpolationKernels 1 T.a T.chainParams.ρA T.κ T.chainParams.κ₂ T.chainParams.δ₂ x (frameRadius x)
        (Kf (rateParameters T)) (Dk (rateParameters T)) V η :=
    fun η hη => hkt x t F V 1 η hst.coupling_le hst.torus hst.small_curvature zero_le_one le_rfl hη
  obtain ⟨sBlock, sSlope, sScore, sWeight⟩ := hsl t x f F V Y hst hrow
  have hd1 : 0 ≤ Dk (rateParameters T) 1 0 := (hDk _ 1 0).le
  have hca := hcA0 T.a T.L T.chainParams
  have hmt := hMt0 T.a
  have n1 : 0 ≤ (T.L : ℝ) ^ 4 * cA T.a T.L T.chainParams := by positivity
  have n2 : 0 ≤ Mt T.a * Dk (rateParameters T) 1 0 * Real.exp (2 ^ 5 * T.κ) := by positivity
  have n3 := abs_nonneg T.Cs
  have n4 := abs_nonneg (cB T.a T.L T.chainParams)
  have n5 := le_abs_self (cB T.a T.L T.chainParams)
  have hCe : C T = |cB T.a T.L T.chainParams| + (T.L : ℝ) ^ 4 * cA T.a T.L T.chainParams +
    Mt T.a * Dk (rateParameters T) 1 0 * Real.exp (2 ^ 5 * T.κ) + |T.Cs| +
      5 * Dk (rateParameters T) 1 0 := rfl
  have hC := hC0 T
  refine ⟨?_, ?_, fun i back => ?_, fun wt B hB hw => ?_⟩
  · refine isVanishingMove_of_slot sBlock (sub_self _) fun η hη hd b => ?_
    exact bondGradNorm_blockIncrement_le hT hM hL hone.small hC (by rw [hCe]; linarith)
      (fun w hp q => hcB T.a T.L T.chainParams hT.one_le_a hT.odd_L hT.big_L hT.admissible F w V hchain hp Y q)
      hη hd b
  · refine isVanishingMove_of_slot sSlope (linearBlockPart_zero _ Y V) fun η hη hd b => ?_
    have hk := hker η fun b => (hη b).le
    exact bondGradNorm_linearBlockPart_le hT hx0 hone.exponent hparts hd1 (by rw [hCe]; linarith) hη
      (fun c b e he => hasDerivAt_line_of_kernel (hk.gap c 1 0 (fun _ => b) (fun _ => e) Fin.elim0 Fin.elim0
        (by norm_num) (fun _ => he) (fun l => l.elim0)))
      (fun b e he => hasDerivAt_line_of_kernel (hk.haar b 1 0 (fun _ => b) (fun _ => e) Fin.elim0 Fin.elim0
        (by norm_num) (fun _ => he) (fun l => l.elim0))) hd b
  · refine isVanishingMove_of_slot (sScore i back) (sub_self _) fun η hη hd b => ?_
    have hk := hker η fun b => (hη b).le
    have h2a : 2 / T.a ≤ x := (div_le_self (by norm_num) hT.one_le_a).trans hx2
    exact bondGradNorm_scoreRemainderIncrement_le hT hM hL hone.small hmt hd1 (by rw [hCe]; linarith)
      (fun hr hr' => hMt T.a hT.one_le_a (coldHalfLawAt T x f) rfl h2a hr hr') hη
      (fun b e he => hasDerivAt_line_of_kernel (hk.logContour _ 1 0 (fun _ => b) (fun _ => e) Fin.elim0
        Fin.elim0 (by norm_num) (fun _ => he) (fun l => l.elim0))) hd b
  · have hN := card_sites_in_cell_le hodd hside Y
    rw [hL] at hN
    refine isVanishingMove_of_slot (sWeight wt B hB hw) ?_ fun η hη hd b => ?_
    · unfold ColdHalfLaw.weightedShareIncrement
      simp
    · exact bondGradNorm_weightedShareIncrement_le hT hM hL hone.small hca hC hN (by rw [hCe]; linarith) hB hw
        (fun w hp y q => hcA T.a T.L T.chainParams hT.one_le_a hT.odd_L hT.big_L hT.admissible F w V hchain hp
          y q) hη hd b
end ResponseInTheExpansion
end YangMills.Construction
end
