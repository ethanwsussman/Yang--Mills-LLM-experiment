import YangMills.Construction.ClusterExpansionOfAStep.PlainFitsOfNearFieldsProof
import YangMills.Construction.ColdStepAtMirrorFrames.FramesAgainstTheLeastField
import YangMills.Construction.RunningCouplingSlope.LeastActionIsWellAtTheTopProof
import YangMills.Construction.SummableBoundsOfTheFlow.ExponentBetweenBoundsProof
import YangMills.Construction.SummableBoundsOfTheFlow.SlopeBetweenComparesOnTwoToriProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.Interpolation
open BlockAverages hiding bondSpread
open ColdStepAtMirrorFrames
variable {F : BlockFrame}
instance : CompleteSpace imaginaryQuaternions := FiniteDimensional.complete ℝ imaginaryQuaternions
private theorem contDiffAt_of_bondAnalytic {G : F.GaugeField F.top → imaginaryQuaternions}
    {V : F.GaugeField F.top} (hG : IsBondAnalyticAt G V)
    {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) :
    ContDiffAt ℝ k (fun τ : Fin k → ℝ => G (leftTranslate (bondSpread c X τ) V)) 0 :=
  (hG k c X).contDiffAt
private theorem bondDeriv_linear_comb {G H : F.GaugeField F.top → imaginaryQuaternions}
    {V : F.GaugeField F.top} (α β : ℝ)
    (hG : IsBondAnalyticAt G V) (hH : IsBondAnalyticAt H V) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) :
    bondDeriv (fun V' => α • G V' + β • H V') V c X = α • bondDeriv G V c X + β • bondDeriv H V c X := by
  unfold bondDeriv
  have hG' := contDiffAt_of_bondAnalytic hG c X
  have hH' := contDiffAt_of_bondAnalytic hH c X
  have e : (fun τ : Fin k → ℝ => α • G (leftTranslate (bondSpread c X τ) V) + β • H (leftTranslate (bondSpread c X τ) V)) =
      (α • fun τ : Fin k → ℝ => G (leftTranslate (bondSpread c X τ) V)) +
        (β • fun τ : Fin k → ℝ => H (leftTranslate (bondSpread c X τ) V)) := rfl
  have hGα : ContDiffAt ℝ k (α • fun τ : Fin k → ℝ => G (leftTranslate (bondSpread c X τ) V)) 0 := hG'.const_smul α
  have hHβ : ContDiffAt ℝ k (β • fun τ : Fin k → ℝ => H (leftTranslate (bondSpread c X τ) V)) 0 := hH'.const_smul β
  rw [e, iteratedFDeriv_add_apply hGα hHβ,
    iteratedFDeriv_const_smul_apply hG', iteratedFDeriv_const_smul_apply hH']
  rfl
private theorem bondAnalytic_linear_comb {G H : F.GaugeField F.top → imaginaryQuaternions}
    {V : F.GaugeField F.top} (α β : ℝ)
    (hG : IsBondAnalyticAt G V) (hH : IsBondAnalyticAt H V) :
    IsBondAnalyticAt (fun V' => α • G V' + β • H V') V := fun k c X =>
  ((hG k c X).const_smul (c := α)).add ((hH k c X).const_smul (c := β))
private theorem bondDeriv_coe {G : F.GaugeField F.top → imaginaryQuaternions} {V : F.GaugeField F.top}
    (hG : IsBondAnalyticAt G V) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) :
    bondDeriv (fun V' => (G V' : ℍ[ℝ])) V c X = ((bondDeriv G V c X : imaginaryQuaternions) : ℍ[ℝ]) := by
  unfold bondDeriv
  have hG' := contDiffAt_of_bondAnalytic hG c X
  have e := (imaginaryQuaternions.subtypeL).iteratedFDeriv_comp_left hG' (i := k) le_rfl
  have e2 : (fun τ : Fin k → ℝ => ((G (leftTranslate (bondSpread c X τ) V) : imaginaryQuaternions) : ℍ[ℝ])) =
      (imaginaryQuaternions.subtypeL) ∘ (fun τ : Fin k → ℝ => G (leftTranslate (bondSpread c X τ) V)) := rfl
  rw [e2, e]
  rfl
private theorem stepFrame_eq_of_small_extent (a ρ : ℝ) (m : ℕ) (h : ¬ ∀ i, 4 * m + 5 < F.extent i)
    (b : F.Site F.depth × Fin 4) (V : F.GaugeField F.top) :
    stepFrame false a ρ m b V = stepFrame true a ρ m b V := by
  simp [stepFrame, bondFrameCoord, h]
private theorem interpolatedFrame_sub (s a ρ : ℝ) (m : ℕ) (b : F.Site F.depth × Fin 4) (V : F.GaugeField F.top) :
    interpolatedFrame s a ρ m b V - stepFrame true a ρ m b V = s • frameGap a ρ m b V := by
  simp only [interpolatedFrame, frameGap]
  module
private theorem norm_convex_comb_le {u v : imaginaryQuaternions} {s B : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1)
    (hu : ‖u‖ ≤ B) (hv : ‖v‖ ≤ B) :
    ‖(1 - s) • u + s • v‖ ≤ B := by
  calc ‖(1 - s) • u + s • v‖ ≤ ‖(1 - s) • u‖ + ‖s • v‖ := norm_add_le _ _
    _ = (1 - s) * ‖u‖ + s * ‖v‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg h0]
    _ ≤ (1 - s) * B + s * B := by gcongr
    _ = B := by ring
private theorem norm_toImaginary (v : EuclideanSpace ℝ (Fin 3)) : ‖toImaginary v‖ = ‖v‖ := by apply _root_.YangMills.Construction.Interpolation.ExponentBoundSteps.norm_toImaginary <;> assumption
private theorem norm_stepCoordinates_le {S : Finset F.Cell} (η : StepVariable S) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ b, ‖η b‖ ≤ B) (x : F.Site F.depth) (i : Fin 4) : ‖stepCoordinates η x i‖ ≤ B := by
  unfold stepCoordinates
  split_ifs with hx
  · rw [norm_toImaginary]; exact h _
  · simpa using hB
private theorem stepCoordinates_zero {S : Finset F.Cell} (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (0 : StepVariable S) x i = 0 := by apply _root_.YangMills.SharedProofs.p7539 <;> assumption
private theorem mem_chordBonds_of_not_tree (hB : BlocksCoverLowerLevel) (hL : Odd F.blockSide)
    (hs : ∀ i, 0 < F.extent i) (z : F.Site F.depth) (i : Fin 4) (h : ¬ IsAxialTreeBond (z, i)) :
    (z, i) ∈ chordBonds (finiteCells F) := by apply _root_.YangMills.SharedProofs.p40832 <;> assumption
private theorem fineBondAt_mem_chordBonds (hB : BlocksCoverLowerLevel) {F' : BlockFrame}
    (hLL : F'.blockSide = F.blockSide)
    (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (hs' : ∀ i, 2 ≤ F'.extent i) (Y : F.Cell) (Y' : F'.Cell)
    (h o : Fin 4 → ℤ) (i : Fin 4) (ho : o ∈ centredCube F.blockSide)
    (hb : fineBondAt Y h o i ∈ chordBonds (finiteCells F)) :
    fineBondAt Y' h o i ∈ chordBonds (finiteCells F') := by
  have hL' : Odd F'.blockSide := hLL ▸ hL
  have ho' : o ∈ centredCube F'.blockSide := hLL ▸ ho
  have hnt : ¬ IsAxialTreeBond (fineBondAt Y h o i) := by
    simp only [chordBonds, Finset.mem_filter] at hb
    exact hb.2
  have e1 := TopLevelSites.isAxialTreeBond_iff hL hs (Y + siteOfCoords F.top h) o ho i
  have e2 := TopLevelSites.isAxialTreeBond_iff hL' hs' (Y' + siteOfCoords F'.top h) o ho' i
  have hnt' : ¬ IsAxialTreeBond (fineBondAt Y' h o i) := by
    intro ht
    apply hnt
    have := e2.1 ht
    rw [hLL] at this
    exact e1.2 this
  exact mem_chordBonds_of_not_tree hB hL' (fun i => by have := hs' i; omega) _ _ hnt'
private theorem frameDeviation_eq (a ρ : ℝ) (m : ℕ) (b : F.Site F.depth × Fin 4) :
    frameDeviation a ρ m b =
      fun V' : F.GaugeField F.top => ((frameGap a ρ m b V' : imaginaryQuaternions) : ℍ[ℝ]) := by
  funext V'
  simp [frameDeviation, frameGap, stepFrame, torusCoordinate]
private theorem frameGap_bondAnalytic {a ρ : ℝ} {m : ℕ} {b : F.Site F.depth × Fin 4} {V : F.GaugeField F.top}
    (h1 : IsBondAnalyticAt (stepFrame false a ρ m b) V) (h2 : IsBondAnalyticAt (stepFrame true a ρ m b) V) :
    IsBondAnalyticAt (frameGap a ρ m b) V := by
  have e : frameGap a ρ m b =
      fun V' => (1 : ℝ) • stepFrame false a ρ m b V' + (-1 : ℝ) • stepFrame true a ρ m b V' := by
    funext V'
    simp only [frameGap]
    module
  rw [e]
  exact bondAnalytic_linear_comb 1 (-1) h1 h2
private theorem interpolatedFrame_nearMinimizer {a ρ δ₂ κ₂ Cf Cs C σ s : ℝ} {m : ℕ} {V : F.GaugeField F.top}
    {Kk : ℕ → ℝ}
    (hnear : (∀ i, 4 * m + 5 < F.extent i) → FrameNearMinimizer a ρ δ₂ Cf σ m V)
    (hsm : ∀ star, FrameSmallness star a ρ δ₂ κ₂ C σ Kk m V) (hs0 : 0 ≤ s)
    (hC : Cf ≤ Cs) (hCf : 0 < Cf) (hσ : 0 < σ) (hδ : 0 < δ₂) :
    InterpolatedFrameNearMinimizer s a ρ δ₂ (Cs * Real.exp (-(δ₂ / 4 * m))) σ m V := by
  have hCs : 0 < Cs := lt_of_lt_of_le hCf hC
  refine ⟨fun b hb => ⟨?_, ?_⟩, fun b hb k c X hk1 hk3 hX => ?_, fun hl b => ?_⟩
  · rw [interpolatedFrame_sub, norm_smul, Real.norm_of_nonneg hs0]
  · by_cases hl : ∀ i, 4 * m + 5 < F.extent i
    · have h1 := (hnear hl b hb).1
      have e : ‖frameGap a ρ m b V‖ = ‖frameDeviation a ρ m b V‖ := by
        rw [frameDeviation_eq]; rfl
      rw [e]
      refine h1.trans ?_
      unfold frameDecayBound
      gcongr
    · have e : frameGap a ρ m b V = 0 := by
        simp [frameGap, stepFrame_eq_of_small_extent a ρ m hl b V]
      rw [e, norm_zero]
      positivity
  · by_cases hl : ∀ i, 4 * m + 5 < F.extent i
    · have hG := frameGap_bondAnalytic ((hsm false).analytic b hb) ((hsm true).analytic b hb)
      have h1 := (hnear hl b hb).2 k c X hk1 hk3 hX
      rw [frameDeviation_eq, bondDeriv_coe hG c X, Nat.cast_max] at h1
      have h2 : ‖bondDeriv (frameGap a ρ m b) V c X‖ ≤
          Cf * Real.exp (-(δ₂ / 4 * ((m : ℝ) + max (m : ℝ) (bondListDistance (enclosingCell b.1) c)))) := h1
      refine h2.trans ?_
      rw [mul_assoc, ← Real.exp_add]
      have h3 : -(δ₂ / 4 * ((m : ℝ) + max (m : ℝ) (bondListDistance (enclosingCell b.1) c))) ≤
          -(δ₂ / 4 * m) + -(δ₂ / 4 * (bondListDistance (enclosingCell b.1) c : ℝ)) := by
        have := le_max_right (m : ℝ) (bondListDistance (enclosingCell b.1) c : ℝ)
        nlinarith
      calc _ ≤ Cs * Real.exp (-(δ₂ / 4 * ((m : ℝ) + max (m : ℝ) (bondListDistance (enclosingCell b.1) c)))) := by
            gcongr
        _ ≤ _ := by gcongr
    · have e : frameGap a ρ m b = fun _ => 0 := funext fun V' => by
        simp [frameGap, stepFrame_eq_of_small_extent a ρ m hl b V']
      rw [e]
      unfold bondDeriv
      simp only [iteratedFDeriv_fun_zero]
      simp
      positivity
  · rw [interpolatedFrame, stepFrame_eq_of_small_extent a ρ m hl b V]
    module
private theorem chartedField_congr {w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions} (V : F.GaugeField F.top)
    (h : ∀ z i, ¬ IsAxialTreeBond (z, i) → w z i = w' z i) : chartedField w V = chartedField w' V := by apply _root_.YangMills.SharedProofs.p16263 <;> assumption
private def zeroOnTree (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) :
    F.Site F.depth → Fin 4 → imaginaryQuaternions := by
  classical exact fun z i => if IsAxialTreeBond (z, i) then 0 else w z i
private theorem chartedField_zeroOnTree (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top) :
    chartedField (zeroOnTree w) V = chartedField w V :=
  chartedField_congr V fun z i h => by simp [zeroOnTree, h]
private theorem norm_zeroOnTree_sub_le {w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions} {ε : ℝ} (h0 : 0 ≤ ε)
    (h : ∀ z i, ¬ IsAxialTreeBond (z, i) → ‖w z i - w' z i‖ ≤ ε) (z : F.Site F.depth) (i : Fin 4) :
    ‖zeroOnTree w z i - zeroOnTree w' z i‖ ≤ ε := by
  by_cases ht : IsAxialTreeBond (z, i)
  · simpa [zeroOnTree, ht] using h0
  · simpa [zeroOnTree, ht] using h z i ht
private theorem chartedField_close (hS : ChartLipschitz.ChartedFieldLipschitz)
    {w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (V : F.GaugeField F.top) {ε : ℝ} (h0 : 0 ≤ ε) (h : ∀ z i, ¬ IsAxialTreeBond (z, i) → ‖w z i - w' z i‖ ≤ ε) :
    (∀ (x : F.Site F.depth) (l : List PathStep),
      ‖((pathHolonomy (chartedField w V) x l : UnitQuaternion) : ℍ[ℝ]) -
        ((pathHolonomy (chartedField w' V) x l : UnitQuaternion) : ℍ[ℝ])‖ ≤ l.length * ε) ∧
    ∀ p : F.Site F.depth × Fin 4 × Fin 4,
      plaquetteDefect (chartedField w V) p ≤ plaquetteDefect (chartedField w' V) p + 4 * ε := by
  have := hS.2 F (zeroOnTree w) (zeroOnTree w') V ε (norm_zeroOnTree_sub_le h0 h) h0
  rwa [chartedField_zeroOnTree, chartedField_zeroOnTree] at this
private theorem bondContour_length_le {L : ℕ} {h : Fin 4 → ℤ} (hh : h ∈ centredCube L) (π : Equiv.Perm (Fin 4))
    (i : Fin 4) : (bondContour L h π i).length ≤ 9 * L := by apply _root_.YangMills.Construction.NearFields.length_bondContour_le <;> assumption
private theorem norm_contourHolonomyRatio_sub {W W' : F.GaugeField F.depth} {V : F.GaugeField F.top}
    {c : F.Site F.top × Fin 4} {h : Fin 4 → ℤ} {π : Equiv.Perm (Fin 4)} :
    ‖contourHolonomyDefect W V c h π - contourHolonomyDefect W' V c h π‖ =
      ‖((pathHolonomy W (_root_.YangMills.Construction.BlockAverages.refineSite c.1) (bondContour F.blockSide h π c.2) : UnitQuaternion) : ℍ[ℝ]) -
        ((pathHolonomy W' (_root_.YangMills.Construction.BlockAverages.refineSite c.1) (bondContour F.blockSide h π c.2) : UnitQuaternion) : ℍ[ℝ])‖ := by
  unfold contourHolonomyDefect
  have e : ((pathHolonomy W (_root_.YangMills.Construction.BlockAverages.refineSite c.1) (bondContour F.blockSide h π c.2) * (V c.1 c.2)⁻¹ :
        UnitQuaternion) : ℍ[ℝ]) -
      ((pathHolonomy W' (_root_.YangMills.Construction.BlockAverages.refineSite c.1) (bondContour F.blockSide h π c.2) * (V c.1 c.2)⁻¹ :
        UnitQuaternion) : ℍ[ℝ]) =
      (((pathHolonomy W (_root_.YangMills.Construction.BlockAverages.refineSite c.1) (bondContour F.blockSide h π c.2) : UnitQuaternion) : ℍ[ℝ]) -
        ((pathHolonomy W' (_root_.YangMills.Construction.BlockAverages.refineSite c.1) (bondContour F.blockSide h π c.2) : UnitQuaternion) : ℍ[ℝ])) *
        (((V c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
    rw [sub_mul]; rfl
  rw [e, norm_mul, CStarRing.norm_coe_unitary, mul_one]
private theorem interpolatedFrame_small {a ρ δ₂ κ₂ C Cs σ s ω : ℝ} {m : ℕ} {V : F.GaugeField F.top}
    {Kk : ℕ → ℝ} (hS : ChartLipschitz.ChartedFieldLipschitz)
    (hch : ∀ z i, ¬ IsAxialTreeBond (z, i) → (z, i) ∈ chordBonds (finiteCells F))
    (hnear : InterpolatedFrameNearMinimizer s a ρ δ₂ ω σ m V)
    (hsm : ∀ star, FrameSmallness star a ρ δ₂ κ₂ C σ Kk m V) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hσ : 0 < σ) (hω : ω * σ ≤ 2⁻¹ ^ 10 * σ) (hCs : C + 9 * F.blockSide * (2⁻¹ ^ 10) ≤ Cs) :
    InterpolatedFrameSmall s a ρ δ₂ Cs σ m V := by
  have hC0 : C ≤ Cs := by
    have : (0 : ℝ) ≤ 9 * F.blockSide * (2⁻¹ ^ 10) := by positivity
    linarith
  have hmove : ∀ z i, ¬ IsAxialTreeBond (z, i) →
      ‖interpolatedFrame s a ρ m (z, i) V - stepFrame true a ρ m (z, i) V‖ ≤ 2⁻¹ ^ 10 * σ := by
    intro z i hz
    obtain ⟨e, hd⟩ := hnear.norm_eq_and_le (z, i) (hch z i hz)
    rw [e]
    have hn : 0 ≤ ‖frameGap a ρ m (z, i) V‖ := norm_nonneg _
    calc s * ‖frameGap a ρ m (z, i) V‖ ≤ 1 * ‖frameGap a ρ m (z, i) V‖ := by gcongr
      _ ≤ 2⁻¹ ^ 10 * σ := by linarith
  have hε : (0 : ℝ) ≤ 2⁻¹ ^ 10 * σ := by positivity
  have hfield : interpolatedField s a ρ m V 0 =
      chartedField (fun z i => interpolatedFrame s a ρ m (z, i) V) V := by
    unfold interpolatedField
    congr 1
    funext z i
    simp [interpolatedCoords, stepCoordinates_zero]
  have hclose := chartedField_close hS (w := fun z i => interpolatedFrame s a ρ m (z, i) V)
    (w' := frameCoordField true a ρ m V) V hε (fun z i hz => hmove z i hz)
  have hcold0 : IsSmallCurvature (41 / 64 * σ) (interpolatedField s a ρ m V 0) := by
    intro p hp
    rw [hfield]
    have h1 := hclose.2 p
    have h2 := (hsm true).small_curvature p hp
    simp only [if_true] at h2
    have : plaquetteDefect (chartedField (frameCoordField true a ρ m V) V) p < 5 / 8 * σ := h2
    have h3 : (2 : ℝ)⁻¹ ^ 10 = 1 / 1024 := by norm_num
    rw [h3] at h1
    linarith
  refine ⟨fun b hb => ?_, fun b hb => ?_, fun c h π hh => ?_, fun b hb k c X hk1 hk3 hX => ?_,
    fun b hb => ?_, fun b hb h => ?_, fun b hb γ => ?_, hcold0, fun η hη p hp => ?_⟩
  · exact (norm_convex_comb_le hs0 hs1 ((hsm true).norm_le b hb) ((hsm false).norm_le b hb)).trans (by gcongr)
  · have h1 : ‖stepFrame true a ρ m b V‖ ≤ ρ - σ / 64 := by
      have := (hsm true).norm_add_le b hb; linarith
    have h2 : ‖stepFrame false a ρ m b V‖ ≤ ρ - σ / 64 := by
      have := (hsm false).norm_add_le b hb; linarith
    have := norm_convex_comb_le hs0 hs1 h1 h2
    have e : ‖interpolatedFrame s a ρ m b V‖ ≤ ρ - σ / 64 := this
    linarith
  · have h1 := (hsm true).holonomy_ratio c h π hh
    have h2 : ‖contourHolonomyDefect (chartedField (fun z i => interpolatedFrame s a ρ m (z, i) V) V) V c h π -
        contourHolonomyDefect (chartedField (frameCoordField true a ρ m V) V) V c h π‖ ≤
          9 * F.blockSide * (2⁻¹ ^ 10 * σ) := by
      rw [norm_contourHolonomyRatio_sub]
      refine (hclose.1 _ _).trans ?_
      have := bondContour_length_le hh π c.2
      have h3 : ((bondContour F.blockSide h π c.2).length : ℝ) ≤ 9 * F.blockSide := by exact_mod_cast this
      gcongr
    calc _ ≤ ‖contourHolonomyDefect (chartedField (fun z i => interpolatedFrame s a ρ m (z, i) V) V) V c h π -
          contourHolonomyDefect (chartedField (frameCoordField true a ρ m V) V) V c h π‖ +
          ‖contourHolonomyDefect (chartedField (frameCoordField true a ρ m V) V) V c h π - 1‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 9 * F.blockSide * (2⁻¹ ^ 10 * σ) + C * σ := add_le_add h2 h1
      _ = (C + 9 * F.blockSide * (2⁻¹ ^ 10)) * σ := by ring
      _ ≤ Cs * σ := by gcongr
  · have e : bondDeriv (interpolatedFrame s a ρ m b) V c X =
        (1 - s) • bondDeriv (stepFrame true a ρ m b) V c X + s • bondDeriv (stepFrame false a ρ m b) V c X :=
      bondDeriv_linear_comb (1 - s) s ((hsm true).analytic b hb) ((hsm false).analytic b hb) c X
    rw [e]
    refine (norm_convex_comb_le hs0 hs1 ((hsm true).deriv_decay b hb k c X hk1 hk3 hX)
      ((hsm false).deriv_decay b hb k c X hk1 hk3 hX)).trans ?_
    gcongr
  · exact bondAnalytic_linear_comb (1 - s) s ((hsm true).analytic b hb) ((hsm false).analytic b hb)
  · simp only [interpolatedFrame, (hsm true).translation_invariant b hb h,
      (hsm false).translation_invariant b hb h]
  · simp only [interpolatedFrame, Submodule.coe_add, Submodule.coe_smul, (hsm true).gauge_covariant b hb γ,
      (hsm false).gauge_covariant b hb γ]
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
  · have h1 := (hS.2 F (zeroOnTree (interpolatedCoords s a ρ m V η)) (zeroOnTree (interpolatedCoords s a ρ m V 0))
      V (σ / 64)
      (norm_zeroOnTree_sub_le (by positivity) (fun z i _ => by
        simp only [interpolatedCoords, stepCoordinates_zero, add_zero, add_sub_cancel_left]
        exact norm_stepCoordinates_le η (by positivity) hη z i)) (by positivity)).2 p
    rw [chartedField_zeroOnTree, chartedField_zeroOnTree] at h1
    have h2 := hcold0 p hp
    have h3 : plaquetteDefect (interpolatedField s a ρ m V η) p ≤
        plaquetteDefect (interpolatedField s a ρ m V 0) p + 4 * (σ / 64) := h1
    linarith
private theorem norm_coe_sub (u v : imaginaryQuaternions) : ‖(u : ℍ[ℝ]) - (v : ℍ[ℝ])‖ = ‖u - v‖ := by
  rw [← Submodule.coe_sub]; rfl
private theorem interpolatedFrame_local {a ρ δ₂ κ₂ C Cs σ s K s₀ : ℝ} {m r : ℕ} {F' : BlockFrame}
    {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell} {Kk Kk' : ℕ → ℝ}
    (hloc : ∀ star, FrameLocality star a ρ δ₂ C σ m V V' Y Y' r)
    (hcmp : ComparesMinimizers a ρ δ₂ K (5 / 4 * σ) s₀ Kk V V' Y Y' r)
    (hsm : ∀ star, FrameSmallness star a ρ δ₂ κ₂ C σ Kk' m V)
    {C' : ℝ} (hsm' : ∀ star, FrameSmallness star a ρ δ₂ κ₂ C' σ Kk' m V')
    (hch : ∀ h o i, IsFineBondWithinRadius Y r h o i → fineBondAt Y' h o i ∈ chordBonds (finiteCells F'))
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hσ : 0 < σ) (hC : C ≤ Cs) (hK : 0 < K) :
    InterpolatedFrameLocal s a ρ δ₂ K Cs σ m V V' Y Y' r := by
  refine ⟨fun h o i hb => ?_, fun h o i k e X hb hk1 hk3 he hX => ?_, fun hl hl' h o i hb hm => ?_⟩
  · have e : interpolatedFrame s a ρ m (fineBondAt Y h o i) V - interpolatedFrame s a ρ m (fineBondAt Y' h o i) V' =
        (1 - s) • (stepFrame true a ρ m (fineBondAt Y h o i) V - stepFrame true a ρ m (fineBondAt Y' h o i) V') +
        s • (stepFrame false a ρ m (fineBondAt Y h o i) V - stepFrame false a ρ m (fineBondAt Y' h o i) V') := by
      simp only [interpolatedFrame]
      module
    rw [e]
    have h1 := (hloc true).value h o i hb
    have h2 := (hloc false).value h o i hb
    rw [norm_coe_sub] at h1 h2
    refine (norm_convex_comb_le hs0 hs1 h1 h2).trans ?_
    gcongr
  · have hb1 := hb.2.1
    have hb2 := hch h o i hb
    have e1 : bondDeriv (interpolatedFrame s a ρ m (fineBondAt Y h o i)) V (bondsAt Y e) X = _ :=
      bondDeriv_linear_comb (1 - s) s ((hsm true).analytic _ hb1) ((hsm false).analytic _ hb1) (bondsAt Y e) X
    have e2 : bondDeriv (interpolatedFrame s a ρ m (fineBondAt Y' h o i)) V' (bondsAt Y' e) X = _ :=
      bondDeriv_linear_comb (1 - s) s ((hsm' true).analytic _ hb2) ((hsm' false).analytic _ hb2) (bondsAt Y' e) X
    rw [e1, e2]
    have e3 : ∀ u v u' v' : imaginaryQuaternions, ((1 - s) • u + s • v) - ((1 - s) • u' + s • v') =
        (1 - s) • (u - u') + s • (v - v') := fun u v u' v' => by module
    rw [e3]
    refine (norm_convex_comb_le hs0 hs1 ((hloc true).deriv h o i k e X hb hk1 hk3 he hX)
      ((hloc false).deriv h o i k e X hb hk1 hk3 he hX)).trans ?_
    gcongr
  · obtain ⟨hsame, -⟩ := (hloc false).eq_of_far rfl hl hl' h o i hb hm
    refine ⟨?_, ?_, ?_⟩
    · simp only [interpolatedFrame, hsame]
      module
    · simp only [frameGap, hsame]
      module
    · have h1 := hcmp.coordinates h o i hb
      rw [norm_coe_sub] at h1
      have e1 : ∀ (G : BlockFrame) (b : G.Site G.depth × Fin 4) (U : G.GaugeField G.top),
          stepFrame true a ρ m b U = torusCoordinate a ρ b U := fun G b U => by
        simp [stepFrame, torusCoordinate]
      rw [e1, e1]
      refine h1.trans ?_
      have : K * (5 / 4 * σ) ≤ 2 * K * σ := by nlinarith
      gcongr
private theorem frameRadius_arith {Cs C σ δ x m : ℝ} (hCs : 0 < Cs) (hC : 0 < C) (hσ : 0 < σ)
    (hδ : 0 < δ) (hx1 : 1 ≤ x) (hm0 : 0 ≤ m)
    (hAm : (16 + Cs * 2 ^ 10 / σ + Cs * 2 ^ 10 + C * Cs + C) * x ^ 2 * Real.exp (-(3 * δ / 16 * m)) ≤ 1) :
    Cs * Real.exp (-(δ / 4 * m)) ≤ 2⁻¹ ^ 10 * σ ∧ Cs * Real.exp (-(δ / 4 * m)) ≤ 2⁻¹ ^ 10 ∧
    (∀ κ : ℝ, 0 < κ → κ ≤ δ / 2 ^ 14 →
      C * x ^ 2 * (Cs * Real.exp (-(δ / 4 * m))) ≤ Real.exp (-(2 ^ 10 * κ * m))) ∧
    C * x ^ 2 * Real.exp (-(2 * δ * m)) ≤ 1 := by
  set e₁ := Real.exp (-(3 * δ / 16 * m)) with he₁
  have hx2 : 1 ≤ x ^ 2 := one_le_pow₀ hx1
  have hP1 : 0 < Cs * 2 ^ 10 / σ := by positivity
  have hP2 : 0 < Cs * 2 ^ 10 := by positivity
  have hP3 : 0 < C * Cs := by positivity
  have hexp : Real.exp (-(δ / 4 * m)) ≤ e₁ := by
    apply Real.exp_le_exp.2
    have : 3 * δ / 16 * m ≤ δ / 4 * m := mul_le_mul_of_nonneg_right (by linarith) hm0
    linarith
  have hterm : ∀ B : ℝ, 0 ≤ B → B ≤ 16 + Cs * 2 ^ 10 / σ + Cs * 2 ^ 10 + C * Cs + C → B * e₁ ≤ 1 := by
    intro B hB0 hB
    calc B * e₁ ≤ B * x ^ 2 * e₁ := by
          have : B * 1 ≤ B * x ^ 2 := by gcongr
          gcongr
          linarith
      _ ≤ (16 + Cs * 2 ^ 10 / σ + Cs * 2 ^ 10 + C * Cs + C) * x ^ 2 * e₁ := by gcongr
      _ ≤ 1 := hAm
  have h10 : (2 : ℝ)⁻¹ ^ 10 = 1 / 2 ^ 10 := by norm_num
  refine ⟨?_, ?_, fun κ hκ0 hκ => ?_, ?_⟩
  · have h1 := hterm (Cs * 2 ^ 10 / σ) hP1.le (by linarith)
    have h2 : Cs * 2 ^ 10 / σ * e₁ = Cs * e₁ * 2 ^ 10 / σ := by ring
    rw [h2, div_le_one hσ] at h1
    have h3 : Cs * Real.exp (-(δ / 4 * m)) ≤ Cs * e₁ := by gcongr
    rw [h10]
    have h4 : Cs * e₁ ≤ σ / 2 ^ 10 := by rw [le_div_iff₀ (by norm_num)]; exact h1
    calc _ ≤ σ / 2 ^ 10 := h3.trans h4
      _ = _ := by ring
  · have h1 := hterm (Cs * 2 ^ 10) hP2.le (by linarith)
    have h3 : Cs * Real.exp (-(δ / 4 * m)) ≤ Cs * e₁ := by gcongr
    rw [h10]
    have h4 : Cs * e₁ ≤ 1 / 2 ^ 10 := by
      rw [le_div_iff₀ (by norm_num)]
      calc Cs * e₁ * 2 ^ 10 = Cs * 2 ^ 10 * e₁ := by ring
        _ ≤ 1 := h1
    exact h3.trans h4
  · have h1 : Real.exp (-(δ / 4 * m)) = e₁ * Real.exp (-(δ / 16 * m)) := by
      rw [he₁, ← Real.exp_add]; congr 1; ring
    have h2 : Real.exp (-(δ / 16 * m)) ≤ Real.exp (-(2 ^ 10 * κ * m)) := by
      apply Real.exp_le_exp.2
      have h5 : 2 ^ 10 * κ ≤ δ / 16 := by
        have : κ * 2 ^ 14 ≤ δ := by rwa [le_div_iff₀ (by norm_num)] at hκ
        linarith
      have := mul_le_mul_of_nonneg_right h5 hm0
      linarith
    have h4 : C * Cs * x ^ 2 * e₁ ≤ 1 := by
      calc C * Cs * x ^ 2 * e₁ ≤ (16 + Cs * 2 ^ 10 / σ + Cs * 2 ^ 10 + C * Cs + C) * x ^ 2 * e₁ := by
            have : C * Cs ≤ 16 + Cs * 2 ^ 10 / σ + Cs * 2 ^ 10 + C * Cs + C := by linarith
            gcongr
        _ ≤ 1 := hAm
    calc C * x ^ 2 * (Cs * Real.exp (-(δ / 4 * m)))
        ≤ C * x ^ 2 * (Cs * (e₁ * Real.exp (-(2 ^ 10 * κ * m)))) := by
          rw [h1]; gcongr
      _ = (C * Cs * x ^ 2 * e₁) * Real.exp (-(2 ^ 10 * κ * m)) := by ring
      _ ≤ 1 * Real.exp (-(2 ^ 10 * κ * m)) := by gcongr
      _ = _ := one_mul _
  · have h1 : Real.exp (-(2 * δ * m)) ≤ e₁ := by
      apply Real.exp_le_exp.2
      have : 3 * δ / 16 * m ≤ 2 * δ * m := mul_le_mul_of_nonneg_right (by linarith) hm0
      linarith
    calc C * x ^ 2 * Real.exp (-(2 * δ * m))
        ≤ (16 + Cs * 2 ^ 10 / σ + Cs * 2 ^ 10 + C * Cs + C) * x ^ 2 * e₁ := by
          have : C ≤ 16 + Cs * 2 ^ 10 / σ + Cs * 2 ^ 10 + C * Cs + C := by linarith
          gcongr
      _ ≤ 1 := hAm
theorem interpolatedFramesControlled_holds (hW : frameBoundsStatement)
    (hB : BlocksCoverLowerLevel) (hS : ChartLipschitz.ChartedFieldLipschitz)
    (hF : Estimates.frameRadiusGrowthStatement) : interpolatedFramesControlled := by
  intro a ha
  refine ⟨2 ^ 40, fun L hL hL0 c hc => ?_⟩
  obtain ⟨Cf, C, σ₀, hCf, hC, hσ₀, hWb⟩ := hW a L c ha hL hL0 hc
  obtain ⟨⟨hρ, hρ1, hs₀, hδ₂, hκ₂, hK, hC1, hKk⟩, hcb⟩ := hc.classical
  refine ⟨max Cf (C + 9 * L * 2⁻¹ ^ 10), fun Cs hCs => ⟨c.δ₂ / 2 ^ 14, by positivity, fun κ hκ0 hκ =>
    ⟨1, one_pos, fun η₃ _ _ _ => ⟨0, fun blk _ => ⟨min σ₀ (c.s₀ / 2), lt_min hσ₀ (by positivity),
    fun σ hσ hσle p hp => ⟨0, fun Cs' _ E hE => ⟨64, fun n₀ hn₀ => ⟨0, fun CE _ => ?_⟩⟩⟩⟩⟩⟩⟩⟩
  have hCfs : Cf ≤ Cs := (le_max_left _ _).trans hCs
  have hCs' : C + 9 * L * 2⁻¹ ^ 10 ≤ Cs := (le_max_right _ _).trans hCs
  have hCs0 : 0 < Cs := lt_of_lt_of_le hCf hCfs
  have hC0 : 0 < C := by linarith
  have hCC : C ≤ Cs := by
    have : (0 : ℝ) ≤ 9 * L * 2⁻¹ ^ 10 := by positivity
    linarith
  have hc₁ : 0 < 3 * c.δ₂ / 16 := by positivity
  obtain ⟨y, hy1, hy⟩ := hF (16 + Cs * 2 ^ 10 / σ + Cs * 2 ^ 10 + C * Cs + C) (3 * c.δ₂ / 16)
    (by positivity) hc₁
  refine ⟨y, fun y₁ hy₁ t x hx => ?_⟩
  have hx' : y₁ ≤ x := hx
  have hyx : y ≤ x := hy₁.trans hx'
  have hx1 : 1 ≤ x := hy1.trans hyx
  obtain ⟨hAm, hmA⟩ := hy x hyx
  have hm0 : (0 : ℝ) ≤ (frameRadius x : ℝ) := Nat.cast_nonneg _
  obtain ⟨hgapCs, hgapCs1, hy2', hy3⟩ := frameRadius_arith hCs0 hC0 hσ hδ₂ hx1 hm0 hAm
  have hm16 : 16 ≤ frameRadius x := by
    have h0 : 0 ≤ Cs * 2 ^ 10 / σ + Cs * 2 ^ 10 + C * Cs + C := by positivity
    have h1 : (16 : ℝ) ≤ (frameRadius x : ℝ) := by linarith
    exact_mod_cast h1
  have hgap0 : Cf * Real.exp (-(c.δ₂ / 4 * (frameRadius x : ℝ))) ≤
      Cs * Real.exp (-(c.δ₂ / 4 * (frameRadius x : ℝ))) := by gcongr
  have hgap : frameDecayBound Cf c.δ₂ (frameRadius x) ≤ 2⁻¹ ^ 10 * σ := hgap0.trans hgapCs
  have hy2 : C * x ^ 2 * frameDecayBound Cf c.δ₂ (frameRadius x) ≤
      Real.exp (-(2 ^ 10 * κ * (frameRadius x : ℝ))) := by
    refine le_trans ?_ (hy2' κ hκ0 hκ)
    unfold frameDecayBound
    gcongr
  set m := frameRadius x with hm
  have hσ₀' : σ ≤ σ₀ := hσle.trans (min_le_left _ _)
  have hσs : 5 / 4 * σ ≤ c.s₀ := by
    have : σ ≤ c.s₀ / 2 := hσle.trans (min_le_right _ _)
    linarith
  have hκ' : κ ≤ c.δ₂ / 2 ^ 14 := hκ
  have hn64 : 64 ≤ n₀ := hn₀
  have hWat := fun (G : BlockFrame) (U : G.GaugeField G.top) (ht : IsCubicTopTorus L t n₀ G)
      (hcold : IsSmallCurvature (5 / 4 * σ) U) =>
    hWb κ σ x m t n₀ hκ0 hκ' hσ hσ₀' hx1 hm16 hn64 hgap hy2 hy3 G U ht hcold
  have hsides : ∀ (G : BlockFrame), IsCubicTopTorus L t n₀ G →
      G.blockSide = L ∧ (∀ i, 2 ≤ G.extent i) ∧ IsBlockTorus L G := by
    rintro G ⟨h1, -, n, hn, hn0⟩
    refine ⟨h1, fun i => ?_, h1, n, by omega, hn⟩
    rw [hn i]; omega
  have hnear : ∀ (G : BlockFrame) (U : G.GaugeField G.top) (s : ℝ), IsCubicTopTorus L t n₀ G →
      IsSmallCurvature (5 / 4 * σ) U → 0 ≤ s →
      InterpolatedFrameNearMinimizer s a c.ρA c.δ₂ (Cs * Real.exp (-(c.δ₂ / 4 * m))) σ m U := by
    intro G U s ht hcold hs0
    obtain ⟨h1, h2, -, -⟩ := hWat G U ht hcold
    exact interpolatedFrame_nearMinimizer h1 h2 hs0 hCfs hCf hσ hδ₂
  refine ⟨fun G U s ht hcold hs0 hs1 => ?_, fun G G' U U' Y Y' r s ht ht' hcold hcold' hag hs0 hs1 => ?_⟩
  · obtain ⟨hGL, hGs, hGc⟩ := hsides G ht
    have hn := hnear G U s ht hcold hs0
    refine ⟨hn, ?_⟩
    obtain ⟨-, h2, -, -⟩ := hWat G U ht hcold
    have hLodd : Odd G.blockSide := hGL ▸ hL
    have hω : Cs * Real.exp (-(c.δ₂ / 4 * m)) * σ ≤ 2⁻¹ ^ 10 * σ := by
      have : Cs * Real.exp (-(c.δ₂ / 4 * m)) ≤ 2⁻¹ ^ 10 := hgapCs1
      gcongr
    exact interpolatedFrame_small hS (fun z i hz => mem_chordBonds_of_not_tree hB hLodd
      (fun i => by have := hGs i; omega) z i hz) hn h2 hs0 hs1 hσ hω (by rw [hGL]; exact hCs')
  · obtain ⟨hGL, hGs, hGc⟩ := hsides G ht
    obtain ⟨hGL', hGs', hGc'⟩ := hsides G' ht'
    obtain ⟨-, h2, -, h4⟩ := hWat G U ht hcold
    obtain ⟨-, h2', -, -⟩ := hWat G' U' ht' hcold'
    have hloc := (h4 G' U' Y Y' r ht' hcold' hag).1
    have hGt : G'.depth = G.depth := ht'.2.1.trans ht.2.1.symm
    have hcmp := (hcb G (5 / 4 * σ) U hGc (by positivity) hσs hcold).2.2.2 G' U' Y Y' r hGc' hGt hcold' hag
    have hLodd : Odd G.blockSide := hGL ▸ hL
    exact interpolatedFrame_local hloc hcmp h2 h2'
      (fun h o i hb => fineBondAt_mem_chordBonds hB (hGL'.trans hGL.symm) hLodd hGs hGs' Y Y' h o i hb.1 hb.2.1)
      hs0 hs1 hσ hCC hK
end YangMills.Construction.Interpolation
end
