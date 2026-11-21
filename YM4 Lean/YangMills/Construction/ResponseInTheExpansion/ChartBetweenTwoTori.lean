import YangMills.Construction.ColdChainAtEveryLevel.SitesOfAPatch
import YangMills.Construction.ColdStepAtMirrorFrames.SitesOfABlock
import YangMills.Construction.ResponseInTheExpansion.CalculusOfTheSmoothMoves
import YangMills.Construction.ResponseInTheExpansion.CalculusOfTwoMoves
import YangMills.Construction.ResponseInTheExpansion.SmoothMovesOnTwoTori
import YangMills.Construction.SummableBoundsOfTheFlow.DistancesOfOffsets
import YangMills.Construction.SummableBoundsOfTheFlow.PropertiesOfIntermediateFrames
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation TorusComparison WeightedResponses
namespace ChartTransfer
variable {F F' : BlockFrame}
structure TorusPairData (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (x : ℝ) (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top) (Y : F.Cell)
    (Y' : F'.Cell) (q : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι] (j : ι → ↥(chordBonds (finiteCells F)))
    (j' : ι → ↥(chordBonds (finiteCells F'))) : Prop where
  odd_side : Odd T.L
  torus : IsBlockTorus T.L F
  torus' : IsBlockTorus T.L F'
  depth_eq : F'.depth = F.depth
  two_le : 2 ≤ q
  extent_gt : ∀ i, 2 * q + 2 < F.extent i
  extent_gt' : ∀ i, 2 * q + 2 < F'.extent i
  agree : AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' q
  short : IsShortPairing Y Y' q j j'
  small : InterpolatedFrameSmall 1 T.a T.chainParams.ρA T.chainParams.δ₂ T.Ct T.σ (frameRadius x) V
  small' : InterpolatedFrameSmall 1 T.a T.chainParams.ρA T.chainParams.δ₂ T.Ct T.σ (frameRadius x) V'
  locality : InterpolatedFrameLocal 1 T.a T.chainParams.ρA T.chainParams.δ₂ T.chainParams.K T.Ct T.σ (frameRadius x)
    V V' Y Y' q
  σ_pos : 0 < T.σ
  Ct_pos : 0 < T.Ct
  δ₂_pos : 0 < T.chainParams.δ₂
  gap_le : 16 * T.Ct * Real.exp (-(T.chainParams.δ₂ / 8 * q)) ≤ 1
  room_le : (T.Ct + 1) * T.σ ≤ 1 / (64 * (T.L : ℝ))
  σ_le : T.σ ≤ T.chainParams.σA
  one_le_a : 1 ≤ T.a
  side_ge : 2 ^ 40 ≤ T.L
  admissible : T.chainParams.Admissible T.a T.L
  κ_pos : 0 < T.κ
  κ_le : T.κ ≤ T.chainParams.δ₂ / 2 ^ 8
def chartPoint (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (x : ℝ) (V : F.GaugeField F.top) {ι : Type} [Fintype ι] [DecidableEq ι]
    (j : ι → ↥(chordBonds (finiteCells F))) (ζ : BondField ι) : F.Site F.depth → Fin 4 → imaginaryQuaternions :=
  interpolatedCoords 1 T.a T.chainParams.ρA (frameRadius x) V (toTorus j ζ)
def frameGap (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (q : ℕ) : ℝ := T.Ct * T.σ * Real.exp (-(T.chainParams.δ₂ / 8 * q))
section Transfer
variable {ι : Type} [Fintype ι] [DecidableEq ι] {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {x : ℝ} {V : F.GaugeField F.top}
  {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell} {q : ℕ} {j : ι → ↥(chordBonds (finiteCells F))}
  {j' : ι → ↥(chordBonds (finiteCells F'))}
theorem TorusPairData.two_le_extent (P : TorusPairData T x V V' Y Y' q j j') (i : Fin 4) : 2 ≤ F.extent i := by
  have := P.extent_gt i
  omega
theorem TorusPairData.two_le_extent' (P : TorusPairData T x V V' Y Y' q j j') (i : Fin 4) : 2 ≤ F'.extent i := by
  have := P.extent_gt' i
  omega
theorem TorusPairData.odd_blockSide (P : TorusPairData T x V V' Y Y' q j j') : Odd F.blockSide := by
  rw [P.torus.1]
  exact P.odd_side
theorem TorusPairData.odd_blockSide' (P : TorusPairData T x V V' Y Y' q j j') : Odd F'.blockSide := by
  rw [P.torus'.1]
  exact P.odd_side
theorem frameGap_nonneg (P : TorusPairData T x V V' Y Y' q j j') : 0 ≤ frameGap T q := by
  have := P.σ_pos
  have := P.Ct_pos
  unfold frameGap
  positivity
theorem sixteen_mul_frameGap_le (P : TorusPairData T x V V' Y Y' q j j') : 16 * frameGap T q ≤ T.σ := by
  have h := mul_le_mul_of_nonneg_right P.gap_le P.σ_pos.le
  unfold frameGap
  nlinarith
theorem fineBondAt_injective_of_small (hD : Estimates.cellOffsetStatement) (hS : SiteDecomposition) {G : BlockFrame}
    (hG : Odd G.blockSide) {q : ℕ} (hs : ∀ i, 2 * q + 2 < G.extent i) (Z : G.Cell) {h h₁ o o₁ : Fin 4 → ℤ}
    {k k₁ : Fin 4} (hh : ∀ l, 2 * |h l| ≤ q) (hh₁ : ∀ l, 2 * |h₁ l| ≤ q) (ho : o ∈ centredCube G.blockSide)
    (ho₁ : o₁ ∈ centredCube G.blockSide) (e : fineBondAt Z h o k = fineBondAt Z h₁ o₁ k₁) :
    h = h₁ ∧ o = o₁ ∧ k = k₁ := by
  have hs2 : ∀ i, 2 ≤ G.extent i := fun i => by
    have := hs i
    omega
  have e1 : cellCentre G.depth (Z + siteOfCoords G.top h) + siteOfCoords G.depth o =
      cellCentre G.depth (Z + siteOfCoords G.top h₁) + siteOfCoords G.depth o₁ := congrArg Prod.fst e
  have e2 : k = k₁ := congrArg Prod.snd e
  obtain ⟨c1, c2⟩ := (hS G hG hs2).1 (Z + siteOfCoords G.top h) o ho
  obtain ⟨c3, c4⟩ := (hS G hG hs2).1 (Z + siteOfCoords G.top h₁) o₁ ho₁
  have e3 : Z + siteOfCoords G.top h = Z + siteOfCoords G.top h₁ := by
    rw [← c1, e1, c3]
  have e4 : o = o₁ := by
    rw [← c2, e1, c4]
  obtain ⟨-, -, -, hd⟩ := hD G hG hs2
  have a1 := (hd q hs Z h h₁ hh hh₁).1
  have a2 := (hd q hs Z h₁ h hh₁ hh).1
  refine ⟨?_, e4, e2⟩
  rw [e3] at a1
  rw [← a1, a2]
theorem two_mul_cellSupDist_add_le (hD : Estimates.cellOffsetStatement) {G : BlockFrame} (hG : Odd G.blockSide)
    {q : ℕ} (hs : ∀ i, 2 * q + 2 < G.extent i) (Z : G.Cell) {h : Fin 4 → ℤ} (hh : ∀ l, 2 * |h l| ≤ q) :
    2 * cellSupDist (Z + siteOfCoords G.top h) Z ≤ q := by
  have hs2 : ∀ i, 2 ≤ G.extent i := fun i => by
    have := hs i
    omega
  obtain ⟨-, -, -, hd⟩ := hD G hG hs2
  have h0 : ∀ l, 2 * |(0 : Fin 4 → ℤ) l| ≤ (q : ℤ) := fun l => by simp
  have a := (hd q hs Z h 0 hh h0).2
  have z0 : Z + siteOfCoords G.top (0 : Fin 4 → ℤ) = Z := by
    funext i
    simp [siteOfCoords]
  rw [z0] at a
  rw [a]
  have hle : (Finset.univ.sup fun i => (h i - (0 : Fin 4 → ℤ) i).natAbs) ≤ q / 2 := by
    refine Finset.sup_le fun i _ => ?_
    have := hh i
    rw [Int.abs_eq_natAbs] at this
    simp only [Pi.zero_apply, sub_zero]
    omega
  omega
theorem exists_pair_of_small_offsets (hD : Estimates.cellOffsetStatement) (hS : SiteDecomposition)
    (P : TorusPairData T x V V' Y Y' q j j') {h o : Fin 4 → ℤ} {k : Fin 4} (hh : ∀ l, 2 * |h l| ≤ q)
    (ho : o ∈ centredCube F.blockSide) (hb : fineBondAt Y h o k ∈ chordBonds (finiteCells F)) :
    ∃ i, (j i).1 = fineBondAt Y h o k ∧ (j' i).1 = fineBondAt Y' h o k := by
  have hs2 := P.two_le_extent
  have hc : enclosingCell (fineBondAt Y h o k).1 = Y + siteOfCoords F.top h :=
    (hD F P.odd_blockSide hs2).1 Y h o k ho
  have hn : (⟨_, hb⟩ : ↥(chordBonds (finiteCells F))) ∈ bondsNearCell Y q := by
    simp only [bondsNearCell, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hc]
    exact two_mul_cellSupDist_add_le hD P.odd_blockSide P.extent_gt Y hh
  obtain ⟨i, hi⟩ := (P.short.isBoxPairing.mem_left_iff _).1 hn
  obtain ⟨h₁, o₁, k₁, hs₁, ho₁, e₁, e₂⟩ := P.short.short_offsets i
  have e : fineBondAt Y h o k = fineBondAt Y h₁ o₁ k₁ := by
    rw [← e₁, hi]
  obtain ⟨rfl, rfl, rfl⟩ := fineBondAt_injective_of_small hD hS P.odd_blockSide P.extent_gt Y hh hs₁ ho ho₁ e
  exact ⟨i, e₁, e₂⟩
theorem norm_interpolatedFrame_sub_le (hD : Estimates.cellOffsetStatement) (hS : SiteDecomposition)
    (P : TorusPairData T x V V' Y Y' q j j') (k : ι) :
    ‖interpolatedFrame 1 T.a T.chainParams.ρA (frameRadius x) (j k).1 V -
      interpolatedFrame 1 T.a T.chainParams.ρA (frameRadius x) (j' k).1 V'‖ ≤ frameGap T q := by
  obtain ⟨h, o, i, hh, ho, e₁, e₂⟩ := P.short.short_offsets k
  have hc : enclosingCell (fineBondAt Y h o i).1 = Y + siteOfCoords F.top h :=
    (hD F P.odd_blockSide P.two_le_extent).1 Y h o i ho
  have hd : 2 * cellSupDist (Y + siteOfCoords F.top h) Y ≤ q :=
    two_mul_cellSupDist_add_le hD P.odd_blockSide P.extent_gt Y hh
  have hd' : cellSupDist Y (enclosingCell (fineBondAt Y h o i).1) = cellSupDist (Y + siteOfCoords F.top h) Y := by
    rw [hc, PatchLocality.cellSupDist_comm]
  have hbox : IsFineBondWithinRadius Y q h o i := by
    refine ⟨ho, ?_, ?_, ?_, ?_⟩
    · rw [← e₁]
      exact (j k).2
    · intro l
      have := hh l
      have := abs_nonneg (h l)
      omega
    · rw [hd']
      omega
    · rcases ((hS F P.odd_blockSide P.two_le_extent).2.2.2 (fineBondAt Y h o i).1 i) with e | e
      · rw [e, hd']
        omega
      · rw [e, hc]
        have t := PatchLocality.cellSupDist_triangle Y (Y + siteOfCoords F.top h)
          (Y + siteOfCoords F.top h + unitStep F.top i)
        have hu := two_mul_cellSupDist_add_le hD P.odd_blockSide (q := 2)
          (fun l => by have := P.extent_gt l; have := P.two_le; omega)
          (Y + siteOfCoords F.top h) (h := Pi.single i 1) (fun l => by
            by_cases hl : l = i
            · subst hl
              simp
            · simp [Pi.single_eq_of_ne hl])
        have hu' : cellSupDist (Y + siteOfCoords F.top h) (Y + siteOfCoords F.top h + unitStep F.top i) ≤ 1 := by
          rw [PatchLocality.cellSupDist_comm]
          unfold unitStep
          omega
        have c := PatchLocality.cellSupDist_comm Y (Y + siteOfCoords F.top h)
        have := P.two_le
        omega
  have hv := P.locality.norm_sub_le h o i hbox
  rw [← e₁, ← e₂] at hv
  refine hv.trans ?_
  rw [← e₁] at hd'
  rw [hd']
  unfold frameGap
  have hq : ((cellSupDist (Y + siteOfCoords F.top h) Y : ℕ) : ℝ) ≤ (q : ℝ) / 2 := by
    have : ((2 * cellSupDist (Y + siteOfCoords F.top h) Y : ℕ) : ℝ) ≤ q := by exact_mod_cast hd
    push_cast at this
    linarith
  have hδ := P.δ₂_pos
  have he : Real.exp (-(T.chainParams.δ₂ / 4 * ((q : ℝ) - cellSupDist (Y + siteOfCoords F.top h) Y))) ≤
      Real.exp (-(T.chainParams.δ₂ / 8 * q)) := by
    apply Real.exp_le_exp.2
    nlinarith
  have := P.σ_pos
  have := P.Ct_pos
  gcongr
theorem chartPoint_sub_interpolatedFrame {G : BlockFrame} (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (x : ℝ) (W : G.GaugeField G.top)
    {ι : Type} [Fintype ι] [DecidableEq ι] (l : ι → ↥(chordBonds (finiteCells G))) (ζ : BondField ι)
    (z : G.Site G.depth) (i : Fin 4) :
    chartPoint T x W l ζ z i - interpolatedFrame 1 T.a T.chainParams.ρA (frameRadius x) (z, i) W =
      stepCoordinates (toTorus l ζ) z i := by
  simp [chartPoint, interpolatedCoords]
theorem chartPoint_admissible {G : BlockFrame} {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {x : ℝ} {W : G.GaugeField G.top} {ι : Type}
    [Fintype ι] [DecidableEq ι] {l : ι → ↥(chordBonds (finiteCells G))} (hl : Function.Injective l) {ζ : BondField ι}
    (hs : InterpolatedFrameSmall 1 T.a T.chainParams.ρA T.chainParams.δ₂ T.Ct T.σ (frameRadius x) W) (hσ : 0 < T.σ)
    (hζ : ∀ i, ‖ζ i‖ ≤ T.ballRadius) (hr : (T.Ct + 1) * T.σ ≤ 1 / (64 * (T.L : ℝ))) (hc : T.σ ≤ T.chainParams.σA) :
    IsAdmissibleChartPoint T.L T.chainParams.σA (chartPoint T x W l ζ) W := by
  have hρ : 0 ≤ T.ballRadius := by
    unfold StepParameters.ballRadius
    positivity
  refine ⟨fun b hb => ?_, fun p hp => ?_⟩
  · have h1 := hs.norm_le b hb
    have h2 := SecondOrderMoves.norm_stepCoordinates_le (toTorus l ζ) hρ
      (SecondOrderMoves.norm_toTorus_le hl hρ hζ) b.1 b.2
    have h3 : ‖chartPoint T x W l ζ b.1 b.2‖ ≤ T.Ct * T.σ + T.ballRadius := by
      unfold chartPoint interpolatedCoords
      exact (norm_add_le _ _).trans (add_le_add h1 h2)
    have : T.ballRadius ≤ T.σ := by
      unfold StepParameters.ballRadius
      linarith
    nlinarith
  · have h1 := hs.small_curvature_nearby (toTorus l ζ)
      (fun b => SecondOrderMoves.norm_toTorus_le hl hρ hζ b) p hp
    have : plaquetteDefect (chartedField (chartPoint T x W l ζ) W) p < 3 / 4 * T.σ := h1
    linarith
def transferredChart (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (x : ℝ) (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top)
    (j : ι → ↥(chordBonds (finiteCells F))) (j' : ι → ↥(chordBonds (finiteCells F'))) (ζ : BondField ι) :
    F'.Site F'.depth → Fin 4 → imaginaryQuaternions :=
  open Classical in fun z i => if h : ∃ k, (j' k).1 = (z, i) then
    chartPoint T x V j ζ (j h.choose).1.1 (j h.choose).1.2
    else chartPoint T x V' j' ζ z i
theorem transferredChart_apply_pair (hj' : Function.Injective j') (ζ : BondField ι) (k : ι) :
    transferredChart T x V V' j j' ζ (j' k).1.1 (j' k).1.2 = chartPoint T x V j ζ (j k).1.1 (j k).1.2 := by
  have h : ∃ k', (j' k').1 = ((j' k).1.1, (j' k).1.2) := ⟨k, rfl⟩
  unfold transferredChart
  rw [dif_pos h]
  have e : h.choose = k := hj' (Subtype.ext h.choose_spec)
  rw [e]
theorem transferredChart_apply_of_not_pair (ζ : BondField ι) {z : F'.Site F'.depth} {i : Fin 4}
    (h : ¬ ∃ k, (j' k).1 = (z, i)) :
    transferredChart T x V V' j j' ζ z i = chartPoint T x V' j' ζ z i := by
  unfold transferredChart
  rw [dif_neg h]
theorem norm_transferredChart_sub_le (hD : Estimates.cellOffsetStatement) (hS : SiteDecomposition)
    (P : TorusPairData T x V V' Y Y' q j j') (ζ : BondField ι) (z : F'.Site F'.depth) (i : Fin 4) :
    ‖transferredChart T x V V' j j' ζ z i - chartPoint T x V' j' ζ z i‖ ≤ frameGap T q := by
  have hj := P.short.isBoxPairing.injective_left
  have hj' := P.short.isBoxPairing.injective_right
  by_cases h : ∃ k, (j' k).1 = (z, i)
  · obtain ⟨k, hk⟩ := h
    have e1 : z = (j' k).1.1 := (congrArg Prod.fst hk).symm
    have e2 : i = (j' k).1.2 := (congrArg Prod.snd hk).symm
    subst e1 e2
    rw [transferredChart_apply_pair hj']
    have a1 : chartPoint T x V j ζ (j k).1.1 (j k).1.2 =
        interpolatedFrame 1 T.a T.chainParams.ρA (frameRadius x) (j k).1 V + toImaginary (ζ k) := by
      rw [← SecondOrderMoves.stepCoordinates_toTorus_apply hj ζ k]
      rfl
    have a2 : chartPoint T x V' j' ζ (j' k).1.1 (j' k).1.2 =
        interpolatedFrame 1 T.a T.chainParams.ρA (frameRadius x) (j' k).1 V' + toImaginary (ζ k) := by
      rw [← SecondOrderMoves.stepCoordinates_toTorus_apply hj' ζ k]
      rfl
    rw [a1, a2, add_sub_add_right_eq_sub]
    exact norm_interpolatedFrame_sub_le hD hS P k
  · rw [transferredChart_apply_of_not_pair ζ h, sub_self, norm_zero]
    exact frameGap_nonneg P
theorem admissible_of_between (hD : Estimates.cellOffsetStatement) (hS : SiteDecomposition)
    (hM : ChartLipschitz.ChartedFieldLipschitz) (P : TorusPairData T x V V' Y Y' q j j') {ζ : BondField ι}
    (hζ : ∀ i, ‖ζ i‖ ≤ T.ballRadius) (v : F'.Site F'.depth → Fin 4 → imaginaryQuaternions)
    (hv : ∀ z i, ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ v z i = chartPoint T x V' j' ζ z i +
      θ • (transferredChart T x V V' j j' ζ z i - chartPoint T x V' j' ζ z i)) :
    IsAdmissibleChartPoint T.L T.chainParams.σA v V' := by
  have hj' := P.short.isBoxPairing.injective_right
  have hρ : 0 ≤ T.ballRadius := by
    have := P.σ_pos
    unfold StepParameters.ballRadius
    positivity
  have hg := frameGap_nonneg P
  have h16 := sixteen_mul_frameGap_le P
  have hmove : ∀ z i, ‖v z i - chartPoint T x V' j' ζ z i‖ ≤ frameGap T q := by
    intro z i
    obtain ⟨θ, t0, t1, e⟩ := hv z i
    rw [e, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg t0]
    have := norm_transferredChart_sub_le hD hS P ζ z i
    have h2 := norm_nonneg (transferredChart T x V V' j j' ζ z i - chartPoint T x V' j' ζ z i)
    nlinarith
  refine ⟨fun b hb => ?_, fun p hp => ?_⟩
  · have h1 := P.small'.norm_le b hb
    have h2 := SecondOrderMoves.norm_stepCoordinates_le (toTorus j' ζ) hρ
      (SecondOrderMoves.norm_toTorus_le hj' hρ hζ) b.1 b.2
    have h3 : ‖chartPoint T x V' j' ζ b.1 b.2‖ ≤ T.Ct * T.σ + T.ballRadius := by
      unfold chartPoint interpolatedCoords
      exact (norm_add_le _ _).trans (add_le_add h1 h2)
    have h4 : ‖v b.1 b.2‖ ≤ ‖chartPoint T x V' j' ζ b.1 b.2‖ + frameGap T q := by
      have := norm_add_le (v b.1 b.2 - chartPoint T x V' j' ζ b.1 b.2) (chartPoint T x V' j' ζ b.1 b.2)
      rw [sub_add_cancel] at this
      linarith [hmove b.1 b.2]
    have hs := P.σ_pos
    have h5 : T.ballRadius + frameGap T q ≤ T.σ := by
      unfold StepParameters.ballRadius
      linarith
    have h6 := P.room_le
    nlinarith
  · have hc := (hM.2 F' v (chartPoint T x V' j' ζ) V' (frameGap T q) hmove hg).2 p
    have h1 := P.small'.small_curvature_nearby (toTorus j' ζ)
      (fun b => SecondOrderMoves.norm_toTorus_le hj' hρ hζ b) p hp
    have h2 : plaquetteDefect (chartedField (chartPoint T x V' j' ζ) V') p < 3 / 4 * T.σ := h1
    have := P.σ_le
    linarith
theorem chartPoint_eq_transferredChart (hD : Estimates.cellOffsetStatement) (hS : SiteDecomposition)
    (P : TorusPairData T x V V' Y Y' q j j') (ζ : BondField ι) (h o : Fin 4 → ℤ) (i : Fin 4)
    (hh : WithinRadius (q / 2) h) (ho : o ∈ centredCube F.blockSide)
    (hb : fineBondAt Y h o i ∈ chordBonds (finiteCells F)) :
    chartPoint T x V j ζ (fineBondAt Y h o i).1 i = transferredChart T x V V' j j' ζ (fineBondAt Y' h o i).1 i := by
  have hh' : ∀ l, 2 * |h l| ≤ q := fun l => by
    have := hh l
    push_cast at this
    omega
  obtain ⟨k, e₁, e₂⟩ := exists_pair_of_small_offsets hD hS P hh' ho hb
  have a := transferredChart_apply_pair (T := T) (x := x) (V := V) (V' := V') (j := j)
    P.short.isBoxPairing.injective_right ζ k
  rw [e₁, e₂] at a
  exact a.symm
theorem card_le_of_short (P : TorusPairData T x V V' Y Y' q j j') :
    (Fintype.card ι : ℝ) ≤ 4 * (2 * (q : ℝ) + 1) ^ 4 * ((centredCube T.L).card : ℝ) := by
  classical
  have hs := fun i => P.short.short_offsets i
  choose h o k hh ho e₁ e₂ using hs
  let B : Finset (Fin 4 → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(q : ℤ)) q
  have hinj : Function.Injective fun i => (h i, o i, k i) := by
    intro i i' e
    simp only [Prod.mk.injEq] at e
    apply P.short.isBoxPairing.injective_left
    apply Subtype.ext
    rw [e₁, e₁, e.1, e.2.1, e.2.2]
  have hm : ∀ i, (h i, o i, k i) ∈ B ×ˢ (centredCube T.L ×ˢ (Finset.univ : Finset (Fin 4))) := by
    intro i
    simp only [Finset.mem_product, Finset.mem_univ, and_true]
    refine ⟨?_, ?_⟩
    · rw [Fintype.mem_piFinset]
      intro l
      have := hh i l
      have h2 := abs_le.1 (le_refl |h i l|)
      rw [Finset.mem_Icc]
      have := abs_nonneg (h i l)
      constructor <;> omega
    · rw [← P.torus.1]
      exact ho i
  have hc := Finset.card_le_card_of_injOn (s := Finset.univ)
    (t := B ×ˢ (centredCube T.L ×ˢ (Finset.univ : Finset (Fin 4))))
    (fun i => (h i, o i, k i)) (fun i _ => hm i) hinj.injOn
  have hB : (B.card : ℝ) = (2 * (q : ℝ) + 1) ^ 4 := by
    simp only [B, Fintype.card_piFinset, Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have : ((q : ℤ) + 1 - -(q : ℤ)).toNat = 2 * q + 1 := by omega
    rw [this]
    push_cast
    ring
  rw [Finset.card_univ, Finset.card_product, Finset.card_product, Finset.card_univ, Fintype.card_fin] at hc
  have hc' : (Fintype.card ι : ℝ) ≤ (B.card : ℝ) * (((centredCube T.L).card : ℝ) * 4) := by exact_mod_cast hc
  rw [hB] at hc'
  linarith
theorem abs_sub_transferredChart_le (hD : Estimates.cellOffsetStatement) (hS : SiteDecomposition)
    (hM : ChartLipschitz.ChartedFieldLipschitz) (P : TorusPairData T x V V' Y Y' q j j') {ζ : BondField ι}
    (hζ : ∀ i, ‖ζ i‖ ≤ T.ballRadius) {E : (F'.Site F'.depth → Fin 4 → imaginaryQuaternions) → ℝ} {B : ℝ}
    (hB : 0 ≤ B)
    (hline : ∀ u, IsAdmissibleChartPoint T.L T.chainParams.σA u V' → ∀ (b : F'.Site F'.depth × Fin 4)
      (X : imaginaryQuaternions), ‖X‖ = 1 → AnalyticAt ℝ (chartLine E u b X) 0 ∧ |deriv (chartLine E u b X) 0| ≤ B) :
    |E (transferredChart T x V V' j j' ζ) - E (chartPoint T x V' j' ζ)| ≤
      (Fintype.card ι : ℝ) * (B * frameGap T q) := by
  classical
  set S : Finset (F'.Site F'.depth × Fin 4) := Finset.univ.image fun k => (j' k).1 with hSdef
  have hoff : ∀ b : F'.Site F'.depth × Fin 4, b ∉ S →
      transferredChart T x V V' j j' ζ b.1 b.2 = chartPoint T x V' j' ζ b.1 b.2 := by
    intro b hb
    apply transferredChart_apply_of_not_pair
    rintro ⟨k, hk⟩
    apply hb
    rw [hSdef, Finset.mem_image]
    exact ⟨k, Finset.mem_univ _, hk⟩
  have h := abs_sub_le_sum_of_line_derivs (E := E) (D := {u | IsAdmissibleChartPoint T.L T.chainParams.σA u V'})
    (B₁ := fun _ => B) (w := chartPoint T x V' j' ζ) (w' := transferredChart T x V V' j j' ζ) S
    (fun u hu b _ X hX => hline u hu b X hX) hoff
    (fun u hu => admissible_of_between hD hS hM P hζ u hu)
  refine h.trans ?_
  calc ∑ b ∈ S, B * ‖transferredChart T x V V' j j' ζ b.1 b.2 - chartPoint T x V' j' ζ b.1 b.2‖
      ≤ ∑ _b ∈ S, B * frameGap T q := Finset.sum_le_sum fun b _ =>
        mul_le_mul_of_nonneg_left (norm_transferredChart_sub_le hD hS P ζ b.1 b.2) hB
    _ = (S.card : ℝ) * (B * frameGap T q) := by simp
    _ ≤ (Fintype.card ι : ℝ) * (B * frameGap T q) := by
        have h1 : S.card ≤ Fintype.card ι := by
          rw [hSdef]
          exact Finset.card_image_le.trans (le_of_eq Finset.card_univ)
        have h2 : (S.card : ℝ) ≤ Fintype.card ι := by exact_mod_cast h1
        exact mul_le_mul_of_nonneg_right h2 (mul_nonneg hB (frameGap_nonneg P))
theorem chartPoint_add_single (hE : (F.Site F.depth → Fin 4 → imaginaryQuaternions) → ℝ) (ζ : BondField ι) (i : ι)
    (e : BondVector) (τ : ℝ) :
    hE (chartPoint T x V j (ζ + Pi.single i (τ • e))) =
      chartLine hE (chartPoint T x V j ζ) (j i).1 (toImaginary e) τ := by
  unfold chartPoint
  have : toTorus j (ζ + Pi.single i (τ • e)) = toTorus j ζ + Pi.single (j i) (τ • e) :=
    extendByZero_add_single j Finset.univ (Finset.mem_univ i) ζ (τ • e)
  rw [this]
  exact comp_interpolatedCoords_add_single hE 1 T.a T.chainParams.ρA (frameRadius x) V (toTorus j ζ) (j i) e τ
end Transfer
section Values
variable {ι : Type} [Fintype ι] [DecidableEq ι] {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {x : ℝ} {V : F.GaugeField F.top}
  {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell} {q : ℕ} {j : ι → ↥(chordBonds (finiteCells F))}
  {j' : ι → ↥(chordBonds (finiteCells F'))}
def countConstant (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) : ℝ :=
  4 * ((centredCube T.L).card : ℝ) * ((128 / T.chainParams.δ₂) ^ 4 * Real.exp (T.chainParams.δ₂ / 32)) *
    (T.Ct * T.σ)
theorem countConstant_nonneg (P : TorusPairData T x V V' Y Y' q j j') : 0 ≤ countConstant T := by
  have := P.σ_pos
  have := P.Ct_pos
  have := P.δ₂_pos
  unfold countConstant
  positivity
def valueRate (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) : ℝ := T.chainParams.δ₂ / 16
theorem card_mul_frameGap_le (P : TorusPairData T x V V' Y Y' q j j') {B : ℝ} (hB : 0 ≤ B) :
    (Fintype.card ι : ℝ) * (B * frameGap T q) ≤ B * countConstant T * Real.exp (-(valueRate T * q)) := by
  have hδ := P.δ₂_pos
  have h1 := card_le_of_short P
  have h2 := SecondOrderMoves.pow_four_mul_exp_le hδ q
  have hg := frameGap_nonneg P
  have hσ := P.σ_pos
  have hC := P.Ct_pos
  calc (Fintype.card ι : ℝ) * (B * frameGap T q)
      ≤ (4 * (2 * (q : ℝ) + 1) ^ 4 * ((centredCube T.L).card : ℝ)) * (B * frameGap T q) :=
        mul_le_mul_of_nonneg_right h1 (mul_nonneg hB hg)
    _ = B * (4 * ((centredCube T.L).card : ℝ) * (T.Ct * T.σ)) *
        ((2 * (q : ℝ) + 1) ^ 4 * Real.exp (-(T.chainParams.δ₂ / 8 * q))) := by
        unfold frameGap
        ring
    _ ≤ B * (4 * ((centredCube T.L).card : ℝ) * (T.Ct * T.σ)) *
        ((128 / T.chainParams.δ₂) ^ 4 * Real.exp (T.chainParams.δ₂ / 32) *
          Real.exp (-(T.chainParams.δ₂ / 16 * q))) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by
        unfold countConstant valueRate
        ring
theorem exp_half_radius_le (P : TorusPairData T x V V' Y Y' q j j') :
    Real.exp (-(T.chainParams.δ₁ * ((q / 2 : ℕ) : ℝ))) ≤ 2 * Real.exp (-(valueRate T * q)) := by
  have hδ := P.δ₂_pos
  obtain ⟨l1, l2, -⟩ := P.admissible.inequalities
  have hq : (q : ℝ) ≤ 2 * ((q / 2 : ℕ) : ℝ) + 1 := by
    have : q ≤ 2 * (q / 2) + 1 := by omega
    exact_mod_cast this
  have h1 : -(T.chainParams.δ₁ * ((q / 2 : ℕ) : ℝ)) ≤ Real.log 2 + -(valueRate T * q) := by
    have : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    unfold valueRate
    nlinarith
  calc Real.exp (-(T.chainParams.δ₁ * ((q / 2 : ℕ) : ℝ))) ≤ Real.exp (Real.log 2 + -(valueRate T * q)) :=
        Real.exp_le_exp.2 h1
    _ = _ := by rw [Real.exp_add, Real.exp_log (by norm_num)]
theorem exp_mul_sum_norm_le_weight (P : TorusPairData T x V V' Y Y' q j j') (ζ : BondField ι) :
    Real.exp (-(valueRate T / 2 * q)) * ∑ i, ‖ζ i‖ ≤ Real.exp (-(4 * T.κ * q)) * weightedBondNorm T.κ Y j ζ := by
  unfold weightedBondNorm
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← mul_assoc, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (norm_nonneg _)
  have hm : (j i) ∈ bondsNearCell Y q := (P.short.isBoxPairing.mem_left_iff (j i)).2 ⟨i, rfl⟩
  simp only [bondsNearCell, Finset.mem_filter, Finset.mem_univ, true_and] at hm
  have hd : 2 * bondDistToCell Y (j i) ≤ q := by
    unfold bondDistToCell
    exact_mod_cast hm
  have hκ := P.κ_pos
  have hκ2 := P.κ_le
  unfold valueRate
  nlinarith
def CellEnergyComparison (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (C : ℝ) : Prop :=
  ∀ (F F' : BlockFrame) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (w' : F'.Site F'.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top)
    (Y : F.Cell) (Y' : F'.Cell) (r : ℕ), 1 ≤ r → IsBlockTorus T.L F → IsBlockTorus T.L F' →
    F'.depth = F.depth → IsAdmissibleChartPoint T.L T.chainParams.σA w V →
    IsAdmissibleChartPoint T.L T.chainParams.σA w' V' →
    AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r →
    (∀ (h o : Fin 4 → ℤ) (i : Fin 4), WithinRadius r h → o ∈ centredCube T.L →
      fineBondAt Y h o i ∈ chordBonds (finiteCells F) →
      w (fineBondAt Y h o i).1 i = w' (fineBondAt Y' h o i).1 i) →
    |cellEnergyShare T.a Y w V - cellEnergyShare T.a Y' w' V'| ≤ C * Real.exp (-(T.chainParams.δ₁ * r))
def ChartComparison (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (C : ℝ) : Prop :=
  ∀ (F F' : BlockFrame) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (w' : F'.Site F'.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top)
    (Y : F.Cell) (Y' : F'.Cell) (r : ℕ), 1 ≤ r → IsBlockTorus T.L F → IsBlockTorus T.L F' →
    F'.depth = F.depth → IsAdmissibleChartPoint T.L T.chainParams.σA w V →
    IsAdmissibleChartPoint T.L T.chainParams.σA w' V' →
    AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r →
    (∀ (h o : Fin 4 → ℤ) (i : Fin 4), WithinRadius r h → o ∈ centredCube T.L →
      fineBondAt Y h o i ∈ chordBonds (finiteCells F) →
      w (fineBondAt Y h o i).1 i = w' (fineBondAt Y' h o i).1 i) →
    (∀ o ∈ centredCube T.L, |minimalSiteShare T.a (cellCentre F.depth Y + siteOfCoords F.depth o) (chartedField w V) -
      minimalSiteShare T.a (cellCentre F'.depth Y' + siteOfCoords F'.depth o) (chartedField w' V')| ≤
        C * Real.exp (-(T.chainParams.δ₁ * r))) ∧
    ∀ (g : Fin 4 → ℤ) (d : Fin 4), WithinRadius r g → WithinRadius r (g + Pi.single d 1) →
      _root_.YangMills.Construction.BlockAverages.contourAverage (chartedField w V) ((Y + siteOfCoords F.top g, d) : F.Site (F.depth + 1) × Fin 4) =
        _root_.YangMills.Construction.BlockAverages.contourAverage (chartedField w' V') ((Y' + siteOfCoords F'.top g, d) : F'.Site (F'.depth + 1) × Fin 4)
def CellEnergyKernels (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (Ck : ℕ → ℝ) : Prop :=
  ∀ (F : BlockFrame) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top),
    IsBlockTorus T.L F → IsAdmissibleChartPoint T.L T.chainParams.σA w V →
    ∀ (Y : F.Cell) (k : ℕ) (q : Fin k → ChartDirection F),
      AnalyticAt ℝ (cellEnergyAlong T.a Y w V q) 0 ∧
      (1 ≤ k → (∀ l, ‖directionVector (q l)‖ = 1) →
        |cellEnergyKernel T.a Y w V q| ≤ Ck k * Real.exp (-(T.chainParams.δ₁ * directionReach Y q)))
def SiteShareKernels (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (Ck : ℕ → ℝ) : Prop :=
  ∀ (F : BlockFrame) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top),
    IsBlockTorus T.L F → IsAdmissibleChartPoint T.L T.chainParams.σA w V →
    ∀ (y : F.Site F.depth) (k : ℕ) (q : Fin k → ChartDirection F),
      AnalyticAt ℝ (siteShareAlong T.a y w V q) 0 ∧
      (1 ≤ k → (∀ l, ‖directionVector (q l)‖ = 1) →
        |siteShareMixedDeriv T.a y w V q| ≤
          Ck k * Real.exp (-(T.chainParams.δ₁ * directionReach (enclosingCell y) q)))
theorem TorusPairData.agreeOnBall_half (P : TorusPairData T x V V' Y Y' q j j') :
    AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' (q / 2) := by
  obtain ⟨a1, a2, a3, a4⟩ := P.agree
  have hin : ∀ {h : Fin 4 → ℤ}, WithinRadius (q / 2) h → WithinRadius q h := fun {h} hh i => by
    have := hh i
    push_cast at this
    omega
  refine ⟨fun i => Or.inr ?_, fun i => Or.inr ?_, fun h hh => a3 h (hin hh), fun b hb => a4 b ⟨hin hb.1, hin hb.2⟩⟩
  · have := P.extent_gt i
    omega
  · have := P.extent_gt' i
    omega
theorem TorusPairData.one_le_half (P : TorusPairData T x V V' Y Y' q j j') : 1 ≤ q / 2 := by
  have := P.two_le
  omega
theorem exp_neg_δ₁_le_one (P : TorusPairData T x V V' Y Y' q j j') (d : ℕ) :
    Real.exp (-(T.chainParams.δ₁ * d)) ≤ 1 := by
  have h := P.admissible.positivity.1
  apply Real.exp_le_one_iff.2
  have : 0 ≤ T.chainParams.δ₁ * d := by positivity
  linarith
def valueConstant (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (A B : ℝ) : ℝ := 2 * A + B * countConstant T + 1
theorem valueConstant_pos (P : TorusPairData T x V V' Y Y' q j j') {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 < valueConstant T A B := by
  have := countConstant_nonneg P
  unfold valueConstant
  positivity
theorem abs_cellEnergyShare_sub_le (hD : Estimates.cellOffsetStatement) (hS : SiteDecomposition)
    (hM : ChartLipschitz.ChartedFieldLipschitz) (hc : Calculus.CompositeDerivativesAtPoint)
    (P : TorusPairData T x V V' Y Y' q j j') {C : ℝ} {Ck : ℕ → ℝ} (hC : 0 ≤ C) (hCk : ∀ k, 0 < Ck k)
    (hB : CellEnergyComparison T C) (hK : CellEnergyKernels T Ck) {ζ : BondField ι}
    (hζ : ∀ i, ‖ζ i‖ ≤ T.ballRadius) :
    |cellEnergyShare T.a Y (chartPoint T x V j ζ) V - cellEnergyShare T.a Y' (chartPoint T x V' j' ζ) V'| ≤
      valueConstant T C (Ck 1) * Real.exp (-(valueRate T * q)) := by
  have hw := hB F F' (chartPoint T x V j ζ) (transferredChart T x V V' j j' ζ) V V' Y Y' (q / 2) P.one_le_half
    P.torus P.torus' P.depth_eq
    (chartPoint_admissible P.short.isBoxPairing.injective_left P.small P.σ_pos hζ P.room_le P.σ_le)
    (admissible_of_between hD hS hM P hζ _ fun z i => ⟨1, zero_le_one, le_rfl, by simp⟩) P.agreeOnBall_half
    (fun h o i hh ho hb => chartPoint_eq_transferredChart hD hS P ζ h o i hh (by rw [P.torus.1]; exact ho) hb)
  have hn := abs_sub_transferredChart_le hD hS hM P hζ (E := fun u => cellEnergyShare T.a Y' u V') (hCk 1).le
    (fun u hu b X hX => by
    obtain ⟨h1, h2, -⟩ := cellEnergyShare_line_bounds hc (fun k l => hK F' u V' P.torus' hu Y' k l) b hX
    refine ⟨h1, h2.trans ?_⟩
    have := exp_neg_δ₁_le_one P (cellSupDist Y' (enclosingCell b.1))
    have := hCk 1
    nlinarith)
  have h3 := card_mul_frameGap_le P (hCk 1).le (ι := ι)
  have h4 := exp_half_radius_le P
  have h5 := abs_sub_le (cellEnergyShare T.a Y (chartPoint T x V j ζ) V)
    (cellEnergyShare T.a Y' (transferredChart T x V V' j j' ζ) V')
    (cellEnergyShare T.a Y' (chartPoint T x V' j' ζ) V')
  have he := Real.exp_pos (-(valueRate T * q))
  unfold valueConstant
  nlinarith
theorem abs_minimalSiteShare_sub_le (hD : Estimates.cellOffsetStatement) (hS : SiteDecomposition)
    (hM : ChartLipschitz.ChartedFieldLipschitz) (hc : Calculus.CompositeDerivativesAtPoint)
    (P : TorusPairData T x V V' Y Y' q j j') {C : ℝ} {Ck : ℕ → ℝ} (hC : 0 ≤ C) (hCk : ∀ k, 0 < Ck k)
    (hB : ChartComparison T C) (hK : SiteShareKernels T Ck) {ζ : BondField ι} (hζ : ∀ i, ‖ζ i‖ ≤ T.ballRadius)
    {o : Fin 4 → ℤ} (ho : o ∈ centredCube T.L) :
    |minimalSiteShare T.a (cellCentre F.depth Y + siteOfCoords F.depth o) (chartedField (chartPoint T x V j ζ) V) -
      minimalSiteShare T.a (cellCentre F'.depth Y' + siteOfCoords F'.depth o)
        (chartedField (chartPoint T x V' j' ζ) V')| ≤
      valueConstant T C (Ck 1) * Real.exp (-(valueRate T * q)) := by
  have hw := (hB F F' (chartPoint T x V j ζ) (transferredChart T x V V' j j' ζ) V V' Y Y' (q / 2) P.one_le_half
    P.torus P.torus' P.depth_eq
    (chartPoint_admissible P.short.isBoxPairing.injective_left P.small P.σ_pos hζ P.room_le P.σ_le)
    (admissible_of_between hD hS hM P hζ _ fun z i => ⟨1, zero_le_one, le_rfl, by simp⟩) P.agreeOnBall_half
    (fun h o i hh ho hb => chartPoint_eq_transferredChart hD hS P ζ h o i hh (by rw [P.torus.1]; exact ho) hb)).1 o ho
  have hn := abs_sub_transferredChart_le hD hS hM P hζ
    (E := fun u => minimalSiteShare T.a (cellCentre F'.depth Y' + siteOfCoords F'.depth o) (chartedField u V'))
    (hCk 1).le (fun u hu b X hX => by
    obtain ⟨h1, h2, -⟩ := minimalSiteShare_line_bounds hc
      (fun k l => hK F' u V' P.torus' hu (cellCentre F'.depth Y' + siteOfCoords F'.depth o) k l) b hX
    refine ⟨h1, h2.trans ?_⟩
    have := exp_neg_δ₁_le_one P
      (cellSupDist (enclosingCell (cellCentre F'.depth Y' + siteOfCoords F'.depth o)) (enclosingCell b.1))
    have := hCk 1
    nlinarith)
  have h3 := card_mul_frameGap_le P (hCk 1).le (ι := ι)
  have h4 := exp_half_radius_le P
  have h5 := abs_sub_le
    (minimalSiteShare T.a (cellCentre F.depth Y + siteOfCoords F.depth o) (chartedField (chartPoint T x V j ζ) V))
    (minimalSiteShare T.a (cellCentre F'.depth Y' + siteOfCoords F'.depth o)
      (chartedField (transferredChart T x V V' j j' ζ) V'))
    (minimalSiteShare T.a (cellCentre F'.depth Y' + siteOfCoords F'.depth o)
      (chartedField (chartPoint T x V' j' ζ) V'))
  have he := Real.exp_pos (-(valueRate T * q))
  unfold valueConstant
  nlinarith
theorem abs_move_sub_le (P : TorusPairData T x V V' Y Y' q j j')
    {E : (F.Site F.depth → Fin 4 → imaginaryQuaternions) → ℝ}
    {E' : (F'.Site F'.depth → Fin 4 → imaginaryQuaternions) → ℝ} {K A : ℝ} (hK : 0 < K) (hA : 0 ≤ A)
    (hval : ∀ ζ : BondField ι, (∀ i, ‖ζ i‖ ≤ T.ballRadius) →
      |E (chartPoint T x V j ζ) - E' (chartPoint T x V' j' ζ)| ≤ K * Real.exp (-(valueRate T * q)))
    (hl : ∀ u, IsAdmissibleChartPoint T.L T.chainParams.σA u V → ∀ (b : F.Site F.depth × Fin 4)
      (X : imaginaryQuaternions), ‖X‖ = 1 →
      AnalyticAt ℝ (chartLine E u b X) 0 ∧ |deriv (deriv (chartLine E u b X)) 0| ≤ A)
    (hl' : ∀ u, IsAdmissibleChartPoint T.L T.chainParams.σA u V' → ∀ (b : F'.Site F'.depth × Fin 4)
      (X : imaginaryQuaternions), ‖X‖ = 1 →
      AnalyticAt ℝ (chartLine E' u b X) 0 ∧ |deriv (deriv (chartLine E' u b X)) 0| ≤ A)
    {ζ : BondField ι} (hζ : ∀ i, ‖ζ i‖ < T.ballRadius) :
    |(E (chartPoint T x V j ζ) - E' (chartPoint T x V' j' ζ)) -
      (E (chartPoint T x V j 0) - E' (chartPoint T x V' j' 0))| ≤
      Real.exp (-(4 * T.κ * q)) *
        (SecondOrderMoves.bondMoveConstant K (2 * A) T.ballRadius * weightedBondNorm T.κ Y j ζ) := by
  have hρ : 0 < T.ballRadius := by
    have := P.σ_pos
    unfold StepParameters.ballRadius
    positivity
  have hr : 0 ≤ valueRate T := by
    have := P.δ₂_pos
    unfold valueRate
    positivity
  have h := SecondOrderMoves.abs_sub_zero_le_of_exp_small
    (g := fun ζ => E (chartPoint T x V j ζ) - E' (chartPoint T x V' j' ζ)) (q := q) hρ hK
    (by positivity : 0 ≤ 2 * A) hr
    (fun ζ hζ => hval ζ fun i => (hζ i).le) (fun ζ hζ i e he => by
      have hX : ‖toImaginary e‖ = 1 := by rw [SecondOrderMoves.norm_toImaginary, he]
      have e1 : (fun τ : ℝ => E (chartPoint T x V j (ζ + Pi.single i (τ • e))) -
          E' (chartPoint T x V' j' (ζ + Pi.single i (τ • e)))) =
          fun τ => chartLine E (chartPoint T x V j ζ) (j i).1 (toImaginary e) τ -
            chartLine E' (chartPoint T x V' j' ζ) (j' i).1 (toImaginary e) τ := by
        funext τ
        rw [chartPoint_add_single E ζ i e τ, chartPoint_add_single E' ζ i e τ]
      have s1 := chartPoint_admissible P.short.isBoxPairing.injective_left P.small P.σ_pos
        (fun i => (hζ i).le) P.room_le P.σ_le
      have s2 := chartPoint_admissible P.short.isBoxPairing.injective_right P.small' P.σ_pos
        (fun i => (hζ i).le) P.room_le P.σ_le
      obtain ⟨a1, b1⟩ := hl _ s1 (j i).1 _ hX
      obtain ⟨a2, b2⟩ := hl' _ s2 (j' i).1 _ hX
      rw [e1]
      refine ⟨a1.contDiffAt.sub a2.contDiffAt, ?_⟩
      rw [SecondOrderMoves.deriv_deriv_sub a1.contDiffAt a2.contDiffAt]
      exact (abs_sub _ _).trans (by linarith)) hζ
  refine h.trans ?_
  have hm : 0 ≤ SecondOrderMoves.bondMoveConstant K (2 * A) T.ballRadius :=
    SecondOrderMoves.bondMoveConstant_nonneg hK.le (by positivity) hρ
  have h2 := mul_le_mul_of_nonneg_left (exp_mul_sum_norm_le_weight P ζ) hm
  calc SecondOrderMoves.bondMoveConstant K (2 * A) T.ballRadius * Real.exp (-(valueRate T / 2 * q)) * ∑ i, ‖ζ i‖
      = SecondOrderMoves.bondMoveConstant K (2 * A) T.ballRadius *
          (Real.exp (-(valueRate T / 2 * q)) * ∑ i, ‖ζ i‖) := by ring
    _ ≤ SecondOrderMoves.bondMoveConstant K (2 * A) T.ballRadius *
          (Real.exp (-(4 * T.κ * q)) * weightedBondNorm T.κ Y j ζ) := h2
    _ = _ := by ring
theorem chartPoint_zero (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (x : ℝ) (V : F.GaugeField F.top) (j : ι → ↥(chordBonds (finiteCells F))) :
    chartPoint T x V j (0 : BondField ι) = interpolatedCoords 1 T.a T.chainParams.ρA (frameRadius x) V 0 := by
  unfold chartPoint
  rw [SecondOrderMoves.toTorus_zero]
end Values
end ChartTransfer
end YangMills.Construction
end
