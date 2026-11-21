import YangMills.Construction.ClusterExpansionOfAStep.PlaquettesUnderGaugesAndMoves
import YangMills.Construction.ColdChainAtEveryLevel.LinesOfTheBlocksOfABond
import YangMills.Construction.ColdStepAtMirrorFrames.BoundsOfTheExponentsOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.SumOfTheSharesProof
import YangMills.Construction.SummableBoundsOfTheFlow.ExponentBetweenBoundsProof
import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenAtTheirEnds
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages YangMills.Construction.Interpolation YangMills.Construction.IteratedDerivative YangMills.Construction.Estimates YangMills.Construction.ScaledVariables YangMills.Construction.CellCounting
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace ExponentBoundsAux
variable {F : BlockFrame}
theorem eventually_with_chosen_rate (P : StepParameters → Prop) (hP : EventuallyInParameters P) :
    ∃ St : ℝ → ℕ → ColdChainParameters → ℝ × ℝ, (∀ a L c, 0 < (St a L c).2) ∧
      EventuallyInParameters fun T =>
        P { T with Ct := (St T.a T.L T.chainParams).1, κ := (St T.a T.L T.chainParams).2 } := by
  classical
  let Tail : ℝ → ℕ → ColdChainParameters → ℝ → ℝ → Prop := fun a L c Ct κ =>
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η₃ : ℝ, 0 < η₃ → η₃ ≤ 1 → η₃ ≤ η₀ →
    ∃ N₀ : ℕ, ∀ m : ℕ, N₀ ≤ m →
    ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∀ σ : ℝ, 0 < σ → σ ≤ σ₀ →
    ∀ p : ℝ → ℝ, IsCutoff (σ / 64) p →
    ∃ C₀ : ℝ, ∀ Cs : ℝ, C₀ ≤ Cs →
    ∀ E : ℝ, 1 ≤ E →
    ∃ m₀ : ℕ, ∀ n₀ : ℕ, m₀ ≤ n₀ →
    ∃ C₁ : ℝ, ∀ CE : ℝ, C₁ ≤ CE →
    ∃ y₀ : ℝ, ∀ y₁ : ℝ, y₀ ≤ y₁ →
      P ⟨a, L, c, Ct, κ, η₃, m, σ, p, Cs, E, n₀, CE, y₁⟩
  have hex : ∀ (a : ℝ) (L : ℕ) (c : ColdChainParameters), ∃ q : ℝ × ℝ, 0 < q.2 ∧
      ((∃ Ct₀ : ℝ, ∀ Ct : ℝ, Ct₀ ≤ Ct → ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ → Tail a L c Ct κ) →
        Tail a L c q.1 q.2) := by
    intro a L c
    by_cases h : ∃ Ct₀ : ℝ, ∀ Ct : ℝ, Ct₀ ≤ Ct → ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ → Tail a L c Ct κ
    · obtain ⟨Ct₀, h1⟩ := h
      obtain ⟨κ₀, h2, h3⟩ := h1 Ct₀ le_rfl
      exact ⟨(Ct₀, κ₀), h2, fun _ => h3 κ₀ h2 le_rfl⟩
    · exact ⟨(0, 1), one_pos, fun h' => absurd h' h⟩
  choose St hpos hSt using hex
  refine ⟨St, hpos, ?_⟩
  intro a ha
  obtain ⟨L₀, hL⟩ := hP a ha
  refine ⟨L₀, fun L hLo hLL c hc => ?_⟩
  obtain ⟨η₀, hη₀, h⟩ := hSt a L c (hL L hLo hLL c hc)
  exact ⟨0, fun _ _ => ⟨1, one_pos, fun _ _ _ => ⟨η₀, hη₀, h⟩⟩⟩
theorem decayingKernel_mono {l j : ℕ} {G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ} {B r r' : ℝ}
    {P : Finset F.Cell} {η : StepVariable (finiteCells F)} {V : F.GaugeField F.top}
    {b : Fin l → ↥(chordBonds (finiteCells F))} {v : Fin l → EuclideanSpace ℝ (Fin 3)}
    {c : Fin j → F.Site F.top × Fin 4} {X : Fin j → imaginaryQuaternions} (hB : 0 ≤ B) (hr : r ≤ r')
    (h : HasDecayingKernelAt G B r' P η V b v c X) : HasDecayingKernelAt G B r P η V b v c X := by
  refine ⟨h.1, h.2.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hB)⟩
  have : (0 : ℝ) ≤ (cellSetDiameter (P ∪ chordBondCells b ∪ topBondCells c) : ℝ) := Nat.cast_nonneg _
  nlinarith
theorem interpolationKernels_mono {s a ρA κ κ' κ₂ rE x : ℝ} {m : ℕ} {K : ℕ → ℝ} {D : ℕ → ℕ → ℝ}
    {V : F.GaugeField F.top} {η : StepVariable (finiteCells F)} (hD : ∀ l j, 0 ≤ D l j) (hκ : κ ≤ κ')
    (h : HasInterpolationKernels s a ρA κ' κ₂ rE x m K D V η) :
    HasInterpolationKernels s a ρA κ κ₂ rE x m K D V η := by
  have hr : (2 : ℝ) ^ 8 * κ ≤ 2 ^ 8 * κ' := by nlinarith
  exact ⟨h.analytic, h.frame_deriv, h.energy,
    fun c₀ l j b v c X h1 h2 h3 => decayingKernel_mono (hD l j) hr (h.logContour c₀ l j b v c X h1 h2 h3),
    fun c₀ l j b v c X h1 h2 h3 => decayingKernel_mono (hD l j) hr (h.gap c₀ l j b v c X h1 h2 h3),
    fun b₀ l j b v c X h1 h2 h3 => decayingKernel_mono (hD l j) hr (h.haar b₀ l j b v c X h1 h2 h3)⟩
theorem card_cellChordBonds_le (hB : SiteDecomposition) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (z : F.Cell) : (cellChordBonds z).card ≤ (centredCube F.blockSide).card * 4 := by apply _root_.YangMills.Construction.Interpolation.ExponentBoundSteps.card_cellChordBonds_le <;> assumption
theorem chordBonds_nonempty (hB : SiteDecomposition) (hC : BlocksCoverLowerLevel) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) : Nonempty ↥(chordBonds (finiteCells F)) := by apply _root_.YangMills.Construction.Interpolation.ExponentBoundSteps.nonempty_chordBonds <;> assumption
def derivBoundTotal (D : ℕ → ℕ → ℝ) : ℝ := ∑ l ∈ Finset.range 4, ∑ j ∈ Finset.range 4, D l j
theorem derivBoundTotal_nonneg {D : ℕ → ℕ → ℝ} (h : ∀ l j, 0 < D l j) : 0 ≤ derivBoundTotal D := by apply _root_.YangMills.Construction.Interpolation.ExponentBoundSteps.derivBoundSum_nonneg <;> assumption
theorem le_derivBoundTotal {D : ℕ → ℕ → ℝ} (h : ∀ l j, 0 < D l j) (l j : ℕ) (hl : l ≤ 3) (hj : j ≤ 3) :
    D l j ≤ derivBoundTotal D := by apply _root_.YangMills.Construction.Interpolation.ExponentBoundSteps.le_derivBoundSum <;> assumption
structure ConstantsFit (Ds : ℝ → ℕ → ColdChainParameters → ℕ → ℕ → ℝ) (κs : ℝ → ℕ → ColdChainParameters → ℝ)
    (Cg : ℝ) (T : StepParameters) : Prop where
  two_le_n₀ : 2 ≤ T.n₀
  rate_le : 2 ^ 10 * T.κ ≤ T.chainParams.δ₂
  rate_le_chosen : T.κ ≤ κs T.a T.L T.chainParams
  one_le_Ct : 1 ≤ T.Ct
  small_radius : T.Ct * T.σ + 5 * (T.L : ℝ) * T.ballRadius ≤ 1 / 2
  gap_decay : ∀ x, T.coupling ≤ x → 2 ≤ x ∧ x * (T.Ct * frameGapBound T (frameRadius x)) ≤ 1
  weight_sums : ∃ Wt : ℝ, (∀ F : BlockFrame, F.blockSide = T.L → (∀ i, 2 ≤ F.extent i) → ∀ z : F.Cell,
      ∑ b : ↥(chordBonds (finiteCells F)),
        Real.exp (-(T.chainParams.δ₂ / 2 * (cellSupDist (enclosingCell b.1.1) z : ℝ))) ≤ Wt) ∧
    ((((centredCube T.L).card * 4 : ℕ) : ℝ) * T.ballRadius +
      (Wt + (((centredCube T.L).card * 4 : ℕ) : ℝ)) / 2 * derivBoundTotal (Ds T.a T.L T.chainParams) +
      4 * (Cg + derivBoundTotal (Ds T.a T.L T.chainParams)) +
      (((centredCube T.L).card * 4 : ℕ) : ℝ) * (1 + derivBoundTotal (Ds T.a T.L T.chainParams)) ≤ T.Ct) ∧
    (derivBoundTotal (Ds T.a T.L T.chainParams) * ((((centredCube T.L).card * 4 : ℕ) : ℝ) + 1) + 1 +
      derivBoundTotal (Ds T.a T.L T.chainParams) * (Wt + 1) + 4 * derivBoundTotal (Ds T.a T.L T.chainParams) +
      (((centredCube T.L).card * 4 : ℕ) : ℝ) * derivBoundTotal (Ds T.a T.L T.chainParams) ≤ T.Ct) ∧
    ((((centredCube T.L).card * 4 : ℕ) : ℝ) * T.ballRadius * derivBoundTotal (Ds T.a T.L T.chainParams) +
      2 * derivBoundTotal (Ds T.a T.L T.chainParams) + 4 * derivBoundTotal (Ds T.a T.L T.chainParams) +
      (((centredCube T.L).card * 4 : ℕ) : ℝ) * derivBoundTotal (Ds T.a T.L T.chainParams) ≤ T.Ct)
theorem eventually_constantsFit (hF : frameRadiusGrowthStatement) (hS : ExpDecaySumBounded)
    (hB : SiteDecomposition) (Ds : ℝ → ℕ → ColdChainParameters → ℕ → ℕ → ℝ)
    (κs : ℝ → ℕ → ColdChainParameters → ℝ) (Cg : ℝ) (hD : ∀ a L c l j, 0 < Ds a L c l j)
    (hκs : ∀ a L c, 0 < κs a L c) : EventuallyInParameters (ConstantsFit Ds κs Cg) := by
  intro a _
  refine ⟨0, fun L hL _ c hc => ?_⟩
  have hδ : 0 < c.δ₂ := hc.classical.1.2.2.2.1
  obtain ⟨W₀, hW0, hW⟩ := hS ((centredCube L).card * 4) (c.δ₂ / 2) (by positivity)
  set Dm := derivBoundTotal (Ds a L c) with hDm
  have hDm0 : 0 ≤ Dm := derivBoundTotal_nonneg (hD a L c)
  set Nb : ℝ := (((centredCube L).card * 4 : ℕ) : ℝ) with hNb
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  refine ⟨max 1 (max (max (Nb + (W₀ + Nb) / 2 * Dm + 4 * (Cg + Dm) + Nb * (1 + Dm))
      (Dm * (Nb + 1) + 1 + Dm * (W₀ + 1) + 4 * Dm + Nb * Dm))
      (Nb * Dm + 2 * Dm + 4 * Dm + Nb * Dm)), fun Ct hCt => ?_⟩
  have hCt1 : 1 ≤ Ct := (le_max_left _ _).trans hCt
  have hCt2 := (le_max_right _ _).trans hCt
  refine ⟨min (c.δ₂ / 2 ^ 10) (κs a L c), lt_min (by positivity) (hκs a L c), fun κ hκ hκle => ?_⟩
  refine ⟨1, one_pos, fun η₃ _ _ _ => ?_⟩
  refine ⟨0, fun m _ => ?_⟩
  have hCL : 0 < Ct + L := by linarith
  refine ⟨1 / (2 * (Ct + L)), by positivity, fun σ hσ hσle p _ => ?_⟩
  have h1 : (Ct + L) * σ ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left hσle hCL.le
    have e : (Ct + L) * (1 / (2 * (Ct + L))) = 1 / 2 := by field_simp
    linarith
  have hσ1 : σ ≤ 1 := by nlinarith
  refine ⟨0, fun Cs _ E _ => ?_⟩
  refine ⟨2, fun n₀ hn₀ => ?_⟩
  refine ⟨0, fun CE _ => ?_⟩
  obtain ⟨y, hy1, hy⟩ := hF (Ct ^ 2 + 1) (c.δ₂ / 4) (by positivity) (by positivity)
  refine ⟨max y 2, fun y₁ hy₁ => ?_⟩
  refine ⟨hn₀, ?_, ?_, hCt1, ?_, ?_, ?_⟩
  · change 2 ^ 10 * κ ≤ c.δ₂
    have := mul_le_mul_of_nonneg_left (hκle.trans (min_le_left _ _)) (by positivity : (0 : ℝ) ≤ 2 ^ 10)
    have e : (2 : ℝ) ^ 10 * (c.δ₂ / 2 ^ 10) = c.δ₂ := by ring
    linarith
  · exact hκle.trans (min_le_right _ _)
  · change Ct * σ + 5 * (L : ℝ) * (σ / 64) ≤ 1 / 2
    have h2 : 5 * (L : ℝ) * (σ / 64) ≤ L * σ := by nlinarith [mul_nonneg hL0 hσ.le]
    nlinarith
  · intro x hx
    have hx' : y₁ ≤ x := hx
    have hxy : y ≤ x := ((le_max_left _ _).trans hy₁).trans hx'
    have hx2 : 2 ≤ x := ((le_max_right _ _).trans hy₁).trans hx'
    refine ⟨hx2, ?_⟩
    have h1 := (hy x hxy).1
    change x * (Ct * (Ct * Real.exp (-(c.δ₂ / 4 * (frameRadius x : ℝ))))) ≤ 1
    have he := Real.exp_pos (-(c.δ₂ / 4 * (frameRadius x : ℝ)))
    have h2 : x * (Ct * (Ct * Real.exp (-(c.δ₂ / 4 * (frameRadius x : ℝ))))) ≤
        (Ct ^ 2 + 1) * x ^ 2 * Real.exp (-(c.δ₂ / 4 * (frameRadius x : ℝ))) := by
      have hxx : x ≤ x ^ 2 := by nlinarith
      have h3 : x * Ct ^ 2 ≤ (Ct ^ 2 + 1) * x ^ 2 := by
        calc x * Ct ^ 2 = Ct ^ 2 * x := by ring
          _ ≤ Ct ^ 2 * x ^ 2 := mul_le_mul_of_nonneg_left hxx (sq_nonneg _)
          _ ≤ (Ct ^ 2 + 1) * x ^ 2 := by nlinarith [sq_nonneg x]
      have := mul_le_mul_of_nonneg_right h3 he.le
      nlinarith
    exact h2.trans h1
  · refine ⟨W₀, ?_, ?_, ?_, ?_⟩
    · intro F hFL hs z
      change ∑ b : ↥(chordBonds (finiteCells F)),
        Real.exp (-(c.δ₂ / 2 * (cellSupDist (enclosingCell b.1.1) z : ℝ))) ≤ W₀
      have hLF : Odd F.blockSide := hFL ▸ hL
      refine hW F ↥(chordBonds (finiteCells F)) (fun b => enclosingCell b.1.1) (fun z' => ?_) z
      have := card_cellChordBonds_le hB hLF hs z'
      rw [hFL] at this
      exact this
    · change Nb * (σ / 64) + (W₀ + Nb) / 2 * Dm + 4 * (Cg + Dm) + Nb * (1 + Dm) ≤ Ct
      have h3 := ((le_max_left _ _).trans (le_max_left _ _)).trans hCt2
      have h4 : Nb * (σ / 64) ≤ Nb := by nlinarith
      linarith
    · exact ((le_max_right _ _).trans (le_max_left _ _)).trans hCt2
    · change Nb * (σ / 64) * Dm + 2 * Dm + 4 * Dm + Nb * Dm ≤ Ct
      have h3 := (le_max_right _ _).trans hCt2
      have h4 : Nb * (σ / 64) * Dm ≤ Nb * Dm := by
        have : Nb * (σ / 64) ≤ Nb := by nlinarith
        exact mul_le_mul_of_nonneg_right this hDm0
      linarith
theorem norm_toImaginary (v : EuclideanSpace ℝ (Fin 3)) : ‖toImaginary v‖ = ‖v‖ := by apply _root_.YangMills.Construction.Interpolation.ExponentBoundSteps.norm_toImaginary <;> assumption
theorem stepCoordinates_chord (η : StepVariable (finiteCells F)) (b : ↥(chordBonds (finiteCells F))) :
    stepCoordinates η b.1.1 b.1.2 = toImaginary (η b) := by apply _root_.YangMills.Construction.Interpolation.ExponentBoundSteps.stepCoordinates_of_chordBond <;> assumption
theorem mem_finiteCells (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell) : z ∈ finiteCells F := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CellShares.mem_finiteCells <;> assumption
theorem expUnit_zero : expUnit (0 : imaginaryQuaternions) = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
theorem leftTranslate_bondSpread_empty (c : Fin 0 → F.Site F.top × Fin 4) (X : Fin 0 → imaginaryQuaternions)
    (τ : Fin 0 → ℝ) (V : F.GaugeField F.top) : leftTranslate (bondSpread c X τ) V = V := by
  funext y i
  simp [leftTranslate, bondSpread, expUnit_zero]
theorem supDist_comm_cells (y z : F.Cell) : cellSupDist y z = cellSupDist z y := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_comm <;> assumption
theorem supDist_self_cell (z : F.Cell) : cellSupDist z z = 0 := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_self <;> assumption
theorem chordBondSpan_pair_le (Y : F.Cell) (b b' : ↥(chordBonds (finiteCells F))) :
    chordBondSpan Y ![b, b'] ≤ max (cellSupDist Y (enclosingCell b.1.1))
      (max (cellSupDist Y (enclosingCell b'.1.1)) (cellSupDist (enclosingCell b.1.1) (enclosingCell b'.1.1))) := by
  have hc : ∀ l : Fin 2, ![b, b'] l = b ∨ ![b, b'] l = b' := by
    intro l
    fin_cases l <;> simp
  unfold chordBondSpan bondSpan
  refine max_le (Finset.sup_le fun l _ => ?_) (Finset.sup_le fun l _ => Finset.sup_le fun l' _ => ?_)
  · show cellSupDist Y (enclosingCell (![b, b'] l).1.1) ≤ _
    rcases hc l with h | h <;> rw [h]
    · exact le_max_left _ _
    · exact (le_max_left _ _).trans (le_max_right _ _)
  · show cellSupDist (enclosingCell (![b, b'] l).1.1) (enclosingCell (![b, b'] l').1.1) ≤ _
    rcases hc l with h | h <;> rcases hc l' with h' | h' <;> rw [h, h']
    · rw [supDist_self_cell]; exact Nat.zero_le _
    · exact (le_max_right _ _).trans (le_max_right _ _)
    · rw [supDist_comm_cells]; exact (le_max_right _ _).trans (le_max_right _ _)
    · rw [supDist_self_cell]; exact Nat.zero_le _
theorem sum_fiberwise_filter {α β : Type} (S : Finset α) (T : Finset β) (g : α → β) (hg : ∀ a ∈ S, g a ∈ T)
    (w : α → ℝ) (inst : ∀ y, DecidablePred fun a => g a = y) :
    ∑ y ∈ T, ∑ a ∈ @Finset.filter _ (fun a => g a = y) (inst y) S, w a = ∑ a ∈ S, w a := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to hg w]
  refine Finset.sum_congr rfl fun y _ => ?_
  exact Finset.sum_congr (by ext a; simp [Finset.mem_filter]) fun _ _ => rfl
theorem rayGradientSum_univ {ι B T : Type} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup T] [NormedSpace ℝ T] (f : (ι → B) × T → ℝ) (η : ι → B)
    (h : ∀ v ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) f (v • η, 0)) :
    rayGradientSum f Finset.univ (η, 0) = f (η, 0) - f (0, 0) := by
  have hcont : ∀ w : (ι → B) × T,
      ContinuousOn (fun v : ℝ => fderiv ℝ f (v • η, (0 : T)) w) (Set.Icc 0 1) := by
    intro w v hv
    have h1 : ContinuousAt (fderiv ℝ f) (v • η, (0 : T)) :=
      ((h v hv).fderiv_right (m := 1) (by norm_num)).continuousAt
    have h2 : ContinuousAt (fun v : ℝ => (v • η, (0 : T))) v := by fun_prop
    have h3 : ContinuousAt (fun v : ℝ => fderiv ℝ f (v • η, (0 : T))) v :=
      ContinuousAt.comp (g := fderiv ℝ f) h1 h2
    exact (h3.clm_apply continuousAt_const).continuousWithinAt
  have hint : ∀ w : (ι → B) × T,
      IntervalIntegrable (fun v : ℝ => fderiv ℝ f (v • η, (0 : T)) w) MeasureTheory.volume 0 1 := fun w =>
    (hcont w).intervalIntegrable_of_Icc zero_le_one
  have hder : ∀ v ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun v : ℝ => f (v • η, (0 : T)))
      (fderiv ℝ f (v • η, (0 : T)) (η, 0)) v := by
    intro v hv
    rw [Set.uIcc_of_le zero_le_one] at hv
    have h1 : HasFDerivAt f (fderiv ℝ f (v • η, (0 : T))) (v • η, (0 : T)) :=
      ((h v hv).differentiableAt (by norm_num)).hasFDerivAt
    have h2 : HasDerivAt (fun v : ℝ => (v • η, (0 : T))) (η, (0 : T)) v := by
      have a1 : HasDerivAt (fun v : ℝ => v • η) η v := by
        simpa using (hasDerivAt_id v).smul_const η
      exact a1.prodMk (hasDerivAt_const v (0 : T))
    exact h1.comp_hasDerivAt v h2
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt hder (hint (η, 0))
  simp only [one_smul, zero_smul] at hF
  rw [← hF]
  show ∑ b : ι, ∫ v in (0 : ℝ)..1, fderiv ℝ f (v • η, (0 : T)) (Pi.single b (η b), 0) = _
  rw [← intervalIntegral.integral_finsetSum (fun b _ => hint _)]
  refine intervalIntegral.integral_congr fun v _ => ?_
  show ∑ b : ι, fderiv ℝ f (v • η, (0 : T)) (Pi.single b (η b), 0) = fderiv ℝ f (v • η, (0 : T)) (η, 0)
  rw [← map_sum]
  congr 1
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_sum]
    exact Finset.univ_sum_single η
  · rw [Prod.snd_sum]
    simp
theorem rotatedEval_contDiffAt_of_units {G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ}
    {V : F.GaugeField F.top} {η : StepVariable (finiteCells F)} {k : ℕ} {c : Fin k → F.Site F.top × Fin 4}
    {n : WithTop ℕ∞}
    (h : ∀ e : Fin k → imaginaryQuaternions, AreUnitVectors e → ContDiffAt ℝ n (rotatedEval G V c e) (η, 0))
    (X : Fin k → imaginaryQuaternions) : ContDiffAt ℝ n (rotatedEval G V c X) (η, 0) := by
  classical
  set w : imaginaryQuaternions := toImaginary (EuclideanSpace.single 0 1) with hw
  have hw1 : ‖w‖ = 1 := by
    rw [hw, norm_toImaginary]
    simp
  let e : Fin k → imaginaryQuaternions := fun l => if X l = 0 then w else (‖X l‖⁻¹ : ℝ) • X l
  let r : Fin k → ℝ := fun l => ‖X l‖
  have he : AreUnitVectors e := by
    intro l
    by_cases hl : X l = 0
    · simp only [e, if_pos hl]
      exact hw1
    · simp only [e, if_neg hl]
      rw [norm_smul, norm_inv, norm_norm]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.2 hl)
  have hmul : ∀ (l : Fin k) (t : ℝ), (r l * t) • e l = t • X l := by
    intro l t
    by_cases hl : X l = 0
    · simp [r, hl]
    · simp only [e, r, if_neg hl]
      rw [smul_smul]
      congr 1
      have := norm_ne_zero_iff.2 hl
      field_simp
  have hsp : ∀ τ : Fin k → ℝ, bondSpread c X τ = bondSpread c e (fun l => r l * τ l) := by
    intro τ
    funext y i
    simp only [bondSpread, hmul]
  let g : StepVariable (finiteCells F) × (Fin k → ℝ) → StepVariable (finiteCells F) × (Fin k → ℝ) :=
    fun p => (p.1, fun l => r l * p.2 l)
  have hg : ContDiffAt ℝ n g (η, 0) := by
    refine ContDiff.contDiffAt ?_
    exact contDiff_fst.prodMk (contDiff_pi.2 fun l =>
      contDiff_const.mul ((contDiff_apply ℝ ℝ l).comp contDiff_snd))
  have hg0 : g (η, 0) = (η, 0) := by
    refine Prod.ext rfl ?_
    funext l
    simp [g]
  have hb : ContDiffAt ℝ n (rotatedEval G V c e) (g (η, 0)) := by
    rw [hg0]
    exact h e he
  refine (ContDiffAt.comp (η, 0) hb hg).congr_of_eventuallyEq (Filter.Eventually.of_forall fun p => ?_)
  show G p.1 (leftTranslate (bondSpread c X p.2) V) = G p.1 (leftTranslate (bondSpread c e fun l => r l * p.2 l) V)
  rw [hsp]
theorem rotatedEval_interpolatedBlockExponent_contDiffAt (hA : JointMixedDerivEqDerivAlong)
    (hRay : RayGradientSumSmoothAndBounded) (hRead : cellExponentRotatedEvalStatement)
    {s a ρA ρ x κ κ₂ δ₂ : ℝ} {m : ℕ} {Kf : ℕ → ℝ} {Dk : ℕ → ℕ → ℝ}
    {V : F.GaugeField F.top} (hne : Nonempty ↥(chordBonds (finiteCells F)))
    (hker : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ ρ) →
      HasInterpolationKernels s a ρA κ κ₂ δ₂ x m Kf Dk V η)
    (Y : F.Cell) (η : StepVariable (finiteCells F)) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (hη : ∀ b, ‖η b‖ ≤ ρ) (hX : AreUnitVectors X) (n : ℕ) :
    ContDiffAt ℝ ((n + 2 : ℕ) : WithTop ℕ∞)
      (rotatedEval (fun ζ V' => interpolatedBlockExponent s a ρA x m Y V' ζ) V c X) (η, 0) := by
  have hball : ∀ v ∈ Set.Icc (0 : ℝ) 1, ∀ b, ‖(v • η) b‖ ≤ ρ := by
    intro v hv b
    rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg hv.1]
    nlinarith [norm_nonneg (η b), hη b, hv.2]
  have hs : ∀ v ∈ Set.Icc (0 : ℝ) 1, ∀ n : ℕ, ContDiffAt ℝ (n : WithTop ℕ∞)
      (rotatedEval (interpolatedEnergy s a ρA m) V c X) (v • η, 0) := fun v hv n =>
    (hA F V _ (v • η) k c X).1 hne
      (fun l b u hl hu => ((hker _ (hball v hv)).energy l k b u c X hl hu hX).1) n
  have hray : ContDiffAt ℝ ((n + 2 : ℕ) : WithTop ℕ∞)
      (rayGradientSum (rotatedEval (interpolatedEnergy s a ρA m) V c X) (cellChordBonds Y)) (η, 0) := by
    have := (hRay _ _ (Fin k → ℝ) (rotatedEval (interpolatedEnergy s a ρA m) V c X) (cellChordBonds Y) η
      (List.replicate n (0 : Fin k → ℝ)) (fun v hv => hs v hv _)).1
    simpa [List.length_replicate] using this
  have e := hRead.1 F s a ρA x m Y V η k c X fun v hv => hs v hv 1
  have hg : ContDiffAt ℝ ((n + 2 : ℕ) : WithTop ℕ∞) (fun p => ∑ c₀ ∈ (innerBonds (finiteCells F) F.top).filter
      (fun c => c.1 = Y), (rotatedEval (contourHaarGap s a ρA x m c₀) V c X p - haarGap (a * x))) (η, 0) :=
    ContDiffAt.sum fun c₀ _ => ((hA F V _ η k c X).1 hne
      (fun l b u hl hu => ((hker η hη).gap c₀ l k b u c X (by omega) hu hX).1) _).sub contDiffAt_const
  have hh : ContDiffAt ℝ ((n + 2 : ℕ) : WithTop ℕ∞) (fun p => ∑ b ∈ cellChordBonds Y,
      rotatedEval (interpolatedHaarLogRatio s a ρA m b) V c X p) (η, 0) :=
    ContDiffAt.sum fun b₀ _ => (hA F V _ η k c X).1 hne
      (fun l b u hl hu => ((hker η hη).haar b₀ l k b u c X (by omega) hu hX).1) _
  exact (((contDiffAt_const.mul hray).sub hg).sub hh).congr_of_eventuallyEq e
end ExponentBoundsAux
open ExponentBoundsAux in
open Classical in
theorem cellExponentsBounded_holds (hKern : interpolationKernelBoundsStatement)
    (hSlope : interpolatedSlopeSmallOnTorus) (hNear : interpolatedFramesControlled)
    (hFloors : frameRadiusGrowthStatement) (hSum : ExpDecaySumBounded)
    (hTop : interpolatedExponentBoundsAtTopStatement) (hJoin : EventuallyInParametersCombines)
    (hGap : HaarGapExcessBounded) (hHaar : haarLogRatioBoundStatement)
    (hMove : ChartShiftLipschitz) (hB : SiteDecomposition)
    (hC : BlocksCoverLowerLevel) (hA : JointMixedDerivEqDerivAlong)
    (hRay : RayGradientSumSmoothAndBounded) (hRead : cellExponentRotatedEvalStatement)
    (hEnds : interpolationAtEndpoints) : CellExponentsBounded := by
  obtain ⟨K, Dk, -, hDpos, hKT⟩ := hKern
  obtain ⟨Cg, hCg0, hCg⟩ := hGap
  obtain ⟨St, hSt0, hKS⟩ := eventually_with_chosen_rate _ hKT
  let Tst : ℝ → ℕ → ColdChainParameters → StepParameters := fun a L c =>
    rateParameters ⟨a, L, c, (St a L c).1, (St a L c).2, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  have hP := hJoin.1 _ _ (hJoin.1 _ _ (hJoin.1 _ _ hKS hSlope) hNear)
    (eventually_constantsFit hFloors hSum hB (fun a L c => Dk (Tst a L c)) (fun a L c => (St a L c).2) Cg
      (fun a L c => hDpos _) hSt0)
  show EventuallyInParameters CellExponentsBoundedAt
  refine hJoin.2 _ _ ?_ hP
  rintro T hT ⟨⟨⟨hk, hs⟩, hn⟩, hnum⟩
  intro t x F V star hx ht hcold
  set s : ℝ := segmentEnd star with hsdef
  have hs0 : 0 ≤ s := by
    rw [hsdef]
    unfold segmentEnd
    split_ifs <;> norm_num
  have hs1 : s ≤ 1 := by
    rw [hsdef]
    unfold segmentEnd
    split_ifs <;> norm_num
  obtain ⟨hFL, -, n, hside, hn₀⟩ := id ht
  have hn2 : 2 ≤ n := hnum.two_le_n₀.trans hn₀
  have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by rw [hside i]; exact hn2
  have hLodd : Odd F.blockSide := hFL ▸ hT.odd_L
  have hρ : 0 < T.ballRadius := by
    have := hT.σ_pos
    unfold StepParameters.ballRadius
    positivity
  obtain ⟨hx2, hωx⟩ := hnum.gap_decay x hx
  have hne := chordBonds_nonempty hB hC hLodd hs2
  obtain ⟨Wt, hW, hC1, hC2, hC3⟩ := hnum.weight_sums
  obtain ⟨-, hsmall⟩ := (hn t x hx).single F V s ht hcold hs0 hs1
  have hCt := hnum.one_le_Ct
  have hω0 : 0 ≤ T.Ct * frameGapBound T (frameRadius x) := by
    unfold frameGapBound
    have := Real.exp_pos (-(T.chainParams.δ₂ / 4 * (frameRadius x : ℝ)))
    have : 0 ≤ T.Ct := by linarith
    positivity
  set D' : ℕ → ℕ → ℝ := Dk (Tst T.a T.L T.chainParams) with hD'
  set K' : ℕ → ℝ := K (Tst T.a T.L T.chainParams) with hK'
  have hDp : ∀ l j, 0 < D' l j := hDpos _
  have hker : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ T.ballRadius) →
      HasInterpolationKernels s T.a T.chainParams.ρA T.κ T.chainParams.κ₂ T.chainParams.δ₂ x (frameRadius x)
        K' D' V η := fun η hη =>
    interpolationKernels_mono (fun l j => (hDp l j).le) hnum.rate_le_chosen
      (hk x t F V s η hx ht hcold hs0 hs1 hη)
  have hBt : InterpolatedExponentBounds s T.a T.chainParams.ρA T.ballRadius x T.κ T.Ct (frameRadius x) V := by
    refine hTop F s T.a T.chainParams.ρA T.ballRadius x T.κ T.chainParams.κ₂ T.chainParams.δ₂ T.Ct
      (frameGapBound T (frameRadius x)) T.Ct Cg 1 Wt
      (derivBoundTotal D') (frameRadius x) ((centredCube T.L).card * 4) K' D' V hne hρ hT.κ_pos hnum.rate_le
      (by linarith) hω0 hωx hCg0 zero_le_one (derivBoundTotal_nonneg hDp) (le_derivBoundTotal hDp) (fun z => ?_)
      (hW F hFL hs2) hker (hs t x hx F V s ht hcold hs0 hs1) (fun η c₀ hη _ => ?_) (fun η b hη => ?_) hC1 hC2 hC3
    · have := card_cellChordBonds_le hB hLodd hs2 z
      rwa [hFL] at this
    · refine hCg F T.a x _ V c₀ hLodd hT.one_le_a hx2 fun h π hh => ?_
      have hm := (hMove F V (fun z i => interpolatedFrame s T.a T.chainParams.ρA (frameRadius x) (z, i) V) η
        T.ballRadius hLodd (fun b => (hη b).le) hρ.le).2.2 c₀ h π hh
      have hc := hsmall.contour_near_one c₀ h π hh
      have hcd := hnum.small_radius
      rw [hFL] at hm
      have e : interpolatedField s T.a T.chainParams.ρA (frameRadius x) V η = chartedField (fun z i =>
          interpolatedFrame s T.a T.chainParams.ρA (frameRadius x) (z, i) V + stepCoordinates η z i) V := rfl
      rw [e]
      linarith
    · refine hHaar _ ?_
      have e : interpolatedCoords s T.a T.chainParams.ρA (frameRadius x) V η b.1.1 b.1.2 =
          interpolatedFrame s T.a T.chainParams.ρA (frameRadius x) b.1 V + toImaginary (η b) := by
        simp only [interpolatedCoords, stepCoordinates_chord]
      rw [e]
      have h1 := hsmall.norm_add_le b.1 b.2
      have h2 := hη b
      have h3 : ‖toImaginary (η b)‖ = ‖η b‖ := norm_toImaginary _
      have h4 := norm_add_le (interpolatedFrame s T.a T.chainParams.ρA (frameRadius x) b.1 V) (toImaginary (η b))
      have h5 : T.ballRadius = T.σ / 64 := rfl
      have hρA : T.chainParams.ρA ≤ 1 := hT.chain_admissible.classical.1.2.1
      linarith
  have hfun : (interpolatedBlockExponent s T.a T.chainParams.ρA x (frameRadius x) :
      F.Cell → F.GaugeField F.top → StepVariable (finiteCells F) → ℝ) =
      cellExponent star T.a T.chainParams.ρA x (frameRadius x) := by
    funext Y V' η
    exact (hEnds F star T.a T.chainParams.ρA 0 x 0 (frameRadius x) V').2.2.2.2.1 Y η
  have hsm : ∀ (Y : F.Cell) (η : StepVariable (finiteCells F)) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
      (X : Fin k → imaginaryQuaternions), (∀ b, ‖η b‖ ≤ T.ballRadius) → ContDiffAt ℝ ((2 + 2 : ℕ) : WithTop ℕ∞)
        (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) =>
          cellExponent star T.a T.chainParams.ρA x (frameRadius x) Y (leftTranslate (bondSpread c X q.1) V) q.2)
        (0, η) := by
    intro Y η k c X hη
    have h1 := rotatedEval_contDiffAt_of_units
      (fun e he => rotatedEval_interpolatedBlockExponent_contDiffAt hA hRay hRead hne hker Y η k c e hη he 2) X
    have h2 : ContDiffAt ℝ ((2 + 2 : ℕ) : WithTop ℕ∞)
        (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) => (q.2, q.1)) (0, η) :=
      (contDiff_snd.prodMk contDiff_fst).contDiffAt
    have h3 := ContDiffAt.comp (g := rotatedEval (fun ζ V' =>
      interpolatedBlockExponent s T.a T.chainParams.ρA x (frameRadius x) Y V' ζ) V c X) (0, η) h1 h2
    rw [← hfun]
    exact h3
  have hsum : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < T.ballRadius) →
      stepExponent star T.a T.chainParams.ρA x (frameRadius x) (fun _ _ _ => 0) 0 V η =
        ∑ Y ∈ finiteCells F, cellExponent star T.a T.chainParams.ρA x (frameRadius x) Y V η := by
    intro η hη
    have hball : ∀ v ∈ Set.Icc (0 : ℝ) 1, ∀ b, ‖(v • η) b‖ ≤ T.ballRadius := by
      intro v hv b
      rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg hv.1]
      nlinarith [norm_nonneg (η b), hη b, hv.2]
    let c0 : Fin 0 → F.Site F.top × Fin 4 := Fin.elim0
    let X0 : Fin 0 → imaginaryQuaternions := Fin.elim0
    have hX0 : AreUnitVectors X0 := fun l => l.elim0
    have hsf : ∀ v ∈ Set.Icc (0 : ℝ) 1, ∀ n : ℕ, ContDiffAt ℝ (n : WithTop ℕ∞)
        (rotatedEval (interpolatedEnergy s T.a T.chainParams.ρA (frameRadius x)) V c0 X0) (v • η, 0) :=
      fun v hv n =>
        (hA F V _ (v • η) 0 c0 X0).1 hne
          (fun l b u hl hu => ((hker _ (hball v hv)).energy l 0 b u c0 X0 hl hu hX0).1) n
    have hpart : ∀ Y : F.Cell, interpolatedBlockExponent s T.a T.chainParams.ρA x (frameRadius x) Y V η =
        x * rayGradientSum (rotatedEval (interpolatedEnergy s T.a T.chainParams.ρA (frameRadius x)) V c0 X0)
          (cellChordBonds Y) (η, 0) -
        (∑ c₀ ∈ (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y),
          haarGapExcess T.a x (interpolatedField s T.a T.chainParams.ρA (frameRadius x) V η) c₀) -
        ∑ b ∈ cellChordBonds Y,
          haarLogRatio (interpolatedCoords s T.a T.chainParams.ρA (frameRadius x) V η b.1.1 b.1.2) := by
      intro Y
      have e := (hRead.1 F s T.a T.chainParams.ρA x (frameRadius x) Y V η 0 c0 X0
        fun v hv => hsf v hv 1).eq_of_nhds
      have e1 : rotatedEval (fun ζ V' => interpolatedBlockExponent s T.a T.chainParams.ρA x (frameRadius x) Y V' ζ)
          V c0 X0 (η, 0) = interpolatedBlockExponent s T.a T.chainParams.ρA x (frameRadius x) Y V η := by
        show interpolatedBlockExponent s T.a T.chainParams.ρA x (frameRadius x) Y
          (leftTranslate (bondSpread c0 X0 0) V) η = _
        rw [leftTranslate_bondSpread_empty]
      have e2 : ∀ c₀ : F.Site F.top × Fin 4,
          rotatedEval (contourHaarGap s T.a T.chainParams.ρA x (frameRadius x) c₀) V c0 X0 (η, 0) -
            haarGap (T.a * x) =
          haarGapExcess T.a x (interpolatedField s T.a T.chainParams.ρA (frameRadius x) V η) c₀ := by
        intro c₀
        show contourHaarGap s T.a T.chainParams.ρA x (frameRadius x) c₀ η (leftTranslate (bondSpread c0 X0 0) V) -
          _ = _
        rw [leftTranslate_bondSpread_empty]
        rfl
      have e3 : ∀ b : ↥(chordBonds (finiteCells F)),
          rotatedEval (interpolatedHaarLogRatio s T.a T.chainParams.ρA (frameRadius x) b) V c0 X0 (η, 0) =
            haarLogRatio (interpolatedCoords s T.a T.chainParams.ρA (frameRadius x) V η b.1.1 b.1.2) := by
        intro b
        show interpolatedHaarLogRatio s T.a T.chainParams.ρA (frameRadius x) b η
          (leftTranslate (bondSpread c0 X0 0) V) = _
        rw [leftTranslate_bondSpread_empty]
        rfl
      have e' := e1.symm.trans e
      simp only [e2, e3] at e'
      exact e'
    have hmemF := mem_finiteCells hs2
    have hgrad : ∑ Y ∈ finiteCells F, rayGradientSum
        (rotatedEval (interpolatedEnergy s T.a T.chainParams.ρA (frameRadius x)) V c0 X0) (cellChordBonds Y) (η, 0) =
        interpolatedEnergy s T.a T.chainParams.ρA (frameRadius x) η V -
          interpolatedEnergy s T.a T.chainParams.ρA (frameRadius x) 0 V := by
      have h1 := rayGradientSum_univ
        (rotatedEval (interpolatedEnergy s T.a T.chainParams.ρA (frameRadius x)) V c0 X0) η
        fun v hv => hsf v hv 2
      have h2 : ∀ ζ : StepVariable (finiteCells F),
          rotatedEval (interpolatedEnergy s T.a T.chainParams.ρA (frameRadius x)) V c0 X0 (ζ, 0) =
            interpolatedEnergy s T.a T.chainParams.ρA (frameRadius x) ζ V := by
        intro ζ
        show interpolatedEnergy s T.a T.chainParams.ρA (frameRadius x) ζ (leftTranslate (bondSpread c0 X0 0) V) = _
        rw [leftTranslate_bondSpread_empty]
      rw [h2, h2] at h1
      rw [← h1]
      exact sum_fiberwise_filter Finset.univ (finiteCells F)
        (fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1) (fun b _ => hmemF _) _ _
    have hgap : ∑ Y ∈ finiteCells F, ∑ c₀ ∈ (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y),
        haarGapExcess T.a x (interpolatedField s T.a T.chainParams.ρA (frameRadius x) V η) c₀ =
        ∑ c₀ ∈ innerBonds (finiteCells F) F.top,
          haarGapExcess T.a x (interpolatedField s T.a T.chainParams.ρA (frameRadius x) V η) c₀ :=
      sum_fiberwise_filter _ (finiteCells F) (fun c : F.Site F.top × Fin 4 => c.1) (fun c _ => hmemF _) _ _
    have hhaar : ∑ Y ∈ finiteCells F, ∑ b ∈ cellChordBonds Y,
        haarLogRatio (interpolatedCoords s T.a T.chainParams.ρA (frameRadius x) V η b.1.1 b.1.2) =
        ∑ b : ↥(chordBonds (finiteCells F)),
          haarLogRatio (interpolatedCoords s T.a T.chainParams.ρA (frameRadius x) V η b.1.1 b.1.2) :=
      sum_fiberwise_filter Finset.univ (finiteCells F)
        (fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1) (fun b _ => hmemF _) _ _
    have hAb : coordsAboveFrame star T.a T.chainParams.ρA (frameRadius x) V =
        interpolatedCoords s T.a T.chainParams.ρA (frameRadius x) V :=
      funext fun ζ => ((hEnds F star T.a T.chainParams.ρA 0 x 0 (frameRadius x) V).2.1 ζ).symm
    have hFd : fieldAboveFrame star T.a T.chainParams.ρA (frameRadius x) V =
        interpolatedField s T.a T.chainParams.ρA (frameRadius x) V :=
      funext fun ζ => ((hEnds F star T.a T.chainParams.ρA 0 x 0 (frameRadius x) V).2.2.1 ζ).symm
    rw [← hfun, Finset.sum_congr rfl fun Y _ => hpart Y, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, hgrad, hgap, hhaar]
    unfold stepExponent
    rw [hAb, hFd, zero_mul, sub_zero]
    rfl
  refine ⟨⟨hsum, fun Y η k c X hη => (hsm Y η k c X hη).of_le (by norm_num), ?_, ?_, ?_⟩,
    fun Y k c X η hη => (hsm Y η k c X hη).of_le (by norm_num)⟩
  · intro Y η k c X hη hk3 hX
    have h := hBt.deriv_top Y η k c X hη hk3 hX
    rw [hfun] at h
    exact h
  · intro Y η b e k c X hη hk3 hX he
    have h := hBt.deriv_top_partial Y η b e k c X hη hk3 hX he
    rw [hfun] at h
    exact h
  · intro Y η b b' e e' hη he he'
    have h := hBt.second_deriv Y η b b' e e' hη he he'
    rw [hfun] at h
    refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) ?_)
    · have h1 := Nat.cast_le (α := ℝ).2 (chordBondSpan_pair_le Y b b')
      have hκ := hT.κ_pos
      have h2 : (0 : ℝ) ≤ 2 ^ 6 * T.κ := by positivity
      exact neg_le_neg (mul_le_mul_of_nonneg_left h1 h2)
    · have : 0 ≤ T.Ct := by linarith
      have : 0 ≤ x := by linarith
      positivity
end YangMills.Construction.ColdStepAtMirrorFrames
end
