import YangMills.Construction.ColdStepAtMirrorFrames.BoundsOfTheExpansionAboveTheFrame
import YangMills.Construction.ColdStepAtMirrorFrames.MeasuresOfTheStepAreRegular
import YangMills.Construction.SummableBoundsOfTheFlow.TheStepIsRegularAtTheLeastFieldProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame}
namespace StepMeasuresRegular
private theorem mem_finiteCells (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell) : z ∈ finiteCells F := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CellShares.mem_finiteCells <;> assumption
private theorem leftTranslate_empty (c : Fin 0 → F.Site F.top × Fin 4) (X : Fin 0 → imaginaryQuaternions)
    (τ : Fin 0 → ℝ) (V : F.GaugeField F.top) : leftTranslate (bondSpread c X τ) V = V := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ExponentBoundsAux.leftTranslate_bondSpread_empty <;> assumption
private def closedBallProduct (F : BlockFrame) (ρ : ℝ) : Set (StepVariable (finiteCells F)) :=
  {η | ∀ b, ‖η b‖ ≤ ρ}
private theorem isCompact_closedBallProduct (ρ : ℝ) : IsCompact (closedBallProduct F ρ) := by apply _root_.YangMills.Construction.Interpolation.RegularStepAtMinimizer.isCompact_closedBallProduct <;> assumption
private theorem openBallProduct_subset (ρ : ℝ) : openBallProduct F ρ ⊆ closedBallProduct F ρ := by apply _root_.YangMills.Construction.Interpolation.RegularStepAtMinimizer.openBallProduct_subset_closed <;> assumption
private theorem exists_bound_on {g : StepVariable (finiteCells F) → ℝ} {ρ : ℝ}
    (hg : ContinuousOn g (closedBallProduct F ρ)) : ∃ M : ℝ, ∀ η ∈ closedBallProduct F ρ, |g η| ≤ M := by apply _root_.YangMills.Construction.Interpolation.RegularStepAtMinimizer.exists_abs_le_of_continuousOn <;> assumption
private theorem cellExponent_continuousOn {star : Bool} {a ρA ρ x κ C : ℝ} {m : ℕ}
    {V : F.GaugeField F.top} (hE : CellExponentBounds star a ρA ρ x κ C m V) (Y : F.Cell) :
    ContinuousOn (cellExponent star a ρA x m Y V) (closedBallProduct F ρ) := by
  intro η hη
  have h := (hE.smooth Y η 0 Fin.elim0 Fin.elim0 hη).continuousAt
  have h2 : ContinuousAt (fun η' : StepVariable (finiteCells F) => ((0 : Fin 0 → ℝ), η')) η := by
    fun_prop
  have h3 := ContinuousAt.comp (f := fun η' : StepVariable (finiteCells F) => ((0 : Fin 0 → ℝ), η')) h h2
  simp only [Function.comp_def, leftTranslate_empty] at h3
  exact h3.continuousWithinAt
private theorem cellCentredExpansion_continuousOn {star : Bool} {a ρA ρ κ δ E E₃ C : ℝ} {L m : ℕ}
    {f : LocalFamily} {V : F.GaugeField F.top} (hR : CentredExpansionBounds star a ρA ρ κ δ E E₃ C L m f V)
    (Y : F.Cell) :
    ContinuousOn (fun η => cellCentredExpansion star a ρA m f Y η V) (closedBallProduct F ρ) := by
  unfold cellCentredExpansion
  apply continuousOn_finsetSum
  intro y _ η hη
  have h := (hR.smooth y η 0 Fin.elim0 Fin.elim0 hη).continuousAt
  have h2 : ContinuousAt (fun η' : StepVariable (finiteCells F) => ((0 : Fin 0 → ℝ), η')) η := by
    fun_prop
  have h3 := ContinuousAt.comp (f := fun η' : StepVariable (finiteCells F) => ((0 : Fin 0 → ℝ), η')) h h2
  simp only [Function.comp_def, leftTranslate_empty] at h3
  exact h3.continuousWithinAt
private theorem cellQuadratic_continuous (lam x : ℝ) (Y : F.Cell) :
    Continuous (cellQuadratic (F := F) lam x Y) := by apply _root_.YangMills.Construction.Interpolation.RegularStepAtMinimizer.continuous_cellQuadratic <;> assumption
private theorem isRegularStep_of_bounds {a ρA ρ lam x κ δ E E₃ C : ℝ} {L m : ℕ} {p : ℝ → ℝ}
    {f : LocalFamily} {V : F.GaugeField F.top} (hρ : 0 < ρ) (hs : ∀ i, 2 ≤ F.extent i)
    (hrim : IsRadialCutoff ρ fun u => cutoffFactor ρ p (max u 0))
    (hE : CellExponentBounds false a ρA ρ x κ C m V)
    (hR : CentredExpansionBounds false a ρA ρ κ δ E E₃ C L m f V) :
    ∃ M, IsRegularStep a ρA ρ lam x M m p f V := by
  classical
  set r : ℝ → ℝ := fun u => cutoffFactor ρ p (max u 0) with hr
  have hrc : Continuous r := hrim.smooth.continuous
  have hfac : ∀ η : StepVariable (finiteCells F), ∀ b, cutoffFactor ρ p ‖η b‖ = r ‖η b‖ := fun η b => by
    simp [hr]
  have hcont : Continuous (cutoffWeight (F := F) ρ p) := by
    have : cutoffWeight (F := F) ρ p = fun η => ∏ b, r ‖η b‖ := by
      funext η
      simp only [cutoffWeight, hfac]
    rw [this]
    exact continuous_finsetProd _ fun b _ => hrc.comp (continuous_apply b).norm
  have hnn : ∀ u : ℝ, 0 ≤ cutoffFactor ρ p u := fun u => by
    unfold cutoffFactor
    split_ifs
    · exact (Real.exp_pos _).le
    · exact le_rfl
  have hnonneg : ∀ η : StepVariable (finiteCells F), 0 ≤ cutoffWeight ρ p η := fun η =>
    Finset.prod_nonneg fun b _ => hnn _
  have hsupp : ∀ η : StepVariable (finiteCells F), η ∉ openBallProduct F ρ → cutoffWeight ρ p η = 0 :=
    fun η hη => by
    simp only [openBallProduct, Set.mem_ofPred_eq, not_forall, not_lt] at hη
    obtain ⟨b, hb⟩ := hη
    exact Finset.prod_eq_zero (Finset.mem_univ b) (by simp [cutoffFactor, not_lt.mpr hb])
  have hcs : HasCompactSupport (cutoffWeight (F := F) ρ p) :=
    HasCompactSupport.intro (isCompact_closedBallProduct ρ) fun η hη =>
      hsupp η fun h => hη (openBallProduct_subset ρ h)
  have hzero : cutoffWeight (F := F) ρ p 0 ≠ 0 := by
    have h0 : ∀ b : ↥(chordBonds (finiteCells F)),
        cutoffFactor ρ p ‖(0 : StepVariable (finiteCells F)) b‖ = 1 := fun b => by
      rw [hfac]
      simpa using hrim.one 0 le_rfl (by positivity)
    rw [cutoffWeight, Finset.prod_eq_one fun b _ => h0 b]
    exact one_ne_zero
  have hpos : 0 < ∫ η : StepVariable (finiteCells F), cutoffWeight ρ p η :=
    hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs hnonneg hzero
  choose M₁ hM₁ using fun Y => exists_bound_on (cellExponent_continuousOn hE Y)
  choose M₂ hM₂ using fun Y => exists_bound_on (ρ := ρ) (cellQuadratic_continuous lam x Y).continuousOn
  choose M₃ hM₃ using fun Y => exists_bound_on (cellCentredExpansion_continuousOn hR Y)
  set M : ℝ := ∑ Y ∈ finiteCells F, (|M₁ Y| + |M₂ Y| + |M₃ Y|) with hM
  have hMnn : 0 ≤ M := Finset.sum_nonneg fun Y _ => by positivity
  have hle : ∀ Y, |M₁ Y| + |M₂ Y| + |M₃ Y| ≤ M := fun Y =>
    Finset.single_le_sum (f := fun Y => |M₁ Y| + |M₂ Y| + |M₃ Y|) (fun Y _ => by positivity)
      (mem_finiteCells hs Y)
  refine ⟨M, ⟨hcont.measurable, hnonneg, hsupp, hcont.integrable_of_hasCompactSupport hcs, hpos,
    hMnn, fun Y => (cellExponent_continuousOn hE Y).mono (openBallProduct_subset ρ),
    fun Y => (cellQuadratic_continuous lam x Y).continuousOn,
    fun Y => (cellCentredExpansion_continuousOn hR Y).mono (openBallProduct_subset ρ),
    fun Y η hη => ?_, fun Y η hη => ?_, fun Y η hη => ?_, fun η hη => ?_⟩⟩
  · have := hM₁ Y η (openBallProduct_subset ρ hη)
    have := hle Y
    have := le_abs_self (M₁ Y)
    have := abs_nonneg (M₂ Y)
    have := abs_nonneg (M₃ Y)
    linarith
  · have := hM₂ Y η (openBallProduct_subset ρ hη)
    have := hle Y
    have := le_abs_self (M₂ Y)
    have := abs_nonneg (M₁ Y)
    have := abs_nonneg (M₃ Y)
    linarith
  · have := hM₃ Y η (openBallProduct_subset ρ hη)
    have := hle Y
    have := le_abs_self (M₃ Y)
    have := abs_nonneg (M₁ Y)
    have := abs_nonneg (M₂ Y)
    linarith
  · have := hE.sum_eq η hη
    simpa [stepExponent] using this
end StepMeasuresRegular
open StepMeasuresRegular in
theorem stepMeasuresRegular (hJ : EventuallyInParametersCombines)
    (hW : frameBoundsStatement) (hC : CouplingThreshold)
    (hX : CellExponentsBounded) (hR : CentredExpansionsBounded)
    (hRim : CutoffFactorIsRadialCutoff) : stepMeasuresRegularStatement := by
  obtain ⟨join, weaken⟩ := hJ
  have hF : EventuallyInParameters fun T => 2 ≤ T.n₀ ∧ ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x →
      ∀ F, IsCubicTopTorus T.L t T.n₀ F →
      ∀ V : F.GaugeField F.top, IsSmallCurvature (5 / 4 * T.σ) V → ∀ b ∈ chordBonds (finiteCells F),
        ‖stepFrame false T.a T.chainParams.ρA (frameRadius x) b V‖ + T.ballRadius ≤ T.chainParams.ρA := by
    intro a ha
    refine ⟨2 ^ 40, fun L hL hLe c hc => ?_⟩
    obtain ⟨Cf, C, σ₀, hC₁, hC₂, hσ₀, hFr⟩ := hW a L c ha hL hLe hc
    have hδ₂ : 0 < c.δ₂ := hc.classical.1.2.2.2.1
    refine ⟨0, fun Ct _ => ⟨c.δ₂ / 2 ^ 14, by positivity, fun κ hκ hκ' => ⟨1, one_pos,
      fun η₃ _ _ _ => ⟨0, fun nss _ => ⟨σ₀, hσ₀, fun σ hσ hσ' p hp => ⟨0, fun Cs _ E hE =>
        ⟨64, fun n₀ hn₀ => ⟨0, fun CE _ => ?_⟩⟩⟩⟩⟩⟩⟩⟩
    obtain ⟨y₀, hy⟩ := hC Cf C c.δ₂ κ σ 0 hδ₂ hκ hκ' hσ
    refine ⟨max y₀ 1, fun y₁ hy₁ => ⟨le_trans (by norm_num) hn₀, fun t x hx F hF V hV b hb => ?_⟩⟩
    have hxy : y₁ ≤ x := hx
    have hx0 : y₀ ≤ x := le_trans (le_trans (le_max_left _ _) hy₁) hxy
    have hx1 : 1 ≤ x := le_trans (le_trans (le_max_right _ _) hy₁) hxy
    obtain ⟨-, h16, hg, hxω, hxe, -⟩ := hy x hx0
    have H := hFr κ σ x (frameRadius x) t n₀ hκ hκ' hσ hσ' hx1 h16 hn₀ hg hxω hxe F V hF hV
    exact (H.2.1 false).norm_add_le b hb
  refine weaken _ _ (fun T hT h t x hx f hf F hF V hV => ?_) (join _ _ hF (join _ _ hX hR))
  obtain ⟨⟨hn₂, hroom⟩, hX, hR⟩ := h
  have hσ := hT.σ_pos
  have hV' : IsSmallCurvature (5 / 4 * T.σ) V := fun q hq => lt_of_lt_of_le (hV q hq) (by linarith)
  have hρA1 : T.chainParams.ρA ≤ 1 := hT.chain_admissible.classical.1.2.1
  have hρ : 0 < T.ballRadius := by
    show 0 < T.σ / 64
    positivity
  refine ⟨fun b hb => ?_, ?_⟩
  · have := hroom t x hx F hF V hV' b hb
    have hpi := Real.pi_gt_three
    linarith
  · obtain ⟨hFL, hFt, n, hside, hn⟩ := hF
    have hs : ∀ i, 2 ≤ F.extent i := fun i => by
      rw [hside]
      omega
    exact isRegularStep_of_bounds hρ hs (hRim T.ballRadius T.p hρ hT.cutoff)
      (hX t x F V false hx ⟨hFL, hFt, n, hside, hn⟩ hV').1
      (hR t x f F V false hx hf ⟨hFL, hFt, n, hside, hn⟩ hV')
end ColdStepAtMirrorFrames
end YangMills.Construction
end
