import YangMills.Construction.ColdStepAtMirrorFrames.CompatibleLocalFamiliesGlue
import YangMills.Construction.ColdStepAtMirrorFrames.DistancesOfSitesAndCells
import YangMills.Construction.SummableBoundsOfTheFlow.FieldsOfTheTopBetween
import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenStayNear
import YangMills.Construction.SummableBoundsOfTheFlow.KernelsAtTheFramesBetween
import YangMills.Construction.SummableBoundsOfTheFlow.MoveOfTheTopAlongItsField
import YangMills.Construction.SummableBoundsOfTheFlow.RightShiftOfTheChart
import YangMills.Construction.SummableBoundsOfTheFlow.TopFieldDecays
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace Interpolation
namespace TopVariationAlongFields
variable {F : BlockFrame}
structure Constants (K : StepParameters → ℕ → ℝ) (M CT : ℝ) (T : StepParameters) : Prop where
  two_le_n₀ : 2 ≤ T.n₀
  rate_le : 2 ^ 10 * T.κ ≤ T.chainParams.δ₂
  const_le : M * (K (rateParameters T) 1 + K (rateParameters T) 2 + K (rateParameters T) 3) +
    CT * (1 + K (rateParameters T) 1 + K (rateParameters T) 1 ^ 2 + K (rateParameters T) 2) ≤ T.Cs
theorem eventually_constants (K : StepParameters → ℕ → ℝ) (M CT : ℝ) :
    EventuallyInParameters (Constants K M CT) := by
  intro a _
  refine ⟨0, fun L hL _ c hc => ?_⟩
  have hδ : 0 < c.δ₂ := hc.classical.1.2.2.2.1
  refine ⟨0, fun Ct _ => ?_⟩
  refine ⟨c.δ₂ / 2 ^ 10, by positivity, fun κ hκ hκle => ?_⟩
  refine ⟨1, one_pos, fun η₃ _ _ _ => ?_⟩
  refine ⟨0, fun nss _ => ?_⟩
  refine ⟨1, one_pos, fun σ _ _ p _ => ?_⟩
  refine ⟨M * (K ⟨a, L, c, Ct, κ, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ 1 + K ⟨a, L, c, Ct, κ, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ 2 +
      K ⟨a, L, c, Ct, κ, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ 3) +
    CT * (1 + K ⟨a, L, c, Ct, κ, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ 1 + K ⟨a, L, c, Ct, κ, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ 1 ^ 2 +
      K ⟨a, L, c, Ct, κ, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ 2), fun Cs hCs E _ => ?_⟩
  refine ⟨2, fun n₀ hn₀ => ?_⟩
  refine ⟨0, fun CE _ => ?_⟩
  refine ⟨0, fun y₁ _ => ?_⟩
  refine ⟨hn₀, ?_, hCs⟩
  change 2 ^ 10 * κ ≤ c.δ₂
  have := mul_le_mul_of_nonneg_left hκle (by positivity : (0 : ℝ) ≤ 2 ^ 10)
  linarith
theorem bondSpan_le_two_mul (hD : SupDistCellComparison) {k : ℕ} (z : F.Cell)
    (c : Fin k → F.Site F.top × Fin 4) : bondSpan z c ≤ 2 * bondListDistance z c := by
  unfold bondSpan
  have h : ∀ l, cellSupDist z (c l).1 ≤ bondListDistance z c := fun l =>
    Finset.le_sup (f := fun l => cellSupDist z (c l).1) (Finset.mem_univ l)
  refine max_le (Finset.sup_le fun l _ => (h l).trans (by omega)) (Finset.sup_le fun l _ =>
    Finset.sup_le fun l' _ => ?_)
  obtain ⟨-, h2, h3⟩ := hD.1 F F.top z (c l).1 (c l').1
  have h5 := (hD.1 F F.top (c l).1 z (c l').1).2.2
  have h6 := h l
  have h7 := h l'
  have e : ∀ y w : F.Cell, siteSupDist y w = cellSupDist y w := fun _ _ => rfl
  simp only [e] at h2 h5 ⊢
  omega
end TopVariationAlongFields
open TopVariationAlongFields in
theorem topVariationAlongFields_holds (hKern : interpolationKernelBoundsStatement)
    (hNear : interpolatedFramesControlled) (hRS : rightTranslationChartStatement)
    (hMove : topVariationAlongField) (hDec : topVariationFieldDecayStatement)
    (hJoin : EventuallyInParametersCombines) (hD : SupDistCellComparison) :
    topVariationAlongFields := by
  obtain ⟨K, Dk, hKpos, -, hKT⟩ := hKern
  obtain ⟨Th, CT, hCT, hShift, hThs, hThb⟩ := hRS
  obtain ⟨M, hM0, hM⟩ := hDec
  have hP := hJoin.1 _ _ (hJoin.1 _ _ hKT hNear) (eventually_constants K M CT)
  refine hJoin.2 _ _ ?_ hP
  rintro T hT ⟨⟨hk, hn⟩, hnum⟩ t x hx F V s ht hcold hs0 hs1
  obtain ⟨hFL, -, n, hside, hn₀⟩ := id ht
  have hn2 : 2 ≤ n := hnum.two_le_n₀.trans hn₀
  have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by rw [hside i]; exact hn2
  have hLodd : Odd F.blockSide := hFL ▸ hT.odd_L
  have hρ : 0 < T.ballRadius := by
    have := hT.σ_pos
    unfold StepParameters.ballRadius
    positivity
  have hρ' : T.ballRadius = T.σ / 64 := rfl
  obtain ⟨-, hsmall⟩ := (hn t x hx).single F V s ht hcold hs0 hs1
  have hcl := hT.chain_admissible.classical.1
  have hρA : T.chainParams.ρA ≤ 1 := hcl.2.1
  have h0ball : ∀ b : ↥(chordBonds (finiteCells F)), ‖(0 : StepVariable (finiteCells F)) b‖ ≤ T.ballRadius :=
    fun b => by
      simpa using hρ.le
  have hker := hk x t F V s 0 hx ht hcold hs0 hs1 h0ball
  have hroom : ∀ b ∈ chordBonds (finiteCells F),
      ‖interpolatedFrame s T.a T.chainParams.ρA (frameRadius x) b V‖ + T.ballRadius ≤ 1 :=
    fun b hb => by
      have := hsmall.norm_add_le b hb
      rw [hρ']
      linarith
  have hper : ∀ i, F.period F.top i ≠ 0 := by
    intro i
    have h1 : F.extent i ≠ 0 := by have := hs2 i; omega
    simp [BlockFrame.period, h1]
  have hκ := hT.κ_pos
  have hκ₂ : 2 ^ 9 * T.κ ≤ T.chainParams.κ₂ := by
    have h1 := hcl.2.2.2.2.1
    have h2 := hnum.rate_le
    have h3 := hcl.2.2.2.1
    nlinarith
  have hr : 0 ≤ T.chainParams.κ₂ := by nlinarith
  refine ⟨⟨fun w X => Th w X, hShift, ?_, ?_⟩⟩
  · intro G η c X hη _ hG
    exact hMove F s T.a T.chainParams.ρA T.ballRadius (frameRadius x) V (fun w X => Th w X) hLodd hs2 hρ hShift
      hker.analytic hroom G η c X hη hG
  · intro c X b u k c' X' hX hu hk2 hX'
    have hfu : ‖interpolatedFrame s T.a T.chainParams.ρA (frameRadius x) b.1 V + u‖ ≤ 1 := by
      have h1 := hroom b.1 b.2
      have h2 := norm_add_le (interpolatedFrame s T.a T.chainParams.ρA (frameRadius x) b.1 V) u
      linarith
    have h1 := hM F s T.a T.chainParams.ρA T.chainParams.κ₂ CT (frameRadius x) V Th (K (rateParameters T)) b.1 c X u k
      c' X' hper hr (fun k => (hKpos _ k).le) hCT hThs hThb (hker.analytic b.1 b.2)
      (fun i cs Xs h1 hXs => hker.frame_deriv b.1 b.2 i cs Xs h1 hXs) hfu hX hk2 hX'
    refine h1.trans (mul_le_mul hnum.const_le ?_ (Real.exp_pos _).le ?_)
    · refine Real.exp_le_exp.2 ?_
      have h2 : (bondSpan (enclosingCell b.1.1) (Fin.cons c c' : Fin (k + 1) → F.Site F.top × Fin 4) : ℝ) ≤
          2 * (bondListDistance (enclosingCell b.1.1) (Fin.cons c c' : Fin (k + 1) → F.Site F.top × Fin 4) : ℝ) := by
        exact_mod_cast bondSpan_le_two_mul hD _ _
      have h3 : (0 : ℝ) ≤
          bondListDistance (enclosingCell b.1.1) (Fin.cons c c' : Fin (k + 1) → F.Site F.top × Fin 4) :=
        Nat.cast_nonneg _
      have h4 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 2 ^ 8 * T.κ)
      have h5 := mul_le_mul_of_nonneg_right hκ₂ h3
      nlinarith
    · have hK := fun k => (hKpos (rateParameters T) k).le
      have a1 := hK 1
      have a2 := hK 2
      have a3 := hK 3
      have : 0 ≤ M * (K (rateParameters T) 1 + K (rateParameters T) 2 + K (rateParameters T) 3) +
          CT * (1 + K (rateParameters T) 1 + K (rateParameters T) 1 ^ 2 + K (rateParameters T) 2) := by
        positivity
      linarith [hnum.const_le]
end Interpolation
end YangMills.Construction
end
