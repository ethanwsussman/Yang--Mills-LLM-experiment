import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionAtANearFlatTopProof
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionFarFromItsBlock
import YangMills.Construction.ColdStepAtMirrorFrames.TransportParameters
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace ExpansionOffBlock
open BlockOffsets
variable {F : BlockFrame}
open Classical in
theorem card_sites_in_cell_le (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (Y : F.Cell) :
    ((sitesOfCells (finiteCells F) F.depth).filter fun y => enclosingCell y = Y).card ≤ F.blockSide ^ 4 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CentredExpansionNearUniformTopProof.card_block_le <;> assumption
theorem expansionOffBlockDecayAt_of_bounds (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) {q : ℝ} (hL : TransportConditionsAt T q)
    (hb : CentredExpansionsBoundedAt T) : ExpansionOffBlockDecayAt T := by
  classical
  intro t x f F V hx hf hF hV star Y η k c X hη hk1 hk3 hX
  obtain ⟨hd, _, hCt, hn0, _⟩ := hL
  have B := hb t x f F V star hx hf hF hV
  obtain ⟨hFL, _, n, hsn, hnn⟩ := id hF
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by rw [hsn i]; omega
  have hLF : Odd F.blockSide := by rw [hFL]; exact hd.odd_L
  have hη' : ∀ b, ‖η b‖ ≤ T.ballRadius := fun b => (hη b).le
  have hcd : ∀ y : F.Site F.depth, ContDiffAt ℝ k
      (fun τ : Fin k → ℝ => centredExpansion star T.a T.chainParams.ρA (frameRadius x) f y η
        (leftTranslate (bondSpread c X τ) V)) 0 := by
    intro y
    have h1 := B.smooth y η k c X hη'
    have h2 : ContDiffAt ℝ 3 (fun τ : Fin k → ℝ => ((τ, η) : (Fin k → ℝ) × StepVariable (finiteCells F))) 0 :=
      contDiffAt_id.prodMk contDiffAt_const
    have h3 := ContDiffAt.comp (0 : Fin k → ℝ) h1 h2
    exact h3.of_le (by exact_mod_cast hk3)
  have e : bondDeriv (cellCentredExpansion star T.a T.chainParams.ρA (frameRadius x) f Y η) V c X =
      ∑ y ∈ (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y),
        bondDeriv (centredExpansion star T.a T.chainParams.ρA (frameRadius x) f y η) V c X := by
    unfold bondDeriv cellCentredExpansion
    have h1 := iteratedFDeriv_fun_sum_apply (𝕜 := ℝ) (n := k)
      (u := (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y))
      (f := fun y (τ : Fin k → ℝ) => centredExpansion star T.a T.chainParams.ρA (frameRadius x) f y η
        (leftTranslate (bondSpread c X τ) V))
      (x := 0) (fun y _ => hcd y)
    rw [h1]
    simp
  rw [e]
  set bnd := T.Ct * (if k = 3 then T.energyRatio else T.E) *
    (1 / torusDecayFactor T.L T.decayRate ((T.L : ℝ) * bondSpan Y c / 16) +
      Real.exp (-(2 ^ 6 * T.κ * bondSpan Y c))) with hbnd
  have hE1 := hd.one_le_E
  have hE3 : 0 < T.energyRatio := by
    unfold StepParameters.energyRatio
    have := hd.η₃_pos
    positivity
  have hEk : 0 < (if k = 3 then T.energyRatio else T.E) := by split_ifs <;> linarith
  have hG : 0 < torusDecayFactor T.L T.decayRate ((T.L : ℝ) * bondSpan Y c / 16) := by
    unfold torusDecayFactor
    have h1 : (1 : ℝ) ≤ max 1 (((T.L : ℝ) * bondSpan Y c / 16 / (T.L : ℝ) ^ (1 / 640 : ℝ)) ^ 16000) :=
      le_max_left _ _
    exact mul_pos (lt_of_lt_of_le one_pos h1) (Real.exp_pos _)
  have hb0 : 0 ≤ bnd := by
    have := Real.exp_pos (-(2 ^ 6 * T.κ * bondSpan Y c))
    positivity
  have h2 := Finset.abs_sum_le_sum_abs
    (fun y => bondDeriv (centredExpansion star T.a T.chainParams.ρA (frameRadius x) f y η) V c X)
    ((sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y))
  have h3 : ∑ y ∈ (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y),
      |bondDeriv (centredExpansion star T.a T.chainParams.ρA (frameRadius x) f y η) V c X| ≤
      (((sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y)).card : ℝ) * bnd := by
    have := Finset.sum_le_card_nsmul ((sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y))
      (fun y => |bondDeriv (centredExpansion star T.a T.chainParams.ρA (frameRadius x) f y η) V c X|) bnd
      (fun y hy => B.deriv_top Y y η k c X (Finset.mem_filter.mp hy).2 hη hk1 hk3 hX)
    simpa using this
  have h4 : (((sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y)).card : ℝ) ≤
      (T.L : ℝ) ^ 4 := by
    have := card_sites_in_cell_le hLF hs Y
    rw [hFL] at this
    exact_mod_cast this
  have h5 := mul_le_mul_of_nonneg_right h4 hb0
  have e2 : (T.L : ℝ) ^ 4 * T.Ct * (if k = 3 then T.energyRatio else T.E) *
      (1 / torusDecayFactor T.L T.decayRate ((T.L : ℝ) * bondSpan Y c / 16) +
        Real.exp (-(2 ^ 6 * T.κ * bondSpan Y c))) =
      (T.L : ℝ) ^ 4 * bnd := by
    rw [hbnd]; ring
  rw [e2]
  linarith
end ExpansionOffBlock
open ExpansionOffBlock
theorem expansionOffBlockDecay_holds (hj : EventuallyInParametersCombines) (hL : transportConditionsEventually)
    (hb : CentredExpansionsBounded) : ExpansionOffBlockDecay :=
  hj.2 _ _ (fun T _ h => expansionOffBlockDecayAt_of_bounds T h.1 h.2) (hj.1 _ _ (hL fun _ => 0) hb)
end YangMills.Construction.ColdStepAtMirrorFrames
end
