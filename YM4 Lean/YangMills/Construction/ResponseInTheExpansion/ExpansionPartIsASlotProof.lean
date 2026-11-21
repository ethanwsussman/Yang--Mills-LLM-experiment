import YangMills.Construction.ResponseInTheExpansion.CalculusOfTheRest
import YangMills.Construction.ResponseInTheExpansion.ExpansionPartIsASlot
import YangMills.Construction.SummableBoundsOfTheFlow.JointSmoothnessFromMoves
import YangMills.Construction.SummableBoundsOfTheFlow.SitesOfACellAreFew
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
open MeasureTheory
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation IteratedDerivative Estimates CellCounting Calculus SmoothSlices
namespace WeightedResponses
namespace FamilyTermSlot
open ResponseInTheExpansion.RemainderCalculus
variable {F : BlockFrame}
theorem exp_neg_le_mul_two {κ n s d : ℝ} (hκ : 0 ≤ κ) (hs : s ≤ n) (hd : d ≤ n) (hs0 : 0 ≤ s) (hd0 : 0 ≤ d) :
    Real.exp (-(2 ^ 7 * κ * n)) ≤ Real.exp (-(2 ^ 5 * κ * s)) * Real.exp (-(2 * κ * d)) := by
  rw [← Real.exp_add, Real.exp_le_exp]
  have h1 : κ * s ≤ κ * n := mul_le_mul_of_nonneg_left hs hκ
  have h2 : κ * d ≤ κ * n := mul_le_mul_of_nonneg_left hd hκ
  nlinarith [mul_nonneg hκ hs0, mul_nonneg hκ hd0]
theorem exp_neg_le_mul_three {κ n s d d' : ℝ} (hκ : 0 ≤ κ) (hs : s ≤ n) (hd : d ≤ n) (hd' : d' ≤ n) (hs0 : 0 ≤ s) (hd0 : 0 ≤ d)
    (hd'0 : 0 ≤ d') :
    Real.exp (-(2 ^ 7 * κ * n)) ≤ Real.exp (-(2 ^ 5 * κ * s)) * Real.exp (-(2 * κ * d)) * Real.exp (-(κ * d')) := by
  rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  have h1 : κ * s ≤ κ * n := mul_le_mul_of_nonneg_left hs hκ
  have h2 : κ * d ≤ κ * n := mul_le_mul_of_nonneg_left hd hκ
  have h3 : κ * d' ≤ κ * n := mul_le_mul_of_nonneg_left hd' hκ
  nlinarith [mul_nonneg hκ hs0, mul_nonneg hκ hd0, mul_nonneg hκ hd'0]
theorem runningMax_le (e : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B) (he : ∀ j, e j ≤ B) (p : ℕ) : runningMax e p ≤ B := by
  induction p with
  | zero => exact hB
  | succ p ih => exact max_le ih (he _)
theorem card_sites_filter_le (hSites : SitesPerCellLePow) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (Y : F.Cell)
    [DecidablePred fun y : F.Site F.depth => enclosingCell y = Y] :
    ((sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y)).card ≤ F.blockSide ^ 4 := by
  classical
  have h := hSites F (finiteCells F) hL hs Y
  have e : (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y) =
      (Finset.univ.filter fun y : ↥(sitesOfCells (finiteCells F) F.depth) => enclosingCell y.1 = Y).map
        ⟨Subtype.val, Subtype.val_injective⟩ := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk, Subtype.exists,
      exists_and_left, exists_prop, exists_eq_right_right]
    tauto
  rw [e, Finset.card_map]
  convert h
end FamilyTermSlot
open FamilyTermSlot ResponseInTheExpansion.RemainderCalculus in
theorem familyTermSlotStatement_proof (hPB : remainderOfBoundsStatement) (hTr : transportBoundsStatement)
    (hJS : JointlyContDiffOnBallsOfDisplacements) (hL : DerivAlongRulesHold)
    (hAl : JointMixedDerivEqDerivAlong) (hTwo : IteratedFDerivParamDiff)
    (hSl : IteratedFDerivSlices) (hSum : _root_.YangMills.Construction.CellCounting.ExpDecaySumBounded)
    (hFew : cellBondsCardStatement) (hSites : SitesPerCellLePow) (hJ : EventuallyInParametersCombines) :
    familyTermSlotStatement := by
  classical
  obtain ⟨join, weaken⟩ := hJ
  obtain ⟨Ct, Ck, hCt, hCk, hTT⟩ := hTr
  choose! Wf hWf0 hWf using hSum
  let A₀ : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℝ := fun U => Ct (rateParameters U) * (U.E + U.energyRatio)
  let At : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℝ := fun U => |(U.L : ℝ) ^ 4 * (A₀ U * (1 + U.ballRadius * Wf (4 * U.L ^ 4) U.κ))|
  obtain ⟨Cq, C, hCq, hC, hPT⟩ := hPB At fun T => abs_nonneg _
  refine ⟨Cq, C, hCq, hC, ?_⟩
  have h64 : EventuallyInParameters fun T => 64 ≤ T.n₀ ∧ 1 ≤ T.coupling := fun _ _ => ⟨0, fun _ _ _ _ _ => ⟨0, fun _ _ =>
    ⟨1, one_pos, fun _ _ _ => ⟨1, one_pos, fun _ _ _ _ => ⟨0, fun _ _ => ⟨1, one_pos,
      fun _ _ _ _ _ => ⟨0, fun _ _ _ _ => ⟨64, fun _ h => ⟨0, fun _ _ => ⟨1, fun _ hy => ⟨h, hy⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  refine weaken _ _ ?_ (join _ _ hPT (join _ _ hTT h64))
  rintro T hDr ⟨hPBT, hTrT, h64', hy1⟩
  intro t x f F V Y hst hrow
  have hfl : T.coupling ≤ x := hst.coupling_le
  have hx : 0 < x := by linarith
  set Q := coldHalfLawAt T x f with hQ
  set U := parametersBeforeSide T with hU
  have hρ : 0 < T.ballRadius := by
    have := hDr.σ_pos
    show 0 < T.σ / 64
    positivity
  have hκ : 0 < T.κ := hDr.κ_pos
  have hE : 1 ≤ T.E := hDr.one_le_E
  have hE₃ : 0 ≤ T.energyRatio := by
    have := hDr.η₃_pos
    show 0 ≤ T.E / T.η₃
    positivity
  obtain ⟨hLF, htt, n, hside, hn⟩ := hst.torus
  have hnpos : 64 ≤ n := h64'.trans hn
  have hoddF : Odd F.blockSide := by rw [hLF]; exact hDr.odd_L
  have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by rw [hside]; omega
  have hN : ∀ z : F.Cell, (Finset.univ.filter fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1 = z).card ≤
      4 * U.L ^ 4 := fun z => by
    have := hFew F hoddF hs2 z
    rwa [hLF] at this
  have hS₀ : ∑ b : ↥(chordBonds (finiteCells F)), Real.exp (-(T.κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ))) ≤
      Wf (4 * U.L ^ 4) U.κ :=
    hWf _ _ hκ F ↥(chordBonds (finiteCells F)) (fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1) hN Y
  have hUo : IsOpen {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ < T.ballRadius} := by
    have : {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ < T.ballRadius} =
        ⋂ b, {η : StepVariable (finiteCells F) | ‖η b‖ < T.ballRadius} := by
      ext η; simp
    rw [this]
    exact isOpen_iInter_of_finite fun b => isOpen_lt (continuous_norm.comp (continuous_apply b)) continuous_const
  let e : ℕ → ℝ := fun j => if j = 3 then T.energyRatio else T.E
  have he0 : ∀ j, 0 ≤ e j := fun j => by
    simp only [e]
    split_ifs
    · exact hE₃
    · linarith
  have heB : ∀ j, e j ≤ T.E + T.energyRatio := fun j => by
    simp only [e]
    split_ifs <;> linarith
  have hD : HasBoundedDerivatives T.L t T.n₀ T.σ T.decayRate 3 e f :=
    ⟨fun F' hF y W hW j c X => hst.family_bounded.smooth F' hF y W hW j c X,
      fun F' hF y W γ hW => hst.family_bounded.gauge_invariant F' hF y W γ hW,
      fun F' hF y W j c X hW h1 h3 hX => hst.family_bounded.decay F' hF y W j c X hW h1 h3 hX⟩
  have hT : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ T.ballRadius) →
      IsTransportBounded 1 T.a T.chainParams.ρA T.κ T.decayRate (Ct (rateParameters T)) (Ck (rateParameters T)) T.L
        (frameRadius x) 3 e f V η :=
    fun η hη => hTrT x t 3 e f F V 1 η hfl (by norm_num) (by norm_num) he0 hD ⟨hLF, htt, n, hside, hn⟩
      hst.small_curvature zero_le_one le_rfl hη
  have hCpos : 0 < Ct (rateParameters T) := hCt _
  set B₀ := Ct (rateParameters T) * (T.E + T.energyRatio) with hB₀
  have hB₀0 : 0 ≤ B₀ := by positivity
  have hlarge : ∀ p, Ct (rateParameters T) * runningMax e p ≤ B₀ := fun p =>
    mul_le_mul_of_nonneg_left (runningMax_le e _ (by linarith) heB p) hCpos.le
  have hsite : ∀ y ∈ (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y),
      ResponseInTheExpansion.RemainderCalculus.HasDilationBounds T B₀ Y Finset.univ
        (interpolatedExpansion 1 T.a T.chainParams.ρA (frameRadius x) f y) V := by
    intro y hy
    have hyY : enclosingCell y = Y := (Finset.mem_filter.1 hy).2
    set G := interpolatedExpansion 1 T.a T.chainParams.ρA (frameRadius x) f y with hG
    have hjs : JointlyContDiffOnBalls T.ballRadius V G := hJS F T.ballRadius V G fun η hη l j b u c X hu hX =>
      (hT η hη).smooth y l j b u c X hu hX
    refine ⟨fun k c X η hη => hjs k c X η hη, fun k c X hk hX η hη b _ e' => ?_, fun k c X hk hX η hη b _ b₀ e₁ e₂ => ?_⟩
    · have h33 : ContDiffAt ℝ 3 (rotatedEval G V c X) (η, 0) :=
        rotatedEval_contDiffAt (show ContDiffAt ℝ 3 (paramFirstEval G V c X) (0, η) from hjs k c X η fun b => (hη b).le)
      have hs : ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (rotatedEval G V c X) (η, 0) :=
        h33.of_le (by exact_mod_cast (by omega : k + 1 ≤ 3))
      refine abs_fderiv_bondDeriv_le hL hAl hs b (fun u hu => ?_) e'
      have hb := (hT η fun b => (hη b).le).jointDeriv_le y 1 k ![b] ![u] c X (by omega) (by omega)
        (fun i => by fin_cases i; exact hu) hX
      refine hb.trans ?_
      set P := insert (enclosingCell y) (chordBondCells ![b] ∪ topBondCells c) with hP
      have m1 : Y ∈ P := by
        rw [hP, hyY]
        exact Finset.mem_insert_self _ _
      have m2 : enclosingCell b.1.1 ∈ P := by
        rw [hP]
        refine Finset.mem_insert_of_mem (Finset.mem_union_left _ ?_)
        exact Finset.mem_image.2 ⟨0, Finset.mem_univ _, rfl⟩
      have m3 : ∀ l, (c l).1 ∈ P := fun l => by
        rw [hP]
        refine Finset.mem_insert_of_mem (Finset.mem_union_right _ ?_)
        exact Finset.mem_image.2 ⟨l, Finset.mem_univ _, rfl⟩
      have h1 : (bondSpan Y c : ℝ) ≤ cellSetDiameter P := by exact_mod_cast bondSpan_le_cellSetDiameter m1 m3
      have h2 : (cellSupDist (enclosingCell b.1.1) Y : ℝ) ≤ cellSetDiameter P := by
        exact_mod_cast cellSupDist_le_cellSetDiameter m2 m1
      have h3 := exp_neg_le_mul_two hκ.le h1 h2 (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      have h4 := hlarge (1 + k)
      have hexp := (Real.exp_pos (-(2 ^ 7 * T.κ * (cellSetDiameter P : ℝ)))).le
      calc Ct (rateParameters T) * runningMax e (1 + k) * Real.exp (-(2 ^ 7 * T.κ * (cellSetDiameter P : ℝ))) ≤
            B₀ * Real.exp (-(2 ^ 7 * T.κ * (cellSetDiameter P : ℝ))) := mul_le_mul_of_nonneg_right h4 hexp
        _ ≤ B₀ * (Real.exp (-(2 ^ 5 * T.κ * bondSpan Y c)) *
              Real.exp (-(2 * T.κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ)))) :=
            mul_le_mul_of_nonneg_left h3 hB₀0
        _ = _ := by ring
    · have h33 : ContDiffAt ℝ 3 (rotatedEval G V c X) (η, 0) :=
        rotatedEval_contDiffAt (show ContDiffAt ℝ 3 (paramFirstEval G V c X) (0, η) from hjs k c X η fun b => (hη b).le)
      have hs : ContDiffAt ℝ ((k + 2 : ℕ) : WithTop ℕ∞) (rotatedEval G V c X) (η, 0) :=
        h33.of_le (by exact_mod_cast (by omega : k + 2 ≤ 3))
      refine abs_fderiv_fderiv_bondDeriv_le hL hAl hs b b₀ (fun u u' hu hu' => ?_) e₁ e₂
      have hb := (hT η fun b => (hη b).le).jointDeriv_le y 2 k ![b₀, b] ![u', u] c X (by omega) (by omega)
        (fun i => by fin_cases i; exacts [hu', hu]) hX
      refine hb.trans ?_
      set P := insert (enclosingCell y) (chordBondCells ![b₀, b] ∪ topBondCells c) with hP
      have m1 : Y ∈ P := by
        rw [hP, hyY]
        exact Finset.mem_insert_self _ _
      have m2 : enclosingCell b₀.1.1 ∈ P := by
        rw [hP]
        refine Finset.mem_insert_of_mem (Finset.mem_union_left _ ?_)
        exact Finset.mem_image.2 ⟨0, Finset.mem_univ _, rfl⟩
      have m2' : enclosingCell b.1.1 ∈ P := by
        rw [hP]
        refine Finset.mem_insert_of_mem (Finset.mem_union_left _ ?_)
        exact Finset.mem_image.2 ⟨1, Finset.mem_univ _, rfl⟩
      have m3 : ∀ l, (c l).1 ∈ P := fun l => by
        rw [hP]
        refine Finset.mem_insert_of_mem (Finset.mem_union_right _ ?_)
        exact Finset.mem_image.2 ⟨l, Finset.mem_univ _, rfl⟩
      have h1 : (bondSpan Y c : ℝ) ≤ cellSetDiameter P := by exact_mod_cast bondSpan_le_cellSetDiameter m1 m3
      have h2 : (cellSupDist (enclosingCell b₀.1.1) Y : ℝ) ≤ cellSetDiameter P := by
        exact_mod_cast cellSupDist_le_cellSetDiameter m2 m1
      have h2' : (cellSupDist (enclosingCell b.1.1) Y : ℝ) ≤ cellSetDiameter P := by
        exact_mod_cast cellSupDist_le_cellSetDiameter m2' m1
      have h3 := exp_neg_le_mul_three hκ.le h1 h2 h2' (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      have h4 := hlarge (2 + k)
      have hexp := (Real.exp_pos (-(2 ^ 7 * T.κ * (cellSetDiameter P : ℝ)))).le
      calc Ct (rateParameters T) * runningMax e (2 + k) * Real.exp (-(2 ^ 7 * T.κ * (cellSetDiameter P : ℝ))) ≤
            B₀ * Real.exp (-(2 ^ 7 * T.κ * (cellSetDiameter P : ℝ))) := mul_le_mul_of_nonneg_right h4 hexp
        _ ≤ B₀ * (Real.exp (-(2 ^ 5 * T.κ * bondSpan Y c)) *
              Real.exp (-(2 * T.κ * (cellSupDist (enclosingCell b₀.1.1) Y : ℝ))) *
              Real.exp (-(T.κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ)))) := mul_le_mul_of_nonneg_left h3 hB₀0
        _ = _ := by ring
  have hsum := ResponseInTheExpansion.RemainderCalculus.HasRemainderBounds.finset_sum hSl
    ((sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y)) hUo
    (K := fun y => ResponseInTheExpansion.RemainderCalculus.dilation Finset.univ
      (interpolatedExpansion 1 T.a T.chainParams.ρA (frameRadius x) f y))
    (A := fun _ => B₀ * (1 + T.ballRadius * Wf (4 * U.L ^ 4) U.κ)) (T := T) (x := x) (Y := Y) (V := V)
    fun y hy => (hsite y hy).hasRemainderBounds hTwo hSl hx.le hB₀0 hκ.le hρ.le hUo hS₀
  have hfin : HasRemainderBounds T x (At U) Y (Q.familyTerm Y) V := by
    refine ResponseInTheExpansion.RemainderCalculus.HasRemainderBounds.mono hx.le ?_ hsum
    have hcard := card_sites_filter_le hSites hoddF hs2 Y
    rw [Finset.sum_const, nsmul_eq_mul]
    have hS0 : 0 ≤ Wf (4 * U.L ^ 4) U.κ := hWf0 _ _ hκ
    have hAc : 0 ≤ B₀ * (1 + T.ballRadius * Wf (4 * U.L ^ 4) U.κ) := by positivity
    have h1 : (((sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y)).card : ℝ) ≤
        (T.L : ℝ) ^ 4 := by
      have := hcard
      rw [hLF] at this
      exact_mod_cast this
    refine (mul_le_mul_of_nonneg_right h1 hAc).trans (le_abs_self _)
  exact hPBT t x f F V Y _ ⟨hst.coupling_le, hst.family_bounded, ⟨hLF, htt, n, hside, hn⟩, hst.small_curvature⟩ hfin
end WeightedResponses
end YangMills.Construction
end
