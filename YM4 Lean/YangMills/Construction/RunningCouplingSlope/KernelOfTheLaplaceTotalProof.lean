import YangMills.Construction.RunningCouplingSlope.CutLogarithmIsTwiceDifferentiable
import YangMills.Construction.RunningCouplingSlope.GapsAtTheLeastFieldAreSmall
import YangMills.Construction.RunningCouplingSlope.KernelOfTheLaplaceTotal
import YangMills.Construction.RunningCouplingSlope.LaplaceOfAFamilyOfExponents
import YangMills.Construction.RunningCouplingSlope.LaplaceTotalIsAGaugeFunction
import YangMills.Construction.RunningCouplingSlope.LaplaceTotalNearTheFlatField
import YangMills.Construction.RunningCouplingSlope.StepExponentNearTheFlatField
import YangMills.Construction.RunningCouplingSlope.StepTotalNearTheFlatField
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.TorusFields YangMills.Construction.RenormalizationStepParameters YangMills.Construction.StepSettings YangMills.Construction.LaplaceAsymptotics YangMills.Construction.SlopeCoefficient
namespace YangMills.Construction.RunningCouplingSlope
private theorem iteratedFDeriv_two_add_apply_zero {f g : (Fin 2 → ℝ) → ℝ} (hf : ContDiffAt ℝ 2 f 0)
    (hg : ContDiffAt ℝ 2 g 0) (v : Fin 2 → Fin 2 → ℝ) :
    iteratedFDeriv ℝ 2 (fun τ => f τ + g τ) 0 v =
      iteratedFDeriv ℝ 2 f 0 v + iteratedFDeriv ℝ 2 g 0 v := by
  have h := iteratedFDeriv_add_apply (𝕜 := ℝ) (i := 2) (x := (0 : Fin 2 → ℝ)) hf hg
  have h2 : iteratedFDeriv ℝ 2 (fun τ => f τ + g τ) 0 = iteratedFDeriv ℝ 2 f 0 + iteratedFDeriv ℝ 2 g 0 := h
  rw [h2]
  rfl
private theorem iteratedFDeriv_two_sub_apply_zero {f g : (Fin 2 → ℝ) → ℝ} (hf : ContDiffAt ℝ 2 f 0)
    (hg : ContDiffAt ℝ 2 g 0) (v : Fin 2 → Fin 2 → ℝ) :
    iteratedFDeriv ℝ 2 (fun τ => f τ - g τ) 0 v =
      iteratedFDeriv ℝ 2 f 0 v - iteratedFDeriv ℝ 2 g 0 v := by
  have hn : ContDiffAt ℝ 2 (fun τ => -g τ) 0 := hg.neg
  have e : (fun τ => f τ - g τ) = fun τ => f τ + -g τ := by
    funext τ
    ring
  have h3 : iteratedFDeriv ℝ 2 (fun τ => -g τ) 0 v = -iteratedFDeriv ℝ 2 g 0 v := by
    have := iteratedFDeriv_neg_apply (𝕜 := ℝ) (i := 2) (f := g) (x := (0 : Fin 2 → ℝ))
    have h4 : iteratedFDeriv ℝ 2 (fun τ => -g τ) 0 = -iteratedFDeriv ℝ 2 g 0 := this
    rw [h4]
    rfl
  rw [e, iteratedFDeriv_two_add_apply_zero hf hn, h3]
  ring
private theorem iteratedFDeriv_two_const_add_apply_zero (κ : ℝ) {f : (Fin 2 → ℝ) → ℝ}
    (hf : ContDiffAt ℝ 2 f 0) (v : Fin 2 → Fin 2 → ℝ) :
    iteratedFDeriv ℝ 2 (fun τ => κ + f τ) 0 v = iteratedFDeriv ℝ 2 f 0 v := by
  have hc : ContDiffAt ℝ 2 (fun _ : Fin 2 → ℝ => κ) 0 := contDiffAt_const
  have h0 : iteratedFDeriv ℝ 2 (fun _ : Fin 2 → ℝ => κ) 0 v = 0 := by
    rw [iteratedFDeriv_const_of_ne (by norm_num : (2 : ℕ) ≠ 0)]
    rfl
  rw [iteratedFDeriv_two_add_apply_zero hc hf, h0, zero_add]
private theorem perturb_eq_perturb_smul {n k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (s : ℝ) (hs : s ≠ 0) (σ : Fin k → ℝ) (W : TorusField n) :
    perturb c X σ W = perturb c (fun l => s • X l) (s⁻¹ • σ) W := by
  funext x i
  unfold perturb
  congr 2
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs
  · simp only [Pi.smul_apply, smul_eq_mul, smul_smul]
    rw [mul_comm s⁻¹, mul_assoc, inv_mul_cancel₀ hs, mul_one]
  · rfl
abbrev _root_.YangMills.SharedProofs.p22089 := @perturb_eq_perturb_smul
private theorem contDiffAt_laplaceRemainder_perturb (hS : LogCutoffIntegralContDiffTwo)
    (hB : stepExponentNearTrivialStatement) (hC : laplaceRemainderNearTrivialStatement)
    (T : ParameterAssignment) (hT : T.Admissible) (y : ℝ) (R : StepSetup) (hy : T.floorMin ≤ y)
    (hR : R.OnParameters T y) (n : ℕ) [NeZero n] (hn : T.n₀ ≤ n) (hside : n ≤ 4 * R.frameReach + 5) (k : ℕ)
    (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) :
    ContDiffAt ℝ 2 (fun σ : Fin k → ℝ => laplaceRemainder R n (perturb c X σ (trivialField n))) 0 := by
  have hρ : 0 < T.ballRadius := by
    have := hT.σ_pos
    unfold ParameterAssignment.ballRadius
    positivity
  set s : ℝ := (1 + ∑ l, ‖X l‖)⁻¹ with hs
  have hs0 : 0 < s := by positivity
  set Y : Fin k → imaginaryQuaternions := fun l => s • X l with hY
  have hYle : ∀ l, ‖Y l‖ ≤ 1 := by
    intro l
    have h1 : ‖X l‖ ≤ ∑ l, ‖X l‖ :=
      Finset.single_le_sum (f := fun l => ‖X l‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ l)
    rw [hY]
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hs0]
    rw [hs, inv_mul_le_iff₀ (by positivity)]
    linarith
  obtain ⟨C, q, -, -, hfam⟩ := hB T hT k
  obtain ⟨-, -, hL⟩ := hfam y R hy hR n c Y hn hYle
  obtain ⟨κ, hκ⟩ := hC T hT y R hy hR n k c Y hn hside
  have hJ : ContDiffAt ℝ 2 (logCutoffIntegral T.ballRadius T.cutoff R.coupling
      (chartEnergyAlongCurve R n c Y) (exponentRemainderAlongCurve R n c Y)) 0 :=
    hS _ k T.ballRadius R.coupling T.cutoff _ _ hρ hT.cut
      (fun η hη => (hL.contDiff_Q η hη).of_le (by norm_num)) (fun η hη => hL.contDiff_B η hη)
  have hK : ContDiffAt ℝ 2 (fun σ : Fin k → ℝ => laplaceRemainder R n (perturb c Y σ (trivialField n))) 0 :=
    (contDiffAt_const.add hJ).congr_of_eventuallyEq hκ
  have hlin : ContDiffAt ℝ 2 (fun σ : Fin k → ℝ => s⁻¹ • σ) 0 := (contDiff_const_smul _).contDiffAt
  have h0 : s⁻¹ • (0 : Fin k → ℝ) = 0 := smul_zero _
  have hK' : ContDiffAt ℝ 2 (fun σ : Fin k → ℝ => laplaceRemainder R n (perturb c Y σ (trivialField n)))
      (s⁻¹ • (0 : Fin k → ℝ)) := by
    rw [h0]
    exact hK
  have hcomp := ContDiffAt.comp (0 : Fin k → ℝ) hK' hlin
  have e : (fun σ : Fin k → ℝ => laplaceRemainder R n (perturb c X σ (trivialField n))) =
      (fun σ : Fin k → ℝ => laplaceRemainder R n (perturb c Y σ (trivialField n))) ∘
        fun σ : Fin k → ℝ => s⁻¹ • σ := by
    funext σ
    simp only [Function.comp_apply]
    rw [perturb_eq_perturb_smul c X s hs0.ne' σ]
  rw [e]
  exact hcomp
theorem laplaceRemainderHessianClose_of_components (hA : LaplaceMethodHessian)
    (hB : stepExponentNearTrivialStatement) (hC : laplaceRemainderNearTrivialStatement)
    (hD : stepTotalNearTrivialStatement) (hE : haarGapSumSecondDerivStatement)
    (hG : LaplaceRemainderIsGaugeFunctionNear) (hS : LogCutoffIntegralContDiffTwo) :
    LaplaceRemainderHessianClose := by
  refine ⟨fun _ => 1, fun _ => one_pos, fun T hT _ => ?_⟩
  have hρ : 0 < T.ballRadius := by
    have := hT.σ_pos
    unfold ParameterAssignment.ballRadius
    positivity
  have hlam : 0 < T.lam := hT.chain.2.2.1
  obtain ⟨CA, qA, hCA, hqA, hAT⟩ := hA T.ballRadius T.lam hρ hlam
  obtain ⟨CB, qB, hCB, hqB, hBT⟩ := hB T hT 2
  obtain ⟨CE, qE, hCE, hqE, hET⟩ := hE T hT
  set D : ℝ := 2 * CB with hD0
  have hDpos : 0 < D := by positivity
  set p : ℝ := qB * qA + qE with hp
  have hp0 : 0 ≤ p := by positivity
  set C : ℝ := CA * D ^ qA + CE with hCdef
  have hCpos : 0 < C := by positivity
  refine ⟨C, p, hCpos, hp0, ?_⟩
  intro y R hy hR _ n _ hn hside hsmall
  have hx1 : 1 ≤ R.coupling := by
    have h1 : (1 : ℝ) ≤ T.floorMin := by
      unfold ParameterAssignment.floorMin
      refine le_trans ?_ (le_max_right _ _)
      exact one_le_pow₀ (by norm_num)
    exact h1.trans (hy.trans hR.le_coupling)
  have hx0 : 0 < R.coupling := by linarith
  have hn1 : (1 : ℝ) ≤ n := by
    have : 1 ≤ n := Nat.pos_of_ne_zero (NeZero.ne n)
    exact_mod_cast this
  have hn0 : (0 : ℝ) < n := by linarith
  refine ⟨⟨contDiffAt_laplaceRemainder_perturb hS hB hC T hT y R hy hR n hn hside,
    hG T hT y R hy hR n hn hside⟩, ?_⟩
  intro b b' X X' hX hX'
  have hunits : AreUnitVectors ![X, X'] := by
    intro l
    fin_cases l
    · exact hX
    · exact hX'
  set c : Fin 2 → TorusBond n := ![b, b'] with hc
  set Xs : Fin 2 → imaginaryQuaternions := ![X, X'] with hXs
  obtain ⟨hne, hcard, hfam⟩ := hBT y R hy hR n c Xs hn (fun l => (hunits l).le)
  have := hne
  set N : ℝ := (Fintype.card ↥(chordBonds (finiteCells (torusFrame R.params.side R.depth n))) : ℝ) with hN
  set K : ℝ := CB * (n : ℝ) ^ qB with hK
  have hK0 : 0 ≤ K := by positivity
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hNK : N + K ≤ D * (n : ℝ) ^ qB := by
    rw [hD0]
    linarith
  have hpow : (N + K) ^ qA ≤ D ^ qA * (n : ℝ) ^ p := by
    calc (N + K) ^ qA ≤ (D * (n : ℝ) ^ qB) ^ qA :=
          Real.rpow_le_rpow (by positivity) hNK hqA
      _ = D ^ qA * (n : ℝ) ^ (qB * qA) := by
          rw [Real.mul_rpow hDpos.le (by positivity), ← Real.rpow_mul hn0.le]
      _ ≤ D ^ qA * (n : ℝ) ^ p := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact Real.rpow_le_rpow_of_exponent_le hn1 (by rw [hp]; linarith)
  have hxr : 0 < R.coupling ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hnp : 0 < (n : ℝ) ^ p := Real.rpow_pos_of_pos hn0 _
  have hfirst : CA * (N + K) ^ qA * R.coupling ^ (-(1 / 2) : ℝ) ≤
      CA * D ^ qA * (n : ℝ) ^ p * R.coupling ^ (-(1 / 2) : ℝ) := by
    refine mul_le_mul_of_nonneg_right ?_ hxr.le
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hpow hCA.le
  have hCE' : 0 ≤ CE * (n : ℝ) ^ p * R.coupling ^ (-(1 / 2) : ℝ) := by positivity
  have hle1 : CA * (N + K) ^ qA * R.coupling ^ (-(1 / 2) : ℝ) ≤ 1 := by
    have h1 : C * (n : ℝ) ^ p * R.coupling ^ (-(1 / 2) : ℝ) ≤ 1 := hsmall.trans (min_le_right _ _)
    have h2 : C * (n : ℝ) ^ p * R.coupling ^ (-(1 / 2) : ℝ) =
        CA * D ^ qA * (n : ℝ) ^ p * R.coupling ^ (-(1 / 2) : ℝ) +
          CE * (n : ℝ) ^ p * R.coupling ^ (-(1 / 2) : ℝ) := by
      rw [hCdef]
      ring
    linarith
  obtain ⟨hJ, hGs, hcore⟩ := hAT ↥(chordBonds (finiteCells (torusFrame R.params.side R.depth n)))
    T.cutoff K R.coupling (chartEnergyAlongCurve R n c Xs) (exponentRemainderAlongCurve R n c Xs)
    hT.cut hK0 hx1 hle1 hfam
  obtain ⟨κ, hκ⟩ := hC T hT y R hy hR n 2 c Xs hn hside
  obtain ⟨hSt, hRw, κ', hκ'⟩ := hD T hT y R hy hR n c Xs hn
  obtain ⟨hgaps, hsmallgaps⟩ := hET y R hy hR n c Xs hn hunits
  set e : Fin 2 → Fin 2 → ℝ := fun l => Pi.single l 1 with he
  have hL : hessianAtTrivial (laplaceRemainder R) n b b' X X' =
      iteratedFDeriv ℝ 2 (logCutoffIntegral T.ballRadius T.cutoff R.coupling (chartEnergyAlongCurve R n c Xs)
        (exponentRemainderAlongCurve R n c Xs)) 0 e := by
    have h1 : iteratedFDeriv ℝ 2 (fun σ : Fin 2 → ℝ => laplaceRemainder R n (perturb c Xs σ (trivialField n))) 0 =
        iteratedFDeriv ℝ 2 (fun τ => κ + logCutoffIntegral T.ballRadius T.cutoff R.coupling
          (chartEnergyAlongCurve R n c Xs) (exponentRemainderAlongCurve R n c Xs) τ) 0 :=
      (Filter.EventuallyEq.iteratedFDeriv ℝ hκ 2).eq_of_nhds
    have h2 : hessianAtTrivial (laplaceRemainder R) n b b' X X' =
        iteratedFDeriv ℝ 2 (fun σ : Fin 2 → ℝ => laplaceRemainder R n (perturb c Xs σ (trivialField n))) 0 e :=
      rfl
    rw [h2, h1, iteratedFDeriv_two_const_add_apply_zero κ hJ]
  have hS2 : hessianAtTrivial (stepGaugeTotal T.coupling T.ρA T.side R.depth) n b b' X X' +
      hessianAtTrivial (densityAtMinimizer R) n b b' X X' =
      iteratedFDeriv ℝ 2 (gaussianLogValue (chartEnergyAlongCurve R n c Xs)
          (exponentRemainderAlongCurve R n c Xs)) 0 e -
        iteratedFDeriv ℝ 2 (haarGapSumAlongCurve R n c Xs) 0 e := by
    have h0 : hessianAtTrivial (stepGaugeTotal T.coupling T.ρA T.side R.depth) n b b' X X' +
        hessianAtTrivial (densityAtMinimizer R) n b b' X X' =
        iteratedFDeriv ℝ 2 (fun τ : Fin 2 → ℝ =>
          stepGaugeTotal T.coupling T.ρA T.side R.depth n (perturb c Xs τ (trivialField n)) +
            densityAtMinimizer R n (perturb c Xs τ (trivialField n))) 0 e :=
      (iteratedFDeriv_two_add_apply_zero hSt hRw e).symm
    have h1 : iteratedFDeriv ℝ 2 (fun τ : Fin 2 → ℝ =>
          stepGaugeTotal T.coupling T.ρA T.side R.depth n (perturb c Xs τ (trivialField n)) +
            densityAtMinimizer R n (perturb c Xs τ (trivialField n))) 0 =
        iteratedFDeriv ℝ 2 (fun τ => κ' + gaussianLogValue (chartEnergyAlongCurve R n c Xs)
          (exponentRemainderAlongCurve R n c Xs) τ - haarGapSumAlongCurve R n c Xs τ) 0 :=
      (Filter.EventuallyEq.iteratedFDeriv ℝ hκ' 2).eq_of_nhds
    have hkg : ContDiffAt ℝ 2 (fun τ => κ' + gaussianLogValue (chartEnergyAlongCurve R n c Xs)
        (exponentRemainderAlongCurve R n c Xs) τ) 0 := contDiffAt_const.add hGs
    rw [h0, h1, iteratedFDeriv_two_sub_apply_zero hkg hgaps, iteratedFDeriv_two_const_add_apply_zero κ' hGs]
  have hgapbound := hsmallgaps
  have hxinv : R.coupling⁻¹ ≤ R.coupling ^ (-(1 / 2) : ℝ) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hnE : (n : ℝ) ^ qE ≤ (n : ℝ) ^ p :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by
      rw [hp]
      have : 0 ≤ qB * qA := by positivity
      linarith)
  have hgap2 : |iteratedFDeriv ℝ 2 (haarGapSumAlongCurve R n c Xs) 0 e| ≤
      CE * (n : ℝ) ^ p * R.coupling ^ (-(1 / 2) : ℝ) := by
    refine hsmallgaps.trans ?_
    have hx3 : 0 ≤ R.coupling⁻¹ := by positivity
    calc CE * (n : ℝ) ^ qE * R.coupling⁻¹ ≤ CE * (n : ℝ) ^ p * R.coupling⁻¹ := by
          refine mul_le_mul_of_nonneg_right ?_ hx3
          exact mul_le_mul_of_nonneg_left hnE hCE.le
      _ ≤ CE * (n : ℝ) ^ p * R.coupling ^ (-(1 / 2) : ℝ) :=
          mul_le_mul_of_nonneg_left hxinv (by positivity)
  have hsum : hessianAtTrivial (laplaceRemainder R) n b b' X X' -
      hessianAtTrivial (stepGaugeTotal T.coupling T.ρA T.side R.depth) n b b' X X' -
      hessianAtTrivial (densityAtMinimizer R) n b b' X X' =
      (iteratedFDeriv ℝ 2 (logCutoffIntegral T.ballRadius T.cutoff R.coupling (chartEnergyAlongCurve R n c Xs)
          (exponentRemainderAlongCurve R n c Xs)) 0 e -
        iteratedFDeriv ℝ 2 (gaussianLogValue (chartEnergyAlongCurve R n c Xs)
          (exponentRemainderAlongCurve R n c Xs)) 0 e) +
        iteratedFDeriv ℝ 2 (haarGapSumAlongCurve R n c Xs) 0 e := by
    rw [hL]
    linarith
  rw [hsum]
  refine (abs_add_le _ _).trans ?_
  have h3 : C * (n : ℝ) ^ p * R.coupling ^ (-(1 / 2) : ℝ) =
      CA * D ^ qA * (n : ℝ) ^ p * R.coupling ^ (-(1 / 2) : ℝ) +
        CE * (n : ℝ) ^ p * R.coupling ^ (-(1 / 2) : ℝ) := by
    rw [hCdef]
    ring
  rw [h3]
  exact add_le_add (hcore.trans hfirst) hgap2
end YangMills.Construction.RunningCouplingSlope
end
