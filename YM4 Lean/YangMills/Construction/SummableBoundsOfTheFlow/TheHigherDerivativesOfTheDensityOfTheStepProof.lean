import YangMills.Construction.RunningCouplingSlope.ContoursAtTheLeastFieldHaveKernelsProof
import YangMills.Construction.RunningCouplingSlope.DerivativesOfTheDensityOfTheStepDecayAtParametersProof
import YangMills.Construction.SummableBoundsOfTheFlow.KernelsOfTheContoursAboveTheFrames
import YangMills.Construction.SummableBoundsOfTheFlow.KernelsOfTheHaarDensityAboveTheFrames
import YangMills.Construction.SummableBoundsOfTheFlow.TheHigherDerivativesOfTheDensityOfTheStep
import YangMills.Construction.SummableBoundsOfTheFlow.TheTraceOfTheHessianHasKernels
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.Interpolation YangMills.Construction.IteratedDerivative YangMills.Construction.Estimates YangMills.Construction.ReferenceDensity YangMills.Construction.TorusFields
namespace YangMills.Construction.StepDensities
variable {F : BlockFrame}
private theorem interpolatedCoords_zero (a ρ : ℝ) (m : ℕ) (V : F.GaugeField F.top)
    (ζ : StepVariable (finiteCells F)) :
    interpolatedCoords 0 a ρ m V ζ = coordsAboveFrame true a ρ 0 V ζ := by apply _root_.YangMills.SharedProofs.p718 <;> assumption
private theorem interpolatedField_zero (a ρ : ℝ) (m : ℕ) (V : F.GaugeField F.top)
    (ζ : StepVariable (finiteCells F)) :
    interpolatedField 0 a ρ m V ζ = fieldAboveFrame true a ρ 0 V ζ := by
  unfold interpolatedField fieldAboveFrame
  rw [interpolatedCoords_zero]
private theorem jointMixedDeriv_of_no_chords (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ)
    (η : StepVariable (finiteCells F))
    (V : F.GaugeField F.top) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (b : Fin 0 → ↥(chordBonds (finiteCells F))) (w : Fin 0 → EuclideanSpace ℝ (Fin 3))
    (h : ContDiffAt ℝ ((0 + k : ℕ) : WithTop ℕ∞) (jointDisplacement G η V b w c X) 0) :
    ContDiffAlongBonds k (G η) V c X ∧ jointMixedDeriv G η V b w c X = bondDeriv (G η) V c X := by apply _root_.YangMills.SharedProofs.p100707 <;> assumption
private theorem bondSpan_le_diameter {k : ℕ} (Y : F.Cell) (c : Fin k → F.Site F.top × Fin 4) :
    bondSpan Y c ≤ cellSetDiameter ({Y} ∪ topBondCells c) := by apply _root_.YangMills.SharedProofs.p63056 <;> assumption
private theorem two_le_n₀ : EventuallyInParameters fun T => 2 ≤ T.n₀ := by
  intro a _
  refine ⟨0, fun L _ _ c _ => ⟨0, fun Ct _ => ⟨1, one_pos, fun κ _ _ => ⟨1, one_pos, fun η₃ _ _ _ => ⟨0, fun nss _ =>
    ⟨1, one_pos, fun σ _ _ p _ => ⟨0, fun Cs _ E _ => ⟨2, fun n₀ hn => ⟨0, fun CE _ => ⟨0, fun y₁ _ => hn⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
abbrev _root_.YangMills.SharedProofs.p10519 := @two_le_n₀
private theorem card_innerBonds_at_cell_le (Y : F.Cell) [DecidablePred fun c : F.Site F.top × Fin 4 => c.1 = Y] :
    ((innerBonds (finiteCells F) F.top).filter fun c => c.1 = Y).card ≤ 4 := by apply _root_.YangMills.SharedProofs.p2730 <;> assumption
theorem stepDensityHigherDerivBound_of_kernels (hTr : HessianTraceDecay)
    (hC : contourKernelDerivBound) (hJ : haarDensityKernelBounds)
    (hP : BondDerivSumProductRules) (hO : TopFamilyDerivBoundsOnTori)
    (hB : cellBondsCardStatement) : StepDensityHigherDerivBound := by
  obtain ⟨Dc, hDc, hC⟩ := hC
  obtain ⟨Dh, hDh, hJ⟩ := hJ
  have h₀ : EventuallyOrdered _ := hTr
  unfold EventuallyOrdered at h₀
  unfold StepDensityHigherDerivBound EventuallyOrdered
  refine EventuallyInParameters.mono (EventuallyInParameters.and h₀
    (EventuallyInParameters.and hC (EventuallyInParameters.and hJ two_le_n₀))) ?_
  rintro T ⟨g₀, gC, gJ, hn₂⟩ hT hn₁
  obtain ⟨Ct, gT⟩ := g₀ hT hn₁
  have hκ0 : 0 < T.κ := hT.κ_pos
  have hσ0 : 0 < T.σ := hT.σ_pos
  set DC : ℝ := ∑ a ∈ Finset.range 7, Dc (rateParameters T) 0 a with hDC
  set DH : ℝ := ∑ a ∈ Finset.range 7, Dh (rateParameters T) 0 a with hDH
  have hDCa : ∀ a, a ≤ 6 → Dc (rateParameters T) 0 a ≤ DC := fun a ha =>
    Finset.single_le_sum (f := fun b => Dc (rateParameters T) 0 b) (fun b _ => (hDc _ _ b).le)
      (Finset.mem_range.2 (by omega))
  have hDHa : ∀ a, a ≤ 6 → Dh (rateParameters T) 0 a ≤ DH := fun a ha =>
    Finset.single_le_sum (f := fun b => Dh (rateParameters T) 0 b) (fun b _ => (hDh _ _ b).le)
      (Finset.mem_range.2 (by omega))
  have hDC0 : 0 ≤ DC := Finset.sum_nonneg fun b _ => (hDc _ _ b).le
  have hDH0 : 0 ≤ DH := Finset.sum_nonneg fun b _ => (hDh _ _ b).le
  refine ⟨|Ct| + 6 * DC + 4 * (T.L : ℝ) ^ 4 * DH, fun ℓ _ _ t n _ hn y W hW k c X h4 h6 hX => ?_⟩
  have hcold : IsCold (5 / 4 * T.σ) W := fun x μ ν h => (hW x μ ν h).trans_le (by linarith)
  refine hO T.L t T.n₀ 6 (5 / 4 * T.σ) (fun _ Y V => stepDensity T.a T.ρA T.lam Y V)
    (fun _ m => (|Ct| + 6 * DC + 4 * (T.L : ℝ) ^ 4 * DH) * Real.exp (-(2 ^ 6 * T.κ * m))) ?_ n hn y W hcold k c X
    (by omega) h6 hX
  clear hW hcold h4 h6 hX c X k W y hn
  intro F hF Y V k c X hV h1 h6 hX
  classical
  have hF' := hF
  obtain ⟨hFL, -, m, hside, hmn⟩ := hF'
  have hside2 : ∀ i, 2 ≤ F.extent i := by
    intro i
    rw [hside i]
    omega
  have hodd : Odd F.blockSide := hFL ▸ hT.odd_L
  have hρ : ∀ b, ‖(0 : StepVariable (finiteCells F)) b‖ ≤ T.ballRadius := by
    intro b
    have : 0 < T.ballRadius := by
      unfold StepParameters.ballRadius
      positivity
    simpa using this.le
  obtain ⟨sI, bI⟩ := gT t F V Y k c X hF hV h6 hX
  obtain ⟨hsum, hsmul, -⟩ := hP F V k c X
  set S : ℕ := cellSetDiameter ({Y} ∪ topBondCells c) with hSdef
  let Gc : (F.Site F.top × Fin 4) → F.GaugeField F.top → ℝ := fun c₀ V' =>
    Real.log ‖contourAverage (fieldAboveFrame true T.a T.ρA 0 V' 0) c₀‖
  have hGc : ∀ c₀ : F.Site F.top × Fin 4, c₀.1 = Y → ContDiffAlongBonds k (Gc c₀) V c X ∧
      |bondDeriv (Gc c₀) V c X| ≤ DC * Real.exp (-(2 ^ 8 * T.κ * S)) := by
    intro c₀ hc₀
    have h := gC T.coupling t F V 0 0 le_rfl hF hV le_rfl zero_le_one hρ c₀ 0 k (fun i => i.elim0) (fun i => i.elim0)
      c X (by omega) (fun i => i.elim0) hX
    obtain ⟨p, q⟩ := jointMixedDeriv_of_no_chords _ _ V c X _ _ h.1
    have e : (fun V' => Real.log ‖contourAverage (interpolatedField 0 T.a T.chainParams.ρA (frameRadius T.coupling) V' 0) c₀‖) = Gc c₀ := by
      funext V'
      rw [interpolatedField_zero]
      rfl
    simp only [e] at p q
    refine ⟨p, ?_⟩
    have hb := h.2
    rw [q, hc₀] at hb
    have e2 : ({Y} ∪ chordBondCells (fun i : Fin 0 => i.elim0) ∪ topBondCells c : Finset F.Cell) =
        {Y} ∪ topBondCells c := by
      simp [chordBondCells]
    rw [e2] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (hDCa _ h6) (Real.exp_pos _).le)
  let Gh : ↥(chordBonds (finiteCells F)) → F.GaugeField F.top → ℝ := fun b₀ V' =>
    haarLogRatio (coordsAboveFrame true T.a T.ρA 0 V' 0 b₀.1.1 b₀.1.2)
  have hGh : ∀ b₀ : ↥(chordBonds (finiteCells F)), enclosingCell b₀.1.1 = Y → ContDiffAlongBonds k (Gh b₀) V c X ∧
      |bondDeriv (Gh b₀) V c X| ≤ DH * Real.exp (-(2 ^ 8 * T.κ * S)) := by
    intro b₀ hb₀
    have h := gJ T.coupling t F V 0 0 le_rfl hF hV le_rfl zero_le_one hρ b₀ 0 k (fun i => i.elim0) (fun i => i.elim0)
      c X (by omega) (fun i => i.elim0) hX
    obtain ⟨p, q⟩ := jointMixedDeriv_of_no_chords _ _ V c X _ _ h.1
    have e : (fun V' => haarLogRatio (interpolatedCoords 0 T.a T.chainParams.ρA (frameRadius T.coupling) V' 0 b₀.1.1 b₀.1.2)) = Gh b₀ := by
      funext V'
      rw [interpolatedCoords_zero]
      rfl
    simp only [e] at p q
    refine ⟨p, ?_⟩
    have hb := h.2
    rw [q, hb₀] at hb
    have e2 : ({Y} ∪ chordBondCells (fun i : Fin 0 => i.elim0) ∪ topBondCells c : Finset F.Cell) =
        {Y} ∪ topBondCells c := by
      simp [chordBondCells]
    rw [e2] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (hDHa _ h6) (Real.exp_pos _).le)
  let Bs := (innerBonds (finiteCells F) F.top).filter fun c => c.1 = Y
  let Cb := Finset.univ.filter fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1 = Y
  let Iy : F.GaugeField F.top → ℝ := fun V' => ∫ τ in (0 : ℝ)..1, hessianCellShare T.a T.ρA T.lam Y V' τ
  have hfun : (fun V' => stepDensity T.a T.ρA T.lam Y V') = fun V' =>
      ((-(1 / 2 : ℝ)) * Iy V' + (3 / 2 : ℝ) * ∑ c₀ ∈ Bs, Gc c₀ V') + ∑ b ∈ Cb, Gh b V' := by
    funext V'
    unfold stepDensity
    simp only [Cb, Bs, Finset.sum_filter]
    rfl
  have sC : ∀ c₀ ∈ Bs, ContDiffAlongBonds k (Gc c₀) V c X := fun c₀ h => (hGc c₀ (Finset.mem_filter.1 h).2).1
  have sH : ∀ b ∈ Cb, ContDiffAlongBonds k (Gh b) V c X := fun b h => (hGh b (Finset.mem_filter.1 h).2).1
  have sCs : ContDiffAlongBonds k (fun V' => ∑ c₀ ∈ Bs, Gc c₀ V') V c X := ContDiffAt.sum sC
  have sHs : ContDiffAlongBonds k (fun V' => ∑ b ∈ Cb, Gh b V') V c X := ContDiffAt.sum sH
  have sI' : ContDiffAlongBonds k Iy V c X := sI
  have a1 : ContDiffAlongBonds k (fun V' => (-(1 / 2 : ℝ)) * Iy V') V c X := contDiffAt_const.mul sI'
  have a2 : ContDiffAlongBonds k (fun V' => (3 / 2 : ℝ) * ∑ c₀ ∈ Bs, Gc c₀ V') V c X := contDiffAt_const.mul sCs
  have a3 : ContDiffAlongBonds k (fun V' => (-(1 / 2 : ℝ)) * Iy V' + (3 / 2 : ℝ) * ∑ c₀ ∈ Bs, Gc c₀ V') V c X :=
    ContDiffAt.add a1 a2
  have add2 : ∀ G H : F.GaugeField F.top → ℝ, ContDiffAlongBonds k G V c X → ContDiffAlongBonds k H V c X →
      bondDeriv (fun V' => G V' + H V') V c X = bondDeriv G V c X + bondDeriv H V c X := by
    intro G H hG hH
    have h := hsum Bool Finset.univ (fun b => if b then G else H) (by
      intro b _
      cases b
      · simpa using hH
      · simpa using hG)
    simpa [Fintype.sum_bool] using h
  show |bondDeriv (fun V' => stepDensity T.a T.ρA T.lam Y V') V c X| ≤ _
  rw [hfun, add2 _ _ a3 sHs, add2 _ _ a1 a2, hsmul _ _ sI', hsmul _ _ sCs, hsum _ _ _ sC, hsum _ _ _ sH]
  set E : ℝ := Real.exp (-(2 ^ 6 * T.κ * S)) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hκS : (0 : ℝ) ≤ T.κ * S := mul_nonneg hκ0.le (Nat.cast_nonneg _)
  have e7 : Real.exp (-(2 ^ 7 * T.κ * S)) ≤ E := Real.exp_le_exp.2 (by nlinarith)
  have e8 : Real.exp (-(2 ^ 8 * T.κ * S)) ≤ E := Real.exp_le_exp.2 (by nlinarith)
  have t1 : |(-(1 / 2 : ℝ)) * bondDeriv Iy V c X| ≤ |Ct| * E := by
    rw [abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have h1 : |bondDeriv Iy V c X| ≤ |Ct| * E :=
      bI.trans (mul_le_mul (le_abs_self _) e7 (Real.exp_pos _).le (abs_nonneg _))
    have h2 : 0 ≤ |bondDeriv Iy V c X| := abs_nonneg _
    linarith
  have hcB : ((Bs.card : ℕ) : ℝ) ≤ 4 := by exact_mod_cast card_innerBonds_at_cell_le Y
  have hcC : ((Cb.card : ℕ) : ℝ) ≤ 4 * (T.L : ℝ) ^ 4 := by
    have h := hB F hodd hside2 Y
    rw [hFL] at h
    exact_mod_cast h
  have t2 : |(3 / 2 : ℝ) * ∑ c₀ ∈ Bs, bondDeriv (Gc c₀) V c X| ≤ 6 * DC * E := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
    have h1 : |∑ c₀ ∈ Bs, bondDeriv (Gc c₀) V c X| ≤ (Bs.card : ℝ) * (DC * E) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [← nsmul_eq_mul]
      refine Finset.sum_le_card_nsmul _ _ _ fun c₀ h => ?_
      exact (hGc c₀ (Finset.mem_filter.1 h).2).2.trans (mul_le_mul_of_nonneg_left e8 hDC0)
    have h2 : (Bs.card : ℝ) * (DC * E) ≤ 4 * (DC * E) :=
      mul_le_mul_of_nonneg_right hcB (mul_nonneg hDC0 hE0)
    linarith
  have t3 : |∑ b ∈ Cb, bondDeriv (Gh b) V c X| ≤ 4 * (T.L : ℝ) ^ 4 * DH * E := by
    have h1 : |∑ b ∈ Cb, bondDeriv (Gh b) V c X| ≤ (Cb.card : ℝ) * (DH * E) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [← nsmul_eq_mul]
      refine Finset.sum_le_card_nsmul _ _ _ fun b h => ?_
      exact (hGh b (Finset.mem_filter.1 h).2).2.trans (mul_le_mul_of_nonneg_left e8 hDH0)
    have h2 : (Cb.card : ℝ) * (DH * E) ≤ 4 * (T.L : ℝ) ^ 4 * (DH * E) :=
      mul_le_mul_of_nonneg_right hcC (mul_nonneg hDH0 hE0)
    linarith
  have hC0 : 0 ≤ |Ct| + 6 * DC + 4 * (T.L : ℝ) ^ 4 * DH := by positivity
  have hspan : (bondSpan Y c : ℝ) ≤ S := by exact_mod_cast bondSpan_le_diameter Y c
  have hfin : E ≤ Real.exp (-(2 ^ 6 * T.κ * (bondSpan Y c : ℝ))) := by
    refine Real.exp_le_exp.2 ?_
    have := mul_le_mul_of_nonneg_left hspan (by positivity : (0 : ℝ) ≤ 2 ^ 6 * T.κ)
    linarith
  calc _ ≤ |(-(1 / 2 : ℝ)) * bondDeriv Iy V c X + (3 / 2 : ℝ) * ∑ c₀ ∈ Bs, bondDeriv (Gc c₀) V c X| +
        |∑ b ∈ Cb, bondDeriv (Gh b) V c X| := abs_add_le _ _
    _ ≤ |(-(1 / 2 : ℝ)) * bondDeriv Iy V c X| + |(3 / 2 : ℝ) * ∑ c₀ ∈ Bs, bondDeriv (Gc c₀) V c X| +
        |∑ b ∈ Cb, bondDeriv (Gh b) V c X| := by
      gcongr
      exact abs_add_le _ _
    _ ≤ |Ct| * E + 6 * DC * E + 4 * (T.L : ℝ) ^ 4 * DH * E := add_le_add (add_le_add t1 t2) t3
    _ = (|Ct| + 6 * DC + 4 * (T.L : ℝ) ^ 4 * DH) * E := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hfin hC0
end YangMills.Construction.StepDensities
end
