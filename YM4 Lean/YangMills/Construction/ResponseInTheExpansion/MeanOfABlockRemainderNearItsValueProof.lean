import YangMills.Construction.ResponseInTheExpansion.BlockRemainderDecaysNearItsValue
import YangMills.Construction.ResponseInTheExpansion.MeanOfARemainderProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
namespace BlockSumExpectation
variable {F : BlockAverages.BlockFrame}
private theorem isSlot_of_le_amplitude {Q : WeightedResponses.ColdHalfLaw} {Cq : ℕ → ℝ} {h h' : ℝ} {Y : F.Cell}
    {K : WeightedResponses.AboveFrames F} {V : F.GaugeField F.top}
    (hC : ∀ q, 0 ≤ Cq q) (h0 : 0 ≤ h) (hh : h ≤ h') (hs : WeightedResponses.IsSlot Q Cq h Y K V) :
    WeightedResponses.IsSlot Q Cq h' Y K V := by apply _root_.YangMills.Construction.ResponseInTheExpansion.RemainderExpectation.isSlot_mono <;> assumption
end BlockSumExpectation
open BlockSumExpectation in
theorem blockSumExpectationNearValue (hM : WeightedResponses.slotExpectationDerivStatement)
    (hRS : remaindersAreSlotsStatement) (hN : blockRemainderNearValueStatement)
    (hJ : ColdStepAtMirrorFrames.EventuallyInParametersCombines) :
    WeightedResponses.blockSumExpectationNearValueStatement := by
  classical
  obtain ⟨join, weaken⟩ := hJ
  obtain ⟨Cq, Cr, hCq, hCr0, hSl⟩ := hRS
  obtain ⟨B, hB0, hMn⟩ := hM Cq hCq
  obtain ⟨Cn, hCn, hNr⟩ := hN
  have h1 : ColdStepAtMirrorFrames.EventuallyInParameters fun T => 1 ≤ T.coupling :=
    fun _ _ => ⟨0, fun _ _ _ _ _ => ⟨0, fun _ _ =>
    ⟨1, one_pos, fun _ _ _ => ⟨1, one_pos, fun _ _ _ _ => ⟨0, fun _ _ => ⟨1, one_pos,
      fun _ _ _ _ _ => ⟨0, fun _ _ _ _ => ⟨0, fun _ _ => ⟨0, fun _ _ => ⟨1, fun _ hy => hy⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  refine weaken _ _ (fun T hD h => ?_) (join _ _ hMn (join _ _ hSl (join _ _ hNr h1)))
  obtain ⟨hMnT, ⟨hSlT, -⟩, hNrT, hy1⟩ := h
  set Bv := B (WeightedResponses.parametersBeforeSide T) with hBv
  set Crv := Cr (WeightedResponses.parametersBeforeSide T) + 1 with hCrv
  set Cv := Cn (WeightedResponses.parametersBeforeSide T) with hCv
  have hBv0 : 0 ≤ Bv := hB0 _
  have hCr1 : 0 ≤ Cr (WeightedResponses.parametersBeforeSide T) := hCr0 _
  refine ⟨Bv * Crv + Cv, fun t x e f F V r Y k c X st hrow he hr hk1 hk2 hX => ?_⟩
  have hη : 0 < T.η₃ := hD.η₃_pos
  have hx : 0 < x := by
    have := st.coupling_le
    linarith
  have hxp : 0 < x ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos hx _
  have hh₀ : 0 < e / T.η₃ := by positivity
  have hslot := isSlot_of_le_amplitude (Q := WeightedResponses.coldHalfLawAt T x f) (hCq _)
    (mul_nonneg (mul_nonneg hCr1 hh₀.le) hxp.le)
    (show Cr (WeightedResponses.parametersBeforeSide T) * (e / T.η₃) * x ^ (-(1 / 2) : ℝ) ≤
        Crv * (e / T.η₃) * x ^ (-(1 / 2) : ℝ) from
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hh₀.le) hxp.le)
    (hSlT t x e f F V r Y st hrow he hr)
  have hpos : 0 < Crv * (e / T.η₃) * x ^ (-(1 / 2) : ℝ) := by positivity
  obtain ⟨-, d2⟩ := hMnT t x _ f F V Y _ st hrow hpos hslot
  have a₁ := d2 k c X hk1 (by omega) hX
  have a₂ := hNrT t x e f F V r Y k c X st hrow he hr hk2 hX
  set s : ℝ := (ColdStepAtMirrorFrames.bondSpan Y c : ℝ) with hs
  have hκ := hD.κ_pos
  have hexp : Real.exp (-(T.κ / 2 ^ 5 * s)) ≤ Real.exp (-(T.κ / 2 ^ 6 * s)) := by
    refine Real.exp_le_exp.2 ?_
    have : 0 ≤ T.κ * s := by positivity
    nlinarith
  have t₁ : Bv * (Crv * (e / T.η₃) * x ^ (-(1 / 2) : ℝ)) * Real.exp (-(T.κ / 2 ^ 5 * s)) ≤
      Bv * Crv * (e / T.η₃) * x ^ (-(1 / 2) : ℝ) * Real.exp (-(T.κ / 2 ^ 6 * s)) := by
    have e₁ : Bv * (Crv * (e / T.η₃) * x ^ (-(1 / 2) : ℝ)) = Bv * Crv * (e / T.η₃) * x ^ (-(1 / 2) : ℝ) := by ring
    rw [e₁]
    exact mul_le_mul_of_nonneg_left hexp (by positivity)
  have tri := abs_sub_le
    (ColdStepAtMirrorFrames.bondDeriv ((WeightedResponses.coldHalfLawAt T x f).expectationOf
      ((WeightedResponses.coldHalfLawAt T x f).blockSum r Y)) V c X)
    ((WeightedResponses.coldHalfLawAt T x f).expectation V
      (fun η => ColdStepAtMirrorFrames.bondDeriv ((WeightedResponses.coldHalfLawAt T x f).blockSum r Y η) V c X))
    (ColdStepAtMirrorFrames.bondDeriv ((WeightedResponses.coldHalfLawAt T x f).blockSum r Y 0) V c X)
  have e₂ : (Bv * Crv + Cv) * (e / T.η₃) * x ^ (-(1 / 2) : ℝ) * Real.exp (-(T.κ / 2 ^ 6 * s)) =
      Bv * Crv * (e / T.η₃) * x ^ (-(1 / 2) : ℝ) * Real.exp (-(T.κ / 2 ^ 6 * s)) +
        Cv * (e / T.η₃) * x ^ (-(1 / 2) : ℝ) * Real.exp (-(T.κ / 2 ^ 6 * s)) := by ring
  rw [e₂]
  linarith
end YangMills.Construction.ResponseInTheExpansion
end
