import YangMills.Construction.ColdStepAtMirrorFrames.TransportOfTheExpansionProof
import YangMills.Construction.ResponseInTheExpansion.MeanOfARemainderProof
import YangMills.Construction.ResponseInTheExpansion.ParametersMatchAboveALowerBound
import YangMills.Construction.SummableBoundsOfTheFlow.TheDensitiesAreNearTheirLimitsProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames WeightedResponses FamilyNorms
namespace ResponseInTheExpansion
namespace BlockRemainderMean
variable {F : BlockFrame}
theorem isNormBoundedLocalFamily_of_isRegularFamily {L t n₀ : ℕ} {σ δ E E₃ : ℝ} {f : LocalFamily}
    (h : IsRegularFamily L t n₀ σ δ E E₃ f) : IsNormBoundedLocalFamily L t n₀ σ δ E E₃ f :=
  ⟨h.smooth, h.gauge_invariant, h.translation_invariant, h.decay, h.locality⟩
theorem torusDecayFactor_pos (L : ℕ) (δ u : ℝ) : 0 < torusDecayFactor L δ u := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.AdmissibleParameters.torusDecayFactor_pos <;> assumption
theorem one_le_torusDecayFactor {L : ℕ} {δ u : ℝ} (hδ : 0 ≤ δ) (hu : 0 ≤ u) : 1 ≤ torusDecayFactor L δ u := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FlatResponseSums.one_le_decayWeight <;> assumption
theorem le_zero_of_le_mul_forall_pos {a C : ℝ} (hC : 0 ≤ C) (h : ∀ ε : ℝ, 0 < ε → a ≤ C * ε) : a ≤ 0 := by apply _root_.YangMills.Construction.ResponseInTheExpansion.RemainderExpectation.nonpos_of_forall_le_mul <;> assumption
theorem isTorusRemainder_mono {L : ℕ} {σ δ e e' η₃ : ℝ} {r : F.Site F.depth → F.GaugeField F.depth → ℝ}
    (hδ : 0 ≤ δ) (he : 0 ≤ e) (hee : e ≤ e') (hη : 0 < η₃) (hr : IsTorusRemainder L σ δ e (e / η₃) r) :
    IsTorusRemainder L σ δ e' (e' / η₃) r := by apply _root_.YangMills.Construction.ResponseInTheExpansion.RemainderExpectation.torusRemainder_mono <;> assumption
theorem torusDecayFactor_mono (L : ℕ) {δ u v : ℝ} (hδ : 0 ≤ δ) (hu : 0 ≤ u) (huv : u ≤ v) :
    torusDecayFactor L δ u ≤ torusDecayFactor L δ v := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ExpansionTransport.torusDecayFactor_mono <;> assumption
theorem torusDecayFactor_mul_exp_le (hWE : LinearResponse.DecayFactorExpBound) (L : ℕ) (δ ε : ℝ) (hL : 0 < L)
    (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ q : ℕ, N ≤ q → torusDecayFactor L δ q * Real.exp (-(2 * δ * q)) ≤ ε := by
  obtain ⟨C, hC1, hC⟩ := hWE L (δ / 2) hL (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * Real.log (C / ε) / δ)
  refine ⟨N, fun q hq => ?_⟩
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hqN : (N : ℝ) ≤ q := by exact_mod_cast hq
  have h1 := hC q hq0
  have hP : max 1 (((q : ℝ) / (L : ℝ) ^ (1 / 640 : ℝ)) ^ 16000) * Real.exp (δ / 2 * q) ≤
      C * Real.exp (2 * (δ / 2) * q) := h1
  have e1 : torusDecayFactor L δ q * Real.exp (-(2 * δ * q)) =
      max 1 (((q : ℝ) / (L : ℝ) ^ (1 / 640 : ℝ)) ^ 16000) * Real.exp (δ / 2 * q) *
        Real.exp (-(3 / 2 * δ * q)) := by
    unfold torusDecayFactor
    have e0 : Real.exp (δ * q) * Real.exp (-(2 * δ * q)) = Real.exp (δ / 2 * q) * Real.exp (-(3 / 2 * δ * q)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [mul_assoc, e0, ← mul_assoc]
  rw [e1]
  have e2 : C * Real.exp (2 * (δ / 2) * q) * Real.exp (-(3 / 2 * δ * q)) = C * Real.exp (-(δ / 2 * q)) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have h3 : C * Real.exp (-(δ / 2 * q)) ≤ ε := by
    have h4 : Real.log (C / ε) ≤ δ / 2 * q := by
      have : 2 * Real.log (C / ε) / δ ≤ q := hN.trans hqN
      rw [div_le_iff₀ hδ] at this
      linarith
    have h5 : C / ε ≤ Real.exp (δ / 2 * q) := by
      have hpos : 0 < C / ε := by positivity
      calc C / ε = Real.exp (Real.log (C / ε)) := (Real.exp_log hpos).symm
        _ ≤ _ := Real.exp_le_exp.mpr h4
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
    rw [div_le_iff₀ hε] at h5
    linarith
  calc _ ≤ C * Real.exp (2 * (δ / 2) * q) * Real.exp (-(3 / 2 * δ * q)) :=
        mul_le_mul_of_nonneg_right hP (Real.exp_pos _).le
    _ = _ := e2
    _ ≤ ε := h3
theorem mul_rpow_neg_half_le_one {w x : ℝ} (hw : 0 ≤ w) (hx : w ^ 2 + 1 ≤ x) : w * x ^ (-(1 / 2) : ℝ) ≤ 1 := by
  have hx0 : 0 < x := by nlinarith
  have e : x ^ (-(1 / 2) : ℝ) = (Real.sqrt x)⁻¹ := by
    rw [Real.rpow_neg hx0.le, Real.sqrt_eq_rpow]
  have hs : w ≤ Real.sqrt x := Real.le_sqrt_of_sq_le (by linarith)
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  rw [e, ← div_eq_mul_inv, div_le_one hs0]
  exact hs
theorem isSlot_mono {Q : ColdHalfLaw} {Cq : ℕ → ℝ} {h h' : ℝ} {Y : F.Cell} {K : AboveFrames F} {V : F.GaugeField F.top}
    (hC : ∀ q, 0 ≤ Cq q) (h0 : 0 ≤ h) (hh : h ≤ h') (hs : IsSlot Q Cq h Y K V) : IsSlot Q Cq h' Y K V := by apply _root_.YangMills.Construction.ResponseInTheExpansion.RemainderExpectation.isSlot_mono <;> assumption
theorem bondDeriv_fin_zero (G : F.GaugeField F.top → ℝ) (V : F.GaugeField F.top)
    (c : Fin 0 → F.Site F.top × Fin 4) (X : Fin 0 → imaginaryQuaternions) :
    bondDeriv G V c X = G V := by apply _root_.YangMills.SharedProofs.p1654 <;> assumption
end BlockRemainderMean
open BlockRemainderMean in
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem blockRemainderMeanStatement_holds (hM : slotExpectationDerivStatement)
    (hRS : remaindersAreSlotsStatement) (hBd : blockSumBoundStatement) (hAbove : blockRemainderStatement)
    (hMB : expectationBoundedStatement) (hFz : TorusFreezing.expectationDecouples)
    (hCV : LocalComparison.DerivDiffLeOfValueDiffLe) (hBP : TorusComparison.bondsNearCellsPairStatement)
    (hWE : LinearResponse.DecayFactorExpBound) (hJF : ParameterAssignments.EventuallyOfJoinWithCouplingFloor)
    (hJ : EventuallyInParametersCombines) : blockRemainderMeanStatement := by
  classical
  obtain ⟨join, weaken⟩ := hJ
  obtain ⟨Cq, Cr, hCq, hCr0, hSl⟩ := hRS
  obtain ⟨Cb, hCb0, hBdT⟩ := hBd
  obtain ⟨B, hB0, hMn⟩ := hM Cq hCq
  obtain ⟨C₀, hC₀, hcv⟩ := hCV
  have h1 : EventuallyInParameters fun T => 1 ≤ T.coupling := fun _ _ => ⟨0, fun _ _ _ _ _ => ⟨0, fun _ _ =>
    ⟨1, one_pos, fun _ _ _ => ⟨1, one_pos, fun _ _ _ _ => ⟨0, fun _ _ => ⟨1, one_pos,
      fun _ _ _ _ _ => ⟨0, fun _ _ _ _ => ⟨0, fun _ _ => ⟨0, fun _ _ => ⟨1, fun _ hy => hy⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  have hP := join _ _ hMn (join _ _ hSl (join _ _ hBdT (join _ _ hMB (join _ _ hFz hAbove))))
  have hR : EventuallyInParameters fun T => T.IsOrdered ∧ 1 ≤ T.coupling :=
    weaken _ _ (fun T hT h => ⟨hT, h⟩) h1
  let S : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℝ := fun U => B U * (Cr U + 1) + Cb U
  let A₂ : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℝ := fun U => 1 + U.Cs * (1 + U.energyRatio) ^ 2 * (Cr U + 1) + U.L + S U
  let CV : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℝ := fun U => C₀ * (A₂ U * (1 + 64 / U.σ + (64 / U.σ) ^ 2 + 1)) + A₂ U
  let ε₀ : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℝ := fun U => 2⁻¹ ^ 5 * U.L * U.η₃ / CV U
  have hNex : ∀ U : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters, ∃ N : ℕ, 0 < U.L → 0 < U.decayRate → 0 < ε₀ U → ∀ q : ℕ, N ≤ q →
      torusDecayFactor U.L U.decayRate q * Real.exp (-(2 * U.decayRate * q)) ≤ ε₀ U := fun U => by
    by_cases h : 0 < U.L ∧ 0 < U.decayRate ∧ 0 < ε₀ U
    · obtain ⟨N, hN⟩ := torusDecayFactor_mul_exp_le hWE U.L U.decayRate (ε₀ U) h.1 h.2.1 h.2.2
      exact ⟨N, fun _ _ _ => hN⟩
    · exact ⟨0, fun a b c' => absurd ⟨a, b, c'⟩ h⟩
  choose Nr hNr using hNex
  let w : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℝ := fun U =>
    2 * S U * torusDecayFactor U.L U.decayRate (Nr U) * 2 ^ 6 / (U.L * U.η₃)
  refine hJF _ _ _ (fun c => c) (fun U => S U + 1) (fun U => w (parametersBeforeSide U) ^ 2 + 1) hP hR ?_
  intro T c c' hc hc' hodd hn₀ hE hη hη1 hGc hK hY hPT hRT
  obtain ⟨hMnT, ⟨hSlT, hAdT⟩, ⟨hBdT', hNear⟩, hMBT, hFzT, hAboveT⟩ := hPT
  obtain ⟨hDr, hy1⟩ := hRT
  set T' : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters := { T with Cs := c, CE := c' } with hT'
  set U : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters := parametersBeforeSide T' with hU
  set Bv := B U with hBv
  set Crv := Cr U + 1 with hCrv
  set Cbv := Cb U with hCbv
  set Cqv := Cq (sizeParameters T') with hCqv
  have hκ : 0 < T.κ := hDr.κ_pos
  have hσ : 0 < T.σ := hDr.σ_pos
  have hδ : 0 < T.decayRate := by
    show 0 < T.κ / 2 ^ 10
    positivity
  have hLp : 0 < T.L := hodd.pos
  have hL1 : (1 : ℝ) ≤ T.L := by exact_mod_cast hLp
  have hCr1 : 0 ≤ Cr U := hCr0 U
  have hCrP : 0 < Crv := by linarith
  have hCbP : 0 < Cbv := hCb0 U
  have hBN : 0 ≤ Bv := hB0 U
  have hc0 : 0 ≤ c := by linarith
  have hE₃ : 0 ≤ T.energyRatio := by
    show 0 ≤ T.E / T.η₃
    positivity
  set Sv : ℝ := Bv * Crv + Cbv with hSv
  have hSvP : 0 < Sv := by positivity
  have hKS : Sv + 1 ≤ T.CE := hK
  have hBC : Bv * Crv ≤ Sv := by rw [hSv]; linarith
  have hCbS : Cbv ≤ Sv := by
    have : 0 ≤ Bv * Crv := by positivity
    rw [hSv]
    linarith
  set A : ℝ := 1 + c * (1 + T.energyRatio) ^ 2 * Crv + T.L + Sv with hA'
  have hn1 : 0 ≤ c * (1 + T.energyRatio) ^ 2 * Crv := by positivity
  have hA1 : 1 ≤ A := by rw [hA']; linarith
  have hAfz : c * (1 + T.energyRatio) ^ 2 * Crv ≤ A := by rw [hA']; linarith
  have hAdec : (T.L : ℝ) + Bv * Crv ≤ A := by rw [hA']; linarith
  set CVv : ℝ := C₀ * (A * (1 + 64 / T.σ + (64 / T.σ) ^ 2 + 1)) + A with hCVv
  have hCVP : 0 < CVv := by positivity
  have hε₀ : 0 < 2⁻¹ ^ 5 * (T.L : ℝ) * T.η₃ / CVv := by positivity
  have hNq : ∀ q : ℕ, Nr U ≤ q → torusDecayFactor T.L T.decayRate q * Real.exp (-(2 * T.decayRate * q)) ≤
      2⁻¹ ^ 5 * (T.L : ℝ) * T.η₃ / CVv := hNr U hLp hδ hε₀
  set Gn := torusDecayFactor T.L T.decayRate (Nr U) with hGn
  have hGnP : 0 < Gn := torusDecayFactor_pos _ _ _
  set wv : ℝ := 2 * Sv * Gn * 2 ^ 6 / (T.L * T.η₃) with hwv
  have hwv0 : 0 ≤ wv := by positivity
  have hYw : wv ^ 2 + 1 ≤ T.coupling := hY
  intro t x e f F r Y hfl hrow hF he hrem
  have hx1 : 1 ≤ x := le_trans hy1 hfl
  have hxp : 0 < x ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hxp1 : x ^ (-(1 / 2) : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)
  have hwx : wv * x ^ (-(1 / 2) : ℝ) ≤ 1 := mul_rpow_neg_half_le_one hwv0 (hYw.trans hfl)
  have stand : ∀ (V : F.GaugeField F.top), IsSmallCurvature (5 / 4 * T.σ) V → IsAdmissibleAt T' t x f F V :=
    fun V hV => ⟨hfl, isNormBoundedLocalFamily_of_isRegularFamily hrow, hF, hV⟩
  set Kb : AboveFrames F := (coldHalfLawAt T x f).blockSum r Y with hKb
  have core : ∀ ε : ℝ, 0 < ε → IsTorusRemainder T.L T.σ T.decayRate ε (ε / T.η₃) r →
      (∀ V : F.GaugeField F.top, IsSmallCurvature (5 / 4 * T.σ) V →
        ContDiffThreeAlongBonds ((coldHalfLawAt T x f).expectationOf Kb) V ∧
        ∀ (k : ℕ) (c₁ : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 3 →
          AreUnitVectors X →
          |bondDeriv ((coldHalfLawAt T x f).expectationOf Kb) V c₁ X -
              (coldHalfLawAt T x f).expectation V (fun η => bondDeriv (Kb η) V c₁ X)| ≤
            Bv * Crv * (ε / T.η₃) * x ^ (-(1 / 2) : ℝ) * Real.exp (-(T.κ / 2 ^ 5 * bondSpan Y c₁)) ∧
          |(coldHalfLawAt T x f).expectation V (fun η => bondDeriv (Kb η) V c₁ X)| ≤
            2⁻¹ ^ 7 * ((T.L : ℝ) * (if k = 3 then ε / T.η₃ else ε)) /
              torusDecayFactor T.L T.decayRate (bondSpan Y c₁)) ∧
      ∀ (V V' : F.GaugeField F.top) (q k : ℕ) (b : Fin k → (Fin 4 → ℤ) × Fin 4) (X : Fin k → imaginaryQuaternions),
        IsSmallCurvature (9 / 8 * T.σ) V → IsSmallCurvature (9 / 8 * T.σ) V' →
        AgreeOnBall (finiteCells F) V (finiteCells F) V' Y Y q → k ≤ 2 → (∀ l, BondWithinRadius q (b l)) →
        AreUnitVectors X →
        |bondDeriv ((coldHalfLawAt T x f).expectationOf Kb) V (bondsAt Y b) X -
            bondDeriv ((coldHalfLawAt T x f).expectationOf Kb) V' (bondsAt Y b) X| ≤
          2⁻¹ ^ 5 * ((T.L : ℝ) * ε) / torusDecayFactor T.L T.decayRate q := by
    intro ε hε hr
    set h₀ : ℝ := ε / T.η₃ with hh₀d
    have hh₀ : 0 < h₀ := by positivity
    have hεh : ε ≤ h₀ := by
      rw [hh₀d, le_div_iff₀ hη]
      nlinarith
    have dec : ∀ V : F.GaugeField F.top, IsSmallCurvature (5 / 4 * T.σ) V →
        ContDiffThreeAlongBonds ((coldHalfLawAt T x f).expectationOf Kb) V ∧
        ∀ (k : ℕ) (c₁ : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 3 →
          AreUnitVectors X →
          |bondDeriv ((coldHalfLawAt T x f).expectationOf Kb) V c₁ X -
              (coldHalfLawAt T x f).expectation V (fun η => bondDeriv (Kb η) V c₁ X)| ≤
            Bv * Crv * h₀ * x ^ (-(1 / 2) : ℝ) * Real.exp (-(T.κ / 2 ^ 5 * bondSpan Y c₁)) ∧
          |(coldHalfLawAt T x f).expectation V (fun η => bondDeriv (Kb η) V c₁ X)| ≤
            2⁻¹ ^ 7 * ((T.L : ℝ) * (if k = 3 then h₀ else ε)) /
              torusDecayFactor T.L T.decayRate (bondSpan Y c₁) := by
      intro V hV
      have st := stand V hV
      have hslot : IsSlot (coldHalfLawAt T x f) (Cq (sizeParameters T')) (Crv * h₀ * x ^ (-(1 / 2) : ℝ)) Y Kb V :=
        isSlot_mono (hCq _) (mul_nonneg (mul_nonneg hCr1 hh₀.le) hxp.le)
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hh₀.le) hxp.le)
          (hSlT t x ε f F V r Y st hrow hε hr)
      have hpos : 0 < Crv * h₀ * x ^ (-(1 / 2) : ℝ) := by positivity
      obtain ⟨d1, d2⟩ := hMnT t x _ f F V Y _ st hrow hpos hslot
      have hbl : BlockRemainderBounds T' (coldHalfLawAt T x f) ε r V :=
        (hAboveT t x ε f F V V r hfl hF hV hV hε.le hr).1
      refine ⟨d1, fun k c₁ X h1' h3 hX => ⟨?_, ?_⟩⟩
      · have a : |bondDeriv ((coldHalfLawAt T x f).expectationOf Kb) V c₁ X -
            (coldHalfLawAt T x f).expectation V (fun η => bondDeriv (Kb η) V c₁ X)| ≤
            Bv * (Crv * h₀ * x ^ (-(1 / 2) : ℝ)) * Real.exp (-(T.κ / 2 ^ 5 * bondSpan Y c₁)) :=
          d2 k c₁ X h1' h3 hX
        refine a.trans (le_of_eq ?_)
        ring
      · refine hMBT t x f F V (fun η => bondDeriv (Kb η) V c₁ X) _ st fun η hη => ?_
        have hcl : InClosedBallProduct T'.ballRadius η := fun b' => (hη b').le
        rcases (by omega : k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl
        · have a : |bondDeriv (Kb η) V c₁ X| ≤
              2⁻¹ ^ 7 * ((T.L : ℝ) * ε) / torusDecayFactor T.L T.decayRate (bondSpan Y c₁) :=
            hbl.low_order Y η 1 c₁ X hcl le_rfl (by norm_num) hX
          rw [if_neg (by norm_num)]
          exact a
        · have a : |bondDeriv (Kb η) V c₁ X| ≤
              2⁻¹ ^ 7 * ((T.L : ℝ) * ε) / torusDecayFactor T.L T.decayRate (bondSpan Y c₁) :=
            hbl.low_order Y η 2 c₁ X hcl (by norm_num) le_rfl hX
          rw [if_neg (by norm_num)]
          exact a
        · have a : |bondDeriv (Kb η) V c₁ X| ≤
              2⁻¹ ^ 7 * ((T.L : ℝ) * ε / T.η₃) / torusDecayFactor T.L T.decayRate (bondSpan Y c₁) :=
            hbl.third_order Y η c₁ X hcl hX
          rw [if_pos rfl]
          refine a.trans (le_of_eq ?_)
          rw [hh₀d]
          ring
    have third : ∀ (W : F.GaugeField F.top) (c₁ : Fin 3 → F.Site F.top × Fin 4) (X' : Fin 3 → imaginaryQuaternions),
        IsSmallCurvature (5 / 4 * T.σ) W → AreUnitVectors X' →
        |bondDeriv ((coldHalfLawAt T x f).expectationOf Kb) W c₁ X'| ≤ A * h₀ := by
      intro W c₁ X' hW hX'
      obtain ⟨a, b⟩ := (dec W hW).2 3 c₁ X' (by norm_num) le_rfl hX'
      rw [if_pos rfl] at b
      have hG1 : 1 ≤ torusDecayFactor T.L T.decayRate (bondSpan Y c₁) :=
        one_le_torusDecayFactor hδ.le (Nat.cast_nonneg _)
      have hex : Real.exp (-(T.κ / 2 ^ 5 * (bondSpan Y c₁ : ℝ))) ≤ 1 := Real.exp_le_one_iff.2 (by
        have : 0 ≤ T.κ / 2 ^ 5 * (bondSpan Y c₁ : ℝ) := by positivity
        linarith)
      have a' : Bv * Crv * h₀ * x ^ (-(1 / 2) : ℝ) * Real.exp (-(T.κ / 2 ^ 5 * bondSpan Y c₁)) ≤ Bv * Crv * h₀ := by
        have p0 : 0 ≤ Bv * Crv * h₀ := by positivity
        have p1 : x ^ (-(1 / 2) : ℝ) * Real.exp (-(T.κ / 2 ^ 5 * bondSpan Y c₁)) ≤ 1 :=
          mul_le_one₀ hxp1 (Real.exp_pos _).le hex
        calc _ = Bv * Crv * h₀ * (x ^ (-(1 / 2) : ℝ) * Real.exp (-(T.κ / 2 ^ 5 * bondSpan Y c₁))) := by ring
          _ ≤ Bv * Crv * h₀ * 1 := mul_le_mul_of_nonneg_left p1 p0
          _ = _ := by ring
      have b' : 2⁻¹ ^ 7 * ((T.L : ℝ) * h₀) / torusDecayFactor T.L T.decayRate (bondSpan Y c₁) ≤ (T.L : ℝ) * h₀ := by
        have p0 : 0 ≤ (T.L : ℝ) * h₀ := by positivity
        calc _ ≤ 2⁻¹ ^ 7 * ((T.L : ℝ) * h₀) := div_le_self (by positivity) hG1
          _ ≤ _ := by nlinarith
      have hab := abs_sub_abs_le_abs_sub (bondDeriv ((coldHalfLawAt T x f).expectationOf Kb) W c₁ X')
        ((coldHalfLawAt T x f).expectation W (fun η => bondDeriv (Kb η) W c₁ X'))
      have : (T.L + Bv * Crv) * h₀ ≤ A * h₀ := mul_le_mul_of_nonneg_right hAdec hh₀.le
      nlinarith
    have close : ∀ (W W' : F.GaugeField F.top) (q : ℕ), IsSmallCurvature (5 / 4 * T.σ) W →
        IsSmallCurvature (5 / 4 * T.σ) W' → AgreeOnBall (finiteCells F) W (finiteCells F) W' Y Y q →
        |(coldHalfLawAt T x f).expectationOf Kb W - (coldHalfLawAt T x f).expectationOf Kb W'| ≤
          A * h₀ * Real.exp (-(T.κ * q / 2 ^ 7)) := by
      intro W W' q hW hW' hAg
      obtain ⟨hLF, htt, n, hside, hn⟩ := hF
      have hs1 : ∀ i, 2 * q + 2 < F.extent i := fun i => by
        rcases hAg.1 i with h0 | h0
        · rw [hside i] at h0
          have : 1 ≤ n := hn₀.trans hn
          omega
        · exact h0
      have hoddF : Odd F.blockSide := by rw [hLF]; exact hodd
      obtain ⟨ι, i1, i2, j, j', hnp⟩ := hBP F F Y Y q hoddF rfl hs1 hs1
      have had := hAdT t x ε f F W W' r Y q ι j j' (stand W hW) (stand W' hW') hrow hε hr hAg hnp
      have hz := hFzT t x 1 (TorusComparison.StepLaw.ofFamily f) F F W W' Y Y q ι j j' (Cr U * h₀) _ _
        hfl zero_le_one le_rfl (isNormBoundedLocalFamily_of_isRegularFamily hrow) ⟨hLF, htt, n, hside, hn⟩
        ⟨hLF, htt, n, hside, hn⟩ hW hW' hAg hnp (mul_nonneg hCr1 hh₀.le)
        had.left_contDiffOn had.right_contDiffOn had.comparison
      refine hz.trans ?_
      have hx := (Real.exp_pos (-(T.κ * (q : ℝ) / 2 ^ 7))).le
      have p0 : 0 ≤ c * (1 + T.energyRatio) ^ 2 := by positivity
      have e : c * (1 + T.energyRatio) ^ 2 * (Cr U * h₀) ≤ A * h₀ :=
        calc c * (1 + T.energyRatio) ^ 2 * (Cr U * h₀) = c * (1 + T.energyRatio) ^ 2 * Cr U * h₀ := by ring
          _ ≤ c * (1 + T.energyRatio) ^ 2 * Crv * h₀ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) p0) hh₀.le
          _ ≤ A * h₀ := mul_le_mul_of_nonneg_right hAfz hh₀.le
      show c * (1 + T.energyRatio) ^ 2 * (Cr U * h₀) * _ ≤ _
      exact mul_le_mul_of_nonneg_right e hx
    refine ⟨fun V hV => ⟨(dec V hV).1, fun k c₁ X h1' h3 hX => ?_⟩,
      fun V V' q k b X hV hV' hAg hk hbox hX => ?_⟩
    · obtain ⟨a, b⟩ := (dec V hV).2 k c₁ X h1' h3 hX
      exact ⟨a, b⟩
    · have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
      have hGq := torusDecayFactor_pos T.L T.decayRate (q : ℝ)
      by_cases hqN : Nr U ≤ q
      · have hres := hcv T.σ T.κ A h₀ CVv F F _ _ Y Y V V' q k b X hσ hκ hA1 hh₀ hk le_rfl
          (fun W hW => (dec W hW).1) (fun W hW => (dec W hW).1)
          (fun W c₁ X' hW hX' => third W c₁ X' hW hX') (fun W c₁ X' hW hX' => third W c₁ X' hW hX')
          (fun W W' hW hW' hA₂ => close W W' q hW hW' hA₂) hV hV' hAg hbox hX
        refine hres.trans ?_
        have e1 := hNq q hqN
        have e2 : Real.exp (-(2 * T.decayRate * q)) ≤
            2⁻¹ ^ 5 * (T.L : ℝ) * T.η₃ / CVv / torusDecayFactor T.L T.decayRate q := by
          rw [le_div_iff₀ hGq]
          linarith
        calc CVv * h₀ * Real.exp (-(2 * (T.κ / 2 ^ 10) * q))
            ≤ CVv * h₀ * (2⁻¹ ^ 5 * (T.L : ℝ) * T.η₃ / CVv / torusDecayFactor T.L T.decayRate q) :=
              mul_le_mul_of_nonneg_left e2 (by positivity)
          _ = _ := by
              rw [hh₀d]
              field_simp
      · have hqlt : q < Nr U := by omega
        have c1 : ∀ {W : F.GaugeField F.top}, IsSmallCurvature (9 / 8 * T.σ) W → IsSmallCurvature (5 / 4 * T.σ) W :=
          fun {W} hW p hp => (hW p hp).trans (by linarith)
        have err : ∀ W : F.GaugeField F.top, IsSmallCurvature (9 / 8 * T.σ) W →
            |bondDeriv ((coldHalfLawAt T x f).expectationOf Kb) W (bondsAt Y b) X - bondDeriv (Kb 0) W (bondsAt Y b) X| ≤
              Sv * h₀ * x ^ (-(1 / 2) : ℝ) := by
          intro W hW
          have hW' := c1 hW
          have near : |(coldHalfLawAt T x f).expectation W (fun η => bondDeriv (Kb η) W (bondsAt Y b) X) -
              bondDeriv (Kb 0) W (bondsAt Y b) X| ≤ Cbv * h₀ * x ^ (-(1 / 2) : ℝ) :=
            hNear t x ε f F W r Y k _ X (stand W hW') hrow hε hr hk hX
          rcases Nat.eq_zero_or_pos k with rfl | hkpos
          · have e0 : bondDeriv ((coldHalfLawAt T x f).expectationOf Kb) W (bondsAt Y b) X =
                (coldHalfLawAt T x f).expectation W (fun η => bondDeriv (Kb η) W (bondsAt Y b) X) := by
              rw [bondDeriv_fin_zero]
              show (coldHalfLawAt T x f).expectation W (fun η => Kb η W) = _
              congr 1
              funext η
              rw [bondDeriv_fin_zero]
            rw [e0]
            refine near.trans ?_
            have : 0 ≤ h₀ * x ^ (-(1 / 2) : ℝ) := by positivity
            nlinarith
          · obtain ⟨a, -⟩ := (dec W hW').2 k (bondsAt Y b) X hkpos (by omega) hX
            have hex : Real.exp (-(T.κ / 2 ^ 5 * (bondSpan Y (bondsAt Y b) : ℝ))) ≤ 1 := Real.exp_le_one_iff.2 (by
              have : 0 ≤ T.κ / 2 ^ 5 * (bondSpan Y (bondsAt Y b) : ℝ) := by positivity
              linarith)
            have a' : Bv * Crv * h₀ * x ^ (-(1 / 2) : ℝ) * Real.exp (-(T.κ / 2 ^ 5 * bondSpan Y (bondsAt Y b))) ≤
                Bv * Crv * h₀ * x ^ (-(1 / 2) : ℝ) := by
              have p0 : 0 ≤ Bv * Crv * h₀ * x ^ (-(1 / 2) : ℝ) := by positivity
              nlinarith
            have tri := abs_sub_le (bondDeriv ((coldHalfLawAt T x f).expectationOf Kb) W (bondsAt Y b) X)
              ((coldHalfLawAt T x f).expectation W (fun η => bondDeriv (Kb η) W (bondsAt Y b) X))
              (bondDeriv (Kb 0) W (bondsAt Y b) X)
            have e9 : Sv * h₀ * x ^ (-(1 / 2) : ℝ) =
                Bv * Crv * h₀ * x ^ (-(1 / 2) : ℝ) + Cbv * h₀ * x ^ (-(1 / 2) : ℝ) := by
              rw [hSv]
              ring
            linarith
        have hfar : |bondDeriv (Kb 0) V (bondsAt Y b) X - bondDeriv (Kb 0) V' (bondsAt Y b) X| ≤
            2⁻¹ ^ 6 * ((T.L : ℝ) * ε) / torusDecayFactor T.L T.decayRate q :=
          (hAboveT t x ε f F V V' r hfl hF (c1 hV) (c1 hV') hε.le hr).2 Y q k b X hAg hk hbox hX
        have hGle : torusDecayFactor T.L T.decayRate q ≤ Gn :=
          torusDecayFactor_mono T.L hδ.le hq0 (by exact_mod_cast hqlt.le)
        have small : 2 * (Sv * h₀ * x ^ (-(1 / 2) : ℝ)) ≤
            2⁻¹ ^ 6 * ((T.L : ℝ) * ε) / torusDecayFactor T.L T.decayRate q := by
          rw [le_div_iff₀ hGq]
          have h5 : wv * x ^ (-(1 / 2) : ℝ) * (2⁻¹ ^ 6 * (T.L : ℝ) * ε) ≤ 1 * (2⁻¹ ^ 6 * (T.L : ℝ) * ε) :=
            mul_le_mul_of_nonneg_right hwx (by positivity)
          have e6 : wv * x ^ (-(1 / 2) : ℝ) * (2⁻¹ ^ 6 * (T.L : ℝ) * ε) = 2 * (Sv * h₀ * x ^ (-(1 / 2) : ℝ)) * Gn := by
            rw [hwv, hh₀d]
            field_simp
          have p0 : 0 ≤ 2 * (Sv * h₀ * x ^ (-(1 / 2) : ℝ)) := by positivity
          have h6 : 2 * (Sv * h₀ * x ^ (-(1 / 2) : ℝ)) * torusDecayFactor T.L T.decayRate q ≤
              2 * (Sv * h₀ * x ^ (-(1 / 2) : ℝ)) * Gn :=
            mul_le_mul_of_nonneg_left hGle p0
          linarith
        have ea := err V hV
        have eb := err V' hV'
        have e7 : 2⁻¹ ^ 5 * ((T.L : ℝ) * ε) / torusDecayFactor T.L T.decayRate q =
            2⁻¹ ^ 6 * ((T.L : ℝ) * ε) / torusDecayFactor T.L T.decayRate q +
              2⁻¹ ^ 6 * ((T.L : ℝ) * ε) / torusDecayFactor T.L T.decayRate q := by
          ring
        rw [e7]
        have t1 := abs_sub_le (bondDeriv ((coldHalfLawAt T x f).expectationOf Kb) V (bondsAt Y b) X)
          (bondDeriv (Kb 0) V (bondsAt Y b) X) (bondDeriv ((coldHalfLawAt T x f).expectationOf Kb) V' (bondsAt Y b) X)
        have t2 := abs_sub_le (bondDeriv (Kb 0) V (bondsAt Y b) X)
          (bondDeriv (Kb 0) V' (bondsAt Y b) X) (bondDeriv ((coldHalfLawAt T x f).expectationOf Kb) V' (bondsAt Y b) X)
        have t3 := abs_sub_comm (bondDeriv (Kb 0) V' (bondsAt Y b) X)
          (bondDeriv ((coldHalfLawAt T x f).expectationOf Kb) V' (bondsAt Y b) X)
        linarith
  have hmid : ∀ (ε : ℝ) (V : F.GaugeField F.top) (k : ℕ) (c₁ : Fin k → F.Site F.top × Fin 4)
      (X : Fin k → imaginaryQuaternions) (u : ℝ),
      0 ≤ ε → |bondDeriv ((coldHalfLawAt T x f).expectationOf Kb) V c₁ X -
        (coldHalfLawAt T x f).expectation V (fun η => bondDeriv (Kb η) V c₁ X)| ≤
        Bv * Crv * (ε / T.η₃) * x ^ (-(1 / 2) : ℝ) * Real.exp (-(T.κ / 2 ^ 5 * bondSpan Y c₁)) →
      |(coldHalfLawAt T x f).expectation V (fun η => bondDeriv (Kb η) V c₁ X)| ≤ u →
      |bondDeriv ((coldHalfLawAt T x f).expectationOf Kb) V c₁ X| ≤
        u + T.CE * ((T.L : ℝ) * ε / T.η₃) * x ^ (-(1 / 2) : ℝ) * Real.exp (-(T.κ / 2 ^ 5 * bondSpan Y c₁)) := by
    intro ε V k c₁ X u hε a b
    have hab := abs_sub_abs_le_abs_sub (bondDeriv ((coldHalfLawAt T x f).expectationOf Kb) V c₁ X)
      ((coldHalfLawAt T x f).expectation V (fun η => bondDeriv (Kb η) V c₁ X))
    have hw : 0 ≤ x ^ (-(1 / 2) : ℝ) * Real.exp (-(T.κ / 2 ^ 5 * bondSpan Y c₁)) := by positivity
    have h2 : Bv * Crv * (ε / T.η₃) ≤ T.CE * ((T.L : ℝ) * ε / T.η₃) := by
      have p0 : 0 ≤ ε / T.η₃ := by positivity
      have p1 : Bv * Crv ≤ T.CE * T.L := by nlinarith
      calc Bv * Crv * (ε / T.η₃) ≤ T.CE * T.L * (ε / T.η₃) := mul_le_mul_of_nonneg_right p1 p0
        _ = _ := by ring
    have h3 : Bv * Crv * (ε / T.η₃) * x ^ (-(1 / 2) : ℝ) * Real.exp (-(T.κ / 2 ^ 5 * bondSpan Y c₁)) ≤
        T.CE * ((T.L : ℝ) * ε / T.η₃) * x ^ (-(1 / 2) : ℝ) * Real.exp (-(T.κ / 2 ^ 5 * bondSpan Y c₁)) := by
      have := mul_le_mul_of_nonneg_right h2 hw
      calc _ = Bv * Crv * (ε / T.η₃) * (x ^ (-(1 / 2) : ℝ) * Real.exp (-(T.κ / 2 ^ 5 * bondSpan Y c₁))) := by ring
        _ ≤ _ := this
        _ = _ := by ring
    linarith
  rcases he.eq_or_lt with rfl | hepos
  · have all : ∀ ε : ℝ, 0 < ε → IsTorusRemainder T.L T.σ T.decayRate ε (ε / T.η₃) r := fun ε hε =>
      isTorusRemainder_mono hδ.le le_rfl hε.le hη hrem
    refine ⟨fun V hV => ⟨((core 1 one_pos (all 1 one_pos)).1 V hV).1, fun k c₁ X h1' h3 hX => ?_⟩,
      fun V V' q k b X hV hV' hAg hk hbox hX => ?_⟩
    · have hG := torusDecayFactor_pos T.L T.decayRate (bondSpan Y c₁)
      have hCE0 : 0 ≤ T.CE := by linarith
      have hz : |bondDeriv ((coldHalfLawAt T x f).expectationOf Kb) V c₁ X| ≤ 0 :=
        le_zero_of_le_mul_forall_pos (C := 2⁻¹ ^ 7 * ((T.L : ℝ) * (1 + 1 / T.η₃)) /
            torusDecayFactor T.L T.decayRate (bondSpan Y c₁) +
          T.CE * ((T.L : ℝ) / T.η₃) * x ^ (-(1 / 2) : ℝ) * Real.exp (-(T.κ / 2 ^ 5 * bondSpan Y c₁)))
          (add_nonneg (div_nonneg (mul_nonneg (by norm_num) (mul_nonneg (by linarith)
            (add_nonneg zero_le_one (div_nonneg zero_le_one hη.le)))) hG.le)
            (mul_nonneg (mul_nonneg (mul_nonneg hCE0 (div_nonneg (by linarith) hη.le)) hxp.le) (Real.exp_pos _).le))
          fun ε hε => by
            obtain ⟨a, b⟩ := ((core ε hε (all ε hε)).1 V hV).2 k c₁ X h1' h3 hX
            have hm := hmid ε V k c₁ X _ hε.le a b
            refine hm.trans ?_
            have hif : (if k = 3 then ε / T.η₃ else ε) ≤ (1 + 1 / T.η₃) * ε := by
              have p : 0 ≤ ε / T.η₃ := by positivity
              have e : (1 + 1 / T.η₃) * ε = ε + ε / T.η₃ := by ring
              split_ifs <;> rw [e] <;> linarith
            have s1 : 2⁻¹ ^ 7 * ((T.L : ℝ) * (if k = 3 then ε / T.η₃ else ε)) /
                  torusDecayFactor T.L T.decayRate (bondSpan Y c₁) ≤
                2⁻¹ ^ 7 * ((T.L : ℝ) * ((1 + 1 / T.η₃) * ε)) / torusDecayFactor T.L T.decayRate (bondSpan Y c₁) :=
              div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hif (by linarith))
                (by norm_num)) hG.le
            refine (add_le_add_left s1 _).trans (le_of_eq ?_)
            ring
      refine hz.trans ?_
      simp
    · have hG := torusDecayFactor_pos T.L T.decayRate (q : ℝ)
      have hz : |bondDeriv ((coldHalfLawAt T x f).expectationOf Kb) V (bondsAt Y b) X -
          bondDeriv ((coldHalfLawAt T x f).expectationOf Kb) V' (bondsAt Y b) X| ≤ 0 :=
        le_zero_of_le_mul_forall_pos (C := 2⁻¹ ^ 5 * (T.L : ℝ) / torusDecayFactor T.L T.decayRate q)
          (div_nonneg (mul_nonneg (by norm_num) (by linarith)) hG.le) fun ε hε => by
          refine ((core ε hε (all ε hε)).2 V V' q k b X hV hV' hAg hk hbox hX).trans (le_of_eq ?_)
          ring
      refine hz.trans ?_
      simp
  · obtain ⟨k1, k2⟩ := core e hepos hrem
    refine ⟨fun V hV => ⟨(k1 V hV).1, fun k c₁ X h1' h3 hX => ?_⟩, k2⟩
    obtain ⟨a, b⟩ := (k1 V hV).2 k c₁ X h1' h3 hX
    exact hmid e V k c₁ X _ hepos.le a b
end ResponseInTheExpansion
end YangMills.Construction
end
