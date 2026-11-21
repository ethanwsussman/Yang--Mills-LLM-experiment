import YangMills.Construction.ResponseInTheExpansion.BlockRemainderIsBounded
import YangMills.Construction.ResponseInTheExpansion.CalculusOfTheColdHalf
import YangMills.Construction.ResponseInTheExpansion.ComparisonFromValues
import YangMills.Construction.ResponseInTheExpansion.MeanIsBounded
import YangMills.Construction.ResponseInTheExpansion.MeanOfASlot
import YangMills.Construction.ResponseInTheExpansion.RemaindersAreSlots
import YangMills.Construction.ResponseInTheExpansion.WeightAgainstAnExponential
import YangMills.Construction.SummableBoundsOfTheFlow.BondsNearACellPairByOffsets
import YangMills.Construction.SummableBoundsOfTheFlow.FreezingWithTwoFamilies
import YangMills.Construction.SummableBoundsOfTheFlow.ParametersMatchAtRaisedConstants
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames WeightedResponses FamilyNorms TorusComparison
namespace ResponseInTheExpansion
namespace RemainderExpectation
variable {F : BlockFrame}
theorem normBounded_of_regular {L t n₀ : ℕ} {σ δ E E₃ : ℝ} {f : LocalFamily}
    (h : IsRegularFamily L t n₀ σ δ E E₃ f) : IsNormBoundedLocalFamily L t n₀ σ δ E E₃ f :=
  ⟨h.smooth, h.gauge_invariant, h.translation_invariant, h.decay, h.locality⟩
theorem isSlot_mono {Q : ColdHalfLaw} {Cq : ℕ → ℝ} {s s' : ℝ} {Y : F.Cell} {K : AboveFrames F}
    {V : F.GaugeField F.top} (hC : ∀ q, 0 ≤ Cq q) (hs0 : 0 ≤ s) (hss : s ≤ s')
    (hs : IsSlot Q Cq s Y K V) : IsSlot Q Cq s' Y K V := by
  have hA : ∀ q, |Cq q| ≤ Cq q := fun q => le_of_eq (abs_of_nonneg (hC q))
  refine ⟨⟨hs.smoothBounded.smooth, fun k c X hk hX => hasLocalSize_mono hA (mul_nonneg hs0 (Real.exp_pos _).le)
    (mul_le_mul_of_nonneg_right hss (Real.exp_pos _).le) (hs.smoothBounded.deriv_bound k c X hk hX)⟩, hs.contDiffAt_two,
    fun Th hTh c X b hX => hasLocalSize_mono hA (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hs0) (Real.exp_pos _).le)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hss (Real.sqrt_nonneg _)) (Real.exp_pos _).le)
      (hs.decaysAlongTopField Th hTh c X b hX)⟩
theorem torusDecayFactor_pos (L : ℕ) (δ u : ℝ) : 0 < torusDecayFactor L δ u := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.AdmissibleParameters.torusDecayFactor_pos <;> assumption
theorem one_le_torusDecayFactor {L : ℕ} {δ u : ℝ} (hδ : 0 ≤ δ) (hu : 0 ≤ u) : 1 ≤ torusDecayFactor L δ u := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FlatResponseSums.one_le_decayWeight <;> assumption
theorem exp_neg_le_div_torusDecayFactor {L : ℕ} {δ Cw κ u : ℝ}
    (hw : torusDecayFactor L δ u ≤ Cw * Real.exp (2 * δ * u))
    (hκ : 2 * δ ≤ κ) (hu : 0 ≤ u) : Real.exp (-(κ * u)) ≤ Cw / torusDecayFactor L δ u := by
  have hG := torusDecayFactor_pos L δ u
  rw [le_div_iff₀ hG]
  have h1 : Real.exp (-(κ * u)) * (Cw * Real.exp (2 * δ * u)) ≤ Cw := by
    have hCw : 0 ≤ Cw := by
      by_contra h
      push Not at h
      have : Cw * Real.exp (2 * δ * u) < 0 := mul_neg_of_neg_of_pos h (Real.exp_pos _)
      linarith
    have h2 : Real.exp (-(κ * u)) * Real.exp (2 * δ * u) ≤ 1 := by
      rw [← Real.exp_add]
      refine Real.exp_le_one_iff.2 ?_
      nlinarith
    nlinarith
  calc Real.exp (-(κ * u)) * torusDecayFactor L δ u ≤ Real.exp (-(κ * u)) * (Cw * Real.exp (2 * δ * u)) :=
        mul_le_mul_of_nonneg_left hw (Real.exp_pos _).le
    _ ≤ Cw := h1
theorem nonpos_of_forall_le_mul {a C : ℝ} (hC : 0 ≤ C) (h : ∀ ε : ℝ, 0 < ε → a ≤ C * ε) : a ≤ 0 := by
  by_contra hc
  push Not at hc
  have h1 := h (a / (2 * (C + 1))) (by positivity)
  have h2 : C * (a / (2 * (C + 1))) ≤ a / 2 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith
theorem torusRemainder_mono {L : ℕ} {σ δ e e' η₃ : ℝ} {r : F.Site F.depth → F.GaugeField F.depth → ℝ}
    (hδ : 0 ≤ δ) (he : 0 ≤ e) (hee : e ≤ e') (hη : 0 < η₃) (hr : IsTorusRemainder L σ δ e (e / η₃) r) :
    IsTorusRemainder L σ δ e' (e' / η₃) r := by
  have hG : ∀ u : ℝ, 0 < torusDecayFactor L δ u := torusDecayFactor_pos L δ
  refine ⟨⟨hr.decaying.smooth, hr.decaying.gauge_invariant, fun y W k c X hW h1 h3 hX => ?_⟩,
    fun y W W' m k h X hW hW' hag hk hb hX => ?_⟩
  · refine (hr.decaying.decay y W k c X hW h1 h3 hX).trans ?_
    have : (if k = 3 then e / η₃ else e) ≤ (if k = 3 then e' / η₃ else e') := by
      split_ifs
      · gcongr
      · exact hee
    gcongr
    exact (hG _).le
  · refine (hr.agreement y W W' m k h X hW hW' hag hk hb hX).trans ?_
    gcongr
    exact (hG _).le
end RemainderExpectation
open RemainderExpectation in
set_option maxHeartbeats 4000000 in
theorem meanRemainder_holds (hM : slotExpectationDerivStatement) (hRS : remaindersAreSlotsStatement)
    (hBd : blockSumBoundStatement) (hMB : expectationBoundedStatement)
    (hFz : TorusFreezing.expectationDecouples) (hCV : LocalComparison.DerivDiffLeOfValueDiffLe)
    (hBP : bondsNearCellsPairStatement) (hWE : LinearResponse.DecayFactorExpBound)
    (hJr : SummableBounds.joinAtLoweredConstantsStatement) (hJ : EventuallyInParametersCombines) :
    meanRemainderStatement := by
  classical
  obtain ⟨join, weaken⟩ := hJ
  obtain ⟨Cq, Cr, hCq, hCr0, hSl⟩ := hRS
  obtain ⟨Cb, hCb0, hBdT⟩ := hBd
  obtain ⟨B, hB0, hMn⟩ := hM Cq hCq
  obtain ⟨C₀, hC₀, hcv⟩ := hCV
  choose! Cw hCw1 hCw using hWE
  have h1 : EventuallyInParameters fun T => 1 ≤ T.coupling := fun _ _ => ⟨0, fun _ _ _ _ _ => ⟨0, fun _ _ =>
    ⟨1, one_pos, fun _ _ _ => ⟨1, one_pos, fun _ _ _ _ => ⟨0, fun _ _ => ⟨1, one_pos,
      fun _ _ _ _ _ => ⟨0, fun _ _ _ _ => ⟨0, fun _ _ => ⟨0, fun _ _ => ⟨1, fun _ hy => hy⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  have hP := join _ _ hMn (join _ _ hSl (join _ _ hBdT (join _ _ hMB hFz)))
  have hR : EventuallyInParameters fun T => T.IsOrdered ∧ 1 ≤ T.coupling :=
    weaken _ _ (fun T hT h => ⟨hT, h⟩) h1
  let A₁ : StepParameters → ℝ := fun U =>
    1 + U.Cs * (1 + U.energyRatio) ^ 2 * Cr U + B U * (Cr U + 1) * Cw U.L U.decayRate + Cb U
  refine hJr _ _ _ (fun c => c)
    (fun U => (C₀ * (A₁ U * (1 + 64 / U.σ + (64 / U.σ) ^ 2 + 1)) + A₁ U) * Cw U.L U.decayRate) hP hR ?_
  intro T c c' hc hc' hodd hn₀ hE hη hη1 hGc hK hPT hRT
  obtain ⟨hMnT, ⟨hSlT, hAdT⟩, ⟨hBdT', -⟩, hMBT, hFzT⟩ := hPT
  obtain ⟨hDr, hy1⟩ := hRT
  set T' : StepParameters := { T with Cs := c, CE := c' } with hT'
  set U : StepParameters := parametersBeforeSide T' with hU
  set Bv := B U with hBv
  set Crv := Cr U with hCrv
  set Cbv := Cb U with hCbv
  set Cqv := Cq (sizeParameters T') with hCqv
  have hκ : 0 < T.κ := hDr.κ_pos
  have hσ : 0 < T.σ := hDr.σ_pos
  have hδ : 0 < T.decayRate := by
    show 0 < T.κ / 2 ^ 10
    positivity
  have hLp : 0 < T.L := hodd.pos
  set Cwv := Cw T.L T.decayRate with hCwv
  have hCw1' : 1 ≤ Cwv := hCw1 T.L T.decayRate hLp hδ
  have hCwG : ∀ u : ℝ, 0 ≤ u → torusDecayFactor T.L T.decayRate u ≤ Cwv * Real.exp (2 * T.decayRate * u) :=
    hCw T.L T.decayRate hLp hδ
  have hCrP : 0 ≤ Crv := hCr0 U
  have hCbN : 0 ≤ Cbv := (hCb0 U).le
  have hBN : 0 ≤ Bv := hB0 U
  have hc0 : 0 ≤ c := by linarith
  have hE₃ : 0 ≤ T.energyRatio := by
    show 0 ≤ T.E / T.η₃
    positivity
  set A : ℝ := 1 + c * (1 + T.energyRatio) ^ 2 * Crv + Bv * (Crv + 1) * Cwv + Cbv with hA'
  have hKA : (C₀ * (A * (1 + 64 / T.σ + (64 / T.σ) ^ 2 + 1)) + A) * Cwv ≤ T.CE := hK
  have hn1 : 0 ≤ c * (1 + T.energyRatio) ^ 2 * Crv := by positivity
  have hn2 : 0 ≤ Bv * (Crv + 1) * Cwv := by positivity
  have hA1 : 1 ≤ A := by rw [hA']; linarith
  have hAfz : c * (1 + T.energyRatio) ^ 2 * Crv ≤ A := by rw [hA']; linarith
  have hAdec : Bv * (Crv + 1) * Cwv + Cbv ≤ A := by rw [hA']; linarith
  have hAB : 0 < C₀ * (A * (1 + 64 / T.σ + (64 / T.σ) ^ 2 + 1)) := by positivity
  have hACE : A ≤ T.CE := by nlinarith
  have hCE' : C₀ * (A * (1 + 64 / T.σ + (64 / T.σ) ^ 2 + 1)) + A ≤ T.CE / Cwv := by
    rw [le_div_iff₀ (by linarith)]
    exact hKA
  intro t x e f F r Y hfl hrow hF he hrem
  have hx1 : 1 ≤ x := le_trans hy1 hfl
  have hxp : 0 < x ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hxp1 : x ^ (-(1 / 2) : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)
  have stand : ∀ (V : F.GaugeField F.top), IsSmallCurvature (5 / 4 * T.σ) V → IsAdmissibleAt T' t x f F V :=
    fun V hV => ⟨hfl, normBounded_of_regular hrow, hF, hV⟩
  have core : ∀ ε : ℝ, 0 < ε → IsTorusRemainder T.L T.σ T.decayRate ε (ε / T.η₃) r →
      (∀ V : F.GaugeField F.top, IsSmallCurvature (5 / 4 * T.σ) V →
        ContDiffThreeAlongBonds ((coldHalfLawAt T x f).expectationOf ((coldHalfLawAt T x f).blockSum r Y)) V ∧
        ∀ (k : ℕ) (c₁ : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 3 →
          AreUnitVectors X →
          |bondDeriv ((coldHalfLawAt T x f).expectationOf ((coldHalfLawAt T x f).blockSum r Y)) V c₁ X| ≤
            A * (ε / T.η₃) / torusDecayFactor T.L T.decayRate (bondSpan Y c₁)) ∧
      ∀ (V V' : F.GaugeField F.top) (q k : ℕ) (b : Fin k → (Fin 4 → ℤ) × Fin 4) (X : Fin k → imaginaryQuaternions),
        IsSmallCurvature (9 / 8 * T.σ) V → IsSmallCurvature (9 / 8 * T.σ) V' →
        AgreeOnBall (finiteCells F) V (finiteCells F) V' Y Y q → k ≤ 2 → (∀ l, BondWithinRadius q (b l)) →
        AreUnitVectors X →
        |bondDeriv ((coldHalfLawAt T x f).expectationOf ((coldHalfLawAt T x f).blockSum r Y)) V (bondsAt Y b) X -
            bondDeriv ((coldHalfLawAt T x f).expectationOf ((coldHalfLawAt T x f).blockSum r Y)) V' (bondsAt Y b) X| ≤
          T.CE * (ε / T.η₃) / torusDecayFactor T.L T.decayRate q := by
    intro ε hε hr
    set h₀ : ℝ := ε / T.η₃ with hh₀d
    have hh₀ : 0 < h₀ := by
      have := hDr.η₃_pos
      positivity
    have dec : ∀ V : F.GaugeField F.top, IsSmallCurvature (5 / 4 * T.σ) V →
        ContDiffThreeAlongBonds ((coldHalfLawAt T x f).expectationOf ((coldHalfLawAt T x f).blockSum r Y)) V ∧
        ∀ (k : ℕ) (c₁ : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 3 →
          AreUnitVectors X →
          |bondDeriv ((coldHalfLawAt T x f).expectationOf ((coldHalfLawAt T x f).blockSum r Y)) V c₁ X| ≤
            A * h₀ / torusDecayFactor T.L T.decayRate (bondSpan Y c₁) := by
      intro V hV
      have st := stand V hV
      have hslot := isSlot_mono (s' := (Crv + 1) * h₀ * x ^ (-(1 / 2) : ℝ)) (hCq _) (by positivity)
        (by gcongr; linarith) (hSlT t x ε f F V r Y st hrow hε hr)
      have hpos : 0 < (Crv + 1) * h₀ * x ^ (-(1 / 2) : ℝ) := by positivity
      obtain ⟨d1, d2⟩ := hMnT t x _ f F V Y _ st hrow hpos hslot
      refine ⟨d1, fun k c₁ X h1' h3 hX => ?_⟩
      have a : |bondDeriv ((coldHalfLawAt T x f).expectationOf ((coldHalfLawAt T x f).blockSum r Y)) V c₁ X -
          (coldHalfLawAt T x f).expectation V (fun η => bondDeriv ((coldHalfLawAt T x f).blockSum r Y η) V c₁ X)| ≤
          Bv * ((Crv + 1) * h₀ * x ^ (-(1 / 2) : ℝ)) * Real.exp (-(T.κ / 2 ^ 5 * bondSpan Y c₁)) :=
        d2 k c₁ X h1' h3 hX
      have hG := torusDecayFactor_pos T.L T.decayRate (bondSpan Y c₁)
      have b : |(coldHalfLawAt T x f).expectation V
            (fun η => bondDeriv ((coldHalfLawAt T x f).blockSum r Y η) V c₁ X)| ≤
          Cbv * h₀ / torusDecayFactor T.L T.decayRate (bondSpan Y c₁) :=
        hMBT t x f F V (fun η => bondDeriv ((coldHalfLawAt T x f).blockSum r Y η) V c₁ X)
        (Cbv * h₀ / torusDecayFactor T.L T.decayRate (bondSpan Y c₁)) st (fun η hη =>
          hBdT' t x ε f F V r Y η k c₁ X st hε hr (fun b' => (hη b').le) h1' h3 hX)
      have hs0 : (0 : ℝ) ≤ bondSpan Y c₁ := Nat.cast_nonneg _
      have e1 : Real.exp (-(T.κ / 2 ^ 5 * bondSpan Y c₁)) ≤
          Cwv / torusDecayFactor T.L T.decayRate (bondSpan Y c₁) :=
        exp_neg_le_div_torusDecayFactor (hCwG _ hs0) (by
          show 2 * (T.κ / 2 ^ 10) ≤ T.κ / 2 ^ 5
          nlinarith) hs0
      have e2 : Bv * ((Crv + 1) * h₀ * x ^ (-(1 / 2) : ℝ)) * Real.exp (-(T.κ / 2 ^ 5 * bondSpan Y c₁)) ≤
          Bv * (Crv + 1) * Cwv * h₀ / torusDecayFactor T.L T.decayRate (bondSpan Y c₁) := by
        have e3 : Bv * ((Crv + 1) * h₀ * x ^ (-(1 / 2) : ℝ)) ≤ Bv * ((Crv + 1) * h₀) := by
          have : (Crv + 1) * h₀ * x ^ (-(1 / 2) : ℝ) ≤ (Crv + 1) * h₀ * 1 :=
            mul_le_mul_of_nonneg_left hxp1 (by positivity)
          nlinarith
        calc _ ≤ Bv * ((Crv + 1) * h₀) * (Cwv / torusDecayFactor T.L T.decayRate (bondSpan Y c₁)) :=
              mul_le_mul e3 e1 (Real.exp_pos _).le (by positivity)
          _ = _ := by ring
      have hab := abs_sub_abs_le_abs_sub
        (bondDeriv ((coldHalfLawAt T x f).expectationOf ((coldHalfLawAt T x f).blockSum r Y)) V c₁ X)
        ((coldHalfLawAt T x f).expectation V (fun η => bondDeriv ((coldHalfLawAt T x f).blockSum r Y η) V c₁ X))
      have hfin : (Bv * (Crv + 1) * Cwv + Cbv) * h₀ / torusDecayFactor T.L T.decayRate (bondSpan Y c₁) ≤
          A * h₀ / torusDecayFactor T.L T.decayRate (bondSpan Y c₁) := by gcongr
      have hsum : Bv * (Crv + 1) * Cwv * h₀ / torusDecayFactor T.L T.decayRate (bondSpan Y c₁) +
          Cbv * h₀ / torusDecayFactor T.L T.decayRate (bondSpan Y c₁) =
          (Bv * (Crv + 1) * Cwv + Cbv) * h₀ / torusDecayFactor T.L T.decayRate (bondSpan Y c₁) := by ring
      linarith
    have third : ∀ (W : F.GaugeField F.top) (c₁ : Fin 3 → F.Site F.top × Fin 4) (X' : Fin 3 → imaginaryQuaternions),
        IsSmallCurvature (5 / 4 * T.σ) W → AreUnitVectors X' →
        |bondDeriv ((coldHalfLawAt T x f).expectationOf ((coldHalfLawAt T x f).blockSum r Y)) W c₁ X'| ≤ A * h₀ := by
      intro W c₁ X' hW hX'
      refine ((dec W hW).2 3 c₁ X' (by norm_num) le_rfl hX').trans ?_
      have hG1 : 1 ≤ torusDecayFactor T.L T.decayRate (bondSpan Y c₁) :=
        one_le_torusDecayFactor hδ.le (Nat.cast_nonneg _)
      exact div_le_self (by positivity) hG1
    have close : ∀ (W W' : F.GaugeField F.top) (q : ℕ), IsSmallCurvature (5 / 4 * T.σ) W →
        IsSmallCurvature (5 / 4 * T.σ) W' → AgreeOnBall (finiteCells F) W (finiteCells F) W' Y Y q →
        |(coldHalfLawAt T x f).expectationOf ((coldHalfLawAt T x f).blockSum r Y) W -
            (coldHalfLawAt T x f).expectationOf ((coldHalfLawAt T x f).blockSum r Y) W'| ≤
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
      have hz := hFzT t x 1 (StepLaw.ofFamily f) F F W W' Y Y q ι j j' (Crv * h₀) _ _
        hfl zero_le_one le_rfl (normBounded_of_regular hrow) ⟨hLF, htt, n, hside, hn⟩
        ⟨hLF, htt, n, hside, hn⟩ hW hW' hAg hnp (by positivity) had.left_contDiffOn had.right_contDiffOn
        had.comparison
      refine hz.trans ?_
      have hx := (Real.exp_pos (-(T.κ * (q : ℝ) / 2 ^ 7))).le
      have e : c * (1 + T.energyRatio) ^ 2 * (Crv * h₀) = c * (1 + T.energyRatio) ^ 2 * Crv * h₀ := by ring
      show c * (1 + T.energyRatio) ^ 2 * (Crv * h₀) * _ ≤ _
      rw [e]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAfz hh₀.le) hx
    refine ⟨dec, fun V V' q k b X hV hV' hAg hk hbox hX => ?_⟩
    have hres := hcv T.σ T.κ A h₀ (T.CE / Cwv) F F _ _ Y Y V V' q k b X hσ hκ hA1 hh₀ hk hCE'
      (fun W hW => (dec W hW).1) (fun W hW => (dec W hW).1)
      (fun W c₁ X' hW hX' => third W c₁ X' hW hX') (fun W c₁ X' hW hX' => third W c₁ X' hW hX')
      (fun W W' hW hW' hA₂ => close W W' q hW hW' hA₂) hV hV' hAg hbox hX
    refine hres.trans ?_
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
    have e1 : Real.exp (-(2 * (T.κ / 2 ^ 10) * q)) ≤ Cwv / torusDecayFactor T.L T.decayRate q :=
      exp_neg_le_div_torusDecayFactor (hCwG _ hq0) le_rfl hq0
    have hCwp : 0 < Cwv := by linarith
    have hCEp : 0 ≤ T.CE := by linarith
    calc T.CE / Cwv * h₀ * Real.exp (-(2 * (T.κ / 2 ^ 10) * q))
        ≤ T.CE / Cwv * h₀ * (Cwv / torusDecayFactor T.L T.decayRate q) :=
          mul_le_mul_of_nonneg_left e1 (by positivity)
      _ = T.CE * h₀ / torusDecayFactor T.L T.decayRate q := by
          field_simp
  have hη₃ := hDr.η₃_pos
  rcases he.eq_or_lt with rfl | hepos
  · have all : ∀ ε : ℝ, 0 < ε → IsTorusRemainder T.L T.σ T.decayRate ε (ε / T.η₃) r := fun ε hε =>
      torusRemainder_mono hδ.le le_rfl hε.le hη₃ hrem
    refine ⟨fun V hV => ⟨((core 1 one_pos (all 1 one_pos)).1 V hV).1, fun k c₁ X h1' h3 hX => ?_⟩,
      fun V V' q k b X hV hV' hAg hk hbox hX => ?_⟩
    · have hG := torusDecayFactor_pos T.L T.decayRate (bondSpan Y c₁)
      have hz : |bondDeriv ((coldHalfLawAt T x f).expectationOf ((coldHalfLawAt T x f).blockSum r Y)) V c₁ X| ≤ 0 :=
        nonpos_of_forall_le_mul (C := A / T.η₃ / torusDecayFactor T.L T.decayRate (bondSpan Y c₁))
          (by positivity) fun ε hε => by
          refine (((core ε hε (all ε hε)).1 V hV).2 k c₁ X h1' h3 hX).trans (le_of_eq ?_)
          ring
      refine hz.trans ?_
      simp
    · have hG := torusDecayFactor_pos T.L T.decayRate (q : ℝ)
      have hCEp : 0 ≤ T.CE := by linarith
      have hz : |bondDeriv ((coldHalfLawAt T x f).expectationOf ((coldHalfLawAt T x f).blockSum r Y)) V
            (bondsAt Y b) X -
          bondDeriv ((coldHalfLawAt T x f).expectationOf ((coldHalfLawAt T x f).blockSum r Y)) V'
            (bondsAt Y b) X| ≤ 0 :=
        nonpos_of_forall_le_mul (C := T.CE / T.η₃ / torusDecayFactor T.L T.decayRate q)
          (by positivity) fun ε hε => by
          refine ((core ε hε (all ε hε)).2 V V' q k b X hV hV' hAg hk hbox hX).trans (le_of_eq ?_)
          ring
      refine hz.trans ?_
      simp
  · obtain ⟨k1, k2⟩ := core e hepos hrem
    refine ⟨fun V hV => ⟨(k1 V hV).1, fun k c₁ X h1' h3 hX => ((k1 V hV).2 k c₁ X h1' h3 hX).trans ?_⟩, k2⟩
    have hG := torusDecayFactor_pos T.L T.decayRate (bondSpan Y c₁)
    have : 0 ≤ e / T.η₃ := by positivity
    gcongr
end ResponseInTheExpansion
end YangMills.Construction
end
