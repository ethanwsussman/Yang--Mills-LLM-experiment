import YangMills.Construction.ColdStepAtMirrorFrames.CompatibleLocalFamiliesGlue
import YangMills.Construction.ResponseInTheExpansion.ComparisonFromValues
import YangMills.Construction.ResponseInTheExpansion.MeanOfASlot
import YangMills.Construction.ResponseInTheExpansion.SmoothMovesAreAdmitted
import YangMills.Construction.ResponseInTheExpansion.SmoothMovesAreSlots
import YangMills.Construction.SummableBoundsOfTheFlow.BondsNearACellPairByOffsets
import YangMills.Construction.SummableBoundsOfTheFlow.FreezingWithTwoFamilies
import YangMills.Construction.SummableBoundsOfTheFlow.ParametersMatchAtRaisedConstants
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames FamilyNorms TorusComparison WeightedResponses ResponseInTheExpansion
namespace WeightedResponses
namespace SmoothIncrementBounds
variable {F : BlockFrame}
theorem isNormBoundedLocalFamily_of_isRegularFamily {L t n₀ : ℕ} {σ δ E E₃ : ℝ} {f : LocalFamily}
    (hf : IsRegularFamily L t n₀ σ δ E E₃ f) :
    IsNormBoundedLocalFamily L t n₀ σ δ E E₃ f :=
  ⟨hf.smooth, hf.gauge_invariant, hf.translation_invariant, hf.decay, hf.locality⟩
theorem expectation_bondDeriv_le_of_slot {P : StepParameters} {Cq : ℕ → ℝ} {B C s x : ℝ} {t : ℕ}
    {f : LocalFamily} {V : F.GaugeField F.top}
    {Y : F.Cell} {K : AboveFrames F} (hm : SlotExpectationDerivAt P Cq B) (hadm : IsAdmissibleAt P t x f F V)
    (hreg : IsRegularFamily P.L t P.n₀ P.σ P.decayRate P.E P.energyRatio f) (hs₀ : 0 < s) (hκ : 0 < P.κ) (hC : 0 ≤ C)
    (hslot : IsSlot (coldHalfLawAt P x f) Cq s Y K V ∧
      ∀ (k : ℕ) (b : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 3 →
        AreUnitVectors X →
        |(coldHalfLawAt P x f).expectation V (fun η => bondDeriv (K η) V b X)| ≤
          C * s * Real.exp (-(2 ^ 5 * P.κ * bondSpan Y b))) :
    ContDiffThreeAlongBonds ((coldHalfLawAt P x f).expectationOf K) V ∧
      ∀ (k : ℕ) (b : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 3 →
        AreUnitVectors X →
        |bondDeriv ((coldHalfLawAt P x f).expectationOf K) V b X| ≤
          (B + C) * s * Real.exp (-(P.κ / 2 ^ 5 * bondSpan Y b)) := by
  obtain ⟨h1, h2⟩ := hm t x s f F V Y K hadm hreg hs₀ hslot.1
  refine ⟨h1, fun k b X hk1 hk3 hX => ?_⟩
  have a := h2 k b X hk1 hk3 hX
  have c := hslot.2 k b X hk1 hk3 hX
  have e : Real.exp (-(2 ^ 5 * P.κ * bondSpan Y b)) ≤ Real.exp (-(P.κ / 2 ^ 5 * bondSpan Y b)) := by
    rw [Real.exp_le_exp]
    have : 0 ≤ P.κ * (bondSpan Y b : ℝ) := by positivity
    nlinarith
  have c' : |(coldHalfLawAt P x f).expectation V (fun η => bondDeriv (K η) V b X)| ≤
      C * s * Real.exp (-(P.κ / 2 ^ 5 * bondSpan Y b)) := c.trans (by gcongr)
  have := abs_sub_abs_le_abs_sub (bondDeriv ((coldHalfLawAt P x f).expectationOf K) V b X)
    ((coldHalfLawAt P x f).expectation V (fun η => bondDeriv (K η) V b X))
  nlinarith
end SmoothIncrementBounds
set_option maxHeartbeats 4000000 in
open SmoothIncrementBounds in
theorem smoothIncrementExpectations_of_components (hM : slotExpectationDerivStatement)
    (hS : SmoothIncrementsAreSlots)
    (hA : smoothIncrementsComparableStatement) (hFz : TorusFreezing.expectationDecouples)
    (hCV : LocalComparison.DerivDiffLeOfValueDiffLe)
    (hBP : bondsNearCellsPairStatement) (hJr : SummableBounds.joinAtLoweredConstantsStatement)
    (hJ : EventuallyInParametersCombines) : SmoothIncrementExpectations := by
  classical
  obtain ⟨join, weaken⟩ := hJ
  obtain ⟨Cq, Cs, hCq, hCs0, hSl⟩ := hS
  obtain ⟨Ca, hCa0, hAd⟩ := hA
  obtain ⟨B, hB0, hMn⟩ := hM Cq hCq
  obtain ⟨C₀, hC₀, hcv⟩ := hCV
  have hcoup : EventuallyInParameters fun P => 1 ≤ P.coupling := fun _ _ => ⟨0, fun _ _ _ _ _ => ⟨0, fun _ _ =>
    ⟨1, one_pos, fun _ _ _ => ⟨1, one_pos, fun _ _ _ _ => ⟨0, fun _ _ => ⟨1, one_pos,
      fun _ _ _ _ _ => ⟨0, fun _ _ _ _ => ⟨0, fun _ _ => ⟨0, fun _ _ => ⟨1, fun _ hy => hy⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  have hP := join _ _ hMn (join _ _ hSl (join _ _ hAd hFz))
  have hR : EventuallyInParameters fun P => P.IsOrdered ∧ 1 ≤ P.coupling :=
    weaken _ _ (fun P hP h => ⟨hP, h⟩) hcoup
  let Cc : StepParameters → ℝ := fun U => Cs U + Ca U
  let A₁ : StepParameters → ℝ := fun U => 1 + U.Cs * (1 + U.energyRatio) ^ 2 * Cc U + (B U + Cc U) * Cc U
  refine hJr _ _ _ (fun c => c)
    (fun U => C₀ * (A₁ U * (1 + 64 / U.σ + (64 / U.σ) ^ 2 + 1)) + A₁ U) hP hR ?_
  intro T c c' hc hc' hodd hn₀ hE hη hη1 hGc hK hPT hRT
  obtain ⟨hMnT, hSlT, ⟨hAdT, hAdW⟩, hFzT⟩ := hPT
  obtain ⟨hOrd, hy1⟩ := hRT
  set T' : StepParameters := { T with Cs := c, CE := c' } with hT'
  set U : StepParameters := parametersBeforeSide T' with hU
  set Bv := B U with hBv
  set Csv := Cs U with hCsv
  set Cav := Ca U with hCav
  set Cqv := Cq (sizeParameters T') with hCqv
  have hCsP : 0 < Csv := hCs0 U
  have hCaN : 0 ≤ Cav := hCa0 U
  have hBN : 0 ≤ Bv := hB0 U
  have hκ : 0 < T.κ := hOrd.κ_pos
  have hσ : 0 < T.σ := hOrd.σ_pos
  have hc0 : 0 ≤ c := by linarith
  have hE₃ : 0 ≤ T.energyRatio := by
    show 0 ≤ T.E / T.η₃
    positivity
  set A : ℝ := 1 + c * (1 + T.energyRatio) ^ 2 * (Csv + Cav) + (Bv + (Csv + Cav)) * (Csv + Cav) with hA'
  have hKA : C₀ * (A * (1 + 64 / T.σ + (64 / T.σ) ^ 2 + 1)) + A ≤ T.CE := hK
  have hA1 : 1 ≤ A := by
    have a1 : 0 ≤ c * (1 + T.energyRatio) ^ 2 * (Csv + Cav) := by positivity
    have a2 : 0 ≤ (Bv + (Csv + Cav)) * (Csv + Cav) := by positivity
    rw [hA']
    linarith
  have hAslot : (Bv + Csv) * Csv ≤ A := by
    have a1 : 0 ≤ c * (1 + T.energyRatio) ^ 2 * (Csv + Cav) := by positivity
    have a2 : (Bv + Csv) * Csv ≤ (Bv + (Csv + Cav)) * (Csv + Cav) :=
      mul_le_mul (by linarith) (by linarith) hCsP.le (by positivity)
    rw [hA']
    linarith
  have hAfz : c * (1 + T.energyRatio) ^ 2 * Cav ≤ A := by
    have a1 : c * (1 + T.energyRatio) ^ 2 * Cav ≤ c * (1 + T.energyRatio) ^ 2 * (Csv + Cav) := by
      have : 0 ≤ c * (1 + T.energyRatio) ^ 2 := by positivity
      exact mul_le_mul_of_nonneg_left (by linarith) this
    have a2 : 0 ≤ (Bv + (Csv + Cav)) * (Csv + Cav) := by positivity
    rw [hA']
    linarith
  have hACE : A ≤ T.CE := by
    have : 0 ≤ C₀ * (A * (1 + 64 / T.σ + (64 / T.σ) ^ 2 + 1)) := by positivity
    linarith
  intro t x f hfl hrow
  have stand : ∀ (F : BlockFrame) (V : F.GaugeField F.top), IsCubicTopTorus T.L t T.n₀ F →
      IsSmallCurvature (5 / 4 * T.σ) V → IsAdmissibleAt T' t x f F V :=
    fun F V hF hV => ⟨hfl, isNormBoundedLocalFamily_of_isRegularFamily hrow, hF, hV⟩
  have decayK : ∀ (F : BlockFrame) (V : F.GaugeField F.top) (Y : F.Cell) (K : AboveFrames F) (h₀ : ℝ), 0 < h₀ →
      IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) V →
      IsSmoothSlotOfSize T' x f Cqv Csv (Csv * h₀) Y K V →
      ContDiffThreeAlongBonds ((coldHalfLawAt T x f).expectationOf K) V ∧
      ∀ (k : ℕ) (c₁ : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 3 →
        AreUnitVectors X →
        |bondDeriv ((coldHalfLawAt T x f).expectationOf K) V c₁ X| ≤
          A * h₀ * Real.exp (-(T.κ / 2 ^ 5 * bondSpan Y c₁)) := by
    intro F V Y K h₀ hh₀ hF hV hs
    obtain ⟨d1, d2⟩ := expectation_bondDeriv_le_of_slot hMnT (stand F V hF hV) hrow (mul_pos hCsP hh₀) hκ
      hCsP.le hs
    refine ⟨d1, fun k c₁ X h1 h3 hX => (d2 k c₁ X h1 h3 hX).trans ?_⟩
    have hx := (Real.exp_pos (-(T.κ / 2 ^ 5 * (bondSpan Y c₁ : ℝ)))).le
    have e : (Bv + Csv) * (Csv * h₀) = (Bv + Csv) * Csv * h₀ := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAslot hh₀.le) hx
  have closeK : ∀ (F F' : BlockFrame) (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top) (Y : F.Cell)
      (Y' : F'.Cell) (K : AboveFrames F)
      (K' : AboveFrames F') (q : ℕ) (h₀ : ℝ), 0 < h₀ → IsCubicTopTorus T.L t T.n₀ F →
      IsCubicTopTorus T.L t T.n₀ F' →
      IsSmallCurvature (5 / 4 * T.σ) V → IsSmallCurvature (5 / 4 * T.σ) V' →
      AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' q →
      (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (j : ι → ↥(chordBonds (finiteCells F)))
        (j' : ι → ↥(chordBonds (finiteCells F'))), IsShortPairing Y Y' q j j' →
        IsComparablePair T' x f (Cav * h₀) q Y Y' j j' K K' V V') →
      |(coldHalfLawAt T x f).expectationOf K V - (coldHalfLawAt T x f).expectationOf K' V'| ≤
        A * h₀ * Real.exp (-(T.κ * q / 2 ^ 7)) := by
    intro F F' V V' Y Y' K K' q h₀ hh₀ hF hF' hV hV' hAg hadm
    obtain ⟨hLF, _, n, hside, hn⟩ := hF
    obtain ⟨hLF', _, n', hside', hn'⟩ := hF'
    have hs1 : ∀ i, 2 * q + 2 < F.extent i := fun i => by
      rcases hAg.1 i with h0 | h0
      · rw [hside i] at h0; omega
      · exact h0
    have hs2 : ∀ i, 2 * q + 2 < F'.extent i := fun i => by
      rcases hAg.2.1 i with h0 | h0
      · rw [hside' i] at h0; omega
      · exact h0
    have hoddF : Odd F.blockSide := by rw [hLF]; exact hodd
    obtain ⟨ι, i1, i2, j, j', hnp⟩ := hBP F F' Y Y' q hoddF (by rw [hLF, hLF']) hs1 hs2
    have had := hadm ι j j' hnp
    have hz := hFzT t x 1 (StepLaw.ofFamily f) F F' V V' Y Y' q ι j j' (Cav * h₀) (fun η => K η V)
      (fun η => K' η V') hfl zero_le_one le_rfl (isNormBoundedLocalFamily_of_isRegularFamily hrow)
      ⟨hLF, ‹_›, n, hside, hn⟩
      ⟨hLF', ‹_›, n', hside', hn'⟩ hV hV' hAg hnp (by positivity) had.left_contDiffOn had.right_contDiffOn
      had.comparison
    refine hz.trans ?_
    have hx := (Real.exp_pos (-(T.κ * (q : ℝ) / 2 ^ 7))).le
    have e : c * (1 + T.energyRatio) ^ 2 * (Cav * h₀) = c * (1 + T.energyRatio) ^ 2 * Cav * h₀ := by ring
    show c * (1 + T.energyRatio) ^ 2 * (Cav * h₀) * _ ≤ _
    rw [e]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAfz hh₀.le) hx
  have mdec : ∀ (h₀ : ℝ) (K : FramedFamily), 0 < h₀ →
      (∀ (F : BlockFrame) (Y : F.Cell) (V : F.GaugeField F.top), IsCubicTopTorus T.L t T.n₀ F →
        IsSmallCurvature (5 / 4 * T.σ) V →
        IsSmoothSlotOfSize T' x f Cqv Csv (Csv * h₀) Y (K F Y) V) → ExpectationDecays T t x f h₀ K := by
    intro h₀ K hh₀ hs F Y V hF hV
    obtain ⟨d1, d2⟩ := decayK F V Y (K F Y) h₀ hh₀ hF hV (hs F Y V hF hV)
    refine ⟨d1, fun k c₁ X h1 h3 hX => (d2 k c₁ X h1 h3 hX).trans ?_⟩
    have hx := (Real.exp_pos (-(T.κ / 2 ^ 5 * (bondSpan Y c₁ : ℝ)))).le
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hACE hh₀.le) hx
  have third : ∀ (F : BlockFrame) (W : F.GaugeField F.top) (Y : F.Cell) (K : AboveFrames F) (h₀ : ℝ), 0 < h₀ →
      IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) W →
      IsSmoothSlotOfSize T' x f Cqv Csv (Csv * h₀) Y K W →
      ∀ (c₁ : Fin 3 → F.Site F.top × Fin 4) (X' : Fin 3 → imaginaryQuaternions),
      AreUnitVectors X' → |bondDeriv ((coldHalfLawAt T x f).expectationOf K) W c₁ X'| ≤ A * h₀ := by
    intro F W Y K h₀ hh₀ hF hW hs c₁ X' hX'
    refine ((decayK F W Y K h₀ hh₀ hF hW hs).2 3 c₁ X' (by norm_num) le_rfl hX').trans ?_
    have h1 : Real.exp (-(T.κ / 2 ^ 5 * (bondSpan Y c₁ : ℝ))) ≤ 1 := Real.exp_le_one_iff.2 (by
      have : 0 ≤ T.κ / 2 ^ 5 * (bondSpan Y c₁ : ℝ) := by positivity
      linarith)
    have h2 : 0 ≤ A * h₀ := by positivity
    nlinarith
  have mcmp : ∀ (h₀ : ℝ) (K : FramedFamily), 0 < h₀ →
      (∀ (F : BlockFrame) (Y : F.Cell) (V : F.GaugeField F.top), IsCubicTopTorus T.L t T.n₀ F →
        IsSmallCurvature (5 / 4 * T.σ) V →
        IsSmoothSlotOfSize T' x f Cqv Csv (Csv * h₀) Y (K F Y) V) →
      (∀ (F F' : BlockFrame) (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell)
        (q : ℕ) (ι : Type)
        [Fintype ι] [DecidableEq ι] (j : ι → ↥(chordBonds (finiteCells F)))
        (j' : ι → ↥(chordBonds (finiteCells F'))), IsCubicTopTorus T.L t T.n₀ F →
        IsCubicTopTorus T.L t T.n₀ F' →
        IsSmallCurvature (5 / 4 * T.σ) V → IsSmallCurvature (5 / 4 * T.σ) V' →
        AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' q → IsShortPairing Y Y' q j j' →
        IsComparablePair T' x f (Cav * h₀) q Y Y' j j' (K F Y) (K F' Y') V V') →
      ExpectationIsLocal T t x f h₀ K := by
    intro h₀ K hh₀ hs hadm F F' Y Y' V V' q k b X hF hF' hV hV' hAg hk hbox hX
    exact hcv T.σ T.κ A h₀ T.CE F F' _ _ Y Y' V V' q k b X hσ hκ hA1 hh₀ hk hKA
      (fun W hW => (decayK F W Y (K F Y) h₀ hh₀ hF hW (hs F Y W hF hW)).1)
      (fun W hW => (decayK F' W Y' (K F' Y') h₀ hh₀ hF' hW (hs F' Y' W hF' hW)).1)
      (fun W c₁ X' hW hX' => third F W Y (K F Y) h₀ hh₀ hF hW (hs F Y W hF hW) c₁ X' hX')
      (fun W c₁ X' hW hX' => third F' W Y' (K F' Y') h₀ hh₀ hF' hW (hs F' Y' W hF' hW) c₁ X' hX')
      (fun W W' hW hW' hA₂ => closeK F F' W W' Y Y' (K F Y) (K F' Y') q h₀ hh₀ hF hF' hW hW' hA₂
        fun ι _ _ j j' hnp => hadm F F' W W' Y Y' q ι j j' hF hF' hW hW' hA₂ hnp) hV hV' hAg hbox hX
  have hx1 : 1 ≤ x := le_trans hy1 hfl
  have hxp : 0 < x ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have sl : ∀ (F : BlockFrame) (Y : F.Cell) (V : F.GaugeField F.top), IsCubicTopTorus T.L t T.n₀ F →
      IsSmallCurvature (5 / 4 * T.σ) V → _ :=
    fun F Y V hF hV => hSlT t x f F V Y (stand F V hF hV) hrow
  have ad : ∀ (F F' : BlockFrame) (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top) (Y : F.Cell)
      (Y' : F'.Cell) (q : ℕ) (ι : Type)
      [Fintype ι] [DecidableEq ι] (j : ι → ↥(chordBonds (finiteCells F)))
      (j' : ι → ↥(chordBonds (finiteCells F'))), IsCubicTopTorus T.L t T.n₀ F → IsCubicTopTorus T.L t T.n₀ F' →
      IsSmallCurvature (5 / 4 * T.σ) V → IsSmallCurvature (5 / 4 * T.σ) V' →
      AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' q → IsShortPairing Y Y' q j j' → _ :=
    fun F F' V V' Y Y' q ι _ _ j j' hF hF' hV hV' hAg hnp =>
      hAdT t x f F F' V V' Y Y' q ι j j' (stand F V hF hV) (stand F' V' hF' hV') hrow hAg hnp
  refine ⟨mdec _ _ hxp fun F Y V hF hV => (sl F Y V hF hV).1,
    mcmp _ _ hxp (fun F Y V hF hV => (sl F Y V hF hV).1)
      (fun F F' V V' Y Y' q ι _ _ j j' hF hF' hV hV' hAg hnp =>
        (ad F F' V V' Y Y' q ι j j' hF hF' hV hV' hAg hnp).1),
    mdec _ _ one_pos fun F Y V hF hV => by rw [mul_one]; exact (sl F Y V hF hV).2.1,
    mcmp _ _ one_pos (fun F Y V hF hV => by rw [mul_one]; exact (sl F Y V hF hV).2.1)
      (fun F F' V V' Y Y' q ι _ _ j j' hF hF' hV hV' hAg hnp => by
        rw [mul_one]; exact (ad F F' V V' Y Y' q ι j j' hF hF' hV hV' hAg hnp).2.1),
    fun i back => ⟨mdec _ _ hxp fun F Y V hF hV => (sl F Y V hF hV).2.2.1 i back,
      mcmp _ _ hxp (fun F Y V hF hV => (sl F Y V hF hV).2.2.1 i back)
        (fun F F' V V' Y Y' q ι _ _ j j' hF hF' hV hV' hAg hnp =>
          (ad F F' V V' Y Y' q ι j j' hF hF' hV hV' hAg hnp).2.2 i back)⟩, ?_⟩
  intro F Y w B₁ hB₁ hw hF
  rcases hB₁.eq_or_lt with rfl | hBp
  · have hw0 : ∀ y, w y = 0 := fun y => abs_nonpos_iff.1 (hw y)
    have e : (coldHalfLawAt T x f).weightedShareIncrement w Y = fun _ _ => 0 := by
      funext η V
      simp [ColdHalfLaw.weightedShareIncrement, hw0]
    have e2 : (coldHalfLawAt T x f).expectationOf (F := F) (fun _ _ => 0) = fun _ => (0 : ℝ) := by
      funext V
      simp [ColdHalfLaw.expectationOf, ColdHalfLaw.expectation, ballExpectation]
    have hz : ∀ (k : ℕ) (c₁ : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
        (V : F.GaugeField F.top), bondDeriv (fun _ : F.GaugeField F.top => (0 : ℝ)) V c₁ X = 0 := by
      intro k c₁ X V
      have : iteratedFDeriv ℝ k (fun _ : Fin k → ℝ => (0 : ℝ)) = 0 := iteratedFDeriv_zero_fun
      simp only [bondDeriv]
      rw [this]
      rfl
    rw [e]
    constructor
    · intro V _
      rw [e2]
      refine ⟨fun k c₁ X => contDiffAt_const, fun k c₁ X _ _ _ => ?_⟩
      rw [hz]
      simp
    · intro V V' q k b X _ _ _ _ _ _
      rw [e2, hz, hz]
      simp
  · have hh₀ : 0 < B₁ * x ^ (-(1 / 2) : ℝ) := mul_pos hBp hxp
    have hsl : ∀ V : F.GaugeField F.top, IsSmallCurvature (5 / 4 * T.σ) V →
        IsSmoothSlotOfSize T' x f Cqv Csv (Csv * (B₁ * x ^ (-(1 / 2) : ℝ))) Y
          ((coldHalfLawAt T x f).weightedShareIncrement w Y) V :=
      fun V hV => by
        have := (sl F Y V hF hV).2.2.2 w B₁ hBp hw
        rwa [mul_assoc] at this
    refine ⟨fun V hV => ?_, fun V V' q k b X hV hV' hAg hk hbox hX => ?_⟩
    · obtain ⟨d1, d2⟩ := decayK F V Y _ _ hh₀ hF hV (hsl V hV)
      refine ⟨d1, fun k c₁ X h1 h3 hX => (d2 k c₁ X h1 h3 hX).trans ?_⟩
      have hx := (Real.exp_pos (-(T.κ / 2 ^ 5 * (bondSpan Y c₁ : ℝ)))).le
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hACE hh₀.le) hx
    · exact hcv T.σ T.κ A _ T.CE F F _ _ Y Y V V' q k b X hσ hκ hA1 hh₀ hk hKA
        (fun W hW => (decayK F W Y _ _ hh₀ hF hW (hsl W hW)).1)
        (fun W hW => (decayK F W Y _ _ hh₀ hF hW (hsl W hW)).1)
        (fun W c₁ X' hW hX' => third F W Y _ _ hh₀ hF hW (hsl W hW) c₁ X' hX')
        (fun W c₁ X' hW hX' => third F W Y _ _ hh₀ hF hW (hsl W hW) c₁ X' hX')
        (fun W W' hW hW' hA₂ => closeK F F W W' Y Y _ _ q _ hh₀ hF hF hW hW' hA₂
          fun ι _ _ j j' hnp => by
            have := hAdW t x f F W W' Y q ι j j' w B₁ (stand F W hF hW) (stand F W' hF hW') hrow hA₂ hnp hBp hw
            rwa [mul_assoc] at this) hV hV' hAg hbox hX
end WeightedResponses
end YangMills.Construction
end
