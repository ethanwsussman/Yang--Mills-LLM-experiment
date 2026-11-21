import YangMills.Construction.ResponseInTheExpansion.CalculusOfTheColdHalf
import YangMills.Construction.ResponseInTheExpansion.CostsHaveKernelsAboveTheFrames
import YangMills.Construction.ResponseInTheExpansion.FieldsOfTheTopAreBounded
import YangMills.Construction.ResponseInTheExpansion.SlotsFromKernels
import YangMills.Construction.ResponseInTheExpansion.SmoothMovesAreSlots
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames WeightedResponses Interpolation TorusComparison
namespace ResponseInTheExpansion
namespace SmoothIncrementSlots
variable {F : BlockFrame}
theorem isSlot_mono {Q : ColdHalfLaw} {Cq Cq' : ℕ → ℝ} {h : ℝ} {Y : F.Cell} {K : AboveFrames F}
    {V : F.GaugeField F.top}
    (hC : ∀ q, |Cq q| ≤ Cq' q) (h0 : 0 ≤ h) (hs : IsSlot Q Cq h Y K V) : IsSlot Q Cq' h Y K V :=
  ⟨⟨hs.smoothBounded.smooth, fun k c X hk hX => hasLocalSize_mono hC (mul_nonneg h0 (Real.exp_pos _).le) le_rfl
      (hs.smoothBounded.deriv_bound k c X hk hX)⟩,
    hs.contDiffAt_two, fun Th hTh c X b hX => hasLocalSize_mono hC
      (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) h0) (Real.exp_pos _).le) le_rfl
      (hs.decaysAlongTopField Th hTh c X b hX)⟩
theorem isSmoothSlotOfSize_of_isSlot {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {x : ℝ} {f : LocalFamily} {Cq Cq' : ℕ → ℝ}
    {C h A : ℝ} {Y : F.Cell} {K : AboveFrames F}
    {V : F.GaugeField F.top} (hC : ∀ q, |Cq q| ≤ Cq' q) (h0 : 0 ≤ h) (hAC : A * h ≤ C * h)
    (hs : IsSlot (coldHalfLawAt T x f) Cq h Y K V)
    (ms : ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 3 →
      AreUnitVectors X →
      |(coldHalfLawAt T x f).expectation V (fun η => bondDeriv (K η) V c X)| ≤
        A * h * Real.exp (-(2 ^ 5 * T.κ * bondSpan Y c))) :
    IsSmoothSlotOfSize T x f Cq' C h Y K V :=
  ⟨isSlot_mono hC h0 hs, fun k c X h1 h3 hX =>
    (ms k c X h1 h3 hX).trans (mul_le_mul_of_nonneg_right hAC (Real.exp_pos _).le)⟩
end SmoothIncrementSlots
open SmoothIncrementSlots in
theorem smoothIncrementsAreSlots (hSl : slotsFromKernelsStatement) (hCost : costKernelBoundsStatement)
    (hFld : TopVariationBoundedOnParameters) (hSm : interpolatedPartsSmoothStatement)
    (hFB : interpolatedFramesStatement) (hLaw : ConvexObservables.normalizedBallLawIsProbabilityStatement)
    (hSum : CellCounting.ExpDecaySumBounded) (hFew : Estimates.cellBondsCardStatement)
    (hG : CubicTorusCellGeometry) (hJ : EventuallyInParametersCombines) : SmoothIncrementsAreSlots := by
  classical
  obtain ⟨hMove, hSlope⟩ := hSl
  obtain ⟨Bc, hBc, hCo⟩ := hCost
  obtain ⟨Zf, hZf, hFi⟩ := hFld
  obtain ⟨join, weaken⟩ := hJ
  obtain ⟨Cq₀, Cz₀, Cr₀, hP⟩ := hFB
  obtain ⟨hg1, -⟩ := hG
  let Wf : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℝ := fun U =>
    if h : 0 < 2 ^ 6 * U.κ then Classical.choose (hSum (4 * U.L ^ 4) (2 ^ 6 * U.κ) h) else 0
  have hWf : ∀ U : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters, 0 < 2 ^ 6 * U.κ → 0 ≤ Wf U ∧ ∀ (F : BlockFrame) (ι : Type) [Fintype ι]
      (y : ι → F.Cell),
      (∀ z, (Finset.univ.filter fun b => y b = z).card ≤ 4 * U.L ^ 4) → ∀ z : F.Cell,
        ∑ b, Real.exp (-(2 ^ 6 * U.κ * (cellSupDist (y b) z : ℝ))) ≤ Wf U := fun U h => by
    simp only [Wf, dif_pos h]
    exact Classical.choose_spec (hSum (4 * U.L ^ 4) (2 ^ 6 * U.κ) h)
  let Wl : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℝ := fun U => 1 + |Wf U|
  have hWl1 : ∀ U, 1 ≤ Wl U := fun U => by
    have := abs_nonneg (Wf U)
    simp only [Wl]
    linarith
  let Cq : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℕ → ℝ := fun U q => 1 + |Cq₀ U q| + |Cz₀ U q|
  let Cc : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℝ := fun U =>
    (1 + |Cq₀ (sizeParameters U) 1|) + 4 * Bc U * Wl U * (1 + Zf U) + |U.Cs| * (3 + Wl U) * (1 + Zf U) + Bc U
  have hCc0 : ∀ U, 0 < Cc U := fun U => by
    have h1 := hBc U
    have h2 := hZf U
    have h3 := hWl1 U
    simp only [Cc]
    positivity
  have h64 : EventuallyInParameters fun T => 1 ≤ T.Cs ∧ 64 ≤ T.n₀ ∧ 1 ≤ T.coupling := fun _ _ =>
    ⟨0, fun _ _ _ _ _ => ⟨0, fun _ _ =>
    ⟨1, one_pos, fun _ _ _ => ⟨1, one_pos, fun _ _ _ _ => ⟨0, fun _ _ => ⟨1, one_pos,
      fun _ _ _ _ _ => ⟨1, fun _ hCs _ _ => ⟨64, fun _ h => ⟨0, fun _ _ => ⟨1, fun _ hy =>
        ⟨hCs, h, hy⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  refine ⟨Cq, Cc, fun T q => by simp only [Cq]; positivity, hCc0, ?_⟩
  refine weaken _ _ ?_ (join _ _ hP (join _ _ h64 (join _ _ hCo (join _ _ hFi hSm))))
  rintro T hDr ⟨hPT, ⟨hc1, h64', hy1⟩, hKer, hFd, hSmo⟩ t x f F V Y hst hrow
  set U := parametersBeforeSide T with hU
  set Q := coldHalfLawAt T x f with hQ
  have hfl : T.coupling ≤ x := hst.coupling_le
  have hx1 : 1 ≤ x := hy1.trans hfl
  have hx : 0 < x := by linarith
  have hκ : 0 < T.κ := hDr.κ_pos
  have hρ : 0 < T.ballRadius := by
    have := hDr.σ_pos
    show 0 < T.σ / 64
    positivity
  let M : LawOnBondVariables ↥(chordBonds (finiteCells F)) := lawAtTop V (Q.exponent V)
  have hadm : M.IsAdmissible T.a T.chainParams.ρA T.chainParams.lam x T.σ T.decayRate T.E T.energyRatio T.L t T.n₀
      (frameRadius x) (chordBondDist F) :=
    ⟨hst.torus, hst.small_curvature, IsIntermediateLaw.ofFamily 1 f zero_le_one le_rfl hst.family_bounded,
      Function.injective_id, fun _ _ => rfl⟩
  obtain ⟨hconv, hmoms, hsizes⟩ := (hPT t x hfl).laws _ (chordBondDist F) 1 (fun _ => 1) (fun _ => M)
    ⟨fun _ => zero_le_one, by simp⟩ (fun _ => hadm)
  have hsz := hsizes M hadm
  rw [convexCombinationExponent_lawAtTop] at hconv hmoms hsz
  obtain ⟨Ψ', K', hΨ', hconvex, -, -⟩ := hconv
  have hΨc : Continuous Ψ' := hconvex.smooth.continuous
  obtain ⟨-, -, -, -, -, -, -, -, -, hnz, -⟩ := hLaw _ T.ballRadius T.p Ψ' hρ hDr.cutoff hΨc
  have hdens : ballDensity (cutoffFactor T.ballRadius T.p) (Q.exponent V) =
      ballDensity (cutoffFactor T.ballRadius T.p) Ψ' := by
    funext η
    by_cases hη' : ∀ b, ‖η b‖ < T.ballRadius
    · unfold ballDensity
      rw [hΨ' η hη']
    · have h0 : ballDensity (cutoffFactor T.ballRadius T.p) Ψ' η = 0 := by
        by_contra hne
        exact hη' ((hnz η).1 hne)
      have h1 : radialWeightProd (cutoffFactor T.ballRadius T.p) η = 0 := by
        unfold ballDensity at h0
        rcases mul_eq_zero.1 h0 with h | h
        · exact h
        · exact absurd h (Real.exp_pos _).ne'
      rw [h0]
      unfold ballDensity
      rw [h1, zero_mul]
  let m : ℕ → ℝ := fun q => |Cq₀ (momentParameters T) q|
  have hm : ∀ q, 0 ≤ m q := fun q => abs_nonneg _
  have hA : LawDataAtField Q m V := ⟨hρ, hDr.cutoff, hx1, ⟨Ψ', hΨc, hdens⟩, fun q b => by
    have h1 := hmoms.moments q b
    refine h1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) ?_)
    have : 0 < x ^ q := pow_pos hx q
    positivity⟩
  obtain ⟨hLF, -, n, hside, hn⟩ := hst.torus
  have hoddF : Odd F.blockSide := by rw [hLF]; exact hDr.odd_L
  have hcub : IsLargeCubicTorus F := ⟨n, h64'.trans hn, hside⟩
  obtain ⟨-, -, hsym, -, -⟩ := hg1 F hoddF hcub
  have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by
    rw [hside]
    have := h64'.trans hn
    omega
  have hκ6 : 0 < 2 ^ 6 * U.κ := by
    show 0 < 2 ^ 6 * T.κ
    positivity
  have hWb : ∀ Y' : F.Cell, ∑ b : ↥(chordBonds (finiteCells F)),
      Real.exp (-(2 ^ 6 * T.κ * bondDistToCell Y' b)) ≤ Wl U := fun Y' => by
    have h1 := (hWf U hκ6).2 F ↥(chordBonds (finiteCells F)) (fun b => enclosingCell b.1.1) (fun z => by
      have h2 := hFew F hoddF hs2 z
      rw [hLF] at h2
      have e : U.L = T.L := rfl
      rw [e]
      convert h2) Y'
    have h3 : Wf U ≤ Wl U := by
      have := le_abs_self (Wf U)
      simp only [Wl]
      linarith
    exact h1.trans h3
  have hZ : TopVariationBounded Q (Zf U) V := hFd t x f F V hst
  obtain ⟨kc, ks, kw, kg, kz⟩ := hKer t x f F V Y hst
  have hB : 0 < Bc U := hBc U
  have hZ0 : 0 ≤ Zf U := hZf U
  have hW1 : 1 ≤ Wl U := hWl1 U
  have hr : 2 ^ 6 * Q.rate ≤ 2 ^ 7 * T.κ := by
    show 2 ^ 6 * T.κ ≤ 2 ^ 7 * T.κ
    nlinarith
  have hWt : ∀ Y' : F.Cell, ∑ b : ↥(chordBonds (finiteCells F)),
      Real.exp (-(2 ^ 7 * T.κ / 2 * bondDistToCell Y' b)) ≤ Wl U := fun Y' => by
    have e : 2 ^ 7 * T.κ / 2 = 2 ^ 6 * T.κ := by ring
    rw [e]
    exact hWb Y'
  have hC0 := (hCc0 U).le
  have hCs : 0 < T.Cs := by linarith
  have hCsU : |U.Cs| = T.Cs := by
    show |T.Cs| = T.Cs
    exact abs_of_pos hCs
  have hBW : 0 ≤ 4 * Bc U * Wl U * (1 + Zf U) := by positivity
  have hSW : 0 ≤ |U.Cs| * (3 + Wl U) * (1 + Zf U) := by positivity
  have hm1 : 0 ≤ 1 + m 1 := by linarith [hm 1]
  have hCA : 4 * Bc U * Wl U * (1 + Zf U) ≤ Cc U := by
    simp only [Cc]
    have := abs_nonneg (Cq₀ (sizeParameters U) 1)
    linarith
  have hCm : 1 + m 1 ≤ Cc U := by
    have e : m 1 = |Cq₀ (sizeParameters U) 1| := rfl
    rw [e]
    simp only [Cc]
    linarith
  have hCS : T.Cs * (3 + Wl U) * (1 + Zf U) + 4 * Bc U * Wl U * (1 + Zf U) + Bc U ≤ Cc U := by
    simp only [Cc]
    rw [hCsU]
    have := abs_nonneg (Cq₀ (sizeParameters U) 1)
    linarith
  have hCqm : ∀ q, |1 + m q| ≤ Cq (sizeParameters T) q := fun q => by
    have h1 := hm q
    rw [abs_of_nonneg (by linarith)]
    have e : m q = |Cq₀ (sizeParameters T) q| := rfl
    rw [e]
    simp only [Cq]
    have := abs_nonneg (Cz₀ (sizeParameters T) q)
    linarith
  have hxy : 0 ≤ x ^ (-(1 / 2) : ℝ) := (Real.rpow_pos_of_pos hx _).le
  have hmv : ∀ {G : AboveFrames F} {B' C' : ℝ}, HasDecayingKernels Q.ballRadius B' (2 ^ 7 * T.κ) Y G V → 0 ≤ B' →
      0 ≤ C' → 4 * B' * Wl U * (1 + Zf U) ≤ C' → 1 + m 1 ≤ Cc U →
      IsSmoothSlotOfSize T x f (Cq (sizeParameters T)) (Cc U) (C' * x ^ (-(1 / 2) : ℝ)) Y
        (fun η V' => G η V' - G 0 V') V := fun {G B' C'} hk hB' hC' hle hm' => by
    obtain ⟨s, ms⟩ := hMove F Q m V Y G B' (2 ^ 7 * T.κ) (Wl U) (Zf U) C' hA hm hk hZ hB' hZ0 hκ hr hW1 hWt hle
    exact isSmoothSlotOfSize_of_isSlot (A := 1 + m 1) hCqm (mul_nonneg hC' hxy)
      (mul_le_mul_of_nonneg_right hm' (mul_nonneg hC' hxy)) s ms
  refine ⟨hmv kc hB.le hC0 hCA hCm, ?_, fun i back => hmv (ks i back) hB.le hC0 hCA hCm, fun w B' hB' hw => ?_⟩
  · have hbs : Q.linearBlockPart Y = fun η V' => Q.blockExponent Y η V' + Q.blockGapTerms Y η V' := by
      funext η V'
      simp only [ColdHalfLaw.linearBlockPart, ColdHalfLaw.blockExponent, interpolatedBlockExponent,
        ColdHalfLaw.blockGapTerms]
      ring
    rw [hbs]
    have hone := (hPT t x hfl).one_torus F V 1 ⟨hLF, hst.torus.2.1, n, hside, hn⟩ hst.small_curvature
      zero_le_one le_rfl
    have hsmt := hSmo t x F V 1 hfl ⟨hLF, hst.torus.2.1, n, hside, hn⟩ hst.small_curvature zero_le_one le_rfl
    obtain ⟨s, ms⟩ := hSlope F Q m (fun q => |Cz₀ (momentParameters T) q|) V Y (Q.blockGapTerms Y) (Bc U)
      (2 ^ 7 * T.κ) (Wl U)
      (Wl U) (Zf U) T.Cs (Cc U) hA hm (fun q => abs_nonneg _) kg hZ hB hZ0 hκ hr hW1 (by linarith) hCs hsym hWt hWb
      hone.exponent (fun k c X η hη => hsmt.smooth Y η k c X hη) (fun k c X hk hX => by
        have h1 : HasLocalSize T.ballRadius (cutoffFactor T.ballRadius T.p) (Q.exponent V)
            (Cz₀ (momentParameters T)) x T.κ
            (T.Cs * Real.exp (-(2 ^ 5 * T.κ * bondSpan Y c))) (embeddedCellDist id Y)
            (fun ζ => bondDeriv (fun V' => interpolatedBlockExponent 1 T.a T.chainParams.ρA x (frameRadius x) Y V'
              (extendByZero id Finset.univ ζ)) V c X) :=
          hsz.exponent_deriv 1 Y k c X zero_le_one le_rfl (by omega) hX
        simp only [extendByZero_id] at h1
        exact hasLocalSize_mono (fun q => le_rfl) (by positivity) le_rfl h1)
      kz hCS
    refine isSmoothSlotOfSize_of_isSlot (A := 1 + m 1) (fun q => ?_) hC0
      (mul_le_mul_of_nonneg_right hCm hC0) s ms
    have h1 := hm q
    have h2 := abs_nonneg (Cz₀ (momentParameters T) q)
    rw [abs_of_nonneg (by linarith)]
    exact le_rfl
  · have hwm : Q.weightedShareIncrement w Y =
        fun η V' => Q.weightedSiteShares w Y η V' - Q.weightedSiteShares w Y 0 V' := by
      funext η V'
      simp only [ColdHalfLaw.weightedShareIncrement, ColdHalfLaw.weightedSiteShares, mul_sub,
        Finset.sum_sub_distrib]
    rw [hwm]
    refine hmv (kw w B' hB' hw) (by positivity) (by positivity) ?_ hCm
    calc 4 * (Bc U * B') * Wl U * (1 + Zf U) = (4 * Bc U * Wl U * (1 + Zf U)) * B' := by ring
      _ ≤ Cc U * B' := mul_le_mul_of_nonneg_right hCA hB'.le
end ResponseInTheExpansion
end YangMills.Construction
end
