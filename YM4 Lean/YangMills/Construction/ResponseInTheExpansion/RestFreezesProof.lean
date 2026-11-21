import YangMills.Construction.ResponseInTheExpansion.BarrierPartIsAdmitted
import YangMills.Construction.ResponseInTheExpansion.CalculusOfTheColdHalf
import YangMills.Construction.ResponseInTheExpansion.GapLessCostIsASlope
import YangMills.Construction.ResponseInTheExpansion.RadialPartsAreAdmitted
import YangMills.Construction.SummableBoundsOfTheFlow.BondsNearACellPairByOffsets
import YangMills.Construction.SummableBoundsOfTheFlow.FreezingWithTwoFamilies
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.Interpolation YangMills.Construction.TorusComparison YangMills.Construction.TorusFreezing YangMills.Construction.FamilyNorms YangMills.Construction.ConvexObservables YangMills.Construction.WeightedResponses
variable {F : BlockFrame}
private theorem ballExpectation_neg_add_add_sub {ι : Type} [Fintype ι] [DecidableEq ι] (r : ℝ → ℝ)
    (Ψ A B C D : BondField ι → ℝ)
    (hA : Integrable fun η => A η * ballDensity r Ψ η) (hB : Integrable fun η => B η * ballDensity r Ψ η)
    (hC : Integrable fun η => C η * ballDensity r Ψ η) (hD : Integrable fun η => D η * ballDensity r Ψ η) :
    ballExpectation r Ψ (fun η => - A η + B η + C η - D η) =
      - ballExpectation r Ψ A + ballExpectation r Ψ B + ballExpectation r Ψ C - ballExpectation r Ψ D := by
  unfold ballExpectation
  have e : (fun η => (- A η + B η + C η - D η) * ballDensity r Ψ η) =
      fun η => - (A η * ballDensity r Ψ η) + B η * ballDensity r Ψ η + C η * ballDensity r Ψ η -
        D η * ballDensity r Ψ η := by
    funext η
    ring
  have hN : Integrable fun η => - (A η * ballDensity r Ψ η) := hA.neg
  have hAB : Integrable fun η => - (A η * ballDensity r Ψ η) + B η * ballDensity r Ψ η := hN.add hB
  have hABC : Integrable fun η => - (A η * ballDensity r Ψ η) + B η * ballDensity r Ψ η +
      C η * ballDensity r Ψ η := hAB.add hC
  rw [e, integral_sub hABC hD, integral_add hAB hC, integral_add hN hB, integral_neg]
  ring
abbrev _root_.YangMills.SharedProofs.p51892 := @ballExpectation_neg_add_add_sub
private theorem integrable_mul_ballDensity_of_moment {ι : Type} [Fintype ι] [DecidableEq ι] {ρ : ℝ}
    {p : ℝ → ℝ} (hρ : 0 < ρ) (hp : IsCutoff ρ p) (hLaw : normalizedBallLawIsProbabilityStatement)
    {Ψ Ψ' H : BondField ι → ℝ} (hΨ' : ∀ η, (∀ b, ‖η b‖ < ρ) → Ψ' η = Ψ η) (hc : Continuous Ψ')
    (hrim : Integrable fun η => H η * radialWeightProd (cutoffFactor ρ p) η)
    (hm : Integrable fun η => |H η| ^ 1 * ballDensity (cutoffFactor ρ p) Ψ η) :
    Integrable fun η => H η * ballDensity (cutoffFactor ρ p) Ψ η := by
  obtain ⟨-, -, -, -, -, hnn, -, -, -, hnz, -⟩ := hLaw _ ρ p Ψ' hρ hp hc
  have hz : ∀ η : BondField ι, ¬ (∀ b, ‖η b‖ < ρ) → radialWeightProd (cutoffFactor ρ p) η = 0 :=
    fun η hη => by
    have h0 : ballDensity (cutoffFactor ρ p) Ψ' η = 0 := by
      by_contra hne
      exact hη ((hnz η).1 hne)
    unfold ballDensity at h0
    rcases mul_eq_zero.1 h0 with h | h
    · exact h
    · exact absurd h (Real.exp_pos _).ne'
  have hd : ballDensity (cutoffFactor ρ p) Ψ = ballDensity (cutoffFactor ρ p) Ψ' := by
    funext η
    by_cases hη : ∀ b, ‖η b‖ < ρ
    · unfold ballDensity
      rw [hΨ' η hη]
    · unfold ballDensity
      rw [hz η hη, zero_mul, zero_mul]
  have hmeas : AEStronglyMeasurable (fun η => H η * ballDensity (cutoffFactor ρ p) Ψ η) volume := by
    rw [hd]
    have e : (fun η => H η * ballDensity (cutoffFactor ρ p) Ψ' η) =
        fun η => (H η * radialWeightProd (cutoffFactor ρ p) η) * Real.exp (- Ψ' η) := by
      funext η
      unfold ballDensity
      ring
    rw [e]
    exact hrim.aestronglyMeasurable.mul (Real.continuous_exp.comp hc.neg).aestronglyMeasurable
  refine hm.mono hmeas (Filter.Eventually.of_forall fun η => ?_)
  have hn : 0 ≤ ballDensity (cutoffFactor ρ p) Ψ η := by
    rw [hd]
    exact hnn η
  simp only [pow_one, norm_mul, Real.norm_eq_abs, abs_abs, le_refl]
private theorem freezingHomotopy_one (lam x : ℝ) (Λ : Finset ↥(chordBonds (finiteCells F)))
    (Ψ : StepVariable (finiteCells F) → ℝ) : freezingHomotopy lam x Λ Ψ 1 = Ψ := by
  funext η
  simp [freezingHomotopy]
private theorem isNormBoundedLocalFamily_of_isRegularFamily {L t n₀ : ℕ} {σ δ E E₃ : ℝ} {f : LocalFamily}
    (h : IsRegularFamily L t n₀ σ δ E E₃ f) : IsNormBoundedLocalFamily L t n₀ σ δ E E₃ f :=
  ⟨h.smooth, h.gauge_invariant, h.translation_invariant, h.decay, h.locality⟩
private theorem comparablePair_expectation_freeze {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {t : ℕ} {x : ℝ} {f : LocalFamily}
    (hDr : T.IsOrdered) (hLaw : normalizedBallLawIsProbabilityStatement) (hFz : ExpectationDecouples T)
    (hfl : T.coupling ≤ x)
    (hfam : IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f)
    {V V' : F.GaugeField F.top} {Y : F.Cell} {q : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    {j : ι → ↥(chordBonds (finiteCells F))} (htop : IsCubicTopTorus T.L t T.n₀ F)
    (hV : IsSmallCurvature (5 / 4 * T.σ) V) (hV' : IsSmallCurvature (5 / 4 * T.σ) V')
    (hag : AgreeOnBall (finiteCells F) V (finiteCells F) V' Y Y q) (hpair : IsShortPairing Y Y q j j)
    {Ψc Ψc' : StepVariable (finiteCells F) → ℝ}
    (hΨ : ∀ η, (∀ b, ‖η b‖ < T.ballRadius) → Ψc η = (coldHalfLawAt T x f).exponent V η)
    (hc : Continuous Ψc)
    (hΨ' : ∀ η, (∀ b, ‖η b‖ < T.ballRadius) → Ψc' η = (coldHalfLawAt T x f).exponent V' η)
    (hc' : Continuous Ψc')
    {C : ℝ} (hC : 0 ≤ C) {K : AboveFrames F} (hK : IsComparablePair T x f C q Y Y j j K K V V') :
    |(coldHalfLawAt T x f).expectation V (fun η => K η V) -
        (coldHalfLawAt T x f).expectation V' (fun η => K η V')| ≤
        T.Cs * (1 + T.energyRatio) ^ 2 * C * Real.exp (-(T.κ * q / 2 ^ 7)) ∧
      (Integrable fun η => K η V *
        ballDensity (cutoffFactor T.ballRadius T.p) ((coldHalfLawAt T x f).exponent V) η) ∧
      Integrable fun η => K η V' *
        ballDensity (cutoffFactor T.ballRadius T.p) ((coldHalfLawAt T x f).exponent V') η := by
  have hρ : 0 < T.ballRadius := by
    have := hDr.σ_pos
    show 0 < T.σ / 64
    positivity
  refine ⟨?_, ?_, ?_⟩
  · exact hFz t x 1 (.ofFamily f) F F V V' Y Y q ι j j C (fun η => K η V) (fun η => K η V') hfl
      zero_le_one le_rfl hfam htop htop hV hV' hag hpair hC hK.left_contDiffOn hK.right_contDiffOn
      hK.comparison
  · have h1 := (hK.comparison.left.hasGradientBound 1 zero_le_one le_rfl).2.1 1 le_rfl
    rw [freezingHomotopy_one] at h1
    exact integrable_mul_ballDensity_of_moment hρ hDr.cutoff hLaw hΨ hc hK.comparison.left.integrable_mul h1.1
  · have h1 := (hK.comparison.right.hasGradientBound 1 zero_le_one le_rfl).2.1 1 le_rfl
    rw [freezingHomotopy_one] at h1
    exact integrable_mul_ballDensity_of_moment hρ hDr.cutoff hLaw hΨ' hc' hK.comparison.right.integrable_mul h1.1
private theorem ballExpectation_congr_of_eqOn_balls {ρ : ℝ} {p : ℝ → ℝ}
    {Ψ u w : StepVariable (finiteCells F) → ℝ}
    (hz : ∀ η, ¬ (∀ b, ‖η b‖ < ρ) → ballDensity (cutoffFactor ρ p) Ψ η = 0)
    (h : ∀ η, (∀ b, ‖η b‖ < ρ) → u η = w η) :
    ballExpectation (cutoffFactor ρ p) Ψ u = ballExpectation (cutoffFactor ρ p) Ψ w := by
  unfold ballExpectation
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
  by_cases hη : ∀ b, ‖η b‖ < ρ
  · show u η * _ = w η * _
    rw [h η hη]
  · show u η * _ = w η * _
    rw [hz η hη, mul_zero, mul_zero]
theorem dilationRemainder_locality (hJ : EventuallyInParametersCombines)
    (hFz : expectationDecouples) (hFB : interpolatedFramesStatement)
    (hPair : bondsNearCellsPairStatement) (hLaw : normalizedBallLawIsProbabilityStatement)
    (h₁ : CutoffTermComparable) (h₂ : radialPartsComparableStatement) (h₃ : GapMinusSlopeIsRadial)
    (h₄ : smoothIncrementsComparableStatement) : dilationRemainderLocalityStatement := by
  classical
  obtain ⟨join, weaken⟩ := hJ
  obtain ⟨Cq, Cz, Cr, hP⟩ := hFB
  obtain ⟨Cm, hCm, hSm⟩ := h₄
  have h1 : EventuallyInParameters fun T => 1 ≤ T.n₀ ∧ 1 ≤ T.coupling := fun _ _ => ⟨0, fun _ _ _ _ _ =>
    ⟨0, fun _ _ => ⟨1, one_pos, fun _ _ _ => ⟨1, one_pos, fun _ _ _ _ => ⟨0, fun _ _ => ⟨1, one_pos,
      fun _ _ _ _ _ => ⟨0, fun _ _ _ _ => ⟨1, fun _ h => ⟨0, fun _ _ => ⟨1, fun _ hy => ⟨h, hy⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  refine weaken _ _ ?_
    (join _ _ hP (join _ _ h1 (join _ _ hFz (join _ _ h₁ (join _ _ h₂ (join _ _ h₃ hSm))))))
  rintro T hDr ⟨hPT, ⟨hn1, hy1⟩, hFzT, a₁, a₂, h₃', a₄, -⟩
  intro t x f hfl hrow
  have hx : 0 < x := by linarith
  have hρ : 0 < T.ballRadius := by
    have := hDr.σ_pos
    show 0 < T.σ / 64
    positivity
  have hfam := isNormBoundedLocalFamily_of_isRegularFamily hrow
  obtain ⟨C₁, hC₁, A₁⟩ := a₁ t x f hfl hrow
  obtain ⟨⟨C₂, hC₂, A₂⟩, ⟨C₃, hC₃, A₃⟩⟩ := a₂ t x f hfl hrow
  set C₄ := Cm (parametersBeforeSide T) with hC₄d
  have hC₄ : 0 ≤ C₄ := hCm _
  refine ⟨1 / (2 * x) * (T.Cs * (1 + T.energyRatio) ^ 2 * (C₁ + C₂ + C₃ + 2 * C₄)), ?_⟩
  intro F V V' Y q htop hV hV' hag
  obtain ⟨hLF, htt, n, hside, hn⟩ := id htop
  have hnpos : 1 ≤ n := hn1.trans hn
  have hsd : ∀ i, 2 * q + 2 < F.extent i := fun i => by
    rcases hag.1 i with h | h
    · rw [hside] at h
      omega
    · exact h
  have hoddF : Odd F.blockSide := by rw [hLF]; exact hDr.odd_L
  obtain ⟨ι, iF, iD, j, j', hpair⟩ := hPair F F Y Y q hoddF rfl hsd hsd
  have hjj : j' = j := by
    funext i
    obtain ⟨h, o, k, -, -, e, e'⟩ := hpair.short_offsets i
    exact Subtype.ext (e'.trans e.symm)
  subst hjj
  have conv : ∀ W : F.GaugeField F.top, IsSmallCurvature (5 / 4 * T.σ) W →
      ∃ Ψc : StepVariable (finiteCells F) → ℝ,
        (∀ η, (∀ b, ‖η b‖ < T.ballRadius) → Ψc η = (coldHalfLawAt T x f).exponent W η) ∧
        Continuous Ψc := fun W hW => by
    let M : LawOnBondVariables ↥(chordBonds (finiteCells F)) := lawAtTop W ((coldHalfLawAt T x f).exponent W)
    have hadm : M.IsAdmissible T.a T.chainParams.ρA T.chainParams.lam x T.σ T.decayRate T.E T.energyRatio
        T.L t T.n₀ (frameRadius x) (chordBondDist F) :=
      ⟨htop, hW, IsIntermediateLaw.ofFamily 1 f zero_le_one le_rfl hfam, Function.injective_id,
        fun _ _ => rfl⟩
    obtain ⟨hconv, -, -⟩ := (hPT t x hfl).laws _ (chordBondDist F) 1 (fun _ => 1) (fun _ => M)
      ⟨fun _ => zero_le_one, by simp⟩ (fun _ => hadm)
    rw [convexCombinationExponent_lawAtTop] at hconv
    obtain ⟨Ψ', K', hΨ', hconvex, -, -⟩ := hconv
    exact ⟨Ψ', hΨ', hconvex.smooth.continuous⟩
  obtain ⟨Ψc, hΨ, hc⟩ := conv V hV
  obtain ⟨Ψc', hΨ', hc'⟩ := conv V' hV'
  have hst : IsAdmissibleAt T t x f F V := ⟨hfl, hfam, htop, hV⟩
  have hst' : IsAdmissibleAt T t x f F V' := ⟨hfl, hfam, htop, hV'⟩
  obtain ⟨m₁, i₁, i₁'⟩ := comparablePair_expectation_freeze (K := (coldHalfLawAt T x f).cutoffTerm Y) hDr
    hLaw hFzT hfl hfam htop hV hV' hag hpair hΨ hc hΨ' hc' hC₁
    (A₁ F V V' Y q ι j' htop hV hV' hag hpair)
  obtain ⟨m₂, i₂, i₂'⟩ := comparablePair_expectation_freeze (K := (coldHalfLawAt T x f).familyTerm Y) hDr
    hLaw hFzT hfl hfam htop hV hV' hag hpair hΨ hc hΨ' hc' hC₂
    (A₂ F V V' Y q ι j' htop hV hV' hag hpair)
  obtain ⟨m₃, i₃, i₃'⟩ := comparablePair_expectation_freeze
    (K := (coldHalfLawAt T x f).exponentRadialPart Y) hDr
    hLaw hFzT hfl hfam htop hV hV' hag hpair hΨ hc hΨ' hc' hC₃
    (A₃ F V V' Y q ι j' htop hV hV' hag hpair)
  obtain ⟨m₄, i₄, i₄'⟩ := comparablePair_expectation_freeze
    (K := (coldHalfLawAt T x f).linearBlockPart Y) hDr
    hLaw hFzT hfl hfam htop hV hV' hag hpair hΨ hc hΨ' hc' hC₄
    (a₄ t x f F F V V' Y Y q ι j' j' hst hst' hrow hag hpair).2.1
  set Q := coldHalfLawAt T x f with hQ
  have off : ∀ W : F.GaugeField F.top, ∀ Ψw : StepVariable (finiteCells F) → ℝ,
      (∀ η, (∀ b, ‖η b‖ < T.ballRadius) → Ψw η = Q.exponent W η) →
      Continuous Ψw → ∀ η, ¬ (∀ b, ‖η b‖ < T.ballRadius) →
        ballDensity (cutoffFactor T.ballRadius T.p) (Q.exponent W) η = 0 := fun W Ψw hw hcw η hη => by
    obtain ⟨-, -, -, -, -, -, -, -, -, hnz, -⟩ := hLaw _ T.ballRadius T.p Ψw hρ hDr.cutoff hcw
    have h0 : ballDensity (cutoffFactor T.ballRadius T.p) Ψw η = 0 := by
      by_contra hne
      exact hη ((hnz η).1 hne)
    unfold ballDensity at h0 ⊢
    rcases mul_eq_zero.1 h0 with h | h
    · rw [h, zero_mul]
    · exact absurd h (Real.exp_pos _).ne'
  have rest : ∀ W : F.GaugeField F.top, IsAdmissibleAt T t x f F W →
      ∀ Ψw : StepVariable (finiteCells F) → ℝ,
      (∀ η, (∀ b, ‖η b‖ < T.ballRadius) → Ψw η = Q.exponent W η) → Continuous Ψw →
      (Integrable fun η => Q.cutoffTerm Y η W *
        ballDensity (cutoffFactor T.ballRadius T.p) (Q.exponent W) η) →
      (Integrable fun η => Q.familyTerm Y η W *
        ballDensity (cutoffFactor T.ballRadius T.p) (Q.exponent W) η) →
      (Integrable fun η => Q.exponentRadialPart Y η W *
        ballDensity (cutoffFactor T.ballRadius T.p) (Q.exponent W) η) →
      (Integrable fun η => Q.linearBlockPart Y η W *
        ballDensity (cutoffFactor T.ballRadius T.p) (Q.exponent W) η) →
      Q.dilationRemainder Y W = 1 / (2 * x) * (- Q.expectation W (fun η => Q.cutoffTerm Y η W) +
        Q.expectation W (fun η => Q.familyTerm Y η W) +
        2 * Q.expectation W (fun η => Q.linearBlockPart Y η W) -
        Q.expectation W (fun η => Q.exponentRadialPart Y η W)) :=
    fun W hW Ψw hw hcw b₁ b₂ b₃ b₄ => by
    have e1 : Q.expectation W (fun η => - Q.cutoffTerm Y η W + Q.gapTerm Y η W + Q.familyTerm Y η W -
          Q.slopeTerm Y η W) =
        Q.expectation W (fun η => - Q.cutoffTerm Y η W + Q.familyTerm Y η W +
          2 * Q.linearBlockPart Y η W - Q.exponentRadialPart Y η W) := by
      refine ballExpectation_congr_of_eqOn_balls (off W Ψw hw hcw) fun η hη => ?_
      have := h₃' t x f F W Y η hW hη
      linarith
    have hc2 : Integrable fun η => (2 * Q.linearBlockPart Y η W) *
        ballDensity (cutoffFactor T.ballRadius T.p) (Q.exponent W) η := by
      simp_rw [mul_assoc]
      exact b₄.const_mul 2
    have e2 := ballExpectation_neg_add_add_sub (cutoffFactor T.ballRadius T.p) (Q.exponent W)
      (fun η => Q.cutoffTerm Y η W) (fun η => Q.familyTerm Y η W)
      (fun η => 2 * Q.linearBlockPart Y η W) (fun η => Q.exponentRadialPart Y η W) b₁ b₂ hc2 b₃
    have e3 : ballExpectation (cutoffFactor T.ballRadius T.p) (Q.exponent W)
          (fun η => 2 * Q.linearBlockPart Y η W) =
        2 * ballExpectation (cutoffFactor T.ballRadius T.p) (Q.exponent W)
          (fun η => Q.linearBlockPart Y η W) := by
      unfold ballExpectation
      simp_rw [mul_assoc]
      rw [integral_const_mul, mul_div_assoc]
    have e4 : Q.dilationRemainder Y W = 1 / (2 * x) *
        Q.expectation W (fun η => - Q.cutoffTerm Y η W + Q.gapTerm Y η W + Q.familyTerm Y η W -
          Q.slopeTerm Y η W) := rfl
    rw [e4, e1]
    exact congrArg _ (e2.trans (by rw [e3]; rfl))
  have r₁ := rest V hst Ψc hΨ hc i₁ i₂ i₃ i₄
  have r₂ := rest V' hst' Ψc' hΨ' hc' i₁' i₂' i₃' i₄'
  rw [r₁, r₂, ← mul_sub, abs_mul, abs_of_pos (by positivity : 0 < 1 / (2 * x)), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [abs_le] at m₁ m₂ m₃ m₄ ⊢
  constructor <;> nlinarith [m₁.1, m₁.2, m₂.1, m₂.2, m₃.1, m₃.2, m₄.1, m₄.2]
end YangMills.Construction.ResponseInTheExpansion
end
