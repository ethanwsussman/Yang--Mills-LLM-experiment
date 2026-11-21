import YangMills.Construction.ResponseInTheExpansion.CalculusOfTheColdHalf
import YangMills.Construction.ResponseInTheExpansion.MeanIsBounded
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.WeightedResponses
open MeasureTheory BlockAverages ColdStepAtMirrorFrames Interpolation ConvexObservables
theorem expectationBounded (hLaw : normalizedBallLawIsProbabilityStatement) (hFB : interpolatedFramesStatement)
    (hJ : EventuallyInParametersCombines) : ResponseInTheExpansion.expectationBoundedStatement := by
  classical
  obtain ⟨join, weaken⟩ := hJ
  obtain ⟨Cm, Cz, Cr, hP⟩ := hFB
  refine weaken _ _ ?_ hP
  intro T hDr hPT t x f F V g M hst hg
  have hPT' := hPT t x hst.coupling_le
  set Q := coldHalfLawAt T x f with hQ
  let Mw : LawOnBondVariables ↥(chordBonds (finiteCells F)) := ResponseInTheExpansion.lawAtTop V (Q.exponent V)
  have hadm : Mw.IsAdmissible T.a T.chainParams.ρA T.chainParams.lam x T.σ T.decayRate T.E T.energyRatio T.L t T.n₀ (frameRadius x)
      (chordBondDist F) :=
    ⟨hst.torus, hst.small_curvature, IsIntermediateLaw.ofFamily 1 f zero_le_one le_rfl hst.family_bounded,
      Function.injective_id, fun _ _ => rfl⟩
  obtain ⟨hconv, -, -⟩ := hPT'.laws _ (chordBondDist F) 1 (fun _ => 1) (fun _ => Mw)
    ⟨fun _ => zero_le_one, by simp⟩ (fun _ => hadm)
  rw [ResponseInTheExpansion.convexCombinationExponent_lawAtTop] at hconv
  obtain ⟨Ψ', K', hΨ', hconvex, -, -⟩ := hconv
  have hΨc : Continuous Ψ' := hconvex.smooth.continuous
  have hρ : 0 < T.ballRadius := by
    have := hDr.σ_pos
    show 0 < T.σ / 64
    positivity
  obtain ⟨hpr, hme, -, hob, -, -, -, -, -, hnz, -⟩ := hLaw _ T.ballRadius T.p Ψ' hρ hDr.cutoff hΨc
  have hz : ∀ η : BondField ↥(chordBonds (finiteCells F)), ¬ (∀ b, ‖η b‖ < T.ballRadius) →
      ballDensity (cutoffFactor T.ballRadius T.p) Ψ' η = 0 := fun η hη => by
    by_contra hne
    exact hη ((hnz η).1 hne)
  have hd : ballDensity (cutoffFactor T.ballRadius T.p) (Q.exponent V) =
      ballDensity (cutoffFactor T.ballRadius T.p) Ψ' := by
    funext η
    by_cases hη' : ∀ b, ‖η b‖ < T.ballRadius
    · unfold ballDensity
      rw [hΨ' η hη']
    · have h0 := hz η hη'
      have h1 : radialWeightProd (cutoffFactor T.ballRadius T.p) η = 0 := by
        unfold ballDensity at h0
        rcases mul_eq_zero.1 h0 with h' | h'
        · exact h'
        · exact absurd h' (Real.exp_pos _).ne'
      rw [h0]
      unfold ballDensity
      rw [h1, zero_mul]
  have e : Q.expectation V g = ∫ η, g η ∂normalizedBallLaw (cutoffFactor T.ballRadius T.p) Ψ' := by
    rw [hme]
    show ballExpectation (cutoffFactor T.ballRadius T.p) (Q.exponent V) g = _
    unfold ballExpectation
    rw [hd]
  rw [e]
  have h1 : ‖∫ η, g η ∂normalizedBallLaw (cutoffFactor T.ballRadius T.p) Ψ'‖ ≤
      M * (normalizedBallLaw (cutoffFactor T.ballRadius T.p) Ψ').real Set.univ :=
    norm_integral_le_of_norm_le_const (by
      filter_upwards [hob] with η hη
      exact hg η hη)
  simpa using h1
end YangMills.Construction.WeightedResponses
end
