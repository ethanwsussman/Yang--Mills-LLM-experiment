import YangMills.Construction.LawInAState.ProductsOfMarksAtOneLevelProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.WeightedResponses
open TorusFields TorusLumps
variable {P : StepParameters}
private theorem continuous_curvatureObservable {m : ℕ} [NeZero m] (w : PlaquetteWeight m) :
    Continuous (curvatureObservable w) := by apply _root_.YangMills.SharedProofs.p1196 <;> assumption
private theorem abs_sourceTerm_le (hSc : BondScoreProperties) (hP : P.Admissible) (T : StageTower P)
    (coef : ℕ → ℝ) (s n : ℕ) [NeZero n] (w : PlaquetteWeight (fineSide P.side (s + 1) n))
    (u : MarkedSample P (s + 1) n) :
    |sourceTerm T coef s n w u| ≤
      |P.coupling / 2 * coef s| * ∑ Y : TorusSite n, |blockMean P.side (s + 1) n Y w| * 16 := by
  unfold sourceTerm stepSourceTerm
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun Y _ => ?_)
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h1 : ∀ i : Fin 4,
      |bondScore P (T.stage s).coupling (topField P s (n * P.side) u.1) u.2.2.1 u.2.1 (Y, i) +
        bondScore P (T.stage s).coupling (topField P s (n * P.side) u.1) u.2.2.1 u.2.1
          (Y - unitStep n i, i)| ≤ 4 := by
    intro i
    have a1 := (hSc P hP (T.stage s).coupling n u.2.1 (Y, i)).2.2.1 (topField P s (n * P.side) u.1) u.2.2.1
    have a2 := (hSc P hP (T.stage s).coupling n u.2.1 (Y - unitStep n i, i)).2.2.1
      (topField P s (n * P.side) u.1) u.2.2.1
    exact (abs_add_le _ _).trans (by linarith)
  calc _ ≤ ∑ _i : Fin 4, (4 : ℝ) := Finset.sum_le_sum fun i _ => h1 i
    _ = 16 := by norm_num
theorem responsesBounded (hTP : ResponseInTheExpansion.TwoPointByTotalCovarianceStatement)
    (hSc : BondScoreProperties) : ResponsesBounded := by
  intro P hP hPl T hcut hcoin β coef s
  induction s with
  | zero =>
    intro n _ w
    have hc : Continuous (curvatureObservable (m := n) w) := continuous_curvatureObservable w
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
    refine ⟨hc.measurable, C, Filter.Eventually.of_forall fun W => ?_⟩
    have := hC W (Set.mem_univ _)
    rw [Real.norm_eq_abs] at this
    exact this
  | succ s ih =>
    intro n _ w
    obtain ⟨hm, C, hC⟩ := ih (n * P.side) w
    have hG := (hTP P hP hPl T hcut hcoin β coef (s + 1) n).2.1
    have hS : response T β coef (s + 1) n w =
        (markedSampleLaw T β (s + 1) n)[stepSum T β coef s n w | stageSigma T (s + 1) n] := by
      funext u
      rfl
    have hb : ∀ᵐ u ∂(markedSampleLaw T β (s + 1) n), |response T β coef s (n * P.side) w u.1| ≤ C := by
      have h1 := (Measure.quasiMeasurePreserving_fst (μ := markedSampleLaw T β s (n * P.side))
        (ν := stepReferenceMeasure P n)).ae hC
      exact (withDensity_absolutelyContinuous _ _).ae_le h1
    have hX : ∀ᵐ u ∂(markedSampleLaw T β (s + 1) n), |stepSum T β coef s n w u| ≤
        |C| + |P.coupling / 2 * coef s| * ∑ Y : TorusSite n, |blockMean P.side (s + 1) n Y w| * 16 := by
      filter_upwards [hb] with u hu
      have h2 := abs_sourceTerm_le hSc hP T coef s n w u
      have h3 := abs_add_le (response T β coef s (n * P.side) w u.1) (sourceTerm T coef s n w u)
      have h4 := le_abs_self C
      have h5 : |stepSum T β coef s n w u| =
        |response T β coef s (n * P.side) w u.1 + sourceTerm T coef s n w u| := rfl
      rw [h5]
      linarith
    rw [hS]
    exact ⟨(stronglyMeasurable_condExp.mono hG).measurable, _, ae_bdd_abs_condExp_of_ae_bdd_abs hX⟩
end YangMills.Construction.WeightedResponses
end
