import YangMills.Construction.Matrices.SpecialUnitaryTwoNotation
import Mathlib
open Filter
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
namespace YangMills.Construction.Matrices.ComplexMatrix2
def coordinateNorm (v : EuclideanSpace ℂ (Fin 2)) : ℝ := (‖v 0‖ ^ 2 + ‖v 1‖ ^ 2) ^ (1 / 2 : ℝ)
theorem coordinateNorm_eq_norm (v : EuclideanSpace ℂ (Fin 2)) : coordinateNorm v = ‖v‖ := by
  rw [coordinateNorm, EuclideanSpace.norm_eq, Real.sqrt_eq_rpow, Fin.sum_univ_two]
def seriesPartialSum (X : ℕ → ComplexMatrix2) (l : ℕ) : ComplexMatrix2 :=
  ∑ n ∈ Finset.range (l + 1), X n
def HasSeriesSum (X : ℕ → ComplexMatrix2) (S : ComplexMatrix2) : Prop :=
  Tendsto (fun l => operatorNorm (S - seriesPartialSum X l)) atTop (𝓝 0)
def SeriesConvergent (X : ℕ → ComplexMatrix2) : Prop := ∃ S, HasSeriesSum X S
def SeriesAbsolutelyConvergent (X : ℕ → ComplexMatrix2) : Prop :=
  ∃ s : ℝ, Tendsto (fun l => ∑ n ∈ Finset.range (l + 1), operatorNorm (X n)) atTop (𝓝 s)
def expSeriesTerm (Y : ComplexMatrix2) (n : ℕ) : ComplexMatrix2 := ((n.factorial : ℂ)⁻¹) • Y ^ n
def logSeriesTerm (Y : ComplexMatrix2) (n : ℕ) : ComplexMatrix2 :=
  if n = 0 then 0 else -(((n : ℂ)⁻¹) • (1 - Y) ^ n)
def expSeriesPartialSum (Y : ComplexMatrix2) (l : ℕ) : ComplexMatrix2 :=
  ∑ n ∈ Finset.range (l + 1), ((n.factorial : ℂ)⁻¹) • Y ^ n
def logSeriesPartialSum (Y : ComplexMatrix2) (l : ℕ) : ComplexMatrix2 :=
  -∑ n ∈ Finset.Icc 1 l, ((n : ℂ)⁻¹) • (1 - Y) ^ n
theorem seriesPartialSum_expSeriesTerm (Y : ComplexMatrix2) (l : ℕ) :
    seriesPartialSum (expSeriesTerm Y) l = expSeriesPartialSum Y l :=
  rfl

theorem seriesPartialSum_logSeriesTerm (Y : ComplexMatrix2) (l : ℕ) :
    seriesPartialSum (logSeriesTerm Y) l = logSeriesPartialSum Y l := by
  induction l with
  | zero => simp [seriesPartialSum, logSeriesPartialSum, logSeriesTerm]
  | succ l ih =>
    have h : seriesPartialSum (logSeriesTerm Y) (l + 1) =
        seriesPartialSum (logSeriesTerm Y) l + logSeriesTerm Y (l + 1) :=
      Finset.sum_range_succ _ _
    rw [h, ih, logSeriesPartialSum, logSeriesPartialSum, Finset.sum_Icc_succ_top (by omega),
      logSeriesTerm, if_neg (by omega), neg_add]
theorem matExp_eq_tsum_expSeriesTerm (Z : ComplexMatrix2) :
    matExp Z = ∑' n : ℕ, expSeriesTerm Z n := by apply _root_.YangMills.Construction.Matrices.ComplexMatrix2.matExp_eq_tsum <;> assumption
theorem logSeries_eq_tsum_logSeriesTerm (X : ComplexMatrix2) :
    logSeries X = ∑' n : ℕ, logSeriesTerm X n := by
  have hs : Function.support (logSeriesTerm X) ⊆ Set.range Nat.succ := by
    intro n hn
    rcases n with _ | n
    · exact absurd (by simp [logSeriesTerm]) hn
    · exact ⟨n, rfl⟩
  rw [← Nat.succ_injective.tsum_eq hs, logSeries, ← tsum_neg]
  refine tsum_congr fun n => ?_
  simp [logSeriesTerm]
end YangMills.Construction.Matrices.ComplexMatrix2
