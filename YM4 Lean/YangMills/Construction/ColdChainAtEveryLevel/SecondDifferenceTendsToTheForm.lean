import YangMills.Construction.ColdChainAtEveryLevel.SecondDifferencesAsLimits
import YangMills.Construction.ColdChainAtEveryLevel.SmallMultiplesOfTwoDirections
import YangMills.Construction.ColdChainAtEveryLevel.VariationsAlongAMisfit
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.SecondDifferences
open BlockAverages
variable {F : BlockFrame}
open Filter Topology
private theorem chartShift_zero (U A : ChainChart F) : chartMove U A 0 = U := by apply _root_.YangMills.Construction.MisfitVariation.chartMove_zero <;> assumption
private theorem chartShift_pair (U A : ChainChart F) (τ σ : ℝ) :
    chartMove (chartMove (zeroChart F) U τ) A σ = chartShiftMulti (zeroChart F) ![U, A] ![τ, σ] := by
  simp [chartMove, chartShiftMulti, zeroChart, Fin.sum_univ_two]
theorem tendsto_chartAction_secondDifference (a : ℝ) (S : Finset F.Cell) (R : F.FieldChain) (V : F.GaugeField F.top)
    (U A : ChainChart F)
    (h : AnalyticAt ℝ (fun t : Fin 2 → ℝ => chartAction a S R (chartShiftMulti (zeroChart F) ![U, A] t) V) 0) :
    Tendsto (fun ε : ℝ => (chartAction a S R (SmallMultiples.scaledSumChart U A ε) V - chartAction a S R (SmallMultiples.scaledChart U ε) V -
        chartAction a S R (SmallMultiples.scaledChart A ε) V + chartAction a S R (zeroChart F) V) / ε ^ 2)
      (𝓝[>] 0) (𝓝 (referenceSecondDeriv a S R V U A)) := by
  set f : (Fin 2 → ℝ) → ℝ := fun t => chartAction a S R (chartShiftMulti (zeroChart F) ![U, A] t) V with hf
  set e : ℝ × ℝ → (Fin 2 → ℝ) := fun q => ![q.1, q.2] with he
  set g : ℝ × ℝ → ℝ := fun q => chartAction a S R (chartMove (chartMove (zeroChart F) U q.1) A q.2) V with hg
  have hgf : g = f ∘ e := by
    funext q
    simp only [hg, hf, he, Function.comp, chartShift_pair]
  have he0 : e 0 = 0 := by
    funext i
    fin_cases i <;> simp [he]
  have hel : ContDiff ℝ 2 e := by
    refine contDiff_pi.2 fun i => ?_
    fin_cases i
    · simpa [he] using (contDiff_fst : ContDiff ℝ 2 (Prod.fst : ℝ × ℝ → ℝ))
    · simpa [he] using (contDiff_snd : ContDiff ℝ 2 (Prod.snd : ℝ × ℝ → ℝ))
  have hc : ContDiffAt ℝ 2 g 0 := by
    rw [hgf]
    refine ContDiffAt.comp 0 ?_ hel.contDiffAt
    rw [he0]
    exact h.contDiffAt
  have key := Calculus.tendsto_secondDifference_div_sq hc
  have val : deriv (fun τ : ℝ => deriv (fun σ : ℝ => g (τ, σ)) 0) 0 = referenceSecondDeriv a S R V U A := rfl
  rw [val] at key
  refine key.congr fun ε => ?_
  have g1 : g (ε, ε) = chartAction a S R (SmallMultiples.scaledSumChart U A ε) V := rfl
  have g2 : g (ε, 0) = chartAction a S R (SmallMultiples.scaledChart U ε) V := by
    simp only [hg, chartShift_zero]
    rfl
  have g3 : g (0, ε) = chartAction a S R (SmallMultiples.scaledChart A ε) V := by
    simp only [hg, chartShift_zero]
    rfl
  have g4 : g (0, 0) = chartAction a S R (zeroChart F) V := by
    simp only [hg, chartShift_zero]
  rw [g1, g2, g3, g4]
end YangMills.Construction.SecondDifferences
end
