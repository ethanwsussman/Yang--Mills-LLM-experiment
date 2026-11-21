import YangMills.Construction.ClusterExpansionOfAStep.PlaquettesUnderGaugesAndMoves
import YangMills.Construction.RunningCouplingSlope.CoefficientOfALocalDensity
import YangMills.Construction.RunningCouplingSlope.DensityOfTheStepIsLocal
import YangMills.Construction.RunningCouplingSlope.StepTotalsHaveCoefficients
import YangMills.Construction.RunningCouplingSlope.TotalOfAStepIsATotal
import YangMills.Construction.RunningCouplingSlope.TotalOfAStepReadsNoBound
import Mathlib
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
open scoped Topology Quaternion
open Filter
namespace YangMills.Construction
open BlockAverages TorusFields TorusLumps RenormalizationStepParameters SlopeCoefficient Conventions
namespace RunningCouplingSlope.StepGaugeTotals
theorem continuous_expUnit : Continuous expUnit := by apply _root_.YangMills.Construction.TorusFields.continuous_expUnit <;> assumption
theorem expUnit_zero : expUnit 0 = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
variable {n : ℕ}
theorem perturb_zero_trivialField {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) :
    perturb c X 0 (trivialField n) = trivialField n := by
  funext x i
  simp [perturb, trivialField, expUnit_zero]
theorem tendsto_perturb_trivialField {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) :
    Tendsto (fun s : Fin k → ℝ => perturb c X s (trivialField n)) (𝓝 0) (𝓝 (trivialField n)) := by
  have hc : Continuous fun s : Fin k → ℝ => perturb c X s (trivialField n) := by
    refine continuous_pi fun x => continuous_pi fun i => ?_
    refine (continuous_expUnit.comp (continuous_finsetSum _ fun l _ => ?_)).mul continuous_const
    split_ifs
    · exact (continuous_apply l).smul continuous_const
    · exact continuous_const
  have := hc.tendsto 0
  rwa [perturb_zero_trivialField] at this
theorem hessianAtTrivial_congr_germ {H H' : GaugeTotal} {n : ℕ}
    (h : ∀ᶠ V in 𝓝 (trivialField n), H n V = H' n V) (c c' : TorusBond n) (X X' : imaginaryQuaternions) :
    hessianAtTrivial H n c c' X X' = hessianAtTrivial H' n c c' X X' := by
  simp only [hessianAtTrivial, mixedDeriv]
  have hev : (fun s : Fin 2 → ℝ => H n (perturb ![c, c'] ![X, X'] s (trivialField n))) =ᶠ[𝓝 0]
      fun s => H' n (perturb ![c, c'] ![X, X'] s (trivialField n)) := by
    filter_upwards [(tendsto_perturb_trivialField ![c, c'] ![X, X']).eventually h] with s hs
    exact hs
  rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hev 2).eq_of_nhds]
theorem slopeCoefficient_unique_of_germ {H H' : GaugeTotal} {b : ℝ}
    (h : ∀ᶠ n in atTop, ∀ᶠ V in 𝓝 (trivialField n), H n V = H' n V)
    (ht : ∀ᶠ n in atTop, IsGaugeTotalAt H n)
    (hH' : HasSlopeCoefficient atTop H' b) : HasSlopeCoefficient atTop H b := by
  obtain ⟨K, hK, hs⟩ := hH'
  obtain ⟨M, θ, hθ, hd⟩ := hK.exp_decay
  refine ⟨K, ⟨ht, ⟨M, θ, hθ, ?_⟩, fun c c' X X' => ?_⟩, hs⟩
  · filter_upwards [h, hd] with n hn hdn c c' X X' hX hX'
    rw [hessianAtTrivial_congr_germ hn]
    exact hdn c c' X X' hX hX'
  · refine (hK.tendsto_kernel c c' X X').congr' ?_
    filter_upwards [h] with n hn
    exact (hessianAtTrivial_congr_germ hn _ _ _ _).symm
theorem stepGaugeTotalsHaveSlopeCoefficients_of_parts (hc : LocalDensityCoefficient.Claim)
    (hd : StepDensityIsLocal.Claim)
    (ht : StepGaugeTotalIsGaugeTotal) (hb : StepGaugeTotalIndependentOfCutoff) :
    StepGaugeTotalsHaveSlopeCoefficients := by
  rintro _ _ ⟨T, hT, rfl, rfl⟩ t
  have ha : 0 < T.coupling := by linarith [hT.a_ge]
  have hL : IsAdmissibleBlockingFactor T.side := ⟨hT.L_odd, le_trans (by norm_num) hT.L_ge⟩
  obtain ⟨-, -, -, hρ, hρ1, -⟩ := hT.chain
  obtain ⟨h1, h2⟩ := hd T hT t
  obtain ⟨b, hb1⟩ := hc _ (stepGaugeTotal T.coupling T.ρA T.side t) h1
    (ht T.coupling ha T.side hL t T.ρA hρ hρ1) h2
  exact ⟨b, fun ρ h0 h1' =>
    slopeCoefficient_unique_of_germ (hb T.coupling ha T.side hL t ρ T.ρA h0 h1' hρ hρ1)
      (ht T.coupling ha T.side hL t ρ h0 h1') hb1⟩
end RunningCouplingSlope.StepGaugeTotals
end YangMills.Construction
end
