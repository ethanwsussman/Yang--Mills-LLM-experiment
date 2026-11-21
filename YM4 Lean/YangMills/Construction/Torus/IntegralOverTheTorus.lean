import YangMills.Construction.Lattice.ObservablesAndTestNorms
import YangMills.Construction.Lattice.ToriLatticesNormsAndFunctionsOfFinitelyManyVariables
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory Set TorusMetric
open scoped ENNReal
namespace PeriodicLattice
variable {L m : ℕ}
@[reducible] def borelSets (L m : ℕ) : MeasurableSpace (FourTorus L m) :=
  @borel _ (metricTopology L m)
structure IsBoundedBorel (h : FourTorus L m → ℝ) : Prop where
  bounded : TestFunctions.IsBoundedFun h
  measurable : @Measurable _ _ (borelSets L m) _ h
theorem continuous_torusProj :
    @Continuous _ _ _ (metricTopology L m) (torusProj (torusSide L m)) := by
  refine (@continuous_def _ _ _ (metricTopology L m) _).2 fun O hO => ?_
  refine isOpen_iff_mem_nhds.2 fun x hx => ?_
  obtain ⟨r, hr, hsub⟩ := hO (torusProj (torusSide L m) x) hx
  have hcont : Continuous fun y : Fin 4 → ℝ => euclidNormVec (y - x) := by
    unfold euclidNormVec
    fun_prop
  have hzero : euclidNormVec (x - x) < r := by simpa [euclidNormVec] using hr
  filter_upwards [hcont.continuousAt.eventually (gt_mem_nhds hzero)] with y hy
  refine hsub ?_
  have hdiff : torusProj (torusSide L m) y - torusProj (torusSide L m) x =
      torusProj (torusSide L m) (y - x) := by
    funext μ
    simp [torusProj]
  have hle : torusEuclidNorm (torusProj (torusSide L m) y - torusProj (torusSide L m) x) ≤
      euclidNormVec (y - x) :=
    csInf_le ⟨0, by
      rintro _ ⟨v, -, rfl⟩
      exact Real.sqrt_nonneg _⟩ ⟨y - x, hdiff.symm, rfl⟩
  exact lt_of_le_of_lt hle hy
end PeriodicLattice
end YangMills.Construction
