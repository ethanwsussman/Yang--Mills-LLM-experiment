import YangMills.Construction.ClusterExpansionOfAStep.NumbersOfTheStepAreFiniteProof
import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
import YangMills.Construction.RunningCouplingSlope.CoefficientOfALocalDensityProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SlopeCoefficient
open YangMills.Construction.TorusFields YangMills.Construction.TorusLumps
theorem summable_prod_pow_natAbs {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    Summable fun v : Fin 4 → ℤ => ∏ i, r ^ (v i).natAbs := by apply _root_.YangMills.Construction.RunningCouplingSlope.LocalDensityCoefficient.summable_prod_pow_natAbs <;> assumption
theorem natAbs_le_offsetNorm (v : Fin 4 → ℤ) (i : Fin 4) : (v i).natAbs ≤ offsetNorm v := by apply _root_.YangMills.Construction.LatticePaths.natAbs_le_supNorm <;> assumption
def expWeight (c : ℝ) (v : Fin 4 → ℤ) : ℝ := Real.exp (-(c * offsetNorm v))
theorem summable_expWeight {c : ℝ} (hc : 0 < c) : Summable (expWeight c) := by apply _root_.YangMills.Construction.TorusLumps.PotentialSums.summable_exp_neg_offsetNorm <;> assumption
variable {n : ℕ} [NeZero n]
def minimalCoords (u : TorusSite n) : Fin 4 → ℤ := fun i => (u i).valMinAbs
theorem minimalCoords_injective : Function.Injective (minimalCoords (n := n)) := by apply _root_.YangMills.Construction.RunningCouplingSlope.LocalDensityCoefficient.siteCoords_injective <;> assumption
theorem expDecayTorusSumBounded_proof : ExpDecayTorusSumBounded := by
  intro c hc
  have hnn : ∀ z, 0 ≤ expWeight c z := fun z => (Real.exp_pos _).le
  have hpos : 0 < ∑' z, expWeight c z + 1 := by
    have : 0 ≤ ∑' z, expWeight c z := tsum_nonneg hnn
    linarith
  refine ⟨∑' z, expWeight c z + 1, hpos, fun n _ y => ?_⟩
  classical
  have e1 : ∑ x : TorusSite n, Real.exp (-(c * supDist y x)) =
      ∑ u : TorusSite n, expWeight c (minimalCoords u) := by
    refine Fintype.sum_equiv (Equiv.subLeft y) _ _ fun x => ?_
    rfl
  rw [e1, ← Finset.sum_image (f := expWeight c) (s := Finset.univ) (g := minimalCoords (n := n))
    (fun a _ b _ h => minimalCoords_injective h)]
  have := (summable_expWeight hc).sum_le_tsum (Finset.univ.image (minimalCoords (n := n)))
    fun z _ => hnn z
  linarith
end YangMills.Construction.SlopeCoefficient
end
