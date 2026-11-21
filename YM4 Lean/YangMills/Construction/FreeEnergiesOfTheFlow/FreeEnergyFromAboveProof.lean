import YangMills.Construction.ClusterExpansionOfAStep.ThreeFactsOfAnExpansion
import YangMills.Construction.ClusterExpansionOfAStep.WilsonWeightHasTheExpansionProof
import YangMills.Construction.FreeEnergiesOfTheFlow.ExpansionAlongTheFlow
import YangMills.Construction.FreeEnergiesOfTheFlow.FreeEnergyFromAbove
import YangMills.Construction.FreeEnergiesOfTheFlow.MassOfTheFlow
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.FreeEnergies
open TorusFields TorusLumps RenormalizationStepParameters ClusterExpansionOfAStep WeightedResponses
private theorem clusterRange_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : clusterRange x ≤ clusterRange y := by apply _root_.YangMills.Construction.WilsonExpansion.clusterRange_mono <;> assumption
theorem freeEnergyUpperBound_of_flow (hM : flowFunctionalIntegral) (hA : expansionAlongFlow)
    (h3 : ExpansionBasicBounds) : freeEnergyUpperBound := by
  intro ℓ hadm hrange₀ hS β t hr n _ hn
  obtain ⟨hmeas, hpos, ⟨Cb, hCb⟩, hmass, hZ⟩ := hM ℓ hadm β t n
  obtain ⟨-, f, hf, Λ, Dq, Φ, φ, hH⟩ := (hA ℓ hS β t hr).1
  have hx : ℓ.y₁ ≤ flowCoupling ℓ β t := hr t le_rfl
  have hy1 := hadm.y₁_ge
  have hrange : 4 * ℓ.n₀ + 2 ^ 16 ≤ clusterRange (flowCoupling ℓ β t) :=
    hrange₀.trans (clusterRange_mono (by linarith) hx)
  obtain ⟨-, -, h23⟩ := h3 ℓ t _ _ f Λ Dq Φ φ hadm hadm.E_ge (by linarith) hrange hf hH
  have hb := h23 n hn
  have hv : 0 < flowFunctionalAtTrivial ℓ β t n := hpos (trivialField n)
  refine ⟨hv, ?_⟩
  have hI : Integrable (flowFunctional ℓ β t n) (fieldHaar n) := by
    refine Integrable.of_bound hmeas.aestronglyMeasurable Cb (Filter.Eventually.of_forall fun V => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (hpos V)]
    exact hCb V
  set N : ℕ := Fintype.card (TorusSite n) with hN
  have hcard : (N : ℝ) = (n : ℝ) ^ 4 := by
    simp [hN, TorusSite, ZMod.card]
  have hZle : torusPartition ℓ β t n ≤ flowFunctionalAtTrivial ℓ β t n * 2 ^ N * Real.exp (2 * ℓ.E * N) := by
    rw [← hmass]
    have h1 : ∫ V, flowFunctional ℓ β t n V ∂(fieldHaar n) ≤
        ∫ _V : TorusField n, flowFunctionalAtTrivial ℓ β t n * 2 ^ N * Real.exp (2 * ℓ.E * N) ∂(fieldHaar n) :=
      integral_mono hI (integrable_const _) hb
    simpa using h1
  have h2 : (0 : ℝ) < 2 ^ N := by positivity
  calc Real.log (torusPartition ℓ β t n)
        ≤ Real.log (flowFunctionalAtTrivial ℓ β t n * 2 ^ N * Real.exp (2 * ℓ.E * N)) :=
        Real.log_le_log hZ hZle
    _ = Real.log (flowFunctionalAtTrivial ℓ β t n) + (Real.log 2 + 2 * ℓ.E) * (n : ℝ) ^ 4 := by
      rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_mul hv.ne' h2.ne', Real.log_pow,
        Real.log_exp, hcard]
      ring
end YangMills.Construction.FreeEnergies
end
