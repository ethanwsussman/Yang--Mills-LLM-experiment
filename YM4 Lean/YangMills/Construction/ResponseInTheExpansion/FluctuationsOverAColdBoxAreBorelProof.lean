import YangMills.Construction.ResponseInTheExpansion.FluctuationsOfAStepAreBorel
import YangMills.Construction.ResponseInTheExpansion.FluctuationsOverAColdBoxAreBorel
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.TorusFields YangMills.Construction.TorusLumps YangMills.Construction.BlockAverages
open Classical
private theorem component_ite_eq_indicator {Ξ : Type} (S : Set Ξ) (g : Ξ → imaginaryQuaternions) (e : Fin 3)
    (c : ℍ[ℝ] → ℝ) (hc0 : c 0 = 0)
    (hc : ∀ w : imaginaryQuaternions, c (w : ℍ[ℝ]) = imaginaryComponent e w) :
    (fun p => c (if p ∈ S then ((g p : imaginaryQuaternions) : ℍ[ℝ]) else 0)) =
      S.indicator fun p => imaginaryComponent e (g p) := by
  funext p
  by_cases hp : p ∈ S
  · rw [if_pos hp, Set.indicator_of_mem hp, hc]
  · rw [if_neg hp, Set.indicator_of_notMem hp, hc0]
theorem coldBallDeviationMeasurable_of_step (h : stepDeviationMeasurableStatement) :
    coldBallDeviationMeasurableStatement := by
  intro a ha
  obtain ⟨L₀, rt₀, C₀, h0, hL⟩ := h a ha
  refine ⟨L₀, rt₀, C₀, h0, fun L h1 h2 T h3 h4 h5 h6 h7 h8 h9 => ?_⟩
  obtain ⟨y₀, hy⟩ := hL L h1 h2 T h3 h4 h5 h6 h7 h8 h9
  refine ⟨y₀, fun y hyy hret hw => ?_⟩
  obtain ⟨x₀, hx⟩ := hy y hyy hret hw
  refine ⟨x₀, fun Tw β k n _ nn j o b hloc _ hj hb => ?_⟩
  have hi := fun e => (hx Tw β k n nn j o hloc hj).1 b e hb
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e : (fun p : TorusField n × TorusField (n * (T.stepParameters y).side) =>
        (if IsColdOnBall (T.stepParameters y).threshold p.1 o (localBlockSide (T.stepParameters y) β k) then
          ((stepDeviation Tw (k + j) p.1 p.2 b : imaginaryQuaternions) : ℍ[ℝ]) else 0).re) = fun _ => 0 := by
      funext p
      split_ifs
      · exact (stepDeviation Tw (k + j) p.1 p.2 b).2
      · rfl
    rw [e]
    exact measurable_const
  · have hm := hi 0
    rw [← component_ite_eq_indicator _ _ 0 (fun q => q.imI) rfl fun _ => rfl] at hm
    exact hm
  · have hm := hi 1
    rw [← component_ite_eq_indicator _ _ 1 (fun q => q.imJ) rfl fun _ => rfl] at hm
    exact hm
  · have hm := hi 2
    rw [← component_ite_eq_indicator _ _ 2 (fun q => q.imK) rfl fun _ => rfl] at hm
    exact hm
end YangMills.Construction.ResponseInTheExpansion
end
