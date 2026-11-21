import YangMills.Construction.ClusterExpansionOfAStep.LumpsOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.TorusLumps
open BlockAverages LumpContours
def PlainFitsOfNearFields : Prop :=
  ∀ (L n : ℕ) [NeZero L] [NeZero n], Odd L → 16 ≤ n → ∀ (W W' : (stepBlockFrame L n).GaugeField 0)
    (V : (stepBlockFrame L n).GaugeField 1) (y : (stepBlockFrame L n).Cell) (i : Fin 4) (ε : ℝ), 0 ≤ ε →
    (∀ (x : (stepBlockFrame L n).Site 0) (k : Fin 4),
      (x ∈ sitesBelow 0 y ∨ x ∈ sitesBelow 0 (y + unitStep 1 i)) →
      (x + unitStep 0 k ∈ sitesBelow 0 y ∨ x + unitStep 0 k ∈ sitesBelow 0 (y + unitStep 1 i)) →
      ‖(W x k : ℍ[ℝ]) - W' x k‖ ≤ ε) →
    |blockFit W V (y, i) - blockFit W' V (y, i)| ≤ 18 * L * ε
end YangMills.Construction.TorusLumps
end
