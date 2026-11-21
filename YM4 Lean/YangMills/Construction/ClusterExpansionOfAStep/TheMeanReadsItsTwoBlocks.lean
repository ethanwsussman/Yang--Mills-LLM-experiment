import YangMills.Construction.ClusterExpansionOfAStep.LumpsOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusLumps
open BlockAverages (unitStep)
open LumpContours (contourMean nearbyLumps sitesBelow)
def ContourMeanReadsTwoBlocks : Prop :=
  ∀ (L n d : ℕ) [NeZero L] [NeZero n], Odd L → 16 ≤ n →
    ∀ (h h' : Finset (Finset ((stepBlockFrame L n).Site 0)))
      (b b' : (stepBlockFrame L n).Cell → (stepBlockFrame L n).Site 0) (W W' : (stepBlockFrame L n).GaugeField 0)
      (y : (stepBlockFrame L n).Cell) (i : Fin 4),
      nearbyLumps h y = nearbyLumps h' y →
      nearbyLumps h (y + unitStep 1 i) = nearbyLumps h' (y + unitStep 1 i) →
      b y = b' y → b y ∈ sitesBelow 0 y →
      b (y + unitStep 1 i) = b' (y + unitStep 1 i) → b (y + unitStep 1 i) ∈ sitesBelow 0 (y + unitStep 1 i) →
      (∀ (x : (stepBlockFrame L n).Site 0) (k : Fin 4), (x ∈ sitesBelow 0 y ∨ x ∈ sitesBelow 0 (y + unitStep 1 i)) →
        (x + unitStep 0 k ∈ sitesBelow 0 y ∨ x + unitStep 0 k ∈ sitesBelow 0 (y + unitStep 1 i)) → W x k = W' x k) →
      contourMean d h b W (y, i) = contourMean d h' b' W' (y, i)
end YangMills.Construction.TorusLumps
end
