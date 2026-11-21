import YangMills.Construction.Torus.PropertiesOfTheWeightedDistanceAndCells
import YangMills.Construction.Torus.LayersCellsBlocksAndTheDistanceProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set TorusMetric
namespace GeneralTorus.ShellSeparation
variable {D : ScaleData} (B : SeparatedChain D)
theorem scaledDist_nonneg (hp : B.ScaledDistIsPseudometric) (x x' : D.Space) :
    0 ≤ B.scaledDist x x' := by
  obtain ⟨-, -, hs, hz, ht⟩ := hp
  have h1 := ht x x' x
  rw [hz x, hs x' x] at h1
  linarith
end GeneralTorus.ShellSeparation
end YangMills.Construction
end
