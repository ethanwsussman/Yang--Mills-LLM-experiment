import YangMills.Construction.ColdStepAtMirrorFrames.FlatChainsOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame}
def CurlShiftBound : Prop :=
  ∀ a : ℝ, 1 ≤ a → ∃ C : ℝ, 0 < C ∧ ∃ L₀ : ℕ,
    ∀ (F : BlockFrame) (c : F.Site F.top × Fin 4) (B : FormChain F),
    Odd F.blockSide → L₀ ≤ F.blockSide → IsLargeCubicTorus F → IsFlatChain a c B →
    ∀ (z : F.Site F.depth) (h : Fin 4 → ℤ) (n : ℕ), (∀ i, |h i| ≤ n) → (∃ i, |h i| = n) → 1 ≤ n →
      n ≤ F.blockSide →
      ∑ p ∈ (sitesOfCells (finiteCells F) F.depth).filter
          (fun p => siteSupDist p z ≤ F.blockSide), ∑ e ∈ orientedPlanes,
        (plaquetteCurl (B F.depth) (p + siteOfCoords F.depth h) e.1 e.2 -
          plaquetteCurl (B F.depth) p e.1 e.2) ^ 2 ≤
      C * ((n : ℝ) / F.blockSide) * chainEnergyOnSites a B (depthBall z (9 * F.blockSide))
end ColdStepAtMirrorFrames
end YangMills.Construction
end
