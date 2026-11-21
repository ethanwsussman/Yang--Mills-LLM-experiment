import YangMills.Construction.ColdStepAtMirrorFrames.MirrorTorusAndFrames
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
def ReflectedCoordinateReadsBox : Prop :=
  ∀ (F F' : BlockFrame) (m : ℕ) (a ρ : ℝ) (y : F.Cell) (y' : F'.Cell) (V : F.GaugeField F.top)
    (V' : F'.GaugeField F'.top) (o : Fin 4 → ℤ) (i : Fin 4), F.blockSide = F'.blockSide → F.depth = F'.depth →
    0 < m →
    (∀ u : (Fin 4 → ℤ) × Fin 4, BondWithinRadius m u →
      V (y + siteOfCoords F.top u.1) u.2 = V' (y' + siteOfCoords F'.top u.1) u.2) →
    minimizingBondCoordinate a ρ (finiteCells (reflectedFrame F m))
        (siteOfCoords (reflectedFrame F m).depth o, i) (reflectedField m y V) =
      minimizingBondCoordinate a ρ (finiteCells (reflectedFrame F' m))
        (siteOfCoords (reflectedFrame F' m).depth o, i) (reflectedField m y' V')
end YangMills.Construction.ColdStepAtMirrorFrames
end
