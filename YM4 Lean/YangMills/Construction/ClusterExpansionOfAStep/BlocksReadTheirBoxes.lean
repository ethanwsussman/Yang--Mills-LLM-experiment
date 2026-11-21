import YangMills.Construction.ClusterExpansionOfAStep.BasesAtABlock
import YangMills.Construction.ClusterExpansionOfAStep.EffectiveDensityOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusLumps
open BlockAverages LumpContours TorusFields
def BlockDataIsLocal : Prop :=
  ∀ (ℓ : StepParameters), ℓ.Admissible → ∀ (n n' : ℕ) [NeZero n] [NeZero n'], 16 ≤ n → 16 ≤ n' →
    ∀ (W : (stepBlockFrame ℓ.side n).GaugeField 0) (W' : (stepBlockFrame ℓ.side n').GaugeField 0)
      (y : (stepBlockFrame ℓ.side n).Cell) (y' : (stepBlockFrame ℓ.side n').Cell),
      (∀ (u : Fin 4 → ℤ) (i : Fin 4), OffsetInBox (3 * ℓ.side) u → OffsetInBox (3 * ℓ.side) (u + Pi.single i 1) →
        W (siteAtOffset y u) i = W' (siteAtOffset y' u) i) →
      (∀ (S : Finset ((stepBlockFrame ℓ.side n).Site 0)) (S' : Finset ((stepBlockFrame ℓ.side n').Site 0)),
        (∀ u, OffsetInBox (3 * ℓ.side) u → (siteAtOffset y u ∈ S ↔ siteAtOffset y' u ∈ S')) →
        (baseSitesAt ℓ.baseDepth (hotLumps ℓ.grid ℓ.threshold S W) y).card =
            (baseSitesAt ℓ.baseDepth (hotLumps ℓ.grid ℓ.threshold S' W') y').card ∧
        ∀ z ∈ centredCube ℓ.side, siteAtOffset y z ∈ baseSitesAt ℓ.baseDepth (hotLumps ℓ.grid ℓ.threshold S W) y ↔
          siteAtOffset y' z ∈ baseSitesAt ℓ.baseDepth (hotLumps ℓ.grid ℓ.threshold S' W') y') ∧
      ∀ (V : (stepBlockFrame ℓ.side n).GaugeField 1) (V' : (stepBlockFrame ℓ.side n').GaugeField 1)
        (z : Fin 4 → ℤ) (i : Fin 4), z ∈ centredCube ℓ.side →
        V y i = V' y' i → bondCoordinate 1 V W (siteAtOffset y z, i) = bondCoordinate 1 V' W' (siteAtOffset y' z, i)
end YangMills.Construction.TorusLumps
end
