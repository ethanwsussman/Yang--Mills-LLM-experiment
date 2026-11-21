import YangMills.Construction.ColdChainAtEveryLevel.PropertiesOfTheColdChainForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EnergySymmetry
open YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def symmetryInverse (g : CubicSymmetry) : CubicSymmetry :=
  ⟨g.perm⁻¹, fun i => g.sign (g.perm⁻¹ i), fun i => - (g.sign (g.perm⁻¹ i) * g.shift (g.perm⁻¹ i))⟩
def transportField (g : CubicSymmetry) {j : ℕ} (X : F.GaugeField j) : F.GaugeField j :=
  fun y i => linkValue X ((symmetryInverse g).actSite j y) (g.perm i, decide (g.sign i = 1))
def BlockEnergySymmetric : Prop :=
  ∀ (F : BlockFrame) (a : ℝ) (S S' : Finset F.Cell) (V V' : F.GaugeField F.top) (g : CubicSymmetry), Odd F.blockSide →
    g.IsSymmetry F →
    (∀ z, z ∈ S ↔ g.actSite F.top z ∈ S') → g.TransportsField V V' →
    (∀ W : F.GaugeField F.depth, blockEnergy a S' F.depth (transportField g W) V' = blockEnergy a S F.depth W V) ∧
    (∀ W' : F.GaugeField F.depth, ∃ W : F.GaugeField F.depth, transportField g W = W') ∧
    ∀ (W : F.GaugeField F.depth) (x : F.Site F.depth) (k : Fin 4),
      linkValue (transportField g W) (g.actSite F.depth x) (g.actStep k) = W x k
end YangMills.Construction.EnergySymmetry
end
