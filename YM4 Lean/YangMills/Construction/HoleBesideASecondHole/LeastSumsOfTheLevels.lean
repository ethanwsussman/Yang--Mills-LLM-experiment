import YangMills.Construction.HoleBesideASecondHole.CutsLumpsBasesAndContours
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ChainEnergies
open BlockAverages LumpContours
def minimalChainEnergiesStatement : Prop :=
  ∀ (F : BlockFrame) (a : ℝ), 0 ≤ a → Odd F.blockSide →
    (∀ (j : ℕ) (X : Finset (F.Site j)) (V : F.GaugeField j), j ≤ F.top →
      ∃ U : F.FieldChain, U j = V ∧ cutChainEnergy a j X U = cutEffectiveAction a j X V) ∧
    (∀ (j : ℕ) (X : Finset (F.Site j)) (U : F.FieldChain),
      cutEffectiveAction a j X (U j) ≤ cutChainEnergy a j X U) ∧
    (∀ (X : Finset F.Cell) (U : F.FieldChain) (V : F.GaugeField F.top),
      cutChainEnergy a F.top X (Function.update U F.top V) ≤
        cutChainEnergy a F.depth (cutBelow F.depth X) U + a * ∑ c ∈ cutBonds X, blockFit (U F.depth) V c) ∧
    (∀ (X : Finset F.Cell) (U : F.FieldChain),
      plainBlockEnergy a X (U F.depth) (U F.top) ≤ cutChainEnergy a F.top X U) ∧
    ∀ (X : Finset F.Cell) (W : F.GaugeField F.depth) (V : F.GaugeField F.top),
      cutEffectiveAction a F.top X V ≤ plainBlockEnergy a X W V
end YangMills.Construction.ChainEnergies
end
