import YangMills.Construction.HoleBesideASecondHole.CutsLumpsBasesAndContours
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.LumpContours
open YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def ChainCoercivity : Prop :=
  ∃ cK : ℝ, 0 < cK ∧ cK ≤ 1 ∧ ∃ L₀ : ℕ, ∀ (a : ℝ) (L : ℕ), 1 ≤ a → Odd L → L₀ ≤ L →
    ∀ (F : BlockFrame), F.blockSide = L → IsAdmissibleAmbient F → ∀ (j : ℕ), j ≤ F.top →
      (∀ (p : F.Site j × Fin 4 × Fin 4) (U : F.FieldChain), p.2.1 < p.2.2 →
        cK * min (plaquetteDefect (U j) p ^ 2) ((L : ℝ) ^ (-4 : ℤ)) ≤
          cutChainEnergy a j (plaquetteCorners p) U) ∧
      ∀ (X : Finset (F.Site j)) (V : F.GaugeField j),
        cK * ∑ p ∈ cutPlaquettes X, min (plaquetteDefect V p ^ 2) ((L : ℝ) ^ (-4 : ℤ)) ≤
          cutEffectiveAction a j X V
end YangMills.Construction.LumpContours
end
