import YangMills.Construction.HoleBesideASecondHole.CutsLumpsBasesAndContours
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.LumpContours
open YangMills.Construction.BlockAverages
def CornerDefectBound : Prop :=
  ∃ cK : ℝ, 0 < cK ∧ cK ≤ 1 ∧ ∃ L₀ : ℕ, ∀ (a : ℝ) (L : ℕ), 1 ≤ a → Odd L → L₀ ≤ L →
    ∀ (F : BlockFrame), F.blockSide = L → IsAdmissibleAmbient F → ∀ (j : ℕ), j ≤ F.top →
      (∀ (p : F.Site j × Fin 4 × Fin 4) (U : F.FieldChain), p.2.1 < p.2.2 →
        cutChainEnergy a j (plaquetteCorners p) U < cK * (L : ℝ) ^ (-4 : ℤ) →
        plaquetteDefect (U j) p ^ 2 ≤ cutChainEnergy a j (plaquetteCorners p) U / cK) ∧
      (∀ (X : Finset (F.Site j)) (P : Finset (F.Site j × Fin 4 × Fin 4)) (U : F.FieldChain),
        P ⊆ cutPlaquettes X →
          ∑ p ∈ P, cutChainEnergy a j (plaquetteCorners p) U ≤ 24 * cutChainEnergy a j X U) ∧
      ∀ (X : Finset (F.Site j)) (P : Finset (F.Site j × Fin 4 × Fin 4)) (U : F.FieldChain),
        P ⊆ cutPlaquettes X →
          (∀ p ∈ P, cutChainEnergy a j (plaquetteCorners p) U < cK * (L : ℝ) ^ (-4 : ℤ)) →
          ∑ p ∈ P, plaquetteDefect (U j) p ^ 2 ≤ (24 / cK) * cutChainEnergy a j X U
end YangMills.Construction.LumpContours
end
