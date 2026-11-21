import YangMills.Construction.HoleBesideASecondHole.CutsLumpsBasesAndContours
import YangMills.Construction.HoleBesideASecondHole.MeanOfAProductOfGroupVariables
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.LumpContours
open YangMills.Construction.BlockAverages YangMills.Construction.GroupMeans
variable {F : BlockFrame}
def bottomModifiedField {t : ℕ} (G : Finset (F.Site t)) (U : F.FieldChain) (U₀ : F.GaugeField 0) :
    (i : ℕ) → F.GaugeField i
  | 0 => U₀
  | i + 1 => by
    classical exact fun y d =>
      if y ∈ cutBelow (i + 1) G ∧ y + unitStep (i + 1) d ∈ cutBelow (i + 1) G then U (i + 1) y d
      else polarPart (contourAverage (bottomModifiedField G U U₀ i) (y, d))
def BottomModifiedChainIdentity : Prop :=
  ∀ (F : BlockFrame) (t : ℕ), t ≤ F.top → Odd F.blockSide → ∀ (G : Finset (F.Site t)) (U : F.FieldChain)
    (U₀ : F.GaugeField 0),
    (∀ b ∈ cutBonds (cutBelow 0 G), U₀ b.1 b.2 = U 0 b.1 b.2) →
    (∀ i ≤ t, ∀ b ∈ cutBonds (cutBelow i G), bottomModifiedField G U U₀ i b.1 b.2 = U i b.1 b.2) ∧
    (∀ i < t, ∀ c : F.Site (i + 1) × Fin 4,
      blockFit (bottomModifiedField G U U₀ i) (bottomModifiedField G U U₀ (i + 1)) c =
        if c ∈ cutBonds (cutBelow (i + 1) G) then blockFit (U i) (U (i + 1)) c else 0) ∧
    ∀ (a : ℝ) (Q : Finset (F.Site t)), G ⊆ Q →
      cutChainEnergy a t Q (bottomModifiedField G U U₀) =
        ∑ p ∈ cutPlaquettes (cutBelow 0 Q), plaquetteEnergy U₀ p +
          a * ∑ i ∈ Finset.range t, ∑ c ∈ cutBonds (cutBelow (i + 1) G), blockFit (U i) (U (i + 1)) c
end YangMills.Construction.LumpContours
end
