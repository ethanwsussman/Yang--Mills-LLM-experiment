import YangMills.Construction.HoleBesideASecondHole.TermsOfAChainAtACell
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.CellTerms
open BlockAverages
def referenceLocalityStatement : Prop :=
  ∃ (c : ℝ) (L₁ : ℕ), 0 < c ∧ ∀ (F : BlockFrame) (m : ℕ) (S S' C : Finset F.Cell) (s : ℝ)
    (V V' : F.GaugeField F.top),
    Odd F.blockSide → L₁ ≤ F.blockSide → IsAdmissibleAmbient F → 1024 ≤ m → IsOrthantRegular S m →
    IsOrthantRegular S' m →
    0 < s → s ≤ c → IsCold S F.top s V → IsCold S' F.top s V' → C ⊆ S →
    (∀ z ∈ C, AgreeNear 100 S S' V V' z) →
    (∀ z ∈ C, ∀ y, cellSupDist z y ≤ 36 → closedOrthant S y = closedOrthant S' y) ∧
    ∃ γ : F.Site 0 → UnitQuaternion, (∀ y ∈ C, γ (cellCentre 0 y) = 1) ∧
      ∀ j, j < F.top → ∀ e : F.Site j × Fin 4, BondWithin C e →
        referenceFieldChain S' V' j e.1 e.2 =
          gaugeTransform (fun x => γ (baseSite x)) (referenceFieldChain S V j) e.1 e.2
end YangMills.Construction.CellTerms
end
