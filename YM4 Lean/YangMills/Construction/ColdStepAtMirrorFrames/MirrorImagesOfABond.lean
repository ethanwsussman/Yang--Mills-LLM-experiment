import YangMills.Construction.ColdStepAtMirrorFrames.MirrorOfAMovedTopForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
def reflectedImagesOfBond : Prop :=
  ∀ (F : BlockFrame) (m : ℕ) (y : F.Cell) (c : F.Cell × Fin 4), 2 ≤ m → (∀ i, 2 * m + 2 < F.extent i) →
    ∃ J : Finset ((reflectedFrame F m).Cell × Fin 4), J.card ≤ 16 ∧
      (∀ (V : F.GaugeField F.top) (X : imaginaryQuaternions) (z : (reflectedFrame F m).Cell) (i : Fin 4), (z, i) ∉ J →
        reflectedDirection m y V c X z i = 0) ∧
      (∀ (V : F.GaugeField F.top) (X : imaginaryQuaternions), ∀ p ∈ J, ‖reflectedDirection m y V c X p.1 p.2‖ = ‖X‖) ∧
      (∀ u : (Fin 4 → ℤ) × Fin 4, BondWithinRadius m u → c = (y + siteOfCoords F.top u.1, u.2) →
        (siteOfCoords (reflectedFrame F m).top u.1, u.2) ∈ J ∧
        (∀ (V : F.GaugeField F.top) (X : imaginaryQuaternions),
          reflectedDirection m y V c X (siteOfCoords (reflectedFrame F m).top u.1) u.2 = X) ∧
        ∀ p ∈ J, p ≠ (siteOfCoords (reflectedFrame F m).top u.1, u.2) → m ≤ cellSupDist 0 p.1) ∧
      ((∀ u : (Fin 4 → ℤ) × Fin 4, BondWithinRadius m u → c ≠ (y + siteOfCoords F.top u.1, u.2)) →
        J = ∅ ∧ m ≤ cellSupDist y c.1)
end ColdStepAtMirrorFrames
end YangMills.Construction
end
