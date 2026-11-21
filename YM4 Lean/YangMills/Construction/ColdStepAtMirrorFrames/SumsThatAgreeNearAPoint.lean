import YangMills.Construction.ColdStepAtMirrorFrames.MirrorTorusAndFrames
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames
def DecayingSumsClose : Prop :=
  ∀ β : ℝ, 0 < β → ∃ M : ℝ, 0 < M ∧
    (∀ (F : BlockFrame) (z : F.Cell), (∀ i, 2 ≤ F.extent i) →
      ∑ Y ∈ finiteCells F, Real.exp (-(β * cellSupDist Y z)) ≤ M) ∧
    ∀ (F F' : BlockFrame) (G : F.Cell → ℝ) (G' : F'.Cell → ℝ) (z : F.Cell) (z' : F'.Cell) (R : ℕ) (T A : ℝ),
      (∀ i, 2 ≤ F.extent i) → (∀ i, 2 ≤ F'.extent i) → (∀ i, 2 * R < F.extent i) →
      (∀ i, 2 * R < F'.extent i) →
      0 ≤ T → 0 ≤ A →
      (∀ h : Fin 4 → ℤ, (∀ i, |h i| ≤ (R : ℤ)) →
        |G (z + siteOfCoords F.top h) - G' (z' + siteOfCoords F'.top h)| ≤
          T * Real.exp (-(β * cellSupDist (z + siteOfCoords F.top h) z))) →
      (∀ Y, R < cellSupDist Y z → |G Y| ≤ A * Real.exp (-(β * cellSupDist Y z))) →
      (∀ Y, R < cellSupDist Y z' → |G' Y| ≤ A * Real.exp (-(β * cellSupDist Y z'))) →
      |∑ Y ∈ finiteCells F, G Y - ∑ Y ∈ finiteCells F', G' Y| ≤ (T + 2 * A) * M
end ColdStepAtMirrorFrames
end YangMills.Construction
end
