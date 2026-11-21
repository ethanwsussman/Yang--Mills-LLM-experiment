import YangMills.Construction.ColdStepAtMirrorFrames.MirrorOfAMovedTopForm
import YangMills.Construction.ResponseInTheExpansion.CoordinateOfASmallForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
namespace YangMills.Construction.WeightedResponses
def ReflectedCoordNearFlatLinearPart : Prop :=
  ∀ (a : ℝ) (L : ℕ) (c : ColdChainParameters), Odd L → c.Admissible a L → ∃ C r₀ s₁ : ℝ, 0 ≤ C ∧ 0 < r₀ ∧ 0 < s₁ ∧
    ∀ (F : BlockFrame) (Y : F.Cell) (R m : ℕ) (o : Fin 4 → ℤ) (i : Fin 4) (V : F.GaugeField F.top)
      (γ : F.Cell → UnitQuaternion) (B : F.Cell → Fin 4 → imaginaryQuaternions) (X : imaginaryQuaternions) (s : ℝ),
      IsBlockTorus L F → (∀ l, 4 * m + 5 < F.extent l) → 16 ≤ R → R ≤ m → o ∈ centredCube L →
      fineBondAt Y 0 o i ∈ chordBonds (finiteCells F) → ‖X‖ = 1 → 0 ≤ s → s ≤ s₁ →
      IsSmallCurvature c.σA (reflectedField m Y V) → IsSmallCurvature c.σA (reflectedField R Y V) →
      (∀ z l, ‖B z l‖ ≤ s) →
      (∀ (h : Fin 4 → ℤ) (l : Fin 4), BondWithinRadius R (h, l) →
        gaugeTransform γ V (Y + siteOfCoords F.top h) l = expUnit (B (Y + siteOfCoords F.top h) l)) →
      ‖((adjointMap (γ Y) (reflectedBondCoord a c.ρA m (fineBondAt Y 0 o i) V) -
          flatLinearPart a c.ρA X (fineBondAt Y 0 o i) B : imaginaryQuaternions) : ℍ[ℝ])‖ ≤
        C * (s ^ 2 + Real.exp (-(r₀ * (R : ℝ))))
end YangMills.Construction.WeightedResponses
end
