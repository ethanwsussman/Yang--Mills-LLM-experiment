import YangMills.Construction.ColdChainAtEveryLevel.PropertiesOfTheColdChainForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def torusDecayFactor (L : ℕ) (δ x : ℝ) : ℝ :=
  max 1 ((x / (L : ℝ) ^ (1 / 640 : ℝ)) ^ 16000) * Real.exp (δ * x)
def IsLargeCubicTorus (F : BlockFrame) : Prop := ∃ n : ℕ, 64 ≤ n ∧ ∀ i, F.extent i = n
def HasTorusDerivativeDecay (a δ ρ s : ℝ) (N : ℕ → ℝ) (S : Finset F.Cell) (V : F.GaugeField F.top) : Prop :=
  (∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), 2 ≤ k → AreUnitVectors X →
    |mixedBondDerivative (minimalAction a S F.top) V c X| ≤
      N k / torusDecayFactor F.blockSide δ (bondListDiameter c)) ∧
  (∀ (Y : F.Cell) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ k →
    AreUnitVectors X →
    |mixedBondDerivative (minimalCellShare a S Y) V c X| ≤
      N k / torusDecayFactor F.blockSide δ (max (bondListDiameter c) (bondListDistance Y c))) ∧
  (∀ (Y : F.Cell) (c : Fin 1 → F.Site F.top × Fin 4) (X : Fin 1 → imaginaryQuaternions), AreUnitVectors X →
    |mixedBondDerivative (minimalCellShare a S Y) V c X| ≤
      N 1 * s / torusDecayFactor F.blockSide δ (bondListDistance Y c)) ∧
  ∀ b ∈ chordBonds S, ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ k →
    AreUnitVectors X → ‖mixedBondDerivative (minimizingBondCoordinate a ρ S b) V c X‖ ≤
      N k / torusDecayFactor F.blockSide δ (max (bondListDiameter c) (bondListDistance (enclosingCell b.1) c))
def HasTorusComparison (a δ ρ s : ℝ) (N : ℕ → ℝ) {F' : BlockFrame} (S : Finset F.Cell)
    (V : F.GaugeField F.top) (S' : Finset F'.Cell) (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell)
    (r : ℕ) : Prop :=
  (∀ (k : ℕ) (h : Fin k → (Fin 4 → ℤ) × Fin 4) (X : Fin k → imaginaryQuaternions),
    (∀ l, BondWithinRadius r (h l)) → AreUnitVectors X →
    |mixedBondDerivative (minimalCellShare a S Y) V (offsetBonds Y h) X -
        mixedBondDerivative (minimalCellShare a S' Y') V' (offsetBonds Y' h) X| ≤
      N k / torusDecayFactor F.blockSide δ r) ∧
  ∀ (h o : Fin 4 → ℤ) (i : Fin 4), o ∈ centredCube F.blockSide → fineBondAt Y h o i ∈ chordBonds S →
    WithinRadius r h → cellSupDist Y (enclosingCell (fineBondAt Y h o i).1) ≤ r →
    cellSupDist Y (enclosingCell ((fineBondAt Y h o i).1 + unitStep F.depth i)) ≤ r →
    ‖(minimizingBondCoordinate a ρ S (fineBondAt Y h o i) V : ℍ[ℝ]) -
        minimizingBondCoordinate a ρ S' (fineBondAt Y' h o i) V'‖ ≤
      N 0 * s / torusDecayFactor F.blockSide δ ((r : ℝ) - cellSupDist Y (enclosingCell (fineBondAt Y h o i).1))
end YangMills.Construction.BlockAverages
end
