import YangMills.Construction.ColdChainAtEveryLevel.SecondOrderOfTheTermsAtAFlatTop
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
open Classical in
def plaquetteCornerShare (Y : F.Cell) (p : F.Site 0 × Fin 4 × Fin 4) : ℝ :=
  ∑ x ∈ plaquetteCorners p, if enclosingCell x = Y then (1 / 4 : ℝ) else 0
open Classical in
def bondEndShare (Y : F.Cell) (j : ℕ) (c : F.Site (j + 1) × Fin 4) : ℝ :=
  (if enclosingCell c.1 = Y then (1 / 2 : ℝ) else 0) +
    (if enclosingCell (c.1 + unitStep (j + 1) c.2) = Y then (1 / 2 : ℝ) else 0)
def flatTopEnergy (a : ℝ) (S : Finset F.Cell) (D : ChainChart F)
    (v : F.Site F.top → Fin 4 → imaginaryQuaternions) : ℝ :=
  weightedQuadraticEnergy a S (fun _ => 1) (fun _ _ => 1) (referenceFieldChain S flatTopField) D v
def criticalChainFirstOrderStatement : Prop :=
  ∀ a : ℝ, 0 < a → ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L →
    ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
      IsOrthantRegular S m →
      ∀ v : F.Site F.top → Fin 4 → imaginaryQuaternions,
        ∃ D : ChainChart F, (∀ A : ChainChart F, flatTopEnergy a S D v ≤ flatTopEnergy a S A v) ∧
          ∀ Y : F.Cell, iteratedDeriv 2 (fun τ : ℝ => minimalCellShare a S Y (rotatedFlatField v τ)) 0 =
            weightedQuadraticEnergy a S (plaquetteCornerShare Y) (bondEndShare Y)
              (referenceFieldChain S flatTopField) D v
end YangMills.Construction.BlockAverages
end
