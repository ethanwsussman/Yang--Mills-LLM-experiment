import YangMills.Construction.ColdChainAtEveryLevel.PatchesAndTheGaugeMap
import YangMills.Construction.ColdChainAtEveryLevel.PropertiesOfTheColdChainForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
open Classical in
def plaquetteCellShare (Y : F.Cell) (p : F.Site 0 × Fin 4 × Fin 4) : ℝ :=
  ∑ x ∈ plaquetteCorners p, if enclosingCell x = Y then (1 / 4 : ℝ) else 0
open Classical in
def bondCellShare {j : ℕ} (Y : F.Cell) (c : F.Site j × Fin 4) : ℝ :=
  (if enclosingCell c.1 = Y then (1 / 2 : ℝ) else 0) +
    (if enclosingCell (c.1 + unitStep j c.2) = Y then (1 / 2 : ℝ) else 0)
def topDirectionDefect (R : F.FieldChain) (U : ChainChart F) (v : F.Site F.top → Fin 4 → imaginaryQuaternions)
    (c : F.Site F.top × Fin 4) : ℍ[ℝ] :=
  (v c.1 c.2 : ℍ[ℝ]) - linearPart R U F.top c.1 c.2
def responseCellShare (a : ℝ) (S : Finset F.Cell) (Y : F.Cell) (R : F.FieldChain) (U : ChainChart F)
    (v : F.Site F.top → Fin 4 → imaginaryQuaternions) : ℝ :=
  ∑ p ∈ innerPlaquettes S 0, plaquetteCellShare Y p * ‖linearizedCurl (R 0) U.fine p‖ ^ 2 +
    a * ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ innerBonds S (j + 1),
      bondCellShare Y c * ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖ ^ 2 +
    a * ∑ c ∈ innerBonds S F.top, bondCellShare Y c * ‖topDirectionDefect R U v c‖ ^ 2
def responseBilinear (a : ℝ) (S : Finset F.Cell) (R : F.FieldChain) (U A : ChainChart F) : ℝ :=
  ∑ p ∈ innerPlaquettes S 0, inner ℝ (linearizedCurl (R 0) U.fine p) (linearizedCurl (R 0) A.fine p) +
    a * ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ innerBonds S (j + 1),
      inner ℝ (U.coarse j c.1 c.2 : ℍ[ℝ]) (A.coarse j c.1 c.2 : ℍ[ℝ]) +
    a * ∑ c ∈ innerBonds S F.top, inner ℝ (linearPart R U F.top c.1 c.2) (linearPart R A F.top c.1 c.2)
def responseLinear (a : ℝ) (S : Finset F.Cell) (R : F.FieldChain) (v : F.Site F.top → Fin 4 → imaginaryQuaternions)
    (A : ChainChart F) : ℝ :=
  a * ∑ c ∈ innerBonds S F.top, inner ℝ (v c.1 c.2 : ℍ[ℝ]) (linearPart R A F.top c.1 c.2)
def IsFlatTopResponse (a : ℝ) (S : Finset F.Cell) (v : F.Site F.top → Fin 4 → imaginaryQuaternions)
    (U : ChainChart F) : Prop :=
  GaugeMap.InGaugeSlice S flatTopField (referenceFieldChain S flatTopField 0) U.fine ∧
    ∀ A : ChainChart F, GaugeMap.InGaugeSlice S flatTopField (referenceFieldChain S flatTopField 0) A.fine →
      responseBilinear a S (referenceFieldChain S flatTopField) U A =
        responseLinear a S (referenceFieldChain S flatTopField) v A
end YangMills.Construction.BlockAverages
end
