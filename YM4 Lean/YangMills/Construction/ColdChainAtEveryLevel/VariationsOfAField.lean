import YangMills.Construction.ColdChainAtEveryLevel.NormsOfCoordinates
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BlockAverages
variable {F : BlockFrame}
def expRotatedField {j : ℕ} (v : F.Site j → Fin 4 → imaginaryQuaternions) (X : F.GaugeField j) : F.GaugeField j :=
  fun x i => expUnit (v x i) * X x i
def linkValueVariation {j : ℕ} (X : F.GaugeField j) (v : F.Site j → Fin 4 → imaginaryQuaternions) (x : F.Site j)
    (st : PathStep) : ℍ[ℝ] :=
  if st.2 then (v x st.1 : ℍ[ℝ])
  else - adjointAction (X (x - unitStep j st.1) st.1)⁻¹ (v (x - unitStep j st.1) st.1)
def pathHolonomyVariation {j : ℕ} (X : F.GaugeField j) (v : F.Site j → Fin 4 → imaginaryQuaternions) :
    F.Site j → List PathStep → ℍ[ℝ]
  | _, [] => 0
  | x, st :: r => linkValueVariation X v x st +
      adjointAction (linkValue X x st) (pathHolonomyVariation X v (x + stepDisplacement j st) r)
def variationCurl {j : ℕ} (X : F.GaugeField j) (v : F.Site j → Fin 4 → imaginaryQuaternions)
    (p : F.Site j × Fin 4 × Fin 4) : ℍ[ℝ] :=
  pathHolonomyVariation X v p.1 [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)]
def bondContourVariation {j : ℕ} (X : F.GaugeField j) (v : F.Site j → Fin 4 → imaginaryQuaternions)
    (c : F.Site (j + 1) × Fin 4) : ℍ[ℝ] :=
  (1 / (24 * (F.blockSide : ℝ) ^ 4)) • ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
    pathHolonomyVariation X v (refineSite c.1) (bondContour F.blockSide h π c.2)
def chartLineShift (w dw : F.Site F.depth → Fin 4 → imaginaryQuaternions) (τ : ℝ) :
    F.Site F.depth → Fin 4 → imaginaryQuaternions :=
  fun x i => w x i + τ • dw x i
def SupportedOnChords (S : Finset F.Cell) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) : Prop :=
  ∀ b, b ∉ chordBonds S → w b.1 b.2 = 0
def chordSqNorm (S : Finset F.Cell) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) : ℝ :=
  ∑ b ∈ chordBonds S, ‖w b.1 b.2‖ ^ 2
open Classical in
def chordSqNormOnPair (S : Finset F.Cell) (y y' : F.Cell) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) : ℝ :=
  ∑ b ∈ (chordBonds S).filter (fun b => enclosingCell b.1 = y ∨ enclosingCell b.1 = y'),
    ‖w b.1 b.2‖ ^ 2
end BlockAverages
end YangMills.Construction
end
