import YangMills.Construction.ColdChainAtEveryLevel.LevelsAndFields
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BlockAverages
variable {F : BlockFrame}
def IsAdmissibleAmbient (F : BlockFrame) : Prop := (∀ i, F.extent i = 0) ∨ ∀ i, 64 ≤ F.extent i
def IsOrthantRegular (S : Finset F.Cell) (m : ℕ) : Prop :=
  ∀ z : F.Cell, ∃ signs : Fin 4 → ℤ, (∀ i, signs i = 1 ∨ signs i = -1) ∧
    ∀ q ∈ S, cellSupDist q z ≤ m → ∀ h : Fin 4 → ℤ, (∀ i, 0 ≤ signs i * h i) →
      (∀ i, |h i| ≤ (m : ℤ)) → q + siteOfCoords F.top h ∈ S
def plaquetteDefect {j : ℕ} (X : F.GaugeField j) (p : F.Site j × Fin 4 × Fin 4) : ℝ :=
  ‖((plaquetteHolonomy X p : UnitQuaternion) : ℍ[ℝ]) - 1‖
def IsCold (S : Finset F.Cell) (j : ℕ) (s : ℝ) (X : F.GaugeField j) : Prop :=
  ∀ p ∈ innerPlaquettes S j, plaquetteDefect X p < s
open Classical in
def hotPlaquetteCount (S : Finset F.Cell) (j : ℕ) (σ : ℝ) (X : F.GaugeField j) : ℕ :=
  ((innerPlaquettes S j).filter fun p => σ ≤ plaquetteDefect X p).card
def AgreeOnBonds (S : Finset F.Cell) (j : ℕ) (X X' : F.GaugeField j) : Prop :=
  ∀ b ∈ innerBonds S j, X b.1 b.2 = X' b.1 b.2
def gaugeTransform {j : ℕ} (γ : F.Site j → UnitQuaternion) (X : F.GaugeField j) : F.GaugeField j :=
  fun x i => γ x * X x i * (γ (x + unitStep j i))⁻¹
def cellOffset (x : F.Site F.depth) : Fin 4 → ℤ :=
  fun i => ((x - cellCentre F.depth (enclosingCell x)) i).valMinAbs
def IsCrossingBond (b : F.Site F.depth × Fin 4) : Prop :=
  enclosingCell (b.1 + unitStep F.depth b.2) ≠ enclosingCell b.1
def IsAxialTreeBond (b : F.Site F.depth × Fin 4) : Prop :=
  ¬ IsCrossingBond b ∧ ∀ l, b.2 < l → cellOffset b.1 l = 0
open Classical in
def chordBonds (S : Finset F.Cell) : Finset (F.Site F.depth × Fin 4) :=
  (innerBonds S F.depth).filter fun b => ¬ IsAxialTreeBond b
open Classical in
def chartedField (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top) :
    F.GaugeField F.depth :=
  fun x i =>
    if IsCrossingBond (x, i) then expUnit (w x i) * V (enclosingCell x) i
    else if IsAxialTreeBond (x, i) then 1 else expUnit (w x i)
def IsMinimizingChart (a : ℝ) (S : Finset F.Cell) (V : F.GaugeField F.top) (ρ : ℝ)
    (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) : Prop :=
  (∀ b, b ∉ chordBonds S → w b.1 b.2 = 0) ∧ (∀ b ∈ chordBonds S, ‖w b.1 b.2‖ ≤ ρ) ∧
    ∀ W', blockEnergy a S F.depth (chartedField w V) V ≤ blockEnergy a S F.depth W' V
open Classical in
def minimizingCoordinates (a : ℝ) (S : Finset F.Cell) (V : F.GaugeField F.top) (ρ : ℝ) :
    F.Site F.depth → Fin 4 → imaginaryQuaternions :=
  if h : ∃ w, IsMinimizingChart a S V ρ w then h.choose else fun _ _ => 0
abbrev BlockFrame.FieldChain (F : BlockFrame) : Type := (j : ℕ) → F.GaugeField j
def chainAction (a : ℝ) (S : Finset F.Cell) (X : F.FieldChain) : ℝ :=
  wilsonAction S (X 0) + a * ∑ j ∈ Finset.range F.top, ∑ c ∈ innerBonds S (j + 1), blockFit (X j) (X (j + 1)) c
def IsMinimalChain (a : ℝ) (S : Finset F.Cell) (V : F.GaugeField F.top) (X : F.FieldChain) : Prop :=
  X F.top = V ∧ ∀ X' : F.FieldChain, X' F.top = V → chainAction a S X ≤ chainAction a S X'
open Classical in
def cellShare (a : ℝ) (S : Finset F.Cell) (Y : F.Cell) (X : F.FieldChain) : ℝ :=
    ∑ p ∈ innerPlaquettes S 0, (∑ x ∈ plaquetteCorners p, if enclosingCell x = Y then (1 / 4 : ℝ) else 0) *
        (1 - ((plaquetteHolonomy (X 0) p : UnitQuaternion) : ℍ[ℝ]).re) +
      a * ∑ j ∈ Finset.range F.top, ∑ c ∈ innerBonds S (j + 1),
        ((if enclosingCell c.1 = Y then (1 / 2 : ℝ) else 0) +
          (if enclosingCell (c.1 + unitStep (j + 1) c.2) = Y then (1 / 2 : ℝ) else 0)) *
        blockFit (X j) (X (j + 1)) c
open Classical in
def minimalCellShare (a : ℝ) (S : Finset F.Cell) (Y : F.Cell) (V : F.GaugeField F.top) : ℝ :=
  if h : ∃ X, IsMinimalChain a S V X then cellShare a S Y h.choose else 0
def bondSpread {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (σ : Fin k → ℝ) : F.Site F.top → Fin 4 → imaginaryQuaternions :=
  fun y i => ∑ l, if c l = (y, i) then σ l • X l else 0
def rotatedField (v : F.Site F.top → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top) :
    F.GaugeField F.top :=
  fun y i => expUnit (v y i) * V y i
def mixedBondDerivative {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ}
    (G : F.GaugeField F.top → E) (V : F.GaugeField F.top) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) : E :=
  iteratedFDeriv ℝ k (fun σ : Fin k → ℝ => G (rotatedField (bondSpread c X σ) V)) 0 (fun l => Pi.single l 1)
def IsBondAnalyticAt {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : F.GaugeField F.top → E) (V : F.GaugeField F.top) : Prop :=
  ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
    AnalyticAt ℝ (fun σ : Fin k → ℝ => G (rotatedField (bondSpread c X σ) V)) 0
def bondListDiameter {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) : ℕ :=
  Finset.univ.sup fun l : Fin k => Finset.univ.sup fun l' : Fin k => cellSupDist (c l).1 (c l').1
def bondListDistance {k : ℕ} (Y : F.Cell) (c : Fin k → F.Site F.top × Fin 4) : ℕ :=
  Finset.univ.sup fun l : Fin k => cellSupDist Y (c l).1
def AreUnitVectors {k : ℕ} (X : Fin k → imaginaryQuaternions) : Prop := ∀ l, ‖X l‖ = 1
end BlockAverages
end YangMills.Construction
end
