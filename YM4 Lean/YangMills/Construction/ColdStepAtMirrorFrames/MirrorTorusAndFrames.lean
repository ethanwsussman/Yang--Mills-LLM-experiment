import YangMills.Construction.ColdChainAtEveryLevel.PropertiesOfTheColdChainForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame}
open Classical in
def finiteCells (F : BlockFrame) : Finset F.Cell :=
  if _h : Finite F.Cell then @Finset.univ _ (Fintype.ofFinite _) else ∅
def reflectCoord (m : ℕ) (c : ℤ) : ℤ :=
  if |c| ≤ (m : ℤ) then c else if 0 < c then 2 * (m : ℤ) - c else -(2 * (m : ℤ)) - c
def reflectedFrame (F : BlockFrame) (m : ℕ) : BlockFrame := ⟨F.blockSide, F.depth, fun _ => 4 * m⟩
def reflectedField (m : ℕ) (y : F.Cell) (V : F.GaugeField F.top) :
    (reflectedFrame F m).GaugeField (reflectedFrame F m).top :=
  fun z i =>
    let c : Fin 4 → ℤ := fun l => (z l).valMinAbs
    let e : Fin 4 → ℤ := fun l => reflectCoord m (c l)
    let e' : Fin 4 → ℤ := fun l => reflectCoord m (c l + (Pi.single i 1 : Fin 4 → ℤ) l)
    if e' i = e i + 1 then V (y + siteOfCoords F.top e) i else (V (y + siteOfCoords F.top e') i)⁻¹
def reflectedBond (m : ℕ) (b : F.Site F.depth × Fin 4) :
    (reflectedFrame F m).Site (reflectedFrame F m).depth × Fin 4 :=
  (siteOfCoords (reflectedFrame F m).depth (cellOffset b.1), b.2)
def reflectedBondCoord (a ρ : ℝ) (m : ℕ) (b : F.Site F.depth × Fin 4) (V : F.GaugeField F.top) :
    imaginaryQuaternions :=
  minimizingBondCoordinate a ρ (finiteCells (reflectedFrame F m)) (reflectedBond m b)
    (reflectedField m (enclosingCell b.1) V)
open Classical in
def bondFrameCoord (a ρ : ℝ) (m : ℕ) (b : F.Site F.depth × Fin 4) (V : F.GaugeField F.top) :
    imaginaryQuaternions :=
  if ∀ i, 4 * m + 5 < F.extent i then reflectedBondCoord a ρ m b V
  else minimizingBondCoordinate a ρ (finiteCells F) b V
end ColdStepAtMirrorFrames
end YangMills.Construction
end
