import YangMills.Construction.ColdStepAtMirrorFrames.FixedVariablesOfTheStep
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame}
abbrev LevelForm (F : BlockFrame) (j : ℕ) : Type := F.Site j → Fin 4 → ℝ
abbrev FormChain (F : BlockFrame) : Type := (j : ℕ) → LevelForm F j
def plaquetteCurl {j : ℕ} (B : LevelForm F j) (x : F.Site j) (μ ν : Fin 4) : ℝ :=
  B x μ + B (x + unitStep j μ) ν - B (x + unitStep j ν) μ - B x ν
def lineAverage {j : ℕ} (B : LevelForm F j) : LevelForm F (j + 1) := fun y i =>
  (1 / (F.blockSide : ℝ) ^ 4) * ∑ h ∈ centredCube F.blockSide, ∑ l ∈ Finset.range F.blockSide,
    B (refineSite y + siteOfCoords j h + siteOfCoords j (Pi.single i (l : ℤ))) i
def blockAverage {j : ℕ} (φ : F.Site j → ℝ) : F.Site (j + 1) → ℝ := fun y =>
  (1 / (F.blockSide : ℝ) ^ 4) * ∑ h ∈ centredCube F.blockSide, φ (refineSite y + siteOfCoords j h)
def chainMisfit (B : FormChain F) (j : ℕ) : LevelForm F (j + 1) := fun y i =>
  lineAverage (B j) y i - B (j + 1) y i
def orientedPlanes : Finset (Fin 4 × Fin 4) := Finset.univ.filter fun e => e.1 < e.2
def chainEnergyPolar (a : ℝ) (B D : FormChain F) : ℝ :=
  (∑ x ∈ sitesOfCells (finiteCells F) 0, ∑ e ∈ orientedPlanes,
      plaquetteCurl (B 0) x e.1 e.2 * plaquetteCurl (D 0) x e.1 e.2) +
    a * ∑ j ∈ Finset.range F.top, ∑ y ∈ sitesOfCells (finiteCells F) (j + 1), ∑ i : Fin 4,
      chainMisfit B j y i * chainMisfit D j y i
def topBondIndicator (c : F.Site F.top × Fin 4) : LevelForm F F.top := fun y i =>
  if (y, i) = c then 1 else 0
structure IsFlatChain (a : ℝ) (c : F.Site F.top × Fin 4) (B : FormChain F) : Prop where
  top_eq : B F.top = topBondIndicator c
  stationary : ∀ D : FormChain F, D F.top = 0 → chainEnergyPolar a B D = 0
def cellCoordinate {j : ℕ} (x : F.Site j) (i : Fin 4) : ℝ :=
  (siteCoords x i : ℝ) / (F.blockSide : ℝ) ^ (F.top - j)
def distToMultiples (n u : ℝ) : ℝ := |u - n * round (u / n)|
def torusSupDist {j : ℕ} (x : F.Site j) (z : F.Cell) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i =>
    distToMultiples (F.extent i) (cellCoordinate x i - siteCoords z i)
open Classical in
def chainEnergyOnCells (a : ℝ) (B : FormChain F) (X : Set F.Cell) : ℝ :=
  (∑ x ∈ (sitesOfCells (finiteCells F) 0).filter (fun x => enclosingCell x ∈ X), ∑ e ∈ orientedPlanes,
      plaquetteCurl (B 0) x e.1 e.2 ^ 2) +
    a * ∑ j ∈ Finset.range F.top,
      ∑ y ∈ (sitesOfCells (finiteCells F) (j + 1)).filter (fun y => enclosingCell y ∈ X),
        ∑ i : Fin 4, chainMisfit B j y i ^ 2
def cellBall (z : F.Cell) (r : ℕ) : Set F.Cell := {y | cellSupDist y z ≤ r}
def depthSite {j : ℕ} (x : F.Site j) : F.Site F.depth :=
  if j ≤ F.depth then ancestorSite F.depth x
  else siteOfCoords F.depth fun i => (F.blockSide : ℤ) * siteCoords x i
open Classical in
def chainEnergyOnSites (a : ℝ) (B : FormChain F) (X : Set (F.Site F.depth)) : ℝ :=
  (∑ x ∈ (sitesOfCells (finiteCells F) 0).filter (fun x => depthSite x ∈ X), ∑ e ∈ orientedPlanes,
      plaquetteCurl (B 0) x e.1 e.2 ^ 2) +
    a * ∑ j ∈ Finset.range F.top,
      ∑ y ∈ (sitesOfCells (finiteCells F) (j + 1)).filter (fun y => depthSite y ∈ X),
        ∑ i : Fin 4, chainMisfit B j y i ^ 2
def depthBall (z : F.Site F.depth) (r : ℕ) : Set (F.Site F.depth) := {y | siteSupDist y z ≤ r}
def pathSum {j : ℕ} (B : LevelForm F j) : F.Site j → List PathStep → ℝ
  | _, [] => 0
  | x, st :: r => (if st.2 then B x st.1 else - B (x - unitStep j st.1) st.1) +
      pathSum B (x + stepDisplacement j st) r
def addGradient {j : ℕ} (B : LevelForm F j) (φ : F.Site j → ℝ) : LevelForm F j :=
  fun x i => B x i + (φ (x + unitStep j i) - φ x)
def cellAverage (φ : F.Site 0 → ℝ) (z : F.Cell) : ℝ :=
  (1 / ((F.blockSide : ℝ) ^ F.top) ^ 4) * ∑ h ∈ centredCube (F.blockSide ^ F.top),
    φ (cellCentre 0 z + siteOfCoords 0 h)
def iteratedLineAverage (B : LevelForm F 0) : (j : ℕ) → LevelForm F j
  | 0 => B
  | j + 1 => lineAverage (iteratedLineAverage B j)
end ColdStepAtMirrorFrames
end YangMills.Construction
end
