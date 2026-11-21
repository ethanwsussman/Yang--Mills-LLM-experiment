import YangMills.Construction.ColdStepAtMirrorFrames.FlatChainsOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame}
def siteOffset {j : ℕ} (y x : F.Site j) : Fin 4 → ℤ := fun i => ((x - y) i).valMinAbs
def smoothCutoff (R : ℝ) (y z : F.Site F.depth) : ℝ :=
  min 1 (max 0 (2 - (siteSupDist z y : ℝ) / R))
def localAxialGauge (R : ℝ) (y : F.Site F.depth) (W : LevelForm F F.depth) : LevelForm F F.depth :=
  addGradient W fun z => smoothCutoff R y z * (- pathSum W y (axisPath (siteOffset y z) 1))
def fineBonds (F : BlockFrame) : Finset (F.Site F.depth × Fin 4) :=
  sitesOfCells (finiteCells F) F.depth ×ˢ Finset.univ
open Classical in
def blockFineSites (Y : F.Cell) : Finset (F.Site F.depth) :=
  (sitesOfCells (finiteCells F) F.depth).filter fun y => enclosingCell y = Y
structure IsAxialResponse (c : F.Site F.top × Fin 4) (B : FormChain F) (W : LevelForm F F.depth) : Prop where
  vanishes_on_tree : ∀ b : F.Site F.depth × Fin 4, IsAxialTreeBond b → W b.1 b.2 = 0
  curl_eq : ∀ (x : F.Site F.depth) (e : Fin 4 × Fin 4), e ∈ orientedPlanes →
    plaquetteCurl W x e.1 e.2 = plaquetteCurl (B F.depth) x e.1 e.2
  contour_mean : ∀ (y : F.Cell) (i : Fin 4),
    (1 / (24 * (F.blockSide : ℝ) ^ 4)) * ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
      pathSum W (refineSite y) (bondContour F.blockSide h π i) =
        topBondIndicator c y i + chainMisfit B F.depth y i
end ColdStepAtMirrorFrames
end YangMills.Construction
end
