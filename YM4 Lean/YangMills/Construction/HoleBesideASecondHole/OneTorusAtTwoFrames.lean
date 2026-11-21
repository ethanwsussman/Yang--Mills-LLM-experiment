import YangMills.Construction.ClusterExpansionOfAStep.FieldsOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace FrameTransfer
open BlockAverages TorusFields
variable {F : BlockFrame}
def transferSite (F' : BlockFrame) (j' : ℕ) {j : ℕ} (x : F.Site j) : F'.Site j' :=
  siteOfCoords j' (siteCoords x)
def transferField (F' : BlockFrame) (j' : ℕ) {j : ℕ} (X : F.GaugeField j) : F'.GaugeField j' :=
  fun x i => X (transferSite F j x) i
def transferSet (F' : BlockFrame) (j' : ℕ) {j : ℕ} (X : Finset (F.Site j)) : Finset (F'.Site j') :=
  X.image (transferSite F' j')
def transferLumps (F' : BlockFrame) (j' : ℕ) {j : ℕ} (H : Finset (Finset (F.Site j))) :
    Finset (Finset (F'.Site j')) :=
  H.image (transferSet F' j')
def transferBond (F' : BlockFrame) (j' : ℕ) {j : ℕ} (c : F.Site j × Fin 4) : F'.Site j' × Fin 4 :=
  (transferSite F' j' c.1, c.2)
def transferBases (F' : BlockFrame) (b : F.Cell → F.Site F.depth) : F'.Cell → F'.Site F'.depth :=
  fun y => transferSite F' F'.depth (b (transferSite F F.top y))
def sitesOfTorus (F : BlockFrame) (j : ℕ) {m : ℕ} (X : Finset (TorusSite m)) : Finset (F.Site j) :=
  X.image fun x => siteOfCoords j fun i => ((x i).cast : ℤ)
end FrameTransfer
end YangMills.Construction
end
