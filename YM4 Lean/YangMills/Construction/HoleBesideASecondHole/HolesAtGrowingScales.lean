import YangMills.Construction.HoleBesideASecondHole.CutsLumpsBasesAndContours
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Holes
open BlockAverages LumpContours
variable {F : BlockFrame}
def holeScale (J₀ i : ℕ) : ℕ := 16 * lumpRange * (40 * J₀) ^ i
def topScaleIndex (J₀ L : ℕ) : ℕ := Nat.findGreatest (fun i => holeScale J₀ i ^ 2 ≤ L) L
def holeRadius (J₀ i : ℕ) : ℕ := 4 * J₀ * holeScale J₀ i
def LumpsLinked (r : ℕ) (h : Finset (Finset (F.Site F.depth))) (l l' : Finset (F.Site F.depth)) : Prop :=
  l ∈ h ∧ l' ∈ h ∧ AreWithin r (lumpNeighbourhood l) (lumpNeighbourhood l')
open Classical in
def linkComponent (r : ℕ) (h : Finset (Finset (F.Site F.depth))) (l : Finset (F.Site F.depth)) :
    Finset (Finset (F.Site F.depth)) :=
  h.filter fun l' => Relation.ReflTransGen (LumpsLinked r h) l l'
open Classical in
def linkComponents (r : ℕ) (h : Finset (Finset (F.Site F.depth))) :
    Finset (Finset (Finset (F.Site F.depth))) :=
  h.image (linkComponent r h)
open Classical in
def componentsWithin (r : ℕ) (h k : Finset (Finset (F.Site F.depth))) :
    Finset (Finset (Finset (F.Site F.depth))) :=
  (linkComponents r h).filter fun k' => k' ⊆ k
def IsStableIndex (J₀ : ℕ) (h k : Finset (Finset (F.Site F.depth))) (i : ℕ) : Prop :=
  componentsWithin (holeScale J₀ i) h k = componentsWithin (holeScale J₀ (i + 1)) h k
open Classical in
def componentsNearCells (J₀ L : ℕ) (h : Finset (Finset (F.Site F.depth))) (Y : Finset F.Cell) :
    Finset (Finset (Finset (F.Site F.depth))) :=
  (linkComponents (holeScale J₀ (topScaleIndex J₀ L)) h).filter
    fun k => ∃ l ∈ k, ∃ y ∈ Y, l ⊆ sitesBelow F.depth y
@[ext] structure Hole (F : BlockFrame) where
  lumps : Finset (Finset (F.Site F.depth))
  centre : F.Site F.depth
  radius : ℕ
def Hole.innerBox (H : Hole F) : Finset (F.Site F.depth) := thicken H.radius {H.centre}
def Hole.outerBox (H : Hole F) : Finset (F.Site F.depth) := thicken (2 * H.radius) {H.centre}
def Hole.annulus (H : Hole F) : Finset (F.Site F.depth) := H.outerBox \ H.innerBox
def Hole.annulusEnergy (H : Hole F) (U₀ : F.GaugeField 0) : ℝ :=
  ∑ p ∈ cutPlaquettes (cutBelow 0 H.annulus), plaquetteEnergy U₀ p
open Classical in
def componentHoles (J₀ : ℕ) (h k : Finset (Finset (F.Site F.depth))) (i : ℕ)
    (o : Finset (Finset (F.Site F.depth)) → F.Site F.depth) : Finset (Hole F) :=
  (componentsWithin (holeScale J₀ i) h k).image fun k' => ⟨k', o k', holeRadius J₀ i⟩
open Classical in
def allHoles (J₀ L : ℕ) (h : Finset (Finset (F.Site F.depth))) (Y : Finset F.Cell)
    (idx : Finset (Finset (F.Site F.depth)) → ℕ) (o : Finset (Finset (F.Site F.depth)) → F.Site F.depth) :
    Finset (Hole F) :=
  (componentsNearCells J₀ L h Y).biUnion fun k => componentHoles J₀ h k (idx k) o
def holeSupport (𝓗 : Finset (Hole F)) : Finset (F.Site F.depth) := 𝓗.biUnion Hole.outerBox
end Holes
end YangMills.Construction
end
