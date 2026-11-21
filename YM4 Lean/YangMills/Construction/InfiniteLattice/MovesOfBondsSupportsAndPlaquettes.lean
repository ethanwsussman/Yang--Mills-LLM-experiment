import YangMills.Construction.InfiniteLattice.HyperoctahedralMotionsAndCubes
import YangMills.Construction.InfiniteLattice.IsometriesOfTheUnitLattice
import YangMills.Construction.InfiniteLattice.KernelsOfFiniteSetsOfBonds
import YangMills.Construction.Lattice.ActionOfLatticeIsometries
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
variable {a : ℝ}
theorem LatticeSymmetry.linkMap_mem_linkImage (r : LatticeSymmetry a) {L : Set (Link a)}
    {e : Link a} (he : e ∈ L) : r.linkMap e ∈ r.linkSetImage L :=
  mem_image_of_mem _ he
def LatticeSymmetry.transportFamily (r : LatticeSymmetry a) {S : Set (Link a)}
    (V : LinkVariables S) : LinkVariables (r.linkSetImage S) :=
  fun c =>
    have h : ∃ e, e ∈ S ∧ r.linkMap e = c.1 := c.2
    V ⟨h.choose, h.choose_spec.1⟩
end InfiniteLattice
namespace GibbsAtFixedSpacing
open YangMills.Construction.InfiniteLattice
def symmetryMaps (a : ℝ) : Set (AmbientSpace → AmbientSpace) :=
  {f | ∃ r : LatticeSymmetry a, r.toFun = f}
def SymmetriesAreLatticeMotions (a : ℝ) : Prop :=
  symmetryMaps a = affineHyperoctahedralMaps a ∧
    ∃ G : Subgroup (Equiv.Perm AmbientSpace), ∀ f : AmbientSpace → AmbientSpace,
      f ∈ symmetryMaps a ↔ ∃ g ∈ G, ⇑g = f
def SymmetriesTransportLinksAndSupports (a : ℝ) (ha : 0 < a) : Prop :=
  (∀ r : LatticeSymmetry a,
    Function.Bijective r.linkMap ∧
    (∀ e : Link a, r.linkMap e.opposite = (r.linkMap e).opposite) ∧
    (∀ (S : Set (Link a)) (h : HasNoOppositePairs S),
      ∃ h' : HasNoOppositePairs (r.linkSetImage S),
        (∀ (V : LinkVariables S) (e : S),
          r.transportFamily V ⟨r.linkMap e, r.linkMap_mem_linkImage e.2⟩ = V e) ∧
        (∀ (V : LinkVariables S) (U : GaugeField a),
          r.pullbackField (overwriteLinks h' (r.transportFamily V) U) =
            overwriteLinks h V (r.pullbackField U)) ∧
        ∀ (E : Type) (F : GaugeField a → E),
          IsIndependentOfLinks h F ↔ IsIndependentOfLinks h' (r.actOn F)) ∧
    ∀ (E : Type) (F : GaugeField a → E) (e : Link a),
      DependsOnLink ha F e ↔ DependsOnLink ha (r.actOn F) (r.linkMap e)) ∧
  ∀ v : LatticePoint a,
    (shift v).linkSetImage (positiveLinkSet a) = positiveLinkSet a ∧
    ∀ (E : Type) (F : GaugeField a → E),
      linkSupport ha ((shift v).actOn F) = shiftedLinks (linkSupport ha F) v
def SymmetriesTransportPlaquettes (a : ℝ) : Prop :=
  ∀ r : LatticeSymmetry a,
    (∀ p : ElementaryPlaquette a,
      (∃! q : ElementaryPlaquette a, q.cornerSet = r.pointMap '' p.cornerSet) ∧
      (r.plaquetteMap p).cornerSet = r.pointMap '' p.cornerSet) ∧
    Function.Bijective r.plaquetteMap ∧
    (∀ (r' : LatticeSymmetry a) (p : ElementaryPlaquette a),
      (r.comp r').plaquetteMap p = r.plaquetteMap (r'.plaquetteMap p)) ∧
    (∀ p : ElementaryPlaquette a,
      r.actOn (fun U : GaugeField a => faceEnergy U p) =
        fun U : GaugeField a => faceEnergy U (r.plaquetteMap p)) ∧
    (∀ p : ElementaryPlaquette a, (r.plaquetteMap p).center = r.toFun p.center) ∧
    ∀ L L' : Finset (Link a), HasNoOppositePairs (L : Set (Link a)) →
      (L' : Set (Link a)) = r.linkSetImage (L : Set (Link a)) →
      plaquettesTouching L' = r.plaquetteMap '' plaquettesTouching L
def SymmetriesTransportLinksSupportsAndPlaquettes : Prop :=
  ∀ (a : ℝ) (ha : 0 < a),
    SymmetriesAreLatticeMotions a ∧
    SymmetriesTransportLinksAndSupports a ha ∧
    SymmetriesTransportPlaquettes a
end GibbsAtFixedSpacing
end YangMills.Construction
