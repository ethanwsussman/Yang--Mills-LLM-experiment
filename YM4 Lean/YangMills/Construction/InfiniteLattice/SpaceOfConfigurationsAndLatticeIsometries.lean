import YangMills.Construction.InfiniteLattice.HyperoctahedralMotionsAndCubes
import YangMills.Construction.InfiniteLattice.IsometriesOfTheUnitLattice
import YangMills.Construction.InfiniteLattice.OneLatticeAtOneSpacing
import YangMills.Construction.Lattice.ActionOfLatticeIsometries
import YangMills.Construction.Lattice.SignedPermutationMatricesAndAffineHypercubicMaps
import Mathlib
set_option autoImplicit false
open Set
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def IsLatticeLinearIsometry (a : ℝ) (R : AmbientSpace →ₗ[ℝ] AmbientSpace) : Prop :=
  (∀ x y, TorusMetric.euclidNormVec (R x - R y) = TorusMetric.euclidNormVec (x - y)) ∧
    R '' (latticeSubgroup a : Set AmbientSpace) = latticeSubgroup a
def FieldSpace.SymmetryProperties : Prop :=
  ∀ a : ℝ, 0 < a →
    (CompactSpace (GaugeField a) ∧
      TopologicalSpace.MetrizableSpace (GaugeField a) ∧
      (inferInstance : MeasurableSpace (GaugeField a)) = linkSigma (univ : Set (Link a))) ∧
    (∀ r r' : LatticeSymmetry a,
      IsHomeomorph r.pullbackField ∧
      (r.comp r').pullbackField = r'.pullbackField ∘ r.pullbackField ∧
      (∀ F F' : GaugeField a → ℂ, IsBoundedObservable F → IsBoundedObservable F' →
        IsBoundedObservable (r.actOn F) ∧
        observableSupNorm (r.actOn F) = observableSupNorm F ∧
        (Continuous F → Continuous (r.actOn F)) ∧
        r.actOn (F * F') = r.actOn F * r.actOn F' ∧
        r.actOn (fun U => conj (F U)) = (fun U => conj (r.actOn F U)) ∧
        (r.comp r').actOn F = r.actOn (r'.actOn F)) ∧
      ∀ S : Set AmbientSpace,
        (fun F => r.actOn F) '' regionObservables a S =
          regionObservables a (r.imageSet S)) ∧
    (∀ (v : LatticePoint a) (S : Set AmbientSpace),
      (fun F => (shift v).actOn F) '' regionObservables a S =
        regionObservables a ((fun x => x + (v : AmbientSpace)) '' S)) ∧
    (∀ R : AmbientSpace →ₗ[ℝ] AmbientSpace,
      (IsLatticeLinearIsometry a R ↔
        LinearMap.toMatrix' R ∈ PeriodicLattice.signedPermMatrices) ∧
      (IsLatticeLinearIsometry a R ↔ ∃ w ∈ hyperoctahedralLinearGroup, ⇑w = ⇑R)) ∧
    (∀ f : AmbientSpace → AmbientSpace,
      (∃ r : LatticeSymmetry a, r.toFun = f) ↔ f ∈ affineHyperoctahedralMaps a) ∧
    (∃ G : Subgroup (Equiv.Perm AmbientSpace), ∀ f : AmbientSpace → AmbientSpace,
      (∃ r : LatticeSymmetry a, r.toFun = f) ↔ ∃ g ∈ G, ⇑g = f) ∧
    (∀ x y : LatticePoint a, (∃ b : Link a, b.initial = x ∧ b.terminal = y) ↔
      TorusMetric.euclidNormVec ((x : AmbientSpace) - y) = a) ∧
    (∀ b : Link a, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented) ∧
    (∀ r : LatticeSymmetry a, Function.Bijective r.linkMap ∧
      ∀ b : Link a, r.linkMap b.opposite = (r.linkMap b).opposite) ∧
    (∀ P : Set (LatticePoint a), (∃ p : ElementaryPlaquette a, p.cornerSet = P) ↔
      ∃ (z u u' : LatticePoint a) (ρ ρ' : Fin 4), ρ ≠ ρ' ∧
        (u = axisStep a ρ ∨ u = -axisStep a ρ) ∧ (u' = axisStep a ρ' ∨ u' = -axisStep a ρ') ∧
        P = {z, z + u, z + u + u', z + u'}) ∧
    (∀ p : ElementaryPlaquette a, p.cornerSet.ncard = 4) ∧
    Function.Injective (ElementaryPlaquette.cornerSet : ElementaryPlaquette a → Set (LatticePoint a)) ∧
    (∀ r : LatticeSymmetry a,
      (∀ p : ElementaryPlaquette a, (r.plaquetteMap p).cornerSet = r.pointMap '' p.cornerSet) ∧
      Function.Bijective r.plaquetteMap)
end YangMills.Construction.InfiniteLattice
