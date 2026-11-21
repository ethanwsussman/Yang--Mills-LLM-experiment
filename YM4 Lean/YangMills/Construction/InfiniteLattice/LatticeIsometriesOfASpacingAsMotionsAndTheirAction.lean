import YangMills.Construction.InfiniteLattice.ActionOfTheLatticeIsometriesOnObservables
import YangMills.Construction.InfiniteLattice.HyperoctahedralMotionsAndCubes
import YangMills.Construction.InfiniteLattice.StatesFunctionsOfTheBondsAndErgodicity
import YangMills.Construction.Lattice.ActionOfLatticeIsometries
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
namespace SymmetriesAsMotions
variable {a : ℝ}
def IsAffineHyperoctahedral (r : LatticeSymmetry a) : Prop :=
  (∃ R ∈ hyperoctahedralLinearGroup, ∃ v : LatticePoint a,
    ∀ x : AmbientSpace, r.toFun x = R x + (v : AmbientSpace)) ∧
    ∀ R ∈ hyperoctahedralLinearGroup, ∀ v : LatticePoint a,
      ∃ t : LatticeSymmetry a, ∀ x : AmbientSpace, t.toFun x = R x + (v : AmbientSpace)
def CompAndInverseExist (r r' : LatticeSymmetry a) : Prop :=
  (r.comp r').toFun = r.toFun ∘ r'.toFun ∧ ∃ t : LatticeSymmetry a, t.IsInverse r
def MapsLinksToLinks (r : LatticeSymmetry a) : Prop :=
  ∀ b : Link a, ∃ b' : Link a, b'.initial = r.pointMap b.initial ∧ b'.terminal = r.pointMap b.terminal
def MapsPlaquettesBijectively (r : LatticeSymmetry a) : Prop :=
  (∀ p q : ElementaryPlaquette a, q = r.plaquetteMap p ↔ q.cornerSet = r.pointMap '' p.cornerSet) ∧
    Function.Bijective r.plaquetteMap ∧
    (∀ t : LatticeSymmetry a, t.IsInverse r →
      Function.LeftInverse t.plaquetteMap r.plaquetteMap ∧
        Function.RightInverse t.plaquetteMap r.plaquetteMap) ∧
    ∀ p : ElementaryPlaquette a, (r.plaquetteMap p).center = r.toFun p.center
def PullbackHomeomorph (r r' : LatticeSymmetry a) : Prop :=
  (∀ (U : GaugeField a) (b : Link a), U (r.linkMap b.opposite) = (U (r.linkMap b))⁻¹) ∧
    (r.comp r').pullbackField = r'.pullbackField ∘ r.pullbackField ∧
    IsHomeomorph r.pullbackField ∧
    ∀ t : LatticeSymmetry a, t.IsInverse r →
      Function.LeftInverse t.pullbackField r.pullbackField ∧
        Function.RightInverse t.pullbackField r.pullbackField
def ActOnBoundedObservables (r r' : LatticeSymmetry a) : Prop :=
  r.actOn (1 : GaugeField a → ℂ) = 1 ∧
    ∀ F F' : GaugeField a → ℂ, IsBoundedObservable F → IsBoundedObservable F' →
      IsBoundedObservable (r.actOn F) ∧
      observableSupNorm (r.actOn F) = observableSupNorm F ∧
      r.actOn (F + F') = r.actOn F + r.actOn F' ∧
      (∀ c : ℂ, r.actOn (c • F) = c • r.actOn F) ∧
      r.actOn (F * F') = r.actOn F * r.actOn F' ∧
      r.actOn (LatticeConventions.conjFun F) = LatticeConventions.conjFun (r.actOn F) ∧
      (r.comp r').actOn F = r.actOn (r'.actOn F) ∧
      (Continuous F → Continuous (r.actOn F)) ∧
      (∀ S : Set AmbientSpace, IsMeasurableFunctionOfLinksIn S F →
        IsMeasurableFunctionOfLinksIn (r.setImage S) (r.actOn F)) ∧
      (IsLocalObservable F → IsLocalObservable (r.actOn F))
def FaceEnergyAroundCorners (p : ElementaryPlaquette a) : Prop :=
  ∀ y₀ y₁ y₂ y₃ : LatticePoint a, p.cornerSet = {y₀, y₁, y₂, y₃} →
    TorusMetric.euclidNormVec ((y₀ : AmbientSpace) - y₁) = a →
    TorusMetric.euclidNormVec ((y₁ : AmbientSpace) - y₂) = a →
    TorusMetric.euclidNormVec ((y₂ : AmbientSpace) - y₃) = a →
    TorusMetric.euclidNormVec ((y₃ : AmbientSpace) - y₀) = a →
    ∃ b₀ b₁ b₂ b₃ : Link a,
      b₀.initial = y₀ ∧ b₀.terminal = y₁ ∧ b₁.initial = y₁ ∧ b₁.terminal = y₂ ∧
      b₂.initial = y₂ ∧ b₂.terminal = y₃ ∧ b₃.initial = y₃ ∧ b₃.terminal = y₀ ∧
      ∀ U : GaugeField a, faceEnergy U p =
        1 - (1 / 2) * (Matrices.ComplexMatrix2.fullTrace
          ((U b₀ * U b₁ * U b₂ * U b₃ : Matrices.ComplexMatrix2.specialUnitary) :
            Matrices.ComplexMatrix2)).re
def TransportsFaceEnergy (r : LatticeSymmetry a) (p : ElementaryPlaquette a) : Prop :=
  r.actOn (fun U : GaugeField a => faceEnergy U p) =
    fun U : GaugeField a => faceEnergy U (r.plaquetteMap p)
def InvariantStatesClosed (r r' : LatticeSymmetry a) : Prop :=
  ∀ ν : Measure (GaugeField a), IsProbabilityMeasure ν →
    IsSymmetricUnder ν r → IsSymmetricUnder ν r' →
      (∀ t : LatticeSymmetry a, t.IsInverse r → IsSymmetricUnder ν t) ∧
        IsSymmetricUnder ν (r.comp r')
def Statement : Prop :=
  ∀ a : ℝ, 0 < a → ∀ r r' : LatticeSymmetry a,
    IsAffineHyperoctahedral r ∧ CompAndInverseExist r r' ∧
    MapsLinksToLinks r ∧ MapsPlaquettesBijectively r ∧
    PullbackHomeomorph r r' ∧ ActOnBoundedObservables r r' ∧
    (∀ p : ElementaryPlaquette a, FaceEnergyAroundCorners p ∧ TransportsFaceEnergy r p) ∧
    InvariantStatesClosed r r'
end SymmetriesAsMotions
end InfiniteLattice
end YangMills.Construction
