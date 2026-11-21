import YangMills.Construction.Lattice.AdicGridPoints
import YangMills.Construction.ToriAtArbitraryCouplings.TheCountableFamilyOfSupportsAndCharts
import YangMills.Construction.Torus.HypercubicGroupTranslationsAndInvarianceOnTorusOrFourSpace
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ToriAtArbitraryCouplings
open ReflectionPositivity.AxisMirror (Ambient)
namespace LatticeSymmetriesOnSupports
open TorusSymmetries (actOn translateOn)
open TorusTransport (hyperoctahedral)
def PreservesSupports (s : TorusSide) (E : Ambient) (r : Equiv.Perm (s.Point E)) : Prop :=
  (∀ Q ∈ s.supportFamily E, r '' Q ∈ s.supportFamily E) ∧
    (∀ f ∈ s.c1Set E, f ∘ r.symm ∈ s.c1Set E) ∧
    ∀ x y, s.pointDist E (r x) (r y) = s.pointDist E x y
def Statement : Prop :=
  ∀ s : TorusSide,
    (∀ w : hyperoctahedral,
      PreservesSupports s .torus (actOn s.asMirrorData.toStandingParameters .torus w)) ∧
    (∀ w : hyperoctahedral,
      PreservesSupports s .euclidean (actOn s.asMirrorData.toStandingParameters .euclidean w)) ∧
    (∀ v : Fin 4 → ℝ, (∀ μ, v μ ∈ PeriodicLattice.adicGridPoints s.L) →
      PreservesSupports s .torus (translateOn s.asMirrorData.toStandingParameters .torus
        (AmbientPoints.proj s.asMirrorData.toStandingParameters .torus v))) ∧
    ∀ v : Fin 4 → ℝ, (∀ μ, v μ ∈ PeriodicLattice.adicGridPoints s.L) →
      PreservesSupports s .euclidean (translateOn s.asMirrorData.toStandingParameters .euclidean
        (AmbientPoints.proj s.asMirrorData.toStandingParameters .euclidean v))
end LatticeSymmetriesOnSupports
end YangMills.Construction.ToriAtArbitraryCouplings
end
