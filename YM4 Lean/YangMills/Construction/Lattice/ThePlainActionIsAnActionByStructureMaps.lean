import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.LayerBondsCoarseSpacesAndAverages
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open PeriodicLattice Conventions
namespace GaugeAction.StructuralAction
instance instFiniteSite (s : StandingParameters) (j : ℤ) : Finite (Site s.L s.m j) :=
  SeparatedSequences.BaseParameters.site_finite (by have := s.isAdmissible.2; omega) _ _
instance instFinitePlaquette (s : StandingParameters) (j : ℤ) : Finite (Plaquette s.L s.m j) :=
  Finite.of_injective (fun p : Plaquette s.L s.m j => (p.origin, p.firstAxis, p.secondAxis)) (by
    rintro ⟨a, b, c, _⟩ ⟨a', b', c', _⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl)
end GaugeAction.StructuralAction
end YangMills.Construction
