import YangMills.Construction.SourcesAndGluing.PredicatesOfSimilaritiesOfLattices
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SourcesAndGluing
def RescalingTransportClaim : Prop :=
  (∀ (D : GluingSetup) (Ψ : LatticeRescaling D),
    Ψ.MapsInfiniteLattice ∧ Ψ.MapsPeriodicLattice ∧
    Ψ.PreservesExpectation ∧ Ψ.MapsPeriodicObservables ∧
    Ψ.MapsLipschitzOnTorus ∧ Ψ.MapsSmearedEnergies ∧
    Ψ.MapsLipschitzOnSpace ∧ Ψ.MapsPeriodicGibbs ∧
    Ψ.MapsGridScales ∧
    ∀ (g : CubicGrid D) (hg : g.IsMirrorGrid),
      Ψ.MapsCubes g hg ∧ Ψ.MapsCubeAlgebras g hg ∧
      Ψ.ConjugatesReflectionGroup g hg ∧ Ψ.MapsReflectionProducts g hg) ∧
  ∀ (D : GluingSetup) (g : CubicGrid D) (hg : g.IsMirrorGrid), MovesToNormalizedOrigin g hg
end YangMills.Construction.SourcesAndGluing
end
