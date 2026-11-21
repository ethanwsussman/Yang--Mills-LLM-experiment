import YangMills.Construction.ChessboardTori.GridsCellsAndCopies
import YangMills.Construction.InfiniteLattice.PositiveLinksAndCylinderFunctions
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace ChessboardTori
namespace PeriodSubgroup
variable {D : ChessboardSetup} (P : PeriodSubgroup D)
def LiftIsGaugeField (U : P.GaugeConfig) : Prop :=
  ∀ b : D.Link, P.liftField U b.opposite = (P.liftField U b)⁻¹
open Classical in
def liftGaugeField (U : P.GaugeConfig) : D.GaugeField :=
  if h : P.LiftIsGaugeField U then ⟨P.liftField U, h⟩
  else InfiniteLattice.trivialField D.mesh
def ProjMapsEdgesAndFaces : Prop :=
  Function.Surjective P.projPoint ∧
  Function.Surjective P.projEdge ∧
  P.projEdge '' {b : D.Link | b.IsPositivelyOriented} = {c : P.DirectedEdge | c.IsForward} ∧
  Function.Surjective P.projFace ∧
  (∀ b : D.Link, P.projEdge b.opposite = (P.projEdge b).flip) ∧
  (∀ p : D.Plaquette, (P.projFace p).vertexSet = P.projPoint '' D.faceCorners p) ∧
  ∀ p : D.Plaquette, P.faceCenter (P.projFace p) = P.proj p.center
def ProjFibresArePeriodOrbits : Prop :=
  (∀ x y : InfiniteLattice.LatticePoint D.mesh,
    P.projPoint x = P.projPoint y ↔ ∃ v ∈ D.periodSubgroupOfGrid P.mult, y = x + v) ∧
  (∀ b b' : D.Link,
    P.projEdge b = P.projEdge b' ↔ ∃ v ∈ D.periodSubgroupOfGrid P.mult, b' = D.shiftLink b v) ∧
  ∀ p p' : D.Plaquette,
    P.projFace p = P.projFace p' ↔
      ∃ v ∈ D.periodSubgroupOfGrid P.mult, p' = D.shiftPlaquette p v
def LiftMatchesFaces : Prop :=
  (∀ U : P.GaugeConfig, P.LiftIsGaugeField U) ∧
  Continuous P.liftGaugeField ∧
  ∀ (U : P.GaugeConfig) (p : D.Plaquette),
    InfiniteLattice.faceHolonomy (P.liftGaugeField U) p =
        BoxTorus.faceHolonomy U (P.projFace p) ∧
      InfiniteLattice.faceEnergy (P.liftGaugeField U) p =
        P.faceEnergy U (P.projFace p)
end PeriodSubgroup
def ProjOnEdgesAndFaces.Statement : Prop :=
  ∀ (D : ChessboardSetup) (P : PeriodSubgroup D),
    P.ProjMapsEdgesAndFaces ∧ P.ProjFibresArePeriodOrbits ∧ P.LiftMatchesFaces
end ChessboardTori
end YangMills.Construction
end
