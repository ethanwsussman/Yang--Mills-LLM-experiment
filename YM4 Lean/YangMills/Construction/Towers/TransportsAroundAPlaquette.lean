import YangMills.Construction.Towers.TheFourBondsOfAPlaquette
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
def transportSign : Fin 4 → ℂ := ![1, 1, -1, -1]
section Periodic
variable {L n k j : ℕ}
def faceEdge (p : Tower.Face L n k j) (i : Fin 4) : Tower.Edge L n k j :=
  (Tower.faceEdges p)[(i : ℕ)]'(by simp [Tower.faceEdges])
def faceTransports (U : Tower.Edge L n k j → Matrices.ComplexMatrix2) (p : Tower.Face L n k j) :
    Fin 4 → Matrices.ComplexMatrix2 :=
  ![1, U (faceEdge p 0), U (faceEdge p 0) * U (faceEdge p 1) * (U (faceEdge p 2))⁻¹,
    PeriodicLattice.plaquetteHolonomy U p]
def transportedForm (U B : Tower.Edge L n k j → Matrices.ComplexMatrix2) (p : Tower.Face L n k j) :
    Fin 4 → Matrices.ComplexMatrix2 :=
  fun i => transportSign i • Matrices.ComplexMatrix2.conjugateBy (faceTransports U p i)
    (B (faceEdge p i))
theorem faceTransports_three (U : Tower.Edge L n k j → Matrices.ComplexMatrix2)
    (hU : ∀ e, U e.opposite = (U e)⁻¹) (p : Tower.Face L n k j) :
    faceTransports U p 3 = faceTransports U p 2 * (U (faceEdge p 3))⁻¹ := by
  simp [faceTransports, PeriodicLattice.plaquetteHolonomy, PeriodicLattice.pathHolonomy,
    PeriodicLattice.Plaquette.boundaryBonds, faceEdge, Tower.faceEdges, hU, mul_assoc]
end Periodic
namespace FullSpace
variable {a : ℝ}
def faceEdge (p : InfiniteLattice.ElementaryPlaquette a) (i : Fin 4) : InfiniteLattice.Link a :=
  (Tower.FullSpace.faceEdges p)[(i : ℕ)]'(by simp [Tower.FullSpace.faceEdges])
def faceTransports (U : InfiniteLattice.Link a → Matrices.ComplexMatrix2)
    (p : InfiniteLattice.ElementaryPlaquette a) : Fin 4 → Matrices.ComplexMatrix2 :=
  ![1, U (faceEdge p 0), U (faceEdge p 0) * U (faceEdge p 1) * (U (faceEdge p 2))⁻¹,
    Tower.FullSpace.faceVariable U p]
def transportedForm (U B : InfiniteLattice.Link a → Matrices.ComplexMatrix2)
    (p : InfiniteLattice.ElementaryPlaquette a) : Fin 4 → Matrices.ComplexMatrix2 :=
  fun i => Tower.transportSign i • Matrices.ComplexMatrix2.conjugateBy (faceTransports U p i)
    (B (faceEdge p i))
theorem faceTransports_three (U : InfiniteLattice.Link a → Matrices.ComplexMatrix2)
    (hU : ∀ e, U e.opposite = (U e)⁻¹) (p : InfiniteLattice.ElementaryPlaquette a) :
    faceTransports U p 3 = faceTransports U p 2 * (U (faceEdge p 3))⁻¹ := by
  simp [faceTransports, Tower.FullSpace.faceVariable, Tower.FullSpace.linkHolonomy,
    Tower.FullSpace.faceBoundary, faceEdge, Tower.FullSpace.faceEdges, hU, mul_assoc]
end FullSpace
end Tower
end YangMills.Construction
end
