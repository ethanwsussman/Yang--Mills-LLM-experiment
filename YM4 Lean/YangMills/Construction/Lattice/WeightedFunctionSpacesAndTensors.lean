import YangMills.Construction.Lattice.CovariantSiteOperators
import YangMills.Construction.Lattice.KernelsAndContourDistanceOfASequence
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.TorusMetric YangMills.Construction.PeriodicLattice YangMills.Construction.PeriodicLattice.DirichletOperators YangMills.Construction.Matrices
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.SeparatedSequences.BaseParameters
variable (P : BaseParameters)
variable {P} in
open Classical in
def extendByZero {Ω₀ : Set P.Torus} (g : ↥(sitesOfRegion P.K Ω₀) → ComplexMatrix2) :
    P.LatticeSite 0 → ComplexMatrix2 :=
  fun x => if hx : x ∈ sitesOfRegion P.K Ω₀ then g ⟨x, hx⟩ else 0
section Weighted
variable {V : Type} [AddCommGroup V] [Module ℝ V]
end Weighted
end YangMills.Construction.SeparatedSequences.BaseParameters
end
