import YangMills.Construction.Lattice.CellGridPropertiesProofs
import YangMills.Construction.Lattice.ContinuityOfTheActionOfAnIsometryOfAGridDatum
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.GridSymmetries
private theorem continuous_edgeVariable {L : ℕ} {κ : ℤ} (d : CellGrid L κ)
    (b : d.DirectedEdge) :
    Continuous fun U : d.GaugeConfig => BoxTorus.edgeVariable U b := by apply _root_.YangMills.Construction.GridLattice.continuous_edgeVariable <;> assumption
theorem pullbackContinuity_holds : PullbackContinuity := by
  intro L κ d g
  have hc : Continuous g.pullback :=
    continuous_pi fun b => continuous_edgeVariable d (g.edgeImage b.1)
  refine ⟨hc, fun F hF ⟨C, hC⟩ => ⟨hF.comp hc.measurable, C, fun U => hC _⟩⟩
end YangMills.Construction.GridSymmetries
end
