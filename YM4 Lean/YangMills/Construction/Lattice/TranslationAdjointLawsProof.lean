import YangMills.Construction.Lattice.SiteIdentification
import YangMills.Construction.Lattice.TwoScaleOperatorDefs
import YangMills.Construction.LatticeFields.BlockAveraging
import YangMills.Construction.Lattice.LocalizedDecayBounds
import YangMills.Construction.Lattice.DiscreteCalculusIdentitiesProof
import YangMills.Construction.Lattice.TranslationAdjointLaws
import Mathlib
set_option autoImplicit false
open Finset
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open ScaledFun
variable {d N : ℕ}
namespace TranslationAdjoint
section Lattice
variable {s : Mesh N} {ι : Type}
theorem forwardDiff_apply (μ : Fin d) (f : SiteFun d s) (x : GridPoint d s) :
    forwardDiff s μ f x = s.h⁻¹ * (f (x + s.basisStep μ) - f x) := rfl
theorem scaledFun_sum_apply {X α : Type} (t : Finset α) (F : α → ScaledFun d s X) (x : X) :
    (∑ i ∈ t, F i) x = ∑ i ∈ t, F i x := by apply _root_.YangMills.SharedProofs.p17632 <;> assumption
end Lattice
section Average
variable {L j : ℕ} (S : Scales d L j N)
include S in
theorem fineScale_pos : 0 < fineScale L j := S.fineMesh.h_pos
end Average
end TranslationAdjoint
end YangMills.Construction.PeriodicLattice
