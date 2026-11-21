import YangMills.Construction.Lattice.FieldNormProperties
import YangMills.Construction.Lattice.GaugeTermOnACubeProof
import YangMills.Construction.Lattice.PointDecayingOneForms
import YangMills.Construction.Lattice.TranslationAdjointLaws
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open ScaledFun
variable {d N : ℕ}
namespace DecayingValueBounds
theorem finset_sum_apply {s : Mesh N} {X T : Type} (A : Finset T) (g : T → ScaledFun d s X)
    (q : X) : (∑ t ∈ A, g t) q = ∑ t ∈ A, g t q := by apply _root_.YangMills.SharedProofs.p17632 <;> assumption
variable {L j : ℕ} (S : Scales d L j N)
open Classical in
def cellRestrict (f : OneForm d S.fineMesh) (y : GridPoint d S.unitMesh) : OneForm d S.fineMesh :=
  ofMap fun q => if q.2 ∈ S.fineCell y then f q else 0
variable {S}
end DecayingValueBounds
end YangMills.Construction.PeriodicLattice
