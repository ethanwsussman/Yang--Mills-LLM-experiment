import YangMills.Construction.PassageToTheLimit.TransportedLatticeFunctionalsAreBoundedFormsProof
import YangMills.Construction.ReflectionPositivity.ReflectionsMirrorsAndSlabsAtOneCutoff
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.CutoffMirrors.LinkLevel
variable {D : MirrorData} (C : LinkLevel D)
def IsCenteredRep (y : D.Torus) (r : ℝ) : Prop :=
  D.IsRep (y D.dir) r ∧ r ∈ Ico (C.pos - D.side / 2) (C.pos + D.side / 2)
theorem side_pos : 0 < D.side := by apply _root_.YangMills.Construction.LimitSpaces.PeriodizeOnSmallSets.torusSide_pos <;> assumption
theorem existsUnique_isCenteredRep (y : D.Torus) : ∃! r, C.IsCenteredRep y r := by
  have hp : 0 < PeriodicLattice.torusSide D.L D.m := side_pos (D := D)
  have : Fact (0 < PeriodicLattice.torusSide D.L D.m) := ⟨hp⟩
  have hlen : C.pos + D.side / 2 = (C.pos - D.side / 2) + PeriodicLattice.torusSide D.L D.m := by
    change C.pos + D.side / 2 = (C.pos - D.side / 2) + D.side
    ring
  obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective (y D.dir)
  have hrep : ((toIcoMod hp (C.pos - D.side / 2) t : ℝ) :
      AddCircle (PeriodicLattice.torusSide D.L D.m)) = y D.dir := by
    have ht' : (t : AddCircle (PeriodicLattice.torusSide D.L D.m)) = y D.dir := ht
    rw [← ht', ← self_sub_toIcoDiv_zsmul hp (C.pos - D.side / 2) t, AddCircle.coe_sub]
    simp [AddCircle.coe_period]
  have hmem : toIcoMod hp (C.pos - D.side / 2) t ∈
      Ico (C.pos - D.side / 2) ((C.pos - D.side / 2) + PeriodicLattice.torusSide D.L D.m) :=
    toIcoMod_mem_Ico hp _ _
  refine ⟨toIcoMod hp (C.pos - D.side / 2) t, ⟨hrep, hlen ▸ hmem⟩, ?_⟩
  rintro r ⟨hr₁, hr₂⟩
  have hr₁' : (r : AddCircle (PeriodicLattice.torusSide D.L D.m)) = y D.dir := hr₁
  rw [hlen] at hr₂
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico hr₂ hmem).1 (hr₁'.trans hrep.symm)
def centeredRep (y : D.Torus) : ℝ := Classical.epsilon (C.IsCenteredRep y)
theorem isCenteredRep_centeredRep (y : D.Torus) : C.IsCenteredRep y (C.centeredRep y) :=
  Classical.epsilon_spec (C.existsUnique_isCenteredRep y).exists
def centeredRepSet (I : Set ℝ) : Set D.Torus := {y | C.centeredRep y ∈ I}
end YangMills.Construction.ReflectionPositivity.CutoffMirrors.LinkLevel
end
