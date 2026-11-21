import YangMills.Construction.PeriodicOperators.TraceOfAMomentumShift
import YangMills.Construction.PeriodicOperators.WaveSpacesOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.ShiftTrace
open YangMills.Construction.PeriodicOperators.RiemannSums (DualClasses periodLattice)
theorem traceVanishes_holds (hB : YangMills.Construction.PeriodicOperators.BlochDecomposition.Claim) :
    TraceVanishes := by
  intro I hI s hs q hq hqp A hA
  classical
  by_cases hfin : Module.Finite ℂ (I.QuotMod s → ℂ)
  swap
  · have hno : ¬∃ t : Finset (I.QuotMod s → ℂ),
        Nonempty (Module.Basis t ℂ (I.QuotMod s → ℂ)) := by
      rintro ⟨t, ⟨b⟩⟩
      exact hfin (Module.Finite.of_basis b)
    rw [LinearMap.trace, dif_neg hno]
    rfl
  have F := hB I hI
  have := F.dualClasses_finite s hs
  let _ : Fintype (DualClasses s) := Fintype.ofFinite _
  let r : DualClasses s → dualLattice s := fun c => Quotient.out c
  have hr : IsDualSection s r := fun c => Quotient.out_eq c
  obtain ⟨hind, htop⟩ := F.internal_sum s hs r hr
  have hint : DirectSum.IsInternal (fun c => blochWaveSubspace I s (r c)) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  let v := fun c => Module.finBasis ℂ (blochWaveSubspace I s (r c))
  let b := hint.collectedBasis v
  rw [LinearMap.trace_eq_matrix_trace ℂ b A]
  refine Finset.sum_eq_zero ?_
  rintro ⟨c, a⟩ -
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply]
  let qm : dualLattice s := ⟨q, hq⟩
  let c' : DualClasses s := c + (QuotientAddGroup.mk qm : DualClasses s)
  have hne : c' ≠ c := by
    intro hcc
    have h0 : (QuotientAddGroup.mk qm : DualClasses s) = 0 := by
      simpa [c'] using hcc
    rw [QuotientAddGroup.eq_zero_iff] at h0
    exact hqp (AddSubgroup.mem_addSubgroupOf.mp h0)
  have hbmem : b ⟨c, a⟩ ∈ blochWaveSubspace I s (r c) := by
    simp only [b, DirectSum.IsInternal.collectedBasis_coe]
    exact (v c a).2
  have hshift : A (b ⟨c, a⟩) ∈ blochWaveSubspace I s ((r c : _) + q) :=
    hA _ (r c).2 _ hbmem
  have hsame : blochWaveSubspace I s ((r c : _) + q) = blochWaveSubspace I s (r c') := by
    refine F.subspace_congr s hs _ ((dualLattice s).add_mem (r c).2 hq) _ (r c').2 ?_
    have hcl : (QuotientAddGroup.mk (r c + qm) : DualClasses s) = (QuotientAddGroup.mk (r c') : DualClasses s) := by
      rw [hr c', QuotientAddGroup.mk_add, hr c]
    rw [QuotientAddGroup.eq] at hcl
    have := AddSubgroup.mem_addSubgroupOf.mp hcl
    simpa [sub_eq_neg_add, qm, add_comm] using this
  rw [hsame] at hshift
  exact hint.collectedBasis_repr_of_mem_ne v hne hshift
end YangMills.Construction.PeriodicOperators.ShiftTrace
end
