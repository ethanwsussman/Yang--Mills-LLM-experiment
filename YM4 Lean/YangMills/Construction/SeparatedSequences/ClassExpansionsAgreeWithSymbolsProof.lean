import YangMills.Construction.Lattice.WeightedDistanceOfASeparatedSequence
import YangMills.Construction.SeparatedSequences.ClassExpansionsAgreeWithSymbols
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set TorusMetric PeriodicLattice PeriodicLattice.DirichletOperators
namespace SeparatedClasses.ExpansionsOfClass
open SingleSequence SingleSequence.SequenceData
theorem isClosed_Ω (s : SequenceData) {n : ℕ} (hn : n ≤ s.data.t) : IsClosed (s.Ω n) := by
  have hL : 0 < s.data.L := by
    have := s.data.isAdmissible.2
    omega
  rcases s.Ω_mem.2.1.1 n hn with h | ⟨hi, h⟩
  · rw [h]
    exact isClosed_empty
  · exact SeparatedSequence.isClosed_of_isPartitionRegion hL hi h
theorem mem_layerAt_iff (s : SequenceData) {n : ℕ} (hn : n ≤ s.data.t) {y : s.data.Point}
    (hy : y ∉ s.data.memberAt s.Ω (n + 1)) : y ∈ s.data.layerAt s.Ω n ↔ y ∈ s.Ω n := by
  rcases hn.lt_or_eq with h | h
  · have hmem : s.data.memberAt s.Ω (n + 1) = s.Ω (n + 1) := by
      simp only [ClassData.memberAt, SeparatedSequences.truncatedMember]
      exact if_pos h
    have hlay : s.data.layerAt s.Ω n = closure (s.Ω n \ s.Ω (n + 1)) := by
      simp only [ClassData.layerAt, SeparatedSequences.layerSet]
      exact if_pos h
    rw [hlay]
    rw [hmem] at hy
    constructor
    · intro hc
      exact closure_minimal sdiff_subset (isClosed_Ω s hn) hc
    · intro hc
      exact subset_closure ⟨hc, hy⟩
  · have hlay : s.data.layerAt s.Ω n = s.Ω n := by
      simp only [ClassData.layerAt, SeparatedSequences.layerSet]
      rw [if_neg (by omega), if_pos h]
      rw [show s.data.t = n from h.symm]
    rw [hlay]
end SeparatedClasses.ExpansionsOfClass
end YangMills.Construction
end
