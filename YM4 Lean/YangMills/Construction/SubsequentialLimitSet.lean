import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
namespace YangMills.Construction.Topology
def subseqLimitSet {X : Type} [TopologicalSpace X] (u : ℕ → X) : Set X :=
  {y | ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun n => u (φ n)) atTop (𝓝 y)}
def SubseqLimitSetNonemptyClosed : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [TopologicalSpace.MetrizableSpace X]
    (u : ℕ → X),
    (subseqLimitSet u).Nonempty ∧ IsClosed (subseqLimitSet u)

theorem subseqLimitSet_eq_setOf_clusterPt {X : Type} [TopologicalSpace X]
    [FirstCountableTopology X] (u : ℕ → X) :
    subseqLimitSet u = {y | ClusterPt y (map u atTop)} := by
  ext y
  constructor
  · rintro ⟨φ, hφ, hlim⟩
    have hcl : MapClusterPt y atTop (u ∘ φ) := Tendsto.mapClusterPt hlim
    exact MapClusterPt.of_comp hφ.tendsto_atTop hcl
  · intro hy
    obtain ⟨φ, hφ, hlim⟩ := MapClusterPt.tendsto_subseq (show MapClusterPt y atTop u from hy)
    exact ⟨φ, hφ, hlim⟩
theorem subseqLimitSet_nonempty_isClosed : SubseqLimitSetNonemptyClosed := by
  intro X _ _ _ u
  let := TopologicalSpace.metrizableSpaceMetric X
  rw [subseqLimitSet_eq_setOf_clusterPt u]
  exact ⟨exists_clusterPt_of_compactSpace (map u atTop), isClosed_setOfPred_clusterPt⟩
end YangMills.Construction.Topology
