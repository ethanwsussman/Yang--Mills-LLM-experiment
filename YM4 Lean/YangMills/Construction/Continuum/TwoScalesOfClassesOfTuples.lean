import YangMills.Construction.Continuum.TuplesAsVectors
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusTransport.TupleVectors
open TestFunctionOrders
variable (D : TransportData)
def admissibleSepTuples (d R : ℝ) (hd : 0 < d) (hR : 0 < R) : Set FnTuple :=
  {nilTuple _} ∪
    ⋃ n : ℕ+, (fun f : Domain.euclidean.FnFamily D n ℝ => (⟨n, f⟩ : FnTuple)) ''
      {f | (⟨n, f⟩ : FnTuple) ∈ sepTuples D Set.univ ∧ FamilyIsAdmissible D d R hd hR f}
def cubeSepTuples (ϖ d R : ℝ) (_hϖ : 0 < ϖ) (_hd : 0 < d) (_hR : 0 < R) : Set FnTuple :=
  {nilTuple _} ∪
    {t | t ∈ sepTuples D Set.univ ∧
      (∀ i, ∃ x, HasCompactSupportIn (t.2 i) (ballR4 x R) ∧
        ballR4 x R ⊆ {y | maxNorm y < ϖ - d / 2}) ∧
      ∀ i k, i ≠ k → ENNReal.ofReal d ≤
        Domain.euclidean.setDist D (entrySupp D (t.2 i)) (entrySupp D (t.2 k))}
theorem nilTuple_mem_admissibleSepTuples {d R : ℝ} (hd : 0 < d) (hR : 0 < R) :
    nilTuple _ ∈ admissibleSepTuples D d R hd hR :=
  Or.inl rfl
theorem admissibleSepTuples_subset {d R : ℝ} (hd : 0 < d) (hR : 0 < R) :
    admissibleSepTuples D d R hd hR ⊆ sepTuples D Set.univ := by
  rintro t (rfl | h)
  · exact nilTuple_mem_sepTuples D _
  · obtain ⟨n, f, hf, rfl⟩ := Set.mem_iUnion.mp h
    exact hf.1
end YangMills.Construction.TorusTransport.TupleVectors
end
