import YangMills.Construction.Lattice.TwistedActionOnFluctuationsAndLattices
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ} {j : ℤ}
theorem IsGaugeFieldWithForm.toComplex {ℬ : Set (Bond L m j)}
    {V₀ A : Bond L m j → Matrices.ComplexMatrix2} (h : IsGaugeFieldWithForm ℬ V₀ A) :
    IsGaugeField complexGaugeGroup ℬ V₀ ∧ A ∈ complexFormsOn ℬ := by
  rcases h with ⟨hV, hA⟩ | h
  · refine ⟨⟨fun b hb => (Matrix.mem_specialUnitaryGroup_iff.mp (hV.1 b hb)).2, hV.2⟩, ?_⟩
    exact ⟨⟨fun b hb => (hA.1.1 b hb).2, hA.1.2⟩, hA.2⟩
  · exact h
theorem twistedTransportOfFluctuations_holds
    (hRegions : LatticeIsometryGroupActionStatement)
    (hTwisted : TwistedTransportIsometryInvariance) :
    TwistedTransportOfFluctuations := by
  intro L m i σ hL hm hi hσ
  obtain ⟨hPositive, -, hMaps, -⟩ := hTwisted L m i σ hL hm hi hσ
  obtain ⟨-, -, -, -, hCarries⟩ := hRegions L m i hL hm hi
  refine ⟨fun j hj hij ℬ hℬ V₀ A h => ?_, fun i' hi' => ?_⟩
  · obtain ⟨hV, hA⟩ := h.toComplex
    obtain ⟨-, hPlain, hMap, -⟩ := hMaps j hj hij ℬ hℬ
    exact ⟨(hMap V₀ hV).transport_expTwist A hA,
      fun hσ' => hPlain (hPositive hσ' j hj hij) V₀ A hA⟩
  · obtain ⟨⟨hLattice, hSegments, hSquares, hBonds, -, hPlaquettes, -, -, -, hPartition⟩, -⟩ :=
      hCarries σ hσ i' hi'
    exact ⟨hLattice, hBonds, hSegments, hPlaquettes, hSquares, hPartition⟩
end YangMills.Construction.PeriodicLattice
