import YangMills.Construction.LimitsOfLatticeFamilies.ClosedBallsAndTheTorusAreCompact
import YangMills.Construction.LimitsOfLatticeFamilies.SeparatedTensorsLieInFiniteBalls
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.LatticeLimits
open ModelSpace
theorem SepTensorsInFiniteBalls.claim_holds
    (hballs : CompactBallsAndTorus.Claim) :
    SepTensorsInFiniteBalls.Claim := by
  intro s Y q _
  have ballMono : ∀ {ρ ρ' : ℝ≥0∞}, ρ ≤ ρ' → ballAtBase s Y ρ ⊆ ballAtBase s Y ρ' :=
    fun h _ hy => lt_of_lt_of_le hy h
  have tupleMono : ∀ {ρ ρ' : ℝ≥0∞}, ρ ≤ ρ' →
      sepTuplesIn s Y q ρ ⊆ sepTuplesIn s Y q ρ' :=
    fun h _ hf => ⟨hf.1, fun i => (hf.2 i).trans (ballMono h)⟩
  have tensorMono : ∀ {ρ ρ' : ℝ≥0∞}, ρ ≤ ρ' →
      sepTensors s Y q ρ ≤ sepTensors s Y q ρ' :=
    fun h => Submodule.span_mono (Set.image_mono (tupleMono h))
  refine ⟨fun F hF => ?_, fun ρ ρ' _ h => tensorMono h⟩
  refine Submodule.span_induction
    (p := fun F _ => ∃ ρ : ℝ, 0 < ρ ∧ F ∈ sepTensors s Y q (ENNReal.ofReal ρ))
    ?_ ?_ ?_ ?_ hF
  · rintro _ ⟨f, hf, rfl⟩
    have hsep : f ∈ sepTuples s Y q := by rwa [sepTuplesIn_top] at hf
    choose r hr hsub using fun i => (((hballs s).1 Y).2 (supportIn s Y (f i)) (hsep.2.1 i)).1
    have hle : ∀ i, r i ≤ 1 + ∑ i, r i := fun i => by
      have := Finset.single_le_sum (fun k _ => (hr k).le) (Finset.mem_univ i)
      linarith
    have hpos : 0 < 1 + ∑ i, r i := by
      have : 0 ≤ ∑ i, r i := Finset.sum_nonneg fun k _ => (hr k).le
      linarith
    exact ⟨_, hpos, cTensor_mem
      ⟨hsep, fun i => (hsub i).trans (ballMono (ENNReal.ofReal_le_ofReal (hle i)))⟩⟩
  · exact ⟨1, one_pos, Submodule.zero_mem _⟩
  · rintro F G _ _ ⟨ρ, hρ, hF⟩ ⟨ρ', _, hG⟩
    exact ⟨max ρ ρ', lt_max_of_lt_left hρ, Submodule.add_mem _
      (tensorMono (ENNReal.ofReal_le_ofReal (le_max_left _ _)) hF)
      (tensorMono (ENNReal.ofReal_le_ofReal (le_max_right _ _)) hG)⟩
  · rintro c F _ ⟨ρ, hρ, hF⟩
    exact ⟨ρ, hρ, Submodule.smul_mem _ c hF⟩
end YangMills.Construction.LatticeLimits
end
