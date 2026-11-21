import YangMills.Construction.ClusterExpansionOfAStep.EnergyNearAClassProof
import YangMills.Construction.ClusterExpansionOfAStep.NearSitesOfAClass
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages LumpContours TorusFields TorusLumps
variable {n : ℕ} [NeZero n]
theorem card_thickening_le (m : ℕ) (S : Finset (TorusSite n)) :
    (thickening m S).card ≤ S.card * (2 * m + 1) ^ 4 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood.card_thickening_le <;> assumption
theorem exists_cover_card_eq_ballCoverNumber (m : ℕ) (X : Finset (TorusSite n)) :
    ∃ C : Finset (TorusSite n), C.card = ballCoverNumber m X ∧ X ⊆ thickening m C := by
  have hne : {k | ∃ C : Finset (TorusSite n), C.card = k ∧ X ⊆ thickening m C}.Nonempty :=
    ⟨X.card, X, rfl, fun z hz => (mem_thickening _ _ _).mpr ⟨z, hz, by simp [supDist_self]⟩⟩
  exact Nat.sInf_mem hne
theorem ballCoverNumber_le (m : ℕ) (X C : Finset (TorusSite n)) (h : X ⊆ thickening m C) :
    ballCoverNumber m X ≤ C.card :=
  Nat.sInf_le ⟨C, rfl, h⟩
open Classical in
theorem exists_cover_of_lumps (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (r : ℕ) (X : Finset (TorusSite n))
    (W : TorusField n) :
    ∃ C : Finset (TorusSite n),
      C.card ≤ ((torusHotLumps ℓ W).filter (· ⊆ X)).card + excessLength ℓ r X W ∧
      X ⊆ thickening (4 * r) C := by
  obtain ⟨C, hC, hcov⟩ := exists_cover_card_eq_ballCoverNumber (4 * r)
    (X \ thickening (4 * r) (((torusHotLumps ℓ W).filter (· ⊆ X)).image lumpCenter))
  refine ⟨((torusHotLumps ℓ W).filter (· ⊆ X)).image lumpCenter ∪ C, ?_, fun z hz => ?_⟩
  · refine (Finset.card_union_le _ _).trans (Nat.add_le_add Finset.card_image_le ?_)
    rw [hC]
    exact le_of_eq rfl
  · by_cases hw : z ∈ thickening (4 * r) (((torusHotLumps ℓ W).filter (· ⊆ X)).image lumpCenter)
    · obtain ⟨u, hu, hzu⟩ := (mem_thickening _ _ _).mp hw
      exact (mem_thickening _ _ _).mpr ⟨u, Finset.mem_union_left _ hu, hzu⟩
    · obtain ⟨u, hu, hzu⟩ := (mem_thickening _ _ _).mp (hcov (Finset.mem_sdiff.mpr ⟨hz, hw⟩))
      exact (mem_thickening _ _ _).mpr ⟨u, Finset.mem_union_right _ hu, hzu⟩
theorem nearSitesLeLumpsAndLength_holds : NearSitesLeLumpsAndLength := by
  classical
  intro ℓ n _ r X W hr
  obtain ⟨C, hC, hcov⟩ := exists_cover_of_lumps ℓ r X W
  refine ⟨(ballCoverNumber_le _ _ _ hcov).trans ?_, ?_⟩
  · convert hC using 2
  · have hsub : nearSites r X ⊆ thickening (4 * r + r / 4) C := by
      intro y hy
      obtain ⟨z, hz, hyz⟩ := (Finset.mem_filter.mp hy).2
      obtain ⟨u, hu, hzu⟩ := (mem_thickening _ _ _).mp (hcov hz)
      have hyz' : supDist y z ≤ r / 4 := by
        have h4 : ((supDist y z * 4 : ℕ) : ℝ) < (r : ℝ) := by
          push_cast
          linarith
        have : supDist y z * 4 < r := by exact_mod_cast h4
        omega
      exact (mem_thickening _ _ _).mpr ⟨u, hu, (supDist_triangle y z u).trans (by omega)⟩
    have h1 := (Finset.card_le_card hsub).trans (card_thickening_le (4 * r + r / 4) C)
    have h2 : 2 * (4 * r + r / 4) + 1 ≤ 10 * r := by omega
    calc (nearSites r X).card ≤ C.card * (2 * (4 * r + r / 4) + 1) ^ 4 := h1
      _ ≤ (((torusHotLumps ℓ W).filter (· ⊆ X)).card + excessLength ℓ r X W) * (10 * r) ^ 4 := by
          refine Nat.mul_le_mul ?_ (Nat.pow_le_pow_left h2 4)
          convert hC using 2
      _ = (10 * r) ^ 4 * (((torusHotLumps ℓ W).filter (· ⊆ X)).card + excessLength ℓ r X W) := by
          ring
end YangMills.Construction.ClusterExpansionOfAStep
end
