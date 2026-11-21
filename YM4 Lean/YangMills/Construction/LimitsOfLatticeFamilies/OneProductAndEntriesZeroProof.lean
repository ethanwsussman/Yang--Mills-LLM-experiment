import YangMills.Construction.LimitsOfLatticeFamilies.OneProductAndEntriesZero
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.LatticeLimits
open ModelSpace
namespace CommonProductAndZeroComponent
theorem disjoint_union_of_eqOn_ne {P : Type*} {n : ℕ} (u v : Fin n → Set P) (i : Fin n)
    (huv : ∀ l, l ≠ i → u l = v l) (hu : ∀ l k, l ≠ k → Disjoint (u l) (u k))
    (hv : ∀ l k, l ≠ k → Disjoint (v l) (v k)) (l k : Fin n) (hlk : l ≠ k) :
    Disjoint (u l ∪ v l) (u k ∪ v k) := by
  have hmix : ∀ l k, l ≠ k → Disjoint (u l) (v k) := by
    intro l k hlk
    by_cases hk : k = i
    · have hl : l ≠ i := fun h => hlk (h.trans hk.symm)
      rw [huv l hl]
      exact hv l k hlk
    · rw [← huv k hk]
      exact hu l k hlk
  rw [Set.disjoint_union_left, Set.disjoint_union_right, Set.disjoint_union_right]
  exact ⟨⟨hu l k hlk, hmix l k hlk⟩, (hmix k l hlk.symm).symm, hv l k hlk⟩
theorem apply_eq_zero_of_component_eq_zero {s : Conventions.StandingParameters} {Y : ModelSpace} {n : ℕ}
    {F : FunTuple s Y n → ℝ} {W : Fin n → Set (Y.Carrier s → ℝ)} (hF : IsMultilinearOn F W)
    (g : FunTuple s Y n) (hW : ∀ l, g l ∈ W l) (i : Fin n) (hi : g i = 0) : F g = 0 := by
  have hlin := hF g hW i (g i) (hW i) (g i) (hW i) 0 0
  have hupd : Function.update g i ((0 : ℝ) • g i + (0 : ℝ) • g i) = g := by
    funext l
    by_cases hl : l = i
    · subst hl
      simp [hi]
    · simp [Function.update_of_ne hl]
  rw [hupd] at hlin
  simpa using hlin
end CommonProductAndZeroComponent
open CommonProductAndZeroComponent in
theorem commonProductAndZeroEntry_holds : CommonProductAndZeroComponent := by
  intro s Y n _ ρ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro g hg g' hg' ⟨i, -, hi⟩
    refine ⟨fun l => supportIn s Y (g l) ∪ supportIn s Y (g' l), fun l => ?_, ?_, fun l => ?_, fun l => ?_⟩
    · exact Set.union_subset (hg.2 l) (hg'.2 l)
    · exact disjoint_union_of_eqOn_ne _ _ i (fun l hl => by rw [hi l hl]) hg.1.2.2 hg'.1.2.2
    · exact ⟨hg.1.1 l, hg.1.2.1 l, Set.subset_union_left⟩
    · exact ⟨hg'.1.1 l, hg'.1.2.1 l, Set.subset_union_right⟩
  · intro Ψ hΨ g hg i hi
    exact apply_eq_zero_of_component_eq_zero (hΨ (fun l => supportIn s Y (g l)) hg.2 hg.1.2.2) g
      (fun l => ⟨hg.1.1 l, hg.1.2.1 l, subset_rfl⟩) i hi
  · rintro g hg g' hg' ⟨i, -, hi⟩
    refine ⟨fun l => supportIn s Y (g l) ∪ supportIn s Y (g' l), fun l => ?_, ?_, fun l => ?_, fun l => ?_⟩
    · exact Set.union_subset (hg.2.2.2 l) (hg'.2.2.2 l)
    · exact disjoint_union_of_eqOn_ne _ _ i (fun l hl => by rw [hi l hl]) hg.2.2.1 hg'.2.2.1
    · exact ⟨hg.1 l, hg.2.1 l, Set.subset_union_left⟩
    · exact ⟨hg'.1 l, hg'.2.1 l, Set.subset_union_right⟩
  · intro Ψ hΨ g hg i hi
    exact apply_eq_zero_of_component_eq_zero (hΨ (fun l => supportIn s Y (g l)) hg.2.2.2 hg.2.2.1) g
      (fun l => ⟨hg.1 l, hg.2.1 l, subset_rfl⟩) i hi
end YangMills.Construction.LatticeLimits
end
