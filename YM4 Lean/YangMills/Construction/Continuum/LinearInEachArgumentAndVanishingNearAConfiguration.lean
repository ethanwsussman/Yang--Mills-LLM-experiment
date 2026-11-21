import YangMills.Construction.Continuum.FlatSchwartzAndTuples
import Mathlib
set_option autoImplicit false
open YangMills.Construction.EuclideanBalls YangMills.Construction.TestFunctions
noncomputable section
namespace YangMills.Construction.DisjointTuples
variable {k n : ℕ}
def disjointSupportTuples (k n : ℕ) : Set (Fin n → (Fin k → ℝ) → ℂ) :=
  {f | (∀ i, f i ∈ compactC1 k ℂ) ∧
    Pairwise fun i j => Disjoint (tsupport (f i)) (tsupport (f j))}
theorem tsupport_add_smul_subset_union (f g : (Fin k → ℝ) → ℂ) (c : ℂ) :
    tsupport (f + c • g) ⊆ tsupport f ∪ tsupport g := by
  refine closure_minimal ?_ ((isClosed_tsupport _).union (isClosed_tsupport _))
  intro x hx
  by_contra hcon
  simp only [Set.mem_union, not_or] at hcon
  have hf : f x = 0 := image_eq_zero_of_notMem_tsupport hcon.1
  have hg : g x = 0 := image_eq_zero_of_notMem_tsupport hcon.2
  exact hx (by simp [hf, hg])
theorem update_add_smul_mem_disjointSupportTuples {f : Fin n → (Fin k → ℝ) → ℂ} {i : Fin n}
    {g : (Fin k → ℝ) → ℂ} (c : ℂ) (hf : f ∈ disjointSupportTuples k n)
    (hg : Function.update f i g ∈ disjointSupportTuples k n) :
    Function.update f i (f i + c • g) ∈ disjointSupportTuples k n := by
  have hgi : g ∈ compactC1 k ℂ := by simpa using hg.1 i
  have hfi : f i ∈ compactC1 k ℂ := hf.1 i
  have hsub := tsupport_add_smul_subset_union (f i) g c
  have hdisj : ∀ j, j ≠ i → Disjoint (tsupport (f i + c • g)) (tsupport (f j)) := by
    intro j hj
    have h₁ : Disjoint (tsupport (f i)) (tsupport (f j)) := hf.2 hj.symm
    have h₂ : Disjoint (tsupport g) (tsupport (f j)) := by
      simpa [Function.update_of_ne hj] using hg.2 hj.symm
    exact (Set.disjoint_union_left.2 ⟨h₁, h₂⟩).mono_left hsub
  refine ⟨fun j => ?_, fun j l hjl => ?_⟩
  · by_cases hj : j = i
    · subst hj
      rw [Function.update_self]
      exact ⟨hfi.1.add (hgi.1.const_smul c),
        (hfi.2.isCompact.union hgi.2.isCompact).of_isClosed_subset (isClosed_tsupport _) hsub⟩
    · rw [Function.update_of_ne hj]
      exact hf.1 j
  · by_cases hj : j = i
    · subst hj
      have hl : l ≠ j := hjl.symm
      simpa [Function.update_of_ne hl] using hdisj l hl
    · by_cases hl : l = i
      · subst hl
        simpa [Function.update_of_ne hj] using (hdisj j hj).symm
      · simpa [Function.update_of_ne hj, Function.update_of_ne hl] using hf.2 hjl
def IsSeparatelyLinear (D : disjointSupportTuples k n → ℂ) : Prop :=
  ∀ (i : Fin n) (c : ℂ) (f : Fin n → (Fin k → ℝ) → ℂ) (g : (Fin k → ℝ) → ℂ)
    (hf : f ∈ disjointSupportTuples k n) (hg : Function.update f i g ∈ disjointSupportTuples k n),
    D ⟨Function.update f i (f i + c • g), update_add_smul_mem_disjointSupportTuples c hf hg⟩ =
      D ⟨f, hf⟩ + c * D ⟨Function.update f i g, hg⟩
def IsVanishingRadius (D : disjointSupportTuples k n → ℂ) (x : injectiveTuples (Fin k → ℝ) n)
    (ρ : ℝ) : Prop :=
  0 < ρ ∧ ∀ f : disjointSupportTuples k n,
    (∀ i, tsupport (f.1 i) ⊆ euclidBall (x.1 i) ρ) → D f = 0
def VanishesNearConfig (D : disjointSupportTuples k n → ℂ)
    (x : injectiveTuples (Fin k → ℝ) n) : Prop :=
  ∃ ρ, IsVanishingRadius D x ρ
end YangMills.Construction.DisjointTuples
end
