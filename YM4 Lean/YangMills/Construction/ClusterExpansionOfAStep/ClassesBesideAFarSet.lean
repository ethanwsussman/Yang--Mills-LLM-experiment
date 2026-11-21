import YangMills.Construction.ClusterExpansionOfAStep.DistancesAndClasses
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusLumps
open YangMills.Construction.TorusFields YangMills.Construction.BlockAverages YangMills.Construction.LumpContours
variable {n : ℕ} [NeZero n] {r : ℕ} {A B : Finset (TorusSite n)}
theorem chainConnected_mono {y z : TorusSite n} (hAB : A ⊆ B) (h : ChainConnected r A y z) :
    ChainConnected r B y z := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact ih.tail ⟨hAB hs.1, hAB hs.2.1, hs.2.2⟩
theorem chainConnected_of_separated (hsep : ∀ a ∈ A, ∀ b ∈ B, r < supDist a b) {y z : TorusSite n} (hy : y ∈ A)
    (h : ChainConnected r (A ∪ B) y z) : ChainConnected r A y z ∧ z ∈ A := by
  induction h with
  | refl => exact ⟨Relation.ReflTransGen.refl, hy⟩
  | tail _ hs ih =>
    obtain ⟨hc, hm⟩ := ih
    rcases Finset.mem_union.mp hs.2.1 with hv | hv
    · exact ⟨hc.tail ⟨hm, hv, hs.2.2⟩, hv⟩
    · exact absurd hs.2.2 (not_le.mpr (hsep _ hm _ hv))
open Classical in
theorem mem_chainComponents_union_of_separated (hsep : ∀ a ∈ A, ∀ b ∈ B, r < supDist a b)
    {X : Finset (TorusSite n)} (hX : X ∈ chainComponents r A) : X ∈ chainComponents r (A ∪ B) := by
  obtain ⟨y, hy, rfl⟩ := mem_chainComponents.mp hX
  refine mem_chainComponents.mpr ⟨y, Finset.mem_union_left _ hy, ?_⟩
  ext z
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hz, hj⟩
    exact ⟨Finset.mem_union_left _ hz, chainConnected_mono Finset.subset_union_left hj⟩
  · rintro ⟨_, hj⟩
    obtain ⟨h1, h2⟩ := chainConnected_of_separated hsep hy hj
    exact ⟨h2, h1⟩
open Classical in
theorem self_mem_chainComponents_union_of_separated (hsep : ∀ a ∈ A, ∀ b ∈ B, r < supDist a b)
    (hne : A.Nonempty) (hconn : ∀ y ∈ A, ∀ z ∈ A, ChainConnected r A y z) :
    A ∈ chainComponents r (A ∪ B) := by
  obtain ⟨y, hy⟩ := hne
  refine mem_chainComponents_union_of_separated hsep (mem_chainComponents.mpr ⟨y, hy, ?_⟩)
  ext z
  simp only [Finset.mem_filter]
  exact ⟨fun hz => ⟨hz, hconn y hy z hz⟩, fun h => h.1⟩
end YangMills.Construction.TorusLumps
end
