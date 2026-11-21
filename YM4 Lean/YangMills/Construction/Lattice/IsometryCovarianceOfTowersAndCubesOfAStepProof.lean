import YangMills.Construction.Lattice.CubesAndSetsOfAStepUnderIsometries
import YangMills.Construction.Lattice.GluedSequencesAndSetsUnderIsometries
import YangMills.Construction.Lattice.IsometryCovarianceOfTowersAndCubesOfAStep
import YangMills.Construction.Lattice.IsometryGroupsAndTheirActionOnRegions
import YangMills.Construction.Lattice.LayeredGluedSequencesAndSetsUnderIsometries
import YangMills.Construction.Lattice.ObjectsOfSequencesUnderIsometries
import YangMills.Construction.Lattice.TowersOfRegionsUnderIsometries
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
namespace TowerCovariance
variable {L m : ℕ}
theorem le_levelDepth {K k : ℕ} {i : ℤ} {D : ℕ → Set (FourTorus L m)}
    (h : IsDeterminingChainFrom K k i D) : ∀ q ≤ k, i ≤ levelDepth K q := by
  intro q hq
  obtain ⟨a, h₁, h₂, -⟩ := h.2.2 q hq
  exact h₁.trans h₂
theorem imageChain_isDeterminingChainFrom {K k : ℕ} {i : ℤ} {σ : FourTorus L m ≃ FourTorus L m}
    {D : ℕ → Set (FourTorus L m)} (hi : -(m : ℤ) ≤ i) (hR : ∀ a : ℤ, i ≤ a → MapsRegions σ a)
    (h : IsDeterminingChainFrom K k i D) :
    IsDeterminingChainFrom K k i (imageChain σ D) := by
  obtain ⟨hk, ⟨hdec, -⟩, hreg⟩ := h
  have hreg' : ∀ q ≤ k, ∃ a : ℤ, i ≤ a ∧ a ≤ levelDepth K q ∧
      IsPartitionRegion a (imageChain σ D q) := by
    intro q hq
    obtain ⟨a, h₁, h₂, h₃⟩ := hreg q hq
    exact ⟨a, h₁, h₂, ((hR a h₁).1 (D q)).2 h₃⟩
  refine ⟨hk, ⟨?_, ?_⟩, hreg'⟩
  · rintro j hj _ ⟨y, hy, rfl⟩
    exact ⟨y, hdec j hj hy, rfl⟩
  · intro q hq
    obtain ⟨a, h₁, h₂, h₃⟩ := hreg' q hq
    exact ⟨a, hi.trans h₁, h₂, h₃⟩
end TowerCovariance
open TowerCovariance in
theorem isometriesPreserveTowersAndStepCubes_holds
    (hT : IsometriesPreserveTowers)
    (hO : IsometryPreservesChainObjects)
    (hJ : IsometriesPreserveGluing)
    (hY : IsometriesPreserveMultiShellGluing)
    (hC : StepCubesAndSetsIsometryInvariant)
    (hG : LatticeIsometryGroupActionStatement) :
    IsometriesPreserveTowersAndStepCubes := by
  refine ⟨fun L m i σ hL hm hi hσ => ?_, fun c m K x i σ hL hm hi hσ =>
    hC c m K x i σ hL hm hi hσ⟩
  have hR : ∀ a : ℤ, i ≤ a → MapsRegions σ a := fun a ha =>
    ((hG L m i hL hm hi).2.2.2.2 σ hσ a ha).2
  have hTow := hT L m i σ hL hm hi hσ
  have hObj := hO L m i σ hL hm hi hσ
  refine ⟨hTow, ?_, ?_, ?_, hJ L m i σ hL hm hi hσ, hY L m i σ hL hm hi hσ⟩
  · intro K k D hD
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, -⟩ :=
      hObj K k D (imageChain σ D) (le_levelDepth hD) (fun _ _ => rfl)
    exact ⟨imageChain_isDeterminingChainFrom hi hR hD, h₁, h₂, h₃, h₄, fun b _ => h₅ b,
      fun p _ => h₆ p⟩
  · intro K k D hD
    obtain ⟨-, -, -, -, -, -, h₁, h₂, h₃, h₄, h₅⟩ :=
      hObj K k D (imageChain σ D) (le_levelDepth hD) (fun _ _ => rfl)
    exact ⟨h₁, h₂, h₃, h₄, h₅⟩
  · intro K j n D _ hj hD hin
    have hjn : i ≤ levelDepth K j := hin.trans (by simp only [scaledCubeIndex]; omega)
    have hdepth : ∀ q ≤ j, i ≤ levelDepth K q := fun q hq =>
      hjn.trans (by simp only [levelDepth]; omega)
    have htower : ∀ q ≤ j, shrinkingTower K n 0 (σ '' D) q = σ '' shrinkingTower K n 0 D q := by
      have h := (hTow K j n 0 0 0 j D hj (Nat.zero_le n) (by omega) hD).2.2
      rw [Nat.zero_add] at h
      exact h hin
    obtain ⟨h₁, -, -, -, -, -, -, h₂, -⟩ :=
      hObj K j (shrinkingTower K n 0 D) (shrinkingTower K n 0 (σ '' D)) hdepth htower
    exact ⟨h₁, h₂⟩
end YangMills.Construction.PeriodicLattice
end
