import YangMills.Construction.Dirichlet.CollarGeometry
import YangMills.Construction.Dirichlet.ShellCrossingChains
import YangMills.Construction.Torus.PartitionsShellsCubes
import YangMills.Construction.Torus.TorusLengths
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Dirichlet.Crossing
open YangMills.Construction.Torus
section Curves
variable {X : Type*} [TopologicalSpace X] {g : ℝ → X} {U K : Set X}
end Curves
variable {d L : ℕ} {S aMinus aPlus : ℝ} (Φ : BlockSetting d L aMinus aPlus S)
structure CurveData (g : ℝ → PeriodicTorus d S) (T : ℝ) (len : ℝ → ℝ → ℝ) : Prop where
  continuousOn : ContinuousOn g (Icc 0 T)
  lower : ∀ i ≤ Φ.t, ∀ u v, 0 ≤ u → u ≤ v → v ≤ T → (g '' Icc u v ∩ Φ.Ω (i + 1)).Finite →
    scaledGap Φ i (g u) (g v) ≤ len u v
  superadd : ∀ u v w, 0 ≤ u → u ≤ v → v ≤ w → w ≤ T → len u v + len v w ≤ len u w
  nonneg : ∀ u v, 0 ≤ len u v
variable {Φ}
theorem lengthWithin_nonneg (Γ : List (TorusSegment d)) (X : Set (PeriodicTorus d S)) :
    0 ≤ lengthWithin Γ X := by
  apply List.sum_nonneg
  intro v hv
  obtain ⟨seg, -, rfl⟩ := List.mem_map.1 hv
  exact mul_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _) ENNReal.toReal_nonneg
theorem chainWeightedLength_nonneg (hL : 0 < (L : ℝ)) {ξ : ℝ} (hξ : 0 < ξ) (t : ℕ)
    (Ω : ℕ → Set (PeriodicTorus d S)) (Γ : List (TorusSegment d)) :
    0 ≤ chainWeightedLength L ξ t Ω Γ := by
  have hinv : ∀ k : ℤ, 0 ≤ (scaleSpacing L ξ k)⁻¹ := fun k =>
    (inv_pos.2 (mul_pos (zpow_pos hL k) hξ)).le
  unfold chainWeightedLength
  refine add_nonneg (Finset.sum_nonneg fun i _ => ?_) ?_
  · exact mul_nonneg (hinv i) (lengthWithin_nonneg _ _)
  · exact mul_nonneg (hinv 0) (lengthWithin_nonneg _ _)
theorem mem_interior_cubeAt (hlen : Torus.LengthAxioms d S) {σ : ℝ} (hσ : 0 < σ)
    (y : PeriodicTorus d S) : y ∈ interior (cubeAt y σ) := by
  have hopen : IsOpen {p : PeriodicTorus d S | supNorm (p - y) < σ / 2} :=
    isOpen_lt (hlen.continuous_supNorm.comp (continuous_id.sub continuous_const)) continuous_const
  refine mem_interior.2 ⟨{p | supNorm (p - y) < σ / 2},
    fun p (hp : supNorm (p - y) < σ / 2) => le_of_lt hp, hopen, ?_⟩
  show supNorm (y - y) < σ / 2
  rw [sub_self, hlen.supNorm_zero]
  exact half_pos hσ
end YangMills.Construction.Dirichlet.Crossing
