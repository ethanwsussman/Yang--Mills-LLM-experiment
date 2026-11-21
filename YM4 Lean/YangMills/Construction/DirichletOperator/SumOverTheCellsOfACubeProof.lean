import YangMills.Construction.DirichletOperator.CellsOfACube
import YangMills.Construction.DirichletOperator.SeparatedSequenceOfThePropagator
import YangMills.Construction.DirichletOperator.WeightedDistanceInACubeProof
import YangMills.Construction.LawInAState.DecayOverATorusProof
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set
open Torus RegionSequence RegionSequence.NestedRegions
namespace PartitionCubes.CellCount
section SpacingLattice
variable {S σ : ℝ}
theorem addCircle_coe_add_zsmul (x : ℝ) (n : ℤ) :
    ((x + n • S : ℝ) : AddCircle S) = (x : AddCircle S) := by
  have h : ((n • S : ℝ) : AddCircle S) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨n, rfl⟩
  rw [AddCircle.coe_add, h, add_zero]
theorem spacingLattice_finite (hS : 0 < S) (hσ : 0 < σ) {k : ℤ} (hk : S = k * σ) :
    (spacingLattice 4 S σ : Set (PeriodicTorus 4 S)).Finite := by
  have hkpos : 0 < k := by
    have h : (0 : ℝ) < k := by
      by_contra h
      have h' := mul_nonpos_of_nonpos_of_nonneg (not_lt.1 h) hσ.le
      linarith
    exact_mod_cast h
  have hfin : (Set.pi univ fun _ : Fin 4 => Ico (0 : ℤ) k).Finite :=
    Set.Finite.pi fun _ => Set.finite_Ico _ _
  refine (hfin.image fun a : Fin 4 → ℤ => torusProj 4 S fun μ => (a μ : ℝ) * σ).subset ?_
  rintro x ⟨a, rfl⟩
  refine ⟨fun μ => a μ % k, fun μ _ => ⟨Int.emod_nonneg _ hkpos.ne', Int.emod_lt_of_pos _ hkpos⟩, ?_⟩
  funext μ
  have h₁ : a μ % k + k * (a μ / k) = a μ := Int.emod_add_mul_ediv _ _
  have h₂ : (a μ : ℝ) = ((a μ % k : ℤ) : ℝ) + k * ((a μ / k : ℤ) : ℝ) := by exact_mod_cast h₁.symm
  have h₃ : (a μ : ℝ) * σ = ((a μ % k : ℤ) : ℝ) * σ + (a μ / k) • S := by
    rw [zsmul_eq_mul, hk]
    linear_combination σ * h₂
  show (((((a μ % k : ℤ) : ℝ) * σ : ℝ)) : AddCircle S) = (((a μ : ℝ) * σ : ℝ) : AddCircle S)
  rw [h₃, addCircle_coe_add_zsmul]
end SpacingLattice
section Exponential
theorem summable_pi_prod {g : ℤ → ℝ} (hg : Summable g) (h0 : ∀ n, 0 ≤ g n) (n : ℕ) :
    Summable fun v : Fin n → ℤ => ∏ i, g (v i) := by
  induction n with
  | zero => exact summable_of_hasFiniteSupport (Set.toFinite _)
  | succ n ih =>
    refine ((Fin.consEquiv fun _ => ℤ).summable_iff).1 ?_
    have h := hg.mul_of_nonneg ih h0 fun v => Finset.prod_nonneg fun i _ => h0 _
    refine h.congr fun x => ?_
    simp [Fin.prod_univ_succ, Fin.consEquiv]
end Exponential
section Cells
theorem scaleSpacing_eq_pow_mul (L : ℕ) (ξ : ℝ) {n j : ℕ} (h : n ≤ j) :
    scaleSpacing L ξ (j : ℤ) = ((L ^ (j - n) : ℕ) : ℝ) * scaleSpacing L ξ (n : ℤ) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  simp only [scaleSpacing, zpow_natCast, Nat.add_sub_cancel_left]
  push_cast
  rw [pow_add]
  ring
variable {𝒮 : RegionSequence.NestedRegions} {M : ℕ}
theorem scale_pos (𝒮 : RegionSequence.NestedRegions) (n : ℕ) : 0 < 𝒮.scale n := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.scale_pos <;> assumption
end Cells
end PartitionCubes.CellCount
end YangMills.Construction
