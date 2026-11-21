import YangMills.Construction.Dirichlet.CutoffDifferenceBoundsProof
import YangMills.Construction.Dirichlet.HolderProductBoundProof
import YangMills.Construction.Dirichlet.LocalRegionGreenEstimates
import YangMills.Construction.DirichletOperator.ChainOfRemaindersProof
import YangMills.Construction.FreeKernel.PoissonInteriorEstimates
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Dirichlet.LocalRegion
open Set Torus RegionEnergy
namespace GridLift
section
variable {d : ℕ} {S : ℝ}
theorem torusProj_add (v w : Fin d → ℝ) :
    torusProj d S (v + w) = torusProj d S v + torusProj d S w := by apply _root_.YangMills.Construction.Dirichlet.Commutator.torusProj_add <;> assumption
theorem torusProj_sub (v w : Fin d → ℝ) :
    torusProj d S (v - w) = torusProj d S v - torusProj d S w := by apply _root_.YangMills.Construction.Dirichlet.CutoffDifferences.torusProj_sub <;> assumption
theorem supNorm_torusProj_le (v : Fin d → ℝ) : supNorm (torusProj d S v) ≤ ‖v‖ :=
  csInf_le ⟨0, by rintro _ ⟨w, -, rfl⟩; exact norm_nonneg _⟩ ⟨v, rfl, rfl⟩
theorem supNorm_sub_le_add (p q r : PeriodicTorus d S) :
    supNorm (p - r) ≤ supNorm (p - q) + supNorm (q - r) := by apply _root_.YangMills.Construction.Dirichlet.Commutator.supNorm_sub_le_add <;> assumption
theorem supNorm_sub_comm (p q : PeriodicTorus d S) : supNorm (p - q) = supNorm (q - p) := by apply _root_.YangMills.Construction.Dirichlet.Commutator.supNorm_sub_comm <;> assumption
theorem lOneNorm_nonneg (p : PeriodicTorus d S) : 0 ≤ lOneNorm p := by apply _root_.YangMills.Construction.Dirichlet.HolderProduct.lOneNorm_nonneg' <;> assumption
end
section
variable {d : ℕ} {S ξ : ℝ}
theorem supLength_le_iff [Nonempty (Fin d)] {v : Fin d → ℝ} {s : ℝ} :
    InfiniteLattice.supLength v ≤ s ↔ ∀ μ, |v μ| ≤ s :=
  ciSup_le_iff (Set.finite_range _).bddAbove
theorem mem_gridCube_iff [Nonempty (Fin d)] {x₀ v : InfiniteLattice.GridSite d ξ} {s : ℝ}
    (hs : 0 ≤ s) : v ∈ InfiniteLattice.gridCube x₀ s ↔ ‖v.1 - x₀.1‖ ≤ s := by
  rw [pi_norm_le_iff_of_nonneg hs]
  simp only [InfiniteLattice.gridCube, Set.mem_ofPred_eq, supLength_le_iff, Real.norm_eq_abs]
  rfl
end
section
variable {d : ℕ} {S ξ : ℝ}
theorem restrictTo_of_mem {X : Set (PeriodicTorus d S)} (u : LatticeSite d S ξ → ℝ)
    {x : LatticeSite d S ξ} (hx : (x : PeriodicTorus d S) ∈ X) : restrictTo X u x = u x :=
  Set.indicator_of_mem (s := {x : LatticeSite d S ξ | (x : PeriodicTorus d S) ∈ X}) hx _
theorem restrictTo_of_not_mem {X : Set (PeriodicTorus d S)} (u : LatticeSite d S ξ → ℝ)
    {x : LatticeSite d S ξ} (hx : (x : PeriodicTorus d S) ∉ X) : restrictTo X u x = 0 := by apply _root_.YangMills.Construction.Dirichlet.RemainderChains.restrictTo_of_not_mem <;> assumption
theorem supNormOn_nonneg (X : Set (PeriodicTorus d S)) (f : LatticeSite d S ξ → ℝ) :
    0 ≤ supNormOn X f :=
  Real.sSup_nonneg (by rintro _ ⟨x, -, rfl⟩; exact abs_nonneg _)
theorem abs_le_supNormOn [Finite (LatticeSite d S ξ)] {X : Set (PeriodicTorus d S)}
    (f : LatticeSite d S ξ → ℝ) {x : LatticeSite d S ξ}
    (hx : (x : PeriodicTorus d S) ∈ X) : |f x| ≤ supNormOn X f := by apply _root_.YangMills.Construction.Dirichlet.RemainderChains.le_supNormOn <;> assumption
end
section
variable {d L : ℕ} {S aMinus aPlus : ℝ} (𝒮 : BlockSetting d L aMinus aPlus S)
theorem supNorm_unitStep_le (ν : Fin d) (hξ : 0 < 𝒮.ξ) (x : LatticeSite d S 𝒮.ξ) :
    supNorm (((x + unitStep d S 𝒮.ξ ν : LatticeSite d S 𝒮.ξ) : PeriodicTorus d S)
      - (x : PeriodicTorus d S)) ≤ 𝒮.ξ := by
  have h := supNorm_torusProj_le (d := d) (S := S) (Pi.single ν 𝒮.ξ)
  have he : ((x + unitStep d S 𝒮.ξ ν : LatticeSite d S 𝒮.ξ) : PeriodicTorus d S) -
      (x : PeriodicTorus d S) = torusProj d S (Pi.single ν 𝒮.ξ) := by
    simp [unitStep]
  rw [he]
  refine h.trans ?_
  rw [pi_norm_le_iff_of_nonneg hξ.le]
  intro μ
  by_cases hμ : μ = ν
  · subst hμ; simp [abs_of_pos hξ]
  · simp [Pi.single_eq_of_ne hμ, hξ.le]
end
end GridLift
open GridLift
end YangMills.Construction.Dirichlet.LocalRegion
