import YangMills.Construction.Dirichlet.BilinearForms
import YangMills.Construction.Dirichlet.BlockGreenLinear
import YangMills.Construction.Dirichlet.CentresAndCells
import YangMills.Construction.Dirichlet.CollarGeometry
import YangMills.Construction.Dirichlet.CommutatorBounds
import YangMills.Construction.Dirichlet.WeightedLengthEstimates
import YangMills.Construction.Dirichlet.WalkExpansionTerms
import Mathlib
import YangMills.Construction.DirichletOperator.ConsequencesOfTheWalkFloors
import YangMills.Construction.Torus.TorusLengths
import YangMills.Construction.WeightedGreen.DecayRateBounds
set_option autoImplicit false

section
open Set
noncomputable section
namespace YangMills.Construction.Dirichlet.CubeEstimates
open YangMills.Construction.Torus YangMills.Construction.WeightedGreen
open YangMills.Construction.Dirichlet.WalkExpansion
variable {d L : ℕ} {S aMinus aPlus : ℝ}
def cutoffSolution (𝒮 : BlockSetting d L aMinus aPlus S) (Q : CentredCube d S)
    (E : Set (LatticeBond d S 𝒮.ξ)) (f : LatticeSite d S 𝒮.ξ → ℝ) (F : BondField d S 𝒮.ξ) :
    LatticeSite d S 𝒮.ξ → ℝ :=
  pointwiseMul (𝒮.latticeCutoff Q) (RegionBounds.regionSolution 𝒮 (𝒮.innerRegion Q) E f F)
end YangMills.Construction.Dirichlet.CubeEstimates
end
end

open Set
noncomputable section
namespace YangMills.Construction.Dirichlet.CubeEstimates
open YangMills.Construction.Torus YangMills.Construction.Dirichlet YangMills.Construction.Dirichlet.RegionBounds
section Lengths
variable {d : ℕ} {S ξ : ℝ}
theorem supNorm_le_norm_of_proj {p : PeriodicTorus d S} {v : Fin d → ℝ}
    (h : torusProj d S v = p) : supNorm p ≤ ‖v‖ :=
  csInf_le ⟨0, by rintro _ ⟨w, -, rfl⟩; exact norm_nonneg _⟩ ⟨v, h, rfl⟩
theorem lOneNorm_le_sum_abs_of_proj {p : PeriodicTorus d S} {v : Fin d → ℝ}
    (h : torusProj d S v = p) : lOneNorm p ≤ ∑ μ, |v μ| :=
  csInf_le ⟨0, by rintro _ ⟨w, -, rfl⟩; exact Finset.sum_nonneg fun _ _ => abs_nonneg _⟩ ⟨v, h, rfl⟩
theorem lOneNorm_unitStep_le (hξ : 0 ≤ ξ) (μ : Fin d) :
    lOneNorm ((unitStep d S ξ μ : LatticeSite d S ξ) : PeriodicTorus d S) ≤ ξ := by
  have h := lOneNorm_le_sum_abs_of_proj
    (p := ((unitStep d S ξ μ : LatticeSite d S ξ) : PeriodicTorus d S))
    (v := Pi.single μ ξ) rfl
  refine h.trans (le_of_eq ?_)
  rw [Finset.sum_eq_single μ]
  · simp [abs_of_nonneg hξ]
  · intro ν _ hν
    simp [Pi.single_eq_of_ne hν]
  · simp
theorem siteLOneDist_nonneg (hLen : LengthAxioms d S) (x x' : LatticeSite d S ξ) :
    0 ≤ siteLOneDist x x' :=
  hLen.lOneNorm_nonneg _
end Lengths
section Calculus
variable {d : ℕ} {S ξ : ℝ}
theorem abs_mul_le_mul_of_abs_le {a b A C : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ C) :
    |a * b| ≤ A * C := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)
theorem abs_le_supNormAll [Finite (LatticeSite d S ξ)] (f : LatticeSite d S ξ → ℝ)
    (x : LatticeSite d S ξ) : |f x| ≤ supNormAll f := by
  refine le_csSup ?_ ⟨x, mem_univ _, rfl⟩
  refine ((Set.finite_range fun x => |f x|).subset ?_).bddAbove
  rintro r ⟨x, -, rfl⟩
  exact ⟨x, rfl⟩
theorem zero_le_supNormAll (f : LatticeSite d S ξ → ℝ) : 0 ≤ supNormAll f := by
  refine Real.sSup_nonneg ?_
  rintro r ⟨x, -, rfl⟩
  exact abs_nonneg _
theorem zero_le_fieldSupNorm (F : BondField d S ξ) : 0 ≤ fieldSupNorm F :=
  Real.iSup_nonneg fun _ => zero_le_supNormAll _
theorem fieldSupNorm_zero_eq : fieldSupNorm (0 : BondField d S ξ) = 0 := by
  refine le_antisymm (Real.iSup_le (fun μ => ?_) le_rfl) (zero_le_fieldSupNorm _)
  refine Real.sSup_le ?_ le_rfl
  rintro r ⟨x, -, rfl⟩
  simp
end Calculus
section Local
variable {d L : ℕ} {S aMinus aPlus : ℝ} {B : BlockSetting d L aMinus aPlus S}
theorem zero_le_holderFactor (hLen : LengthAxioms d S) {y : PeriodicTorus d S}
    (hs : 0 < B.centreSpacing y) (α : ℝ) (x x' : LatticeSite d S B.ξ) :
    0 ≤ holderFactor B α y x x' :=
  Real.rpow_nonneg (div_nonneg (siteLOneDist_nonneg hLen x x') hs.le) α
end Local
section Partition
variable {d L : ℕ} {S aMinus aPlus : ℝ} {B : BlockSetting d L aMinus aPlus S}
theorem le_centreSpacing (hL : (1 : ℝ) ≤ L) (y : PeriodicTorus d S) :
    B.ξ ≤ B.centreSpacing y := by
  have hξ := B.isSeparatedChain.scale_pos
  have h1 : (1 : ℝ) ≤ (L : ℝ) ^ (shellIndex L B.ξ B.Ω y) := one_le_pow₀ hL
  unfold BlockSetting.centreSpacing shellSpacing scaleSpacing
  rw [zpow_natCast]
  nlinarith
theorem centreOf_eq (hB : CentreCellFacts B) {y : PeriodicTorus d S} (hy : y ∈ B.centres)
    {x : LatticeSite d S B.ξ} (hx : (x : PeriodicTorus d S) ∈ B.cell y) :
    B.centreOf x = y := by
  obtain ⟨y₀, -, huniq⟩ := hB.existsUnique_cell x (hB.cell_subset y hy hx)
  have hsp : B.centreOf x ∈ B.centres ∧ (x : PeriodicTorus d S) ∈ B.cell (B.centreOf x) :=
    Classical.epsilon_spec (p := fun y => y ∈ B.centres ∧ (x : PeriodicTorus d S) ∈ B.cell y)
      ⟨y, hy, hx⟩
  rw [huniq _ hsp, huniq y ⟨hy, hx⟩]
end Partition
end YangMills.Construction.Dirichlet.CubeEstimates
