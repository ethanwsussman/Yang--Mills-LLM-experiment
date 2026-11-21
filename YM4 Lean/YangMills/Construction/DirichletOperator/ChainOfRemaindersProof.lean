import YangMills.Construction.Dirichlet.BlockGreenLinear
import YangMills.Construction.Dirichlet.CentresAndCells
import YangMills.Construction.Dirichlet.CoverCubeCount
import YangMills.Construction.Dirichlet.WeightedLengthEstimates
import YangMills.Construction.DirichletOperator.ConsequencesOfTheWalkFloors
import YangMills.Construction.DirichletOperator.RemainderOnABlock
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Torus YangMills.Construction.Dirichlet YangMills.Construction.WeightedGreen YangMills.Construction.Dirichlet.WalkExpansion
noncomputable section
namespace YangMills.Construction.Dirichlet.RemainderChains
section ListsOfLength
variable {α β X : Type*}
end ListsOfLength
section SupNorms
variable {d : ℕ} {S ξ : ℝ}
theorem supNormOn_nonneg (X : Set (PeriodicTorus d S)) (f : LatticeSite d S ξ → ℝ) :
    0 ≤ supNormOn X f := by
  apply Real.sSup_nonneg
  rintro r ⟨x, -, hr⟩
  rw [hr]
  exact abs_nonneg (f x)
theorem le_supNormOn [Finite (LatticeSite d S ξ)] {X : Set (PeriodicTorus d S)}
    (f : LatticeSite d S ξ → ℝ) {x : LatticeSite d S ξ}
    (hx : (x : PeriodicTorus d S) ∈ X) : |f x| ≤ supNormOn X f := by
  have hfin : Set.Finite
      {r | ∃ y : LatticeSite d S ξ, (y : PeriodicTorus d S) ∈ X ∧ r = |f y|} := by
    refine (Set.finite_range fun y => |f y|).subset ?_
    rintro r ⟨y, -, hr⟩
    exact ⟨y, hr.symm⟩
  exact le_csSup hfin.bddAbove ⟨x, hx, rfl⟩
theorem restrictTo_of_mem {X : Set (PeriodicTorus d S)} (f : LatticeSite d S ξ → ℝ)
    {x : LatticeSite d S ξ} (hx : (x : PeriodicTorus d S) ∈ X) : restrictTo X f x = f x := by
  unfold restrictTo
  exact Set.indicator_of_mem (show x ∈ {y : LatticeSite d S ξ | (y : PeriodicTorus d S) ∈ X} from hx) f
theorem restrictTo_of_not_mem {X : Set (PeriodicTorus d S)} (f : LatticeSite d S ξ → ℝ)
    {x : LatticeSite d S ξ} (hx : (x : PeriodicTorus d S) ∉ X) : restrictTo X f x = 0 := by
  unfold restrictTo
  exact Set.indicator_of_notMem (show x ∉ {y : LatticeSite d S ξ | (y : PeriodicTorus d S) ∈ X} from hx) f
end SupNorms
section Cells
variable {d L : ℕ} {S aLow aHigh : ℝ} (𝒮 : BlockSetting d L aLow aHigh S)
theorem blockDist_self_nonpos (y : PeriodicTorus d S) : 𝒮.blockDist y y ≤ 0 := by
  obtain ⟨v, hv⟩ : ∃ v : Fin d → ℝ, torusProj d S v = y := by
    choose v hv using fun μ => QuotientAddGroup.mk_surjective (y μ)
    exact ⟨v, funext hv⟩
  have hpt : ∀ τ : ℝ, (⟨v, 0⟩ : TorusSegment d).pointAt S τ = y := by
    intro τ
    simp [TorusSegment.pointAt, hv]
  have hcar : segmentUnion S [(⟨v, 0⟩ : TorusSegment d)] = {y} := by
    ext p
    simp only [segmentUnion, List.mem_singleton, exists_eq_left, hpt, mem_ofPred_eq,
      mem_singleton_iff]
    exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨0, by simp, h⟩⟩
  have h0 : chainWeightedLength L 𝒮.ξ 𝒮.t 𝒮.Ω [(⟨v, 0⟩ : TorusSegment d)] = 0 := by
    simp [chainWeightedLength, lengthWithin, TorusSegment.lOneLength]
  unfold BlockSetting.blockDist chainWeightedDist
  by_cases hb : BddBelow {r | ∃ Γ : List (TorusSegment d), IsConnected (segmentUnion S Γ) ∧
      y ∈ segmentUnion S Γ ∧ y ∈ segmentUnion S Γ ∧ r = chainWeightedLength L 𝒮.ξ 𝒮.t 𝒮.Ω Γ}
  · refine csInf_le hb ⟨[⟨v, 0⟩], ?_, ?_, ?_, h0.symm⟩
    · rw [hcar]
      exact isConnected_singleton
    · rw [hcar]
      exact mem_singleton y
    · rw [hcar]
      exact mem_singleton y
  · rw [Real.sInf_of_not_bddBelow hb]
variable (E : CentredCube d S → Set (LatticeBond d S 𝒮.ξ))
end Cells
end YangMills.Construction.Dirichlet.RemainderChains
