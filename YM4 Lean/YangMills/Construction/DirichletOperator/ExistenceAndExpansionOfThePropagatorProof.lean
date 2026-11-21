import YangMills.Construction.DirichletOperator.CornerBoundsOnTheToriOfTheCubesProof
import YangMills.Construction.DirichletOperator.BlockNormCalculus
import YangMills.Construction.DirichletOperator.FloorsOfThePropagator
import YangMills.Construction.DirichletOperator.LawsOfTheApproximateInverse
import YangMills.Construction.RegionSequence.CellsAndAdjoints
import YangMills.Construction.RegionSequence.DifferenceAdjointsByParts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set Filter Topology
open Dirichlet Torus RegionSequence RegionSequence.NestedRegions PartitionCubes Propagator
  PropagatorThresholds RemainderEstimates
namespace PropagatorProof
theorem finite_fineSite (hl : Torus.TorusLengthsStatement) (𝒯 : RegionSequence.NestedRegions) :
    Finite 𝒯.FineSite := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineSite <;> assumption
theorem finite_fineBond (hl : Torus.TorusLengthsStatement) (𝒯 : RegionSequence.NestedRegions) :
    Finite 𝒯.FineBond := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineBond <;> assumption
theorem hasSum_congr_terms {f g : ℕ → ℝ} {s : ℝ} (e : ∀ i, f i = g i) (h : HasSum g s) :
    HasSum f s := by
  rw [show f = g from funext e]
  exact h
section Inner
variable {𝒮 : RegionSequence.NestedRegions} [Fintype 𝒮.FineBond]
theorem bondInner_eq_sum (A B : 𝒮.FineBond → ℝ) :
    bondInner A B = 𝒮.ξ ^ 4 * ∑ b, A b * B b := by
  rw [bondInner, finsum_eq_sum_of_fintype]
theorem bondInner_comm (A B : 𝒮.FineBond → ℝ) : bondInner A B = bondInner B A := by
  simp only [bondInner_eq_sum, mul_comm (A _)]
theorem bondInner_add_left (A B C : 𝒮.FineBond → ℝ) :
    bondInner (A + B) C = bondInner A C + bondInner B C := by
  simp only [bondInner_eq_sum, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]
theorem bondInner_sub_left (A B C : 𝒮.FineBond → ℝ) :
    bondInner (A - B) C = bondInner A C - bondInner B C := by
  simp only [bondInner_eq_sum, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, mul_sub]
theorem eq_zero_of_bondInner_self (D : 𝒮.FineBond → ℝ) (h : bondInner D D = 0) : D = 0 := by
  rw [bondInner_eq_sum] at h
  have hs : ∑ b, D b * D b = 0 := (mul_eq_zero.mp h).resolve_left (pow_pos 𝒮.ξ_pos 4).ne'
  have hz := (Finset.sum_eq_zero_iff_of_nonneg fun b _ => mul_self_nonneg (D b)).mp hs
  funext b
  exact mul_self_eq_zero.mp (hz b (Finset.mem_univ b))
end Inner
section SelfAdjoint
variable {𝒮 : RegionSequence.NestedRegions} [Fintype 𝒮.FineBond]
  {D : (𝒮.FineBond → ℝ) → 𝒮.FineBond → ℝ}
end SelfAdjoint
section FormVectors
abbrev FormVec (𝒮 : RegionSequence.NestedRegions) : Type := (formCutSpace 𝒮).space
variable {𝒮 : RegionSequence.NestedRegions}
open Classical in
def bondIndicator (c : 𝒮.FineBond) : FormVec 𝒮 :=
  ⟨(fun b => if b = c ∧ c ∈ 𝒮.bonds then 1 else 0 : 𝒮.FineBond → ℝ), by
    show _ ∈ 𝒮.oneForms
    intro b hb
    refine if_neg ?_
    rintro ⟨rfl, hc⟩
    exact hb hc⟩
section Finite
variable [Fintype 𝒮.FineBond]
variable [Fintype 𝒮.allCentres]
end Finite
end FormVectors
section CubeChains
variable {𝒮 : RegionSequence.NestedRegions} {M : ℕ}
end CubeChains
end PropagatorProof
end YangMills.Construction
