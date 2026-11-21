import YangMills.Construction.RegionSequence.DifferenceAdjointsByParts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set
open Dirichlet Torus
namespace RegionSequence.GradientAdjointsOnTorus
open NestedRegions
theorem finite_fineSite (hT : Torus.TorusLengthsStatement) (𝒮 : NestedRegions) :
    Finite 𝒮.FineSite := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineSite <;> assumption
def fineBondEquiv (𝒮 : NestedRegions) : 𝒮.FineBond ≃ 𝒮.FineSite × Fin 4 where
  toFun b := (b.source, b.dir)
  invFun p := ⟨p.1, p.2⟩
  left_inv b := by cases b; rfl
  right_inv p := by cases p; rfl
variable {𝒮 : NestedRegions}
theorem innerSum_comm (f g : 𝒮.FineSite → ℝ) : innerSum f g = innerSum g f := by
  simp only [innerSum, mul_comm (f _)]
theorem bondInner_comm (A B : 𝒮.FineBond → ℝ) : bondInner A B = bondInner B A := by
  simp only [bondInner, mul_comm (A _)]
theorem bondInner_eq_sum_comp (hF : Finite 𝒮.FineSite) (A B : 𝒮.FineBond → ℝ) :
    bondInner A B = ∑ ν, innerSum (comp A ν) (comp B ν) := by
  have := Fintype.ofFinite 𝒮.FineSite
  simp only [bondInner, innerSum, comp]
  rw [← finsum_comp_equiv (fineBondEquiv 𝒮).symm]
  simp only [finsum_eq_sum_of_fintype]
  rw [Fintype.sum_prod_type_right, Finset.mul_sum]
  rfl
theorem innerSum_sum_left (hF : Finite 𝒮.FineSite) (f : Fin 4 → 𝒮.FineSite → ℝ)
    (g : 𝒮.FineSite → ℝ) :
    innerSum (fun x => ∑ ν, f ν x) g = ∑ ν, innerSum (f ν) g := by
  have := Fintype.ofFinite 𝒮.FineSite
  simp only [innerSum, finsum_eq_sum_of_fintype, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
end RegionSequence.GradientAdjointsOnTorus
end YangMills.Construction
