import YangMills.Construction.RegionSequence.DifferenceAdjointsByParts
import YangMills.Construction.RegionSequence.TorusHodgeIdentity
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Dirichlet YangMills.Construction.Torus
noncomputable section
namespace YangMills.Construction.RegionSequence.TorusHodge
theorem finite_fineSite (hL : TorusLengthsStatement) (𝒮 : NestedRegions) : Finite 𝒮.FineSite := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineSite <;> assumption
open NestedRegions
def fineBondEquiv (𝒮 : NestedRegions) : 𝒮.FineBond ≃ 𝒮.FineSite × Fin 4 where
  toFun b := (b.source, b.dir)
  invFun p := ⟨p.1, p.2⟩
  left_inv b := by cases b; rfl
  right_inv p := by cases p; rfl
def shiftEquiv (𝒮 : NestedRegions) (ν : Fin 4) : 𝒮.FineBond ≃ 𝒮.FineBond where
  toFun := shiftUp ν
  invFun := shiftDown ν
  left_inv b := by cases b; simp [shiftUp, shiftDown]
  right_inv b := by cases b; simp [shiftUp, shiftDown]
theorem eq_of_forall_weighted_sum {ι : Type} [Fintype ι] {c : ℝ} (hc : 0 < c) {v v' : ι → ℝ}
    (h : ∀ u : ι → ℝ, c * ∑ i, v i * u i = c * ∑ i, v' i * u i) : v = v' := by
  have h0 := mul_left_cancel₀ hc.ne' (h (v - v'))
  have h1 : ∑ i, (v i - v' i) ^ 2 = 0 := by
    have : ∑ i, (v i - v' i) ^ 2 =
        ∑ i, v i * (v - v') i - ∑ i, v' i * (v - v') i := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by simp only [Pi.sub_apply]; ring
    rw [this, h0, sub_self]
  funext i
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (v i - v' i)).mp h1 i
    (Finset.mem_univ i)
  have h3 : v i - v' i = 0 := by simpa using h2
  linarith
theorem sum_ordered_pairs (G : {p : Fin 4 × Fin 4 // p.1 < p.2} → ℝ) :
    ∑ q, G q = G ⟨(0, 1), by decide⟩ + G ⟨(0, 2), by decide⟩ + G ⟨(0, 3), by decide⟩ +
      G ⟨(1, 2), by decide⟩ + G ⟨(1, 3), by decide⟩ + G ⟨(2, 3), by decide⟩ := by
  have hu : (Finset.univ : Finset {p : Fin 4 × Fin 4 // p.1 < p.2}) =
      {⟨(0, 1), by decide⟩, ⟨(0, 2), by decide⟩, ⟨(0, 3), by decide⟩, ⟨(1, 2), by decide⟩,
        ⟨(1, 3), by decide⟩, ⟨(2, 3), by decide⟩} := by decide
  rw [hu]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring
section Sums
variable {𝒮 : NestedRegions} [Fintype 𝒮.FineSite] [Fintype 𝒮.FineBond]
theorem innerSum_eq_sum (f g : 𝒮.FineSite → ℝ) : innerSum f g = 𝒮.ξ ^ 4 * ∑ x, f x * g x := by
  rw [innerSum, finsum_eq_sum_of_fintype]
theorem bondInner_eq_sum (A B : 𝒮.FineBond → ℝ) :
    bondInner A B = 𝒮.ξ ^ 4 * ∑ b, A b * B b := by
  rw [bondInner, finsum_eq_sum_of_fintype]
theorem innerSum_comm (f g : 𝒮.FineSite → ℝ) : innerSum f g = innerSum g f := by
  simp only [innerSum_eq_sum, mul_comm (f _)]
theorem bondInner_comm (A B : 𝒮.FineBond → ℝ) : bondInner A B = bondInner B A := by
  simp only [bondInner_eq_sum, mul_comm (A _)]
theorem bondInner_add (A B C : 𝒮.FineBond → ℝ) :
    bondInner A (B + C) = bondInner A B + bondInner A C := by
  simp only [bondInner_eq_sum, Pi.add_apply, mul_add, Finset.sum_add_distrib]
end Sums
end YangMills.Construction.RegionSequence.TorusHodge
