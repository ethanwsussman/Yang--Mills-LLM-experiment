import YangMills.Construction.Lattice.LocalizedDecayBounds
import YangMills.Construction.Lattice.SiteIdentification
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open Finset ScaledFun
namespace OrderTorusOps
variable {d N : ℕ}
theorem adjoint_eq_of_inner {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (T : E →ₗ[ℝ] F) (w : F) (v : E)
    (hv : ∀ u, inner ℝ w (T u) = inner ℝ v u) : LinearMap.adjoint T w = v :=
  ext_inner_right ℝ fun u => by rw [LinearMap.adjoint_inner_left, hv]
section Adjoints
variable (m : Mesh N)
def backwardDiff (μ : Fin d) (f : GridPoint d m → ℝ) (x : GridPoint d m) : ℝ :=
  m.h⁻¹ * (f (x - m.basisStep μ) - f x)
theorem sum_mul_forwardDiff_eq (μ : Fin d) (f g : GridPoint d m → ℝ) :
    ∑ x, m.h ^ d * f x * (m.h⁻¹ * (g (x + m.basisStep μ) - g x)) =
      ∑ x, m.h ^ d * backwardDiff m μ f x * g x := by
  have hshift : ∑ x, m.h ^ d * f x * g (x + m.basisStep μ) =
      ∑ x, m.h ^ d * f (x - m.basisStep μ) * g x := by
    rw [← (Equiv.subRight (m.basisStep μ)).sum_comp fun x => m.h ^ d * f x * g (x + m.basisStep μ)]
    exact sum_congr rfl fun x _ => by simp
  have h₁ : ∀ x, m.h ^ d * f x * (m.h⁻¹ * (g (x + m.basisStep μ) - g x)) =
      m.h⁻¹ * (m.h ^ d * f x * g (x + m.basisStep μ)) - m.h⁻¹ * (m.h ^ d * f x * g x) :=
    fun x => by ring
  have h₂ : ∀ x, m.h ^ d * backwardDiff m μ f x * g x =
      m.h⁻¹ * (m.h ^ d * f (x - m.basisStep μ) * g x) - m.h⁻¹ * (m.h ^ d * f x * g x) :=
    fun x => by simp only [backwardDiff]; ring
  simp only [h₁, h₂, sum_sub_distrib, ← mul_sum, hshift]
theorem adjoint_forwardDiff (μ : Fin d) (f : SiteFun d m) :
    LinearMap.adjoint (forwardDiff m μ) f = ofMap (backwardDiff m μ f) :=
  adjoint_eq_of_inner _ _ _ fun g => by
    rw [ScaledFun.inner_eq, ScaledFun.inner_eq]
    exact sum_mul_forwardDiff_eq m μ f g
theorem discreteLaplacian_apply (g : SiteFun d m) (x : GridPoint d m) :
    discreteLaplacian m g x = ∑ μ : Fin d, backwardDiff m μ (forwardDiff m μ g) x := by
  have hg : discreteLaplacian m g =
      ∑ μ : Fin d, (ofMap (backwardDiff m μ (forwardDiff m μ g)) : SiteFun d m) := by
    simp only [discreteLaplacian, LinearMap.sum_apply, LinearMap.comp_apply, adjoint_forwardDiff]
  rw [hg]
  exact Finset.sum_apply x univ fun μ : Fin d => backwardDiff m μ (forwardDiff m μ g)
theorem sum_sum_ite_eq {X : Type} [Fintype X] (a : Fin d) (u : X → ℝ) :
    ∑ ν, ∑ x, (if a = ν then u x else 0) = ∑ x, u x := by
  rw [sum_comm]
  simp
end Adjoints
section Transport
variable {L j : ℕ} {S : Scales d L j N}
  {e : LatticeFields.LatticeSite (L ^ j) S.uniformTorusShape ≃ GridPoint d S.fineMesh}
  {e₁ : LatticeFields.LatticeSite 1 S.uniformTorusShape ≃ GridPoint d S.unitMesh}
theorem latticeSpacing_eq (S : Scales d L j N) :
    LatticeFields.latticeSpacing (L ^ j) = S.fineMesh.h := by
  change ((L ^ j : ℕ) : ℝ)⁻¹ = ((L : ℝ) ^ j)⁻¹
  push_cast
  rfl
theorem map_add_unitStep (H : S.IsQuotientMapPair e e₁) (μ : Fin d)
    (x : LatticeFields.LatticeSite (L ^ j) S.uniformTorusShape) :
    e (x + LatticeFields.unitStep (L ^ j) S.uniformTorusShape μ) = e x + S.fineMesh.basisStep μ := by
  obtain ⟨v, rfl⟩ := LatticeFields.toSite_surjective _ _ x
  apply Subtype.ext
  unfold LatticeFields.unitStep
  rw [← map_add, AddSubgroup.coe_add, H.apply_toSite, H.apply_toSite]
  funext ν
  change ((((v : Fin d → ℝ) ν +
      (Pi.single μ (LatticeFields.latticeSpacing (L ^ j)) : Fin d → ℝ) ν : ℝ)) :
      AddCircle (N : ℝ)) = (((v : Fin d → ℝ) ν : ℝ) : AddCircle (N : ℝ)) +
        axisMultiple μ S.fineMesh.h ν
  rw [AddCircle.coe_add, latticeSpacing_eq S]
  congr 1
  by_cases hν : ν = μ
  · subst hν
    simp [axisMultiple]
  · simp [axisMultiple, Pi.single_eq_of_ne hν]
theorem map_sub_unitStep (H : S.IsQuotientMapPair e e₁) (μ : Fin d)
    (x : LatticeFields.LatticeSite (L ^ j) S.uniformTorusShape) :
    e (x - LatticeFields.unitStep (L ^ j) S.uniformTorusShape μ) = e x - S.fineMesh.basisStep μ := by
  have hx := map_add_unitStep H μ (x - LatticeFields.unitStep (L ^ j) S.uniformTorusShape μ)
  rw [sub_add_cancel] at hx
  exact eq_sub_of_add_eq hx.symm
end Transport
end OrderTorusOps
end YangMills.Construction.PeriodicLattice
