import YangMills.Construction.Lattice.PeriodicTorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.DirichletLaplacian
variable {d N : ℕ}
section Multiplication
variable {s : PeriodicLattice.Mesh N} {X : Type}
def indicatorMul (S : Set X) :
    PeriodicLattice.ScaledFun d s X →ₗ[ℝ] PeriodicLattice.ScaledFun d s X where
  toFun f := PeriodicLattice.ScaledFun.ofMap (S.indicator fun x => f x)
  map_add' f g := PeriodicLattice.ScaledFun.ext fun x => by
    by_cases hx : x ∈ S <;> simp [hx]
  map_smul' c f := PeriodicLattice.ScaledFun.ext fun x => by
    by_cases hx : x ∈ S <;> simp [hx]
theorem indicatorMul_apply_of_mem {S : Set X} (f : PeriodicLattice.ScaledFun d s X) {x : X}
    (hx : x ∈ S) : indicatorMul S f x = f x := by
  simp [indicatorMul, hx]
theorem indicatorMul_apply_of_notMem {S : Set X} (f : PeriodicLattice.ScaledFun d s X) {x : X}
    (hx : x ∉ S) : indicatorMul S f x = 0 := by
  simp [indicatorMul, hx]
theorem indicatorMul_idem (S : Set X) (f : PeriodicLattice.ScaledFun d s X) :
    indicatorMul S (indicatorMul S f) = indicatorMul S f :=
  PeriodicLattice.ScaledFun.ext fun x => by
    by_cases hx : x ∈ S
    · rw [indicatorMul_apply_of_mem _ hx]
    · rw [indicatorMul_apply_of_notMem _ hx, indicatorMul_apply_of_notMem _ hx]
variable [Fintype X]
theorem inner_indicatorMul_left (S : Set X) (f g : PeriodicLattice.ScaledFun d s X) :
    inner ℝ (indicatorMul S f) g = inner ℝ f (indicatorMul S g) := by
  rw [PeriodicLattice.ScaledFun.inner_eq, PeriodicLattice.ScaledFun.inner_eq]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : x ∈ S
  · rw [indicatorMul_apply_of_mem _ hx, indicatorMul_apply_of_mem _ hx]
  · rw [indicatorMul_apply_of_notMem _ hx, indicatorMul_apply_of_notMem _ hx]; ring
theorem inner_indicatorMul_self_nonneg (S : Set X) (f : PeriodicLattice.ScaledFun d s X) :
    0 ≤ inner ℝ f (indicatorMul S f) := by
  rw [PeriodicLattice.ScaledFun.inner_eq]
  refine Finset.sum_nonneg fun x _ => ?_
  have hw := pow_pos s.h_pos d
  by_cases hx : x ∈ S
  · rw [indicatorMul_apply_of_mem _ hx, mul_assoc]
    exact mul_nonneg hw.le (mul_self_nonneg _)
  · rw [indicatorMul_apply_of_notMem _ hx, mul_zero]
end Multiplication
variable (d) in
abbrev Plaquette (s : PeriodicLattice.Mesh N) : Type :=
  PeriodicLattice.OrderedAxisPair d × PeriodicLattice.GridPoint d s
section Space
variable {s : PeriodicLattice.Mesh N}
def supportedForms (B : Set (PeriodicLattice.Link d s)) :
    Submodule ℝ (PeriodicLattice.OneForm d s) :=
  LinearMap.range (indicatorMul B)
theorem indicatorMul_of_mem_supportedForms {B : Set (PeriodicLattice.Link d s)}
    {A : PeriodicLattice.OneForm d s} (hA : A ∈ supportedForms B) :
    indicatorMul B A = A := by
  obtain ⟨C, rfl⟩ := hA
  exact indicatorMul_idem B C
end Space
variable {hN : 0 < N}
def maskedHodgeLaplacian (P : Set (Plaquette d (PeriodicLattice.Mesh.one hN)))
    (V : Set (PeriodicLattice.GridPoint d (PeriodicLattice.Mesh.one hN))) :
    PeriodicLattice.OneForm d (PeriodicLattice.Mesh.one hN) →ₗ[ℝ]
      PeriodicLattice.OneForm d (PeriodicLattice.Mesh.one hN) :=
  LinearMap.adjoint (PeriodicLattice.discreteCurl (PeriodicLattice.Mesh.one hN)) ∘ₗ
      indicatorMul P ∘ₗ PeriodicLattice.discreteCurl (PeriodicLattice.Mesh.one hN) +
    PeriodicLattice.discreteGrad (PeriodicLattice.Mesh.one hN) ∘ₗ indicatorMul V ∘ₗ
      LinearMap.adjoint (PeriodicLattice.discreteGrad (PeriodicLattice.Mesh.one hN))
def dirichletOp (B : Set (PeriodicLattice.Link d (PeriodicLattice.Mesh.one hN)))
    (P : Set (Plaquette d (PeriodicLattice.Mesh.one hN)))
    (V : Set (PeriodicLattice.GridPoint d (PeriodicLattice.Mesh.one hN))) (a : ℝ) :
    Module.End ℝ (supportedForms B) :=
  a • LinearMap.id +
    ((indicatorMul B ∘ₗ maskedHodgeLaplacian P V ∘ₗ indicatorMul B) ∘ₗ
      (supportedForms B).subtype).codRestrict (supportedForms B)
      fun _ => LinearMap.mem_range_self _ _
variable {B : Set (PeriodicLattice.Link d (PeriodicLattice.Mesh.one hN))}
  {P : Set (Plaquette d (PeriodicLattice.Mesh.one hN))}
  {V : Set (PeriodicLattice.GridPoint d (PeriodicLattice.Mesh.one hN))} {a : ℝ}
theorem mul_norm_sq_le_inner_dirichletOp (A : supportedForms B) :
    a * ‖(A : PeriodicLattice.OneForm d (PeriodicLattice.Mesh.one hN))‖ ^ 2 ≤
      inner ℝ (A : PeriodicLattice.OneForm d (PeriodicLattice.Mesh.one hN))
        (dirichletOp B P V a A : PeriodicLattice.OneForm d (PeriodicLattice.Mesh.one hN)) := by
  have hA : indicatorMul B (A : PeriodicLattice.OneForm d (PeriodicLattice.Mesh.one hN)) = A :=
    indicatorMul_of_mem_supportedForms A.2
  have hop : (dirichletOp B P V a A : PeriodicLattice.OneForm d (PeriodicLattice.Mesh.one hN)) =
      a • (A : PeriodicLattice.OneForm d (PeriodicLattice.Mesh.one hN)) +
        indicatorMul B (maskedHodgeLaplacian P V
          (indicatorMul B (A : PeriodicLattice.OneForm d (PeriodicLattice.Mesh.one hN)))) := rfl
  rw [hop, hA, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq,
    ← inner_indicatorMul_left, hA]
  have h₁ : 0 ≤ inner ℝ (A : PeriodicLattice.OneForm d (PeriodicLattice.Mesh.one hN))
      (LinearMap.adjoint (PeriodicLattice.discreteCurl (PeriodicLattice.Mesh.one hN))
        (indicatorMul P (PeriodicLattice.discreteCurl (PeriodicLattice.Mesh.one hN)
          (A : PeriodicLattice.OneForm d (PeriodicLattice.Mesh.one hN))))) := by
    rw [LinearMap.adjoint_inner_right]
    exact inner_indicatorMul_self_nonneg _ _
  have h₂ : 0 ≤ inner ℝ (A : PeriodicLattice.OneForm d (PeriodicLattice.Mesh.one hN))
      (PeriodicLattice.discreteGrad (PeriodicLattice.Mesh.one hN)
        (indicatorMul V (LinearMap.adjoint (PeriodicLattice.discreteGrad (PeriodicLattice.Mesh.one hN))
          (A : PeriodicLattice.OneForm d (PeriodicLattice.Mesh.one hN))))) := by
    rw [← LinearMap.adjoint_inner_left]
    exact inner_indicatorMul_self_nonneg _ _
  have hsum : inner ℝ (A : PeriodicLattice.OneForm d (PeriodicLattice.Mesh.one hN))
      (maskedHodgeLaplacian P V (A : PeriodicLattice.OneForm d (PeriodicLattice.Mesh.one hN))) =
        inner ℝ (A : PeriodicLattice.OneForm d (PeriodicLattice.Mesh.one hN))
          (LinearMap.adjoint (PeriodicLattice.discreteCurl (PeriodicLattice.Mesh.one hN))
            (indicatorMul P (PeriodicLattice.discreteCurl (PeriodicLattice.Mesh.one hN)
              (A : PeriodicLattice.OneForm d (PeriodicLattice.Mesh.one hN))))) +
        inner ℝ (A : PeriodicLattice.OneForm d (PeriodicLattice.Mesh.one hN))
          (PeriodicLattice.discreteGrad (PeriodicLattice.Mesh.one hN)
            (indicatorMul V (LinearMap.adjoint (PeriodicLattice.discreteGrad (PeriodicLattice.Mesh.one hN))
              (A : PeriodicLattice.OneForm d (PeriodicLattice.Mesh.one hN))))) :=
    inner_add_right _ _ _
  rw [hsum]
  linarith
theorem dirichletOp_injective (ha : 0 < a) : Function.Injective (dirichletOp B P V a) := by
  refine (injective_iff_map_eq_zero _).mpr fun A hA => ?_
  have h := mul_norm_sq_le_inner_dirichletOp (P := P) (V := V) (a := a) A
  rw [hA] at h
  simp only [ZeroMemClass.coe_zero, inner_zero_right] at h
  have hn : ‖(A : PeriodicLattice.OneForm d (PeriodicLattice.Mesh.one hN))‖ ^ 2 ≤ 0 := by
    by_contra hc
    exact absurd h (not_le.mpr (mul_pos ha (not_le.mp hc)))
  have h0 : ‖(A : PeriodicLattice.OneForm d (PeriodicLattice.Mesh.one hN))‖ = 0 :=
    pow_eq_zero_iff (two_ne_zero) |>.mp (le_antisymm hn (sq_nonneg _))
  exact Subtype.ext (norm_eq_zero.mp h0)
variable (B P V) in
def dirichletOpInv (ha : 0 < a) : Module.End ℝ (supportedForms B) :=
  (LinearEquiv.ofInjectiveEndo (dirichletOp B P V a) (dirichletOp_injective ha)).symm.toLinearMap
variable (B P V) in
def dirichletGreen (ha : 0 < a) :
    PeriodicLattice.OneForm d (PeriodicLattice.Mesh.one hN) →ₗ[ℝ]
      PeriodicLattice.OneForm d (PeriodicLattice.Mesh.one hN) :=
  indicatorMul B ∘ₗ (supportedForms B).subtype ∘ₗ dirichletOpInv B P V ha ∘ₗ
    (indicatorMul B).codRestrict (supportedForms B) fun _ => LinearMap.mem_range_self _ _
end YangMills.Construction.DirichletLaplacian
