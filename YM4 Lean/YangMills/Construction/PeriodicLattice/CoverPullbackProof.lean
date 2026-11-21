import YangMills.Construction.Lattice.OneScaleOperatorsOnCubesWithArbitraryCentresProof
import Mathlib
set_option autoImplicit false
open Finset
noncomputable section
namespace YangMills.Construction.PeriodicLattice.CoverPullbackProof
open ScaledFun
section
variable {d N m : ℕ}
theorem exists_real_lift_norm {p : ℝ} (a : AddCircle p) : ∃ t : ℝ, (t : AddCircle p) = a ∧ |t| = ‖a‖ := by apply _root_.YangMills.Construction.TorusMetric.exists_coe_eq_abs_eq_norm <;> assumption
theorem norm_coe_le_abs {p : ℝ} (t : ℝ) : ‖(t : AddCircle p)‖ ≤ |t| := by apply _root_.YangMills.Construction.TorusMetric.addCircle_norm_coe_le_abs <;> assumption
theorem taxicabDist_comm {M : ℕ} (a b : Torus d M) : taxicabDist a b = taxicabDist b a := by apply _root_.YangMills.SharedProofs.p1021 <;> assumption
theorem exists_preimage_near (x : Torus d (m * N)) (u : Torus d N)
    (h : maxDist (torusMod d m N x) u ≤ 1) :
    ∃ v : Torus d (m * N), torusMod d m N v = u ∧ maxDist x v ≤ 1 := by
  choose t ht ht' using fun μ => exists_real_lift_norm ((torusMod d m N x - u) μ)
  refine ⟨x - fun μ => ((t μ : ℝ) : AddCircle (((m * N : ℕ) : ℝ))), ?_, ?_⟩
  · funext μ
    have h1 : circleMod m N ((t μ : ℝ) : AddCircle (((m * N : ℕ) : ℝ))) =
        torusMod d m N x μ - u μ := ht μ
    change circleMod m N (x μ - ((t μ : ℝ) : AddCircle (((m * N : ℕ) : ℝ)))) = u μ
    rw [map_sub, h1]
    exact sub_sub_cancel (circleMod m N (x μ)) (u μ)
  · refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun μ => ?_
    have h2 : ‖(torusMod d m N x - u) μ‖ ≤ 1 := (norm_le_pi_norm _ μ).trans h
    change ‖x μ - (x μ - ((t μ : ℝ) : AddCircle (((m * N : ℕ) : ℝ))))‖ ≤ 1
    rw [sub_sub_cancel]
    exact (norm_coe_le_abs _).trans ((ht' μ).le.trans h2)
end
section
variable {d N m : ℕ}
section PullCommutes
variable {V V' V'' W W' W'' : Type}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℝ V'] [FiniteDimensional ℝ V']
  [NormedAddCommGroup V''] [InnerProductSpace ℝ V''] [FiniteDimensional ℝ V'']
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup W'] [InnerProductSpace ℝ W'] [FiniteDimensional ℝ W']
  [NormedAddCommGroup W''] [InnerProductSpace ℝ W''] [FiniteDimensional ℝ W'']
structure PullCommutes (p : V →ₗ[ℝ] W) (p' : V' →ₗ[ℝ] W') (D : V →ₗ[ℝ] V') (E : W →ₗ[ℝ] W') :
    Prop where
  comm : E ∘ₗ p = p' ∘ₗ D
  adj_comm : LinearMap.adjoint E ∘ₗ p' = p ∘ₗ LinearMap.adjoint D
variable {p : V →ₗ[ℝ] W} {p' : V' →ₗ[ℝ] W'} {p'' : V'' →ₗ[ℝ] W''}
theorem PullCommutes.comp {D : V →ₗ[ℝ] V'} {E : W →ₗ[ℝ] W'} {D' : V' →ₗ[ℝ] V''} {E' : W' →ₗ[ℝ] W''}
    (h' : PullCommutes p' p'' D' E') (h : PullCommutes p p' D E) :
    PullCommutes p p'' (D' ∘ₗ D) (E' ∘ₗ E) where
  comm := by
    rw [LinearMap.comp_assoc, h.comm, ← LinearMap.comp_assoc, h'.comm, LinearMap.comp_assoc]
  adj_comm := by
    rw [LinearMap.adjoint_comp, LinearMap.adjoint_comp, LinearMap.comp_assoc, h'.adj_comm,
      ← LinearMap.comp_assoc, h.adj_comm, LinearMap.comp_assoc]
theorem PullCommutes.adjoint {D : V →ₗ[ℝ] V'} {E : W →ₗ[ℝ] W'} (h : PullCommutes p p' D E) :
    PullCommutes p' p (LinearMap.adjoint D) (LinearMap.adjoint E) where
  comm := h.adj_comm
  adj_comm := by
    rw [LinearMap.adjoint_adjoint, LinearMap.adjoint_adjoint]
    exact h.comm
theorem PullCommutes.add {D₁ D₂ : V →ₗ[ℝ] V'} {E₁ E₂ : W →ₗ[ℝ] W'} (h₁ : PullCommutes p p' D₁ E₁)
    (h₂ : PullCommutes p p' D₂ E₂) : PullCommutes p p' (D₁ + D₂) (E₁ + E₂) where
  comm := by rw [LinearMap.add_comp, LinearMap.comp_add, h₁.comm, h₂.comm]
  adj_comm := by
    rw [map_add, map_add, LinearMap.add_comp, LinearMap.comp_add, h₁.adj_comm, h₂.adj_comm]
theorem PullCommutes.sub {D₁ D₂ : V →ₗ[ℝ] V'} {E₁ E₂ : W →ₗ[ℝ] W'} (h₁ : PullCommutes p p' D₁ E₁)
    (h₂ : PullCommutes p p' D₂ E₂) : PullCommutes p p' (D₁ - D₂) (E₁ - E₂) where
  comm := by rw [LinearMap.sub_comp, LinearMap.comp_sub, h₁.comm, h₂.comm]
  adj_comm := by
    rw [map_sub, map_sub, LinearMap.sub_comp, LinearMap.comp_sub, h₁.adj_comm, h₂.adj_comm]
theorem PullCommutes.smul {D : V →ₗ[ℝ] V'} {E : W →ₗ[ℝ] W'} (c : ℝ) (h : PullCommutes p p' D E) :
    PullCommutes p p' (c • D) (c • E) where
  comm := by rw [LinearMap.smul_comp, LinearMap.comp_smul, h.comm]
  adj_comm := by
    simp only [map_smulₛₗ, conj_trivial, LinearMap.smul_comp, LinearMap.comp_smul, h.adj_comm]
theorem PullCommutes.zero : PullCommutes p p' (0 : V →ₗ[ℝ] V') (0 : W →ₗ[ℝ] W') where
  comm := by simp
  adj_comm := by simp
theorem PullCommutes.id : PullCommutes p p LinearMap.id LinearMap.id where
  comm := rfl
  adj_comm := by simp
theorem PullCommutes.sum {κ : Type} (A : Finset κ) {D : κ → V →ₗ[ℝ] V'} {E : κ → W →ₗ[ℝ] W'}
    (h : ∀ k, PullCommutes p p' (D k) (E k)) :
    PullCommutes p p' (∑ k ∈ A, D k) (∑ k ∈ A, E k) := by
  classical
  induction A using Finset.induction_on with
  | empty => simpa using PullCommutes.zero
  | insert a A ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (h a).add ih
end PullCommutes
variable {s : Mesh N} {t : Mesh (m * N)}
theorem scaledFun_sum_apply {X κ : Type} (A : Finset κ) (F : κ → ScaledFun d s X) (x : X) :
    (∑ k ∈ A, F k) x = ∑ k ∈ A, F k x := by apply _root_.YangMills.SharedProofs.p17632 <;> assumption
theorem forwardDiff_eq (s : Mesh N) (μ : Fin d) :
    forwardDiff s μ = s.h⁻¹ • (shiftOp s (s.basisStep μ) - LinearMap.id) := by
  refine LinearMap.ext fun f => ScaledFun.ext fun x => ?_
  rfl
end
section
variable {d N m L j : ℕ}
variable (S : Scales d L j N) (T : Scales d L j (m * N))
end
section
variable {d N m L j : ℕ}
section Norms
variable {M : ℕ} {s : Mesh M} {ι : Type}
theorem holderQuotientSup_nonneg (α : ℝ) {v : GridPoint d s → GridPoint d s → ℝ}
    (hv : ∀ x x', 0 ≤ v x x') : 0 ≤ holderQuotientSup s α v := by apply _root_.YangMills.Construction.CubeCovering.RescaledGreen.holderQuotientSup_nonneg <;> assumption
theorem multiField_holderSemi_nonneg [Fintype ι] (α : ℝ) (f : MultiField d s ι) :
    0 ≤ MultiField.holderSemi α f := by apply _root_.YangMills.Construction.CubeCovering.RescaledGreen.multiField_holderSemi_nonneg <;> assumption
theorem siteFun_holderSemi_nonneg (α : ℝ) (f : SiteFun d s) :
    0 ≤ SiteFun.holderSemi α f := by apply _root_.YangMills.Construction.CubeCovering.RescaledGreen.siteFun_holderSemi_nonneg <;> assumption
theorem abs_le_normAt [Fintype ι] (f : MultiField d s ι) (i : ι) (x : GridPoint d s) :
    |f (i, x)| ≤ MultiField.normAt f x :=
  le_ciSup (f := fun i => |f (i, x)|) (Set.finite_range _).bddAbove i
theorem normAt_nonneg [Fintype ι] (f : MultiField d s ι) (x : GridPoint d s) :
    0 ≤ MultiField.normAt f x :=
  Real.iSup_nonneg fun _ => abs_nonneg _
theorem normAt_le_maxNorm [Fintype ι] (f : MultiField d s ι) (x : GridPoint d s) :
    MultiField.normAt f x ≤ MultiField.maxNorm f :=
  le_ciSup (f := fun x => MultiField.normAt f x) (Set.finite_range _).bddAbove x
theorem maxNorm_nonneg [Fintype ι] (f : MultiField d s ι) : 0 ≤ MultiField.maxNorm f :=
  Real.iSup_nonneg fun _ => normAt_nonneg _ _
theorem siteFun_abs_le_maxNorm (f : SiteFun d s) (x : GridPoint d s) :
    |f x| ≤ SiteFun.maxNorm f :=
  le_ciSup (f := fun x => |f x|) (Set.finite_range _).bddAbove x
theorem siteFun_maxNorm_nonneg (f : SiteFun d s) : 0 ≤ SiteFun.maxNorm f :=
  Real.iSup_nonneg fun _ => abs_nonneg _
end Norms
variable (S : Scales d L j N) (T : Scales d L j (m * N))
variable {ι : Type} {v : Torus d (m * N)}
end
section
variable {d N m L j : ℕ}
variable (S : Scales d L j N) (T : Scales d L j (m * N))
variable {ι ι₁ ι₂ : Type}
theorem mul_mul_le_mul_mul {K E a a' : ℝ} (hK : 0 ≤ K) (hE : 0 ≤ E) (ha : a ≤ a') :
    K * E * a ≤ K * a' * E := by
  have := mul_le_mul_of_nonneg_left ha (mul_nonneg hK hE)
  linarith [mul_right_comm K E a']
theorem mul_mul_mul_le_mul_mul_mul {K E a a' b b' : ℝ} (hK : 0 ≤ K) (hE : 0 ≤ E) (ha : a ≤ a')
    (hb : b ≤ b') (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) :
    K * E * a * b ≤ K * a' * b' * E := by
  have h1 : a * b ≤ a' * b' := mul_le_mul ha hb hb0 (ha0.trans ha)
  have := mul_le_mul_of_nonneg_left h1 (mul_nonneg hK hE)
  nlinarith
end
section
variable {d N m L j : ℕ}
variable (S : Scales d L j N) (T : Scales d L j (m * N))
end
end YangMills.Construction.PeriodicLattice.CoverPullbackProof
