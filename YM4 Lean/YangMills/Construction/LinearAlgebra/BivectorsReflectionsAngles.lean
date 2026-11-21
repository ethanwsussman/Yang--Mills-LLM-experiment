import YangMills.Construction.Geometry.TorusMetric
import Mathlib
set_option autoImplicit false
open Matrix YangMills.Construction.TorusMetric
noncomputable section
namespace YangMills.Construction.Exterior
def skewMatrices : Submodule ℝ (Matrix (Fin 4) (Fin 4) ℝ) where
  carrier := {ω | ∀ μ ν, ω ν μ = -ω μ ν}
  add_mem' := by
    intro a b ha hb μ ν
    have ha' : a ν μ = -a μ ν := ha μ ν
    have hb' : b ν μ = -b μ ν := hb μ ν
    simp only [Matrix.add_apply, ha', hb']
    ring
  zero_mem' := by
    intro μ ν
    simp
  smul_mem' := by
    intro c a ha μ ν
    have ha' : a ν μ = -a μ ν := ha μ ν
    simp [ha']
theorem mem_skewMatrices {ω : Matrix (Fin 4) (Fin 4) ℝ} :
    ω ∈ skewMatrices ↔ ∀ μ ν, ω ν μ = -ω μ ν :=
  Iff.rfl
def Bivector : Type := skewMatrices
instance : AddCommGroup Bivector := inferInstanceAs (AddCommGroup skewMatrices)
instance : Module ℝ Bivector := inferInstanceAs (Module ℝ skewMatrices)
instance : FiniteDimensional ℝ Bivector :=
  inferInstanceAs (FiniteDimensional ℝ skewMatrices)
namespace Bivector
def ofSkew (ω : Matrix (Fin 4) (Fin 4) ℝ) (h : ∀ μ ν, ω ν μ = -ω μ ν) : Bivector :=
  (⟨ω, h⟩ : skewMatrices)
theorem apply_swap (ω : Bivector) (μ ν : Fin 4) : ω.1 ν μ = -ω.1 μ ν :=
  mem_skewMatrices.1 ω.2 μ ν
@[ext] theorem ext {ω η : Bivector} (h : ω.1 = η.1) : ω = η := Subtype.ext h
@[simp] theorem ofSkew_val (ω : Matrix (Fin 4) (Fin 4) ℝ) (h : ∀ μ ν, ω ν μ = -ω μ ν) :
    (ofSkew ω h).1 = ω := rfl
@[simp] theorem zero_val : (0 : Bivector).1 = 0 := rfl
@[simp] theorem add_val (ω η : Bivector) : (ω + η).1 = ω.1 + η.1 := rfl
@[simp] theorem smul_val (c : ℝ) (ω : Bivector) : (c • ω).1 = c • ω.1 := rfl
end Bivector
def wedgeProd : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) →ₗ[ℝ] Bivector :=
  LinearMap.mk₂ ℝ
    (fun u v => Bivector.ofSkew (vecMulVec u v - vecMulVec v u) fun μ ν => by
      simp only [Matrix.sub_apply, vecMulVec_apply]
      ring)
    (fun u u' v => by
      ext μ ν
      simp [Matrix.sub_apply, vecMulVec_apply]
      ring)
    (fun c u v => by
      ext μ ν
      simp [Matrix.sub_apply, vecMulVec_apply]
      ring)
    (fun u v v' => by
      ext μ ν
      simp [Matrix.sub_apply, vecMulVec_apply]
      ring)
    (fun c u v => by
      ext μ ν
      simp [Matrix.sub_apply, vecMulVec_apply]
      ring)
def ascPairs : Finset (Fin 4 × Fin 4) := Finset.univ.filter fun p => p.1 < p.2
def bivInner (ω η : Bivector) : ℝ := ∑ p ∈ ascPairs, ω.1 p.1 p.2 * η.1 p.1 p.2
theorem bivInner_eq_sum_six (ω η : Bivector) :
    bivInner ω η =
      ω.1 0 1 * η.1 0 1 + ω.1 0 2 * η.1 0 2 + ω.1 0 3 * η.1 0 3 + ω.1 1 2 * η.1 1 2 +
        ω.1 1 3 * η.1 1 3 + ω.1 2 3 * η.1 2 3 := by
  have h : ascPairs = {(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)} := by decide
  rw [bivInner, h]
  simp
  ring
abbrev bivInnerCore : InnerProductSpace.Core ℝ Bivector where
  inner := bivInner
  conj_inner_symm ω η := by simp [bivInner, mul_comm]
  re_inner_nonneg ω := by
    simpa [bivInner] using Finset.sum_nonneg fun p _ => mul_self_nonneg (ω.1 p.1 p.2)
  add_left ω η ζ := by simp [bivInner, add_mul, Finset.sum_add_distrib]
  smul_left ω η r := by simp [bivInner, Finset.mul_sum, mul_assoc]
  definite ω h := by
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg
      (fun p _ => mul_self_nonneg (ω.1 p.1 p.2))).1 h
    have hlt : ∀ μ ν : Fin 4, μ < ν → ω.1 μ ν = 0 := fun μ ν hμν =>
      mul_self_eq_zero.1 (hzero (μ, ν) (by simp [ascPairs, hμν]))
    ext μ ν
    rw [Bivector.zero_val, Matrix.zero_apply]
    rcases lt_trichotomy μ ν with hμν | hμν | hμν
    · exact hlt μ ν hμν
    · subst hμν
      have := ω.apply_swap μ μ
      linarith
    · rw [ω.apply_swap ν μ, hlt ν μ hμν, neg_zero]
instance : NormedAddCommGroup Bivector := bivInnerCore.toNormedAddCommGroup
instance : InnerProductSpace ℝ Bivector := InnerProductSpace.ofCore bivInnerCore.toCore
theorem inner_eq_bivInner (ω η : Bivector) : inner ℝ ω η = bivInner ω η := rfl
def IsSelfAdjointMap (M : Bivector →ₗ[ℝ] Bivector) : Prop :=
  ∀ ω η : Bivector, inner ℝ ω (M η) = inner ℝ (M ω) η
def exteriorSq (T : Matrix (Fin 4) (Fin 4) ℝ) : Bivector →ₗ[ℝ] Bivector where
  toFun ω := Bivector.ofSkew (T * ω.1 * Tᵀ) fun μ ν => by
    have hω : ω.1ᵀ = -ω.1 := by
      ext α β
      exact ω.apply_swap α β
    have h : (T * ω.1 * Tᵀ)ᵀ = -(T * ω.1 * Tᵀ) := by
      simp [Matrix.transpose_mul, hω, Matrix.mul_assoc]
    exact congrFun (congrFun h μ) ν
  map_add' ω η := by
    ext1
    change T * (ω.1 + η.1) * Tᵀ = T * ω.1 * Tᵀ + T * η.1 * Tᵀ
    rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c ω := by
    ext1
    change T * (c • ω.1) * Tᵀ = c • (T * ω.1 * Tᵀ)
    simp
def wedgeVolume (ω η : Bivector) : ℝ :=
  ω.1 0 1 * η.1 2 3 - ω.1 0 2 * η.1 1 3 + ω.1 0 3 * η.1 1 2 + ω.1 1 2 * η.1 0 3 -
    ω.1 1 3 * η.1 0 2 + ω.1 2 3 * η.1 0 1
def hodge : Bivector →ₗ[ℝ] Bivector where
  toFun η := Bivector.ofSkew
    !![0, η.1 2 3, -η.1 1 3, η.1 1 2;
       -η.1 2 3, 0, η.1 0 3, -η.1 0 2;
       η.1 1 3, -η.1 0 3, 0, η.1 0 1;
       -η.1 1 2, η.1 0 2, -η.1 0 1, 0]
    fun μ ν => by fin_cases μ <;> fin_cases ν <;> simp
  map_add' η ζ := by
    ext μ ν
    fin_cases μ <;> fin_cases ν <;> simp <;> ring
  map_smul' c η := by
    ext μ ν
    fin_cases μ <;> fin_cases ν <;> simp
theorem inner_hodge (ω η : Bivector) : inner ℝ ω (hodge η) = wedgeVolume ω η := by
  rw [inner_eq_bivInner, bivInner_eq_sum_six]
  simp [hodge, wedgeVolume]
  ring
def householder (u : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ := 1 - (2 : ℝ) • vecMulVec u u
def wedgeRange (u : Fin 4 → ℝ) : Submodule ℝ Bivector := LinearMap.range (wedgeProd u)
def wedgeRangeProj (u : Fin 4 → ℝ) : Bivector →ₗ[ℝ] Bivector :=
  (wedgeRange u).starProjection.toLinearMap
def unitSphere4 : Set (Fin 4 → ℝ) := {x | euclidNormVec x = 1}

def BivectorInnerMinorsReflectionDet : Prop :=
  (∀ a b c d : Fin 4 → ℝ,
      inner ℝ (wedgeProd a b) (wedgeProd c d) = (a ⬝ᵥ c) * (b ⬝ᵥ d) - (a ⬝ᵥ d) * (b ⬝ᵥ c)) ∧
  (∀ K : InnerProductSpace.Core ℝ Bivector,
      (∀ a b c d : Fin 4 → ℝ,
        K.toInner.inner (wedgeProd a b) (wedgeProd c d) =
          (a ⬝ᵥ c) * (b ⬝ᵥ d) - (a ⬝ᵥ d) * (b ⬝ᵥ c)) →
      ∀ α β : Bivector, K.toInner.inner α β = inner ℝ α β) ∧
  (∀ (M : Matrix (Fin 4) (Fin 4) ℝ) (i j k l : Fin 4), i < j → k < l →
      inner ℝ (wedgeProd (Pi.single i 1) (Pi.single j 1))
          (exteriorSq M (wedgeProd (Pi.single k 1) (Pi.single l 1))) =
        M i k * M j l - M i l * M j k) ∧
  (∀ n : Fin 4 → ℝ, euclidNormVec n = 1 →
      (householder n)ᵀ = householder n ∧
      householder n ∈ Matrix.orthogonalGroup (Fin 4) ℝ ∧
      householder n *ᵥ n = -n ∧
      (∀ w : Fin 4 → ℝ, n ⬝ᵥ w = 0 → householder n *ᵥ w = w) ∧
      Module.finrank ℝ (wedgeRange n) = 3) ∧
  (∀ a b c d : Fin 4 → ℝ,
      wedgeVolume (wedgeProd a b) (wedgeProd c d) = ((Matrix.of ![a, b, c, d])ᵀ).det)
end YangMills.Construction.Exterior
