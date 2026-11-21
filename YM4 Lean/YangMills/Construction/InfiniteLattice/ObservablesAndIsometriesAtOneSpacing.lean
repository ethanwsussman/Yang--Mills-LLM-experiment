import YangMills.Construction.InfiniteLattice.HypercubicMotionsOfTheLattice
import YangMills.Construction.InfiniteLattice.HyperoctahedralMotionsAndCubes
import YangMills.Construction.InfiniteLattice.ReflectionNorm
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.InfiniteLattice
variable {a : ℝ}
theorem mem_hypercubicGroup_iff_signedPerm (w : AmbientSpace →ₗ[ℝ] AmbientSpace) :
    w ∈ hypercubicGroup ↔ ∃ (σ : Equiv.Perm (Fin 4)) (ε : Fin 4 → ℝ),
      (∀ μ, ε μ = 1 ∨ ε μ = -1) ∧ ∀ μ, w (basisVector μ) = ε μ • basisVector (σ μ) := by
  constructor
  · rintro ⟨π, hπ⟩
    have hsign : ∀ κ, ∃ e : ℝ, (e = 1 ∨ e = -1) ∧ w (basisVector κ) = e • basisVector (π κ) := by
      intro κ
      rcases hπ κ with hκ | hκ
      · exact ⟨1, Or.inl rfl, by simp [hκ]⟩
      · exact ⟨-1, Or.inr rfl, by simp [hκ]⟩
    choose ε hε hw using hsign
    exact ⟨π, ε, hε, hw⟩
  · rintro ⟨σ, ε, hε, hw⟩
    refine ⟨σ, fun κ => ?_⟩
    rcases hε κ with he | he
    · left
      simp [hw, he]
    · right
      simp [hw, he]
def translateBy (v : AmbientSpace) : AmbientSpace → AmbientSpace := fun x => x + v
theorem shift_toFun_eq_translateBy (v : LatticePoint a) :
    (shift v).toFun = translateBy (v : AmbientSpace) :=
  rfl
namespace LatticeSymmetry
variable (r : LatticeSymmetry a)
theorem toFun_injective : Function.Injective r.toFun := by
  intro x y hxy
  have hd := r.preservesDist x y
  rw [hxy, sub_self] at hd
  have hz : TorusMetric.euclidNormVec (x - y) = 0 := by
    rw [← hd]
    simp [TorusMetric.euclidNormVec]
  rw [TorusMetric.euclidNormVec, Real.sqrt_eq_zero (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at hz
  funext μ
  have hμ := (Finset.sum_eq_zero_iff_of_nonneg fun ν _ => sq_nonneg ((x - y) ν)).mp hz μ
    (Finset.mem_univ μ)
  exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hμ)
def pushforwardFun {E : Type*} (f : AmbientSpace → E) : AmbientSpace → E :=
  f ∘ Function.invFun r.toFun
theorem pushforwardFun_apply_toFun {E : Type*} (f : AmbientSpace → E) (x : AmbientSpace) :
    r.pushforwardFun f (r.toFun x) = f x := by
  simp only [pushforwardFun, Function.comp_apply]
  rw [Function.leftInverse_invFun r.toFun_injective]
end LatticeSymmetry
def axisReflection (μ : Fin 4) : AmbientSpace →ₗ[ℝ] AmbientSpace where
  toFun x := x - (2 * x μ) • basisVector μ
  map_add' x y := by
    simp only [Pi.add_apply, mul_add, add_smul]
    abel
  map_smul' t x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, smul_sub, smul_smul]
    congr 2
    ring
theorem axisReflection_eq_coordinateSignFlip (μ : Fin 4) :
    axisReflection μ = coordinateSignFlip μ := by
  refine LinearMap.ext fun x => ?_
  have hx := coordinateReflection_eq_signFlip_add μ 0 x
  change x - (2 * x μ) • basisVector μ = _
  simpa [coordinateReflection] using hx
theorem axialReflection_toFun_eq_axisReflection (μ : Fin 4) :
    (axialReflection a μ).toFun = axisReflection μ :=
  funext fun x => axialReflection_toFun μ x
def signFlipSet : Set (AmbientSpace →ₗ[ℝ] AmbientSpace) :=
  range fun ε : Fin 4 → ℤˣ => (signFlip ε : AmbientSpace →ₗ[ℝ] AmbientSpace)
theorem signFlipSet_subset_hypercubicGroup : signFlipSet ⊆ hypercubicGroup := by
  rintro _ ⟨ε, rfl⟩
  refine (mem_hypercubicGroup_iff_signedPerm _).mpr
    ⟨1, fun μ => ((ε μ : ℤ) : ℝ), fun μ => ?_, fun μ => ?_⟩
  · rcases Int.units_eq_one_or (ε μ) with hε | hε <;> simp [hε]
  · funext ν
    by_cases hν : ν = μ
    · subst hν
      simp [signFlip, basisVector]
    · simp [signFlip, basisVector, Pi.single_eq_of_ne hν]
theorem ncard_signFlipSet : signFlipSet.ncard = 16 := by
  have hinj : Function.Injective fun ε : Fin 4 → ℤˣ =>
      (signFlip ε : AmbientSpace →ₗ[ℝ] AmbientSpace) := fun ε ε' h =>
    signFlip_injective (LinearEquiv.toLinearMap_injective h)
  rw [signFlipSet, ← Nat.card_coe_set_eq, Nat.card_range_of_injective hinj,
    Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_units_int]
  simp
end YangMills.Construction.InfiniteLattice
