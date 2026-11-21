import YangMills.Construction.ReflectionPositivity.SixteenFamiliesOfMirrors
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix
noncomputable section
namespace YangMills.Construction.Mirrors
open InfiniteLattice (AmbientSpace latticeSubgroup)
open PeriodicLattice (coordVec)
namespace ReflectingHyperplane
variable (M : ReflectingHyperplane)
def normalNorm : ℝ := Real.sqrt (M.normalVec ⬝ᵥ M.normalVec)
def unitNormalVec : AmbientSpace := M.normalNorm⁻¹ • M.normalVec
def signedOffset : ℝ := M.offset / M.normalNorm
def withOffset (c'' : ℝ) : ReflectingHyperplane := ⟨M.normalVec, M.normalVec_mem, c''⟩
def reflectL2 (x : EuclideanSpace ℝ (Fin 4)) : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 (M.reflect (WithLp.ofLp x))
end ReflectingHyperplane
def UnitNormalAndLattice.Statement : Prop :=
  ∀ (M : ReflectingHyperplane) (a : ℝ), 0 < a →
    (M.carrier = {x | M.unitNormalVec ⬝ᵥ x = M.signedOffset} ∧
      (∀ x, M.reflect x = x - (2 * (M.unitNormalVec ⬝ᵥ x - M.signedOffset)) • M.unitNormalVec) ∧
      M.positiveSide = {x | M.unitNormalVec ⬝ᵥ x > M.signedOffset}) ∧
    (∀ μ : Fin 4, M.normalVec = coordVec μ →
      (M.reflect '' (latticeSubgroup a : Set AmbientSpace) = latticeSubgroup a ↔
        ∃ q : ℤ, M.offset = (q : ℝ) * (a / 2))) ∧
    (∀ μ ν : Fin 4, μ < ν →
      (M.normalVec = coordVec μ + coordVec ν ∨
        M.normalVec = coordVec μ - coordVec ν) →
      (M.reflect '' (latticeSubgroup a : Set AmbientSpace) = latticeSubgroup a ↔
        ∃ q : ℤ, M.offset = (q : ℝ) * a) ∧
      (M.reflect '' (latticeSubgroup a : Set AmbientSpace) = latticeSubgroup a ↔
        ∃ q : ℤ, Real.sqrt 2 * M.signedOffset = (q : ℝ) * a)) ∧
    ((∀ x, M.normalVec ⬝ᵥ M.reflect x - M.offset = -(M.normalVec ⬝ᵥ x - M.offset)) ∧
      M.reflect ∘ M.reflect = id ∧
      Isometry M.reflectL2 ∧
      M.reflect '' M.positiveSide = {x | M.normalVec ⬝ᵥ x < M.offset}) ∧
    (∀ (c'' : ℝ) (x : AmbientSpace), M.reflect x = (M.withOffset c'').reflect x +
      (2 * (M.offset - c'') * (M.normalNorm ^ 2)⁻¹) • M.normalVec)
end YangMills.Construction.Mirrors
