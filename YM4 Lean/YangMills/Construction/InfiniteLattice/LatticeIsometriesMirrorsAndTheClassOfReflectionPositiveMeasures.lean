import YangMills.Construction.InfiniteLattice.ThreeNamedSetsOfConditionsOnAState
import YangMills.Construction.InfiniteLattice.WhatIsReadOfAPeriodicGibbsStateProof
import YangMills.Construction.InfiniteLattice.LatticeMirrorsAndTwoFormsOfReflectionPositivityProof
import YangMills.Construction.InfiniteLattice.ObservablesAndIsometriesAtOneSpacing
import YangMills.Construction.InfiniteLattice.OneLatticeItsConfigurationsAndMeasuresOnCompactSpaces
import YangMills.Construction.InfiniteLattice.ReflectionsLatticeMirrorsAndTuplesOnTheTwoSidesProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set YangMills.Construction.InfiniteLattice
open scoped ComplexConjugate ComplexOrder Matrix
noncomputable section
namespace YangMills.Construction.LatticePhases
variable {a : ℝ}
def upperSide (P : LatticeMirror a) : Set AmbientSpace := {x | P.level ≤ P.cls.realNormal ⬝ᵥ x}
def lowerSide (P : LatticeMirror a) : Set AmbientSpace := {x | P.cls.realNormal ⬝ᵥ x ≤ P.level}
theorem realNormal_axial (μ : Fin 4) :
    (ReflectionClass.axial μ).realNormal = LatticeConventions.basisVector μ := by apply _root_.YangMills.Construction.InfiniteLattice.EuclideanMirrors.MirrorReflections.realNormal_axial <;> assumption
theorem realNormal_mem (F : ReflectionClass) :
    LatticeConventions.IsAxialNormal F.realNormal ∨
      LatticeConventions.IsFaceDiagonalNormal F.realNormal := by apply _root_.YangMills.Construction.LatticeConventions.LatticeMirrorsAndReflectionPositivity.realNormal_valid <;> assumption
def toNormalHyperplane (P : LatticeMirror a) : LatticeConventions.NormalHyperplane where
  normal := P.cls.realNormal
  level := P.level
  normal_valid := realNormal_mem P.cls
theorem not_isFaceDiagonalNormal_basisVector (μ : Fin 4) :
    ¬ LatticeConventions.IsFaceDiagonalNormal (LatticeConventions.basisVector μ) := by apply _root_.YangMills.Construction.LatticeConventions.basisVector_not_isFaceDiagonalNormal <;> assumption
theorem toNormalHyperplane_isLatticeMirror (P : LatticeMirror a) :
    (toNormalHyperplane P).IsLatticeMirror a := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodicGibbsConsequences.normalHyperplane_isLatticeMirror <;> assumption
theorem toNormalHyperplane_reflect (P : LatticeMirror a) :
    (toNormalHyperplane P).reflect = P.symmetry.toFun := by
  funext x
  have h : LatticeConventions.euclidNorm P.cls.realNormal ^ 2 =
      P.cls.realNormal ⬝ᵥ P.cls.realNormal := by
    have h0 : 0 ≤ LatticeConventions.euclidDot P.cls.realNormal P.cls.realNormal :=
      Finset.sum_nonneg fun μ _ => mul_self_nonneg _
    rw [LatticeConventions.euclidNorm, ← Real.sqrt_eq_rpow, Real.sq_sqrt h0]
    rfl
  change x - (2 * (LatticeConventions.euclidDot P.cls.realNormal x - P.level) /
      LatticeConventions.euclidNorm P.cls.realNormal ^ 2) • P.cls.realNormal =
    hyperplaneReflect _ _ x
  rw [h]
  rfl
def axisSignChanges : Set (AmbientSpace →ₗ[ℝ] AmbientSpace) :=
  {γ | ∀ μ, γ (InfiniteLattice.basisVector μ) = InfiniteLattice.basisVector μ ∨
    γ (InfiniteLattice.basisVector μ) = -InfiniteLattice.basisVector μ}
theorem axisSignChanges_eq_signFlipSet : axisSignChanges = signFlipSet := by
  ext γ
  constructor
  · intro h
    have hs : ∀ μ, ∃ u : ℤˣ,
        γ (InfiniteLattice.basisVector μ) = ((u : ℤ) : ℝ) • InfiniteLattice.basisVector μ := by
      intro μ
      rcases h μ with h | h
      · exact ⟨1, by simp [h]⟩
      · exact ⟨-1, by simp [h]⟩
    choose ε hε using hs
    refine ⟨ε, LinearMap.ext fun x => ?_⟩
    have hx : x = ∑ κ, x κ • InfiniteLattice.basisVector κ := by
      funext ν
      simp [InfiniteLattice.basisVector, Finset.sum_apply, Pi.single_apply]
    have hγ : γ x = ∑ κ, x κ • (((ε κ : ℤ) : ℝ) • InfiniteLattice.basisVector κ) := by
      conv_lhs => rw [hx]
      simp only [map_sum, map_smul, hε]
    rw [hγ]
    funext μ
    simp [signFlip, InfiniteLattice.basisVector, Finset.sum_apply, Pi.single_apply, mul_comm]
  · rintro ⟨ε, rfl⟩ μ
    have hc : ∀ ν, ν ≠ μ → (signFlip ε (InfiniteLattice.basisVector μ)) ν = 0 := fun ν e => by
      simp [signFlip, InfiniteLattice.basisVector, Pi.single_eq_of_ne e]
    rcases Int.units_eq_one_or (ε μ) with h | h
    · refine Or.inl (funext fun ν => ?_)
      by_cases e : ν = μ
      · subst e
        simp [signFlip, InfiniteLattice.basisVector, h]
      · simpa [InfiniteLattice.basisVector, Pi.single_eq_of_ne e] using hc ν e
    · refine Or.inr (funext fun ν => ?_)
      by_cases e : ν = μ
      · subst e
        simp [signFlip, InfiniteLattice.basisVector, h]
      · simpa [InfiniteLattice.basisVector, Pi.single_eq_of_ne e] using hc ν e
def IsReflectionPositiveAt (ρ : ProbMeasure (GaugeField a)) (P : LatticeMirror a) : Prop :=
  (∀ F ∈ regionObservables a (upperSide P), IsLocalObservable F →
    0 ≤ ρ.eval fun U => conj (P.symmetry.actOn F U) * F U) ∧
  ∀ F ∈ regionObservables a (lowerSide P), IsLocalObservable F →
    0 ≤ ρ.eval fun U => conj (P.symmetry.actOn F U) * F U
def Setup.reflectionPositiveStates (D : Setup) : Set (ProbMeasure (GaugeField D.mesh)) :=
  {ρ | (∀ v : LatticePoint D.mesh, IsSymmetricUnder ρ.toMeasure (shift v)) ∧
    ∀ P : LatticeMirror D.mesh, IsReflectionPositiveAt ρ P}
end YangMills.Construction.LatticePhases
end
