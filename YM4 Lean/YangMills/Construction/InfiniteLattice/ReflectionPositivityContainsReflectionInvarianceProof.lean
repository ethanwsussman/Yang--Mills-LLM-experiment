import YangMills.Construction.InfiniteLattice.ReflectionPositivityContainsReflectionInvariance
import YangMills.Construction.InfiniteLattice.ReflectionsAndLatticeMirrors
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.LatticeConventions.ReflectionPositivityGivesReflectionInvariance
theorem normal_intValued (Q : NormalHyperplane) :
    ∃ m : Fin 4 → ℤ, ∀ μ, Q.normal μ = (m μ : ℝ) := by
  rcases Q.normal_valid with ⟨μ, h⟩ | ⟨μ, lam, -, h | h⟩
  · refine ⟨Pi.single μ 1, fun κ => ?_⟩
    rw [h]
    by_cases hκ : κ = μ
    · subst hκ; simp [basisVector]
    · simp [basisVector, Pi.single_eq_of_ne hκ]
  · refine ⟨Pi.single μ 1 + Pi.single lam 1, fun κ => ?_⟩
    rw [h]
    by_cases hκ : κ = μ <;> by_cases hκ' : κ = lam <;>
      simp [basisVector, Pi.single_apply, hκ, hκ']
  · refine ⟨Pi.single μ 1 - Pi.single lam 1, fun κ => ?_⟩
    rw [h]
    by_cases hκ : κ = μ <;> by_cases hκ' : κ = lam <;>
      simp [basisVector, Pi.single_apply, hκ, hκ']
theorem normal_ne_zero (Q : NormalHyperplane) : Q.normal ≠ 0 := by
  intro h0
  rcases Q.normal_valid with ⟨μ, h⟩ | ⟨μ, lam, hne, h | h⟩
  · have := congrFun (h0.symm.trans h) μ
    simp [basisVector] at this
  · have := congrFun (h0.symm.trans h) μ
    simp [basisVector, hne] at this
  · have := congrFun (h0.symm.trans h) μ
    simp [basisVector, hne] at this
theorem holds (h₁ : MirrorReflections.MirrorReflectionsStatement)
    (h₂ : ReflectionPositivityWithTranslation) :
    Statement := by
  intro a Q hQ
  have hmem : (a : ℝ) • Q.normal ∈ InfiniteLattice.latticeSubgroup (a : ℝ) := by
    obtain ⟨m, hm⟩ := normal_intValued Q
    exact ⟨m, fun μ => by simp [hm, mul_comm]⟩
  have hne : (a : ℝ) • Q.normal ≠ 0 := smul_ne_zero a.2.ne' (normal_ne_zero Q)
  have hs : Q.reflectionLinear ((a : ℝ) • Q.normal) = -((a : ℝ) • Q.normal) := by
    rw [map_smul, ((h₁ a).1 Q).2.1.1, smul_neg]
  refine ⟨⟨hmem, hne, hs⟩, fun ν _ hinv hrp => ?_⟩
  exact (h₂ a Q hQ ν hrp).2 ⟨(a : ℝ) • Q.normal, hmem⟩
    (fun h => hne (congrArg Subtype.val h)) hs (hinv _)
end YangMills.Construction.LatticeConventions.ReflectionPositivityGivesReflectionInvariance
