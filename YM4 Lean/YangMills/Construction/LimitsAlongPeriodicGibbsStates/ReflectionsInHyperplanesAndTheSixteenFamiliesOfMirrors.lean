import YangMills.Construction.TwoPoints.FirstConsequencesOfThreePropertiesProof
import YangMills.Construction.EuclideanFunctionals.TuplesIsometriesFreeSpaceAndMirrorOfFourSpace
import YangMills.Construction.TwoPoints.ElementaryFactsOfMirrorsAndPlates
import Mathlib
noncomputable section
namespace YangMills.Construction.PeriodicGibbsLimits
open YangMills.Construction.EuclideanFunctionals (R4 FreeSep freeConj)
open YangMills.Construction.TwoPoints (euclidNorm euclidDot reflectAcross normalRepresentatives)
open YangMills.Construction.PeriodicLattice (coordVec)
theorem euclidDot_self_of_unit {n : R4} (hn : euclidNorm n = 1) :
    euclidDot n n = 1 := by apply _root_.YangMills.Construction.TwoPoints.AdmissibleFormConsequences.euclidDot_self_of_unit <;> assumption
theorem euclidNorm_of_mem_normalRepresentatives {n : R4} (hn : n ∈ normalRepresentatives) :
    euclidNorm n = 1 := by
  have key : ∑ μ, n μ ^ 2 = 1 := by
    rcases hn with (⟨μ, rfl⟩ | ⟨μ, ν, h, rfl⟩) | ⟨μ, ν, h, rfl⟩
    · fin_cases μ <;> simp [coordVec, Pi.single_apply]
    · fin_cases μ <;> fin_cases ν <;> simp_all [coordVec, Fin.sum_univ_four,
        Pi.single_apply, mul_pow] <;> norm_num
    · fin_cases μ <;> fin_cases ν <;> simp_all [coordVec, Fin.sum_univ_four,
        Pi.single_apply, mul_pow] <;> norm_num
  change Real.sqrt (∑ μ, n μ ^ 2) = 1
  rw [key, Real.sqrt_one]
def reflectLinear (n : R4) : R4 →ₗ[ℝ] R4 where
  toFun := reflectAcross n
  map_add' x y := by
    funext μ
    simp only [reflectAcross, euclidDot, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, mul_add, Finset.sum_add_distrib]
    ring
  map_smul' t x := by
    funext μ
    simp only [reflectAcross, euclidDot, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
      RingHom.id_apply]
    have : ∑ ν, n ν * (t * x ν) = t * ∑ ν, n ν * x ν := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun ν _ => by ring
    rw [this]
    ring
def hyperplaneReflection (n : R4) (hn : euclidNorm n = 1) (c : ℝ) :
    YangMills.Construction.EuclideanFunctionals.EuclidMotion where
  lin := reflectLinear n
  offset := (2 * c) • n
  lin_norm x := by
    have h1 := euclidDot_self_of_unit hn
    have hp : ∑ μ, n μ * x μ = euclidDot n x := rfl
    set p := euclidDot n x with hpdef
    have hval : ∀ μ, reflectLinear n x μ = x μ - 2 * p * n μ := fun μ => rfl
    simp only [YangMills.Construction.TorusMetric.euclidNormVec, hval]
    congr 1
    simp only [euclidDot, Fin.sum_univ_four] at h1 hp
    simp only [Fin.sum_univ_four]
    linear_combination (-4 * p) * hp + 4 * p ^ 2 * h1
theorem hyperplaneReflection_apply (n : R4) (hn : euclidNorm n = 1) (c : ℝ) (x : R4) :
    hyperplaneReflection n hn c x = x - (2 * (euclidDot n x - c)) • n := by
  funext μ
  change x μ - 2 * euclidDot n x * n μ + 2 * c * n μ = x μ - 2 * (euclidDot n x - c) * n μ
  ring
theorem hyperplaneReflection_zero_apply (n : R4) (hn : euclidNorm n = 1) (x : R4) :
    hyperplaneReflection n hn 0 x = reflectAcross n x := by
  rw [hyperplaneReflection_apply, sub_zero]
  rfl
theorem euclidDot_hyperplaneReflection (n : R4) (hn : euclidNorm n = 1) (c : ℝ) (x : R4) :
    euclidDot n (hyperplaneReflection n hn c x) - c = -(euclidDot n x - c) := by
  have h1 := euclidDot_self_of_unit hn
  rw [hyperplaneReflection_apply]
  have h2 : euclidDot n (x - (2 * (euclidDot n x - c)) • n) =
      euclidDot n x - 2 * (euclidDot n x - c) * euclidDot n n := by
    simp only [euclidDot, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub,
      Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun ν _ => by ring
  rw [h2, h1]
  ring
theorem hyperplaneReflection_hyperplaneReflection (n : R4) (hn : euclidNorm n = 1) (c : ℝ)
    (x : R4) :
    hyperplaneReflection n hn c (hyperplaneReflection n hn c x) = x := by
  rw [hyperplaneReflection_apply n hn c (hyperplaneReflection n hn c x)]
  have h2 := euclidDot_hyperplaneReflection n hn c x
  rw [h2, hyperplaneReflection_apply]
  funext μ
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring
theorem hyperplaneReflection_inv (n : R4) (hn : euclidNorm n = 1) (c : ℝ) :
    (hyperplaneReflection n hn c)⁻¹ = hyperplaneReflection n hn c := by
  refine inv_eq_of_mul_eq_one_left
    (YangMills.Construction.EuclideanFunctionals.EuclidMotion.ext_of_apply fun x => ?_)
  rw [YangMills.Construction.EuclideanFunctionals.EuclidMotion.mul_apply,
    hyperplaneReflection_hyperplaneReflection,
    YangMills.Construction.EuclideanFunctionals.EuclidMotion.one_apply]
theorem hyperplaneReflection_actFn {α : Type*} (n : R4) (hn : euclidNorm n = 1) (c : ℝ)
    (f : R4 → α) :
    (hyperplaneReflection n hn c).actFn f = fun x => f (hyperplaneReflection n hn c x) := by
  funext x
  simp only [YangMills.Construction.EuclideanFunctionals.EuclidMotion.actFn,
    hyperplaneReflection_inv]
def reflectedConj (n : R4) (hn : euclidNorm n = 1) (c : ℝ) (F : FreeSep) : FreeSep :=
  (hyperplaneReflection n hn c).actFree (freeConj F)
end YangMills.Construction.PeriodicGibbsLimits
end
