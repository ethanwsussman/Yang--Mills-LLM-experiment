import YangMills.Construction.ClusterExpansionOfAStep.UnitQuaternionsAsSpecialUnitaryMatrices
import YangMills.Construction.ColdChainAtEveryLevel.UnitPartsOfQuaternions
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace TorusFields
open YangMills.Construction.BlockAverages
variable {n : ℕ}
theorem coe_inv_unitQuaternion (g : UnitQuaternion) :
    ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = star (g : ℍ[ℝ]) := by
  rw [← Unitary.star_eq_inv, Unitary.coe_star]
theorem normSq_unitQuaternion (g : UnitQuaternion) : Quaternion.normSq (g : ℍ[ℝ]) = 1 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.normSq_unitQuaternion <;> assumption
theorem norm_unitQuaternion (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
theorem sq_norm_unitQuaternion_sub_one (g : UnitQuaternion) :
    ‖(g : ℍ[ℝ]) - 1‖ ^ 2 = 2 * (1 - (g : ℍ[ℝ]).re) := by
  have h := normSq_unitQuaternion g
  have h2 : ‖(g : ℍ[ℝ]) - 1‖ ^ 2 = Quaternion.normSq ((g : ℍ[ℝ]) - 1) := by
    rw [Quaternion.normSq_eq_norm_mul_self]
    ring
  rw [h2]
  simp only [Quaternion.normSq_def', Quaternion.re_sub, Quaternion.re_one, Quaternion.imI_sub,
    Quaternion.imI_one, Quaternion.imJ_sub, Quaternion.imJ_one, Quaternion.imK_sub,
    Quaternion.imK_one] at *
  nlinarith
theorem plaquetteEnergy_eq_curvature_sq (U : TorusField n) (x : TorusSite n) (μ ν : Fin 4) :
    plaquetteEnergy U x μ ν = curvature U x μ ν ^ 2 / 2 := by
  unfold plaquetteEnergy curvature
  rw [sq_norm_unitQuaternion_sub_one]
  ring
theorem plaquetteEnergy_nonneg (U : TorusField n) (x : TorusSite n) (μ ν : Fin 4) :
    0 ≤ plaquetteEnergy U x μ ν := by
  rw [plaquetteEnergy_eq_curvature_sq]
  positivity
theorem re_unitQuaternion_conj (g h : UnitQuaternion) :
    ((g * h * g⁻¹ : UnitQuaternion) : ℍ[ℝ]).re = (h : ℍ[ℝ]).re := by
  have hc : ∀ a b : ℍ[ℝ], (a * b).re = (b * a).re := by
    intro a b
    simp only [Quaternion.re_mul]
    ring
  rw [Submonoid.coe_mul, Submonoid.coe_mul, hc, ← mul_assoc]
  have hinv : ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (g : ℍ[ℝ]) = 1 := by
    rw [← Submonoid.coe_mul, inv_mul_cancel]
    rfl
  rw [hinv, one_mul]
theorem holonomy_gaugeTransform (g : TorusSite n → UnitQuaternion) (U : TorusField n)
    (x : TorusSite n) (μ ν : Fin 4) :
    holonomy (gaugeTransform g U) x μ ν = g x * holonomy U x μ ν * (g x)⁻¹ := by
  unfold holonomy gaugeTransform
  have e1 : x + unitStep n μ + unitStep n ν = x + unitStep n ν + unitStep n μ := by abel
  simp only [mul_inv_rev, inv_inv, e1]
  group
theorem plaquetteEnergy_gaugeTransform (g : TorusSite n → UnitQuaternion) (U : TorusField n)
    (x : TorusSite n) (μ ν : Fin 4) :
    plaquetteEnergy (gaugeTransform g U) x μ ν = plaquetteEnergy U x μ ν := by
  unfold plaquetteEnergy
  rw [holonomy_gaugeTransform, re_unitQuaternion_conj]
theorem curvature_gaugeTransform (g : TorusSite n → UnitQuaternion) (U : TorusField n)
    (x : TorusSite n) (μ ν : Fin 4) :
    curvature (gaugeTransform g U) x μ ν = curvature U x μ ν := by
  have h1 := plaquetteEnergy_gaugeTransform g U x μ ν
  rw [plaquetteEnergy_eq_curvature_sq, plaquetteEnergy_eq_curvature_sq] at h1
  have h2 : curvature (gaugeTransform g U) x μ ν ^ 2 = curvature U x μ ν ^ 2 := by linarith
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2
theorem holonomy_translate (u : TorusSite n) (U : TorusField n) (x : TorusSite n) (μ ν : Fin 4) :
    holonomy (translate u U) x μ ν = holonomy U (x + u) μ ν := by
  unfold holonomy translate
  have e1 : x + unitStep n μ + u = x + u + unitStep n μ := by abel
  have e2 : x + unitStep n ν + u = x + u + unitStep n ν := by abel
  rw [e1, e2]
theorem curvature_translate (u : TorusSite n) (U : TorusField n) (x : TorusSite n) (μ ν : Fin 4) :
    curvature (translate u U) x μ ν = curvature U (x + u) μ ν := by
  unfold curvature
  rw [holonomy_translate]
theorem plaquetteEnergy_translate (u : TorusSite n) (U : TorusField n) (x : TorusSite n)
    (μ ν : Fin 4) :
    plaquetteEnergy (translate u U) x μ ν = plaquetteEnergy U (x + u) μ ν := by
  unfold plaquetteEnergy
  rw [holonomy_translate]
theorem continuous_holonomy (x : TorusSite n) (μ ν : Fin 4) :
    Continuous fun U : TorusField n => holonomy U x μ ν := by
  unfold holonomy
  fun_prop
theorem continuous_curvature (x : TorusSite n) (μ ν : Fin 4) :
    Continuous fun U : TorusField n => curvature U x μ ν := by
  unfold curvature
  have h1 : Continuous fun U : TorusField n => ((holonomy U x μ ν : UnitQuaternion) : ℍ[ℝ]) :=
    continuous_subtype_val.comp (continuous_holonomy x μ ν)
  exact (h1.sub continuous_const).norm
theorem continuous_plaquetteEnergy (x : TorusSite n) (μ ν : Fin 4) :
    Continuous fun U : TorusField n => plaquetteEnergy U x μ ν := by
  simp only [plaquetteEnergy_eq_curvature_sq]
  exact ((continuous_curvature x μ ν).pow 2).div_const 2
theorem continuous_wilsonAction [NeZero n] (S : Finset (TorusSite n)) :
    Continuous (wilsonAction S) := by
  unfold wilsonAction
  exact continuous_finsetSum _ fun p _ => continuous_plaquetteEnergy p.1 p.2.1 p.2.2
theorem holonomy_trivialField (x : TorusSite n) (μ ν : Fin 4) :
    holonomy (trivialField n) x μ ν = 1 := by
  simp [holonomy, trivialField]
theorem wilsonAction_trivialField [NeZero n] (S : Finset (TorusSite n)) :
    wilsonAction S (trivialField n) = 0 := by
  simp [wilsonAction, plaquetteEnergy, holonomy_trivialField]
theorem wilsonAction_gaugeTransform [NeZero n] (S : Finset (TorusSite n))
    (g : TorusSite n → UnitQuaternion) (U : TorusField n) :
    wilsonAction S (gaugeTransform g U) = wilsonAction S U := by
  simp [wilsonAction, plaquetteEnergy_gaugeTransform]
theorem expUnit_zero : expUnit 0 = 1 := by
  apply Subtype.ext
  simp [expUnit]
theorem perturb_apply_of_ne {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (t : Fin k → ℝ) (U : TorusField n) (b : TorusBond n) (hb : ∀ l, c l ≠ b) :
    perturb c X t U b.1 b.2 = U b.1 b.2 := by
  unfold perturb
  have hsum : (∑ l, if c l = (b.1, b.2) then t l • X l else 0) = (0 : imaginaryQuaternions) :=
    Finset.sum_eq_zero fun l _ => if_neg (hb l)
  rw [hsum, expUnit_zero, one_mul]
theorem holonomy_perturb_of_ne {k : ℕ} (c : Fin k → TorusBond n)
    (X : Fin k → imaginaryQuaternions) (t : Fin k → ℝ) (U : TorusField n)
    (x : TorusSite n) (μ ν : Fin 4) (h1 : ∀ l, c l ≠ (x, μ))
    (h2 : ∀ l, c l ≠ (x + unitStep n μ, ν))
    (h3 : ∀ l, c l ≠ (x + unitStep n ν, μ)) (h4 : ∀ l, c l ≠ (x, ν)) :
    holonomy (perturb c X t U) x μ ν = holonomy U x μ ν := by
  unfold holonomy
  rw [perturb_apply_of_ne c X t U (x, μ) h1, perturb_apply_of_ne c X t U (x + unitStep n μ, ν) h2,
    perturb_apply_of_ne c X t U (x + unitStep n ν, μ) h3, perturb_apply_of_ne c X t U (x, ν) h4]
theorem continuous_expUnit : Continuous expUnit := by
  apply Continuous.subtype_mk
  have hexp : Continuous (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) := by
    have h : AnalyticOnNhd ℝ (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) Set.univ :=
      fun x _ => NormedSpace.exp_analytic x
    exact h.continuous
  exact hexp.comp continuous_subtype_val
theorem continuous_perturb {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (U : TorusField n) : Continuous fun t : Fin k → ℝ => perturb c X t U := by
  unfold perturb
  refine continuous_pi fun x => continuous_pi fun i => ?_
  refine Continuous.mul (continuous_expUnit.comp ?_) continuous_const
  refine continuous_finsetSum _ fun l _ => ?_
  split_ifs
  · exact (continuous_apply l).smul continuous_const
  · exact continuous_const
theorem perturb_zero {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (U : TorusField n) : perturb c X (0 : Fin k → ℝ) U = U := by
  unfold perturb
  funext x i
  simp [expUnit_zero]
end TorusFields
end YangMills.Construction
end
