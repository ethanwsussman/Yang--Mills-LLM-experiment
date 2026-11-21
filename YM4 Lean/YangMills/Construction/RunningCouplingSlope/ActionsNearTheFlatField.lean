import YangMills.Construction.ColdChainAtEveryLevel.UnitPartsOfQuaternions
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology Quaternion
noncomputable section
namespace YangMills.Construction
namespace RunningCouplingSlope
open BlockAverages
section Normalization
theorem norm_coe_unitQuaternion (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
theorem inv_norm_smul_mem_unitary (q : ℍ[ℝ]) (hq : q ≠ 0) : ((‖q‖⁻¹ : ℝ) • q) ∈ unitary ℍ[ℝ] := by apply _root_.YangMills.Construction.BlockAverages.smul_inv_norm_mem_unitary <;> assumption
open Classical in
def normalize (q : ℍ[ℝ]) : UnitQuaternion :=
  if hq : q = 0 then 1 else ⟨(‖q‖⁻¹ : ℝ) • q, inv_norm_smul_mem_unitary q hq⟩
theorem coe_normalize {q : ℍ[ℝ]} (hq : q ≠ 0) : ((normalize q : UnitQuaternion) : ℍ[ℝ]) = (‖q‖⁻¹ : ℝ) • q := by
  simp [normalize, hq]
theorem normalize_coe (g : UnitQuaternion) : normalize (g : ℍ[ℝ]) = g := by
  have hg : (g : ℍ[ℝ]) ≠ 0 := by
    intro h0
    have := norm_coe_unitQuaternion g
    rw [h0] at this
    simp at this
  apply Subtype.ext
  rw [coe_normalize hg, norm_coe_unitQuaternion]
  simp
def quatReCLM : ℍ[ℝ] →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1 : ℝ))
def quatStarCLM : ℍ[ℝ] →L[ℝ] ℍ[ℝ] := LinearMap.toContinuousLinearMap
  { toFun := star
    map_add' := star_add
    map_smul' := fun c q => by ext <;> simp }
@[simp] theorem quatStarCLM_apply (q : ℍ[ℝ]) : quatStarCLM q = star q := rfl
theorem coe_inv_unitQuaternion (g : UnitQuaternion) : ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = star (g : ℍ[ℝ]) := rfl
section Analyticity
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem analyticAt_quat_star {f : E → ℍ[ℝ]} {e : E} (hf : AnalyticAt ℝ f e) :
    AnalyticAt ℝ (fun x => star (f x)) e :=
  (quatStarCLM.analyticAt _).comp hf
theorem analyticAt_quat_re {f : E → ℍ[ℝ]} {e : E} (hf : AnalyticAt ℝ f e) :
    AnalyticAt ℝ (fun x => (f x).re) e :=
  (quatReCLM.analyticAt _).comp hf
theorem analyticAt_quat_norm {f : E → ℍ[ℝ]} {e : E} (hf : AnalyticAt ℝ f e) (h0 : f e ≠ 0) :
    AnalyticAt ℝ (fun x => ‖f x‖) e := by
  have hq : AnalyticAt ℝ (fun x => (f x * star (f x)).re) e := analyticAt_quat_re (hf.mul (analyticAt_quat_star hf))
  have hp : 0 < (f e * star (f e)).re := by
    rw [Quaternion.self_mul_star]
    simpa using Quaternion.normSq_nonneg.lt_of_ne' (by simpa using h0)
  have hlog : AnalyticAt ℝ (fun x => Real.log (f x * star (f x)).re) e :=
    AnalyticAt.comp (g := Real.log) (f := fun x => (f x * star (f x)).re) (analyticAt_log hp) hq
  have hl : AnalyticAt ℝ (fun x => Real.exp (Real.log (f x * star (f x)).re * (1 / 2))) e :=
    AnalyticAt.comp (g := Real.exp) (f := fun x => Real.log (f x * star (f x)).re * (1 / 2))
      analyticAt_rexp (hlog.mul analyticAt_const)
  refine hl.congr ?_
  have hc : ContinuousAt (fun x => (f x * star (f x)).re) e := hq.continuousAt
  filter_upwards [hc.eventually (lt_mem_nhds hp)] with x hx
  have e1 : (f x * star (f x)).re = ‖f x‖ ^ 2 := by
    rw [Quaternion.self_mul_star]
    simp [Quaternion.normSq_eq_norm_mul_self, sq]
  rw [e1] at hx ⊢
  have hn : 0 < ‖f x‖ := by
    rcases (norm_nonneg (f x)).eq_or_lt with h1 | h1
    · rw [← h1] at hx; simp at hx
    · exact h1
  rw [Real.log_pow]
  push_cast
  rw [show (2 : ℝ) * Real.log ‖f x‖ * (1 / 2) = Real.log ‖f x‖ by ring, Real.exp_log hn]
theorem analyticAt_normalize {f : E → ℍ[ℝ]} {e : E} (hf : AnalyticAt ℝ f e) (h0 : f e ≠ 0) :
    AnalyticAt ℝ (fun x => ((normalize (f x) : UnitQuaternion) : ℍ[ℝ])) e := by
  have hn := analyticAt_quat_norm hf h0
  have hi : AnalyticAt ℝ (fun x => ‖f x‖⁻¹) e := hn.inv (norm_ne_zero_iff.2 h0)
  refine (hi.smul hf).congr ?_
  have hc : ContinuousAt f e := hf.continuousAt
  filter_upwards [hc.eventually_ne h0] with x hx
  exact (coe_normalize hx).symm
end Analyticity
end Normalization
variable {F : BlockFrame} {k : ℕ}
def trivialBlockField (F : BlockFrame) (k : ℕ) : F.GaugeField k := fun _ _ => 1
def fieldOfQuaternions (Y : F.Site k → Fin 4 → ℍ[ℝ]) : F.GaugeField k := fun x i => normalize (Y x i)
def quaternionsOfField (W : F.GaugeField k) : F.Site k → Fin 4 → ℍ[ℝ] := fun x i => (W x i : ℍ[ℝ])
theorem fieldOfQuaternions_quaternionsOfField (W : F.GaugeField k) : fieldOfQuaternions (quaternionsOfField W) = W := by
  funext x i
  exact normalize_coe _
def fieldAlongLine (B : F.Site k → Fin 4 → imaginaryQuaternions) (τ : ℝ) : F.GaugeField k :=
  fieldOfQuaternions fun x i => 1 + τ • (B x i : ℍ[ℝ])
def IsPureGauge (W : F.GaugeField k) : Prop :=
  ∃ g : (Fin 4 → ℤ) → UnitQuaternion, ∀ z i, W (siteOfCoords k z) i = g z * (g (z + Pi.single i 1))⁻¹
def IsExactForm (B : F.Site k → Fin 4 → imaginaryQuaternions) : Prop :=
  ∃ l : (Fin 4 → ℤ) → imaginaryQuaternions, ∀ z i, B (siteOfCoords k z) i = l z - l (z + Pi.single i 1)
structure IsNondegenerateAtTrivial [Fintype (F.Site k)] (A : F.GaugeField k → ℝ) : Prop where
  nonneg : ∀ W, 0 ≤ A W
  trivial_eq_zero : A (trivialBlockField F k) = 0
  continuous : Continuous A
  isPureGauge_of_eq_zero : ∀ W, A W = 0 → IsPureGauge W
  analyticAt_trivial : AnalyticAt ℝ (fun Y : F.Site k → Fin 4 → ℍ[ℝ] => A (fieldOfQuaternions Y))
    (quaternionsOfField (trivialBlockField F k))
  isExactForm_of_deriv : ∀ B : F.Site k → Fin 4 → imaginaryQuaternions,
    deriv (deriv fun τ : ℝ => A (fieldAlongLine B τ)) 0 = 0 → IsExactForm B
end RunningCouplingSlope
end YangMills.Construction
end
