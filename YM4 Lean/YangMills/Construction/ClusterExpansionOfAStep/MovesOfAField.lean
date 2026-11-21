import YangMills.Construction.ClusterExpansionOfAStep.DerivativesFromDifferences
import YangMills.Construction.ClusterExpansionOfAStep.PlaquettesUnderGaugesAndMoves
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace FieldMoves
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields
section Calculus
variable {E E' F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem iteratedFDeriv_comp_const_add (f : E → F) (a : E) (k : ℕ) :
    iteratedFDeriv ℝ k (fun z => f (a + z)) = fun z => iteratedFDeriv ℝ k f (a + z) := by
  induction k with
  | zero =>
    funext z
    ext m
    simp
  | succ k ih =>
    funext z
    rw [iteratedFDeriv_succ_eq_comp_left, iteratedFDeriv_succ_eq_comp_left, ih]
    simp only [Function.comp]
    rw [fderiv_comp_add_left]
theorem iteratedFDeriv_comp_continuousLinearMap (L : E' →L[ℝ] E) {f : E → F} {x : E'} {k : ℕ}
    (hf : ContDiffAt ℝ k f (L x)) :
    iteratedFDeriv ℝ k (f ∘ L) x =
      (iteratedFDeriv ℝ k f (L x)).compContinuousLinearMap fun _ => L := by
  obtain ⟨u, uo, xu, hu⟩ := (contDiffWithinAt_univ.mpr hf).contDiffOn' (m := k) le_rfl (by simp)
  have hu' : ContDiffOn ℝ k f u := by simpa using hu
  have hpre : IsOpen (L ⁻¹' u) := uo.preimage L.continuous
  have h := L.iteratedFDerivWithin_comp_right hu' uo.uniqueDiffOn hpre.uniqueDiffOn xu le_rfl
  rw [iteratedFDerivWithin_of_isOpen k hpre xu, iteratedFDerivWithin_of_isOpen k uo xu] at h
  exact h
theorem iteratedFDeriv_comp_affine_zero (L : E' →L[ℝ] E) {f : E → F} {p : E} {k : ℕ}
    (hf : ContDiffAt ℝ k f p) (v : Fin k → E') :
    iteratedFDeriv ℝ k (fun τ => f (p + L τ)) 0 v = iteratedFDeriv ℝ k f p fun i => L (v i) := by
  have hg : ContDiffAt ℝ k (fun z => f (p + z)) (L 0) := by
    have h1 : ContDiffAt ℝ k (fun z : E => p + z) (L 0) := contDiffAt_const.add contDiffAt_id
    have h2 : ContDiffAt ℝ k f (p + L 0) := by simpa using hf
    exact h2.comp (L 0) h1
  have h := iteratedFDeriv_comp_continuousLinearMap L hg
  have e : (fun τ => f (p + L τ)) = (fun z => f (p + z)) ∘ L := rfl
  rw [e, h, iteratedFDeriv_comp_const_add]
  simp
end Calculus
variable {n : ℕ}
def bondShift {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (σ : Fin k → ℝ)
    (β : TorusBond n) : imaginaryQuaternions :=
  ∑ l, if c l = β then σ l • X l else 0
theorem perturb_apply {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (σ : Fin k → ℝ)
    (W : TorusField n) (x : TorusSite n) (i : Fin 4) :
    perturb c X σ W x i = expUnit (bondShift c X σ (x, i)) * W x i := rfl
theorem expUnit_add_of_commute {a b : imaginaryQuaternions} (h : Commute (a : ℍ[ℝ]) (b : ℍ[ℝ])) :
    expUnit (a + b) = expUnit a * expUnit b := by
  apply Subtype.ext
  simp only [expUnit, Submonoid.coe_mul, Submodule.coe_add]
  have hr := NormedSpace.expSeries_radius_eq_top ℝ ℍ[ℝ]
  exact NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ) h (by rw [hr]; simp) (by rw [hr]; simp)
def CommutingPair (c : Fin 2 → TorusBond n) (X : Fin 2 → imaginaryQuaternions) : Prop :=
  c 0 ≠ c 1 ∨ X 0 = X 1
theorem bondShift_pair (c : Fin 2 → TorusBond n) (X : Fin 2 → imaginaryQuaternions) (σ : Fin 2 → ℝ)
    (β : TorusBond n) :
    bondShift c X σ β = (if c 0 = β then σ 0 • X 0 else 0) + (if c 1 = β then σ 1 • X 1 else 0) :=
  Fin.sum_univ_two _
theorem exists_bondShift_smul_common {c : Fin 2 → TorusBond n} {X : Fin 2 → imaginaryQuaternions}
    (h : CommutingPair c X) (σ σ' : Fin 2 → ℝ) (β : TorusBond n) :
    ∃ (Z : imaginaryQuaternions) (a a' : ℝ), bondShift c X σ β = a • Z ∧ bondShift c X σ' β = a' • Z := by
  rw [bondShift_pair, bondShift_pair]
  rcases h with h | h
  · by_cases h0 : c 0 = β
    · have h1 : c 1 ≠ β := fun e => h (h0.trans e.symm)
      exact ⟨X 0, σ 0, σ' 0, by simp [h0, h1], by simp [h0, h1]⟩
    · by_cases h1 : c 1 = β
      · exact ⟨X 1, σ 1, σ' 1, by simp [h0, h1], by simp [h0, h1]⟩
      · exact ⟨0, 0, 0, by simp [h0, h1], by simp [h0, h1]⟩
  · refine ⟨X 0, (if c 0 = β then σ 0 else 0) + (if c 1 = β then σ 1 else 0),
      (if c 0 = β then σ' 0 else 0) + (if c 1 = β then σ' 1 else 0), ?_, ?_⟩ <;>
    · rw [h]
      split_ifs <;> simp [add_smul]
theorem bondShift_add {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (σ σ' : Fin k → ℝ) (β : TorusBond n) :
    bondShift c X (σ + σ') β = bondShift c X σ β + bondShift c X σ' β := by
  unfold bondShift
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp [add_smul]
theorem perturb_perturb {c : Fin 2 → TorusBond n} {X : Fin 2 → imaginaryQuaternions}
    (h : CommutingPair c X) (σ σ' : Fin 2 → ℝ) (W : TorusField n) :
    perturb c X σ' (perturb c X σ W) = perturb c X (σ + σ') W := by
  funext x i
  simp only [perturb_apply]
  rw [← mul_assoc, add_comm σ σ', bondShift_add, expUnit_add_of_commute]
  obtain ⟨Z, a, a', e, e'⟩ := exists_bondShift_smul_common h σ' σ (x, i)
  rw [e, e']
  exact ((Commute.refl (Z : ℍ[ℝ])).smul_left a).smul_right a'
def pullParams {k m : ℕ} (ι : Fin k → Fin m) (τ : Fin k → ℝ) : Fin m → ℝ :=
  fun i => ∑ l, if ι l = i then τ l else 0
theorem bondShift_comp {k m : ℕ} (c : Fin m → TorusBond n) (X : Fin m → imaginaryQuaternions)
    (ι : Fin k → Fin m) (τ : Fin k → ℝ) (β : TorusBond n) :
    bondShift (c ∘ ι) (X ∘ ι) τ β = bondShift c X (pullParams ι τ) β := by
  unfold bondShift pullParams
  have h1 : ∀ i, (if c i = β then (∑ l, if ι l = i then τ l else 0) • X i else 0) =
      ∑ l, if ι l = i then (if c i = β then τ l • X i else 0) else 0 := by
    intro i
    split_ifs with hc
    · rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun l _ => ?_
      split_ifs <;> simp
    · simp
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single (ι l)]
  · simp
  · intro i _ hi
    simp [Ne.symm hi]
  · simp
theorem perturb_comp {k m : ℕ} (c : Fin m → TorusBond n) (X : Fin m → imaginaryQuaternions)
    (ι : Fin k → Fin m) (τ : Fin k → ℝ) (W : TorusField n) :
    perturb (c ∘ ι) (X ∘ ι) τ W = perturb c X (pullParams ι τ) W := by
  funext x i
  simp only [perturb_apply, bondShift_comp]
def pullParamsCLM {k m : ℕ} (ι : Fin k → Fin m) : (Fin k → ℝ) →L[ℝ] (Fin m → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := pullParams ι
      map_add' := by
        intro a b
        funext i
        simp only [pullParams, Pi.add_apply]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun l _ => ?_
        split_ifs <;> simp
      map_smul' := by
        intro a b
        funext i
        simp only [pullParams, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        split_ifs <;> simp }
theorem pullParamsCLM_apply {k m : ℕ} (ι : Fin k → Fin m) (τ : Fin k → ℝ) :
    pullParamsCLM ι τ = pullParams ι τ := rfl
theorem pullParamsCLM_single {k m : ℕ} (ι : Fin k → Fin m) (l : Fin k) :
    pullParamsCLM ι (Pi.single l 1) = Pi.single (ι l) 1 := by
  rw [pullParamsCLM_apply]
  funext i
  simp only [pullParams, Pi.single_apply]
  rw [Finset.sum_eq_single l]
  · simp [eq_comm]
  · intro b _ hb
    simp [hb]
  · simp
def alongPair (F : TorusField n → ℝ) (c : Fin 2 → TorusBond n) (X : Fin 2 → imaginaryQuaternions)
    (W : TorusField n) (σ : Fin 2 → ℝ) : ℝ :=
  F (perturb c X σ W)
theorem mixedDeriv_perturb_eq_iteratedFDeriv {F : TorusField n → ℝ} {c : Fin 2 → TorusBond n}
    {X : Fin 2 → imaginaryQuaternions} {W : TorusField n}
    (h : CommutingPair c X) {k : ℕ} (ι : Fin k → Fin 2) (σ₀ : Fin 2 → ℝ)
    (hC : ContDiffAt ℝ k (alongPair F c X W) σ₀) :
    mixedDeriv F (perturb c X σ₀ W) (c ∘ ι) (X ∘ ι) =
      iteratedFDeriv ℝ k (alongPair F c X W) σ₀ fun l => Pi.single (ι l) 1 := by
  unfold mixedDeriv
  have e : (fun τ : Fin k → ℝ => F (perturb (c ∘ ι) (X ∘ ι) τ (perturb c X σ₀ W))) =
      fun τ => alongPair F c X W (σ₀ + pullParamsCLM ι τ) := by
    funext τ
    rw [perturb_comp, perturb_perturb h]
    rfl
  rw [e, iteratedFDeriv_comp_affine_zero (pullParamsCLM ι) hC]
  simp only [pullParamsCLM_single]
theorem contDiffAt_alongPair {F : TorusField n → ℝ} {c : Fin 2 → TorusBond n}
    {X : Fin 2 → imaginaryQuaternions} {W : TorusField n}
    (h : CommutingPair c X) (σ₀ : Fin 2 → ℝ)
    (hC : ContDiffAt ℝ 3 (fun τ : Fin 2 → ℝ => F (perturb c X τ (perturb c X σ₀ W))) 0) :
    ContDiffAt ℝ 3 (alongPair F c X W) σ₀ := by
  have e : (fun τ : Fin 2 → ℝ => F (perturb c X τ (perturb c X σ₀ W))) =
      fun τ => alongPair F c X W (σ₀ + τ) := by
    funext τ
    rw [perturb_perturb h]
    rfl
  rw [e] at hC
  have h1 : ContDiffAt ℝ 3 (fun σ : Fin 2 → ℝ => σ - σ₀) σ₀ := contDiffAt_id.sub contDiffAt_const
  have h2 : ContDiffAt ℝ 3 (fun τ => alongPair F c X W (σ₀ + τ)) ((fun σ : Fin 2 → ℝ => σ - σ₀) σ₀) := by
    simpa using hC
  have h3 : ContDiffAt ℝ 3 (fun σ : Fin 2 → ℝ => (fun τ => alongPair F c X W (σ₀ + τ)) (σ - σ₀)) σ₀ :=
    ContDiffAt.comp (f := fun σ : Fin 2 → ℝ => σ - σ₀) σ₀ h2 h1
  refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun σ => ?_)
  simp
theorem abs_iteratedFDeriv_two_le_of_mixed_difference {U : (Fin 2 → ℝ) → ℝ} {h M e : ℝ} (hh : 0 < h)
    (hC : ∀ σ : Fin 2 → ℝ, (∀ i, 0 ≤ σ i ∧ σ i ≤ h) → ContDiffAt ℝ 3 U σ)
    (h3 : ∀ σ : Fin 2 → ℝ, (∀ i, 0 ≤ σ i ∧ σ i ≤ h) → ∀ ι : Fin 3 → Fin 2,
      |iteratedFDeriv ℝ 3 U σ fun l => Pi.single (ι l) 1| ≤ M)
    (hd : |U ![h, h] - U ![h, 0] - U ![0, h] + U 0| ≤ e) :
    |iteratedFDeriv ℝ 2 U 0 fun l => Pi.single l 1| ≤ e / h ^ 2 + 2 * M * h := by
  set u : Fin 2 → ℝ := Pi.single 1 1 with hu
  set v : Fin 2 → ℝ := Pi.single 0 1 with hv
  have pt : ∀ s t : ℝ, s • u + t • v = ![t, s] := by
    intro s t
    funext i
    fin_cases i <;> simp [hu, hv]
  have sq : ∀ s t : ℝ, 0 ≤ s → s ≤ h → 0 ≤ t → t ≤ h → ∀ i, 0 ≤ (s • u + t • v) i ∧ (s • u + t • v) i ≤ h := by
    intro s t a b c d i
    rw [pt]
    fin_cases i <;> simp [a, b, c, d]
  have third : ∀ s t : ℝ, 0 ≤ s → s ≤ h → 0 ≤ t → t ≤ h → ∀ ι : Fin 3 → Fin 2,
      |fderiv ℝ (fderiv ℝ (fderiv ℝ U)) (s • u + t • v) (Pi.single (ι 0) 1) (Pi.single (ι 1) 1)
        (Pi.single (ι 2) 1)| ≤ M := by
    intro s t a b c d ι
    have := h3 _ (sq s t a b c d) ι
    rwa [YangMills.Construction.Calculus.iteratedFDeriv_three_apply_eq_fderiv] at this
  have key := YangMills.Construction.Calculus.abs_mixed_fderiv_le_of_mixed_difference (G := U) (u := u)
    (v := v) (h := h) (M := M) (e := e) hh (fun s t a b c d => hC _ (sq s t a b c d))
    (fun s t a b c d => third s t a b c d ![1, 0, 1])
    (fun s t a b c d => third s t a b c d ![0, 0, 1]) (by
      have e1 := pt h h
      have e2 := pt h 0
      have e3 := pt 0 h
      simp only [zero_smul, add_zero, zero_add] at e2 e3
      rw [e1, e2, e3]
      simpa [abs_sub_comm, sub_right_comm] using hd)
  rw [iteratedFDeriv_two_apply]
  exact key
theorem abs_iteratedFDeriv_one_le_of_difference {U : (Fin 2 → ℝ) → ℝ} {h M e : ℝ} (hh : 0 < h)
    (hC : ∀ s : ℝ, 0 ≤ s → s ≤ h → ContDiffAt ℝ 2 U ![s, 0])
    (h2 : ∀ s : ℝ, 0 ≤ s → s ≤ h → |iteratedFDeriv ℝ 2 U ![s, 0] fun _ => Pi.single 0 1| ≤ M)
    (hd : |U ![h, 0] - U 0| ≤ e) :
    |iteratedFDeriv ℝ 1 U 0 fun _ => Pi.single 0 1| ≤ e / h + M * h := by
  set u : Fin 2 → ℝ := Pi.single 0 1 with hu
  have pt : ∀ s : ℝ, s • u = ![s, 0] := by
    intro s
    funext i
    fin_cases i <;> simp [hu]
  have key := YangMills.Construction.Calculus.abs_fderiv_le_of_difference (G := U) (u := u) (h := h)
    (M := M) (e := e) hh
    (fun s a b => by rw [pt]; exact hC s a b)
    (fun s a b => by
      have := h2 s a b
      rw [iteratedFDeriv_two_apply] at this
      rw [pt]
      exact this)
    (by rw [pt]; exact hd)
  rw [iteratedFDeriv_one_apply]
  exact key
theorem curvature_le_add_of_close {W W' : TorusField n} {ε : ℝ}
    (h : ∀ x i, ‖((W' x i : UnitQuaternion) : ℍ[ℝ]) - W x i‖ ≤ ε)
    (x : TorusSite n) (μ ν : Fin 4) : curvature W' x μ ν ≤ curvature W x μ ν + 4 * ε := by
  have hinv : ∀ g g' : UnitQuaternion,
      ‖((g'⁻¹ : UnitQuaternion) : ℍ[ℝ]) - ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ = ‖(g' : ℍ[ℝ]) - g‖ := by
    intro g g'
    rw [coe_inv_unitQuaternion, coe_inv_unitQuaternion, ← star_sub, norm_star]
  have hn : ∀ g : UnitQuaternion, ‖(g : ℍ[ℝ])‖ = 1 := norm_unitQuaternion
  set a := W x μ
  set b := W (x + TorusFields.unitStep n μ) ν
  set c := W (x + TorusFields.unitStep n ν) μ
  set d := W x ν
  set a' := W' x μ
  set b' := W' (x + TorusFields.unitStep n μ) ν
  set c' := W' (x + TorusFields.unitStep n ν) μ
  set d' := W' x ν
  have h1 : ‖(a' : ℍ[ℝ]) - a‖ ≤ ε := h _ _
  have h2 : ‖(b' : ℍ[ℝ]) - b‖ ≤ ε := h _ _
  have h3 : ‖((c'⁻¹ : UnitQuaternion) : ℍ[ℝ]) - ((c⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ ≤ ε := by
    rw [hinv]; exact h _ _
  have h4 : ‖((d'⁻¹ : UnitQuaternion) : ℍ[ℝ]) - ((d⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ ≤ ε := by
    rw [hinv]; exact h _ _
  have key : ‖((holonomy W' x μ ν : UnitQuaternion) : ℍ[ℝ]) - (holonomy W x μ ν : UnitQuaternion)‖ ≤ 4 * ε := by
    have e : ((holonomy W' x μ ν : UnitQuaternion) : ℍ[ℝ]) - (holonomy W x μ ν : UnitQuaternion) =
        ((a' : ℍ[ℝ]) - a) * b' * ((c'⁻¹ : UnitQuaternion) : ℍ[ℝ]) * ((d'⁻¹ : UnitQuaternion) : ℍ[ℝ]) +
        (a : ℍ[ℝ]) * ((b' : ℍ[ℝ]) - b) * ((c'⁻¹ : UnitQuaternion) : ℍ[ℝ]) * ((d'⁻¹ : UnitQuaternion) : ℍ[ℝ]) +
        (a : ℍ[ℝ]) * b * (((c'⁻¹ : UnitQuaternion) : ℍ[ℝ]) - ((c⁻¹ : UnitQuaternion) : ℍ[ℝ])) *
          ((d'⁻¹ : UnitQuaternion) : ℍ[ℝ]) +
        (a : ℍ[ℝ]) * b * ((c⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
          (((d'⁻¹ : UnitQuaternion) : ℍ[ℝ]) - ((d⁻¹ : UnitQuaternion) : ℍ[ℝ])) := by
      simp only [holonomy, Submonoid.coe_mul]
      noncomm_ring
    rw [e]
    refine (norm_add₄_le).trans ?_
    simp only [norm_mul, hn, mul_one, one_mul]
    linarith
  unfold curvature
  calc ‖((holonomy W' x μ ν : UnitQuaternion) : ℍ[ℝ]) - 1‖
      = ‖(((holonomy W' x μ ν : UnitQuaternion) : ℍ[ℝ]) - (holonomy W x μ ν : UnitQuaternion)) +
          (((holonomy W x μ ν : UnitQuaternion) : ℍ[ℝ]) - 1)‖ := by
        congr 1
        abel
    _ ≤ 4 * ε + ‖((holonomy W x μ ν : UnitQuaternion) : ℍ[ℝ]) - 1‖ := (norm_add_le _ _).trans (by linarith)
    _ = ‖((holonomy W x μ ν : UnitQuaternion) : ℍ[ℝ]) - 1‖ + 4 * ε := add_comm _ _
end FieldMoves
end YangMills.Construction
end
