import YangMills.Construction.ClusterExpansionOfAStep.LogarithmOfAMove
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction.TorusPaths
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields YangMills.Construction.QuaternionLogarithm YangMills.Construction.ColdStepAtMirrorFrames
variable {n k : ℕ}
abbrev BondWord (n : ℕ) : Type := List (TorusBond n × Bool)
def orientedValue (s : Bool) (g : UnitQuaternion) : UnitQuaternion := if s then g else g⁻¹
def wordHolonomy (U : TorusField n) : BondWord n → UnitQuaternion
  | [] => 1
  | e :: r => orientedValue e.2 (U e.1.1 e.1.2) * wordHolonomy U r
def perturbationGenerator (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (b : TorusBond n) :
    (Fin k → ℝ) →L[ℝ] ℍ[ℝ] :=
  ∑ i, if c i = b then (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (X i : ℍ[ℝ]) else 0
theorem perturbationGenerator_apply (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (b : TorusBond n) (t : Fin k → ℝ) :
    perturbationGenerator c X b t =
      (((∑ i, if c i = b then t i • X i else 0 : imaginaryQuaternions)) : ℍ[ℝ]) := by
  rw [perturbationGenerator, ContinuousLinearMap.sum_apply, AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp
theorem coe_perturb_bond (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (t : Fin k → ℝ)
    (U : TorusField n) (b : TorusBond n) :
    ((perturb c X t U b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) =
      NormedSpace.exp (perturbationGenerator c X b t) * ((U b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) := by
  rw [perturbationGenerator_apply]
  rfl
theorem norm_perturbationGenerator_le (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (hX : AreUnitVectors X) (b : TorusBond n) :
    ‖perturbationGenerator c X b‖ ≤ k := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun t => ?_
  rw [perturbationGenerator_apply, AddSubmonoidClass.coe_finsetSum]
  calc ‖∑ i, (((if c i = b then t i • X i else 0 : imaginaryQuaternions)) : ℍ[ℝ])‖
      ≤ ∑ i, ‖(((if c i = b then t i • X i else 0 : imaginaryQuaternions)) : ℍ[ℝ])‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin k, ‖t‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        split_ifs
        · have h1 : ‖((X i : imaginaryQuaternions) : ℍ[ℝ])‖ = 1 := hX i
          have h2 : (((t i • X i : imaginaryQuaternions)) : ℍ[ℝ]) =
              t i • ((X i : imaginaryQuaternions) : ℍ[ℝ]) := rfl
          rw [h2, norm_smul, h1, mul_one]
          exact norm_le_pi_norm t i
        · simp
    _ = k * ‖t‖ := by simp
def quaternionRightMul (w : ℍ[ℝ]) : ℍ[ℝ] →L[ℝ] ℍ[ℝ] := (ContinuousLinearMap.mul ℝ ℍ[ℝ]).flip w
def quaternionConj : ℍ[ℝ] →L[ℝ] ℍ[ℝ] :=
  LinearMap.toContinuousLinearMap
    { toFun := star, map_add' := star_add, map_smul' := fun a q => by ext <;> simp }
theorem quaternionConj_apply (q : ℍ[ℝ]) : quaternionConj q = star q := rfl
theorem norm_quaternionRightMul_le (g : UnitQuaternion) : ‖quaternionRightMul (g : ℍ[ℝ])‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun q => ?_
  show ‖q * (g : ℍ[ℝ])‖ ≤ 1 * ‖q‖
  rw [norm_mul, norm_unitQuaternion, mul_one, one_mul]
theorem norm_quaternionConj_le : ‖quaternionConj‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun q => ?_
  rw [quaternionConj_apply, norm_star, one_mul]
def orientedFactor (s : Bool) (g : UnitQuaternion) : ℍ[ℝ] →L[ℝ] ℍ[ℝ] :=
  if s then quaternionRightMul (g : ℍ[ℝ]) else quaternionConj.comp (quaternionRightMul (g : ℍ[ℝ]))
theorem norm_orientedFactor_le (s : Bool) (g : UnitQuaternion) : ‖orientedFactor s g‖ ≤ 1 := by
  unfold orientedFactor
  split_ifs
  · exact norm_quaternionRightMul_le g
  · refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have h1 := norm_quaternionConj_le
    have h2 := norm_quaternionRightMul_le g
    have h3 := norm_nonneg (quaternionRightMul (g : ℍ[ℝ]))
    nlinarith [norm_nonneg quaternionConj]
def letterValue (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (U : TorusField n)
    (e : TorusBond n × Bool) (t : Fin k → ℝ) : ℍ[ℝ] :=
  orientedFactor e.2 (U e.1.1 e.1.2) (NormedSpace.exp (perturbationGenerator c X e.1 t))
theorem letterValue_eq (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (U : TorusField n)
    (e : TorusBond n × Bool) (t : Fin k → ℝ) :
    letterValue c X U e t = ((orientedValue e.2 (perturb c X t U e.1.1 e.1.2) : UnitQuaternion) : ℍ[ℝ]) := by
  have h := coe_perturb_bond c X t U e.1
  unfold letterValue orientedFactor orientedValue
  cases e.2
  · simp only [Bool.false_eq_true, if_false]
    show star (NormedSpace.exp (perturbationGenerator c X e.1 t) * ((U e.1.1 e.1.2 : UnitQuaternion) : ℍ[ℝ])) = _
    rw [← h, coe_inv_unitQuaternion]
  · simp only [if_true]
    show NormedSpace.exp (perturbationGenerator c X e.1 t) * ((U e.1.1 e.1.2 : UnitQuaternion) : ℍ[ℝ]) = _
    rw [← h]
theorem contDiff_letterValue (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (U : TorusField n)
    (e : TorusBond n × Bool) :
    ContDiff ℝ ⊤ (letterValue c X U e) :=
  (orientedFactor e.2 (U e.1.1 e.1.2)).contDiff.comp
    (contDiff_exp_quaternion.comp (perturbationGenerator c X e.1).contDiff)
def letterDerivBound : ℝ :=
  ∑ j ∈ Finset.range 4, ‖iteratedFDeriv ℝ j (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) 0‖ * 3 ^ j + 1
theorem one_le_letterDerivBound : 1 ≤ letterDerivBound := by
  have : 0 ≤ ∑ j ∈ Finset.range 4, ‖iteratedFDeriv ℝ j (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) 0‖ * 3 ^ j :=
    Finset.sum_nonneg fun _ _ => by positivity
  unfold letterDerivBound
  linarith
theorem norm_iteratedFDeriv_letterValue_le (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (hX : AreUnitVectors X) (hk : k ≤ 3) (U : TorusField n)
    (e : TorusBond n × Bool) {j : ℕ} (hj : j ≤ 3) :
    ‖iteratedFDeriv ℝ j (letterValue c X U e) 0‖ ≤ letterDerivBound := by
  have hl : ‖perturbationGenerator c X e.1‖ ≤ 3 :=
    (norm_perturbationGenerator_le c X hX e.1).trans (by exact_mod_cast hk)
  have hexp : ContDiff ℝ ⊤ ((NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) ∘ perturbationGenerator c X e.1) :=
    contDiff_exp_quaternion.comp (perturbationGenerator c X e.1).contDiff
  have h1 : iteratedFDeriv ℝ j (letterValue c X U e) 0 =
      (orientedFactor e.2 (U e.1.1 e.1.2)).compContinuousMultilinearMap
        (iteratedFDeriv ℝ j ((NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) ∘ perturbationGenerator c X e.1) 0) :=
    (orientedFactor e.2 (U e.1.1 e.1.2)).iteratedFDeriv_comp_left (n := ⊤) hexp.contDiffAt
      (by exact_mod_cast le_top)
  have h2 : iteratedFDeriv ℝ j ((NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) ∘ perturbationGenerator c X e.1) 0 =
      (iteratedFDeriv ℝ j (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ])
        (perturbationGenerator c X e.1 0)).compContinuousLinearMap
        fun _ => perturbationGenerator c X e.1 :=
    (perturbationGenerator c X e.1).iteratedFDeriv_comp_right (n := ⊤) contDiff_exp_quaternion 0
      (by exact_mod_cast le_top)
  rw [h1, h2, map_zero]
  set E := ‖iteratedFDeriv ℝ j (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) 0‖ with hE
  have h3 : ‖((iteratedFDeriv ℝ j (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) 0).compContinuousLinearMap
      fun _ => perturbationGenerator c X e.1)‖ ≤ E * 3 ^ j := by
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hl j) (norm_nonneg _)
  have h4 : E * 3 ^ j ≤ letterDerivBound := by
    have hmem : j ∈ Finset.range 4 := Finset.mem_range.mpr (by omega)
    have hs : E * 3 ^ j ≤
        ∑ j ∈ Finset.range 4, ‖iteratedFDeriv ℝ j (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) 0‖ * 3 ^ j :=
      Finset.single_le_sum (f := fun j => ‖iteratedFDeriv ℝ j (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) 0‖ * 3 ^ j)
        (fun i _ => by positivity) hmem
    unfold letterDerivBound
    linarith
  refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
  calc _ ≤ 1 * (E * 3 ^ j) := mul_le_mul (norm_orientedFactor_le _ _) h3 (norm_nonneg _) zero_le_one
    _ ≤ letterDerivBound := by rw [one_mul]; exact h4
def perturbedHolonomy (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (U : TorusField n)
    (w : BondWord n) (t : Fin k → ℝ) : ℍ[ℝ] :=
  ((wordHolonomy (perturb c X t U) w : UnitQuaternion) : ℍ[ℝ])
theorem perturbedHolonomy_cons (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (U : TorusField n)
    (e : TorusBond n × Bool) (w : BondWord n) :
    perturbedHolonomy c X U (e :: w) = fun t => letterValue c X U e t * perturbedHolonomy c X U w t := by
  funext t
  rw [letterValue_eq]
  rfl
theorem contDiff_perturbedHolonomy (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (U : TorusField n) (w : BondWord n) :
    ContDiff ℝ ⊤ (perturbedHolonomy c X U w) := by
  induction w with
  | nil => exact contDiff_const
  | cons e r ih =>
    rw [perturbedHolonomy_cons]
    exact (contDiff_letterValue c X U e).mul ih
theorem norm_iteratedFDeriv_perturbedHolonomy_le (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (hX : AreUnitVectors X) (hk : k ≤ 3) (U : TorusField n)
    (w : BondWord n) {j : ℕ} (hj : j ≤ 3) :
    ‖iteratedFDeriv ℝ j (perturbedHolonomy c X U w) 0‖ ≤ (8 * letterDerivBound) ^ w.length := by
  have hA := one_le_letterDerivBound
  induction w generalizing j with
  | nil =>
    have hc : perturbedHolonomy c X U ([] : BondWord n) = fun _ => (1 : ℍ[ℝ]) := by
      funext t
      rfl
    rw [hc]
    cases j with
    | zero => simp
    | succ i => simp [iteratedFDeriv_const_of_ne (𝕜 := ℝ) (Nat.succ_ne_zero i) (1 : ℍ[ℝ])]
  | cons e r ih =>
    rw [perturbedHolonomy_cons]
    refine (norm_iteratedFDeriv_mul_le (N := ⊤) (contDiff_letterValue c X U e)
      (contDiff_perturbedHolonomy c X U r) 0 (by exact_mod_cast le_top)).trans ?_
    set B := (8 * letterDerivBound) ^ r.length with hB
    have hB0 : 0 ≤ B := by positivity
    have hterm : ∀ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (letterValue c X U e) 0‖ *
          ‖iteratedFDeriv ℝ (j - i) (perturbedHolonomy c X U r) 0‖ ≤
            (j.choose i : ℝ) * (letterDerivBound * B) := by
      intro i hi
      have hi' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have a1 := norm_iteratedFDeriv_letterValue_le c X hX hk U e (j := i) (by omega)
      have a2 := ih (j := j - i) (by omega)
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul a1 a2 (norm_nonneg _) (by linarith)) (by positivity)
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.sum_mul]
    have hsum : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) = 2 ^ j := by
      exact_mod_cast Nat.sum_range_choose j
    rw [hsum, List.length_cons, pow_succ, ← hB]
    have h2 : (2 : ℝ) ^ j ≤ 8 := by
      calc (2 : ℝ) ^ j ≤ 2 ^ 3 := pow_le_pow_right₀ (by norm_num) hj
        _ = 8 := by norm_num
    have h3 : 0 ≤ letterDerivBound * B := by positivity
    calc (2 : ℝ) ^ j * (letterDerivBound * B) ≤ 8 * (letterDerivBound * B) := by gcongr
      _ = B * (8 * letterDerivBound) := by ring
theorem wordHolonomy_perturb_update (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (t : Fin k → ℝ) (U : TorusField n) (w : BondWord n)
    (i₀ : Fin k) (s : ℝ) (hw : ∀ e ∈ w, c i₀ ≠ e.1) :
    wordHolonomy (perturb c X (Function.update t i₀ s) U) w = wordHolonomy (perturb c X t U) w := by
  induction w with
  | nil => rfl
  | cons e r ih =>
    have h1 := ih fun e' he' => hw e' (List.mem_cons_of_mem _ he')
    have h2 : c i₀ ≠ e.1 := hw e List.mem_cons_self
    have h3 : perturb c X (Function.update t i₀ s) U e.1.1 e.1.2 = perturb c X t U e.1.1 e.1.2 := by
      unfold YangMills.Construction.TorusFields.perturb
      congr 2
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi0 : i = i₀
      · subst hi0
        rw [if_neg h2, if_neg h2]
      · rw [Function.update_of_ne hi0]
    show orientedValue e.2 _ * _ = orientedValue e.2 _ * _
    rw [h1, h3]
theorem iteratedFDeriv_coordinates_eq_zero_of_update {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : (Fin k → ℝ) → E}
    (hf : ContDiff ℝ ⊤ f) (i₀ : Fin k) (h : ∀ t, f (Function.update t i₀ 0) = f t) :
    iteratedFDeriv ℝ k f 0 (fun i => Pi.single i 1) = 0 := by
  classical
  set P : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) :=
    ContinuousLinearMap.pi fun i => if i = i₀ then 0 else ContinuousLinearMap.proj i with hP
  have hPa : ∀ t, P t = Function.update t i₀ 0 := by
    intro t
    funext i
    by_cases hi : i = i₀
    · subst hi
      simp [hP]
    · simp [hP, hi]
  have hfe : f = f ∘ P := by
    funext t
    simp only [Function.comp, hPa, h]
  have h1 : iteratedFDeriv ℝ k (f ∘ P) 0 =
      (iteratedFDeriv ℝ k f (P 0)).compContinuousLinearMap fun _ => P :=
    P.iteratedFDeriv_comp_right (n := ⊤) hf 0 (by exact_mod_cast le_top)
  rw [hfe, h1, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  refine ContinuousMultilinearMap.map_coord_zero _ i₀ ?_
  simp only [hPa]
  funext i
  by_cases hi : i = i₀
  · subst hi
    simp
  · simp [hi, Pi.single_eq_of_ne (Ne.symm hi)]
theorem norm_iteratedFDeriv_coordinates_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (Fin k → ℝ) → E) :
    ‖iteratedFDeriv ℝ k f 0 (fun i => Pi.single i 1)‖ ≤ ‖iteratedFDeriv ℝ k f 0‖ := by
  refine ((iteratedFDeriv ℝ k f 0).le_opNorm _).trans ?_
  have h1 : ∀ i ∈ (Finset.univ : Finset (Fin k)), ‖(Pi.single i 1 : Fin k → ℝ)‖ ≤ 1 := by
    intro i _
    rw [Pi.norm_single]
    simp
  have h2 : ∏ i, ‖(Pi.single i 1 : Fin k → ℝ)‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) h1
  exact mul_le_of_le_one_right (norm_nonneg _) h2
end YangMills.Construction.TorusPaths
end
