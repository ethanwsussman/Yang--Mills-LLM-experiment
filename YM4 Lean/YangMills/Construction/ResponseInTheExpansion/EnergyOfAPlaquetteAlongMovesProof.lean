import YangMills.Construction.ClusterExpansionOfAStep.DerivativesOfTheWilsonEnergyProofFormForm
import YangMills.Construction.ResponseInTheExpansion.EnergyOfAPlaquetteAlongMoves
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.WeightedResponses
open YangMills.Construction.TorusFields YangMills.Construction.BlockAverages
def realPartCLM : ℍ[ℝ] →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun q => q.re, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => by simp }
theorem contDiff_quaternion_exp : ContDiff ℝ ⊤ (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) := by apply _root_.YangMills.SharedProofs.p23558 <;> assumption
abbrev EdgePair : Type := (Fin 4 → ℍ[ℝ]) × (Fin 4 → ℍ[ℝ])
def plaquetteForm (z : EdgePair) : ℝ :=
  1 - realPartCLM (NormedSpace.exp (z.2 0) * z.1 0 * (NormedSpace.exp (z.2 1) * z.1 1) *
    star (NormedSpace.exp (z.2 2) * z.1 2) * star (NormedSpace.exp (z.2 3) * z.1 3))
def conjCLM : ℍ[ℝ] →L[ℝ] ℍ[ℝ] :=
  LinearMap.toContinuousLinearMap
    { toFun := star, map_add' := star_add, map_smul' := fun c q => by ext <;> simp }
theorem contDiff_quaternion_star : ContDiff ℝ ⊤ (star : ℍ[ℝ] → ℍ[ℝ]) := conjCLM.contDiff
theorem contDiff_plaquetteForm : ContDiff ℝ ⊤ plaquetteForm := by
  unfold plaquetteForm
  have hC (i : Fin 4) : ContDiff ℝ ⊤ fun z : EdgePair => z.1 i := by fun_prop
  have hV (i : Fin 4) : ContDiff ℝ ⊤ fun z : EdgePair => NormedSpace.exp (z.2 i) :=
    contDiff_quaternion_exp.comp (by fun_prop)
  have e (i : Fin 4) : ContDiff ℝ ⊤ fun z : EdgePair => NormedSpace.exp (z.2 i) * z.1 i :=
    (hV i).mul (hC i)
  exact contDiff_const.sub (realPartCLM.contDiff.comp
    ((((e 0).mul (e 1)).mul (contDiff_quaternion_star.comp (e 2))).mul (contDiff_quaternion_star.comp (e 3))))
variable {n k : ℕ}
def bondMoveCLM (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (b : TorusBond n) :
    (Fin k → ℝ) →L[ℝ] ℍ[ℝ] :=
  ∑ l, if c l = b then (ContinuousLinearMap.proj l : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (X l : ℍ[ℝ]) else 0
theorem coe_sum_move (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (b : TorusBond n)
    (σ : Fin k → ℝ) :
    (((∑ l, if c l = b then σ l • X l else 0 : imaginaryQuaternions)) : ℍ[ℝ]) = bondMoveCLM c X b σ := by
  rw [bondMoveCLM, _root_.sum_apply, AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp
theorem bondMoveCLM_single (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (b : TorusBond n)
    (l₀ : Fin k) :
    bondMoveCLM c X b (Pi.single l₀ 1) = if c l₀ = b then (X l₀ : ℍ[ℝ]) else 0 := by
  rw [bondMoveCLM, _root_.sum_apply, Finset.sum_eq_single l₀]
  · split_ifs <;> simp
  · intro l _ hl
    split_ifs <;> simp [hl]
  · simp
def edgeMoveCLM (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (x : TorusSite n) (μ ν : Fin 4) :
    (Fin k → ℝ) →L[ℝ] (Fin 4 → ℍ[ℝ]) :=
  ContinuousLinearMap.pi fun i => bondMoveCLM c X (plaquetteEdges x μ ν i)
def edgeValues (W : TorusField n) (x : TorusSite n) (μ ν : Fin 4) : Fin 4 → ℍ[ℝ] :=
  fun i => ((W (plaquetteEdges x μ ν i).1 (plaquetteEdges x μ ν i).2 : UnitQuaternion) : ℍ[ℝ])
theorem coe_perturb (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (σ : Fin k → ℝ)
    (W : TorusField n) (b : TorusBond n) :
    ((perturb c X σ W b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) =
      NormedSpace.exp (bondMoveCLM c X b σ) * ((W b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) := by
  have : (perturb c X σ W b.1 b.2 : UnitQuaternion) =
      expUnit (∑ l, if c l = (b.1, b.2) then σ l • X l else 0) * W b.1 b.2 :=
    rfl
  rw [this, Submonoid.coe_mul]
  congr 1
  show NormedSpace.exp _ = _
  rw [coe_sum_move]
theorem coe_inv_unitQuaternion (g : UnitQuaternion) : ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = star (g : ℍ[ℝ]) := by
  rw [← Unitary.star_eq_inv, Unitary.coe_star]
theorem plaquetteEnergy_perturb (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (σ : Fin k → ℝ)
    (W : TorusField n) (x : TorusSite n) (μ ν : Fin 4) :
    plaquetteEnergy (perturb c X σ W) x μ ν = plaquetteForm (edgeValues W x μ ν, edgeMoveCLM c X x μ ν σ) := by
  unfold plaquetteEnergy plaquetteForm holonomy
  have h1 := coe_perturb c X σ W (x, μ)
  have h2 := coe_perturb c X σ W (x + TorusFields.unitStep n μ, ν)
  have h3 := coe_perturb c X σ W (x + TorusFields.unitStep n ν, μ)
  have h4 := coe_perturb c X σ W (x, ν)
  simp only [Submonoid.coe_mul, coe_inv_unitQuaternion] at *
  rw [h1, h2, h3, h4]
  rfl
theorem exists_bound_iteratedFDeriv_plaquetteForm : ∃ M : ℝ, 0 ≤ M ∧ ∀ (m : ℕ), m ≤ 3 → ∀ C : Fin 4 → ℍ[ℝ],
    (∀ i, C i ∈ unitary ℍ[ℝ]) → ‖iteratedFDeriv ℝ m plaquetteForm (C, 0)‖ ≤ M := by
  have hK : IsCompact (Set.pi Set.univ fun _ : Fin 4 => (unitary ℍ[ℝ] : Set ℍ[ℝ])) :=
    isCompact_univ_pi fun _ => isCompact_unitary_quaternion
  have hb (m : ℕ) : ∃ M : ℝ, ∀ C ∈ Set.pi Set.univ fun _ : Fin 4 => (unitary ℍ[ℝ] : Set ℍ[ℝ]),
      ‖iteratedFDeriv ℝ m plaquetteForm (C, (0 : Fin 4 → ℍ[ℝ]))‖ ≤ M := by
    have hc : Continuous fun C : Fin 4 → ℍ[ℝ] => iteratedFDeriv ℝ m plaquetteForm (C, (0 : Fin 4 → ℍ[ℝ])) :=
      (contDiff_plaquetteForm.continuous_iteratedFDeriv (m := m) (by exact_mod_cast le_top)).comp (by fun_prop)
    exact hK.exists_bound_of_continuousOn hc.continuousOn
  choose M hM using hb
  refine ⟨|M 0| + |M 1| + |M 2| + |M 3|, by positivity, fun m hm C hC => ?_⟩
  have hCm : C ∈ Set.pi Set.univ fun _ : Fin 4 => (unitary ℍ[ℝ] : Set ℍ[ℝ]) := fun i _ => hC i
  have h0 := le_abs_self (M m)
  have := hM m C hCm
  interval_cases m <;> linarith [abs_nonneg (M 0), abs_nonneg (M 1), abs_nonneg (M 2), abs_nonneg (M 3)]
theorem contDiff_plaquetteEnergy_perturb (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (W : TorusField n) (x : TorusSite n) (μ ν : Fin 4) :
    ContDiff ℝ ⊤ fun σ : Fin k → ℝ => plaquetteEnergy (perturb c X σ W) x μ ν := by apply _root_.YangMills.Construction.WilsonDerivativeBounds.contDiff_plaquetteEnergy_perturb <;> assumption
theorem iteratedFDeriv_plaquetteEnergy_perturb (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (W : TorusField n) (x : TorusSite n) (μ ν : Fin 4) (m : Fin k → Fin k → ℝ) :
    iteratedFDeriv ℝ k (fun σ : Fin k → ℝ => plaquetteEnergy (perturb c X σ W) x μ ν) 0 m =
      iteratedFDeriv ℝ k plaquetteForm (edgeValues W x μ ν, 0) fun l =>
        (0, edgeMoveCLM c X x μ ν (m l)) := by
  let B : (Fin k → ℝ) →L[ℝ] EdgePair :=
    (ContinuousLinearMap.inr ℝ (Fin 4 → ℍ[ℝ]) (Fin 4 → ℍ[ℝ])).comp (edgeMoveCLM c X x μ ν)
  have hf : (fun σ : Fin k → ℝ => plaquetteEnergy (perturb c X σ W) x μ ν) =
      (fun z : EdgePair => plaquetteForm (z + (edgeValues W x μ ν, 0))) ∘ B := by
    funext σ
    simp [plaquetteEnergy_perturb, B]
  have hs : ContDiff ℝ ⊤ fun z : EdgePair => plaquetteForm (z + (edgeValues W x μ ν, 0)) :=
    contDiff_plaquetteForm.comp (contDiff_id.add contDiff_const)
  rw [hf, B.iteratedFDeriv_comp_right hs 0 (by exact_mod_cast le_top)]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_comp_add_right]
  simp [B]
open Classical in
theorem norm_edge_direction_le_one (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (hX : AreUnitVectors X) (x : TorusSite n) (μ ν : Fin 4) (l : Fin k) :
    ‖((0, edgeMoveCLM c X x μ ν (Pi.single l 1)) : EdgePair)‖ ≤ 1 := by
  rw [Prod.norm_def]
  refine max_le (by simp) ?_
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
  show ‖bondMoveCLM c X (plaquetteEdges x μ ν i) (Pi.single l 1)‖ ≤ 1
  rw [bondMoveCLM_single]
  split_ifs
  · exact (hX l).le
  · simp
theorem plaquetteEnergySmoothBound_holds : PlaquetteEnergySmoothBound := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_iteratedFDeriv_plaquetteForm
  refine ⟨M, hM0, fun n k W x μ ν c X =>
    ⟨contDiff_plaquetteEnergy_perturb c X W x μ ν, fun hk hX => ?_, fun l hl => ?_⟩⟩
  · have hunit : ∀ i : Fin 4, edgeValues W x μ ν i ∈ unitary ℍ[ℝ] :=
      fun i => (W (plaquetteEdges x μ ν i).1 (plaquetteEdges x μ ν i).2).2
    unfold mixedDeriv
    rw [iteratedFDeriv_plaquetteEnergy_perturb, ← Real.norm_eq_abs]
    refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
    have h1 := hM k hk (edgeValues W x μ ν) hunit
    have h2 : ∏ l : Fin k, ‖((0, edgeMoveCLM c X x μ ν (Pi.single l 1)) : EdgePair)‖ ≤ 1 :=
      Finset.prod_le_one (fun _ _ => norm_nonneg _) fun l _ => norm_edge_direction_le_one c X hX _ _ _ l
    calc _ ≤ M * 1 := mul_le_mul h1 h2 (Finset.prod_nonneg fun _ _ => norm_nonneg _) hM0
      _ = M := mul_one M
  · have hz : ((0, edgeMoveCLM c X x μ ν (Pi.single l 1)) : EdgePair) = 0 := by
      ext1
      · rfl
      · funext i
        show bondMoveCLM c X (plaquetteEdges x μ ν i) (Pi.single l 1) = 0
        rw [bondMoveCLM_single, if_neg fun h => hl i h.symm]
    unfold mixedDeriv
    rw [iteratedFDeriv_plaquetteEnergy_perturb, ContinuousMultilinearMap.map_coord_zero _ l hz]
end YangMills.Construction.WeightedResponses
end
