import YangMills.Construction.InfiniteLattice.InvariantFunctionsDensitiesAndACriterion
import YangMills.Construction.InfiniteLattice.MeansOfCorrelationsOverCubesProof
import YangMills.Construction.InfiniteLattice.MeansOverBoxesConvergeToTheConditionalExpectation
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped Topology ENNReal InnerProductSpace
noncomputable section
namespace YangMills.Construction.InfiniteLattice
namespace BoxAverages
section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
def intCube (n : ℕ) : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (0 : ℤ) ((n : ℤ) - 1)
theorem card_intCube (n : ℕ) : (intCube n).card = n ^ 4 := by
  simp [intCube]
def cubeAverage (U : (Fin 4 → ℤ) → E →ₗᵢ[ℂ] E) (n : ℕ) (x : E) : E :=
  ((n : ℂ) ^ 4)⁻¹ • ∑ k ∈ intCube n, U k x
theorem cubeAverage_add (U : (Fin 4 → ℤ) → E →ₗᵢ[ℂ] E) (n : ℕ) (x y : E) :
    cubeAverage U n (x + y) = cubeAverage U n x + cubeAverage U n y := by
  simp [cubeAverage, Finset.sum_add_distrib, smul_add]
theorem cubeAverage_smul (U : (Fin 4 → ℤ) → E →ₗᵢ[ℂ] E) (n : ℕ) (c : ℂ) (x : E) :
    cubeAverage U n (c • x) = c • cubeAverage U n x := by
  simp only [cubeAverage, map_smul, ← Finset.smul_sum]
  rw [smul_comm]
theorem cubeAverage_zero (U : (Fin 4 → ℤ) → E →ₗᵢ[ℂ] E) (n : ℕ) : cubeAverage U n 0 = 0 := by
  simp [cubeAverage]
theorem norm_cubeAverage_le (U : (Fin 4 → ℤ) → E →ₗᵢ[ℂ] E) (n : ℕ) (x : E) :
    ‖cubeAverage U n x‖ ≤ ‖x‖ := by
  have hsum : ‖∑ k ∈ intCube n, U k x‖ ≤ (n : ℝ) ^ 4 * ‖x‖ := by
    refine (norm_sum_le _ _).trans ?_
    simp only [LinearIsometry.norm_map, Finset.sum_const, card_intCube, nsmul_eq_mul]
    push_cast
    exact le_rfl
  rw [cubeAverage, norm_smul, norm_inv, norm_pow, Complex.norm_natCast]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hpos : (0 : ℝ) < (n : ℝ) ^ 4 := by positivity
    rw [inv_mul_le_iff₀ hpos]
    exact hsum
def overlapCube (k : Fin 4 → ℤ) (n : ℕ) : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset fun i => Finset.Icc (max 0 (k i)) ((n : ℤ) - 1 + min 0 (k i))
theorem overlapCube_subset (k : Fin 4 → ℤ) (n : ℕ) : overlapCube k n ⊆ intCube n := by
  intro j hj
  simp only [overlapCube, intCube, Fintype.mem_piFinset, Finset.mem_Icc] at hj ⊢
  intro i
  have h := hj i
  omega
theorem overlapCube_subset_image_add (k : Fin 4 → ℤ) (n : ℕ) :
    overlapCube k n ⊆ (intCube n).image (· + k) := by
  intro j hj
  simp only [overlapCube, Fintype.mem_piFinset, Finset.mem_Icc] at hj
  refine Finset.mem_image.mpr ⟨j - k, ?_, by simp⟩
  simp only [intCube, Fintype.mem_piFinset, Finset.mem_Icc, Pi.sub_apply]
  intro i
  have h := hj i
  omega
theorem card_overlapCube (k : Fin 4 → ℤ) (n : ℕ) (hn : ∀ i, |k i| ≤ (n : ℤ)) :
    ((overlapCube k n).card : ℝ) = ∏ i, ((n : ℝ) - |(k i : ℝ)|) := by
  simp only [overlapCube, Fintype.card_piFinset, Int.card_Icc]
  push_cast
  refine Finset.prod_congr rfl fun i _ => ?_
  have hnn : (0 : ℤ) ≤ (n : ℤ) - 1 + min 0 (k i) + 1 - max 0 (k i) := by
    have := hn i
    rcases abs_cases (k i) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  have he : (n : ℤ) - 1 + min 0 (k i) + 1 - max 0 (k i) = (n : ℤ) - |k i| := by
    rcases abs_cases (k i) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  have hcast : ((((n : ℤ) - 1 + min 0 (k i) + 1 - max 0 (k i)).toNat : ℤ) : ℝ) =
      (n : ℝ) - |(k i : ℝ)| := by
    rw [Int.toNat_of_nonneg hnn, he]
    push_cast
    rfl
  exact_mod_cast hcast
theorem tendsto_one_sub_prod_overlap (k : Fin 4 → ℤ) :
    Tendsto (fun n : ℕ => 1 - ∏ i, (1 - |(k i : ℝ)| / (n : ℝ))) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => ∏ i, (1 - |(k i : ℝ)| / (n : ℝ))) atTop
      (𝓝 (∏ _i : Fin 4, (1 - 0 : ℝ))) :=
    tendsto_finsetProd _ fun i _ =>
      tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat _)
  have h2 := (tendsto_const_nhds (x := (1 : ℝ))).sub h
  simpa using h2
theorem norm_cubeAverage_sub_le (U : (Fin 4 → ℤ) → E →ₗᵢ[ℂ] E)
    (hU : ∀ j k x, U (j + k) x = U j (U k x)) (y : E) (k : Fin 4 → ℤ) (n : ℕ) (hn0 : 0 < n)
    (hn : ∀ i, |k i| ≤ (n : ℤ)) :
    ‖cubeAverage U n (y - U k y)‖ ≤ 2 * (1 - ∏ i, (1 - |(k i : ℝ)| / (n : ℝ))) * ‖y‖ := by
  classical
  set A := intCube n with hA
  set B := A.image (· + k) with hB
  set C := overlapCube k n with hC
  have hinj : Function.Injective fun j : Fin 4 → ℤ => j + k := add_left_injective k
  have hcardB : B.card = n ^ 4 := by
    rw [hB, Finset.card_image_of_injective _ hinj, hA, card_intCube]
  have hCA : C ⊆ A := overlapCube_subset k n
  have hCB : C ⊆ B := overlapCube_subset_image_add k n
  have hs1 : ∑ j ∈ A, U j (U k y) = ∑ j ∈ B, U j y := by
    rw [hB, Finset.sum_image fun _ _ _ _ h => hinj h]
    exact Finset.sum_congr rfl fun j _ => (hU j k y).symm
  have hd : ∑ j ∈ A, U j y - ∑ j ∈ B, U j y =
      ∑ j ∈ A \ C, U j y - ∑ j ∈ B \ C, U j y := by
    rw [← Finset.sum_sdiff hCA, ← Finset.sum_sdiff hCB]
    abel
  have hb : ∀ s : Finset (Fin 4 → ℤ), ‖∑ j ∈ s, U j y‖ ≤ s.card * ‖y‖ := fun s => by
    refine (norm_sum_le _ _).trans ?_
    simp
  have hcA : ((A \ C).card : ℝ) = (n : ℝ) ^ 4 - C.card := by
    rw [Finset.card_sdiff_of_subset hCA, Nat.cast_sub (Finset.card_le_card hCA), hA,
      card_intCube]
    push_cast
    rfl
  have hcB : ((B \ C).card : ℝ) = (n : ℝ) ^ 4 - C.card := by
    rw [Finset.card_sdiff_of_subset hCB, Nat.cast_sub (Finset.card_le_card hCB), hcardB]
    push_cast
    rfl
  have hC4 : (C.card : ℝ) = (n : ℝ) ^ 4 * ∏ i, (1 - |(k i : ℝ)| / (n : ℝ)) := by
    rw [hC, card_overlapCube k n hn]
    have : ∀ i : Fin 4, (n : ℝ) - |(k i : ℝ)| = (n : ℝ) * (1 - |(k i : ℝ)| / (n : ℝ)) := fun i => by
      field_simp
    simp only [this, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  have hmean : cubeAverage U n (y - U k y) =
      ((n : ℂ) ^ 4)⁻¹ • (∑ j ∈ A \ C, U j y - ∑ j ∈ B \ C, U j y) := by
    rw [cubeAverage, ← hd, ← hs1, ← Finset.sum_sub_distrib]
    simp only [map_sub, hA]
  rw [hmean, norm_smul, norm_inv, norm_pow, Complex.norm_natCast]
  have hpos : (0 : ℝ) < (n : ℝ) ^ 4 := by positivity
  rw [inv_mul_le_iff₀ hpos]
  calc ‖∑ j ∈ A \ C, U j y - ∑ j ∈ B \ C, U j y‖
      ≤ ‖∑ j ∈ A \ C, U j y‖ + ‖∑ j ∈ B \ C, U j y‖ := norm_sub_le _ _
    _ ≤ (A \ C).card * ‖y‖ + (B \ C).card * ‖y‖ := add_le_add (hb _) (hb _)
    _ = (n : ℝ) ^ 4 * (2 * (1 - ∏ i, (1 - |(k i : ℝ)| / (n : ℝ))) * ‖y‖) := by
        rw [hcA, hcB, hC4]
        ring
theorem tendsto_cubeAverage_sub (U : (Fin 4 → ℤ) → E →ₗᵢ[ℂ] E)
    (hU : ∀ j k x, U (j + k) x = U j (U k x)) (y : E) (k : Fin 4 → ℤ) :
    Tendsto (fun n => cubeAverage U n (y - U k y)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hlim : Tendsto (fun n : ℕ => 2 * (1 - ∏ i, (1 - |(k i : ℝ)| / (n : ℝ))) * ‖y‖) atTop
      (𝓝 0) := by
    simpa using ((tendsto_one_sub_prod_overlap k).const_mul 2).mul_const ‖y‖
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop (1 + ∑ i, (k i).natAbs)] with n hn
  refine norm_cubeAverage_sub_le U hU y k n (by omega) fun i => ?_
  have h1 : (k i).natAbs ≤ ∑ i, (k i).natAbs :=
    Finset.single_le_sum (f := fun i => (k i).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  rw [Int.abs_eq_natAbs]
  omega
def averagesToZero (U : (Fin 4 → ℤ) → E →ₗᵢ[ℂ] E) : Submodule ℂ E where
  carrier := {x | Tendsto (fun n => cubeAverage U n x) atTop (𝓝 0)}
  add_mem' := fun {x y} hx hy => by
    simp only [Set.mem_ofPred_eq, cubeAverage_add] at hx hy ⊢
    simpa using hx.add hy
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, cubeAverage_zero]
    exact tendsto_const_nhds
  smul_mem' := fun c x hx => by
    simp only [Set.mem_ofPred_eq, cubeAverage_smul] at hx ⊢
    simpa using hx.const_smul c
theorem isClosed_averagesToZero (U : (Fin 4 → ℤ) → E →ₗᵢ[ℂ] E) :
    IsClosed (averagesToZero U : Set E) := by
  refine isClosed_of_closure_subset fun x hx => ?_
  change Tendsto (fun n => cubeAverage U n x) atTop (𝓝 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨y, hy, hd⟩ := Metric.mem_closure_iff.mp hx (ε / 2) (by positivity)
  have hy' : Tendsto (fun n => cubeAverage U n y) atTop (𝓝 0) := hy
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hy' (ε / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn
  rw [dist_zero_right] at h1 ⊢
  have h2 : cubeAverage U n x = cubeAverage U n (x - y) + cubeAverage U n y := by
    rw [← cubeAverage_add, sub_add_cancel]
  have h3 : ‖x - y‖ < ε / 2 := by rwa [← dist_eq_norm]
  calc ‖cubeAverage U n x‖ ≤ ‖cubeAverage U n (x - y)‖ + ‖cubeAverage U n y‖ := by
        rw [h2]; exact norm_add_le _ _
    _ ≤ ‖x - y‖ + ‖cubeAverage U n y‖ := by gcongr; exact norm_cubeAverage_le U n _
    _ < ε := by linarith
def invariantVectors (U : (Fin 4 → ℤ) → E →ₗᵢ[ℂ] E) : Submodule ℂ E where
  carrier := {x | ∀ k, U k x = x}
  add_mem' := fun {x y} hx hy k => by rw [map_add, hx k, hy k]
  zero_mem' := fun k => map_zero _
  smul_mem' := fun c x hx k => by rw [map_smul, hx k]
theorem mem_invariantVectors_of_inner_sub_eq_zero (U : (Fin 4 → ℤ) → E →ₗᵢ[ℂ] E) {x : E}
    (hx : ∀ y k, ⟪y - U k y, x⟫_ℂ = 0) : x ∈ invariantVectors U := by
  intro k
  have h0 : ⟪x - U k x, x⟫_ℂ = 0 := hx x k
  have h1 : ⟪U k x, x⟫_ℂ = ⟪x, x⟫_ℂ := by
    rw [inner_sub_left, sub_eq_zero] at h0
    exact h0.symm
  have h2 : ⟪U k x, U k x⟫_ℂ = ⟪x, x⟫_ℂ := (U k).inner_map_map x x
  have h3 : ⟪x, U k x⟫_ℂ = ⟪x, x⟫_ℂ := by
    rw [← inner_conj_symm, h1, inner_conj_symm]
  have h4 : ⟪x - U k x, x - U k x⟫_ℂ = 0 := by
    simp only [inner_sub_left, inner_sub_right, h1, h2, h3, sub_self]
  exact (sub_eq_zero.mp (inner_self_eq_zero.mp h4)).symm
variable [CompleteSpace E]
theorem exists_invariant_add_orthogonal (U : (Fin 4 → ℤ) → E →ₗᵢ[ℂ] E)
    (hU : ∀ j k x, U (j + k) x = U j (U k x)) (x : E) :
    ∃ x₀ x₁ : E, x = x₀ + x₁ ∧ (∀ k, U k x₀ = x₀) ∧
      (∀ w : E, (∀ k, U k w = w) → ⟪w, x₁⟫_ℂ = 0) ∧
      Tendsto (fun n => cubeAverage U n x) atTop (𝓝 x₀) := by
  have hclosed : IsClosed (invariantVectors U : Set E) := by
    have : (invariantVectors U : Set E) = ⋂ k, {x | U k x = x} := by
      ext x
      simp [invariantVectors]
    rw [this]
    exact isClosed_iInter fun k => isClosed_eq (U k).continuous continuous_id
  have : CompleteSpace (invariantVectors U) := hclosed.completeSpace_coe
  obtain ⟨x₀, h₀, x₁, h₁, rfl⟩ := (invariantVectors U).exists_add_mem_mem_orthogonal x
  refine ⟨x₀, x₁, rfl, h₀, fun w hw => h₁ w hw, ?_⟩
  set S : Submodule ℂ E := Submodule.span ℂ {w | ∃ y k, w = y - U k y} with hS
  have hSv : S ≤ averagesToZero U := by
    refine Submodule.span_le.mpr ?_
    rintro w ⟨y, k, rfl⟩
    exact tendsto_cubeAverage_sub U hU y k
  have hcl : S.topologicalClosure ≤ averagesToZero U :=
    Submodule.topologicalClosure_minimal S hSv (isClosed_averagesToZero U)
  have hSo : Sᗮ ≤ invariantVectors U := fun w hw =>
    mem_invariantVectors_of_inner_sub_eq_zero U fun y k =>
      hw _ (Submodule.subset_span ⟨y, k, rfl⟩)
  have hx₁ : x₁ ∈ S.topologicalClosure := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure]
    exact Submodule.orthogonal_le hSo h₁
  have hv : Tendsto (fun n => cubeAverage U n x₁) atTop (𝓝 0) := hcl hx₁
  have hfix : ∀ᶠ n : ℕ in atTop, cubeAverage U n x₀ = x₀ := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : ((n : ℂ) ^ 4) ≠ 0 := by
      have : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
      exact pow_ne_zero _ this
    have hsum : ∑ k ∈ intCube n, U k x₀ = ((n : ℂ) ^ 4) • x₀ := by
      rw [Finset.sum_congr rfl fun k _ => h₀ k, Finset.sum_const, card_intCube,
        ← Nat.cast_smul_eq_nsmul ℂ]
      push_cast
      rfl
    rw [cubeAverage, hsum, smul_smul, inv_mul_cancel₀ hn', one_smul]
  have hsum : Tendsto (fun n => cubeAverage U n x₀ + cubeAverage U n x₁) atTop (𝓝 (x₀ + 0)) :=
    (tendsto_const_nhds.congr' (hfix.mono fun _ h => h.symm)).add hv
  simpa only [add_zero, cubeAverage_add] using hsum
end Hilbert
section Shifts
variable {a : ℝ}
theorem measurePreserving_shift (μ : Measure (GaugeField a)) [IsProbabilityMeasure μ]
    (hμ : IsShiftInvariant μ) (v : LatticePoint a) :
    MeasurePreserving (shift v).pullbackField μ μ := by apply _root_.YangMills.Construction.LatticePhases.CubeErgodic.measurePreserving_shift <;> assumption
def koopman (μ : GaugeFieldProbability a) (hμ : IsShiftInvariant μ.1)
    (k : Fin 4 → ℤ) : StateL2 μ →ₗᵢ[ℂ] StateL2 μ :=
  haveI := μ.2
  Lp.compMeasurePreservingₗᵢ ℂ (shift (latticePointOfInt a k)).pullbackField
    (measurePreserving_shift μ.1 hμ _)
theorem koopman_coeFn (μ : GaugeFieldProbability a) (hμ : IsShiftInvariant μ.1)
    (k : Fin 4 → ℤ) (f : StateL2 μ) :
    (koopman μ hμ k f : GaugeField a → ℂ) =ᵐ[μ.1]
      (f : GaugeField a → ℂ) ∘ (shift (latticePointOfInt a k)).pullbackField :=
  have := μ.2
  Lp.coeFn_compMeasurePreserving f (measurePreserving_shift μ.1 hμ _)
theorem latticePointOfInt_add (j k : Fin 4 → ℤ) :
    latticePointOfInt a (k + j) = latticePointOfInt a k + latticePointOfInt a j := by
  refine Subtype.ext (funext fun i => ?_)
  simp [latticePointOfInt, add_mul]
theorem exists_latticePointOfInt (v : LatticePoint a) : ∃ k, v = latticePointOfInt a k := by
  obtain ⟨k, hk⟩ := v.2
  exact ⟨k, Subtype.ext (funext hk)⟩
theorem koopman_add (hcomp : ∀ v w : LatticePoint a, (shift v).pullbackField ∘ (shift w).pullbackField = (shift (v + w)).pullbackField) (μ : GaugeFieldProbability a)
    (hμ : IsShiftInvariant μ.1) (j k : Fin 4 → ℤ) (f : StateL2 μ) :
    koopman μ hμ (j + k) f = koopman μ hμ j (koopman μ hμ k f) := by
  have := μ.2
  refine Lp.ext ?_
  have hq : Measure.QuasiMeasurePreserving
      (shift (latticePointOfInt a j)).pullbackField μ.1 μ.1 :=
    (measurePreserving_shift μ.1 hμ _).quasiMeasurePreserving
  have h1 := koopman_coeFn μ hμ (j + k) f
  have h2 := koopman_coeFn μ hμ j (koopman μ hμ k f)
  have h3 := hq.ae_eq_comp (koopman_coeFn μ hμ k f)
  refine h1.trans (EventuallyEq.trans ?_ (h2.trans h3).symm)
  refine EventuallyEq.of_eq ?_
  rw [Function.comp_assoc, hcomp, add_comm j k, latticePointOfInt_add]
end Shifts
section Main
variable {a : ℝ}
theorem stateL2Norm_congr (μ : GaugeFieldProbability a) {f g : GaugeField a → ℂ}
    (h : f =ᵐ[μ.1] g) : stateL2Norm μ f = stateL2Norm μ g := by
  unfold stateL2Norm
  congr 1
  exact integral_congr_ae (h.mono fun A hA => by simp only [hA])
theorem coeFn_finsetSum {ι : Type*} (μ : GaugeFieldProbability a) (s : Finset ι)
    (f : ι → StateL2 μ) :
    ((∑ k ∈ s, f k : StateL2 μ) : GaugeField a → ℂ) =ᵐ[μ.1]
      fun A => ∑ k ∈ s, (f k : GaugeField a → ℂ) A := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Lp.coeFn_zero ℂ 2 μ.1
  | insert b s hb ih =>
    rw [Finset.sum_insert hb]
    filter_upwards [Lp.coeFn_add (f b) (∑ k ∈ s, f k), ih] with A h1 h2
    rw [h1, Pi.add_apply, h2, Finset.sum_insert hb]
theorem latticePointOfInt_injective (ha : a ≠ 0) :
    Function.Injective (latticePointOfInt a) := fun k k' h => by
  funext i
  have hi := congrFun (congrArg Subtype.val h) i
  simpa [latticePointOfInt, ha] using hi
theorem cubeAverage_ae_eq (ha : a ≠ 0) (μ : GaugeFieldProbability a)
    (hμ : IsShiftInvariant μ.1) {F : GaugeField a → ℂ} {f : StateL2 μ}
    (hF : (f : GaugeField a → ℂ) =ᵐ[μ.1] F) (n : ℕ) :
    ((cubeAverage (koopman μ hμ) n f : StateL2 μ) : GaugeField a → ℂ) =ᵐ[μ.1]
      cornerCubeAverage n F := by
  have := μ.2
  have hall : ∀ᵐ A ∂μ.1, ∀ k, (koopman μ hμ k f : GaugeField a → ℂ) A =
      F ((shift (latticePointOfInt a k)).pullbackField A) := by
    rw [ae_all_iff]
    intro k
    exact (koopman_coeFn μ hμ k f).trans
      ((measurePreserving_shift μ.1 hμ _).quasiMeasurePreserving.ae_eq_comp hF)
  filter_upwards [Lp.coeFn_smul (((n : ℂ) ^ 4)⁻¹) (∑ k ∈ intCube n, koopman μ hμ k f),
    coeFn_finsetSum μ (intCube n) fun k => koopman μ hμ k f, hall] with A h1 h2 h3
  classical
  rw [cubeAverage, h1, Pi.smul_apply, h2, cornerCubeAverage, cornerCube,
    Finset.sum_image fun _ _ _ _ h => latticePointOfInt_injective ha h, smul_eq_mul]
  congr 1
  exact Finset.sum_congr rfl fun k _ => h3 k
theorem tendsto_stateL2Norm (ha : a ≠ 0)
    (hcomp : ∀ v w : LatticePoint a, (shift v).pullbackField ∘ (shift w).pullbackField =
      (shift (v + w)).pullbackField)
    (hb : ShiftInvariance.AEInvariantAgreesOnInvariantSet a)
    (μ : GaugeFieldProbability a) (hμ : IsShiftInvariant μ.1)
    (F : GaugeField a → ℂ) (hF : IsBoundedObservable F) :
    Tendsto (fun n : ℕ => stateL2Norm μ fun A => cornerCubeAverage n F A - condExpShiftInvariant μ.1 F A)
      atTop (𝓝 0) := by
  have := μ.2
  have hFmem : MemLp F 2 μ.1 := by
    obtain ⟨hm, C, hC⟩ := hF
    exact MemLp.of_bound hm.aestronglyMeasurable C (ae_of_all _ hC)
  obtain ⟨f, hf⟩ : ∃ f : StateL2 μ, (f : GaugeField a → ℂ) =ᵐ[μ.1] F :=
    ⟨hFmem.toLp F, hFmem.coeFn_toLp⟩
  obtain ⟨f₀, f₁, hsum, hfix, hperp, hlim⟩ := exists_invariant_add_orthogonal (koopman μ hμ)
    (fun j k x => koopman_add hcomp μ hμ j k x) f
  have hgm : Measurable (f₀ : GaugeField a → ℂ) := (Lp.stronglyMeasurable f₀).measurable
  have hinv : ∀ v : LatticePoint a, (f₀ : GaugeField a → ℂ) ∘ (shift v).pullbackField =ᵐ[μ.1]
      (f₀ : GaugeField a → ℂ) := by
    intro v
    obtain ⟨k, rfl⟩ := exists_latticePointOfInt v
    have h := koopman_coeFn μ hμ k f₀
    rw [hfix k] at h
    exact h.symm
  obtain ⟨V, hV, hV1, hJ⟩ := hb μ hμ _ hgm hinv
  have hJg : (fun A => (f₀ : GaugeField a → ℂ) A * V.indicator (1 : GaugeField a → ℂ) A)
      =ᵐ[μ.1] (f₀ : GaugeField a → ℂ) := by
    have hVae : ∀ᵐ A ∂μ.1, A ∈ V := by
      rw [ae_iff]
      exact (prob_compl_eq_zero_iff hV.1).mpr hV1
    filter_upwards [hVae] with A hA
    simp [hA]
  have hm : shiftInvariantSigma a ≤ (inferInstance : MeasurableSpace (GaugeField a)) :=
    fun I hI => hI.1
  have hFi : Integrable F μ.1 := hFmem.integrable one_le_two
  have hgi : Integrable (f₀ : GaugeField a → ℂ) μ.1 := (Lp.memLp f₀).integrable one_le_two
  have hJi := hgi.congr hJg.symm
  have hsets : ∀ I : Set (GaugeField a), MeasurableSet[shiftInvariantSigma a] I →
      ∫ A in I, (f₀ : GaugeField a → ℂ) A * V.indicator (1 : GaugeField a → ℂ) A ∂μ.1 =
        ∫ A in I, F A ∂μ.1 := by
    intro I hI
    have hμI : μ.1 I ≠ ∞ := measure_ne_top _ _
    have hc : (indicatorConstLp 2 hI.1 hμI (1 : ℂ) : GaugeField a → ℂ) =ᵐ[μ.1]
        I.indicator (1 : GaugeField a → ℂ) := indicatorConstLp_coeFn
    have hχ : ∀ k, koopman μ hμ k (indicatorConstLp 2 hI.1 hμI (1 : ℂ)) =
        indicatorConstLp 2 hI.1 hμI (1 : ℂ) := by
      intro k
      refine Lp.ext ?_
      have h1 := koopman_coeFn μ hμ k (indicatorConstLp 2 hI.1 hμI (1 : ℂ))
      have h2 := (measurePreserving_shift μ.1 hμ
        (latticePointOfInt a k)).quasiMeasurePreserving.ae_eq_comp hc
      refine h1.trans (h2.trans (EventuallyEq.trans (EventuallyEq.of_eq ?_) hc.symm))
      exact hI.2 _
    have h0 := hperp _ hχ
    have h1 : ⟪indicatorConstLp 2 hI.1 hμI (1 : ℂ), f⟫_ℂ =
        ⟪(indicatorConstLp 2 hI.1 hμI (1 : ℂ) : StateL2 μ), f₀⟫_ℂ := by
      rw [hsum, inner_add_right, h0, add_zero]
    rw [L2.inner_indicatorConstLp_one, L2.inner_indicatorConstLp_one] at h1
    rw [integral_congr_ae (ae_restrict_of_ae hJg), ← h1]
    exact integral_congr_ae (ae_restrict_of_ae hf)
  have hE : (fun A => (f₀ : GaugeField a → ℂ) A * V.indicator (1 : GaugeField a → ℂ) A)
      =ᵐ[μ.1] condExpShiftInvariant μ.1 F :=
    ae_eq_condExp_of_forall_setIntegral_eq hm hFi (fun s _ _ => hJi.integrableOn)
      (fun s hs _ => hsets s hs) hJ.stronglyMeasurable.aestronglyMeasurable
  have hg : (f₀ : GaugeField a → ℂ) =ᵐ[μ.1] condExpShiftInvariant μ.1 F := hJg.symm.trans hE
  have hnorm : ∀ n, (stateL2Norm μ fun A => cornerCubeAverage n F A - condExpShiftInvariant μ.1 F A) =
      ‖cubeAverage (koopman μ hμ) n f - f₀‖ := by
    intro n
    rw [norm_stateL2]
    refine stateL2Norm_congr μ ?_
    filter_upwards [Lp.coeFn_sub (cubeAverage (koopman μ hμ) n f) f₀,
      cubeAverage_ae_eq ha μ hμ hf n, hg] with A h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
  simp only [hnorm]
  exact tendsto_iff_norm_sub_tendsto_zero.mp hlim
end Main
end BoxAverages
theorem meanErgodicStatement_holds
    (hInvariant : ShiftInvariance.ShiftInvarianceAndErgodicity) :
    MeanErgodicStatement := by
  intro L K hodd h13 hK μ hμ F hF
  obtain ⟨⟨-, hcomp⟩, -, -, hb, -⟩ := hInvariant L K hodd h13 hK
  exact BoxAverages.tendsto_stateL2Norm
    (ShiftInvariance.meshSize_pos (by omega) K).ne' hcomp hb μ hμ F hF
end YangMills.Construction.InfiniteLattice
