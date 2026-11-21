import YangMills.Construction.Towers.HolomorphicSymbolsAndTheCalculusAtFluxZeroProof
import Mathlib
set_option autoImplicit false
open Filter YangMills.Construction.OneLoopNotation YangMills.Construction.Tower.UnitLatticeL2 YangMills.Construction.Tower.UnitaryCombinations
noncomputable section
namespace YangMills.Construction.Tower.UnitarySeriesBounds
variable {L p q : ℕ}
theorem lp_hasSum_norm_sq {ι E : Type} [NormedAddCommGroup E] (u : lp (fun _ : ι => E) 2) :
    HasSum (fun x => ‖u x‖ ^ 2) (‖u‖ ^ 2) := by
  have hu := lp.hasSum_norm (p := 2) (by norm_num) u
  simpa using hu
theorem norm_coord_apply (w : VectorL2 L q) (i : Fin q)
    (x : FullSpace.Vertex L 0 0) : ‖coord w i x‖ = ‖w x i‖ := by
  change ‖(EuclideanSpace.single 0 (w x i) : EuclideanSpace ℂ (Fin 1))‖ = _
  simp
theorem sum_norm_sq_coord (w : VectorL2 L q) :
    ∑ i, ‖coord w i‖ ^ 2 = ‖w‖ ^ 2 := by
  have hs : HasSum (fun x => ∑ i, ‖coord w i x‖ ^ 2) (∑ i, ‖coord w i‖ ^ 2) :=
    hasSum_sum fun i _ => lp_hasSum_norm_sq (coord w i)
  have hf : (fun x => ∑ i, ‖coord w i x‖ ^ 2) = fun x => ‖w x‖ ^ 2 := by
    funext x
    rw [EuclideanSpace.norm_sq_eq]
    exact Finset.sum_congr rfl fun i _ => by rw [norm_coord_apply]
  rw [hf] at hs
  exact hs.unique (lp_hasSum_norm_sq w)
theorem hasSum_norm_sq_applyCoordwise {U : ScalarL2 L →ₗ[ℂ] ScalarL2 L}
    (hU : IsUnitaryOp U) (w : VectorL2 L q) :
    HasSum (fun x => ‖applyCoordwise U w x‖ ^ 2) (‖w‖ ^ 2) := by
  have hs : HasSum (fun x => ∑ i, ‖U (coord w i) x‖ ^ 2) (∑ i, ‖U (coord w i)‖ ^ 2) :=
    hasSum_sum fun i _ => lp_hasSum_norm_sq (U (coord w i))
  have hf : (fun x => ∑ i, ‖U (coord w i) x‖ ^ 2) = fun x => ‖applyCoordwise U w x‖ ^ 2 := by
    funext x
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [EuclideanSpace.norm_sq_eq]
    simp [applyCoordwise]
  have hn : ∑ i, ‖U (coord w i)‖ ^ 2 = ‖w‖ ^ 2 := by
    rw [← sum_norm_sq_coord w]
    exact Finset.sum_congr rfl fun i _ => by rw [hU.2]
  rw [hf, hn] at hs
  exact hs
theorem opNormValue_nonneg [NeZero p] [NeZero q] (A : Matrix (Fin p) (Fin q) ℂ) :
    0 ≤ Matrices.RectangularMatrix.opNormValue A := by apply _root_.YangMills.Construction.Tower.MagneticWeyl.FluxZeroCalculus.opNormValue_nonneg <;> assumption
theorem norm_toEuclideanLin_le_opNormValue [NeZero p] [NeZero q] (A : Matrix (Fin p) (Fin q) ℂ)
    (y : EuclideanSpace ℂ (Fin q)) :
    ‖Matrix.toEuclideanLin A y‖ ≤ Matrices.RectangularMatrix.opNormValue A * ‖y‖ :=
  (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)).le_opNorm y
theorem summable_norm_sq_matMulUnitary [NeZero p] [NeZero q]
    (A : Matrix (Fin p) (Fin q) ℂ) {U : ScalarL2 L →ₗ[ℂ] ScalarL2 L}
    (hU : IsUnitaryOp U) (w : VectorL2 L q) :
    Summable (fun x => ‖matMulUnitary A U w x‖ ^ 2) := by
  have hs := (hasSum_norm_sq_applyCoordwise hU w).summable.mul_left
    (Matrices.RectangularMatrix.opNormValue A ^ 2)
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun x => ?_) hs
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_toEuclideanLin_le_opNormValue A _) 2
theorem norm_le_of_eq_matMulUnitary [NeZero p] [NeZero q] (A : Matrix (Fin p) (Fin q) ℂ)
    {U : ScalarL2 L →ₗ[ℂ] ScalarL2 L} (hU : IsUnitaryOp U)
    (w : VectorL2 L q) (v : VectorL2 L p)
    (hv : ∀ x, v x = matMulUnitary A U w x) :
    ‖v‖ ≤ Matrices.RectangularMatrix.opNormValue A * ‖w‖ := by
  have ha := lp_hasSum_norm_sq v
  have hb := (hasSum_norm_sq_applyCoordwise hU w).mul_left
    (Matrices.RectangularMatrix.opNormValue A ^ 2)
  have hc : ‖v‖ ^ 2 ≤ Matrices.RectangularMatrix.opNormValue A ^ 2 * ‖w‖ ^ 2 := by
    refine hasSum_le (fun x => ?_) ha hb
    rw [hv x, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_toEuclideanLin_le_opNormValue A _) 2
  rw [← mul_pow] at hc
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (opNormValue_nonneg A) (norm_nonneg _))).1 hc
theorem coord_add (w w' : VectorL2 L q) (i : Fin q) :
    coord (w + w') i = coord w i + coord w' i := by
  ext x j
  fin_cases j
  change (EuclideanSpace.single 0 ((w + w') x i) : EuclideanSpace ℂ (Fin 1)) 0 =
    (EuclideanSpace.single 0 (w x i) : EuclideanSpace ℂ (Fin 1)) 0 +
      (EuclideanSpace.single 0 (w' x i) : EuclideanSpace ℂ (Fin 1)) 0
  simp
theorem coord_smul (c : ℂ) (w : VectorL2 L q) (i : Fin q) :
    coord (c • w) i = c • coord w i := by
  ext x j
  fin_cases j
  simp [coord]
theorem applyCoordwise_add (U : ScalarL2 L →ₗ[ℂ] ScalarL2 L)
    (w w' : VectorL2 L q) (x : FullSpace.Vertex L 0 0) :
    applyCoordwise U (w + w') x = applyCoordwise U w x + applyCoordwise U w' x := by
  ext i
  simp [applyCoordwise, coord_add]
theorem applyCoordwise_smul (U : ScalarL2 L →ₗ[ℂ] ScalarL2 L) (c : ℂ)
    (w : VectorL2 L q) (x : FullSpace.Vertex L 0 0) :
    applyCoordwise U (c • w) x = c • applyCoordwise U w x := by
  ext i
  simp [applyCoordwise, coord_smul]
theorem exists_bddOp_eq_matMulUnitary [NeZero p] [NeZero q] (A : Matrix (Fin p) (Fin q) ℂ)
    {U : ScalarL2 L →ₗ[ℂ] ScalarL2 L} (hU : IsUnitaryOp U) :
    ∃ T : BddOpBetween (VectorL2 L q) (VectorL2 L p),
      ∀ w x, T w x = matMulUnitary A U w x := by
  have hmem : ∀ w : VectorL2 L q, Memℓp (matMulUnitary A U w) 2 := fun w =>
    memℓp_gen (by simpa using summable_norm_sq_matMulUnitary A hU w)
  let T₀ : VectorL2 L q →ₗ[ℂ] VectorL2 L p :=
    { toFun := fun w => ⟨matMulUnitary A U w, hmem w⟩
      map_add' := fun w w' => by
        ext1
        funext x
        change matMulUnitary A U (w + w') x =
          matMulUnitary A U w x + matMulUnitary A U w' x
        simp [matMulUnitary, applyCoordwise_add]
      map_smul' := fun c w => by
        ext1
        funext x
        change matMulUnitary A U (c • w) x = c • matMulUnitary A U w x
        simp [matMulUnitary, applyCoordwise_smul] }
  exact ⟨T₀.mkContinuous (Matrices.RectangularMatrix.opNormValue A)
    fun w => norm_le_of_eq_matMulUnitary A hU w _ fun _ => rfl, fun _ _ => rfl⟩
theorem matMulUnitaryOp_apply [NeZero p] [NeZero q] (A : Matrix (Fin p) (Fin q) ℂ)
    {U : ScalarL2 L →ₗ[ℂ] ScalarL2 L} (hU : IsUnitaryOp U) :
    ∀ w x, matMulUnitaryOp A U w x = matMulUnitary A U w x :=
  Classical.epsilon_spec (exists_bddOp_eq_matMulUnitary A hU)
theorem norm_matMulUnitaryOp_le [NeZero p] [NeZero q] (A : Matrix (Fin p) (Fin q) ℂ)
    {U : ScalarL2 L →ₗ[ℂ] ScalarL2 L} (hU : IsUnitaryOp U) :
    ‖matMulUnitaryOp A U‖ ≤ Matrices.RectangularMatrix.opNormValue A :=
  ContinuousLinearMap.opNorm_le_bound _ (opNormValue_nonneg A) fun w =>
    norm_le_of_eq_matMulUnitary A hU w _ (matMulUnitaryOp_apply A hU w)
theorem matMulUnitaryBounded (L p q : ℕ) [NeZero p] [NeZero q] : MatMulUnitaryBounded L p q :=
  fun A _ hU => ⟨matMulUnitaryOp_apply A hU, norm_matMulUnitaryOp_le A hU⟩
theorem seriesConvergesUnconditionally (hC : OperatorCalculus.Calculus.Statement)
    (L p q : ℕ) [NeZero p] [NeZero q] : SeriesConvergesUnconditionally L p q := by
  intro c U hc hU
  have hle : ∀ m, ‖matMulUnitaryOp (c m) (U m)‖ ≤ Matrices.RectangularMatrix.opNormValue (c m) :=
    fun m => norm_matMulUnitaryOp_le (c m) (hU m)
  have hsum : Summable fun m => ‖matMulUnitaryOp (c m) (U m)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hc
  obtain ⟨S, -, -, hnorm, hlim⟩ :=
    (hC (VectorL2 L q) (VectorL2 L p)).2.2.1 (Fin 4 → ℤ) _ hsum
  have hspec : TendstoUnconditionally (fun m => matMulUnitaryOp (c m) (U m))
      (tsumOp c U) := Classical.epsilon_spec (p := fun S =>
        TendstoUnconditionally (fun m => matMulUnitaryOp (c m) (U m)) S) ⟨S, hlim⟩
  obtain ⟨σ⟩ := nonempty_equiv_of_countable (α := ℕ+) (β := Fin 4 → ℤ)
  have hS : tsumOp c U = S := tendsto_nhds_unique (hspec σ) (hlim σ)
  refine ⟨hspec, ?_⟩
  rw [hS]
  exact hnorm.trans (Summable.tsum_le_tsum hle hsum hc)
theorem unitaryOperatorSeriesClaim_of_calculus (hC : OperatorCalculus.Calculus.Statement) :
    UnitaryOperatorSeriesClaim := by
  intro L p q _ _
  exact ⟨matMulUnitaryBounded L p q, seriesConvergesUnconditionally hC L p q⟩
end YangMills.Construction.Tower.UnitarySeriesBounds
end
