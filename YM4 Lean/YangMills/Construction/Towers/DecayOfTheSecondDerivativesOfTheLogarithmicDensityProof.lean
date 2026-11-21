import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import YangMills.Construction.Torus.PointsAndTuplesOfTorusOrFourSpace
import YangMills.Construction.Towers.DecayOfTheSecondDerivativesOfTheLogarithmicDensity
import YangMills.Construction.Towers.SecondDerivativesOfTheLogarithmicDensity
import YangMills.Construction.Towers.VariationsOfALocalFamily
import Mathlib
set_option autoImplicit false
open Filter Topology
noncomputable section
namespace YangMills.Construction.Tower.LocalFamilies
open OperatorCalculus Tower.UnitLatticeL2 Tower.AbelianFieldDensity
open Tower.ResolventDecay OneLoopNotation
namespace HessianDecay
variable {J : Type}
theorem euclidNormVec_nonneg (v : Fin 4 → ℝ) : 0 ≤ TorusMetric.euclidNormVec v := Real.sqrt_nonneg _
theorem euclidNormVec_sub_comm (x y : Fin 4 → ℝ) :
    TorusMetric.euclidNormVec (x - y) = TorusMetric.euclidNormVec (y - x) := by apply _root_.YangMills.Construction.AmbientPoints.euclidNormVec_sub_comm <;> assumption
theorem euclidNormVec_sub_le (x y u : Fin 4 → ℝ) :
    TorusMetric.euclidNormVec (x - u) ≤
      TorusMetric.euclidNormVec (x - y) + TorusMetric.euclidNormVec (y - u) := by apply _root_.YangMills.Construction.AmbientPoints.euclidNormVec_sub_le <;> assumption
theorem abs_apply_le_euclidNormVec (v : Fin 4 → ℝ) (μ : Fin 4) :
    |v μ| ≤ TorusMetric.euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
theorem finite_and_ncard_near {pos : J → InfiniteLattice.AmbientSpace} {m : ℕ}
    (h : IsIntegerPlacement pos m) (y : Fin 4 → ℤ) :
    {i | TorusMetric.euclidNormVec (PeriodicOperators.castVec y - pos i) ≤ 2}.Finite ∧
      {i | TorusMetric.euclidNormVec (PeriodicOperators.castVec y - pos i) ≤ 2}.ncard ≤
        m * 5 ^ 4 := by
  classical
  let D : Finset (Fin 4 → ℤ) := Fintype.piFinset fun μ => Finset.Icc (y μ - 2) (y μ + 2)
  have hD : D.card = 5 ^ 4 := by
    have h5 : ∀ μ : Fin 4, (y μ + 2 + 1 - (y μ - 2)).toNat = 5 := fun μ => by omega
    simp [D, Fintype.card_piFinset, h5]
  let F : (Fin 4 → ℤ) → Finset J :=
    fun d => (h.fibre_bounded (PeriodicOperators.castVec d)).1.toFinset
  have hsub : {i | TorusMetric.euclidNormVec (PeriodicOperators.castVec y - pos i) ≤ 2} ⊆
      ((D.biUnion F : Finset J) : Set J) := by
    intro i hi
    obtain ⟨k, hk⟩ := h.on_lattice i
    have hmem : k ∈ D := by
      refine Fintype.mem_piFinset.2 fun μ => ?_
      have h1 := (abs_apply_le_euclidNormVec _ μ).trans hi
      rw [hk] at h1
      have h2 : |((y μ - k μ : ℤ) : ℝ)| ≤ 2 := by
        simpa [PeriodicOperators.castVec] using h1
      have h3 : |y μ - k μ| ≤ 2 := by exact_mod_cast h2
      have h4 := abs_le.1 h3
      exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
    refine Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨k, hmem, ?_⟩)
    simp [F, hk]
  refine ⟨(Finset.finite_toSet _).subset hsub, ?_⟩
  calc _ ≤ ((D.biUnion F : Finset J) : Set J).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (D.biUnion F).card := Set.ncard_coe_finset _
    _ ≤ D.card * m := by
        refine Finset.card_biUnion_le_card_mul _ _ _ fun d _ => ?_
        have := (h.fibre_bounded (PeriodicOperators.castVec d)).2
        rwa [Set.ncard_eq_toFinset_card _ (h.fibre_bounded (PeriodicOperators.castVec d)).1] at this
    _ = m * 5 ^ 4 := by rw [hD, Nat.mul_comm]
theorem matrixEntry_comp (hE : MatrixEntryProperties J) (A B : BddOp (IndexL2 J))
    (i' i : J) : matrixEntry (A.comp B) i' i = ∑' k, matrixEntry A i' k * matrixEntry B k i :=
  ((hE A).2 (B (basisVec i)) i').2
theorem norm_matrixEntry_comp_le (hE : MatrixEntryProperties J)
    (A B : BddOp (IndexL2 J)) (i' i : J) {S : Set J} (hS : S.Finite) {n : ℕ}
    (hcard : S.ncard ≤ n) {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ k, matrixEntry A i' k * matrixEntry B k i ≠ 0 →
      k ∈ S ∧ ‖matrixEntry A i' k * matrixEntry B k i‖ ≤ a) :
    ‖matrixEntry (A.comp B) i' i‖ ≤ n * a := by
  classical
  rw [matrixEntry_comp hE, tsum_eq_sum (s := hS.toFinset) (fun k hk => by
    by_contra hne
    exact hk (hS.mem_toFinset.2 (h k hne).1))]
  calc _ ≤ ∑ k ∈ hS.toFinset, ‖matrixEntry A i' k * matrixEntry B k i‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ hS.toFinset, a := by
        refine Finset.sum_le_sum fun k _ => ?_
        by_cases hz : matrixEntry A i' k * matrixEntry B k i = 0
        · rw [hz, norm_zero]; exact ha
        · exact (h k hz).2
    _ = hS.toFinset.card * a := by simp
    _ ≤ n * a := by
        refine mul_le_mul_of_nonneg_right ?_ ha
        rw [← Set.ncard_eq_toFinset_card _ hS]
        exact_mod_cast hcard
structure SupportedNear (pos : J → InfiniteLattice.AmbientSpace) (C : ℝ)
    (t : InfiniteLattice.AmbientSpace) (V : BddOp (IndexL2 J)) : Prop where
  entry_le : ∀ k k', ‖matrixEntry V k k'‖ ≤ C
  range_le_two : ∀ k k', ¬ TorusMetric.euclidNormVec (pos k - pos k') ≤ 2 →
    matrixEntry V k k' = 0
  near_pt : ∀ k k', ¬ TorusMetric.euclidNormVec (t - pos k) ≤ 2 → matrixEntry V k k' = 0
theorem norm_matrixEntry_sandwich_le {pos : J → InfiniteLattice.AmbientSpace} {m : ℕ}
    (hL : IsIntegerPlacement pos m) (hE : MatrixEntryProperties J)
    (X V Y : BddOp (IndexL2 J)) (i' i : J) (y : Fin 4 → ℤ) {C α β : ℝ}
    (hC : 0 ≤ C) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hV : SupportedNear pos C (PeriodicOperators.castVec y) V)
    (hXY : ∀ k k', matrixEntry V k k' ≠ 0 → ‖matrixEntry X i' k‖ ≤ α ∧ ‖matrixEntry Y k' i‖ ≤ β) :
    ‖matrixEntry (X.comp (V.comp Y)) i' i‖ ≤
      ((m * 5 ^ 4 : ℕ) : ℝ) * (α * (((m * 5 ^ 4 : ℕ) : ℝ) * (C * β))) := by
  refine norm_matrixEntry_comp_le hE X (V.comp Y) i' i (finite_and_ncard_near hL y).1
    (finite_and_ncard_near hL y).2 (by positivity) fun k hk => ?_
  have hVY : matrixEntry (V.comp Y) k i ≠ 0 := right_ne_zero_of_mul hk
  obtain ⟨k', hk'⟩ : ∃ k', matrixEntry V k k' ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hVY (by rw [matrixEntry_comp hE]; simp [hall])
  refine ⟨?_, ?_⟩
  · by_contra hout
    exact hk' (hV.near_pt k k' hout)
  · obtain ⟨p, hp⟩ := hL.on_lattice k
    have hin : ‖matrixEntry (V.comp Y) k i‖ ≤ ((m * 5 ^ 4 : ℕ) : ℝ) * (C * β) := by
      refine norm_matrixEntry_comp_le hE V Y k i (finite_and_ncard_near hL p).1
        (finite_and_ncard_near hL p).2 (by positivity) fun k₁ hk₁ => ?_
      have hV₁ : matrixEntry V k k₁ ≠ 0 := left_ne_zero_of_mul hk₁
      refine ⟨?_, ?_⟩
      · by_contra hout
        refine hV₁ (hV.range_le_two k k₁ fun hle => hout ?_)
        show TorusMetric.euclidNormVec (PeriodicOperators.castVec p - pos k₁) ≤ 2
        rw [← hp]
        exact hle
      · rw [norm_mul]
        exact mul_le_mul (hV.entry_le k k₁) (hXY k k₁ hV₁).2 (norm_nonneg _) hC
    rw [norm_mul]
    exact mul_le_mul (hXY k k' hk').1 hin (norm_nonneg _) hα
theorem exp_neg_mul_le_shift {c d D s : ℝ} (hc : 0 ≤ c) (h : D ≤ d + s) :
    Real.exp (-(c * d)) ≤ Real.exp (-(c * (D - s))) := by
  refine Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left ?_ hc))
  linarith
theorem matrixEntry_sub (A B : BddOp (IndexL2 J)) (i' i : J) :
    matrixEntry (A - B) i' i = matrixEntry A i' i - matrixEntry B i' i := by
  simp [matrixEntry]
theorem norm_matrixEntry_inner_le {pos : J → InfiniteLattice.AmbientSpace} {m : ℕ}
    (hL : IsIntegerPlacement pos m) (hE : MatrixEntryProperties J)
    (R V : BddOp (IndexL2 J)) (y : Fin 4 → ℤ) {C A c : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hc : 0 ≤ c)
    (hR : ∀ k k', ‖matrixEntry R k k'‖ ≤
      A * Real.exp (-(c * TorusMetric.euclidNormVec (pos k - pos k'))))
    (hV : SupportedNear pos C (PeriodicOperators.castVec y) V) (i₀ i : J) :
    ‖matrixEntry (R.comp (V.comp R)) i₀ i‖ ≤ ((m * 5 ^ 4 : ℕ) : ℝ) * (A * (((m * 5 ^ 4 : ℕ) : ℝ) *
      (C * (A * Real.exp (-(c * (TorusMetric.euclidNormVec (pos i - PeriodicOperators.castVec y) -
        4))))))) := by
  refine norm_matrixEntry_sandwich_le hL hE R V R i₀ i y hC hA (by positivity) hV
    fun k k' hne => ?_
  have h2 : TorusMetric.euclidNormVec (pos k - pos k') ≤ 2 := by
    by_contra hout
    exact hne (hV.range_le_two k k' hout)
  have h3 : TorusMetric.euclidNormVec (PeriodicOperators.castVec y - pos k) ≤ 2 := by
    by_contra hout
    exact hne (hV.near_pt k k' hout)
  refine ⟨(hR i₀ k).trans (mul_le_of_le_one_right hA (Real.exp_le_one_iff.2 ?_)),
    (hR k' i).trans (mul_le_mul_of_nonneg_left (exp_neg_mul_le_shift hc ?_) hA)⟩
  · have := mul_nonneg hc (euclidNormVec_nonneg (pos i₀ - pos k))
    linarith
  · have t1 := euclidNormVec_sub_le (pos i) (pos k') (PeriodicOperators.castVec y)
    have t2 := euclidNormVec_sub_le (pos k') (pos k) (PeriodicOperators.castVec y)
    have c1 := euclidNormVec_sub_comm (pos i) (pos k')
    have c2 := euclidNormVec_sub_comm (pos k) (pos k')
    have c3 := euclidNormVec_sub_comm (pos k) (PeriodicOperators.castVec y)
    linarith
theorem norm_diag_single_le {pos : J → InfiniteLattice.AmbientSpace} {m : ℕ}
    (hL : IsIntegerPlacement pos m) (hE : MatrixEntryProperties J)
    (R V : BddOp (IndexL2 J)) (y y' : Fin 4 → ℤ) {C A c : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hc : 0 ≤ c)
    (hR : ∀ k k', ‖matrixEntry R k k'‖ ≤
      A * Real.exp (-(c * TorusMetric.euclidNormVec (pos k - pos k'))))
    (hV : SupportedNear pos C (PeriodicOperators.castVec y) V)
    (hV' : ∀ k k', ¬ TorusMetric.euclidNormVec (PeriodicOperators.castVec y' - pos k) ≤ 2 →
      matrixEntry V k k' = 0) (i : J) :
    ‖matrixEntry (R.comp (V.comp R)) i i‖ ≤ ((m * 5 ^ 4 : ℕ) : ℝ) *
      ((A * Real.exp (-(c * (TorusMetric.euclidNormVec (pos i - PeriodicOperators.castVec y) -
        2)))) * (((m * 5 ^ 4 : ℕ) : ℝ) * (C * (A * Real.exp
          (-(c * (TorusMetric.euclidNormVec (pos i - PeriodicOperators.castVec y') -
            4))))))) := by
  refine norm_matrixEntry_sandwich_le hL hE R V R i i y hC (by positivity) (by positivity) hV
    fun k k' hne => ?_
  have h2 : TorusMetric.euclidNormVec (pos k - pos k') ≤ 2 := by
    by_contra hout
    exact hne (hV.range_le_two k k' hout)
  have h3 : TorusMetric.euclidNormVec (PeriodicOperators.castVec y - pos k) ≤ 2 := by
    by_contra hout
    exact hne (hV.near_pt k k' hout)
  have h4 : TorusMetric.euclidNormVec (PeriodicOperators.castVec y' - pos k) ≤ 2 := by
    by_contra hout
    exact hne (hV' k k' hout)
  refine ⟨(hR i k).trans (mul_le_mul_of_nonneg_left (exp_neg_mul_le_shift hc ?_) hA),
    (hR k' i).trans (mul_le_mul_of_nonneg_left (exp_neg_mul_le_shift hc ?_) hA)⟩
  · have t1 := euclidNormVec_sub_le (pos i) (pos k) (PeriodicOperators.castVec y)
    rw [euclidNormVec_sub_comm (pos k)] at t1
    linarith
  · have t1 := euclidNormVec_sub_le (pos i) (pos k') (PeriodicOperators.castVec y')
    have t2 := euclidNormVec_sub_le (pos k') (pos k) (PeriodicOperators.castVec y')
    have c1 := euclidNormVec_sub_comm (pos i) (pos k')
    have c2 := euclidNormVec_sub_comm (pos k) (pos k')
    have c3 := euclidNormVec_sub_comm (pos k) (PeriodicOperators.castVec y')
    linarith
theorem norm_diag_double_le {pos : J → InfiniteLattice.AmbientSpace} {m : ℕ}
    (hL : IsIntegerPlacement pos m) (hE : MatrixEntryProperties J)
    (R V V' : BddOp (IndexL2 J)) (y y' : Fin 4 → ℤ) {C A c : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hc : 0 ≤ c)
    (hR : ∀ k k', ‖matrixEntry R k k'‖ ≤
      A * Real.exp (-(c * TorusMetric.euclidNormVec (pos k - pos k'))))
    (hV : SupportedNear pos C (PeriodicOperators.castVec y) V)
    (hV' : SupportedNear pos C (PeriodicOperators.castVec y') V') (i : J) :
    ‖matrixEntry (R.comp (V.comp (R.comp (V'.comp R)))) i i‖ ≤ ((m * 5 ^ 4 : ℕ) : ℝ) *
      ((A * Real.exp (-(c * (TorusMetric.euclidNormVec (pos i - PeriodicOperators.castVec y) -
        2)))) * (((m * 5 ^ 4 : ℕ) : ℝ) * (C * (((m * 5 ^ 4 : ℕ) : ℝ) * (A *
          (((m * 5 ^ 4 : ℕ) : ℝ) * (C * (A * Real.exp (-(c *
            (TorusMetric.euclidNormVec (pos i - PeriodicOperators.castVec y') -
              4))))))))))) := by
  refine norm_matrixEntry_sandwich_le hL hE R V (R.comp (V'.comp R)) i i y hC (by positivity)
    (by positivity) hV fun k k' hne => ?_
  have h3 : TorusMetric.euclidNormVec (PeriodicOperators.castVec y - pos k) ≤ 2 := by
    by_contra hout
    exact hne (hV.near_pt k k' hout)
  refine ⟨(hR i k).trans (mul_le_mul_of_nonneg_left (exp_neg_mul_le_shift hc ?_) hA),
    norm_matrixEntry_inner_le hL hE R V' y' hC hA hc hR hV' k' i⟩
  have t1 := euclidNormVec_sub_le (pos i) (pos k) (PeriodicOperators.castVec y)
  rw [euclidNormVec_sub_comm (pos k)] at t1
  linarith
theorem norm_traceAt_le {pos : J → InfiniteLattice.AmbientSpace} {m : ℕ}
    (S : BddOp (IndexL2 J)) {x : InfiniteLattice.AmbientSpace}
    (hfib : {i | pos i = x}.Finite ∧ {i | pos i = x}.ncard ≤ m) {G : ℝ} (hG : 0 ≤ G)
    (h : ∀ i, pos i = x → ‖matrixEntry S i i‖ ≤ G) :
    ‖traceAt pos S x‖ ≤ m * G := by
  classical
  unfold traceAt
  rw [finsum_mem_eq_finite_toFinset_sum _ hfib.1]
  calc _ ≤ ∑ i ∈ hfib.1.toFinset, ‖matrixEntry S i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ hfib.1.toFinset, G :=
        Finset.sum_le_sum fun i hi => h i (hfib.1.mem_toFinset.1 hi)
    _ = hfib.1.toFinset.card * G := by simp
    _ ≤ m * G := by
        refine mul_le_mul_of_nonneg_right ?_ hG
        rw [← Set.ncard_eq_toFinset_card _ hfib.1]
        exact_mod_cast hfib.2
theorem integral_inv_sq_Ioi {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun w : ℝ => ((z / 4 + w)⁻¹) ^ 2) (Set.Ioi 0) ∧
      ∫ w in Set.Ioi (0 : ℝ), ((z / 4 + w)⁻¹) ^ 2 = 4 / z := by
  have hd : ∀ w ∈ Set.Ici (0 : ℝ),
      HasDerivAt (fun w : ℝ => -(z / 4 + w)⁻¹) (((z / 4 + w)⁻¹) ^ 2) w := by
    intro w hw
    have hpos : 0 < z / 4 + w := by
      have := Set.mem_Ici.1 hw
      linarith
    have h1 : HasDerivAt (fun w : ℝ => z / 4 + w) 1 w := by
      simpa using (hasDerivAt_id w).const_add (z / 4)
    have h2 := (h1.fun_inv hpos.ne').fun_neg
    have e : -(-1 / (z / 4 + w) ^ 2) = ((z / 4 + w)⁻¹) ^ 2 := by
      rw [inv_pow, neg_div, neg_neg, one_div]
    rw [e] at h2
    exact h2
  have hp : ∀ w ∈ Set.Ioi (0 : ℝ), 0 ≤ ((z / 4 + w)⁻¹) ^ 2 := fun _ _ => sq_nonneg _
  have ht : Tendsto (fun w : ℝ => -(z / 4 + w)⁻¹) atTop (𝓝 0) := by
    have h1 : Tendsto (fun w : ℝ => z / 4 + w) atTop atTop :=
      tendsto_atTop_add_const_left atTop (z / 4) tendsto_id
    simpa using (tendsto_inv_atTop_zero.comp h1).neg
  refine ⟨MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' hd hp ht, ?_⟩
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' hd hp ht]
  simp
end HessianDecay
open HessianDecay in
theorem logDensityHessianDecay_holds
    (hH : LogTraceSecondDerivative.IntegralFormula)
    (hV : LocalFamilyVariations) :
    LogDensityHessianDecay := by
  intro z C m m' hz hC
  have hc : 0 ≤ resolventDecayRate z C := by
    unfold resolventDecayRate
    have h1 : 0 < z / (4 * 12 * 5 ^ 4 * C) := by positivity
    have h2 : 0 ≤ Real.log (1 + z / (4 * 12 * 5 ^ 4 * C)) := Real.log_nonneg (by linarith)
    positivity
  obtain ⟨Nr, hNr⟩ : ∃ Nr : ℝ, Nr = ((m * 5 ^ 4 : ℕ) : ℝ) := ⟨_, rfl⟩
  refine ⟨(m : ℝ) * ((Nr ^ 2 * C + 2 * (Nr ^ 4 * C ^ 2) * (4 / z)) *
    Real.exp (6 * resolventDecayRate z C)) * (4 / z), ?_⟩
  intro J B pos src T hs n b b'
  have hE := hs.space.entryFacts
  have hL := hs.space.placement
  obtain ⟨y, hy⟩ := hs.edges.on_lattice b
  obtain ⟨y', hy'⟩ := hs.edges.on_lattice b'
  obtain ⟨-, hb1, hr1, hn1, hn2, -, -⟩ := hV J B pos src m m' z C T hz hC hs b b'
  obtain ⟨-, hb1', hr1', hn1', -, -, -⟩ := hV J B pos src m m' z C T hz hC hs b' b
  have hSb : SupportedNear pos C (PeriodicOperators.castVec y) (firstVar T b) :=
    ⟨fun k k' => (hb1 k k').1, fun k k' h => (hr1 k k' h).1,
      fun k k' h => (hn1 k k' (by rw [hy]; exact h)).1⟩
  have hSb' : SupportedNear pos C (PeriodicOperators.castVec y') (firstVar T b') :=
    ⟨fun k k' => (hb1' k k').1, fun k k' h => (hr1' k k' h).1,
      fun k k' h => (hn1' k k' (by rw [hy']; exact h)).1⟩
  have hSbb : SupportedNear pos C (PeriodicOperators.castVec y) (secondVar T b b') :=
    ⟨fun k k' => (hb1 k k').2, fun k k' h => (hr1 k k' h).2,
      fun k k' h => (hn1 k k' (by rw [hy]; exact h)).2⟩
  have hnb' : ∀ k k', ¬ TorusMetric.euclidNormVec
      (PeriodicOperators.castVec y' - pos k) ≤ 2 →
      matrixEntry (secondVar T b b') k k' = 0 :=
    fun k k' h => hn2 k k' (by rw [hy']; exact h)
  have hlow : UnitLatticeL2.IsBoundedBelowBy (addScalar (T fun _ => 0) z) (z / 2) := by
    obtain ⟨r, hr, hsm⟩ := hs.lower_bound
    exact hsm _ fun _ => by simpa using hr.le
  have hent : ∀ i' i, ‖matrixEntry (T fun _ => 0) i' i‖ ≤ C := by
    intro i' i
    obtain ⟨E, P, -, -, hP, heq⟩ := hs.family.entry_smooth i' i
    rw [heq]
    simpa using hP 0 (by norm_num) fun b => (0 : ℝ)
  have hR : ∀ w : ℝ, 0 ≤ w → ∀ k k', ‖matrixEntry (baseResolvent T z w) k k'‖ ≤
      (z / 4 + w)⁻¹ * Real.exp (-(resolventDecayRate z C *
        TorusMetric.euclidNormVec (pos k - pos k'))) :=
    fun w hw k k' => hs.space.resolventDecay (T fun _ => 0) (hs.family.selfAdjoint _) hlow hent
      (hs.family.finite_range _) w hw k k'
  obtain ⟨D₁, hD₁⟩ : ∃ D₁ : ℝ, D₁ = TorusMetric.euclidNormVec
    (PeriodicOperators.castVec n - PeriodicOperators.castVec y) := ⟨_, rfl⟩
  obtain ⟨D₂, hD₂⟩ : ∃ D₂ : ℝ, D₂ = TorusMetric.euclidNormVec
    (PeriodicOperators.castVec n - PeriodicOperators.castVec y') := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = Real.exp (6 * resolventDecayRate z C) *
    Real.exp (-(resolventDecayRate z C * (D₁ + D₂))) := ⟨_, rfl⟩
  have hQ0 : 0 ≤ Q := hQ ▸ by positivity
  have hpt : ∀ w ∈ Set.Ioi (0 : ℝ),
      ‖traceAt pos (secondOrderResolvent T z b b' w) (PeriodicOperators.castVec n)‖ ≤
        ((m : ℝ) * ((Nr ^ 2 * C + 2 * (Nr ^ 4 * C ^ 2) * (4 / z)) * Q)) *
          ((z / 4 + w)⁻¹) ^ 2 := by
    intro w hw
    have hw0 : 0 ≤ w := (Set.mem_Ioi.1 hw).le
    obtain ⟨A, hAeq⟩ : ∃ A : ℝ, A = (z / 4 + w)⁻¹ := ⟨_, rfl⟩
    have hA : 0 ≤ A := by rw [hAeq]; positivity
    have hA4 : A ≤ 4 / z := by
      have h4 : (4 : ℝ) / z = (z / 4)⁻¹ := (inv_div z 4).symm
      rw [hAeq, h4]
      exact inv_anti₀ (by positivity) (by linarith)
    have hRw : ∀ k k', ‖matrixEntry (baseResolvent T z w) k k'‖ ≤
        A * Real.exp (-(resolventDecayRate z C *
          TorusMetric.euclidNormVec (pos k - pos k'))) := by
      rw [hAeq]
      exact hR w hw0
    rw [← hAeq, mul_assoc]
    refine norm_traceAt_le _ (hL.fibre_bounded _) (by positivity) fun i hi => ?_
    have t1 := norm_diag_single_le hL hE _ _ y y' hC.le hA hc hRw hSbb hnb' i
    have t2 := norm_diag_double_le hL hE _ _ _ y y' hC.le hA hc hRw hSb hSb' i
    have t3 := norm_diag_double_le hL hE _ _ _ y' y hC.le hA hc hRw hSb' hSb i
    rw [hi, ← hD₁, ← hD₂, ← hNr] at t1 t2
    rw [hi, ← hD₁, ← hD₂, ← hNr] at t3
    have e1 : Real.exp (-(resolventDecayRate z C * (D₁ - 2))) *
        Real.exp (-(resolventDecayRate z C * (D₂ - 4))) = Q := by
      rw [hQ, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    have e2 : Real.exp (-(resolventDecayRate z C * (D₂ - 2))) *
        Real.exp (-(resolventDecayRate z C * (D₁ - 4))) = Q := by
      rw [hQ, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    have hsplit : matrixEntry (secondOrderResolvent T z b b' w) i i =
        matrixEntry ((baseResolvent T z w).comp ((secondVar T b b').comp
          (baseResolvent T z w))) i i -
        matrixEntry ((baseResolvent T z w).comp ((firstVar T b).comp ((baseResolvent T z w).comp
          ((firstVar T b').comp (baseResolvent T z w))))) i i -
        matrixEntry ((baseResolvent T z w).comp ((firstVar T b').comp ((baseResolvent T z w).comp
          ((firstVar T b).comp (baseResolvent T z w))))) i i := by
      unfold secondOrderResolvent
      rw [matrixEntry_sub, matrixEntry_sub]
    rw [hsplit]
    have u1 : Nr * (A * Real.exp (-(resolventDecayRate z C * (D₁ - 2))) * (Nr * (C * (A *
        Real.exp (-(resolventDecayRate z C * (D₂ - 4))))))) = Nr ^ 2 * C * A ^ 2 * Q := by
      rw [← e1]; ring
    have u2 : Nr * (A * Real.exp (-(resolventDecayRate z C * (D₁ - 2))) * (Nr * (C * (Nr *
        (A * (Nr * (C * (A * Real.exp (-(resolventDecayRate z C * (D₂ - 4))))))))))) =
        Nr ^ 4 * C ^ 2 * A ^ 3 * Q := by
      rw [← e1]; ring
    have u3 : Nr * (A * Real.exp (-(resolventDecayRate z C * (D₂ - 2))) * (Nr * (C * (Nr *
        (A * (Nr * (C * (A * Real.exp (-(resolventDecayRate z C * (D₁ - 4))))))))))) =
        Nr ^ 4 * C ^ 2 * A ^ 3 * Q := by
      rw [← e2]; ring
    rw [u1] at t1
    rw [u2] at t2
    rw [u3] at t3
    have hA3 : Nr ^ 4 * C ^ 2 * A ^ 3 * Q ≤ Nr ^ 4 * C ^ 2 * (A ^ 2 * (4 / z)) * Q := by
      have : A ^ 3 ≤ A ^ 2 * (4 / z) := by
        rw [pow_succ]
        exact mul_le_mul_of_nonneg_left hA4 (by positivity)
      have hNC : 0 ≤ Nr ^ 4 * C ^ 2 := by positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hNC) hQ0
    calc _ ≤ _ := norm_sub_le _ _
      _ ≤ ‖_‖ + ‖_‖ + ‖_‖ := add_le_add_left (norm_sub_le _ _) _
      _ ≤ Nr ^ 2 * C * A ^ 2 * Q + Nr ^ 4 * C ^ 2 * A ^ 3 * Q + Nr ^ 4 * C ^ 2 * A ^ 3 * Q :=
          add_le_add (add_le_add t1 t2) t3
      _ ≤ _ := by
          have : (Nr ^ 2 * C + 2 * (Nr ^ 4 * C ^ 2) * (4 / z)) * Q * A ^ 2 =
              Nr ^ 2 * C * A ^ 2 * Q + Nr ^ 4 * C ^ 2 * (A ^ 2 * (4 / z)) * Q +
                Nr ^ 4 * C ^ 2 * (A ^ 2 * (4 / z)) * Q := by ring
          rw [this]
          linarith
  obtain ⟨hint, hval⟩ := integral_inv_sq_Ioi hz
  rw [(hH J B pos src m m' z C T hz hC hs n b b').2.2, hy, hy', ← hD₁, ← hD₂]
  calc _ ≤ ∫ w in Set.Ioi (0 : ℝ), ((m : ℝ) * ((Nr ^ 2 * C + 2 * (Nr ^ 4 * C ^ 2) * (4 / z)) *
          Q)) * ((z / 4 + w)⁻¹) ^ 2 :=
        MeasureTheory.norm_integral_le_of_norm_le (hint.const_mul _)
          ((MeasureTheory.ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall hpt))
    _ = ((m : ℝ) * ((Nr ^ 2 * C + 2 * (Nr ^ 4 * C ^ 2) * (4 / z)) * Q)) * (4 / z) := by
        rw [MeasureTheory.integral_const_mul, hval]
    _ = _ := by rw [hQ]; ring
end YangMills.Construction.Tower.LocalFamilies
end
