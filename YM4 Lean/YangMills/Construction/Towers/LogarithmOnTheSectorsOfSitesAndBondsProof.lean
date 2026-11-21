import YangMills.Construction.Towers.LogarithmOfAShiftedOperatorAndIntertwiners
import YangMills.Construction.Towers.LogarithmOnTheSectorsOfSitesAndBonds
import YangMills.Construction.Towers.MultiplesOfTheSectorMatricesAndTheConjugation
import Mathlib
set_option autoImplicit false
open YangMills.Construction.OperatorCalculus YangMills.Construction.OneLoopNotation YangMills.Construction.Tower.UnitLatticeL2
noncomputable section
namespace YangMills.Construction.Tower.AbelianFieldDensity.SectorDecomposition
namespace VertexEdgeLog
section ScaledIsometries
variable {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
theorem addScalar_eval {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : BddOp E) (s : ℝ) (ψ : E) : addScalar T s ψ = T ψ + (s : ℂ) • ψ := by
  simp [addScalar, scalarOp]
theorem opLog_of_scaled_isometry {z c : ℝ}
    (hlog : LogCommIntertwiner H K z) (hc : 0 < c) (M : H → K)
    (hadd : ∀ v v', M (v + v') = M v + M v')
    (hsmul : ∀ (s : ℂ) (v : H), M (s • v) = s • M v)
    (hinner : ∀ v v', inner ℂ (M v) (M v') = (c : ℂ) * inner ℂ v v')
    (T : BddOp K) (S : H → H) (hT : ShiftedHalfPositive z T)
    (hTS : ∀ v, T (M v) = M (S v)) :
    IsBddOpMap S ∧ ShiftedHalfPositive z (toBddOp S) ∧
      ∀ v, opLog (addScalar T z) (M v) =
        M (opLog (addScalar (toBddOp S) z) v) := by
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hnorm : ∀ v, ‖M v‖ ^ 2 = c * ‖v‖ ^ 2 := by
    intro v
    have e : ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (ψ : E),
        inner ℂ ψ ψ = ((‖ψ‖ ^ 2 : ℝ) : ℂ) := by
      intro E _ _ ψ
      rw [inner_self_eq_norm_sq_to_K]
      push_cast
      rfl
    have h := hinner v v
    rw [e, e] at h
    exact Complex.ofReal_injective (by rw [h]; push_cast; ring)
  have hinj : ∀ v v', M v = M v' → v = v' := by
    intro v v' h
    have h0 : M (v - v') = 0 := by
      have e : v - v' = v + (-1 : ℂ) • v' := by simp [sub_eq_add_neg]
      rw [e, hadd, hsmul, h]
      simp
    have h1 := hnorm (v - v')
    rw [h0, norm_zero] at h1
    have h2 : c * ‖v - v'‖ ^ 2 = 0 := by
      rw [← h1]
      simp
    have h3 : ‖v - v'‖ ^ 2 = 0 := (mul_eq_zero.mp h2).resolve_left hc.ne'
    have h4 : ‖v - v'‖ = 0 := by simpa using h3
    exact sub_eq_zero.mp (norm_eq_zero.mp h4)
  have hSadd : ∀ v v', S (v + v') = S v + S v' := fun v v' => hinj _ _ (by
    rw [← hTS, hadd, map_add, hTS, hTS, hadd])
  have hSsmul : ∀ (s : ℂ) (v : H), S (s • v) = s • S v := fun s v => hinj _ _ (by
    rw [← hTS, hsmul, map_smul, hTS, hsmul])
  have hSbound : ∀ v, ‖S v‖ ≤ ‖T‖ * ‖v‖ := by
    intro v
    have h1 : ‖M (S v)‖ ≤ ‖T‖ * ‖M v‖ := by
      rw [← hTS]
      exact T.le_opNorm _
    have h2 : c * ‖S v‖ ^ 2 ≤ c * (‖T‖ * ‖v‖) ^ 2 := by
      rw [← hnorm, mul_pow, mul_left_comm, ← hnorm, ← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 := le_of_mul_le_mul_left h2 hc
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp h3
  let B : BddOp H := LinearMap.mkContinuous
    { toFun := S, map_add' := hSadd, map_smul' := fun s v => by simpa using hSsmul s v }
    ‖T‖ hSbound
  have hbdd : IsBddOpMap S := ⟨B, fun _ => rfl⟩
  have hvals : ∀ ψ, toBddOp S ψ = S ψ := by
    unfold toBddOp
    exact Classical.epsilon_spec hbdd
  have hadj : ContinuousLinearMap.adjoint T = T := hT.1
  have hsym : ∀ x y, inner ℂ (T x) y = inner ℂ x (T y) := by
    intro x y
    have h := ContinuousLinearMap.adjoint_inner_left T y x
    rwa [hadj] at h
  have hself : IsSelfAdjointOp (toBddOp S) := by
    have h : toBddOp S =
        ContinuousLinearMap.adjoint (toBddOp S) := by
      rw [ContinuousLinearMap.eq_adjoint_iff]
      intro x y
      rw [hvals, hvals]
      apply mul_left_cancel₀ hcC
      rw [← hinner, ← hinner, ← hTS, ← hTS, hsym]
    exact h.symm
  have hbelow : IsBoundedBelowBy (addScalar (toBddOp S) z) (z / 2) := by
    intro ψ
    have e : inner ℂ (M ψ) (addScalar T z (M ψ)) - ((z / 2 : ℝ) : ℂ) * inner ℂ (M ψ) (M ψ) =
        (c : ℂ) * (inner ℂ ψ (addScalar (toBddOp S) z ψ) -
          ((z / 2 : ℝ) : ℂ) * inner ℂ ψ ψ) := by
      rw [addScalar_eval, addScalar_eval, hvals, hTS, inner_add_right, inner_add_right,
        inner_smul_right, inner_smul_right, hinner, hinner]
      ring
    obtain ⟨h1, h2⟩ := hT.2 (M ψ)
    rw [e, Complex.re_ofReal_mul] at h2
    rw [e, Complex.im_ofReal_mul] at h1
    exact ⟨(mul_eq_zero.mp h1).resolve_left hc.ne', nonneg_of_mul_nonneg_right h2 hc⟩
  have hshift : ShiftedHalfPositive z (toBddOp S) := ⟨hself, hbelow⟩
  have hlin : IsLinearMap ℂ M := ⟨hadd, hsmul⟩
  have hMbdd : IsNormBounded M := by
    refine ⟨Real.sqrt c, Real.sqrt_nonneg c, fun f => ?_⟩
    have h1 : ‖M f‖ ^ 2 ≤ (Real.sqrt c * ‖f‖) ^ 2 := by
      rw [hnorm, mul_pow, Real.sq_sqrt hc.le]
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp h1
  refine ⟨hbdd, hshift, fun v => ?_⟩
  exact (hlog (toBddOp S) T M hshift hT (Or.inl hlin) hMbdd
    (fun f => by rw [hvals, hTS]) v).symm
end ScaledIsometries
theorem opLog_on_weight_sector {L N' : ℕ} {σ : Type}
    {multiple : VectorL2 L N' → Matrices.ComplexMatrix2 → L2Field σ} {z : ℝ}
    (hlog : LogCommIntertwiner (VectorL2 L N') (L2Field σ) z)
    (hf : WeightMultipleFacts multiple) : LogRestrictsToSector multiple z := by
  intro t ht T S hT hTS
  have hadd := hf.map_add t ht
  have hsmul := hf.map_smul t ht
  rcases ht with rfl | rfl | rfl
  · exact opLog_of_scaled_isometry (c := 1) hlog one_pos
      (fun v => multiple v (Matrices.ComplexMatrix2.pauliFamily 2)) hadd hsmul
      (fun v v' => by simpa using hf.inner_third v v') T S hT hTS
  · exact opLog_of_scaled_isometry (c := 1 / 2) hlog (by norm_num)
      (fun v => multiple v raisingPauli) hadd hsmul
      (fun v v' => by rw [hf.inner_raising]; norm_num) T S hT hTS
  · exact opLog_of_scaled_isometry (c := 1 / 2) hlog (by norm_num)
      (fun v => multiple v loweringPauli) hadd hsmul
      (fun v v' => by rw [hf.inner_lowering]; norm_num) T S hT hTS
end VertexEdgeLog
theorem logOnVertexAndEdgeSectors_holds
    (h₁ : LogShiftedAndIntertwiners)
    (h₂ : WeightMultiplesAndStar) :
    LogOnVertexAndEdgeSectors := by
  intro L hL z hz
  obtain ⟨-, -, -, -, -, -, hs, hb⟩ := h₂ L hL
  exact ⟨VertexEdgeLog.opLog_on_weight_sector
      (h₁ (VectorL2 L 1) (L2Field (FullSpace.Vertex L 0 0)) z hz).2.2 hs,
    VertexEdgeLog.opLog_on_weight_sector
      (h₁ (VectorL2 L 4) (L2Field (PeriodicOperators.PosEdge L 0 0))
        z hz).2.2 hb⟩
end YangMills.Construction.Tower.AbelianFieldDensity.SectorDecomposition
end
