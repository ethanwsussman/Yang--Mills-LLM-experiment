import YangMills.Construction.RunningCouplingSlope.DistanceOfTwoCells
import Mathlib
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.CellDistance
theorem half_sum_abs_le_euclidNormVec (w : Fin 4 → ℝ) :
    1 / 2 * ∑ μ, |w μ| ≤ TorusMetric.euclidNormVec w := by
  have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun μ => |w μ|)
  simp only [Finset.card_univ, Fintype.card_fin, sq_abs, Nat.cast_ofNat] at h
  have h1 : TorusMetric.euclidNormVec w = Real.sqrt (∑ μ, w μ ^ 2) := rfl
  rw [h1]
  refine Real.le_sqrt_of_sq_le ?_
  nlinarith
theorem coe_cellOfCoords (L n k : ℕ) (hL : 0 < L) (z : Fin 4 → ℤ) (ν : Fin 4) :
    ((RunningCouplingSlope.cellOfCoords L n k z : Tower.Vertex L n k k) : PeriodicLattice.FourTorus L n) ν =
      ((z ν : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) := by
  have hsp : PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k k) = 1 := by
    simp [PeriodicLattice.meshSize, PeriodicLattice.levelDepth]
  change (((0 + ∑ μ, z μ • PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k k) μ :
    PeriodicLattice.Site L n (PeriodicLattice.levelDepth k k)) : PeriodicLattice.FourTorus L n)) ν = _
  simp only [zero_add, AddSubgroup.val_finset_sum, AddSubgroup.coe_zsmul, Finset.sum_apply,
    Pi.smul_apply]
  have hst : ∀ μ, ((PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k k) μ :
      PeriodicLattice.Site L n (PeriodicLattice.levelDepth k k)) : PeriodicLattice.FourTorus L n) =
      PeriodicLattice.pointOnAxis L n μ 1 := by
    intro μ
    change PeriodicLattice.pointOnAxis L n μ _ = _
    rw [hsp]
  simp only [hst, PeriodicLattice.pointOnAxis]
  rw [Finset.sum_eq_single ν]
  · simp only [Pi.single_eq_same]
    have : ((z ν : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) =
        z ν • ((1 : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) := by
      rw [← QuotientAddGroup.mk_zsmul]
      simp
    rw [this]
  · intro μ _ h
    simp [Pi.single_eq_of_ne (Ne.symm h)]
  · simp
theorem cellDistLowerBound_holds : RunningCouplingSlope.CellDistLowerBound := by
  intro L n k hL z hz
  set S := PeriodicLattice.torusSide L n with hS
  have hSpos : 0 < S := by
    have : (0 : ℝ) < L := by exact_mod_cast hL
    simp only [hS, PeriodicLattice.torusSide]
    positivity
  set x : PeriodicLattice.FourTorus L n :=
    ((RunningCouplingSlope.cellOfCoords L n k 0 : Tower.Vertex L n k k) : PeriodicLattice.FourTorus L n) -
      ((RunningCouplingSlope.cellOfCoords L n k z : Tower.Vertex L n k k) : PeriodicLattice.FourTorus L n) with hx
  have hxv : ∀ ν, x ν = ((-(z ν : ℝ) : ℝ) : AddCircle S) := by
    intro ν
    simp only [hx, Pi.sub_apply, coe_cellOfCoords L n k hL]
    simp
    rfl
  refine le_csInf ?_ ?_
  · refine ⟨_, ⟨fun ν => -(z ν : ℝ), ?_, rfl⟩⟩
    funext ν
    exact (hxv ν).symm
  · rintro _ ⟨w, hw, rfl⟩
    have hw' : ∀ ν, |(z ν : ℝ)| ≤ |w ν| := by
      intro ν
      have e1 : ((w ν : ℝ) : AddCircle S) = ((-(z ν : ℝ) : ℝ) : AddCircle S) := by
        rw [← hxv ν]
        exact congrFun hw ν
      have e2 : ((w ν + (z ν : ℝ) : ℝ) : AddCircle S) = 0 := by
        rw [AddCircle.coe_add, e1, ← AddCircle.coe_add]
        simp
      obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff S).mp e2
      have hzS : 2 * |(z ν : ℝ)| ≤ S := by
        have h1 : ((|z ν| : ℤ) : ℝ) ≤ (((L : ℤ) ^ n : ℤ) : ℝ) := by exact_mod_cast hz ν
        simp only [Int.cast_abs, Int.cast_pow, Int.cast_natCast] at h1
        simp only [hS, PeriodicLattice.torusSide]
        linarith
      rcases eq_or_ne m 0 with rfl | hm0
      · have : w ν = -(z ν : ℝ) := by
          simp at hm
          linarith
        rw [this, abs_neg]
      · have h1 : S ≤ |m • S| := by
          rw [zsmul_eq_mul, abs_mul, abs_of_pos hSpos]
          have : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hm0
          nlinarith
        rw [hm] at h1
        have h2 : |w ν + (z ν : ℝ)| ≤ |w ν| + |(z ν : ℝ)| := abs_add_le _ _
        linarith
    calc 1 / 2 * ∑ μ, |(z μ : ℝ)| ≤ 1 / 2 * ∑ μ, |w μ| := by
          have := Finset.sum_le_sum fun μ (_ : μ ∈ Finset.univ) => hw' μ
          linarith
      _ ≤ TorusMetric.euclidNormVec w := half_sum_abs_le_euclidNormVec w
end YangMills.Construction.RunningCouplingSlope.CellDistance
end
