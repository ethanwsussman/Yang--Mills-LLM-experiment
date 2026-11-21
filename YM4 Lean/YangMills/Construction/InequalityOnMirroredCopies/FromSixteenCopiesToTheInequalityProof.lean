import YangMills.Construction.InequalityOnMirroredCopies.ArrayFallsWithThePeriods
import YangMills.Construction.InequalityOnMirroredCopies.CentreOfACopyProof
import YangMills.Construction.InequalityOnMirroredCopies.ChessboardValueFallsToTheLeastTorus
import YangMills.Construction.InequalityOnMirroredCopies.FromSixteenCopiesToTheInequality
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReflectedCopies
open ChessboardTori
open InfiniteLattice (AmbientSpace)
variable {D : ChessboardSetup}
private theorem sub_const_mem_cellObservables {S : Set AmbientSpace} {F : D.GaugeField → ℂ}
    (hF : F ∈ ReflectionGrid.cellObservables (D := D) S) (κ : ℂ) :
    (fun U => F U - κ) ∈ ReflectionGrid.cellObservables (D := D) S := by apply _root_.YangMills.SharedProofs.p60740 <;> assumption
private theorem cellCount_pos (n : EvenIndexVector) : 0 < cellCount n := by
  refine Finset.card_pos.mpr ⟨0, ?_⟩
  rw [EvenIndexVector.indexBox, Fintype.mem_piFinset]
  intro κ
  have := n.two_le κ
  simp only [Pi.zero_apply, Finset.mem_Ico, le_refl, true_and]
  omega
private theorem torusPartition_nonneg (g : ReflectionGrid D) (n : EvenIndexVector) :
    0 ≤ torusPartition g n :=
  MeasureTheory.integral_nonneg fun _ => (Real.exp_pos _).le
private theorem le_pow_of_rpow_inv_le {x y R E q₀ q : ℝ} {N : ℕ} (hN : 0 < N) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hroot : x ^ (1 / (N : ℝ)) ≤ R * y ^ (1 / 16 : ℝ)) (hRE : R ≤ E) (hR : 1 ≤ R)
    (hq₀ : 0 ≤ q₀) (hy₀ : y ≤ q₀ ^ 16) (hq : E * q₀ ≤ q) : x ≤ q ^ N := by
  have h₁ : y ^ (1 / 16 : ℝ) ≤ q₀ := by
    calc y ^ (1 / 16 : ℝ) ≤ (q₀ ^ 16) ^ (1 / 16 : ℝ) := Real.rpow_le_rpow hy hy₀ (by norm_num)
      _ = q₀ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hq₀]
        norm_num
  have h₂ : x ^ (1 / (N : ℝ)) ≤ q :=
    hroot.trans ((mul_le_mul_of_nonneg_left h₁ (by linarith)).trans
      ((mul_le_mul_of_nonneg_right hRE hq₀).trans hq))
  calc x = (x ^ (1 / (N : ℝ))) ^ N := by
        rw [one_div, Real.rpow_inv_natCast_pow hx hN.ne']
    _ ≤ q ^ N := pow_le_pow_left₀ (Real.rpow_nonneg hx _) h₂ N
private theorem logPos_le_logPos {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    TorusBound.logPos s ≤ TorusBound.logPos t :=
  max_le_max (Real.log_le_log hs hst) le_rfl
private theorem exp_mul_copyBound_le {A₀ b₀ b₁ l ϱ : ℝ} (h : AmbientSpace → ℝ) (hA₀ : 0 ≤ A₀) (hb₁ : 0 ≤ b₁)
    (hϱ : 0 < ϱ) (hϱl : ϱ ≤ l / 4) (hn : 0 ≤ radiusNorm ϱ h) :
    Real.exp (b₁ * l ^ 4 + b₁ * TorusBound.logPos (1 / l) ^ (1 / 20 : ℝ)) *
        copyBound A₀ b₀ l ϱ h ≤ copyBound A₀ (b₀ + b₁) l ϱ h := by
  have hl : ϱ ≤ l := by linarith
  have hlog : TorusBound.logPos (1 / l) ^ (1 / 20 : ℝ) ≤
      TorusBound.logPos (1 / ϱ) ^ (1 / 20 : ℝ) :=
    Real.rpow_le_rpow (le_max_right _ _)
      (logPos_le_logPos (by have : 0 < l := by linarith
                            positivity) (one_div_le_one_div_of_le hϱ hl)) (by norm_num)
  have hexp : Real.exp (b₁ * l ^ 4 + b₁ * TorusBound.logPos (1 / l) ^ (1 / 20 : ℝ)) *
        Real.exp (b₀ * l ^ 4 + b₀ * TorusBound.logPos (1 / ϱ) ^ (1 / 20 : ℝ)) ≤
      Real.exp ((b₀ + b₁) * l ^ 4 +
        (b₀ + b₁) * TorusBound.logPos (1 / ϱ) ^ (1 / 20 : ℝ)) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [mul_le_mul_of_nonneg_left hlog hb₁]
  unfold copyBound copySize
  calc _ = A₀ * (Real.exp (b₁ * l ^ 4 + b₁ * TorusBound.logPos (1 / l) ^ (1 / 20 : ℝ)) *
        Real.exp (b₀ * l ^ 4 + b₀ * TorusBound.logPos (1 / ϱ) ^ (1 / 20 : ℝ))) *
        radiusNorm ϱ h := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hA₀) hn
private theorem radiusNorm_nonneg (ϱ : ℝ) (h : AmbientSpace → ℝ) : 0 ≤ radiusNorm ϱ h :=
  le_max_of_le_left (Real.iSup_nonneg fun _ => norm_nonneg _)
theorem sixteenCopiesImpliesInequality_holds
    (hChess : ChessboardNormBoundedByMinimalTorus)
    (hTiled : TiledIntegralFallsWithPeriods)
    (hObs : SmearedMemCellObservables) :
    SixteenCopiesImpliesInequality := by
  intro D A₀ b₀ b₁ hA₀ hb₀ hb₁ h16 hRatio c ϱ h hh
  obtain ⟨κ, hκ⟩ := h16 c ϱ h hh
  refine ⟨κ, fun j => ?_⟩
  have hF : centredSmeared D h κ ∈ ReflectionGrid.cellObservables (D := D) c.cell :=
    sub_const_mem_cellObservables (hObs D c ϱ h hh) (κ : ℂ)
  obtain ⟨him, hre, -, -⟩ :=
    hTiled D c.grid c.hasAdmissibleSide c.cell c.cell_mem_cellSet _ hF (cubicCounts D j)
  obtain ⟨hR, hchess⟩ := hChess D c.grid c.hasAdmissibleSide j
  have hroot := hchess c.cell c.cell_mem_cellSet _ hF
  have hZ := torusPartition_nonneg c.grid (cubicCounts D j)
  have hn := radiusNorm_nonneg ϱ h
  have hq₀ : 0 ≤ copyBound A₀ b₀ c.side ϱ h :=
    mul_nonneg (mul_nonneg hA₀ (Real.exp_pos _).le) hn
  have hRb : torusPartitionRatio c.grid j ≤ Real.exp (b₁ * c.side ^ 4 +
      b₁ * TorusBound.logPos (1 / c.side) ^ (1 / 20 : ℝ)) := hRatio c.grid c.hasAdmissibleSide j
  have hle := le_pow_of_rpow_inv_le (cellCount_pos (cubicCounts D j)) (norm_nonneg _)
    (norm_nonneg _) hroot hRb hR hq₀ hκ
    (exp_mul_copyBound_le h hA₀ hb₁ hh.radius_pos hh.radius_le hn)
  refine ⟨?_, ?_, (Complex.re_le_norm _).trans hle⟩
  · rw [tiledMean, Complex.div_ofReal_im, him, zero_div]
  · rw [tiledMean, Complex.div_ofReal_re]
    exact div_nonneg hre hZ
end YangMills.Construction.ReflectedCopies
end
