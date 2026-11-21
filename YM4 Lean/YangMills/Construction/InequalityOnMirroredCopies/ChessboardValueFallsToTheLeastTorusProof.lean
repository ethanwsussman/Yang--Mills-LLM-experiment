import YangMills.Construction.ChessboardTori.ChessboardEstimateAndSubadditivityProof
import YangMills.Construction.ChessboardTori.MirrorPeriodicWeightsAsCellFunctionsProof
import YangMills.Construction.InequalityOnMirroredCopies.ArrayFallsWithThePeriods
import YangMills.Construction.LawInAState.DominationOnTheLeastTorusProof
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.ReflectedCopies
open ChessboardTori
variable {D : ChessboardSetup}
private theorem finite_face (P : PeriodSubgroup D) : Finite P.Face := by apply _root_.YangMills.Construction.ChessboardTori.ReflectionPeriodicWeightsAsCellFunctions.finite_face <;> assumption
private theorem continuous_edgeVariable {L : ℕ} {κ : ℤ} {ℓ : Fin 4 → ℝ}
    (b : BoxTorus.DirectedEdge L κ ℓ) :
    Continuous fun U : BoxTorus.GaugeConfig L κ ℓ => BoxTorus.edgeVariable U b := by
  unfold BoxTorus.edgeVariable
  split_ifs
  · exact continuous_apply _
  · exact (continuous_apply _).inv
private theorem continuous_faceEnergy {L : ℕ} {κ : ℤ} {ℓ : Fin 4 → ℝ}
    (p : BoxTorus.Face L κ ℓ) :
    Continuous fun U : BoxTorus.GaugeConfig L κ ℓ =>
      BoxTorus.faceEnergy U p := by
  have hv : Continuous fun U : BoxTorus.GaugeConfig L κ ℓ =>
      BoxTorus.faceHolonomy U p := by
    unfold BoxTorus.faceHolonomy
    exact (((continuous_edgeVariable _).mul (continuous_edgeVariable _)).mul
      (continuous_edgeVariable _).inv).mul (continuous_edgeVariable _).inv
  have hm : Continuous fun U : BoxTorus.GaugeConfig L κ ℓ =>
      (BoxTorus.faceHolonomy U p : Matrices.ComplexMatrix2) := continuous_subtype_val.comp hv
  unfold BoxTorus.faceEnergy
  refine continuous_const.sub (continuous_const.mul (Complex.continuous_re.comp ?_))
  exact Continuous.matrix_trace hm
abbrev _root_.YangMills.SharedProofs.p4767 := @continuous_faceEnergy
private theorem continuous_wilsonAction (P : PeriodSubgroup D) : Continuous P.wilsonAction := by
  have := finite_face P
  have := Fintype.ofFinite P.Face
  have h : P.wilsonAction = fun U => ∑ p : P.Face, BoxTorus.faceEnergy U p := by
    funext U
    exact finsum_eq_sum_of_fintype _
  rw [h]
  exact continuous_finsetSum _ fun p _ => continuous_faceEnergy p
private instance isProbabilityMeasure_haarMeasure (P : PeriodSubgroup D) :
    IsProbabilityMeasure P.haarMeasure := by
  unfold PeriodSubgroup.haarMeasure BoxTorus.haarConfigMeasure Matrices.ComplexMatrix2.haarPi
  infer_instance
private theorem torusPartition_pos (g : ReflectionGrid D) (n : EvenIndexVector) :
    0 < torusPartition g n := by
  have hc : Continuous fun U : (gridPeriods g n).GaugeConfig =>
      Real.exp (-D.β * (gridPeriods g n).wilsonAction U) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_wilsonAction _))
  exact integral_exp_pos (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
private theorem one_mem_cellObservables (S : Set InfiniteLattice.AmbientSpace) :
    (fun _ => (1 : ℂ)) ∈ ReflectionGrid.cellObservables (D := D) S := by apply _root_.YangMills.Construction.ChessboardTori.ChessboardEstimateAndSubadditivity.one_mem_cellObservables <;> assumption
private theorem tiledIntegral_one (g : ReflectionGrid D) (n : EvenIndexVector)
    (S : Set InfiniteLattice.AmbientSpace) :
    tiledIntegral g n S (fun _ => 1) = (torusPartition g n : ℂ) := by apply _root_.YangMills.SharedProofs.p27906 <;> assumption
private theorem cellCount_cubicCounts (j : ℕ) :
    cellCount (cubicCounts D j) = 16 * (D.L ^ j) ^ 4 := by
  have h : (2 * (D.L : ℤ) ^ j).toNat = 2 * D.L ^ j := by
    have : 2 * (D.L : ℤ) ^ j = ((2 * D.L ^ j : ℕ) : ℤ) := by push_cast; ring
    rw [this, Int.toNat_natCast]
  simp only [cellCount, EvenIndexVector.indexBox, Fintype.card_piFinset, Int.card_Ico, sub_zero,
    cubicCounts, h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring
private theorem rpow_inv_le_of_le_pow {a b : ℝ} {M : ℕ} (hM : 0 < M) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ≤ b ^ (16 * M / 16)) :
    a ^ (1 / ((16 * M : ℕ) : ℝ)) ≤ b ^ (1 / 16 : ℝ) := by
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hd : 16 * M / 16 = M := by omega
  rw [hd] at h
  calc a ^ (1 / ((16 * M : ℕ) : ℝ)) ≤ (b ^ M) ^ (1 / ((16 * M : ℕ) : ℝ)) :=
        Real.rpow_le_rpow ha h (by positivity)
    _ = b ^ (1 / 16 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hb]
        congr 1
        push_cast
        field_simp
theorem chessboardNormBoundedByMinimalTorus_of_tiledIntegralFalls
    (h : TiledIntegralFallsWithPeriods) :
    ChessboardNormBoundedByMinimalTorus := by
  intro D g hg j
  have hMpos : 0 < (D.L ^ j) ^ 4 := by
    have : 0 < D.L := by
      have := D.isAdmissible.2
      omega
    positivity
  have hN := cellCount_cubicCounts (D := D) j
  have hz := torusPartition_pos g (cubicCounts D j)
  have hw := torusPartition_pos g (minimalCounts D)
  have hfall : ∀ S ∈ g.cellSet, ∀ F ∈ ReflectionGrid.cellObservables (D := D) S,
      0 ≤ (tiledIntegral g (minimalCounts D) S F).re ∧
      (tiledIntegral g (cubicCounts D j) S F).im = 0 ∧
      (tiledIntegral g (minimalCounts D) S F).im = 0 ∧
      0 ≤ (tiledIntegral g (cubicCounts D j) S F).re ∧
      (tiledIntegral g (cubicCounts D j) S F).re ^
          (1 / (cellCount (cubicCounts D j) : ℝ)) ≤
        (tiledIntegral g (minimalCounts D) S F).re ^ (1 / 16 : ℝ) := by
    intro S hS F hF
    obtain ⟨hi, h0, -, hle⟩ := h D g hg S hS F hF (cubicCounts D j)
    obtain ⟨hi', h0', -, -⟩ := h D g hg S hS F hF (minimalCounts D)
    refine ⟨h0', hi, hi', h0, ?_⟩
    rw [hN] at hle ⊢
    exact rpow_inv_le_of_le_pow hMpos h0 h0' hle
  constructor
  · have hS : g.cell 0 ∈ g.cellSet := ⟨0, rfl⟩
    obtain ⟨-, -, -, -, hle⟩ := hfall _ hS _ (one_mem_cellObservables _)
    rw [tiledIntegral_one, tiledIntegral_one, Complex.ofReal_re, Complex.ofReal_re] at hle
    have hzp : 0 < torusPartition g (cubicCounts D j) ^
        (1 / (cellCount (cubicCounts D j) : ℝ)) := Real.rpow_pos_of_pos hz _
    rw [torusPartitionRatio, le_div_iff₀ hzp, one_mul]
    exact hle
  · intro S hS F hF
    obtain ⟨hb, hai, hbi, ha, hle⟩ := hfall S hS F hF
    set a := (tiledIntegral g (cubicCounts D j) S F).re with ha_def
    set b := (tiledIntegral g (minimalCounts D) S F).re with hb_def
    set z := torusPartition g (cubicCounts D j) with hz_def
    set w := torusPartition g (minimalCounts D) with hw_def
    set e := (1 / (cellCount (cubicCounts D j) : ℝ)) with he_def
    have hA : tiledIntegral g (cubicCounts D j) S F = (a : ℂ) :=
      Complex.ext (by simp [ha_def]) (by simp [hai])
    have hB : tiledIntegral g (minimalCounts D) S F = (b : ℂ) :=
      Complex.ext (by simp [hb_def]) (by simp [hbi])
    have hnA : ‖tiledMean g (cubicCounts D j) S F‖ = a / z := by
      rw [tiledMean, hA, ← hz_def, ← Complex.ofReal_div, Complex.norm_real, Real.norm_of_nonneg
        (div_nonneg ha hz.le)]
    have hnB : ‖tiledMean g (minimalCounts D) S F‖ = b / w := by
      rw [tiledMean, hB, ← hw_def, ← Complex.ofReal_div, Complex.norm_real, Real.norm_of_nonneg
        (div_nonneg hb hw.le)]
    have hze : 0 < z ^ e := Real.rpow_pos_of_pos hz _
    rw [hnA, hnB, torusPartitionRatio, ← hz_def, ← hw_def, ← he_def, Real.div_rpow ha hz.le,
      Real.div_rpow hb hw.le]
    have : w ^ (1 / 16 : ℝ) / z ^ e * (b ^ (1 / 16 : ℝ) / w ^ (1 / 16 : ℝ)) =
        b ^ (1 / 16 : ℝ) / z ^ e := by
      field_simp
    rw [this]
    exact div_le_div_of_nonneg_right hle hze.le
end YangMills.Construction.ReflectedCopies
end
