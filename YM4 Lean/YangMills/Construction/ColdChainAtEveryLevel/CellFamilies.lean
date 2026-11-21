import YangMills.Construction.ColdChainAtEveryLevel.CellNorms
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
namespace YangMills.Construction.CellSpans
variable {F : BlockAverages.BlockFrame} {k : ℕ}
def spanChart (U : BlockAverages.ChainChart F) (A : Fin k → BlockAverages.ChainChart F) (t : Fin k → ℂ) :
    BlockAverages.ComplexChainChart F :=
  ⟨BlockAverages.chartShiftMulti U A fun l => (t l).re,
    BlockAverages.chartShiftMulti (BlockAverages.zeroChart F) A fun l => (t l).im⟩
theorem purePart_ofQuat_imaginary (w : BlockAverages.imaginaryQuaternions) :
    ComplexifiedQuaternions.purePart (ComplexifiedQuaternions.ofQuat (w : ℍ[ℝ])) =
      ComplexifiedQuaternions.ofQuat (w : ℍ[ℝ]) := by
  rw [ComplexifiedQuaternions.purePart_ofQuat]
  congr 1
  have h : ((w : ℍ[ℝ])).re = 0 := w.2
  ext <;> simp [h] <;> ring
theorem conjByUnit_ofQuat (g : BlockAverages.UnitQuaternion) (q : ℍ[ℝ]) :
    BlockAverages.conjByUnit g (ComplexifiedQuaternions.ofQuat q) =
      ComplexifiedQuaternions.ofQuat (BlockAverages.adjointAction g q) := by
  simp only [BlockAverages.conjByUnit, BlockAverages.adjointAction, BlockAverages.ofUnit,
    ComplexifiedQuaternions.ofQuat_mul]
theorem complexifiedImaginary_span (a₀ : BlockAverages.imaginaryQuaternions)
    (a : Fin k → BlockAverages.imaginaryQuaternions) (t : Fin k → ℂ) :
    BlockAverages.complexifiedImaginary (a₀ + ∑ l, (t l).re • a l)
        ((0 : BlockAverages.imaginaryQuaternions) + ∑ l, (t l).im • a l) =
      ComplexifiedQuaternions.ofQuat (a₀ : ℍ[ℝ]) + ∑ l, t l • ComplexifiedQuaternions.ofQuat (a l : ℍ[ℝ]) := by
  unfold BlockAverages.complexifiedImaginary
  simp only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul, ComplexifiedQuaternions.ofQuat_add,
    BlockAverages.ofQuat_sum, ComplexifiedQuaternions.ofQuat_smul, zero_add,
    Submodule.coe_zero, ComplexifiedQuaternions.ofQuat_zero, Finset.smul_sum]
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [smul_smul, ← add_smul]
  congr 1
  rw [mul_comm]
  exact Complex.re_add_im (t l)
theorem baseSource_spanChart (U : BlockAverages.ChainChart F) (A : Fin k → BlockAverages.ChainChart F)
    (t : Fin k → ℂ) (x : F.Site 0) (i : Fin 4) :
    CellSources.baseSource (spanChart U A t) x i =
      ComplexifiedQuaternions.ofQuat (U.fine x i : ℍ[ℝ]) +
        ∑ l, t l • ComplexifiedQuaternions.ofQuat ((A l).fine x i : ℍ[ℝ]) :=
  complexifiedImaginary_span (U.fine x i) (fun l => (A l).fine x i) t
theorem upperSource_spanChart (U : BlockAverages.ChainChart F) (A : Fin k → BlockAverages.ChainChart F)
    (t : Fin k → ℂ) (x : Σ m : ℕ, F.Site (m + 1) × Fin 4) :
    CellSources.upperSource (spanChart U A t) x =
      ComplexifiedQuaternions.ofQuat (U.coarse x.1 x.2.1 x.2.2 : ℍ[ℝ]) +
        ∑ l, t l • ComplexifiedQuaternions.ofQuat ((A l).coarse x.1 x.2.1 x.2.2 : ℍ[ℝ]) :=
  complexifiedImaginary_span (U.coarse x.1 x.2.1 x.2.2) (fun l => (A l).coarse x.1 x.2.1 x.2.2) t
def ofQuatForm (U : BlockAverages.ChainChart F) : F.Site 0 → Fin 4 → ComplexifiedQuaternions.ComplexQuat :=
  fun x i => ComplexifiedQuaternions.ofQuat (U.fine x i : ℍ[ℝ])
theorem baseSource_spanChart_eq (U : BlockAverages.ChainChart F) (A : Fin k → BlockAverages.ChainChart F)
    (t : Fin k → ℂ) :
    CellSources.baseSource (spanChart U A t) = ofQuatForm U + ∑ l, t l • ofQuatForm (A l) := by
  funext x i
  rw [baseSource_spanChart]
  simp [ofQuatForm, Finset.sum_apply]
theorem ofQuat_sub (p q : ℍ[ℝ]) :
    ComplexifiedQuaternions.ofQuat (p - q) = ComplexifiedQuaternions.ofQuat p - ComplexifiedQuaternions.ofQuat q :=
  eq_sub_of_add_eq (by rw [← ComplexifiedQuaternions.ofQuat_add, sub_add_cancel])
theorem covariantCurl_ofQuatForm (R : F.GaugeField 0) (q : F.Site 0 × Fin 4 × Fin 4)
    (U : BlockAverages.ChainChart F) :
    ComplexPlaquettes.covariantCurl R q (ofQuatForm U) =
      ComplexifiedQuaternions.ofQuat (BlockAverages.linearizedCurl R U.fine q) := by
  simp only [ComplexPlaquettes.covariantCurl, ofQuatForm, purePart_ofQuat_imaginary, conjByUnit_ofQuat,
    BlockAverages.linearizedCurl, ComplexPlaquettes.basePlaquetteHolonomy, ComplexifiedQuaternions.ofQuat_add,
    ofQuat_sub]
theorem covariantCurl_smul (R : F.GaugeField 0) (q : F.Site 0 × Fin 4 × Fin 4) (c : ℂ)
    (ξ : F.Site 0 → Fin 4 → ComplexifiedQuaternions.ComplexQuat) :
    ComplexPlaquettes.covariantCurl R q (c • ξ) = c • ComplexPlaquettes.covariantCurl R q ξ := by
  simp only [ComplexPlaquettes.covariantCurl, Pi.smul_apply, ComplexifiedQuaternions.purePart_smul,
    ComplexContours.conjByUnit_smul, smul_add, smul_sub]
theorem covariantCurl_zero (R : F.GaugeField 0) (q : F.Site 0 × Fin 4 × Fin 4) :
    ComplexPlaquettes.covariantCurl R q 0 = 0 := by
  have := covariantCurl_smul R q 0 0
  simpa using this
theorem covariantCurl_sum (R : F.GaugeField 0) (q : F.Site 0 × Fin 4 × Fin 4) {ι : Type} (s : Finset ι)
    (f : ι → F.Site 0 → Fin 4 → ComplexifiedQuaternions.ComplexQuat) :
    ComplexPlaquettes.covariantCurl R q (∑ i ∈ s, f i) = ∑ i ∈ s, ComplexPlaquettes.covariantCurl R q (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using covariantCurl_zero R q
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ComplexPlaquettes.covariantCurl_add, ih]
section Sizes
theorem finsetLpNorm_span_le {ι : Type} {P : ℕ} (hP : 1 ≤ P) (s : Finset ι) (f₀ : ι → ℝ) (f : Fin k → ι → ℝ)
    (c : Fin k → ℝ) (hc : ∀ l, 0 ≤ c l) :
    LevelRecursion.finsetLpNorm P s (fun i => f₀ i + ∑ l, c l * f l i) ≤
      LevelRecursion.finsetLpNorm P s f₀ + ∑ l, c l * LevelRecursion.finsetLpNorm P s (f l) := by
  refine (LevelRecursion.finsetLpNorm_add_le hP s _ _).trans (add_le_add le_rfl ?_)
  refine (LevelRecursion.finsetLpNorm_sum_le hP Finset.univ s fun l i => c l * f l i).trans
    (Finset.sum_le_sum fun l _ => ?_)
  exact ComplexDifferences.finsetLpNorm_const_mul_le hP s (f l) (hc l)
def spanLocalNorm (S : Finset F.Cell) (R : F.FieldChain) (U : BlockAverages.ChainChart F)
    (A : Fin k → BlockAverages.ChainChart F) (t : Fin k → ℂ) (z : F.Cell) : ℝ :=
  BlockAverages.localNorm S R U (BlockAverages.constOneWeights F) z +
    ∑ l, ‖t l‖ * BlockAverages.localNorm S R (A l) (BlockAverages.constOneWeights F) z
theorem norm_ofQuat_imaginary (w : BlockAverages.imaginaryQuaternions) :
    ‖ComplexifiedQuaternions.ofQuat (w : ℍ[ℝ])‖ = ‖w‖ := by
  rw [ComplexifiedQuaternions.norm_ofQuat]
  rfl
theorem sourceBounds_spanChart (hL : Odd F.blockSide) {S : Finset F.Cell} {z : F.Cell} (R : F.FieldChain)
    (U : BlockAverages.ChainChart F) (A : Fin k → BlockAverages.ChainChart F) (t : Fin k → ℂ) {y : ℝ}
    (hy : spanLocalNorm S R U A t z ≤ y) :
    CellNormBounds.SourceBounds S z R (spanChart U A t) y := by
  have hc : ∀ l, 0 ≤ ‖t l‖ := fun _ => norm_nonneg _
  have one_mul' : ∀ {j : ℕ} (x : F.Site j) (c : ℝ), BlockAverages.constOneWeights F j x * c = c :=
    fun _ c => one_mul c
  refine ⟨?_, ?_, ?_⟩
  · have h1 := finsetLpNorm_span_le (P := 4) (by norm_num)
      (BlockAverages.innerBonds (BlockAverages.cellBall S z 1) 0) (fun b => ‖U.fine b.1 b.2‖)
      (fun l b => ‖(A l).fine b.1 b.2‖) (fun l => ‖t l‖) hc
    have hU := CellNormBounds.finsetLpNorm_fine_le_localNorm hL S z R U (BlockAverages.constOneWeights F)
    simp only [one_mul'] at hU
    have hA : ∀ l, LevelRecursion.finsetLpNorm 4 (BlockAverages.innerBonds (BlockAverages.cellBall S z 1) 0)
        (fun b => ‖(A l).fine b.1 b.2‖) ≤
        BlockAverages.localNorm S R (A l) (BlockAverages.constOneWeights F) z := fun l => by
      have := CellNormBounds.finsetLpNorm_fine_le_localNorm hL S z R (A l) (BlockAverages.constOneWeights F)
      simpa only [one_mul'] using this
    refine le_trans (CellSources.finsetLpNorm_le_of_le (by norm_num) (fun _ _ => norm_nonneg _)
      fun b _ => ?_) (h1.trans ?_)
    · rw [baseSource_spanChart]
      refine (norm_add_le _ _).trans
        (add_le_add (le_of_eq (norm_ofQuat_imaginary _)) ((norm_sum_le _ _).trans ?_))
      refine Finset.sum_le_sum fun l _ => ?_
      rw [norm_smul, norm_ofQuat_imaginary]
    · refine le_trans (add_le_add hU
        (Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hA l) (hc l))) hy
  · have h1 := finsetLpNorm_span_le (P := 2) (by norm_num)
      (ComplexCells.lowerBonds (BlockAverages.cellBall S z 1)) (fun x => ‖U.coarse x.1 x.2.1 x.2.2‖)
      (fun l x => ‖(A l).coarse x.1 x.2.1 x.2.2‖) (fun l => ‖t l‖) hc
    have hU := CellNormBounds.finsetLpNorm_coarse_le_localNorm hL S z R U (BlockAverages.constOneWeights F)
    simp only [one_mul'] at hU
    have hA : ∀ l, LevelRecursion.finsetLpNorm 2 (ComplexCells.lowerBonds (BlockAverages.cellBall S z 1))
        (fun x => ‖(A l).coarse x.1 x.2.1 x.2.2‖) ≤
        BlockAverages.localNorm S R (A l) (BlockAverages.constOneWeights F) z := fun l => by
      have := CellNormBounds.finsetLpNorm_coarse_le_localNorm hL S z R (A l) (BlockAverages.constOneWeights F)
      simpa only [one_mul'] using this
    refine le_trans (CellSources.finsetLpNorm_le_of_le (by norm_num) (fun _ _ => norm_nonneg _)
      fun x _ => ?_) (h1.trans ?_)
    · rw [upperSource_spanChart]
      refine (norm_add_le _ _).trans
        (add_le_add (le_of_eq (norm_ofQuat_imaginary _)) ((norm_sum_le _ _).trans ?_))
      refine Finset.sum_le_sum fun l _ => ?_
      rw [norm_smul, norm_ofQuat_imaginary]
    · refine le_trans (add_le_add hU
        (Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hA l) (hc l))) hy
  · have h1 := finsetLpNorm_span_le (P := 2) (by norm_num) (BlockAverages.plaquettesOver S {z} 0)
      (fun q => ‖BlockAverages.linearizedCurl (R 0) U.fine q‖)
      (fun l q => ‖BlockAverages.linearizedCurl (R 0) (A l).fine q‖) (fun l => ‖t l‖) hc
    have hU := CellNormBounds.finsetLpNorm_curl_le_localNorm hL S z R U (BlockAverages.constOneWeights F)
    simp only [one_mul'] at hU
    have hA : ∀ l, LevelRecursion.finsetLpNorm 2 (BlockAverages.plaquettesOver S {z} 0)
        (fun q => ‖BlockAverages.linearizedCurl (R 0) (A l).fine q‖) ≤
        BlockAverages.localNorm S R (A l) (BlockAverages.constOneWeights F) z := fun l => by
      have := CellNormBounds.finsetLpNorm_curl_le_localNorm hL S z R (A l) (BlockAverages.constOneWeights F)
      simpa only [one_mul'] using this
    refine le_trans (CellSources.finsetLpNorm_le_of_le (by norm_num) (fun _ _ => norm_nonneg _)
      fun q _ => ?_) (h1.trans ?_)
    · rw [baseSource_spanChart_eq, ComplexPlaquettes.covariantCurl_add, covariantCurl_sum,
        covariantCurl_ofQuatForm]
      refine (norm_add_le _ _).trans
        (add_le_add (le_of_eq (ComplexifiedQuaternions.norm_ofQuat _)) ((norm_sum_le _ _).trans ?_))
      refine Finset.sum_le_sum fun l _ => ?_
      rw [covariantCurl_smul, covariantCurl_ofQuatForm, norm_smul, ComplexifiedQuaternions.norm_ofQuat]
    · refine le_trans (add_le_add hU
        (Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hA l) (hc l))) hy
theorem sourceParallelogram_spanChart (U : BlockAverages.ChainChart F) (A : Fin k → BlockAverages.ChainChart F)
    {t₀ t₁ t₂ t₃ : Fin k → ℂ} (h : t₃ = t₁ + t₂ - t₀) :
    CellSources.SourceParallelogram (spanChart U A t₀) (spanChart U A t₁) (spanChart U A t₂)
      (spanChart U A t₃) := by
  subst h
  refine ⟨fun x i => ?_, fun x => ?_⟩
  · simp only [baseSource_spanChart, Pi.sub_apply, Pi.add_apply, sub_smul, add_smul, Finset.sum_sub_distrib,
      Finset.sum_add_distrib]
    abel
  · simp only [upperSource_spanChart, Pi.sub_apply, Pi.add_apply, sub_smul, add_smul, Finset.sum_sub_distrib,
      Finset.sum_add_distrib]
    abel
end Sizes
section Weights
theorem scaleWeight_le_classWeight {S : Finset F.Cell} (hodd : Odd F.blockSide) {φ : F.Cell → ℝ} {del : ℝ}
    (hdel : 0 ≤ del) (hφ : ∀ y y', |φ y - φ y'| ≤ del * BlockAverages.cellSupDist y y') (θ : ℝ) (p : F.Site 0)
    (z : F.Cell) {j : ℕ} (x : F.Site j) (hx : BlockAverages.cellSupDist z (BlockAverages.enclosingCell x) ≤ 1) :
    LevelRecursion.scaleWeight p θ j x ≤
        (Real.exp (del - φ z) * ((F.blockSide : ℝ) ^ F.top) ^ (-θ)) * BlockAverages.classWeight F φ θ p j x ∧
      LevelRecursion.scaleWeight p (-θ) j x ≤ (Real.exp (del + φ z) * ((F.blockSide : ℝ) ^ F.top) ^ θ) *
        BlockAverages.invertedWeights (BlockAverages.classWeight F φ θ p) j x := by
  have hL1 : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  set N : ℝ := (F.blockSide : ℝ) ^ F.top with hN
  have hN0 : 0 < N := by positivity
  set ρ := BlockAverages.scaleRadius F j p x with hρ
  have hρ0 : 0 < ρ := WeightedAverages.Chains.scaleRadius_pos hodd.pos _ _ _
  set c := BlockAverages.enclosingCell x with hc
  have hd : (BlockAverages.cellSupDist z c : ℝ) ≤ 1 := by exact_mod_cast hx
  have h1 := abs_le.1 (hφ z c)
  have hdd : del * (BlockAverages.cellSupDist z c : ℝ) ≤ del := by
    have := mul_le_mul_of_nonneg_left hd hdel
    linarith
  have e1 : BlockAverages.classWeight F φ θ p j x = Real.exp (φ c) * (ρ ^ (-θ) / N ^ (-θ)) := by
    simp only [BlockAverages.classWeight]
    rw [Real.div_rpow hρ0.le hN0.le]
  have hA : 0 < ρ ^ (-θ) := Real.rpow_pos_of_pos hρ0 _
  have hA' : 0 < ρ ^ θ := Real.rpow_pos_of_pos hρ0 _
  have eρ : ρ ^ (-θ) * ρ ^ θ = 1 := by
    rw [← Real.rpow_add hρ0]
    simp
  have eN : N ^ (-θ) * N ^ θ = 1 := by
    rw [← Real.rpow_add hN0]
    simp
  constructor
  · rw [e1]
    show ρ ^ (-θ) ≤ _
    have e2 : Real.exp (del - φ z) * N ^ (-θ) * (Real.exp (φ c) * (ρ ^ (-θ) / N ^ (-θ))) =
        Real.exp (del - φ z + φ c) * ρ ^ (-θ) := by
      rw [Real.exp_add]
      field_simp
    rw [e2]
    have : 1 ≤ Real.exp (del - φ z + φ c) := Real.one_le_exp (by linarith)
    nlinarith
  · show ρ ^ (- -θ) ≤ _
    rw [neg_neg]
    have e2 : BlockAverages.invertedWeights (BlockAverages.classWeight F φ θ p) j x =
        Real.exp (-φ c) * N ^ (-θ) * ρ ^ θ := by
      simp only [BlockAverages.invertedWeights]
      rw [e1, Real.exp_neg]
      have h3 : ρ ^ θ = (ρ ^ (-θ))⁻¹ := by
        field_simp
        linarith
      rw [h3]
      field_simp
    rw [e2]
    have e3 : Real.exp (del + φ z) * N ^ θ * (Real.exp (-φ c) * N ^ (-θ) * ρ ^ θ) =
        Real.exp (del + φ z - φ c) * ρ ^ θ := by
      rw [sub_eq_add_neg, Real.exp_add (del + φ z)]
      calc _ = Real.exp (del + φ z) * Real.exp (-φ c) * (N ^ (-θ) * N ^ θ) * ρ ^ θ := by ring
        _ = _ := by rw [eN, mul_one]
    rw [e3]
    have : 1 ≤ Real.exp (del + φ z - φ c) := Real.one_le_exp (by linarith)
    nlinarith
theorem weighted_diff_le (hL : Odd F.blockSide) {S : Finset F.Cell} {z : F.Cell} (R : F.FieldChain)
    (B : BlockAverages.ChainChart F) (τ : ℂ) {w : F.SiteWeights} {κ : ℝ} (p : F.Site 0) {θ : ℝ} (hκ : 0 ≤ κ)
    (hw0 : ∀ j x, 0 ≤ w j x)
    (hw : ∀ (j : ℕ) (x : F.Site j), BlockAverages.cellSupDist z (BlockAverages.enclosingCell x) ≤ 1 →
      LevelRecursion.scaleWeight p θ j x ≤ κ * w j x) :
    LevelRecursion.weightedScaleNorm (BlockAverages.cellBall S z 1) p θ 4 0
        (fun x i => ‖τ • ComplexifiedQuaternions.ofQuat (B.fine x i : ℍ[ℝ])‖) +
      LevelRecursion.finsetLpNorm 2 (ComplexCells.lowerBonds (BlockAverages.cellBall S z 1))
        (fun x => CellSources.lowerScaleWeight p θ x *
          ‖τ • ComplexifiedQuaternions.ofQuat (B.coarse x.1 x.2.1 x.2.2 : ℍ[ℝ])‖) +
      LevelRecursion.finsetLpNorm 2 (BlockAverages.plaquettesOver S {z} 0)
        (fun q => LevelRecursion.scaleWeight p θ 0 q.1 *
          ‖τ • ComplexifiedQuaternions.ofQuat (BlockAverages.linearizedCurl (R 0) B.fine q)‖) ≤
      3 * (‖τ‖ * κ * BlockAverages.localNorm S R B w z) := by
  have hc0 : 0 ≤ ‖τ‖ * κ := mul_nonneg (norm_nonneg _) hκ
  have hpt : ∀ {j : ℕ} (x : F.Site j) (c : ℝ), 0 ≤ c →
      BlockAverages.cellSupDist z (BlockAverages.enclosingCell x) ≤ 1 →
      LevelRecursion.scaleWeight p θ j x * (‖τ‖ * c) ≤ (‖τ‖ * κ) * (w j x * c) := by
    intro j x c hc hx
    have h1 := mul_le_mul_of_nonneg_right (hw j x hx) (mul_nonneg (norm_nonneg τ) hc)
    calc _ ≤ κ * w j x * (‖τ‖ * c) := h1
      _ = _ := by ring
  have hcell : ∀ {j : ℕ} {b : F.Site j × Fin 4}, b ∈ BlockAverages.innerBonds (BlockAverages.cellBall S z 1) j →
      BlockAverages.cellSupDist z (BlockAverages.enclosingCell b.1) ≤ 1 := by
    intro j b hb
    simp only [BlockAverages.innerBonds, Finset.mem_filter, Finset.mem_product] at hb
    exact (Finset.mem_filter.1 (BlockLines.enclosingCell_mem hL hb.1.1)).2
  have t1 : LevelRecursion.weightedScaleNorm (BlockAverages.cellBall S z 1) p θ 4 0
      (fun x i => ‖τ • ComplexifiedQuaternions.ofQuat (B.fine x i : ℍ[ℝ])‖) ≤
      ‖τ‖ * κ * BlockAverages.localNorm S R B w z := by
    have c1 := ComplexDifferences.finsetLpNorm_const_mul_le (P := 4) (by norm_num)
      (BlockAverages.innerBonds (BlockAverages.cellBall S z 1) 0)
      (fun b => w 0 b.1 * ‖B.fine b.1 b.2‖) (a := ‖τ‖ * κ) hc0
    refine le_trans (CellSources.finsetLpNorm_le_of_le (by norm_num)
      (fun b _ => mul_nonneg (LevelRecursion.scaleWeight_pos hL p θ 0 b.1).le (norm_nonneg _)) fun b hb => ?_)
      (c1.trans (mul_le_mul_of_nonneg_left (CellNormBounds.finsetLpNorm_fine_le_localNorm hL S z R B w) hc0))
    beta_reduce
    rw [norm_smul, norm_ofQuat_imaginary]
    exact hpt _ _ (norm_nonneg _) (hcell hb)
  have t2 : LevelRecursion.finsetLpNorm 2 (ComplexCells.lowerBonds (BlockAverages.cellBall S z 1))
      (fun x => CellSources.lowerScaleWeight p θ x *
        ‖τ • ComplexifiedQuaternions.ofQuat (B.coarse x.1 x.2.1 x.2.2 : ℍ[ℝ])‖) ≤
      ‖τ‖ * κ * BlockAverages.localNorm S R B w z := by
    have c1 := ComplexDifferences.finsetLpNorm_const_mul_le (P := 2) (by norm_num)
      (ComplexCells.lowerBonds (BlockAverages.cellBall S z 1))
      (fun x => w (x.1 + 1) x.2.1 * ‖B.coarse x.1 x.2.1 x.2.2‖) (a := ‖τ‖ * κ) hc0
    refine le_trans (CellSources.finsetLpNorm_le_of_le (by norm_num)
      (fun x _ => mul_nonneg (CellSources.lowerScaleWeight_pos hL p θ x).le (norm_nonneg _)) fun x hx => ?_)
      (c1.trans (mul_le_mul_of_nonneg_left (CellNormBounds.finsetLpNorm_coarse_le_localNorm hL S z R B w) hc0))
    rw [norm_smul, norm_ofQuat_imaginary]
    exact hpt x.2.1 _ (norm_nonneg _) (hcell (ComplexCells.mem_lowerBonds hx).2)
  have t3 : LevelRecursion.finsetLpNorm 2 (BlockAverages.plaquettesOver S {z} 0)
      (fun q => LevelRecursion.scaleWeight p θ 0 q.1 *
        ‖τ • ComplexifiedQuaternions.ofQuat (BlockAverages.linearizedCurl (R 0) B.fine q)‖) ≤
      ‖τ‖ * κ * BlockAverages.localNorm S R B w z := by
    have c1 := ComplexDifferences.finsetLpNorm_const_mul_le (P := 2) (by norm_num)
      (BlockAverages.plaquettesOver S {z} 0)
      (fun q => w 0 q.1 * ‖BlockAverages.linearizedCurl (R 0) B.fine q‖) (a := ‖τ‖ * κ) hc0
    refine le_trans (CellSources.finsetLpNorm_le_of_le (by norm_num)
      (fun q _ => mul_nonneg (LevelRecursion.scaleWeight_pos hL p θ 0 q.1).le (norm_nonneg _)) fun q hq => ?_)
      (c1.trans (mul_le_mul_of_nonneg_left (CellNormBounds.finsetLpNorm_curl_le_localNorm hL S z R B w) hc0))
    rw [norm_smul, ComplexifiedQuaternions.norm_ofQuat]
    refine hpt q.1 _ (norm_nonneg _) ?_
    have hcz : BlockAverages.enclosingCell q.1 = z := Finset.mem_singleton.1 (Finset.mem_filter.1 hq).2
    rw [hcz, BlockLines.cellSupDist_self]
    omega
  linarith
end Weights
section Span
structure CellHypotheses (S : Finset F.Cell) (z : F.Cell) (R : F.FieldChain) (C₀ s y : ℝ) : Prop where
  small : CellNormBounds.SmallParameter F.blockSide y
  const_pos : 0 < C₀
  scale_pos : 0 < s
  const_mul_scale_le : C₀ * s ≤ y
  near : ComplexLevels.ContoursNearUnit R (BlockAverages.cellBall S z 1) C₀ s
  defect_le : LevelRecursion.finsetLpNorm 2 (ComplexCells.lowerBonds (BlockAverages.cellBall S z 1))
    (fun x => ‖BlockAverages.ofUnit (BlockAverages.referenceDefect R x.1 x.2) - 1‖) ≤ y
  plaquette_le : ∀ q ∈ BlockAverages.plaquettesOver S {z} 0,
    ‖BlockAverages.ofUnit (ComplexPlaquettes.basePlaquetteHolonomy (R 0) q) - 1‖ ≤
      C₀ * s / ((F.blockSide : ℝ) ^ F.top) ^ 2
  level_le : ∀ W : BlockAverages.ComplexChainChart F,
    Real.sqrt (Real.sqrt (∑ b ∈ BlockAverages.innerBonds (BlockAverages.cellBall S z 1) 0,
      ‖ComplexLevels.levelDeviation R W 0 b.1 b.2‖ ^ 4)) ≤ 2 * y →
    (∀ j, j + 1 < F.top → Real.sqrt (∑ c ∈ BlockAverages.innerBonds (BlockAverages.cellBall S z 1) (j + 1),
      ‖ComplexLevels.levelSource W j c.1 c.2 - 1‖ ^ 2) ≤ 2 * y) →
    ∀ j, j < F.top → Real.sqrt (Real.sqrt (∑ b ∈ BlockAverages.innerBonds (BlockAverages.cellBall S z 1) j,
      ‖ComplexLevels.levelDeviation R W j b.1 b.2‖ ^ 4)) ≤ 4 * (2 * y)
theorem sum_add_smul_single {E : Type} [AddCommGroup E] [Module ℂ E] (t : Fin k → ℂ) (τ : ℂ) (l₀ : Fin k)
    (v : Fin k → E) :
    ∑ l, (t + τ • (Pi.single l₀ 1 : Fin k → ℂ)) l • v l = ∑ l, t l • v l + τ • v l₀ := by
  classical
  simp only [Pi.add_apply, Pi.smul_apply, add_smul, Finset.sum_add_distrib, Pi.single_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
theorem source_sub_single (U : BlockAverages.ChainChart F) (A : Fin k → BlockAverages.ChainChart F)
    (t : Fin k → ℂ) (τ : ℂ) (l₀ : Fin k) :
    (∀ x i, CellSources.baseSource (spanChart U A (t + τ • (Pi.single l₀ 1 : Fin k → ℂ))) x i -
        CellSources.baseSource (spanChart U A t) x i =
      τ • ComplexifiedQuaternions.ofQuat ((A l₀).fine x i : ℍ[ℝ])) ∧
    (∀ x, CellSources.upperSource (spanChart U A (t + τ • (Pi.single l₀ 1 : Fin k → ℂ))) x -
        CellSources.upperSource (spanChart U A t) x =
      τ • ComplexifiedQuaternions.ofQuat ((A l₀).coarse x.1 x.2.1 x.2.2 : ℍ[ℝ])) := by
  constructor
  · intro x i
    rw [baseSource_spanChart, baseSource_spanChart, sum_add_smul_single]
    abel
  · intro x
    rw [upperSource_spanChart, upperSource_spanChart, sum_add_smul_single]
    abel
theorem covariantCurl_sourceDiff_single (R : F.GaugeField 0) (q : F.Site 0 × Fin 4 × Fin 4)
    (U : BlockAverages.ChainChart F) (A : Fin k → BlockAverages.ChainChart F) (t : Fin k → ℂ) (τ : ℂ)
    (l₀ : Fin k) :
    ComplexPlaquettes.covariantCurl R q
        (CellBounds.baseSourceDiff (spanChart U A t) (spanChart U A (t + τ • (Pi.single l₀ 1 : Fin k → ℂ)))) =
      τ • ComplexifiedQuaternions.ofQuat (BlockAverages.linearizedCurl R (A l₀).fine q) := by
  have e : CellBounds.baseSourceDiff (spanChart U A t)
      (spanChart U A (t + τ • (Pi.single l₀ 1 : Fin k → ℂ))) = τ • ofQuatForm (A l₀) := by
    funext x i
    exact (source_sub_single U A t τ l₀).1 x i
  rw [e, covariantCurl_smul, covariantCurl_ofQuatForm]
set_option maxHeartbeats 1000000 in
theorem norm_second_diff_complexCellTerms_le (hamb : BlockAverages.IsAdmissibleAmbient F)
    (hodd : Odd F.blockSide) (h2 : 2 ≤ F.blockSide) (a : ℝ) {S : Finset F.Cell} {z : F.Cell}
    {R : F.FieldChain} (V : F.GaugeField F.top) {C₀ s y : ℝ} (ctx : CellHypotheses S z R C₀ s y)
    (U : BlockAverages.ChainChart F) (A : Fin k → BlockAverages.ChainChart F) (t : Fin k → ℂ) (τ₁ τ₂ : ℂ)
    (l₁ l₂ : Fin k)
    (n₀ : spanLocalNorm S R U A t z ≤ y) (n₁ : spanLocalNorm S R U A (t + τ₁ • (Pi.single l₁ 1 : Fin k → ℂ)) z ≤ y)
    (n₂ : spanLocalNorm S R U A (t + τ₂ • (Pi.single l₂ 1 : Fin k → ℂ)) z ≤ y)
    (n₃ : spanLocalNorm S R U A
      (t + τ₁ • (Pi.single l₁ 1 : Fin k → ℂ) + τ₂ • (Pi.single l₂ 1 : Fin k → ℂ)) z ≤ y)
    {φ : F.Cell → ℝ} {del θ : ℝ} (hdel : 0 ≤ del)
    (hφ : ∀ y y', |φ y - φ y'| ≤ del * BlockAverages.cellSupDist y y') (hθ : |θ| ≤ 1 / 8)
    (p : F.Site 0) :
    ‖BlockAverages.complexCellTerms a S R
          (spanChart U A (t + τ₁ • (Pi.single l₁ 1 : Fin k → ℂ) + τ₂ • (Pi.single l₂ 1 : Fin k → ℂ))) V z -
        BlockAverages.complexCellTerms a S R (spanChart U A (t + τ₁ • (Pi.single l₁ 1 : Fin k → ℂ))) V z -
        BlockAverages.complexCellTerms a S R (spanChart U A (t + τ₂ • (Pi.single l₂ 1 : Fin k → ℂ))) V z +
        BlockAverages.complexCellTerms a S R (spanChart U A t) V z‖ ≤
      CellBounds.cellSecondDiffConst (HullBounds.hullFactor F.blockSide) (200000 * (F.blockSide : ℝ) ^ 2)
          (1 / (2 * (200000 * (F.blockSide : ℝ) ^ 2))) a *
        ((3 * (‖τ₁‖ * (Real.exp (del - φ z) * ((F.blockSide : ℝ) ^ F.top) ^ (-θ)) *
            BlockAverages.localNorm S R (A l₁) (BlockAverages.classWeight F φ θ p) z)) *
          (3 * (‖τ₂‖ * (Real.exp (del + φ z) * ((F.blockSide : ℝ) ^ F.top) ^ θ) *
            BlockAverages.localNorm S R (A l₂)
              (BlockAverages.invertedWeights (BlockAverages.classWeight F φ θ p)) z))) := by
  have hpar := sourceParallelogram_spanChart U A (t₀ := t) (t₁ := t + τ₁ • (Pi.single l₁ 1 : Fin k → ℂ))
    (t₂ := t + τ₂ • (Pi.single l₂ 1 : Fin k → ℂ))
    (t₃ := t + τ₁ • (Pi.single l₁ 1 : Fin k → ℂ) + τ₂ • (Pi.single l₂ 1 : Fin k → ℂ)) (by abel)
  have hb := CellNormBounds.norm_complexCellTerms_second_diff_le hamb hodd h2 a V hpar ctx.small ctx.const_pos
    ctx.scale_pos ctx.const_mul_scale_le ctx.near ctx.defect_le ctx.plaquette_le
    (sourceBounds_spanChart hodd R U A _ n₀) (sourceBounds_spanChart hodd R U A _ n₁)
    (sourceBounds_spanChart hodd R U A _ n₂) (sourceBounds_spanChart hodd R U A _ n₃) ctx.level_le hθ p
  refine hb.trans ?_
  have hw0 : ∀ j x, 0 ≤ BlockAverages.classWeight F φ θ p j x := fun j x => by
    have := WeightedAverages.Chains.scaleRadius_pos (F := F) hodd.pos j p x
    simp only [BlockAverages.classWeight]
    positivity
  have hw0' : ∀ j x, 0 ≤ BlockAverages.invertedWeights (BlockAverages.classWeight F φ θ p) j x :=
    fun j x => inv_nonneg.2 (hw0 j x)
  have d₁ := weighted_diff_le (S := S) (z := z) hodd R (A l₁) τ₁ (w := BlockAverages.classWeight F φ θ p)
    (κ := Real.exp (del - φ z) * ((F.blockSide : ℝ) ^ F.top) ^ (-θ)) p (θ := θ) (by positivity) hw0
    (fun j x hx => (scaleWeight_le_classWeight (S := S) hodd hdel hφ θ p z x hx).1)
  have d₂ := weighted_diff_le (S := S) (z := z) hodd R (A l₂) τ₂
    (w := BlockAverages.invertedWeights (BlockAverages.classWeight F φ θ p))
    (κ := Real.exp (del + φ z) * ((F.blockSide : ℝ) ^ F.top) ^ θ) p (θ := -θ) (by positivity) hw0'
    (fun j x hx => (scaleWeight_le_classWeight (S := S) hodd hdel hφ θ p z x hx).2)
  obtain ⟨u₁, m₁⟩ := source_sub_single U A t τ₁ l₁
  obtain ⟨u₂, m₂⟩ := source_sub_single U A t τ₂ l₂
  simp only [u₁, u₂, m₁, m₂, covariantCurl_sourceDiff_single]
  have hK : 0 ≤ CellBounds.cellSecondDiffConst (HullBounds.hullFactor F.blockSide)
      (200000 * (F.blockSide : ℝ) ^ 2) (1 / (2 * (200000 * (F.blockSide : ℝ) ^ 2))) a := by
    have hF := ComplexCells.hullFactor_nonneg F.blockSide
    unfold CellBounds.cellSecondDiffConst CellBounds.secondDiffConst
    positivity
  refine mul_le_mul_of_nonneg_left ?_ hK
  refine mul_le_mul d₁ d₂ ?_ ?_
  · exact add_nonneg (add_nonneg (LevelRecursion.finsetLpNorm_nonneg _ _ _)
      (LevelRecursion.finsetLpNorm_nonneg _ _ _)) (LevelRecursion.finsetLpNorm_nonneg _ _ _)
  · exact (add_nonneg (add_nonneg (LevelRecursion.finsetLpNorm_nonneg _ _ _)
      (LevelRecursion.finsetLpNorm_nonneg _ _ _)) (LevelRecursion.finsetLpNorm_nonneg _ _ _)).trans d₁
end Span
end YangMills.Construction.CellSpans
end
