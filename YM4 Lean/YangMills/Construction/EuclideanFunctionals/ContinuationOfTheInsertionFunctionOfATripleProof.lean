import YangMills.Construction.RotationInvariance.FunctionalOnTuplesOfRealFunctionsProof
import YangMills.Construction.EuclideanFunctionals.BracketOfTheParametrixProof
import YangMills.Construction.EuclideanFunctionals.MatrixElementBetweenTwoOperatorsOfTheSemigroupOfTheCone
import YangMills.Construction.EuclideanFunctionals.OneInsertionAsAnOperator
import Mathlib
set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.TripleContinuationProof
open MotionMulRules (shiftFn shiftFree)
open SpectralPoint
def ofRealFn (k : R4 → ℝ) : R4 → ℂ := fun y => (k y : ℂ)
theorem supp_ofRealFn (k : R4 → ℝ) : supp (ofRealFn k) = supp k := by apply _root_.YangMills.Construction.EuclideanFunctionals.RealTuples.supp_ofReal <;> assumption
theorem ofRealFn_mem_C1c {k : R4 → ℝ} (hk : k ∈ C1c ℝ) :
    ofRealFn k ∈ C1c ℂ := by apply _root_.YangMills.Construction.EuclideanFunctionals.RealTuples.ofReal_mem_C1c <;> assumption
theorem nonneg_sharpNorm (c : SharpScale) (f : R4 → ℝ) : 0 ≤ c.sharpNorm f :=
  (Real.iSup_nonneg fun _ => norm_nonneg _ : 0 ≤ TestFunctions.uniformNorm f).trans (le_max_left _ _)
theorem abs_time_le_norm (v : R4) : |v 3| ≤ TorusMetric.euclidNormVec v := by apply _root_.YangMills.Construction.EuclideanFunctionals.ParametrixBracket.abs_apply_three_le <;> assumption
theorem half_rpow_neg_eq {η : ℝ} (hη : 0 < η) (p : ℝ) :
    (η / 2) ^ (-p) = (2 : ℝ) ^ p * η ^ (-p) := by
  rw [Real.div_rpow hη.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) p]
  field_simp
theorem reconClass_shiftFree (hRules : MotionMulRules.MotionMulTupleRules)
    (hCone : ConeSemigroup.statement) {m : SharpScale} {S : ConnFamily}
    (σ : EuclidFunctionalWithRecon m S) (hcone : σ.ConeCondition) {η : ℝ}
    {A : FreeSep} (hA : A ∈ finCombIn {y | η / 4 < y 3}) (v : R4) (hv : 0 ≤ v 3) :
    reconClass σ (shiftFree (v + (-(η / 4)) • timeVec) A) =
      σ.coneOp (ofRealPoint v) (reconClass σ (pullDown (η / 4) A)) := by
  obtain ⟨hTr, -, -, -, -, -, -, -, -, hAbove, -, -, -, -⟩ := hRules
  obtain ⟨-, -, -, -, hReal, -⟩ := hCone σ hcone
  have hPull : pullDown (η / 4) A ∈ finCombIn upperHalf := by
    have h := (hAbove ((-(η / 4)) • timeVec) (η / 4) A hA).1
    have hset : {x : R4 | η / 4 + ((-(η / 4)) • timeVec : R4) 3 < x 3} = upperHalf := by
      ext x
      simp [upperHalf, PeriodicLattice.coordVec]
    rw [hset] at h
    exact h
  have hE := (hReal v hv).2.2.2 ⟨_, hPull⟩
  have hClass : reconClass σ (pullDown (η / 4) A) =
      σ.recon.cls ⟨_, hPull⟩ := by
    unfold reconClass readClass
    rw [dif_pos hPull]
  rw [hClass, hE]
  have hComp := (hTr v ((-(η / 4)) • timeVec) A).1
  change reconClass σ _ = readClass σ.recon.cls
    (shiftFree v (shiftFree ((-(η / 4)) • timeVec) A))
  rw [hComp]
  rfl
theorem extensionExists_holds (hOperator : OneInsertionOperator.statement)
    (hSandwich : ConeSandwich.Holds)
    (hForm : InsertionForm.InsertionFormTheorem)
    (hRules : MotionMulRules.MotionMulTupleRules)
    (hCone : ConeSemigroup.statement) : TripleContinuation.ExtensionExists := by
  intro m S σ hcone p C c hI η F k A hT
  obtain ⟨hpos, hle, hkmem, hksupp, hF, hA⟩ := hT
  have hkc := ofRealFn_mem_C1c hkmem
  have hslab : supp (ofRealFn k) ⊆ {x | |x 3| < η / 8} := by
    rw [supp_ofRealFn]
    intro z hz
    have h₁ : TorusMetric.euclidNormVec z ≤ 1 / 2 * c * η := hksupp hz
    have h₂ := abs_time_le_norm z
    have h₃ : c * η < 1 / 8 * η := mul_lt_mul_of_pos_right hI.fraction_lt_eighth hpos
    change |z 3| < η / 8
    nlinarith
  have hb : 0 ≤ C * (η / 2) ^ (-p) * m.sharpNorm k :=
    mul_nonneg (mul_nonneg hI.nonneg_constant (Real.rpow_nonneg (by positivity) _))
      (nonneg_sharpNorm m k)
  have hEighth : η / 2 / 4 = η / 8 := by ring
  have hBound : OneInsertionOperator.InsertionBounded σ (η / 8) (ofRealFn k)
      (C * (η / 2) ^ (-p) * m.sharpNorm k) := by
    intro F' hF' A' hA'
    have h := hI.le_bound (η / 2) (by positivity) (by linarith) 0
      (by simpa using (by positivity : 0 ≤ η / 2 / 8)) k hkmem
      (fun z hz => by
        have h₁ : TorusMetric.euclidNormVec z ≤ 1 / 2 * c * η := hksupp hz
        change TorusMetric.euclidNormVec (z - 0) ≤ c * (η / 2)
        rw [sub_zero]
        linarith)
      F' (by rw [hEighth]; exact hF') A' (by rw [hEighth]; exact hA')
    rw [hEighth] at h
    exact h
  obtain ⟨-, -, -, -, -, hNorm, hMatrix⟩ :=
    hOperator m S σ (η / 8) (ofRealFn k) _ (by positivity) hkc hslab hb hBound
  set B := OneInsertionOperator.insertionOp σ (η / 8) (ofRealFn k) with hB
  set ΦF := reconClass σ (pullDown (η / 4) F) with hΦF
  set ΦA := reconClass σ (pullDown (η / 4) A) with hΦA
  obtain ⟨⟨-, hClosure, -, -⟩, -, hWBound, hCont, hHol⟩ := hSandwich σ hcone η hpos hle B ΦF ΦA
  refine ⟨σ.coneSandwich η B ΦF ΦA, hClosure, hCont, hHol, ?_, ?_⟩
  · intro x hx
    have hQuarter : 0 < η / 4 := by positivity
    obtain ⟨-, -, hTranslations, -⟩ := hForm m S σ (η / 4) hQuarter F hF A hA
    obtain ⟨-, hF₁, hA₁, hEq⟩ := hTranslations x (η / 8) (by positivity) (by linarith)
      (ofRealFn k) ⟨hkc, hslab⟩
    change _ = insertion S F (shiftFn x (ofRealFn k)) A
    rw [hEq, ← hMatrix _ hF₁ _ hA₁]
    have hTr := hRules.1
    have hPulled : ∀ (y : R4) (G : FreeSep), pullDown (η / 8) (shiftFree y G) =
        shiftFree ((-(η / 8)) • timeVec + y) G := fun y G => (hTr _ y G).1
    rw [hPulled, hPulled]
    have hv : (0 : ℝ) ≤ ((η / 8) • timeVec - x : R4) 3 := by
      have := (abs_le.1 hx).2
      simp [PeriodicLattice.coordVec]
      linarith
    have hw : (0 : ℝ) ≤ ((η / 8) • timeVec - timeFlip x : R4) 3 := by
      have := (abs_le.1 hx).1
      simp [timeFlip_apply, PeriodicLattice.coordVec]
      linarith
    have hVecA : (-(η / 8)) • timeVec + -x = ((η / 8) • timeVec - x) + (-(η / 4)) • timeVec := by
      module
    have hVecF : (-(η / 8)) • timeVec + -timeFlip x =
        ((η / 8) • timeVec - timeFlip x) + (-(η / 4)) • timeVec := by
      module
    rw [hVecA, hVecF, reconClass_shiftFree hRules hCone σ hcone hA _ hv,
      reconClass_shiftFree hRules hCone σ hcone hF _ hw]
    obtain ⟨-, -, hAdj, -⟩ := hCone σ hcone
    have hMargin : 0 ≤ coneMargin (ofRealPoint ((η / 8) • timeVec - timeFlip x)) := by
      obtain ⟨-, -, -, -, hReal, -⟩ := hCone σ hcone
      exact (hReal _ hw).2.1
    have hStar := (hAdj _ hMargin).2.2
    have hConj : reflectConj (ofRealPoint ((η / 8) • timeVec - timeFlip x)) =
        timeEighthPoint η + ofRealPoint x := by
      funext μ
      fin_cases μ <;>
        simp [reflectConj, ofRealPoint, spatialComplex, timeEighthPoint,
          timeFlip_apply, PeriodicLattice.coordVec, Fin.snoc]
      have h₈ : (starRingEnd ℂ) (8 : ℂ) = 8 := Complex.conj_ofNat 8
      have h₂ : (starRingEnd ℂ) (2 : ℂ) = 2 := Complex.conj_ofNat 2
      rw [h₈, h₂]
      ring
    have hMinus : ofRealPoint ((η / 8) • timeVec - x) =
        timeEighthPoint η - ofRealPoint x := by
      funext μ
      simp [ofRealPoint, timeEighthPoint]
    rw [hConj] at hStar
    rw [hMinus, ← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
      hStar]
    rfl
  · intro z hz
    have h := (hWBound z hz).2.2
    have hN : ‖B‖ * ‖ΦF‖ * ‖ΦA‖ ≤ C * (η / 2) ^ (-p) * m.sharpNorm k * ‖ΦF‖ * ‖ΦA‖ := by
      gcongr
    calc ‖σ.coneSandwich η B ΦF ΦA z‖
        ≤ C * (η / 2) ^ (-p) * m.sharpNorm k * ‖ΦF‖ * ‖ΦA‖ := h.trans hN
      _ = (2 : ℝ) ^ p * C * η ^ (-p) * m.sharpNorm k * heightNorm σ (η / 4) F *
            heightNorm σ (η / 4) A := by
        rw [half_rpow_neg_eq hpos]
        change _ * _ * heightNorm σ (η / 4) F * heightNorm σ (η / 4) A = _
        ring
end YangMills.Construction.EuclideanFunctionals.TripleContinuationProof
