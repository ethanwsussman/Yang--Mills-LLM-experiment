import YangMills.Construction.ColdChainAtEveryLevel.FirstOrderOfTheCriticalChainAtAFlatTopProof
import YangMills.Construction.ColdChainAtEveryLevel.FormNearItsMainPartProof
import YangMills.Construction.ColdChainAtEveryLevel.ChainCoordinatesMovedAndCriticalFormForm
import YangMills.Construction.ColdChainAtEveryLevel.ResponseAtAFlatTop
import Mathlib
set_option autoImplicit false

noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def referenceHessianFlatTopStatement : Prop :=
  ∀ a : ℝ, 0 < a → ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L →
    ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
      IsOrthantRegular S m →
      ∀ U A : ChainChart F,
        referenceSecondDeriv a S (referenceFieldChain S flatTopField) flatTopField U A =
          responseBilinear a S (referenceFieldChain S flatTopField) U A
end YangMills.Construction.BlockAverages
end

noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
namespace FlatTopHessian
variable {F : BlockFrame}
theorem eq_zero_of_le_mul_small {x M c : ℝ} (hc : 0 < c) (hx : 0 ≤ x)
    (h : ∀ s, 0 < s → s ≤ c → x ≤ M * s) : x = 0 := by
  by_contra hne
  have hx0 : 0 < x := lt_of_le_of_ne hx (Ne.symm hne)
  have hM : 0 < M := by
    by_contra hM
    have := h c hc le_rfl
    nlinarith
  have h1 := h (min c (x / (2 * M))) (lt_min hc (by positivity)) (min_le_left _ _)
  have h2 : M * min c (x / (2 * M)) ≤ M * (x / (2 * M)) :=
    mul_le_mul_of_nonneg_left (min_le_right _ _) hM.le
  have h3 : M * (x / (2 * M)) = x / 2 := by field_simp
  linarith
theorem isCold_flatTopField (S : Finset F.Cell) {s : ℝ} (hs : 0 < s) :
    IsCold S F.top s (flatTopField : F.GaugeField F.top) := by apply _root_.YangMills.Construction.BlockAverages.CriticalChainFirstOrder.flatTopField_isCold <;> assumption
theorem plaquettesOver_self (hodd : Odd F.blockSide) (S : Finset F.Cell) :
    plaquettesOver S S 0 = innerPlaquettes S 0 := by apply _root_.YangMills.Construction.SecondDifferences.plaquettesOver_self <;> assumption
theorem bondsOver_self (hodd : Odd F.blockSide) (S : Finset F.Cell) (j : ℕ) :
    bondsOver S S j = innerBonds S j := by apply _root_.YangMills.SharedProofs.p14425 <;> assumption
end FlatTopHessian
open FlatTopHessian in
theorem referenceHessianFlatTopStatement_holds (hFM : hessianNearPrincipalStatement) :
    referenceHessianFlatTopStatement := by
  intro a ha
  obtain ⟨L₀, hFM⟩ := hFM a 0 (1 / 8) ha le_rfl (by norm_num) (by norm_num) le_rfl
  refine ⟨L₀, fun L hodd hL => ?_⟩
  obtain ⟨c, C, hc, hC, hFM⟩ := hFM L hodd hL
  intro F m S hFL hamb hm hreg U A
  have hoddF : Odd F.blockSide := by rw [hFL]; exact hodd
  have hmain : principalHessian a S (referenceFieldChain S flatTopField) U A =
      responseBilinear a S (referenceFieldChain S flatTopField) U A := by
    unfold principalHessian responseBilinear
    rw [plaquettesOver_self hoddF, bondsOver_self hoddF]
    simp only [bondsOver_self hoddF]
  rw [← hmain, ← sub_eq_zero]
  refine abs_eq_zero.1 (eq_zero_of_le_mul_small (M := C *
      _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S flatTopField) U (classWeight F (fun _ => 0) 0 0) *
      _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S flatTopField) A
        (invertedWeights (classWeight F (fun _ => 0) 0 0)))
    hc (abs_nonneg _) fun s hs hsc => ?_)
  have := hFM F m S hFL hamb hm hreg s flatTopField hs hsc (isCold_flatTopField S hs) (fun _ => 0) 0 0
    (Or.inl rfl) (fun y y' => by simp) U A
  calc _ ≤ _ := this
    _ = _ := by ring
end YangMills.Construction.BlockAverages
end
