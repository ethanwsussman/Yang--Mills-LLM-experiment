import YangMills.Construction.ClusterExpansionOfAStep.PlaquettesUnderGaugesAndMoves
import YangMills.Construction.ColdChainAtEveryLevel.CompositeMeanOfTheGeneratorsProof
import YangMills.Construction.ColdStepAtMirrorFrames.FlatChainOfNoFlux
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
private theorem expUnit_zero : expUnit (0 : imaginaryQuaternions) = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
private theorem pathHolonomy_of_trivial {F : BlockFrame} {j : ℕ} (A : F.GaugeField j)
    (hA : ∀ x i, A x i = 1) :
    ∀ (γ : List PathStep) (x : F.Site j), pathHolonomy A x γ = 1
  | [], _ => rfl
  | s :: γ, x => by
    rw [pathHolonomy, pathHolonomy_of_trivial A hA γ]
    unfold linkValue
    split_ifs <;> simp [hA]
private theorem card_centredCube (n : ℕ) (hn : Odd n) :
    ((centredCube n).card : ℝ) = (n : ℝ) ^ 4 := by apply _root_.YangMills.Construction.BlockAverages.GeneratorMeans.card_centredCube_real <;> assumption
private theorem quaternionUnitPart_one : quaternionUnitPart (1 : Quaternion ℝ) = 1 := by
  have hex : ∃ u : UnitQuaternion, (1 : Quaternion ℝ) ≠ 0 ∧
      (1 : Quaternion ℝ) = ‖(1 : Quaternion ℝ)‖ • (u : Quaternion ℝ) :=
    ⟨1, one_ne_zero, by simp⟩
  unfold quaternionUnitPart
  rw [dif_pos hex]
  have hs := hex.choose_spec.2
  have hnorm : ‖(1 : Quaternion ℝ)‖ = 1 := by simp
  apply Subtype.ext
  have heq : (1 : Quaternion ℝ) = (hex.choose : Quaternion ℝ) :=
    hs.trans (by rw [show ‖(1 : Quaternion ℝ)‖ • (hex.choose : Quaternion ℝ) = (1 : ℝ) • (hex.choose : Quaternion ℝ) from
      congrArg (· • (hex.choose : Quaternion ℝ)) hnorm, one_smul])
  exact heq.symm
theorem constantCurvatureChain_flat_of_zeroFlux : ConstantCurvatureChainFlatOfZeroFlux := by
  intro F A μ ν j hodd
  induction j with
  | zero =>
    intro x i
    show constantCurvatureField F A μ ν 0 x i = 1
    unfold constantCurvatureField
    dsimp only
    have e : 2 * Real.pi * ((0 : ℕ) : ℝ) / (finestSide F μ : ℝ) ^ 2 = 0 := by
      simp
    simp only [e, neg_zero, zero_mul, mul_zero, zero_smul, expUnit_zero]
    split_ifs <;> rfl
  | succ j ih =>
    intro x i
    show quaternionUnitPart (contourAverage (constantCurvatureChain F A μ ν 0 j) (x, i)) = 1
    have hside : (F.blockSide : ℝ) ≠ 0 := by
      have := hodd.pos
      positivity
    have havg : contourAverage (constantCurvatureChain F A μ ν 0 j) (x, i) = 1 := by
      unfold contourAverage
      dsimp only
      simp only [pathHolonomy_of_trivial _ ih, OneMemClass.coe_one, Finset.sum_const, Finset.card_univ,
        Fintype.card_perm, Fintype.card_fin]
      rw [smul_smul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
      have hfact : Nat.factorial 4 = 24 := rfl
      rw [hfact]
      have : 1 / (24 * (F.blockSide : ℝ) ^ 4) * (((centredCube F.blockSide).card * 24 : ℕ) : ℝ) = 1 := by
        push_cast
        rw [card_centredCube F.blockSide hodd]
        field_simp
      rw [this, one_smul]
    rw [havg, quaternionUnitPart_one]
end YangMills.Construction.ColdStepAtMirrorFrames
end
