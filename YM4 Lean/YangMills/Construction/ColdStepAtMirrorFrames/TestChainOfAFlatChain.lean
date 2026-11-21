import YangMills.Construction.ColdStepAtMirrorFrames.BlockMeansOfFormsOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame}
theorem exists_read_offset (hL : Odd F.blockSide) {j : ℕ} (y : F.Site (j + 1)) (k l : Fin 4) (h : Fin 4 → ℤ)
    (hh : h ∈ centredCube F.blockSide) (m m' : ℕ) (hm : m ∈ Finset.range F.blockSide)
    (hm' : m' ∈ Finset.range F.blockSide) :
    ∃ v : Fin 4 → ℤ, BlockAverages.refineSite y + siteOfCoords j h + axisOffset j k (m : ℤ) + axisOffset j l (m' : ℤ) =
        BlockAverages.refineSite y + siteOfCoords j v ∧
      ∀ i, |v i| ≤ 3 * (F.blockSide : ℤ) := by
  obtain ⟨a, ha⟩ := id hL
  have hb := (mem_centredCube_iff ha h).1 hh
  have h1 := Finset.mem_range.1 hm
  have h2 := Finset.mem_range.1 hm'
  refine ⟨h + Pi.single k (m : ℤ) + Pi.single l (m' : ℤ), ?_, ?_⟩
  · unfold axisOffset
    rw [siteOfCoords_add, siteOfCoords_add]
    abel
  · intro i
    have q := hb i
    have e1 : |(Pi.single k (m : ℤ) : Fin 4 → ℤ) i| ≤ (F.blockSide : ℤ) := by
      by_cases hk : i = k
      · subst hk
        simp only [Pi.single_eq_same, abs_le]
        constructor <;> omega
      · simp only [Pi.single_eq_of_ne hk, abs_zero]
        omega
    have e2 : |(Pi.single l (m' : ℤ) : Fin 4 → ℤ) i| ≤ (F.blockSide : ℤ) := by
      by_cases hk : i = l
      · subst hk
        simp only [Pi.single_eq_same, abs_le]
        constructor <;> omega
      · simp only [Pi.single_eq_of_ne hk, abs_zero]
        omega
    simp only [Pi.add_apply]
    rw [abs_le] at e1 e2 ⊢
    constructor <;> omega
def weightedChain (W : (j : ℕ) → F.Site j → ℝ) (B : FormChain F) (j : ℕ) : LevelForm F j :=
  fun x i => W j x * B j x i
def testForm (W : (j : ℕ) → F.Site j → ℝ) (B : FormChain F) : (j : ℕ) → LevelForm F j
  | 0 => fun x i => W 0 x * B 0 x i
  | j + 1 => fun y i => lineAverage (testForm W B j) y i - W (j + 1) y * chainMisfit B j y i
def testDefect (W : (j : ℕ) → F.Site j → ℝ) (B : FormChain F) (j : ℕ) : LevelForm F j :=
  testForm W B j - weightedChain W B j
def weightCommutator (W : (j : ℕ) → F.Site j → ℝ) (B : FormChain F) (j : ℕ) : LevelForm F (j + 1) :=
  fun y i => lineAverage (weightedChain W B j) y i - W (j + 1) y * lineAverage (B j) y i
theorem testDefect_zero (W : (j : ℕ) → F.Site j → ℝ) (B : FormChain F) : testDefect W B 0 = 0 := by
  funext x i
  simp [testDefect, testForm, weightedChain]
theorem testDefect_succ (W : (j : ℕ) → F.Site j → ℝ) (B : FormChain F) (j : ℕ) :
    testDefect W B (j + 1) = lineAverage (testDefect W B j) + weightCommutator W B j := by
  funext y i
  have e : lineAverage (testDefect W B j) =
      lineAverage (testForm W B j) - lineAverage (weightedChain W B j) := by
    unfold testDefect
    exact lineAverage_sub _ _
  rw [Pi.add_apply, Pi.add_apply, e]
  simp only [testDefect, Pi.sub_apply, testForm, weightedChain, weightCommutator, chainMisfit]
  ring
end ColdStepAtMirrorFrames
end YangMills.Construction
end
