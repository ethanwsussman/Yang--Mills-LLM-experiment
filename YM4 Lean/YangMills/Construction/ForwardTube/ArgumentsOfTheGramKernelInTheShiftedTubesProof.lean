import YangMills.Construction.ForwardTube.ArgumentsOfTheGramKernelInTheShiftedTubes
import YangMills.Construction.ForwardTube.ArgumentsOfTheGramKernelProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ForwardTube.GramArgsInShiftedTubes
theorem mem_image_add_timeTranslate {A : Set (ℂ × ℂ)} {w : ℂ × ℂ} {η : ℝ}
    (hw : w - timeTranslate (η / 2) ∈ A) :
    w ∈ (fun u => timeTranslate (η / 2) + u) '' A :=
  ⟨_, hw, add_sub_cancel _ _⟩
theorem tubeStar_mem_forwardTube {v : ℂ × ℂ} (hv : v ∈ forwardTube) :
    tubeStar v ∈ forwardTube := by apply _root_.YangMills.Construction.ForwardTube.GramKernelArgs.tubeStar_mem <;> assumption
theorem add_mem_forwardTube {u v : ℂ × ℂ} (hu : u ∈ forwardTube) (hv : v ∈ forwardTube) :
    u + v ∈ forwardTube := by apply _root_.YangMills.Construction.ForwardTube.GramKernelArgs.add_mem_forwardTube <;> assumption
theorem tubeStar_sub_timeTranslate (v : ℂ × ℂ) (s : ℝ) :
    tubeStar v - timeTranslate s = tubeStar (v - timeTranslate s) := by
  ext <;> simp [tubeStar, timeTranslate]
theorem tubeStar_add_sub_timeTranslate_half (a b : ℂ × ℂ) (η : ℝ) :
    tubeStar a + b - timeTranslate (η / 2) =
      tubeStar (a - timeTranslate (η / 4)) + (b - timeTranslate (η / 4)) := by
  rw [← tubeStar_sub_timeTranslate]
  have hsplit : timeTranslate (η / 2) = timeTranslate (η / 4) + timeTranslate (η / 4) := by
    ext <;> simp [timeTranslate]
    ring
  rw [hsplit]
  abel
theorem holds : Holds := by
  intro n m η _ _ _ x hx y hy
  obtain ⟨hx₀, hxs⟩ := hx
  obtain ⟨hy₀, hys⟩ := hy
  refine Set.mem_univ_pi.2 fun k => mem_image_add_timeTranslate ?_
  have hk : (k : ℕ) < n + m - 1 := k.2
  simp only [gramKernelArgs]
  split_ifs with h h'
  · rw [tubeStar_sub_timeTranslate]
    refine tubeStar_mem_forwardTube ?_
    have hidx : n - 1 - (k : ℕ) = n - 2 - (k : ℕ) + 1 := by omega
    simp only [hidx]
    exact hxs (n - 2 - k) (by omega)
  · rw [tubeStar_add_sub_timeTranslate_half]
    exact add_mem_forwardTube (tubeStar_mem_forwardTube (hx₀ (by omega))) (hy₀ (by omega))
  · have hidx : (k : ℕ) + 1 - n = (k : ℕ) - n + 1 := by omega
    simp only [hidx]
    exact hys (k - n) (by omega)
end YangMills.Construction.ForwardTube.GramArgsInShiftedTubes
end
