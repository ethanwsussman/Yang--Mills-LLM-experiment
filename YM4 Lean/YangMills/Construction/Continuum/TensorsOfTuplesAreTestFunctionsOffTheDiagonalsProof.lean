import YangMills.Construction.Continuum.FirstFactsOnTheTestSpaces
import YangMills.Construction.Continuum.TensorsOfTuplesAreTestFunctionsOffTheDiagonals
import Mathlib
set_option autoImplicit false
open scoped ContDiff ENNReal
noncomputable section
namespace YangMills.Construction.TestSpaces.OffDiagonalTensors
variable {n : ℕ}
theorem tensorProdComplex_mem_smoothCompactSupp (hF : Elementary.BasicProperties) (hn : 1 ≤ n)
    (X : SepTupleOfCard n) (hX : HasSmoothComponents Set.univ X.1) :
    tensorProdComplex X.1 ∈
      (smoothCompactSupp (distinctLocus n) : Set (PointTuple n → ℂ)) := by
  obtain ⟨-, hb, -, hd, -⟩ := hF n hn
  obtain ⟨hs, hc, ht⟩ := ((hd Set.univ isOpen_univ X.1 X.2).2 hX).1
  have e : tensorProdComplex X.1 = Complex.ofRealCLM ∘ tensorProd X.1 := rfl
  have hV : Elementary.setPower (Set.univ : Set (Fin 4 → ℝ)) ∩
      TestFunctions.injectiveTuples (Fin 4 → ℝ) n = distinctLocus n := hb.2.2.2.2.1.symm
  rw [hV] at ht
  refine ⟨?_, ?_, ?_⟩
  · rw [e]; exact Complex.ofRealCLM.contDiff.comp hs
  · rw [e]; exact hc.comp_left (by simp)
  · rw [e]; exact (tsupport_comp_subset (by simp) _).trans ht
theorem statement_of_basicProperties (hF : Elementary.BasicProperties) : Statement := fun n hn =>
  ⟨fun X hX => tensorProdComplex_mem_smoothCompactSupp hF hn X hX, fun φ hφ p =>
    ((hF n hn).2.2.1 (distinctLocus n) (hF n hn).2.1.1 φ hφ).2.2.1 p⟩
end YangMills.Construction.TestSpaces.OffDiagonalTensors
end
