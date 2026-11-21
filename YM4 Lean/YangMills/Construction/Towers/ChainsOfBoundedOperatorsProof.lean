import YangMills.Construction.Towers.BoundOfTheChainsOfLocalKernels
import YangMills.Construction.Towers.ChainsOfBoundedOperators
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open OperatorCalculus Tower.UnitLatticeL2 Tower.AbelianFieldDensity OneLoopNotation
namespace Tower.LocalFamilies.LoopSums
variable {J : Type}
theorem matrixEntry_comp (hE : MatrixEntryProperties J)
    (A B : BddOp (IndexL2 J)) (i' i : J) :
    matrixEntry (A.comp B) i' i = ∑' k, matrixEntry A i' k * matrixEntry B k i :=
  ((hE A).2 (B (basisVec i)) i').2
theorem traceAt_eq_tsum_originIndex (pos : J → InfiniteLattice.AmbientSpace)
    (h : {i | pos i = 0}.Finite) (T : BddOp (IndexL2 J)) :
    traceAt pos T 0 = ∑' o : OriginIndex pos, matrixEntry T o.1 o.1 := by
  have hfin : Finite (OriginIndex pos) := h
  rw [tsum_eq_finsum (Set.toFinite _)]
  exact (finsum_set_coe_eq_finsum_mem (s := {i | pos i = 0}) (f := fun i => matrixEntry T i i)).symm
theorem loopSumsAsTraces_of_loopTermsBound (h : LoopTermsBound) : LoopSumsAsTraces := by
  intro c m hc J pos hL hE s hs
  obtain ⟨M, -, hM⟩ := h c m hc
  obtain ⟨hB₁, hB₂, hB₃⟩ := hM J pos hL s hs
  have hfin := (hL.fibre_bounded 0).1
  refine ⟨?_, ?_, ?_⟩
  · intro S₀ S₁ X A hA h₀ h₁ hX
    have hF : Summable (loopTermsOne pos (matrixEntry S₀) (matrixEntry X) (matrixEntry S₁)) :=
      (hB₁ (matrixEntry S₀) (matrixEntry S₁) (matrixEntry X) A hA h₀ h₁ hX).1.of_norm
    rw [traceAt_eq_tsum_originIndex pos hfin]
    unfold loopSumOne
    rw [hF.tsum_prod]
    refine tsum_congr fun o => ?_
    have k₁ := hF.prod_factor o
    rw [k₁.tsum_prod]
    simp only [matrixEntry_comp hE, loopTermsOne, mul_assoc, tsum_mul_left]
  · intro S₀ S₁ S₂ X Y A A' hA hA' h₀ h₁ h₂ hX hY
    have hF : Summable (loopTermsTwo pos (matrixEntry S₀) (matrixEntry X) (matrixEntry S₁)
        (matrixEntry Y) (matrixEntry S₂)) :=
      (hB₂ (matrixEntry S₀) (matrixEntry S₁) (matrixEntry S₂) (matrixEntry X) (matrixEntry Y)
        A A' hA hA' h₀ h₁ h₂ hX hY).1.of_norm
    rw [traceAt_eq_tsum_originIndex pos hfin]
    unfold loopSumTwo
    rw [hF.tsum_prod]
    refine tsum_congr fun o => ?_
    have k₁ := hF.prod_factor o
    rw [k₁.tsum_prod]
    have e₁ : ∀ a, ∑' q, loopTermsTwo pos (matrixEntry S₀) (matrixEntry X) (matrixEntry S₁)
        (matrixEntry Y) (matrixEntry S₂) (o, a, q) = ∑' b, ∑' d, ∑' e, loopTermsTwo pos
          (matrixEntry S₀) (matrixEntry X) (matrixEntry S₁) (matrixEntry Y) (matrixEntry S₂)
          (o, a, b, d, e) := fun a => by
      have k₂ := k₁.prod_factor a
      rw [k₂.tsum_prod]
      refine tsum_congr fun b => ?_
      have k₃ := k₂.prod_factor b
      rw [k₃.tsum_prod]
    rw [tsum_congr e₁]
    simp only [matrixEntry_comp hE, loopTermsTwo, mul_assoc, tsum_mul_left]
  · intro S₀ S₁ S₂ S₃ X Y W A A' A'' hA hA' hA'' h₀ h₁ h₂ h₃ hX hY hW
    have hF : Summable (loopTermsThree pos (matrixEntry S₀) (matrixEntry X) (matrixEntry S₁)
        (matrixEntry Y) (matrixEntry S₂) (matrixEntry W) (matrixEntry S₃)) :=
      (hB₃ (matrixEntry S₀) (matrixEntry S₁) (matrixEntry S₂) (matrixEntry S₃) (matrixEntry X)
        (matrixEntry Y) (matrixEntry W) A A' A'' hA hA' hA'' h₀ h₁ h₂ h₃ hX hY hW).1.of_norm
    rw [traceAt_eq_tsum_originIndex pos hfin]
    unfold loopSumThree
    rw [hF.tsum_prod]
    refine tsum_congr fun o => ?_
    have k₁ := hF.prod_factor o
    rw [k₁.tsum_prod]
    have e₁ : ∀ a, ∑' q, loopTermsThree pos (matrixEntry S₀) (matrixEntry X) (matrixEntry S₁)
        (matrixEntry Y) (matrixEntry S₂) (matrixEntry W) (matrixEntry S₃) (o, a, q) =
          ∑' b, ∑' d, ∑' e, ∑' f, ∑' g, loopTermsThree pos (matrixEntry S₀) (matrixEntry X)
            (matrixEntry S₁) (matrixEntry Y) (matrixEntry S₂) (matrixEntry W) (matrixEntry S₃)
            (o, a, b, d, e, f, g) := fun a => by
      have k₂ := k₁.prod_factor a
      rw [k₂.tsum_prod]
      refine tsum_congr fun b => ?_
      have k₃ := k₂.prod_factor b
      rw [k₃.tsum_prod]
      refine tsum_congr fun d => ?_
      have k₄ := k₃.prod_factor d
      rw [k₄.tsum_prod]
      refine tsum_congr fun e => ?_
      have k₅ := k₄.prod_factor e
      rw [k₅.tsum_prod]
    rw [tsum_congr e₁]
    simp only [matrixEntry_comp hE, loopTermsThree, mul_assoc, tsum_mul_left]
end Tower.LocalFamilies.LoopSums
end YangMills.Construction
end
