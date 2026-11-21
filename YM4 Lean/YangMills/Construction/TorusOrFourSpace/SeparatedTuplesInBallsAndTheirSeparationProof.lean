import YangMills.Construction.TorusOrFourSpace.ClassesOfTuplesAndTheSeparation
import YangMills.Construction.TorusOrFourSpace.QuotientMapCompactSetsAndFunctionsOfClassC1
import YangMills.Construction.TorusOrFourSpace.SeparatedTuplesInBallsAndTheirSeparation
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.SeparatedTupleFacts
open Kind
private theorem eval_eq_zero_of_component_eq_zero (P : Params) (X : Kind) {n : ℕ}
    {S : Set (FnTuple P X n)} {L : S → ℝ} (hL : IsMultilinearOn P X S L) {g : FnTuple P X n}
    (hg : g ∈ S) {j : Fin n} (hzero : g j = 0) : L ⟨g, hg⟩ = 0 := by
  have hScalar : (0 : ℝ) • g j = g j := by rw [hzero, smul_zero]
  have hUpd : Function.update g j ((0 : ℝ) • g j) = g := by
    rw [hScalar, Function.update_eq_self]
  have hIn : Function.update g j ((0 : ℝ) • g j) ∈ S := hUpd.symm ▸ hg
  have hHom := (hL j ⟨g, hg⟩ ⟨g, hg⟩ fun _ _ => rfl).2 0 hIn
  calc
    L ⟨g, hg⟩ = L ⟨_, hIn⟩ := congrArg L (Subtype.ext hUpd.symm)
    _ = 0 * L ⟨g, hg⟩ := hHom
    _ = 0 := zero_mul _
theorem separatedTupleBasics_holds (hTup : TupleClasses.Statement)
    (hQuot : Kind.QuotientCompactC1.Claim) : SeparatedTupleBasics := by
  intro P X n hn g hg
  have hLip : g ∈ sepLipTuples P X n :=
    ⟨fun j => ((hQuot P X).2.2.2.2 (g j) (hg.1 j) (hg.2.1 j)).2.2.2.2.1, hg.2⟩
  obtain ⟨-, hPos, hInf, hBall, -⟩ := hTup P X n (by omega)
  obtain ⟨hEquiv, hZero⟩ := hInf hn g hLip
  refine ⟨hBall g hg, ⟨hPos hn g hLip, hEquiv⟩, fun hgap => ?_⟩
  obtain ⟨j, hj⟩ := hZero (hEquiv.1 hgap)
  have hzero : g j = 0 := funext hj
  exact ⟨⟨j, hzero⟩, fun r _ hg' L hL => eval_eq_zero_of_component_eq_zero P X hL hg' hzero⟩
end YangMills.Construction.PeriodicSpace.SeparatedTupleFacts
