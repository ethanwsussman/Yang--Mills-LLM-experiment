import YangMills.Construction.PeriodicOperators.CopiesAndUnionsOfPeriodicIndexSets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators
open BlockJets
private theorem quotToCopy_surjective (V : PeriodicData) (l : Fin 2) :
    Function.Surjective (V.quotToCopy l) := by
  intro c
  induction c using Quot.ind with
  | mk x =>
    refine ⟨V.mkQuot 1 x.1.2, ?_⟩
    have e : V.intoCopy l x.1.2 = x := Subtype.ext (Prod.ext x.2.symm rfl)
    exact congrArg ((V.copy l).mkQuot 1) e
private theorem isPeriodic_copy (V : PeriodicData) (l : Fin 2) (h : IsPeriodic V) :
    IsPeriodic (V.copy l) where
  translate_zero := fun x => Subtype.ext (Prod.ext x.2.symm (h.translate_zero x.1.2))
  translate_add := fun a b x => Subtype.ext (Prod.ext rfl (h.translate_add a b x.1.2))
  free := fun a x e =>
    h.free a x.1.2 (congrArg (fun y : (V.copy l).Carrier => y.1.2) e)
  finite_quot :=
    have := h.finite_quot
    Finite.of_surjective (V.quotToCopy l) (quotToCopy_surjective V l)
  pos_translate := fun a x => h.pos_translate a x.1.2
  finite_components := h.finite_components
  componentOf_translate := fun a x => h.componentOf_translate a x.1.2
  weight_pos := h.weight_pos
theorem CopiesUnions.claim_holds : CopiesUnions.Claim := by
  unfold CopiesUnions.Claim CopiesAndSigmaPeriodic
  refine ⟨fun V l h => isPeriodic_copy V l h, fun V V' x y e => ?_,
    fun J h => IsPeriodic.sigma h⟩
  have e₁ : (0 : Fin 2) = 1 := x.2.symm.trans (e.trans y.2)
  exact absurd e₁ (by decide)
end YangMills.Construction.PeriodicOperators
end
