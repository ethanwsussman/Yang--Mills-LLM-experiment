import YangMills.Construction.PeriodicOperators.ClassesOfTheCopiesOfIndexSets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.CopyQuotients
variable (V : PeriodicData) (l : Fin 2)
theorem intoCopy_snd (x : (V.copy l).Carrier) : V.intoCopy l x.1.2 = x :=
  Subtype.ext (Prod.ext x.2.symm rfl)
theorem quotOfCopy_quotToCopy (c : V.UnitQuot) : V.quotOfCopy l (V.quotToCopy l c) = c :=
  Quot.inductionOn c fun _ => rfl
theorem quotToCopy_mkQuot_snd (x : (V.copy l).Carrier) :
    V.quotToCopy l (V.mkQuot 1 x.1.2) = (V.copy l).mkQuot 1 x :=
  congrArg ((V.copy l).mkQuot 1) (intoCopy_snd V l x)
theorem quotToCopy_quotOfCopy (c' : (V.copy l).UnitQuot) :
    V.quotToCopy l (V.quotOfCopy l c') = c' :=
  Quot.inductionOn c' fun x => quotToCopy_mkQuot_snd V l x
theorem mkQuot_copy_eq_iff (c : V.UnitQuot) (x : (V.copy l).Carrier) :
    (V.copy l).mkQuot 1 x = V.quotToCopy l c ↔ V.mkQuot 1 x.1.2 = c := by
  constructor
  · intro e
    have := congrArg (V.quotOfCopy l) e
    rw [quotOfCopy_quotToCopy] at this
    exact this
  · rintro rfl
    exact (quotToCopy_mkQuot_snd V l x).symm
theorem quotWeight_quotToCopy_eq (c : V.UnitQuot) :
    (V.copy l).quotWeight 1 (V.quotToCopy l c) = V.quotWeight 1 c := by
  refine congrArg Classical.epsilon (funext fun w => propext ⟨fun h i hi => ?_, fun h x hx => ?_⟩)
  · exact h (V.intoCopy l i) ((mkQuot_copy_eq_iff V l c _).2 hi)
  · exact h x.1.2 ((mkQuot_copy_eq_iff V l c x).1 hx)
theorem claim_holds : Claim := fun V _ =>
  { mkQuot_copy_iff := fun l c x => mkQuot_copy_eq_iff (V l) l c x
    existsUnique_quotToCopy := fun l c' =>
      ⟨(V l).quotOfCopy l c', quotToCopy_quotOfCopy (V l) l c', fun c hc => by
        rw [← hc, quotOfCopy_quotToCopy]⟩
    quotWeight_quotToCopy := fun l c => quotWeight_quotToCopy_eq (V l) l c }
end YangMills.Construction.PeriodicOperators.CopyQuotients
end
