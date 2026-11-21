import YangMills.Construction.SeparatedSequences.ClassFormsAgreeWithDefiningForms
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.SeparatedClasses.ClassOneFormsOfParameters
open SingleSequence SingleSequence.SequenceData
theorem ext_of_bondEnds_eq (s : SequenceData) {b b' : s.data.BareBond}
    (h : s.bondEnds b = s.bondEnds b') : b = b' := by
  have hs : b.1.source = b'.1.source := Subtype.ext (congrArg Prod.fst h)
  have ht : b.1.target = b'.1.target := Subtype.ext (congrArg Prod.snd h)
  exact Subtype.ext (PeriodicLattice.Bond.ext hs ht)
theorem bondRel_iff_eq (s : SequenceData) (b b' : s.data.BareBond) :
    OneFormData.BondRel s.oneFormData.toOneFormData s.classOneForms id b b' ↔ b = b' := by
  constructor
  · intro h
    exact ext_of_bondEnds_eq s h
  · rintro rfl
    rfl
theorem eq_of_agreeAlong (s : SequenceData) {f f' : s.data.BareBond → ℝ}
    (h : AgreeAlong (OneFormData.BondRel s.oneFormData.toOneFormData s.classOneForms id) f f') :
    f = f' :=
  funext fun b => h b b ((bondRel_iff_eq s b b).2 rfl)
theorem statement_holds : Statement := by
  intro s
  refine ⟨⟨fun b => ⟨b, (bondRel_iff_eq s b b).2 rfl, fun b' h => ((bondRel_iff_eq s b b').1 h).symm⟩,
    fun b' => ⟨b', (bondRel_iff_eq s b' b').2 rfl, fun b h => (bondRel_iff_eq s b b').1 h⟩⟩,
    ⟨fun f hf => ⟨f, hf, fun b b' h => ?_⟩, fun f hf => ⟨f, hf, fun b b' h => ?_⟩⟩, ?_⟩
  · rw [(bondRel_iff_eq s b b').1 h]
  · rw [(bondRel_iff_eq s b b').1 h]
  · intro f _ g _ f' _ g' _ hf hg
    obtain rfl := eq_of_agreeAlong s hf
    obtain rfl := eq_of_agreeAlong s hg
    rfl
end YangMills.Construction.SeparatedClasses.ClassOneFormsOfParameters
