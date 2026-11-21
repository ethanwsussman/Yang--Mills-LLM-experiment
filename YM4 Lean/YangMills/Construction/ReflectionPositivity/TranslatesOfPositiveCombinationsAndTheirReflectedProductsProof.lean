import YangMills.Construction.ReflectionPositivity.FactsOnSeparatedTuplesOfFourSpace
import YangMills.Construction.ReflectionPositivity.LatticeFormulaForTheScalarProductProof
import YangMills.Construction.ReflectionPositivity.TranslatesOfPositiveCombinationsAndTheirReflectedProducts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SeparatedTuples
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.ReflectionPositivity.TupleForm (PositiveSpan reflectConj)
namespace PositiveTranslates
theorem isOpen_upperHalfSpace : IsOpen TimeAxis.upperHalfSpace :=
  isOpen_lt continuous_const (continuous_apply _)
theorem pushSpan_translate_mem_spanIn (hA : BasicFacts.PushSpanProperties) {v : AmbientSpace}
    (hv : 0 ≤ v TimeAxis.timeIdx) {F : FormalSpan}
    (hF : F ∈ spanIn TimeAxis.upperHalfSpace) :
    pushSpan (translate v) F ∈ spanIn TimeAxis.upperHalfSpace := by
  have hr := isEuclidIsometry_translate v
  have h1 := ((hA _ _ hr hr 0 0 F).2.2.2.2.1 _ isOpen_upperHalfSpace).2
  have h2 : pushSpan (translate v) F ∈
      spanIn (translate v '' TimeAxis.upperHalfSpace) := by
    rw [← h1]
    exact Submodule.mem_map_of_mem hF
  have hO : translate v '' TimeAxis.upperHalfSpace ⊆ TimeAxis.upperHalfSpace := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : 0 < x TimeAxis.timeIdx := hx
    show 0 < (x + v) TimeAxis.timeIdx
    simpa using add_pos_of_pos_of_nonneg hx' hv
  refine Submodule.span_mono ?_ h2
  rintro _ ⟨X, rfl⟩
  exact ⟨⟨X.1, fun f hf => (X.2 f hf).trans hO⟩, rfl⟩
theorem mem_supportedIn_of_mem_support {O : Set AmbientSpace} {G : FormalSpan}
    (hG : G ∈ spanIn O) : ∀ Y ∈ G.support, Y ∈ supportedIn O := by apply _root_.YangMills.Construction.ReflectionPositivity.LatticeScalarProduct.mem_supportedIn_of_mem_support <;> assumption
theorem exists_eq_push_of_mem_support (r : AmbientSpace → AmbientSpace) (G : FormalSpan)
    {Z : SepTuple} (hZ : Z ∈ (pushSpan r G).support) : ∃ Y ∈ G.support, Z = push r Y := by apply _root_.YangMills.Construction.ReflectionPositivity.LatticeScalarProduct.exists_of_mem_support_pushSpan <;> assumption
theorem mem_support_of_mem_support_conjugation (G : FormalSpan) {Z : SepTuple}
    (hZ : Z ∈ (conjugation G).support) : Z ∈ G.support := by apply _root_.YangMills.Construction.ReflectionPositivity.LatticeScalarProduct.mem_support_of_mem_support_conjugation <;> assumption
theorem composable_push_timeReflection (hP : BasicFacts.ReflectedJuxtapositionAtHyperplane)
    {X Y : SepTuple}
    (hX : X ∈ supportedIn TimeAxis.upperHalfSpace) (hY : Y ∈ supportedIn TimeAxis.upperHalfSpace) :
    SepTuple.Composable (push TimeAxis.timeReflection X) Y := by
  have h := (hP (Mirrors.axialHyperplane TimeAxis.timeIdx 0) X Y
    (by rw [← Mirrors.upperHalfSpace_eq_positiveSide]; exact hX)
    (by rw [← Mirrors.upperHalfSpace_eq_positiveSide]; exact hY)).2
  rw [Mirrors.timeReflection_eq_axialReflection]
  exact h
theorem statement_holds (hFacts : BasicFacts.MainFacts) : Statement := by
  obtain ⟨-, -, hP, -, hA, -⟩ := hFacts
  intro F F' v hv
  have hstay := pushSpan_translate_mem_spanIn hA hv F'.2
  have hZ : ∀ Z ∈ (reflectConj F).support, ∃ X ∈ supportedIn TimeAxis.upperHalfSpace,
      Z = push TimeAxis.timeReflection X := by
    intro Z h
    obtain ⟨Y, hY, rfl⟩ := exists_eq_push_of_mem_support _ _ h
    exact ⟨Y, mem_supportedIn_of_mem_support F.2 Y
      (mem_support_of_mem_support_conjugation _ hY), rfl⟩
  refine ⟨hstay, ?_, ?_⟩
  · intro Z h Y hY
    obtain ⟨X, hX, rfl⟩ := hZ Z h
    exact composable_push_timeReflection hP hX (mem_supportedIn_of_mem_support F'.2 Y hY)
  · intro Z h Y hY
    obtain ⟨X, hX, rfl⟩ := hZ Z h
    exact composable_push_timeReflection hP hX (mem_supportedIn_of_mem_support hstay Y hY)
end PositiveTranslates
end YangMills.Construction.SeparatedTuples
end
