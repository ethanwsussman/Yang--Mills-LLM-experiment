import YangMills.Construction.Continuum.ConnectedFunctionsAndCentredFunctionalOfAFunctional
import YangMills.Construction.Continuum.SeparatedTuplesAsListsAndAsMaps
import YangMills.Construction.InfiniteLattice.ConnectedCorrelations
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace TestSpaces
open TupleLists
abbrev IsMultilinearSepFunctional (s : SepTuple → ℝ) : Prop :=
  IsSepFunctional s
theorem cumulantOne_eq (s : SepTuple → ℝ) (f : (Fin 4 → ℝ) → ℝ)
    (hf : f ∈ c1CompactSupp (Set.univ : Set (Fin 4 → ℝ))) :
    cumulantOne s f hf = s ⟨1, singletonSepTuple f hf⟩ :=
  cumulant_single s _
theorem ofList_sepTupleNil : ofList SeparatedTuples.SepTuple.nil = sepTupleNil := by
  rw [← toList_sepTupleNil, ofList_toList]
def centredOfCumulantsFunctional (S : (n : ℕ) → 2 ≤ n → SepTupleOfCard n → ℝ) :
    SeparatedTuples.TupleFunctional where
  toFun X := centredOfCumulants S (ofList X)
  map_nil := by rw [ofList_sepTupleNil, centredOfCumulants_nil]
def centredPartFunctional (s : SepTuple → ℝ) : SeparatedTuples.TupleFunctional :=
  centredOfCumulantsFunctional (cumulantFamily s)
theorem centredOfCumulantsFunctional_spanExtension_basisVec
    (S : (n : ℕ) → 2 ≤ n → SepTupleOfCard n → ℝ) (X : SepTuple) :
    (centredOfCumulantsFunctional S).spanExtension (SeparatedTuples.basisVec (toList X)) =
      (centredOfCumulants S X : ℂ) := by
  simp only [SeparatedTuples.TupleFunctional.spanExtension, SeparatedTuples.linearExtend_basisVec]
  exact congrArg (fun Y => ((centredOfCumulants S Y : ℝ) : ℂ)) (ofList_toList X)
theorem centredPartFunctional_spanExtension_basisVec (s : SepTuple → ℝ) (X : SepTuple) :
    (centredPartFunctional s).spanExtension (SeparatedTuples.basisVec (toList X)) =
      (centredPart s X : ℂ) :=
  centredOfCumulantsFunctional_spanExtension_basisVec _ X
end TestSpaces
namespace InfiniteLattice
theorem ursellFunction_eq_mixedCumulant {a : ℝ}
    (ρ : MeasureTheory.Measure (GaugeField a)) (n : ℕ) (f : Fin n → AmbientSpace → ℝ) :
    ursellFunction ρ n f =
      Cumulants.mixedCumulant ρ fun i U => smearedEnergy (f i) U :=
  rfl
end InfiniteLattice
end YangMills.Construction
end
