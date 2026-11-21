import Reconstruction.Predicates
import YangMills.Construction.LimitTheorem.AssertionsAtGivenConstants
import YangMills.Construction.MinkowskiSpace.ConditionsOnAFunctionalForAFieldForm
import YangMills.Construction.LimitTheorem.OsterwalderSchrader
import Reconstruction.MinkowskiSpace.BoundOnOneInsertedFieldGivesAFieldForm
import YangMills.Construction.MinkowskiSpace.MeasureOfTheTimeTranslationsAndTheVectorsTheyFix
import Reconstruction.MinkowskiSpace.WightmanTheoryOfAFunctionalWithOneBoundedField
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open ConfigSpace (FlatSequence schwartzFlatOffDiagonal)
open Filter Topology
namespace LimitTheorem
namespace ComponentWightman
open HilbertSpaceBasics (IsPosSemidef)
open SeparatedTuples ReflectionPositivity.TupleForm
open InfiniteLattice (AmbientSpace)
open TorusMetric (euclidNormVec)
open WightmanReconstruction (flatSequenceAsMaps)
open TupleLists (toList ofList ofList_toList toList_ofList)
open ComponentConditions
def WightmanFromConditionsStatement : Prop :=
  ∀ (C : ConditionConstants) (σ : TupleFunctional), 0 ≤ C.cE → 0 ≤ C.CE →
    IsPosSemidef (reflectionForm σ) →
    TestSpaces.IsSepFunctional (evalOnMap σ) →
    (∀ v : AmbientSpace, σ.IsInvariant (SeparatedTuples.translate v)) → IsO4InvariantFunctional σ → σ.IsPermInvariant →
    GrowthBound C σ → FieldFormConditions.PairingPosSemidef (evalOnMap σ) →
    FieldFormConditions.ExistsTranslationMeasure (evalOnMap σ) →
    FieldFormConditions.ExistsInsertionBound (evalOnMap σ) → ClustersAtInfinity σ →
    HasWightmanReconstruction C σ
theorem isSymmetricInvariant_of {σ : TupleFunctional}
    (ht : ∀ v, σ.IsInvariant (SeparatedTuples.translate v))
    (hr : IsO4InvariantFunctional σ) (hsym : σ.IsPermInvariant) :
    FieldFormConditions.IsSymmetricInvariant (evalOnMap σ) := by
  have hv : ∀ T', evalOnMap σ (ofList T') = σ T' := evalOnMap_ofList σ
  refine ⟨fun n _ X ς => ?_, fun r X => ?_⟩
  · have key : ∀ (Z : TestSpaces.SepTuple) (Y : TestSpaces.SepTupleOfCard Z.1)
        (τ : Equiv.Perm (Fin Z.1)),
        Y.1 = Z.2.1 ∘ τ → evalOnMap σ ⟨Z.1, Y⟩ = evalOnMap σ Z := by
      intro Z
      obtain ⟨T', rfl⟩ : ∃ T', Z = ofList T' := ⟨toList Z, (ofList_toList Z).symm⟩
      intro Y τ hY
      change evalOnMap σ ⟨T'.1.length, Y⟩ = _
      rw [← ofList_reorder T' τ Y hY, hv, hv]
      exact hsym T' τ
    exact key ⟨n, X⟩ _ ς rfl
  · exact evalOnMap_eq_of_motion ht hr r X.2 _ rfl
theorem wightmanFromConditions (hForm : InsertedFieldForm.BoundedFieldFormOfInsertionBound)
    (hGen : BoundedFieldWightman.WightmanFromBoundedFieldFunctional)
    (hSpec : TimeTranslations.MeasureAndFixedVectors)
    (hcarry : TestSpaces.SchwingerPropertiesTransfer)
    (hrp : ReflectionPositivityFromValues.Statement)
    (hTr : WightmanReconstruction.ClusteringTransfer.Statement)
    (hOne : TestSpaces.SchwingerUniqueAtEachOrder) : WightmanFromConditionsStatement := by
  intro C σ hc hC h hfun ht hr hsym hG hpos hE hB hfar T hT
  have hmaps := isSchwingerFamily_flatSequenceAsMaps hT
  have hv := evalOnMap_ofList σ
  refine ⟨osFromConditions hcarry hrp hTr hOne C σ hc hC h hfun ht hr hsym hG hfar T hT, ?_⟩
  have hsi := isSymmetricInvariant_of ht hr hsym
  obtain ⟨E, hEm⟩ := hE
  obtain ⟨p, K, hp, hK, hbd⟩ := id hB
  obtain ⟨A, hA, -⟩ := hForm _ hfun hsi hpos E hEm p K hp hK hbd
  have Hd := hGen _ hfun hsi hpos E hEm hB A hA T hT.2.1 hmaps
  obtain ⟨T', J, Tf, hseq, -, -, -, -, -, huniq⟩ := Hd.exists_theory
  have hclt : TimeTranslations.TimeClustering (evalOnMap σ) := fun X Y => by
    simp only [hv]
    refine tendsto_juxt_translate hfar _ _ ?_
    intro h0
    have := congrFun h0 TimeAxis.timeIdx
    simp [PeriodicLattice.coordVec] at this
  have hfix : BoundedFieldWightman.OnlyVacuumTimeInvariant (evalOnMap σ) E :=
    ((hSpec _ hfun hpos).2.2 E hEm hclt).2
  exact ⟨_, inferInstance, inferInstance, inferInstance, T', Hd.separable, huniq hfix,
    hseq.covariant, hseq.spectrum, hseq.localField, hseq.schwinger⟩
end ComponentWightman
end LimitTheorem
end YangMills.Construction
end
