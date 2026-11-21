import YangMills.Construction.BoundsOnEverySide.LimitsAlongStatesFreeOfAWindow
import YangMills.Construction.Continuum.SubTuplesIsometriesAndTheConjugateOnFourSpace
import YangMills.Construction.LimitsAlongPeriodicGibbsStates.TheLetterSForALimitAlongPeriodicGibbsStates
import YangMills.Construction.ReflectionsAndOneInsertion.ReflectionsObservablesAndCellData
import YangMills.Construction.Torus.LipschitzClassesAtASeparationAndARadiusAndSourceDiscsOfTheLetter
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace YangMills.Construction.BoundsOnEverySide
structure FreeMomentConstants where
  M : ℝ
  one_le_M : 1 ≤ M
  cStar : ℕ → ℝ → ℝ → ℝ≥0∞
  cTr : ℝ
def partitionsBlocksGeTwo {m : ℕ} (A : Finset (Fin m)) : Finset (SetPartition.Partitions A) :=
  Finset.univ.filter fun π => ∀ J ∈ π.parts, 2 ≤ J.card
namespace FreeMomentConstants
variable (c : FreeMomentConstants)
def blockProductSum {m : ℕ} (A : Finset (Fin m)) (d R : ℝ) : ℝ≥0∞ :=
  ∑ π ∈ partitionsBlocksGeTwo A, ∏ J ∈ π.parts, c.cStar J.card d R
def momentBound (m : ℕ) (d R : ℝ) : ℝ≥0∞ :=
  ∑ I : Finset (Fin m), ENNReal.ofReal (c.cTr * (1 + R) ^ 4) ^ I.card * c.blockProductSum Iᶜ d R
end FreeMomentConstants
namespace TranslatedTuples
abbrev IsLipAt (s : Conventions.StandingParameters) (M : ℝ) (hM : 1 ≤ M) {m : ℕ} (d R : ℝ)
    (f : Fin m → AmbientPoints.Pt s .euclidean → ℝ) : Prop :=
  f ∈ LipschitzClasses.lipTuplesSepRadius s M hM m d R .euclidean
variable {s : Conventions.StandingParameters} (c : FreeMomentConstants)
abbrev TupleLipAt (X : R4TupleForms.FinTuple s) (d R : ℝ) : Prop :=
  IsLipAt s c.M c.one_le_M d R (Continuum.SeparatedFourTuples.tupleComponents X)
def sharpNormProd (X : R4TupleForms.FinTuple s) : ℝ :=
  ∏ i, TestFunctions.sharpNormR4 c.M (Continuum.SeparatedFourTuples.tupleComponents X i)
def shiftedSharpNormSum (X : R4TupleForms.FinTuple s) (v : Fin 4 → ℝ) : ℝ :=
  ∑ i, TestFunctions.sharpNormR4 c.M
      (Continuum.SeparatedFourTuples.translateFn v (Continuum.SeparatedFourTuples.tupleComponents X i) -
        Continuum.SeparatedFourTuples.tupleComponents X i) *
    ∏ l ∈ Finset.univ.erase i,
      TestFunctions.sharpNormR4 c.M (Continuum.SeparatedFourTuples.tupleComponents X l)
variable {K : ℕ → ℕ}
structure MomentHypotheses
    (ρ ν : ∀ j, Measure (InfiniteLattice.GaugeField (PeriodicLattice.meshSize s.L (K j : ℤ)))) :
    Prop where
  cStar_ne_top : ∀ m, 2 ≤ m → ∀ d R : ℝ, 0 < d → 0 < R → c.cStar m d R ≠ ⊤
  cumulant_le : ∀ (j m : ℕ), 2 ≤ m → ∀ d R : ℝ, 0 < d → 0 < R →
    ∀ f : Fin m → InfiniteLattice.AmbientSpace → ℝ, IsLipAt s c.M c.one_le_M d R f →
      ENNReal.ofReal
          ‖Cumulants.mixedCumulant (ρ j) fun i U => InfiniteLattice.smearedEnergy (f i) U‖ ≤
        c.cStar m d R * ENNReal.ofReal (∏ i, TestFunctions.sharpNormR4 c.M (f i))
  transfer_le : ∀ (j : ℕ) (R : ℝ), 0 < R →
    ∀ (h : InfiniteLattice.AmbientSpace → ℝ) (x : InfiniteLattice.AmbientSpace),
    TestFunctions.IsLipschitzFor TestFunctions.euclidDistR4 h →
    ReflectionPositivity.CutoffMirrors.euclidSupp h ⊆ TestFunctions.closedBallR4 x R →
      |(∫ U, InfiniteLattice.smearedEnergy h U ∂ρ j) -
          ∫ U, InfiniteLattice.smearedEnergy h U ∂ν j| ≤
        c.cTr * (1 + R) ^ 4 * TestFunctions.sharpNormR4 c.M h
structure LimitProperties
    (ρ ν : ∀ j, Measure (InfiniteLattice.GaugeField (PeriodicLattice.meshSize s.L (K j : ℤ))))
    (σ : R4TupleForms.FinTuple s → ℝ) : Prop where
  momentBound_ne_top : ∀ m, 1 ≤ m → ∀ d R : ℝ, 0 < d → 0 < R →
    c.momentBound m d R ≠ ⊤
  abs_value_le : ∀ (X : R4TupleForms.FinTuple s), 1 ≤ Continuum.SeparatedFourTuples.tupleLength X →
    ∀ d R : ℝ, 0 < d → 0 < R → TupleLipAt c X d R → ∀ j,
      |StateLimits.pairedValue K ρ ν j X| ≤
        (c.momentBound (Continuum.SeparatedFourTuples.tupleLength X) d R).toReal * sharpNormProd c X
  abs_limit_le : ∀ (X : R4TupleForms.FinTuple s), 1 ≤ Continuum.SeparatedFourTuples.tupleLength X →
    ∀ d R : ℝ, 0 < d → 0 < R → TupleLipAt c X d R →
      |σ X| ≤
        (c.momentBound (Continuum.SeparatedFourTuples.tupleLength X) d R).toReal * sharpNormProd c X
  abs_shift_sub_le : ∀ (X : R4TupleForms.FinTuple s),
    1 ≤ Continuum.SeparatedFourTuples.tupleLength X →
    ∀ d R : ℝ, 0 < d → 0 < R → TupleLipAt c X d R →
    ∀ (j : ℕ) (v : Fin 4 → ℝ), TorusMetric.euclidNormVec v ≤ min (d / 2) 1 →
      |StateLimits.pairedValue K ρ ν j (Continuum.SeparatedFourTuples.translateSep v X) -
          StateLimits.pairedValue K ρ ν j X| ≤
        (c.momentBound (Continuum.SeparatedFourTuples.tupleLength X) (d / 2) (R + 1)).toReal *
          shiftedSharpNormSum c X v
  shift_bound_tendsto : ∀ (X : R4TupleForms.FinTuple s),
    1 ≤ Continuum.SeparatedFourTuples.tupleLength X →
    ∀ d R : ℝ, 0 < d → 0 < R → TupleLipAt c X d R →
      Tendsto (fun v : Fin 4 → ℝ =>
        (c.momentBound (Continuum.SeparatedFourTuples.tupleLength X) (d / 2) (R + 1)).toReal *
          shiftedSharpNormSum c X v) (𝓝 0) (𝓝 0)
  tendsto_shifted : ∀ (Ξ : SeparatedTuples.FormalSpan) (v : ℕ → Fin 4 → ℝ),
    Tendsto v atTop (𝓝 0) →
    Tendsto (fun j => R4TupleForms.realSpanLift (StateLimits.pairedValue K ρ ν j)
        (SeparatedTuples.pushSpan (SeparatedTuples.translate (v j)) Ξ))
      atTop (𝓝 (R4TupleForms.realSpanLift σ Ξ))
  symm : Continuum.SeparatedFourTuples.IsSymm σ
  multilin : Continuum.SeparatedFourTuples.IsMultilin σ
  translate_invariant : ∀ (y : Fin 4 → ℝ) (Ξ : SeparatedTuples.FormalSpan),
    R4TupleForms.realSpanLift σ (SeparatedTuples.pushSpan (SeparatedTuples.translate y) Ξ) =
      R4TupleForms.realSpanLift σ Ξ
  connected : PeriodicGibbsLimit.HasMultilinearConnected σ
  partition_expansion : ∀ (m : ℕ), 1 ≤ m → ∀ f : AmbientPoints.separatedTuples s .euclidean m,
    σ (AmbientPoints.toAllSeparated f) = ∑ π : SetPartition.PartitionsFin m, ∏ J ∈ π.parts,
      AmbientPoints.connectedOf σ J.card (AmbientPoints.restrictSeparated f J)
  reflection_positive : ∃ hσ : AmbientPoints.IsTupleFunctional σ,
    HilbertSpaceBasics.IsPosSemidef
      (ReflectionPositivity.TupleForm.reflectionForm (R4TupleForms.toTupleFunctional σ hσ)) ∧
    HilbertSpaceBasics.IsHermitianForm
      (ReflectionPositivity.TupleForm.reflectionForm (R4TupleForms.toTupleFunctional σ hσ)) ∧
    (∀ F F' : ReflectionPositivity.TupleForm.PositiveSpan,
      ‖ReflectionPositivity.TupleForm.reflectionForm (R4TupleForms.toTupleFunctional σ hσ) F F'‖ ≤
        ReflectionsAndOneInsertion.spanClassNorm (R4TupleForms.toTupleFunctional σ hσ) F *
          ReflectionsAndOneInsertion.spanClassNorm (R4TupleForms.toTupleFunctional σ hσ) F') ∧
    (∀ F F' : ReflectionPositivity.TupleForm.PositiveSpan,
      ReflectionsAndOneInsertion.spanClassNorm (R4TupleForms.toTupleFunctional σ hσ) (F + F') ≤
        ReflectionsAndOneInsertion.spanClassNorm (R4TupleForms.toTupleFunctional σ hσ) F +
          ReflectionsAndOneInsertion.spanClassNorm (R4TupleForms.toTupleFunctional σ hσ) F') ∧
    ∀ (u : ℝ), 0 ≤ u → ∀ F : ReflectionPositivity.TupleForm.PositiveSpan,
      ∃ G : ReflectionPositivity.TupleForm.PositiveSpan,
        G.1 = SeparatedTuples.pushSpan
          (SeparatedTuples.translate (u • ReflectionsAndOneInsertion.timeUnitVec)) F.1 ∧
        ReflectionsAndOneInsertion.spanClassNorm (R4TupleForms.toTupleFunctional σ hσ) G ≤
          ReflectionsAndOneInsertion.spanClassNorm (R4TupleForms.toTupleFunctional σ hσ) F
def Statement : Prop :=
  ∀ (s : Conventions.StandingParameters) (c : FreeMomentConstants) (K : ℕ → ℕ) (β : ℕ → ℝ)
    (ρ ν : ∀ j, Measure (InfiniteLattice.GaugeField (PeriodicLattice.meshSize s.L (K j : ℤ))))
    (σ : R4TupleForms.FinTuple s → ℝ),
    IsPeriodicStateLimit K β ρ ν σ → (∀ j, 0 < β j) →
    MomentHypotheses c ρ ν → LimitProperties c ρ ν σ
end TranslatedTuples
end YangMills.Construction.BoundsOnEverySide
end
