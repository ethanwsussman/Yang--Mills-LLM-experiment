import YangMills.Construction.Continuum.MomentFunctionalsOnSymbols
import YangMills.Construction.Continuum.TensorsAboveTheMirrorAndTheirFiniteSequences
import YangMills.Construction.GrowingTori.BoundFunctionsHierarchiesAndCentredMomentsOfFourSpace
import Mathlib
set_option autoImplicit false
open scoped NNReal ComplexConjugate
noncomputable section
namespace YangMills.Construction.SymbolSequences
open TorusTransport TorusTransport.TupleVectors TorusTransport.TestFunctionOrders
open TimeAxisSymbols
open GrowingTori (diagMap)
open TorusPeriodization (euclideanMotions)
variable {D : TransportData}
theorem components_mem_sepC1Tuples (E : PeriodicSpace.Params) (X : SpaceTimeSymbol D) :
    X.1.2 ∈ PeriodicSpace.Kind.sepC1Tuples E .euclidean X.1.1 := by
  obtain ⟨-, hk, hd, hc, -⟩ := (mem_sepTuples_iff D _ X.1).mp X.2
  exact (BallTuples.mem_sepC1Tuples_euclidean_iff X.1.2).mpr
    ⟨hc, hk, fun _ _ h => hd h⟩
def momentOnSymbol {E : PeriodicSpace.Params} (Φ : ToriLimits.EuclidHierarchy E)
    (X : SpaceTimeSymbol D) : ℝ :=
  Φ.partitionMoment ⟨X.1.2, components_mem_sepC1Tuples E X⟩
theorem momentOnSymbol_unitSymbol {E : PeriodicSpace.Params}
    (Φ : ToriLimits.EuclidHierarchy E) :
    momentOnSymbol Φ (unitSymbol D) = 1 :=
  Φ.partitionMoment_zero _
theorem osForm_linComb {ι κ : Type*} [Fintype ι] [Fintype κ] (m : SpaceTimeSymbol D → ℝ) (c : ι → ℂ)
    (X : ι → PosSymbol D) (c' : κ → ℂ) (Y : κ → PosSymbol D) :
    osForm m (linComb c X) (linComb c' Y) =
      ∑ b, ∑ b', conj (c b) * c' b' * ((m (reflectAppend (X b) (Y b')) : ℝ) : ℂ) := by
  have key : ∀ P Q : PosSymbol D,
      momentLinExtend m
        (appendBilin
          (linExtendSymbolMap reflectSymbol (posSymbolSpanInclusion D (basisVec P)))
          (posSymbolSpanInclusion D (basisVec Q))) =
        ((m (reflectAppend P Q) : ℝ) : ℂ) := fun P Q => by
    have hc : conjCoeffs (basisVec P) = basisVec P := by
      simp [conjCoeffs, TupleVectors.basisVec]
    have h := osForm_basisVec m P Q
    rwa [osForm, hc] at h
  rw [osForm, conjCoeffs_linComb]
  simp only [linComb, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, key,
    smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_)
  ring
def symbolTensor (X : PosSymbol D) : OrderedTestFun X.1.1 :=
  CentredTensorMoments.realTupleTensor X.1.2
theorem symbolTensor_mem (E : PeriodicSpace.Params) (X : PosSymbol D) :
    symbolTensor X ∈ ReflectionSpaces.sepTensorsUpper E X.1.1 := by
  obtain ⟨⟨q, f⟩, hX⟩ := X
  cases q with
  | zero => exact Submodule.mem_top
  | succ q =>
    have hs := components_mem_sepC1Tuples E (inclusionMap D (Set.subset_univ _) ⟨⟨q + 1, f⟩, hX⟩)
    obtain ⟨-, -, -, -, ho⟩ := (mem_sepTuples_iff D _ _).mp hX
    exact show symbolTensor ⟨⟨q + 1, f⟩, hX⟩ ∈ ToriLimits.sepTensorSpanOn E (q + 1)
        (ReflectionSpaces.upperHalfOpen : Set (Fin 4 → ℝ)) from by
      refine Submodule.subset_span ⟨f, ⟨hs, fun i => ?_⟩, rfl⟩
      rw [BallTuples.supportQ_euclidean]
      exact ho i
def symbolSequence (E : PeriodicSpace.Params) (X : PosSymbol D) :
    ReflectionSpaces.finiteUpperSequences E :=
  ⟨Pi.single X.1.1 (symbolTensor X), fun q => by
      by_cases h : q = X.1.1
      · subst h
        rw [Pi.single_eq_same]
        exact symbolTensor_mem E X
      · rw [Pi.single_eq_of_ne h]
        exact Submodule.zero_mem _,
    X.1.1 + 1, fun q hq => Pi.single_eq_of_ne (by omega) _⟩
theorem symbolSequence_self (E : PeriodicSpace.Params) (X : PosSymbol D) :
    (symbolSequence E X).1 X.1.1 = symbolTensor X :=
  Pi.single_eq_same _ _
theorem symbolSequence_of_ne (E : PeriodicSpace.Params) (X : PosSymbol D) {q : ℕ}
    (h : q ≠ X.1.1) : (symbolSequence E X).1 q = 0 :=
  Pi.single_eq_of_ne h _
def spanSequence (E : PeriodicSpace.Params) :
    PosSymbolSpan D →ₗ[ℂ] ReflectionSpaces.finiteUpperSequences E :=
  linExtend (symbolSequence E)
theorem spanSequence_basisVec (E : PeriodicSpace.Params) (X : PosSymbol D) :
    spanSequence E (basisVec X) = symbolSequence E X :=
  linExtend_basisVec _ X
def rotateFamily (w : timeAxisStabilizer) (F : TestFamily) : TestFamily :=
  ReflectionSpaces.composeFamily (fun _ => diagMap (w.1⁻¹ : hyperoctahedral).1) F
end YangMills.Construction.SymbolSequences
end
