import YangMills.Construction.Continuum.AxiomsOfOsterwalderAndSchrader
import Reconstruction.Continuum.OrderedTimes
import YangMills.Construction.Coordinates.HolomorphyInCoordinates
import YangMills.Construction.HilbertSpaces.CalculusOfAProjectionValuedMeasureWithBoundedFunctions
import YangMills.Construction.HilbertSpaces.FormsOperatorsAndFamiliesInAHilbertSpace
import YangMills.Construction.MinkowskiSpace.MinkowskiFormConesLorentzGroupAndEuclideanPoints
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Matrix Set
open scoped ComplexConjugate ENNReal InnerProductSpace Topology
noncomputable section
namespace YangMills.Construction
namespace WightmanTheory
open MinkowskiSpace ProjectionMeasures PVMCalculus FormsOperators OneLoopNotation
def asOnePointFn {F : Type*} (f : (Fin 4 → ℝ) → F) : TestSpaces.PointTuple 1 → F := fun x => f (x 0)
def schwartzR4 : Set ((Fin 4 → ℝ) → ℂ) :=
  {f | asOnePointFn f ∈ TestSpaces.schwartzSet 1}
abbrev TestFn : Type := schwartzR4
def schwartzNorm (k : ℕ) (f : (Fin 4 → ℝ) → ℂ) : ℝ≥0∞ :=
  TestSpaces.weightedSeminorm k (asOnePointFn f)
abbrev PoincareElt : Type := restrictedPoincare
theorem one_mem_restrictedLorentz : (1 : RealMat4) ∈ restrictedLorentz := by
  have h1 : toComplexMatrix (1 : RealMat4) = 1 := by
    simp [toComplexMatrix, Matrix.map_one]
  refine ⟨?_, by simp, ?_⟩
  · intro z z'
    rw [h1]
    simp
  · rw [h1]
    simp [minkowskiForm, MinkowskiSpace.toComplex, timeUnit, mkTimeSpace, spaceBilin, spacePart]
def pureTranslation (a : RealVec4) : PoincareElt :=
  ⟨(a, 1), Set.mk_mem_prod (Set.mem_univ a) one_mem_restrictedLorentz⟩
def fieldWord {D : Type*} (φ : TestFn → D → D) {n : ℕ} (f : Fin n → TestFn) (Ψ : D) : D :=
  (List.ofFn f).foldr φ Ψ
variable (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
structure HermitianScalarTheory [CompleteSpace H] where
  rep : PoincareElt → UnitaryMap H H
  rep_mul : ∀ g g' g'' : PoincareElt, g''.1 = poincareMul g.1 g'.1 →
    rep g'' = rep g * rep g'
  rep_continuous : ∀ ψ : H, Continuous fun g => rep g ψ
  vacuum : H
  norm_vacuum : ‖vacuum‖ = 1
  rep_vacuum : ∀ g, rep g vacuum = vacuum
  domain : Submodule ℂ H
  dense_domain : Dense (domain : Set H)
  vacuum_mem_domain : vacuum ∈ domain
  rep_mem_domain : ∀ g, ∀ ψ ∈ domain, rep g ψ ∈ domain
  field : TestFn → domain →ₗ[ℂ] domain
  field_linear : ∀ (a b : ℂ) (f f' f'' : TestFn), f''.1 = a • f.1 + b • f'.1 →
    field f'' = a • field f + b • field f'
  field_tempered : ∀ Ψ Ψ' : domain, ∃ (k : ℕ) (c : ℝ), 0 < k ∧ 0 ≤ c ∧ ∀ f : TestFn,
    ENNReal.ofReal ‖⟪(Ψ : H), (field f Ψ' : H)⟫_ℂ‖ ≤ ENNReal.ofReal c * schwartzNorm k f.1
  field_hermitian : ∀ f : TestFn, ∃ f' : TestFn, (f'.1 = fun x => conj (f.1 x)) ∧
    ∀ Ψ Ψ' : domain, ⟪(Ψ : H), (field f Ψ' : H)⟫_ℂ = ⟪(field f' Ψ : H), (Ψ' : H)⟫_ℂ
  vacuum_cyclic : Dense (Submodule.span ℂ (Set.range fun p : Σ n : ℕ, (Fin n → TestFn) =>
    ((fieldWord (fun f Ψ => field f Ψ) p.2 ⟨vacuum, vacuum_mem_domain⟩ : domain) : H)) : Set H)
variable {H} [CompleteSpace H]
namespace HermitianScalarTheory
variable (T : HermitianScalarTheory H)
def IsPoincareCovariant : Prop :=
  ∀ (g : PoincareElt) (f : TestFn), ∃ f' : TestFn,
    asOnePointFn f'.1 = poincarePullback g.1 (asOnePointFn f.1) ∧
      ∀ Ψ : T.domain, ∃ Ψ' : T.domain, (Ψ' : H) = (T.rep g).symm Ψ ∧
        T.rep g (T.field f Ψ' : H) = (T.field f' Ψ : H)
end HermitianScalarTheory
def minkowskiPhase (a p : RealVec4) : ℂ :=
  Complex.exp (Complex.I * minkowskiForm (MinkowskiSpace.toComplex a) (MinkowskiSpace.toComplex p))
namespace HermitianScalarTheory
variable (T : HermitianScalarTheory H)
structure IsEnergyMomentumMeasure (E : FourBorelSet → BddOp H) : Prop where
  isPVM : IsPVM E
  supportedOn : IsSupportedOn E closedFutureConeBorel
  translation_eq : ∀ a : RealVec4, HasWeakIntegrals E (minkowskiPhase a)
    ((T.rep (pureTranslation a)).toContinuousLinearEquiv : H →L[ℂ] H)
def SpectrumCondition : Prop := ∃ E, T.IsEnergyMomentumMeasure E
def hamiltonianSemigroup (E : FourBorelSet → BddOp H) (t : ℝ) : BddOp H :=
  pvmIntegral E (closedFutureCone.indicator fun p => Complex.exp (-((t * p 0 : ℝ) : ℂ)))
def IsLocalField : Prop :=
  ∀ (Ψ : T.domain) (f h : TestFn),
    (∀ x ∈ tsupport f.1, ∀ y ∈ tsupport h.1, x - y ∈ spacelikeSet) →
      T.field f (T.field h Ψ) = T.field h (T.field f Ψ)
def UniqueVacuum : Prop :=
  ∀ ψ : H, (∀ a : RealVec4, T.rep (pureTranslation a) ψ = ψ) →
    ∃ c : ℂ, ψ = c • T.vacuum
def vacuumVec : T.domain := ⟨T.vacuum, T.vacuum_mem_domain⟩
def wightmanFn {n : ℕ} (f : Fin n → TestFn) : ℂ :=
  ⟪T.vacuum, ((fieldWord (fun f Ψ => T.field f Ψ) f T.vacuumVec : T.domain) : H)⟫_ℂ
end HermitianScalarTheory
def tubeTuples (m : ℕ) : Set (Fin m → ComplexVec4) := Set.univ.pi fun _ => futureTube
def coordsToTuple {m : ℕ} (z : Coordinates.ComplexCoordinates (m * 4)) : Fin m → ComplexVec4 :=
  fun k μ => z (finProdFinEquiv (k, μ))
def IsHolomorphicOnTube {m : ℕ} (w : (Fin m → ComplexVec4) → ℂ) : Prop :=
  Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) (coordsToTuple ⁻¹' tubeTuples m)
    fun z _ => w (coordsToTuple z)
def boundaryApproach {m : ℕ} (x : TestSpaces.PointTuple (m + 1)) (ε : ℝ) : Fin m → ComplexVec4 :=
  fun k => successiveDiffs (tupleToComplex x) k + ((ε : ℂ) * Complex.I) • MinkowskiSpace.toComplex timeUnit
def wickDiffs {m : ℕ} (y : TestSpaces.PointTuple (m + 1)) : Fin m → ComplexVec4 :=
  successiveDiffs (wickMapTuple (tupleToComplex y))
structure IsAnalyticContinuationData (T : HermitianScalarTheory H) (S : ConfigSpace.FlatSequence)
    (m : ℕ) (w : (Fin m → ComplexVec4) → ℂ) (q : ℕ) (c : ℝ)
    (s : TestSpaces.PointTuple (m + 1) → ℂ) : Prop where
  holomorphic : IsHolomorphicOnTube w
  continuousOn : ContinuousOn s (TestSpaces.distinctLocus (m + 1))
  growth : ∀ ζ ∈ tubeTuples m, ‖w ζ‖ ≤ c * ∏ k, (min 1 (tubeGap (ζ k)))⁻¹ ^ q
  boundary_values : ∀ f : Fin (m + 1) → TestFn,
    (∀ ε : ℝ, 0 < ε →
      Integrable fun x : TestSpaces.PointTuple (m + 1) => w (boundaryApproach x ε) * ∏ i, (f i).1 (x i)) ∧
    Tendsto (fun ε : ℝ => ∫ x : TestSpaces.PointTuple (m + 1),
        w (boundaryApproach x ε) * ∏ i, (f i).1 (x i))
      (𝓝[>] 0) (𝓝 (T.wightmanFn f))
  euclidean_values : ∀ (ς : Equiv.Perm (Fin (m + 1))) (x : TestSpaces.PointTuple (m + 1)),
    TestSpaces.rotatePermute 1 ς x ∈ TestSpaces.increasingTimes (m + 1) →
      s x = w (wickDiffs (TestSpaces.rotatePermute 1 ς x))
  schwinger_values : ∀ φ : ConfigSpace.schwartzFlatOffDiagonal (m + 1),
    φ.1 ∈ TestSpaces.smoothCompactSupp (TestSpaces.distinctLocus (m + 1)) →
      Integrable (fun x : TestSpaces.PointTuple (m + 1) => s x * φ.1 x) ∧
        S.atSucc m φ = ∫ x : TestSpaces.PointTuple (m + 1), s x * φ.1 x
namespace HermitianScalarTheory
variable (T : HermitianScalarTheory H)
def IsSchwingerSequence (S : ConfigSpace.FlatSequence) : Prop :=
  ConfigSpace.IsCLMSequence S ∧
    ∀ m : ℕ, ∃ (w : (Fin m → ComplexVec4) → ℂ) (q : ℕ) (c : ℝ)
      (s : TestSpaces.PointTuple (m + 1) → ℂ), IsAnalyticContinuationData T S m w q c s
end HermitianScalarTheory
end WightmanTheory
end YangMills.Construction
end
