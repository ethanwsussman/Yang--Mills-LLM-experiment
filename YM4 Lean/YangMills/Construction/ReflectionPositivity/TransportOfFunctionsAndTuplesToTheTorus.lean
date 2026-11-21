import YangMills.Construction.PassageToTheLimit.SeparatedTuplesMultilinearFunctionalsCentredFunctionalTensors
import YangMills.Construction.ReflectionPositivity.SupportsTranslationsSeparationAndTransportOfTuples
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.LimitSpaces
theorem periodizeList_ofFn (s : Conventions.StandingParameters) {n : ℕ}
    (g : Fin n → (Fin 4 → ℝ) → ℝ) :
    periodizeList s (List.ofFn g) = List.ofFn fun i => periodizeFun s (g i) := by
  simp [periodizeList, List.map_ofFn, Function.comp_def]
namespace Periodization
section SingleFunction
variable (s : Conventions.StandingParameters)
def ProjIsometricOn (S : Set (Fin 4 → ℝ)) : Prop :=
  (∀ x ∈ S, ∀ y ∈ S,
    Ambient.periodic.pointDist s (Ambient.periodic.proj s x) (Ambient.periodic.proj s y) =
      Ambient.euclidean.pointDist s x y) ∧
  ∀ A B : Set (Fin 4 → ℝ), A ⊆ S → B ⊆ S →
    Ambient.periodic.infSetDist s (Ambient.periodic.proj s '' A) (Ambient.periodic.proj s '' B) =
      Ambient.euclidean.infSetDist s A B
def PeriodizeIsSumWithOneTerm (f : (Fin 4 → ℝ) → ℝ) : Prop :=
  ∀ y : Fin 4 → ℝ,
    periodizeFun s f (Ambient.periodic.proj s y) =
        ∑' k : Fin 4 → ℤ, f (y + TestFunctions.latticeTranslate s.side k) ∧
      {k : Fin 4 → ℤ | f (y + TestFunctions.latticeTranslate s.side k) ≠ 0}.Subsingleton
def PeriodizeIsLinear (f h : (Fin 4 → ℝ) → ℝ) : Prop :=
  ∀ a b : ℝ, periodizeFun s (a • f + b • h) =
    a • periodizeFun s f + b • periodizeFun s h
def SupportOfPeriodize (f : (Fin 4 → ℝ) → ℝ) : Prop :=
  Ambient.periodic.closedSupport s (periodizeFun s f) =
      Ambient.periodic.proj s '' Ambient.euclidean.closedSupport s f ∧
    ∀ (x : Fin 4 → ℝ) (R : ℝ), 0 < R → R < s.side / 2 →
      Ambient.euclidean.closedSupport s f ⊆ TestFunctions.closedBallR4 x R →
      Ambient.periodic.closedSupport s (periodizeFun s f) ⊆
        TestFunctions.closedBallTorus (ℓ := s.side) (Ambient.periodic.proj s x) R
def PeriodizePreservesNormsAndClasses (f : (Fin 4 → ℝ) → ℝ) : Prop :=
  (TestFunctions.IsBoundedFun f →
    TestFunctions.uniformNorm (periodizeFun s f) = TestFunctions.uniformNorm f ∧
      TestFunctions.IsBoundedFun (periodizeFun s f)) ∧
  (Ambient.euclidean.IsLip s f →
    Ambient.periodic.IsLip s (periodizeFun s f) ∧
      Ambient.periodic.lipConst s (periodizeFun s f) ≤ Ambient.euclidean.lipConst s f ∧
      ∀ M : SharpParameter,
        Ambient.periodic.normSharp s M (periodizeFun s f) ≤ Ambient.euclidean.normSharp s M f) ∧
  (f ∈ Ambient.euclidean.c1Compact s →
    periodizeFun s f ∈ Ambient.periodic.c1Compact s)
def PeriodizeCommutesWithReflect (S : Set (Fin 4 → ℝ)) (f : (Fin 4 → ℝ) → ℝ) : Prop :=
  ∀ (μ : Fin 4) (c : ℝ),
    Ambient.euclidean.SupportedWithin s (Ambient.euclidean.reflect s μ c '' S)
        (Ambient.euclidean.reflectFun s μ c f) ∧
      TestFunctions.HasDiameterLE (Ambient.euclidean.reflect s μ c '' S) (s.side / 2) ∧
      periodizeFun s (Ambient.euclidean.reflectFun s μ c f) =
        Ambient.periodic.reflectFun s μ c (periodizeFun s f)
end SingleFunction
def PeriodizeSupportedInOpenSlab (D : ReflectionPositivity.AxisMirror.MirrorData)
    (f : (Fin 4 → ℝ) → ℝ) : Prop :=
  ∀ (μ : Fin 4) (c : ℝ),
    Ambient.euclidean.closedSupport D.toStandingParameters f ⊆
        ReflectionPositivity.AxisMirror.coordSet μ (fun t => c < t ∧ t < c + D.side / 2) →
      Ambient.periodic.SupportedWithin D.toStandingParameters
        ((⟨μ, c⟩ : ReflectionPositivity.AxisMirror.CoordMirror).upperSide D .torus)
        (periodizeFun D.toStandingParameters f)
def PeriodizeSeparatedTuple (s : Conventions.StandingParameters) {n : ℕ}
    (g : Fin n → (Fin 4 → ℝ) → ℝ) : Prop :=
  Ambient.euclidean.IsSepLipTuple s univ g → FitsInTorus s (List.ofFn g) →
    Ambient.periodic.IsSepLipTuple s univ (fun i => periodizeFun s (g i)) ∧
      Ambient.periodic.listGap s (periodizeList s (List.ofFn g)) =
        Ambient.euclidean.listGap s (List.ofFn g) ∧
      (∀ J : Finset (Fin n),
        List.ofFn (Ambient.pickComponents (fun i => periodizeFun s (g i)) J) =
          periodizeList s (List.ofFn (Ambient.pickComponents g J))) ∧
      (Ambient.euclidean.IsSepC1Tuple s univ g →
        Ambient.periodic.IsSepC1Tuple s univ (fun i => periodizeFun s (g i)))
def PeriodizeReflectAppend (D : ReflectionPositivity.AxisMirror.MirrorData)
    (X Y : List ((Fin 4 → ℝ) → ℝ)) : Prop :=
  (∀ f ∈ X, Ambient.euclidean.IsCompactSubset D.toStandingParameters
    (Ambient.euclidean.closedSupport D.toStandingParameters f)) →
  (∀ f ∈ Y, Ambient.euclidean.IsCompactSubset D.toStandingParameters
    (Ambient.euclidean.closedSupport D.toStandingParameters f)) →
  ∀ (μ : Fin 4) (c : ℝ),
    FitsInTorus D.toStandingParameters
        ((⟨μ, c⟩ : ReflectionPositivity.AxisMirror.CoordMirror).reflectAppend D .euclidean X Y) →
      FitsInTorus D.toStandingParameters X ∧ FitsInTorus D.toStandingParameters Y ∧
        periodizeList D.toStandingParameters
            ((⟨μ, c⟩ : ReflectionPositivity.AxisMirror.CoordMirror).reflectAppend D .euclidean X Y) =
          (⟨μ, c⟩ : ReflectionPositivity.AxisMirror.CoordMirror).reflectAppend D .torus
            (periodizeList D.toStandingParameters X) (periodizeList D.toStandingParameters Y)
def Properties : Prop :=
  ∀ D : ReflectionPositivity.AxisMirror.MirrorData,
    (∀ (S : Set (Fin 4 → ℝ)) (f h : (Fin 4 → ℝ) → ℝ),
      TestFunctions.HasDiameterLE S (D.side / 2) →
      Ambient.euclidean.SupportedWithin D.toStandingParameters S f →
      Ambient.euclidean.SupportedWithin D.toStandingParameters S h →
        ProjIsometricOn D.toStandingParameters S ∧
        PeriodizeIsSumWithOneTerm D.toStandingParameters f ∧
        PeriodizeIsLinear D.toStandingParameters f h ∧
        SupportOfPeriodize D.toStandingParameters f ∧
        PeriodizePreservesNormsAndClasses D.toStandingParameters f ∧
        PeriodizeCommutesWithReflect D.toStandingParameters S f ∧
        PeriodizeSupportedInOpenSlab D f) ∧
    (∀ (n : ℕ) (g : Fin n → (Fin 4 → ℝ) → ℝ), PeriodizeSeparatedTuple D.toStandingParameters g) ∧
    ∀ X Y : List ((Fin 4 → ℝ) → ℝ), PeriodizeReflectAppend D X Y
end Periodization
end YangMills.Construction.LimitSpaces
