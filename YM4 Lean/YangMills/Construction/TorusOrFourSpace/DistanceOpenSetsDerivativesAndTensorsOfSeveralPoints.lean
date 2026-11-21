import YangMills.Construction.TorusOrFourSpace.CutOffsOnAProductOfOpenSets
import YangMills.Construction.TorusOrFourSpace.SpaceAndItsFunctionsAreWellDefined
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.TupleFacts
open Kind
def eucNorm {p : ℕ+} (x : Coords p) : ℝ := Real.sqrt (∑ j, x j ^ 2)
def unitCoord (μ : Fin 4) : Fin (4 * ((1 : ℕ+) : ℕ)) :=
  ⟨μ, by have := μ.2; simp⟩
def unitIndex (μ : Fin 4) : CoordIndex 1 :=
  Pi.single (unitCoord μ) 1
def indexBlock {p : ℕ+} (α : CoordIndex p) (i : Fin (p : ℕ)) : CoordIndex 1 :=
  fun j => α ⟨4 * (i : ℕ) + (j : ℕ), by
    have hi := i.2
    have hj := j.2
    simp only [PNat.one_coe] at hj
    omega⟩
def rePart {X : Type*} (F : X → ℂ) : X → ℂ := fun y => ((F y).re : ℂ)
def imPart {X : Type*} (F : X → ℂ) : X → ℂ := fun y => ((F y).im : ℂ)
variable (D : Params) (E : Kind) (p : ℕ+)
def fromSingle {Z : Type*} (G : E.Tuple D 1 → Z) : E.Pt D → Z :=
  fun y => G fun _ => y
def IsClassCSingle (ν : ℕ) (φ : E.Pt D → ℂ) : Prop :=
  Tuple.IsClassC D E ν (Tuple.ofSingle D E φ)
def singlePartialDeriv (a : CoordIndex 1) (φ : E.Pt D → ℂ) : E.Pt D → ℂ :=
  fromSingle D E (Tuple.partialDeriv D E a (Tuple.ofSingle D E φ))
def translateNorms (x x' : Coords p) : Set ℝ :=
  {r | ∃ k ∈ Tuple.periodSet D E p, r = eucNorm (x - x' - k)}
def ProjSurjectiveFibres : Prop :=
  Function.Surjective (Tuple.proj D E (p := p)) ∧
    ∀ x x' : Coords p,
      Tuple.proj D E x = Tuple.proj D E x' ↔
        x - x' ∈ Tuple.periodSet D E p
def DistEqMinTranslateNorm : Prop :=
  ∀ x x' : Coords p,
    IsLeast (translateNorms D E p x x')
        (Tuple.tupleDist D E (Tuple.proj D E x)
          (Tuple.proj D E x')) ∧
      Tuple.tupleDist D E (Tuple.proj D E x)
          (Tuple.proj D E x') ≤ eucNorm (x - x')
def DistIsMetric : Prop :=
  (∀ y y' : E.Tuple D p, 0 ≤ Tuple.tupleDist D E y y') ∧
    (∀ y y' : E.Tuple D p, Tuple.tupleDist D E y y' = 0 ↔ y = y') ∧
    (∀ y y' : E.Tuple D p,
      Tuple.tupleDist D E y y' = Tuple.tupleDist D E y' y) ∧
    ∀ y y' y'' : E.Tuple D p,
      Tuple.tupleDist D E y y'' ≤
        Tuple.tupleDist D E y y' + Tuple.tupleDist D E y' y''
def ExistsNearestLift : Prop :=
  ∀ (x : Coords p) (y' : E.Tuple D p), ∃ x', Tuple.IsLiftOf D E y' x' ∧
    eucNorm (x - x') = Tuple.tupleDist D E (Tuple.proj D E x) y'
def TranslateNormMinUnique : Prop :=
  ∀ y y' : E.Tuple D p, ∃! r : ℝ, ∀ x x' : Coords p,
    Tuple.IsLiftOf D E y x → Tuple.IsLiftOf D E y' x' →
      IsLeast (translateNorms D E p x x') r
def ProjContinuous : Prop :=
  MetricNotions.IsContinuousWrt (fun x x' : Coords p => eucNorm (x - x'))
    (Tuple.tupleDist D E) (Tuple.proj D E)
def ProjOpenMap : Prop :=
  ∀ U : Set (Coords p), IsOpen U →
    Tuple.IsOpenT D E (Tuple.proj D E '' U)
def IsOpenIffPreimage : Prop :=
  ∀ Ω : Set (E.Tuple D p),
    Tuple.IsOpenT D E Ω ↔ IsOpen (Tuple.proj D E ⁻¹' Ω)
def ContinuousIffComp : Prop :=
  ∀ F : E.Tuple D p → ℂ,
    Tuple.IsContinuousT D E F ↔ Continuous (F ∘ Tuple.proj D E)
def BallFacts : Prop :=
  ∀ (y : E.Tuple D p) (r : ℝ), 0 < r →
    Tuple.IsOpenT D E {y' | Tuple.tupleDist D E y' y < r} ∧
      (∀ a ∈ {y' | Tuple.tupleDist D E y' y < r},
        ∀ b ∈ {y' | Tuple.tupleDist D E y' y < r},
          Tuple.tupleDist D E a b < 2 * r) ∧
      Tuple.IsCompactT D E {y' | Tuple.tupleDist D E y' y ≤ r}
def BoxSetFacts : Prop :=
  ∀ Ω : Fin (p : ℕ) → Set (E.Pt D),
    ((∀ i, Kind.IsOpenQ D E (Ω i)) →
      Tuple.IsOpenT D E (Tuple.boxSet D E Ω)) ∧
    ((∀ i, Kind.IsClosedQ D E (Ω i)) →
      Tuple.IsClosedT D E (Tuple.boxSet D E Ω)) ∧
    ((∀ i, Kind.IsCompactQ D E (Ω i)) →
      Tuple.IsCompactT D E (Tuple.boxSet D E Ω))
def EvalLipschitzCompact : Prop :=
  ∀ i : Fin (p : ℕ),
    (∀ y y' : E.Tuple D p,
      Kind.quotDist D E (y i) (y' i) ≤ Tuple.tupleDist D E y y') ∧
    ∀ K : Set (E.Tuple D p), Tuple.IsCompactT D E K →
      Kind.IsCompactQ D E ((fun y : E.Tuple D p => y i) '' K)
def FactorDistContinuous : Prop :=
  ∀ i i' : Fin (p : ℕ), i ≠ i' →
    Tuple.IsContinuousT D E
      (fun y : E.Tuple D p => Kind.quotDist D E (y i) (y i'))
def DerivFacts : Prop :=
  ∀ (ν : ℕ) (F : E.Tuple D p → ℂ), Tuple.IsClassC D E ν F →
    ∀ α : CoordIndex p, α.degree ≤ ν →
      (∃! H : E.Tuple D p → ℂ, H ∘ Tuple.proj D E =
        Coords.iterPartial α (F ∘ Tuple.proj D E)) ∧
      Tuple.partialDeriv D E α F ∘ Tuple.proj D E =
        Coords.iterPartial α (F ∘ Tuple.proj D E) ∧
      Tuple.IsContinuousT D E (Tuple.partialDeriv D E α F) ∧
      Tuple.IsClassC D E (ν - α.degree) (Tuple.partialDeriv D E α F) ∧
      (∀ β : CoordIndex p, β.degree ≤ ν - α.degree →
        Tuple.partialDeriv D E β (Tuple.partialDeriv D E α F) =
          Tuple.partialDeriv D E (α + β) F) ∧
      Tuple.supportT D E (Tuple.partialDeriv D E α F) ⊆ Tuple.supportT D E F
def CNormFiniteOfCompactSupport : Prop :=
  ∀ (ν : ℕ) (F : E.Tuple D p → ℂ), Tuple.IsClassC D E ν F →
    Tuple.IsCompactT D E (Tuple.supportT D E F) →
      Tuple.cNorm D E ν F < ∞
def SingleC1Agree : Prop :=
  ∀ u : E.Pt D → ℝ,
    (Tuple.IsClassC D E 1 (Tuple.ofSingle D E fun y => (u y : ℂ)) ↔
      Kind.IsC1Fn D E u) ∧
    (Kind.IsC1Fn D E u →
      (∀ μ : Fin 4,
        Tuple.partialDeriv D E (unitIndex μ)
            (Tuple.ofSingle D E fun y => (u y : ℂ)) =
          Tuple.ofSingle D E fun y => (Kind.partialDeriv D E μ u y : ℂ)) ∧
      Tuple.supportT D E (Tuple.ofSingle D E fun y => (u y : ℂ)) =
        Tuple.singleSet D E (Kind.supportQ D E u))
def SupportAddMul : Prop :=
  ∀ (F H : E.Tuple D p → ℂ) (a b : ℂ),
    Tuple.supportT D E (a • F + b • H) ⊆
        Tuple.supportT D E F ∪ Tuple.supportT D E H ∧
      Tuple.supportT D E (F * H) ⊆
        Tuple.supportT D E F ∩ Tuple.supportT D E H
def ClassCAddMulParts : Prop :=
  ∀ (ν : ℕ) (F H : E.Tuple D p → ℂ), Tuple.IsClassC D E ν F →
    Tuple.IsClassC D E ν H →
      (∀ a b : ℂ, Tuple.IsClassC D E ν (a • F + b • H)) ∧
      Tuple.IsClassC D E ν (F * H) ∧
      Tuple.IsClassC D E ν (rePart F) ∧
      Tuple.IsClassC D E ν (imPart F) ∧
      ∀ α : CoordIndex p, α.degree ≤ ν →
        Tuple.partialDeriv D E α (rePart F) =
            rePart (Tuple.partialDeriv D E α F) ∧
          Tuple.partialDeriv D E α (imPart F) =
            imPart (Tuple.partialDeriv D E α F)
def TestFnsSubmodule : Prop :=
  ∀ Ω : Set (E.Tuple D p), Tuple.IsOpenT D E Ω →
    (∃ S : Submodule ℂ (E.Tuple D p → ℂ),
      (S : Set (E.Tuple D p → ℂ)) = Tuple.testFns D E Ω) ∧
    ∀ F ∈ Tuple.testFns D E Ω,
      rePart F ∈ Tuple.testFns D E Ω ∧
      imPart F ∈ Tuple.testFns D E Ω ∧
      (∀ α : CoordIndex p,
        Tuple.partialDeriv D E α F ∈ Tuple.testFns D E Ω) ∧
      (∀ H : E.Tuple D p → ℂ, Tuple.IsSmoothT D E H →
        H * F ∈ Tuple.testFns D E Ω) ∧
      ∀ ν : ℕ, Tuple.cNorm D E ν F < ∞
def TestFnsEmpty : Prop :=
  Tuple.testFns D E (∅ : Set (E.Tuple D p)) = {0}
def TensorClassC : Prop :=
  ∀ (ν : ℕ) (φ : Fin (p : ℕ) → E.Pt D → ℂ), (∀ i, IsClassCSingle D E ν (φ i)) →
    Tuple.IsClassC D E ν (Tuple.tensorProd D E φ) ∧
    (∀ α : CoordIndex p, α.degree ≤ ν →
      Tuple.partialDeriv D E α (Tuple.tensorProd D E φ) =
        Tuple.tensorProd D E fun i => singlePartialDeriv D E (indexBlock α i) (φ i)) ∧
    Tuple.supportT D E (Tuple.tensorProd D E φ) ⊆
      Tuple.boxSet D E fun i => Kind.supportQ D E (φ i)
def TensorTestFns : Prop :=
  ∀ (Ω : Fin (p : ℕ) → Set (E.Pt D)) (φ : Fin (p : ℕ) → E.Pt D → ℂ),
    (∀ i, Kind.IsOpenQ D E (Ω i)) →
      (∀ i, φ i ∈ Tuple.singleTestFns D E (Ω i)) →
        Tuple.tensorProd D E φ ∈
          Tuple.testFns D E (Tuple.boxSet D E Ω)
def TensorMultilinear : Prop :=
  ∀ (φ : Fin (p : ℕ) → E.Pt D → ℂ) (i : Fin (p : ℕ)) (ψ χ : E.Pt D → ℂ) (c : ℂ),
    Tuple.tensorProd D E (Function.update φ i (ψ + χ)) =
        Tuple.tensorProd D E (Function.update φ i ψ) +
          Tuple.tensorProd D E (Function.update φ i χ) ∧
      Tuple.tensorProd D E (Function.update φ i (c • ψ)) =
        c • Tuple.tensorProd D E (Function.update φ i ψ)
def AllFacts : Prop :=
  ∀ (D : Params) (E : Kind) (p : ℕ+),
    ProjSurjectiveFibres D E p ∧
    DistEqMinTranslateNorm D E p ∧
    DistIsMetric D E p ∧
    ExistsNearestLift D E p ∧
    TranslateNormMinUnique D E p ∧
    WellPosedness.TranslateNormMinWellDefined D E ∧
    ProjContinuous D E p ∧
    ProjOpenMap D E p ∧
    IsOpenIffPreimage D E p ∧
    ContinuousIffComp D E p ∧
    BallFacts D E p ∧
    BoxSetFacts D E p ∧
    EvalLipschitzCompact D E p ∧
    FactorDistContinuous D E p ∧
    DerivFacts D E p ∧
    CNormFiniteOfCompactSupport D E p ∧
    SingleC1Agree D E ∧
    SupportAddMul D E p ∧
    ClassCAddMulParts D E p ∧
    TestFnsSubmodule D E p ∧
    TestFnsEmpty D E p ∧
    TensorClassC D E p ∧
    TensorTestFns D E p ∧
    TensorMultilinear D E p
end YangMills.Construction.PeriodicSpace.TupleFacts
