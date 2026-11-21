import YangMills.Construction.TorusOrFourSpace.AdmissibleFamiliesOfOpenSets
import YangMills.Construction.TorusOrFourSpace.ClassesOfFunctionsWithSupportInASet
import YangMills.Construction.TorusOrFourSpace.CutOffsOnAProductOfOpenSets
import YangMills.Construction.TorusOrFourSpace.OriginClosedBallsAndBallsAboutTheOrigin
import YangMills.Construction.TorusOrFourSpace.QuarterSideOpenBallsDistinctPointsAndBoundedFamilies
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind
variable (D : Params) (E : Kind) {n : ℕ+}
def translateChart (z : Fin 4 → ℝ) : euclidean.Pt D → E.Pt D :=
  fun u : Fin 4 → ℝ => E.quotMap D (z + u)
def chartSource (z : Fin 4 → ℝ) (G : Set (E.Pt D)) : Set (euclidean.Pt D) :=
  {u | ENNReal.ofReal (TorusMetric.euclidNormVec u) < periodQuarter D E ∧ translateChart D E z u ∈ G}
namespace Tuple
def chartSources (z : Fin (n : ℕ) → Fin 4 → ℝ) (G : Fin (n : ℕ) → Set (E.Pt D)) :
    Set (euclidean.Tuple D n) :=
  boxSet D euclidean fun i => chartSource D E (z i) (G i)
def prodChart (z : Fin (n : ℕ) → Fin 4 → ℝ) :
    euclidean.Tuple D n → E.Tuple D n :=
  fun u i => translateChart D E (z i) (u i)
def HasCompactSupportWithin (Ω : Set (E.Tuple D n)) (F : E.Tuple D n → ℂ) : Prop :=
  IsCompactT D E (supportT D E F) ∧ supportT D E F ⊆ Ω
def pullback (z : Fin (n : ℕ) → Fin 4 → ℝ) (G : Fin (n : ℕ) → Set (E.Pt D))
    (F : E.Tuple D n → ℂ) : euclidean.Tuple D n → ℂ :=
  (chartSources D E z G).indicator (F ∘ prodChart D E z)
def pushforward (z : Fin (n : ℕ) → Fin 4 → ℝ) (G : Fin (n : ℕ) → Set (E.Pt D))
    (H : euclidean.Tuple D n → ℂ) : E.Tuple D n → ℂ :=
  (boxSet D E G).indicator
    (H ∘ Function.invFunOn (prodChart D E z) (chartSources D E z G))
def singlePullback (z : Fin 4 → ℝ) (G : Set (E.Pt D)) (φ : E.Pt D → ℂ) :
    euclidean.Pt D → ℂ :=
  fun u => pullback D E (n := 1) (fun _ => z) (fun _ => G) (ofSingle D E φ) fun _ => u
def singlePushforward (z : Fin 4 → ℝ) (G : Set (E.Pt D)) (h : euclidean.Pt D → ℂ) :
    E.Pt D → ℂ :=
  fun y => pushforward D E (n := 1) (fun _ => z) (fun _ => G) (ofSingle D euclidean h) fun _ => y
open scoped Classical in
def composePullback (z : Fin (n : ℕ) → Fin 4 → ℝ) (G : Fin (n : ℕ) → Set (E.Pt D))
    (T : testFns D euclidean (chartSources D E z G) → ℂ) :
    testFns D E (boxSet D E G) → ℂ :=
  fun F => if h : pullback D E z G F.1 ∈ testFns D euclidean (chartSources D E z G)
    then T ⟨_, h⟩ else 0
open scoped Classical in
def composePushforward (z : Fin (n : ℕ) → Fin 4 → ℝ) (G : Fin (n : ℕ) → Set (E.Pt D))
    (T' : testFns D E (boxSet D E G) → ℂ) :
    testFns D euclidean (chartSources D E z G) → ℂ :=
  fun H => if h : pushforward D E z G H.1 ∈ testFns D E (boxSet D E G)
    then T' ⟨_, h⟩ else 0
end Tuple
namespace AdmissibleCharts
open PeriodicSpace.Kind.Tuple
def FactorIsometricCharts (R : ℝ) (z : Fin (n : ℕ) → Fin 4 → ℝ)
    (G : Fin (n : ℕ) → Set (E.Pt D)) : Prop :=
  0 < maxMemberDiam D E G ∧ maxMemberDiam D E G ≤ ENNReal.ofReal (2 * R) ∧
    maxMemberDiam D E G < periodQuarter D E ∧
    ∀ i, Kind.IsOpenQ D euclidean (chartSource D E (z i) (G i)) ∧
      (0 : euclidean.Pt D) ∈ chartSource D E (z i) (G i) ∧
      Set.BijOn (translateChart D E (z i)) (chartSource D E (z i) (G i)) (G i) ∧
      (∀ u ∈ chartSource D E (z i) (G i), ∀ u' ∈ chartSource D E (z i) (G i),
        quotDist D E (translateChart D E (z i) u) (translateChart D E (z i) u') =
          TorusMetric.euclidNormVec (u - u')) ∧
      chartSource D E (z i) (G i) ⊆
        {u | ENNReal.ofReal (TorusMetric.euclidNormVec u) ≤ maxMemberDiam D E G} ∧
      {u : euclidean.Pt D | ENNReal.ofReal (TorusMetric.euclidNormVec u) ≤
        maxMemberDiam D E G} ⊆ {u | TorusMetric.euclidNormVec u ≤ 2 * R} ∧
      G i ⊆ closedBallAbout D E (E.quotMap D (z i)) (maxMemberDiam D E G).toReal
def ProdChartHomeomorph (z : Fin (n : ℕ) → Fin 4 → ℝ)
    (G : Fin (n : ℕ) → Set (E.Pt D)) : Prop :=
  ∃ h : chartSources D E z G ≃ boxSet D E G,
    (∀ u, (h u).1 = prodChart D E z u.1) ∧
      MetricNotions.IsContinuousWrt
        (fun a b : chartSources D E z G => Tuple.tupleDist D euclidean a.1 b.1)
        (fun a b : boxSet D E G => Tuple.tupleDist D E a.1 b.1) h ∧
      MetricNotions.IsContinuousWrt
        (fun a b : boxSet D E G => Tuple.tupleDist D E a.1 b.1)
        (fun a b : chartSources D E z G => Tuple.tupleDist D euclidean a.1 b.1) h.symm
def PullbackPushforwardInverse (z : Fin (n : ℕ) → Fin 4 → ℝ)
    (G : Fin (n : ℕ) → Set (E.Pt D)) : Prop :=
  (∀ (a b : ℂ) (F F' : E.Tuple D n → ℂ),
    HasCompactSupportWithin D E (boxSet D E G) F →
    HasCompactSupportWithin D E (boxSet D E G) F' →
      pullback D E z G (a • F + b • F') = a • pullback D E z G F + b • pullback D E z G F') ∧
  (∀ (a b : ℂ) (H H' : euclidean.Tuple D n → ℂ),
    HasCompactSupportWithin D euclidean (chartSources D E z G) H →
    HasCompactSupportWithin D euclidean (chartSources D E z G) H' →
      pushforward D E z G (a • H + b • H') =
        a • pushforward D E z G H + b • pushforward D E z G H') ∧
  (∀ F : E.Tuple D n → ℂ, HasCompactSupportWithin D E (boxSet D E G) F →
    HasCompactSupportWithin D euclidean (chartSources D E z G) (pullback D E z G F) ∧
      pushforward D E z G (pullback D E z G F) = F ∧
      Tuple.supportT D euclidean (pullback D E z G F) =
        chartSources D E z G ∩ prodChart D E z ⁻¹' Tuple.supportT D E F) ∧
  ∀ H : euclidean.Tuple D n → ℂ,
    HasCompactSupportWithin D euclidean (chartSources D E z G) H →
    HasCompactSupportWithin D E (boxSet D E G) (pushforward D E z G H) ∧
      pullback D E z G (pushforward D E z G H) = H ∧
      Tuple.supportT D E (pushforward D E z G H) =
        prodChart D E z '' Tuple.supportT D euclidean H
def PullbackPushforwardCommuteDeriv (z : Fin (n : ℕ) → Fin 4 → ℝ)
    (G : Fin (n : ℕ) → Set (E.Pt D)) : Prop :=
  (∀ (ν : ℕ) (F : E.Tuple D n → ℂ), HasCompactSupportWithin D E (boxSet D E G) F →
    IsClassC D E ν F → IsClassC D euclidean ν (pullback D E z G F) ∧
      ∀ α : CoordIndex n, α.degree ≤ ν →
        Tuple.partialDeriv D euclidean α (pullback D E z G F) =
          pullback D E z G (Tuple.partialDeriv D E α F)) ∧
  ∀ (ν : ℕ) (H : euclidean.Tuple D n → ℂ),
    HasCompactSupportWithin D euclidean (chartSources D E z G) H →
    IsClassC D euclidean ν H → IsClassC D E ν (pushforward D E z G H) ∧
      ∀ α : CoordIndex n, α.degree ≤ ν →
        Tuple.partialDeriv D E α (pushforward D E z G H) =
          pushforward D E z G (Tuple.partialDeriv D euclidean α H)
def PullbackIsometryOnTestFns (z : Fin (n : ℕ) → Fin 4 → ℝ)
    (G : Fin (n : ℕ) → Set (E.Pt D)) : Prop :=
  Set.BijOn (pullback D E z G) (testFns D E (boxSet D E G))
      (testFns D euclidean (chartSources D E z G)) ∧
    Set.InvOn (pushforward D E z G) (pullback D E z G) (testFns D E (boxSet D E G))
      (testFns D euclidean (chartSources D E z G)) ∧
    ∀ F ∈ testFns D E (boxSet D E G), ∀ ν : ℕ,
      cNorm D euclidean ν (pullback D E z G F) = cNorm D E ν F
def ConvergenceDistribCorrespond (z : Fin (n : ℕ) → Fin 4 → ℝ)
    (G : Fin (n : ℕ) → Set (E.Pt D)) : Prop :=
  (∀ (Fs : ℕ+ → testFns D E (boxSet D E G))
      (F : testFns D E (boxSet D E G))
      (Hs : ℕ+ → testFns D euclidean (chartSources D E z G))
      (H : testFns D euclidean (chartSources D E z G)),
      (∀ t, (Hs t).1 = pullback D E z G (Fs t).1) → H.1 = pullback D E z G F.1 →
        (TendstoInTestFns Fs F ↔ TendstoInTestFns Hs H)) ∧
    Set.BijOn (composePullback D E z G) {T | IsDistrib T} {T' | IsDistrib T'} ∧
    Set.InvOn (composePushforward D E z G) (composePullback D E z G)
      {T | IsDistrib T} {T' | IsDistrib T'} ∧
    ∀ T : testFns D euclidean (chartSources D E z G) → ℂ, IsDistrib T → ∀ ν₀ : ℕ,
      (IsDistribOfOrderLE ν₀ (composePullback D E z G T) ↔
        IsDistribOfOrderLE ν₀ T)
def SingleMapsOnClasses (z : Fin (n : ℕ) → Fin 4 → ℝ) (G : Fin (n : ℕ) → Set (E.Pt D)) : Prop :=
  (∀ i, singlePullback D E (z i) (G i) '' singleTestFns D E (G i) =
      singleTestFns D euclidean (chartSource D E (z i) (G i)) ∧
    ∀ φ ∈ singleTestFns D E (G i), (∀ y, (φ y).im = 0) →
      ∀ u, (singlePullback D E (z i) (G i) φ u).im = 0) ∧
  (∀ φ : Fin (n : ℕ) → E.Pt D → ℂ, (∀ i, φ i ∈ singleTestFns D E (G i)) →
    pullback D E z G (tensorProd D E φ) =
      tensorProd D euclidean fun i => singlePullback D E (z i) (G i) (φ i)) ∧
  ∀ i, (fun g : euclidean.Pt D → ℝ =>
        singlePushforward D E (z i) (G i) fun u => (g u : ℂ)) ''
          c1SupportedIn D euclidean (chartSource D E (z i) (G i)) =
      (fun (h : E.Pt D → ℝ) (y : E.Pt D) => (h y : ℂ)) '' c1SupportedIn D E (G i) ∧
    (∀ (a b : ℝ), ∀ g ∈ c1SupportedIn D euclidean (chartSource D E (z i) (G i)),
      ∀ g' ∈ c1SupportedIn D euclidean (chartSource D E (z i) (G i)),
        (singlePushforward D E (z i) (G i) fun u => ((a * g u + b * g' u : ℝ) : ℂ)) =
          (a : ℂ) • (singlePushforward D E (z i) (G i) fun u => (g u : ℂ)) +
            (b : ℂ) • singlePushforward D E (z i) (G i) fun u => (g' u : ℂ)) ∧
    ∀ g ∈ c1SupportedIn D euclidean (chartSource D E (z i) (G i)),
      c1NormSingle D E (singlePushforward D E (z i) (G i) fun u => (g u : ℂ)) =
        c1NormSingleReal D euclidean g
def Claim : Prop :=
  ∀ (D : Params) (E : Kind) (n : ℕ+) (R d : ℝ) (G : Fin (n : ℕ) → Set (E.Pt D))
    (z : Fin (n : ℕ) → Fin 4 → ℝ),
    AdmissibleWith D E R d G → (∀ i, (G i).Nonempty) →
    (∀ i, E.quotMap D (z i) ∈ G i) →
      FactorIsometricCharts D E R z G ∧ ProdChartHomeomorph D E z G ∧
        PullbackPushforwardInverse D E z G ∧
        PullbackPushforwardCommuteDeriv D E z G ∧
        PullbackIsometryOnTestFns D E z G ∧
        ConvergenceDistribCorrespond D E z G ∧ SingleMapsOnClasses D E z G
end AdmissibleCharts
end YangMills.Construction.PeriodicSpace.Kind
