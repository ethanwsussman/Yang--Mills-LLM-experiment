import YangMills.Construction.Matrices.ExponentialChartsOfPowersOfG
import YangMills.Construction.PowerSeries.ConvergentSeries
import YangMills.Construction.Towers.TheLeftChart
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
namespace YangMills.Construction
namespace IdentityExpChart
open YangMills.Construction.Matrices
open YangMills.Construction.Matrices.GroupLieProduct YangMills.Construction.Matrices.PowerExpCharts
section LinearCoordinates
variable {V W T : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
def IsRealAnalyticVia {l : ℕ} (e : T → Coordinates.ComplexCoordinates l) (D : Set V) (g : V → T) :
    Prop :=
  IsOpen D ∧ ∀ (N : ℕ) (x : V ≃ₗ[ℝ] (Fin N → ℝ)),
    Coordinates.ComplexCoordinates.IsRealAnalyticIn
      (PowerSeries.RealSeries.realEmbed '' (x '' D))
      fun z => e (g (x.symm fun i => (z i).re))
def IsRealAnalyticToRealSpace (D : Set V) (g : V → W) : Prop :=
  ∀ (M : ℕ) (y : W ≃ₗ[ℝ] (Fin M → ℝ)),
    IsRealAnalyticVia (fun w => PowerSeries.RealSeries.realEmbed (y w)) D g
end LinearCoordinates
section FiniteProducts
variable {σ τ : Type}
def toMatrices (Y : σ → ComplexMatrix2.LieElement) : σ → ComplexMatrix2 :=
  fun s => (Y s).toMatrix
def expFamily (Y : σ → ComplexMatrix2.LieElement) : σ → ComplexMatrix2 :=
  fun s => ComplexMatrix2.matExp (Complex.I • (Y s).toMatrix)
def lieBall (σ : Type) (ε : ℝ) : Set (σ → ComplexMatrix2.LieElement) :=
  {Y | supNorm (toMatrices Y) < ε}
def expImage (σ : Type) : Set (σ → ComplexMatrix2) := expFamily '' lieBall σ (1 / 2)
def logFamily (X : σ → ComplexMatrix2) : σ → ComplexMatrix2 :=
  fun s => (1 / Complex.I) • ComplexMatrix2.logSeries (X s)
def toLieFamily (A : σ → ComplexMatrix2) : σ → ComplexMatrix2.LieElement :=
  open Classical in fun s =>
    if h : A s ∈ ComplexMatrix2.hermitianTraceless then
      (⟨A s, h⟩ : ComplexMatrix2.hermitianTraceless) else 0
def logChart (X : σ → ComplexMatrix2) : σ → ComplexMatrix2.LieElement :=
  toLieFamily (logFamily X)
def oneFamily (σ : Type) : σ → ComplexMatrix2 := fun _ => 1
def IsExpChartAtOne [Fintype σ] (c : EmbeddedSubmanifold.Chart (specialUnitaryPower σ))
    (ν : σ × Fin 3 ≃ Fin c.dim) : Prop :=
  c.source = {u | ofCoeffs (fun s a => u (ν (s, a))) ∈ lieBall σ (1 / 2)} ∧
    ∀ u ∈ c.source,
      c.param u = expFamily (ofCoeffs fun s a => u (ν (s, a)))
def ExpChartAtOne (σ : Type) [Fintype σ] : Prop :=
  InjOn expFamily (lieBall σ (1 / 2)) ∧
  specialUnitaryPower.IsOpenSubset (expImage σ) ∧
  (∀ Y ∈ lieBall σ (1 / 2), logChart (expFamily Y) = Y) ∧
  (∀ X ∈ expImage σ, toMatrices (logChart X) = logFamily X) ∧
  ContinuousOn (expFamily (σ := σ)) (lieBall σ (1 / 2)) ∧
  ContinuousOn (logChart (σ := σ)) (expImage σ) ∧
  ∃ (c : EmbeddedSubmanifold.Chart (specialUnitaryPower σ)) (ν : σ × Fin 3 ≃ Fin c.dim),
    IsExpChartAtOne c ν
def ExpImagesOfBalls (σ : Type) [Fintype σ] : Prop :=
  (∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → expFamily '' lieBall σ ε =
    {X | X ∈ specialUnitaryPower σ ∧
      ∀ s, ComplexMatrix2.operatorNorm (X s - 1) < 2 * Real.sin (ε / 2)}) ∧
  ∀ N ∈ 𝓝[specialUnitaryPower σ] oneFamily σ, ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 2 ∧
    expFamily '' lieBall σ ε ⊆ N
def pullbackDomain (O : Set (σ → ComplexMatrix2)) : Set (σ → ComplexMatrix2.LieElement) :=
  {Y | Y ∈ lieBall σ (1 / 2) ∧ expFamily Y ∈ O}
def RealAnalyticIffInExpChart (σ τ : Type) [Fintype σ] [Fintype τ]
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) : Prop :=
  ∀ O : Set (σ → ComplexMatrix2), specialUnitaryPower.IsOpenSubset O → O ⊆ expImage σ →
    (∀ f : (σ → ComplexMatrix2) → ℝ,
      IsLocallyHolomorphicRestriction (HolomorphicScalar b) Complex.ofReal O f ↔
        IsRealAnalyticToRealSpace (pullbackDomain O) (f ∘ expFamily)) ∧
    (∀ f : (σ → ComplexMatrix2) → ComplexMatrix2,
      IsLocallyHolomorphicRestriction (HolomorphicMatrix b) id O f ↔
        IsRealAnalyticVia Coordinates.ComplexCoordinates.matrixEquiv (pullbackDomain O)
          (f ∘ expFamily)) ∧
    ∀ f : (σ → ComplexMatrix2) → τ → ComplexMatrix2, MapsTo f O (specialUnitaryPower τ) →
      (IsLocallyHolomorphicRestriction (IsHolomorphicToProduct b) asGroupFactors O f ↔
        ∀ (k : ℕ) (ν : τ ≃ Fin k),
          IsRealAnalyticVia (matrixPiEquiv ν) (pullbackDomain O) (f ∘ expFamily)) ∧
      (MapsTo f O (expImage τ) →
        (IsLocallyHolomorphicRestriction (IsHolomorphicToProduct b) asGroupFactors O f ↔
          IsRealAnalyticToRealSpace (pullbackDomain O) (logChart ∘ f ∘ expFamily)))
end FiniteProducts
section OnTower
open YangMills.Construction.Tower
variable {L n k j j' : ℕ}
def expForm (Y : Edge L n k j → ComplexMatrix2) : Edge L n k j → ComplexMatrix2 :=
  PeriodicLattice.expTwist Y 1
def logPullback (φ : (Edge L n k j → ComplexMatrix2) → Edge L n k j' → ComplexMatrix2)
    (Y : Edge L n k j → ComplexMatrix2) : Edge L n k j' → ComplexMatrix2 :=
  extendOddly fun c => (1 / Complex.I) • ComplexMatrix2.logSeries (φ (expForm Y) c)
def funPullback (F : (Edge L n k j → ComplexMatrix2) → ℝ) (Y : Edge L n k j → ComplexMatrix2) :
    ℝ :=
  F (expForm Y)
def formValues (B : Edge L n k j → ComplexMatrix2) :
    PositiveEdge L n k j → ComplexMatrix2.LieElement :=
  toLieFamily (restrictToPositiveEdges B)
def ofValues (y : PositiveEdge L n k j → ComplexMatrix2.LieElement) :
    Edge L n k j → ComplexMatrix2 :=
  extendOddly fun b =>
    open Classical in if h : b.IsPositivelyOriented then (y ⟨b, h⟩).toMatrix else 0
def mapOnValues (G : (Edge L n k j → ComplexMatrix2) → Edge L n k j' → ComplexMatrix2) :
    (PositiveEdge L n k j → ComplexMatrix2.LieElement) →
      PositiveEdge L n k j' → ComplexMatrix2.LieElement :=
  fun y => formValues (G (ofValues y))
def fnOnValues (G : (Edge L n k j → ComplexMatrix2) → ℝ) :
    (PositiveEdge L n k j → ComplexMatrix2.LieElement) → ℝ :=
  fun y => G (ofValues y)
end OnTower
end IdentityExpChart
end YangMills.Construction
