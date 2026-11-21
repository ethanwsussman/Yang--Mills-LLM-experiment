import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import YangMills.Construction.Lattice.SiteCoordinates
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace QuotientLattices
open InfiniteLattice (AmbientSpace)
abbrev refinementIndex (k j : ℕ) : ℤ := (k : ℤ) - (j : ℤ)
def sitesPerAxis (L n k j : ℕ) : ℕ := 2 * L ^ (n + k - j)
def scaledIntVector (a : ℝ) (N : Fin 4 → ℤ) : AmbientSpace := fun μ => (N μ : ℝ) * a
def IsQuotientLattice (L n k j : ℕ) : Prop :=
  0 ≤ refinementIndex k j ∧ refinementIndex k j > -(n : ℤ) ∧ -(n : ℤ) < 0 ∧
  PeriodicLattice.meshSize L (refinementIndex k j) = (L : ℝ) ^ ((j : ℤ) - (k : ℤ)) ∧
  PeriodicLattice.torusSide L n / PeriodicLattice.meshSize L (refinementIndex k j) =
    (sitesPerAxis L n k j : ℝ) ∧
  2 * L ≤ sitesPerAxis L n k j ∧
  InfiniteLattice.latticeSubgroup (PeriodicLattice.torusSide L n) ≤
    InfiniteLattice.latticeSubgroup (PeriodicLattice.meshSize L (refinementIndex k j)) ∧
  (PeriodicLattice.sublattice L n (refinementIndex k j) : Set (PeriodicLattice.FourTorus L n)) =
    TorusMetric.torusProj (PeriodicLattice.torusSide L n) ''
      (InfiniteLattice.latticeSubgroup (PeriodicLattice.meshSize L (refinementIndex k j)) :
        Set AmbientSpace) ∧
  (∀ N N' : Fin 4 → ℤ,
    TorusMetric.torusProj (PeriodicLattice.torusSide L n)
        (scaledIntVector (PeriodicLattice.meshSize L (refinementIndex k j)) N) =
      TorusMetric.torusProj (PeriodicLattice.torusSide L n)
        (scaledIntVector (PeriodicLattice.meshSize L (refinementIndex k j)) N') ↔
    ∀ μ, N μ ≡ N' μ [ZMOD (sitesPerAxis L n k j : ℤ)]) ∧
  (∀ (y : PeriodicLattice.Site L n (refinementIndex k j)) (μ : Fin 4),
    (PeriodicLattice.axisLine y μ).ncard = sitesPerAxis L n k j) ∧
  Finite (PeriodicLattice.Site L n (refinementIndex k j)) ∧
  Finite (PeriodicLattice.Bond L n (refinementIndex k j)) ∧
  Finite (PeriodicLattice.Plaquette L n (refinementIndex k j))
def StraightPathLengthCriterion (L n k j : ℕ) : Prop :=
  ∀ t : ℤ, ((|t| : ℤ) : ℝ) < (L : ℝ) ^ ((n : ℤ) + refinementIndex k j) ↔
    ((|t| : ℤ) : ℝ) * PeriodicLattice.meshSize L (refinementIndex k j) <
      PeriodicLattice.torusSide L n / 2
def LevelLatticeAtCutoff (L n k j : ℕ) : Prop :=
  1 ≤ k → (∃ K : ℕ+, (K : ℕ) = k) ∧
    PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k j) =
      PeriodicLattice.sublattice L n (refinementIndex k j)
def periodShiftedDiff (S : ℝ) (a b : AmbientSpace) (n : Fin 4 → ℤ) : AmbientSpace :=
  a - b + fun μ => S * (n μ : ℝ)
def minPeriodicDist (S : ℝ) (a b : AmbientSpace) : ℝ :=
  sInf (range fun n : Fin 4 → ℤ => TorusMetric.euclidNormVec (periodShiftedDiff S a b n))
def MinPeriodicDistOfClasses (S : ℝ) : Prop :=
  ∀ a b : AmbientSpace,
    IsLeast (range fun n : Fin 4 → ℤ => TorusMetric.euclidNormVec (periodShiftedDiff S a b n))
      (minPeriodicDist S a b) ∧
    (∀ a' b' : AmbientSpace, TorusMetric.torusProj S a' = TorusMetric.torusProj S a →
      TorusMetric.torusProj S b' = TorusMetric.torusProj S b →
      minPeriodicDist S a' b' = minPeriodicDist S a b) ∧
    (minPeriodicDist S a b = 0 → TorusMetric.torusProj S a = TorusMetric.torusProj S b) ∧
    minPeriodicDist S a b =
      TorusMetric.torusEuclidNorm (TorusMetric.torusProj S a - TorusMetric.torusProj S b)
section GroupSteps
variable {X : Type} [AddCommGroup X]
def unitStepsWithZero (e : Fin 4 → X) : Option (ℤˣ × Fin 4) → X
  | none => 0
  | some q => (q.1 : ℤ) • e q.2
def IsSignedAxisStep (e : Fin 4 → X) (x x' : X) (ε : ℤˣ) (μ : Fin 4) : Prop :=
  x' - x = (ε : ℤ) • e μ
def IsPositiveStep (e : Fin 4 → X) (x x' : X) : Prop := ∃ μ, IsSignedAxisStep e x x' 1 μ
def AreNeighbours (e : Fin 4 → X) (x x' : X) : Prop := ∃ ε μ, IsSignedAxisStep e x x' ε μ
def StepsDistinctAndSigned (Λ : AddSubgroup X) (e : Fin 4 → X) : Prop :=
  (∀ q, unitStepsWithZero e q ∈ Λ) ∧
  Function.Injective (unitStepsWithZero e) ∧
  ∀ x ∈ Λ, ∀ x' ∈ Λ,
    (∀ ε μ ε' μ', IsSignedAxisStep e x x' ε μ → IsSignedAxisStep e x x' ε' μ' →
      ε = ε' ∧ μ = μ') ∧
    ∀ ε μ, IsSignedAxisStep e x x' ε μ →
      IsSignedAxisStep e x' x (-ε) μ ∧ Xor (IsPositiveStep e x x') (IsPositiveStep e x' x)
def NeighboursAtSpacing (d : X → X → ℝ) (Λ : AddSubgroup X) (a : ℝ) (e : Fin 4 → X) : Prop :=
  (∀ x ∈ Λ, ∀ x' ∈ Λ, d x x' = a ↔ AreNeighbours e x x') ∧
  ∀ s : X → X, (∀ p q, d (s p) (s q) = d p q) → s '' (Λ : Set X) = Λ →
    InjOn s (Λ : Set X) ∧
    (∀ x ∈ Λ, ∀ x' ∈ Λ, AreNeighbours e x x' → AreNeighbours e (s x) (s x')) ∧
    ∀ y ∈ Λ, ∀ y' ∈ Λ, AreNeighbours e y y' →
      AreNeighbours e (Function.invFunOn s (Λ : Set X) y)
        (Function.invFunOn s (Λ : Set X) y')
end GroupSteps
def torusAxisSteps (L n k j : ℕ) (μ : Fin 4) : PeriodicLattice.FourTorus L n :=
  (PeriodicLattice.unitStep L n (refinementIndex k j) μ : PeriodicLattice.FourTorus L n)
def spaceAxisSteps (a : ℝ) (μ : Fin 4) : AmbientSpace := (InfiniteLattice.axisStep a μ : AmbientSpace)
def torusDist (L n : ℕ) (x y : PeriodicLattice.FourTorus L n) : ℝ :=
  TorusMetric.torusEuclidNorm (x - y)
def spaceDist (x y : AmbientSpace) : ℝ := TorusMetric.euclidNormVec (x - y)
def TorusAndSpaceLatticeProperties : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ n j k : ℕ, 1 ≤ n → j ≤ k →
    PeriodicLattice.torusSide L n ∈ PeriodicLattice.torusSides L ∧
    IsQuotientLattice L n k j ∧
    StraightPathLengthCriterion L n k j ∧
    LevelLatticeAtCutoff L n k j ∧
    MinPeriodicDistOfClasses (PeriodicLattice.torusSide L n) ∧
    StepsDistinctAndSigned (PeriodicLattice.sublattice L n (refinementIndex k j))
      (torusAxisSteps L n k j) ∧
    StepsDistinctAndSigned
      (InfiniteLattice.latticeSubgroup (PeriodicLattice.meshSize L (refinementIndex k j)))
      (spaceAxisSteps (PeriodicLattice.meshSize L (refinementIndex k j))) ∧
    NeighboursAtSpacing (torusDist L n) (PeriodicLattice.sublattice L n (refinementIndex k j))
      (PeriodicLattice.meshSize L (refinementIndex k j)) (torusAxisSteps L n k j) ∧
    NeighboursAtSpacing spaceDist
      (InfiniteLattice.latticeSubgroup (PeriodicLattice.meshSize L (refinementIndex k j)))
      (PeriodicLattice.meshSize L (refinementIndex k j))
      (spaceAxisSteps (PeriodicLattice.meshSize L (refinementIndex k j)))
end QuotientLattices
end YangMills.Construction
