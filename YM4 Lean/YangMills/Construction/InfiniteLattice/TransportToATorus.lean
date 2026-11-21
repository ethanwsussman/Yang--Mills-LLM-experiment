import YangMills.Construction.InfiniteLattice.SeparatedLipschitzTuplesAndPartialFamilies
import YangMills.Construction.Lattice.EuclideanIsometries
import YangMills.Construction.Lattice.ObservablesAndTestNorms
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicTransport
abbrev radialBall (ρ : ℝ) : Set (Fin 4 → ℝ) := SeparatedFamilies.originBall (ENNReal.ofReal ρ)
structure AdmissibleData (L m : ℕ) (ρ : ℝ) : Prop where
  blocking : Conventions.IsAdmissibleBlockingFactor L
  one_le_m : 1 ≤ m
  radius_pos : 0 < ρ
  radius_le_side : 2 * ρ + 2 ≤ (L : ℝ) ^ m
def SupportedInBall (ρ : ℝ) (f : (Fin 4 → ℝ) → ℝ) : Prop :=
  HasCompactSupport f ∧ tsupport f ⊆ radialBall ρ
def ProjIsometricOnBall (L m : ℕ) (ρ : ℝ) : Prop :=
  (∀ x y, PeriodicLattice.torusEuclidDist L m
      (TorusMetric.torusProj (PeriodicLattice.torusSide L m) x)
      (TorusMetric.torusProj (PeriodicLattice.torusSide L m) y) ≤
      TestFunctions.euclidDistR4 x y) ∧
    (∀ x ∈ radialBall ρ, ∀ y ∈ radialBall ρ,
      PeriodicLattice.torusEuclidDist L m
        (TorusMetric.torusProj (PeriodicLattice.torusSide L m) x)
        (TorusMetric.torusProj (PeriodicLattice.torusSide L m) y) =
        TestFunctions.euclidDistR4 x y) ∧
    InjOn (TorusMetric.torusProj (PeriodicLattice.torusSide L m)) (radialBall ρ)
def AgreesWithPeriodization {ℓ : ℝ} (S : Set (Fin 4 → ℝ)) (f : (Fin 4 → ℝ) → ℝ)
    (h : TorusMetric.Torus4 ℓ → ℝ) : Prop :=
  (∀ x ∈ S, h (TorusMetric.torusProj ℓ x) = f x) ∧
    ∀ u, u ∉ TorusMetric.torusProj ℓ '' S → h u = 0
def PeriodizeEqLatticeSum (L m : ℕ) (ρ : ℝ) (f : (Fin 4 → ℝ) → ℝ) : Prop :=
  TestFunctions.HasDiameterLE (radialBall ρ) (PeriodicLattice.torusSide L m / 2) ∧
    TestFunctions.IsPeriodizable (PeriodicLattice.torusSide L m) (radialBall ρ) f ∧
    (∀ x, TestFunctions.periodize (PeriodicLattice.torusSide L m) f
        (TorusMetric.torusProj (PeriodicLattice.torusSide L m) x) =
      ∑' k : Fin 4 → ℤ, f (x + TestFunctions.latticeTranslate (PeriodicLattice.torusSide L m) k)) ∧
    (∀ x, {k : Fin 4 → ℤ |
      f (x + TestFunctions.latticeTranslate (PeriodicLattice.torusSide L m) k) ≠ 0}.Subsingleton) ∧
    AgreesWithPeriodization (radialBall ρ) f
      (TestFunctions.periodize (PeriodicLattice.torusSide L m) f)
def PeriodizeIndepOfRadius (L m : ℕ) (f : (Fin 4 → ℝ) → ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → tsupport f ⊆ radialBall r → 2 * r + 2 ≤ (L : ℝ) ^ m →
    TestFunctions.IsPeriodizable (PeriodicLattice.torusSide L m) (radialBall r) f ∧
      AgreesWithPeriodization (radialBall r) f
        (TestFunctions.periodize (PeriodicLattice.torusSide L m) f)
def PeriodizeLinear (L m : ℕ) (f g : (Fin 4 → ℝ) → ℝ) : Prop :=
  ∀ c c' : ℝ, TestFunctions.periodize (PeriodicLattice.torusSide L m) (c • f + c' • g) =
    c • TestFunctions.periodize (PeriodicLattice.torusSide L m) f +
      c' • TestFunctions.periodize (PeriodicLattice.torusSide L m) g
def PeriodizeLipschitzBounds (L m : ℕ) (f : (Fin 4 → ℝ) → ℝ) : Prop :=
  TestFunctions.IsLipschitzFor TestFunctions.euclidDistR4 f →
    TestFunctions.IsLipschitzFor (PeriodicLattice.torusEuclidDist L m)
        (TestFunctions.periodize (PeriodicLattice.torusSide L m) f) ∧
      TestFunctions.uniformNorm (TestFunctions.periodize (PeriodicLattice.torusSide L m) f) =
        TestFunctions.uniformNorm f ∧
      TestFunctions.lipConstTorus (TestFunctions.periodize (PeriodicLattice.torusSide L m) f) ≤
        TestFunctions.lipConstR4 f ∧
      ∀ M : ℝ, 0 < M → TestFunctions.sharpNormTorus M
          (TestFunctions.periodize (PeriodicLattice.torusSide L m) f) ≤
        TestFunctions.sharpNormR4 M f
def PeriodizeSupports (L m : ℕ) (ρ : ℝ) (f g : (Fin 4 → ℝ) → ℝ) : Prop :=
  SeparatedFamilies.torusSupport (L := L) (m := m)
      (TestFunctions.periodize (PeriodicLattice.torusSide L m) f) =
      TorusMetric.torusProj (PeriodicLattice.torusSide L m) '' tsupport f ∧
    SeparatedFamilies.torusSupport (L := L) (m := m)
        (TestFunctions.periodize (PeriodicLattice.torusSide L m) f) ⊆
      TestFunctions.closedBallTorus (TorusMetric.torusProj (PeriodicLattice.torusSide L m) 0) ρ ∧
    TorusMetric.setEuclidDist
        (SeparatedFamilies.torusSupport (L := L) (m := m)
          (TestFunctions.periodize (PeriodicLattice.torusSide L m) f))
        (SeparatedFamilies.torusSupport (L := L) (m := m)
          (TestFunctions.periodize (PeriodicLattice.torusSide L m) g)) =
      TestFunctions.setDistR4 (tsupport f) (tsupport g) ∧
    (tsupport f ∩ tsupport g = ∅ →
      SeparatedFamilies.torusSupport (L := L) (m := m)
          (TestFunctions.periodize (PeriodicLattice.torusSide L m) f) ∩
        SeparatedFamilies.torusSupport (L := L) (m := m)
          (TestFunctions.periodize (PeriodicLattice.torusSide L m) g) = ∅)
def PeriodizeC1 (L m : ℕ) (f : (Fin 4 → ℝ) → ℝ) : Prop :=
  ContDiff ℝ 1 f →
    TestFunctions.periodize (PeriodicLattice.torusSide L m) f ∈ SeparatedFamilies.torusC1 L m
def MainClaim : Prop :=
  ∀ (L m : ℕ) (ρ : ℝ) (f g : (Fin 4 → ℝ) → ℝ), AdmissibleData L m ρ →
    SupportedInBall ρ f → SupportedInBall ρ g →
    ProjIsometricOnBall L m ρ ∧
      PeriodizeEqLatticeSum L m ρ f ∧
      PeriodizeIndepOfRadius L m f ∧
      PeriodizeLinear L m f g ∧
      PeriodizeLipschitzBounds L m f ∧
      PeriodizeSupports L m ρ f g ∧
      PeriodizeC1 L m f
end PeriodicTransport
end YangMills.Construction
