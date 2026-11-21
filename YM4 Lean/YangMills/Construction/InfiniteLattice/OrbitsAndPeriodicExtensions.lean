import YangMills.Construction.InfiniteLattice.HyperoctahedralMotionsAndCubes
import YangMills.Construction.InfiniteLattice.PeriodOrbitsArraysOfOneGeneratorAndPerturbedKernels
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.InfiniteLattice
namespace GibbsAtFixedSpacing
variable {a : ℝ}
def QuotientTorusFinite (Γ : PeriodSublattice a) : Prop :=
  Γ.periods.FiniteIndex ∧ Finite Γ.QuotientTorus ∧ Finite Γ.QuotientLink ∧
    Finite Γ.QuotientPlaquette ∧
    ∀ Q : AddSubgroup (LatticePoint a), Γ.periods ≤ Q → Finite (Q ⧸ Γ.periods.addSubgroupOf Q)
def LiftContinuousPeriodic (Γ : PeriodSublattice a) : Prop :=
  Continuous Γ.lift ∧
    (∀ (U : Γ.QuotientField), ∀ γ ∈ Γ.periods,
      (shift γ).pullbackField (Γ.lift U) = Γ.lift U) ∧
    ∀ (U : Γ.QuotientField), ∀ γ ∈ Γ.periods, ∀ b : Link a,
      Γ.lift U (b.shiftBy γ) = Γ.lift U b
def PeriodizationOrbitInvariant (Γ : PeriodSublattice a) : Prop :=
  (∀ (E : Type) (F : GaugeField a → E) (v w : LatticePoint a), pointOrbit Γ v = pointOrbit Γ w →
    Γ.periodize ((shift v).actOn F) = Γ.periodize ((shift w).actOn F)) ∧
    (∀ p q : ElementaryPlaquette a, Γ.plaquetteOrbit p = Γ.plaquetteOrbit q →
      Γ.periodize (fun U : GaugeField a => faceEnergy U p) =
        Γ.periodize fun U : GaugeField a => faceEnergy U q) ∧
    ∀ (E : Type) [TopologicalSpace E] (F : GaugeField a → E), Continuous F →
      Continuous (Γ.periodize F)
def PeriodSublatticeQuotientFacts : Prop :=
  ∀ a : ℝ, 0 < a → ∀ Γ : PeriodSublattice a,
    QuotientTorusFinite Γ ∧ LiftContinuousPeriodic Γ ∧ PeriodizationOrbitInvariant Γ
end GibbsAtFixedSpacing
end YangMills.Construction
end
