import YangMills.Construction.Continuum.SchwingerFunctions
import YangMills.Construction.InfiniteLattice.HyperoctahedralMotionsAndCubes
import YangMills.Construction.InfiniteLattice.LimitsOfTheMeasuresOfCubicTori
import YangMills.Construction.InfiniteLattice.PeriodOrbitsArraysOfOneGeneratorAndPerturbedKernels
import YangMills.Construction.InfiniteLattice.SmearedDensityAndConnectedFunctionsOfAMeasure
import YangMills.Construction.Lattice.BondsOfTheTorusLatticeAndThePeriodicExtension
import YangMills.Construction.Torus.LiftsAndInducedMaps
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Function
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
def cubicPeriodSet (ℓ : ℝ) : Set AmbientSpace := range (TestFunctions.latticeTranslate ℓ)
namespace PeriodSublattice
def HasCubicPeriods {a : ℝ} (Γ : PeriodSublattice a) (ℓ : ℝ) : Prop :=
  (fun γ : LatticePoint a => (γ : AmbientSpace)) '' (Γ.periods : Set (LatticePoint a)) = cubicPeriodSet ℓ
variable {L : ℕ} {j : ℤ} (m : ℕ) (Γ : PeriodSublattice (PeriodicLattice.meshSize L j))
def orbitLink (ω : Γ.QuotientLink) : PeriodicLattice.Bond L m j :=
  projectLink L m j (mem_range.1 ω.2).choose.1
def orbitPlaquette (ω : Γ.QuotientPlaquette) : PeriodicLattice.Plaquette L m j :=
  TorusLifts.projectPlaquette L m j (Γ.quotientPlaquette_nonempty ω).some
def pullbackConfig (U : PeriodicLattice.CompactGaugeField L m j) : Γ.QuotientField :=
  fun ω => U.linkValue (Γ.orbitLink m ω)
open Classical in
def pullbackFun (U : PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2) : Γ.QuotientField :=
  if h : U ∈ PeriodicLattice.compactGaugeFields L m j then Γ.pullbackConfig m ⟨U, h⟩ else fun _ => 1
end PeriodSublattice
structure CubicPeriodSublatticeProperties {a : ℝ} (Γ : PeriodSublattice a) (ℓ : ℝ) : Prop where
  minPeriodNorm_eq : GibbsAtFixedSpacing.minPeriodNorm Γ = ℓ
  image_cubicPeriodSet : ∀ w ∈ hyperoctahedralLinearGroup,
    (fun x => w x) '' cubicPeriodSet ℓ = cubicPeriodSet ℓ
structure QuotientByCubicPeriodsIsPeriodicLattice (L m K : ℕ) (β : ℝ)
    (Γ : PeriodSublattice (PeriodicLattice.meshSize L (K : ℤ))) : Prop where
  isPositivelyOriented_projectLink : ∀ b : Link (PeriodicLattice.meshSize L (K : ℤ)),
    (projectLink L m (K : ℤ) b).IsPositivelyOriented ↔ b.IsPositivelyOriented
  orbitLink_linkClass : ∀ b : PositiveLink (PeriodicLattice.meshSize L (K : ℤ)),
    Γ.orbitLink m (Γ.linkClass b) = projectLink L m (K : ℤ) b.1
  bijOn_orbitLink : BijOn (Γ.orbitLink m) univ
    (PeriodicLattice.forwardBonds L m (K : ℤ))
  isHomeomorph_pullbackConfig : IsHomeomorph (Γ.pullbackConfig m (j := (K : ℤ)))
  map_productHaarMeasure : (PeriodicLattice.productHaarMeasure L m (K : ℤ)).map
    (Γ.pullbackFun m) = Γ.quotientHaar
  lift_pullbackConfig : ∀ U : PeriodicLattice.CompactGaugeField L m (K : ℤ),
    Γ.lift (Γ.pullbackConfig m U) = liftCompactField U
  continuous_liftCompactField :
    Continuous (liftCompactField : PeriodicLattice.CompactGaugeField L m (K : ℤ) → _)
  orbitPlaquette_mk : ∀ p : ElementaryPlaquette (PeriodicLattice.meshSize L (K : ℤ)),
    Γ.orbitPlaquette m ⟨Γ.plaquetteOrbit p, p, rfl⟩ =
      TorusLifts.projectPlaquette L m (K : ℤ) p
  bijective_orbitPlaquette : Bijective (Γ.orbitPlaquette m)
  faceEnergy_liftCompactField : ∀ (U : PeriodicLattice.CompactGaugeField L m (K : ℤ))
    (p : ElementaryPlaquette (PeriodicLattice.meshSize L (K : ℤ))),
    faceEnergy (liftCompactField U) p =
      PeriodicLattice.plaquetteCost U.1 (TorusLifts.projectPlaquette L m (K : ℤ) p)
  gibbsMeasure_eq_map : Γ.gibbsMeasure β = (PeriodicLattice.wilsonGibbsMeasure L m K β).map
    (Γ.pullbackFun m)
  liftedGibbsMeasure_eq : Γ.liftedGibbsMeasure β = liftedWilsonMeasure L m K β
def LiftedWilsonMeasureIntegral (L m K : ℕ) (β : ℝ) : Prop :=
  ∀ F : GaugeField (PeriodicLattice.meshSize L (K : ℤ)) → ℂ, IsBoundedObservable F →
    ∫ V, F V ∂liftedWilsonMeasure L m K β =
      PeriodicLattice.gibbsExpectation L m K β (F ∘ liftField L m (K : ℤ))
structure PlaquetteSmearingUnderProjection (L m K : ℕ) (β : ℝ) : Prop where
  plaquetteSmearing_liftCompactField : ∀ (f : AmbientSpace → ℂ), TestFunctions.IsBoundedFun f →
    (∃ A : Set AmbientSpace, TestFunctions.IsPeriodizable (PeriodicLattice.torusSide L m) A f) →
    ∀ U : PeriodicLattice.CompactGaugeField L m (K : ℤ),
      plaquetteSmearing f (liftCompactField U) =
        PeriodicLattice.smearedObservable (TestFunctions.periodize (PeriodicLattice.torusSide L m) f) U.1
  integral_plaquetteSmearing : ∀ (f : AmbientSpace → ℂ), TestFunctions.IsBoundedFun f →
    (∃ A : Set AmbientSpace, TestFunctions.IsPeriodizable (PeriodicLattice.torusSide L m) A f) →
    ∫ V, plaquetteSmearing f V ∂liftedWilsonMeasure L m K β =
      PeriodicLattice.gibbsExpectation L m K β
        (PeriodicLattice.smearedObservable (TestFunctions.periodize (PeriodicLattice.torusSide L m) f))
  ursellFunctionOfMeasure_eq : ∀ {n : ℕ} (f : Fin n → AmbientSpace → ℝ),
    IsSeparatedLipschitzTuple (PeriodicLattice.torusSide L m) f →
      ursellFunctionOfMeasure (liftedWilsonMeasure L m K β) f =
        SchwingerFunctions.connectedSchwingerR4 L m K β f
def CubicTorusAsQuotient.Statement : Prop :=
  ∀ (s : Conventions.StandingParameters) (β : ℝ), 0 < β →
    (∃ Γ : PeriodSublattice (PeriodicLattice.meshSize s.L ((s.K : ℕ) : ℤ)),
      Γ.HasCubicPeriods (PeriodicLattice.torusSide s.L s.m)) ∧
    (∀ Γ : PeriodSublattice (PeriodicLattice.meshSize s.L ((s.K : ℕ) : ℤ)),
      Γ.HasCubicPeriods (PeriodicLattice.torusSide s.L s.m) →
        CubicPeriodSublatticeProperties Γ (PeriodicLattice.torusSide s.L s.m) ∧
          QuotientByCubicPeriodsIsPeriodicLattice s.L s.m s.K β Γ) ∧
    LiftedWilsonMeasureIntegral s.L s.m s.K β ∧
    PlaquetteSmearingUnderProjection s.L s.m s.K β
end InfiniteLattice
end YangMills.Construction
