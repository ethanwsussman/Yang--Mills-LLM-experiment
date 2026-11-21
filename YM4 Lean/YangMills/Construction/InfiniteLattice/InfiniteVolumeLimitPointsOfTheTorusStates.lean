import YangMills.Construction.Continuum.SchwingerFunctions
import YangMills.Construction.InfiniteLattice.HyperoctahedralMotionsAndCubes
import YangMills.Construction.InfiniteLattice.LimitsOfTheMeasuresOfCubicTori
import YangMills.Construction.InfiniteLattice.MirrorsOfTheSixteenFamiliesAndTheClassOfReflectionPositiveStates
import YangMills.Construction.InfiniteLattice.PeriodicGibbsAndTorusLimitSets
import YangMills.Construction.InfiniteLattice.SmearedDensityAndConnectedFunctionsOfAMeasure
import YangMills.Construction.InfiniteLattice.SpecificationGaugeTransformationsAndClassesOfMeasures
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped Topology
noncomputable section
namespace YangMills.Construction.InfiniteLattice
open YangMills.Construction.GibbsAtFixedSpacing YangMills.Construction.TestFunctions YangMills.Construction.LatticeConventions
open YangMills.Construction.LatticeConventions.NormalHyperplane (reflectSymmetry)
theorem axial_isLatticeMirror_of_two_mul_mem {a : ℝ} {μ : Direction} {c : ℝ}
    (hc : ∃ q : ℤ, 2 * c = (q : ℝ) * a) :
    (NormalHyperplane.axial μ c).IsLatticeMirror a := by
  obtain ⟨q, hq⟩ := hc
  refine ⟨fun _ => ⟨q, ?_⟩, fun hd => absurd hd (not_isFaceDiagonalNormal_basisVector μ)⟩
  show c = (q : ℝ) * (a / 2)
  linarith
theorem two_mul_mem_of_mem_halfShift {a c : ℝ} (hc : ∃ q : ℤ, c = ((q : ℝ) + 1 / 2) * a) :
    ∃ q : ℤ, 2 * c = (q : ℝ) * a := by
  obtain ⟨q, rfl⟩ := hc
  exact ⟨2 * q + 1, by push_cast; ring⟩
def SideExponentsTendToInfinity (L : ℕ) (m : ℕ → ℕ) : Prop :=
  (∀ i, 0 < m i) ∧ Tendsto (fun i => PeriodicLattice.torusSide L (m i)) atTop atTop
def LiftedMeasuresTendstoWeakly (L K : ℕ) (β : ℝ) (m : ℕ → ℕ)
    (ν : BorelProb (refinedSpacing L K)) : Prop :=
  ∃ ρ : ℕ → BorelProb (refinedSpacing L K),
    (∀ i, (ρ i).1 = liftedWilsonMeasure L (m i) K β) ∧ BorelProb.TendstoWeak ρ ν
def LimitSetClosedNonemptyAndSubseqConvergent (L K : ℕ) (β : ℝ) : Prop :=
  (cubicTorusLimitStates L K β).Nonempty ∧ IsClosed (cubicTorusLimitStates L K β) ∧
    ∀ m : ℕ → ℕ, SideExponentsTendToInfinity L m →
      ∃ (φ : ℕ → ℕ) (ν : BorelProb (refinedSpacing L K)), StrictMono φ ∧
        LiftedMeasuresTendstoWeakly L K β (m ∘ φ) ν
def IsSymmetricReflPosGibbs (L K : ℕ) (β : ℝ) (ν : BorelProb (refinedSpacing L K)) :
    Prop :=
  IsGibbs β ν.1 ∧
    (∀ r : LatticeSymmetry (refinedSpacing L K),
      r.toFun ∈ affineHyperoctahedralMaps (refinedSpacing L K) →
      IsSymmetricUnder ν.1 r) ∧
    (∀ v : LatticePoint (refinedSpacing L K), IsSymmetricUnder ν.1 (shift v)) ∧
    (∀ r : LatticeSymmetry (refinedSpacing L K), (∃ w ∈ hyperoctahedralLinearGroup, r.toFun = ⇑w) →
      IsSymmetricUnder ν.1 r) ∧
    (∀ (μ : Direction) (c : ℝ) (hc : ∃ q : ℤ, 2 * c = (q : ℝ) * refinedSpacing L K),
      IsSymmetricUnder ν.1 (reflectSymmetry (axial_isLatticeMirror_of_two_mul_mem (μ := μ) hc))) ∧
    ν.1 ∈ periodicGibbsSet L K β ∧
    ∀ (μ : Direction) (c : ℝ) (hc : ∃ q : ℤ, c = ((q : ℝ) + 1 / 2) * refinedSpacing L K),
      IsFullyReflectionPositive
        (axial_isLatticeMirror_of_two_mul_mem (μ := μ) (two_mul_mem_of_mem_halfShift hc)) ν
def IsDisjointCompactLipschitzTuple {n : ℕ} (f : Fin n → AmbientSpace → ℝ) : Prop :=
  2 ≤ n ∧ (∀ i, IsLipschitzFor euclidDist (f i)) ∧ (∀ i, HasCompactSupport (f i)) ∧
    ∀ i k, i ≠ k → Disjoint (tsupport (f i)) (tsupport (f k))
def LocalQuantitiesTendsto (L K : ℕ) (β : ℝ) (m : ℕ → ℕ) (ν : BorelProb (refinedSpacing L K)) :
    Prop :=
  (∀ F ∈ continuousLocalFunctions (refinedSpacing L K),
    Tendsto (fun i => ∫ U, F U ∂liftedWilsonMeasure L (m i) K β) atTop (𝓝 (ν.integral F))) ∧
  (∀ f : AmbientSpace → ℂ, IsBoundedFun f → Bornology.IsBounded (Function.support f) →
    (∀ᶠ i in atTop, ∃ A : Set AmbientSpace,
      HasDiameterLE A (PeriodicLattice.torusSide L (m i) / 2) ∧ Function.support f ⊆ A) ∧
    Tendsto
      (fun i => PeriodicLattice.gibbsExpectation L (m i) K β
        (PeriodicLattice.smearedObservable (periodize (PeriodicLattice.torusSide L (m i)) f)))
      atTop (𝓝 (ν.integral (plaquetteSmearing f)))) ∧
  ∀ (n : ℕ) (f : Fin n → AmbientSpace → ℝ), IsDisjointCompactLipschitzTuple f →
    (∀ᶠ i in atTop, IsSeparatedLipschitzTuple (PeriodicLattice.torusSide L (m i)) f) ∧
    Tendsto (fun i => SchwingerFunctions.connectedSchwingerR4 L (m i) K β f) atTop
      (𝓝 (ursellFunctionOfMeasure (L := L) (K := K) ν.1 f))
def UrsellBoundsPassToLimits (L K : ℕ) (β : ℝ) : Prop :=
  ∀ (n : ℕ) (f : Fin n → AmbientSpace → ℝ), IsDisjointCompactLipschitzTuple f →
    ∀ (b : ℝ) (m₀ : ℕ), 0 ≤ b → 0 < m₀ →
      (∀ m : ℕ, 0 < m → PeriodicLattice.torusSide L m₀ ≤ PeriodicLattice.torusSide L m →
        IsSeparatedLipschitzTuple (PeriodicLattice.torusSide L m) f ∧
          ‖SchwingerFunctions.connectedSchwingerR4 L m K β f‖ ≤ b) →
      ∀ ν ∈ cubicTorusLimitStates L K β, ‖ursellFunctionOfMeasure (L := L) (K := K) ν.1 f‖ ≤ b
def TorusStateLimitPoints : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ K : ℕ, 0 < K → ∀ β : ℝ, 0 < β →
    LimitSetClosedNonemptyAndSubseqConvergent L K β ∧
    (∀ ν ∈ cubicTorusLimitStates L K β, IsSymmetricReflPosGibbs L K β ν) ∧
    (∀ (m : ℕ → ℕ) (ν : BorelProb (refinedSpacing L K)), SideExponentsTendToInfinity L m →
      LiftedMeasuresTendstoWeakly L K β m ν → LocalQuantitiesTendsto L K β m ν) ∧
    UrsellBoundsPassToLimits L K β
end YangMills.Construction.InfiniteLattice
