import YangMills.Construction.Cumulants.SumOverPartitionsSortedByBlocksOfOneElement
import YangMills.Construction.InfiniteLattice.PeriodicGibbsStatesAtOneCutoff
import YangMills.Construction.ReflectionPositiveLimits.LatticeRepresentativesAtOneCutoff
import YangMills.Construction.ReflectionPositiveLimits.PlateauxOfLimitsOfLatticeStatesProof
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.SpacingFreeSizes
open YangMills.Construction.GibbsAtFixedSpacing (BorelProb)
open YangMills.Construction.InfiniteLattice (LatticeSymmetry scaledCube regionObservables
  periodicGibbsSet smearedEnergy axisStep shift)
open YangMills.Construction.ReflectionPositivity.LatticeRepresentatives (toComplexObs)
open YangMills.Construction.ReflectionPositivity.DirectionPictures (axisReflectionGroup
  scaledCubeReflectionSize siteReflectPerm)
open YangMills.Construction.SetPartition (PartitionsFin)
open YangMills.Construction.SetPartition.SingletonSplit (singletonFreeProdSumOn)
open YangMills.Construction.TestFunctions (closedBallR4 euclidDistR4 sharpNormR4)
theorem axisReflectionGroup_eq_reflectionGroup :
    axisReflectionGroup = reflectionGroup := by apply _root_.YangMills.Construction.ReflectionPositivity.LimitPlateaux.axisReflectionGroup_eq_reflectionGroup <;> assumption
def reflectionToLatticeSymmetry (a : ℝ) (γ : reflectionGroup) : LatticeSymmetry a :=
  YangMills.Construction.ReflectionPositivity.DirectionPictures.axisReflectionGroup.toLatticeSymmetry a
    ⟨γ.1, by rw [axisReflectionGroup_eq_reflectionGroup]; exact γ.2⟩
def momentBound (x : ℝ) (y : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ T : Finset (Fin k), x ^ T.card * singletonFreeProdSumOn y (Finset.univ \ T)
variable {L K : ℕ}
def realExpectation (ρ : BorelProb (YangMills.Construction.PeriodicLattice.meshSize L (K : ℤ)))
    (F : GaugeFieldsAtLevel L K → ℝ) : ℝ :=
  ∫ U, F U ∂ρ.1
def partCumulant (ρ ν : BorelProb (YangMills.Construction.PeriodicLattice.meshSize L (K : ℤ)))
    {k : ℕ} (f : Fin k → ScalarField) (J : Finset (Fin k)) : ℂ :=
  if J.card = 1 then
    ∑ i ∈ J, ((realExpectation ρ (smearedEnergy (f i)) - realExpectation ν (smearedEnergy (f i)) : ℝ) : ℂ)
  else
    YangMills.Construction.Cumulants.finsetCumulant ρ.1 (fun i => smearedEnergy (f i)) J
def MomentPartitionExpansion
    (ρ ν : BorelProb (YangMills.Construction.PeriodicLattice.meshSize L (K : ℤ))) (X : Tuple) :
    Prop :=
  ((realExpectation ρ (centeredProduct L K ν X) : ℝ) : ℂ) =
    ∑ π : PartitionsFin X.1.length, ∏ J ∈ π.parts, partCumulant ρ ν (fun i => X.1.get i) J
structure ConstantsBound (s : YangMills.Construction.Conventions.StandingParameters) {K : ℕ}
    (ρ ν : BorelProb (YangMills.Construction.PeriodicLattice.meshSize s.L (K : ℤ)))
    (M d R x : ℝ) (y : ℕ → ℝ) : Prop where
  singleBound : ∀ F : ScalarField, YangMills.Construction.TestFunctions.IsLipschitzFor euclidDistR4 F →
    (∃ c, tsupport F ⊆ closedBallR4 c R) →
    |realExpectation ρ (smearedEnergy F) - realExpectation ν (smearedEnergy F)| ≤ x * sharpNormR4 M F
  cumulantBound : ∀ n : ℕ, 2 ≤ n → ∀ f : Fin n → ScalarField,
    (∀ i, YangMills.Construction.TestFunctions.IsLipschitzFor euclidDistR4 (f i)) →
    YangMills.Construction.FourSpaceSymbols.FamilyAdmissible (s := s) d R (fun i => tsupport (f i)) →
    ‖YangMills.Construction.PeriodicGibbsAtCutoff.connectedCorrelation (L := s.L) (K := K) ρ.1 n f‖ ≤
      y n * ∏ i, sharpNormR4 M (f i)
def MomentBounded (ρ ν : BorelProb (YangMills.Construction.PeriodicLattice.meshSize L (K : ℤ)))
    (M x : ℝ) (y : ℕ → ℝ) (X : Tuple) : Prop :=
  |realExpectation ρ (centeredProduct L K ν X)| ≤
    momentBound x y X.len * (X.1.map (sharpNormR4 M)).prod
def reflectedObservable (ν : BorelProb (YangMills.Construction.PeriodicLattice.meshSize L (K : ℤ)))
    (γ : reflectionGroup) (X : Tuple) : GaugeFieldsAtLevel L K → ℂ :=
  (reflectionToLatticeSymmetry (YangMills.Construction.PeriodicLattice.meshSize L (K : ℤ)) γ).actOn
    (toComplexObs (centeredProduct L K ν X))
def sizeCorr (ρ ν : BorelProb (YangMills.Construction.PeriodicLattice.meshSize L (K : ℤ)))
    (r : ℕ+) (μ : Fin 4) (γ : reflectionGroup) (X : Tuple) : ℂ :=
  YangMills.Construction.ReflectionPositivity.DirectionPictures.reflCorr ρ μ (reflectedObservable ν γ X)
    ((shift ((2 * (r : ℕ)) • axisStep (YangMills.Construction.PeriodicLattice.meshSize L (K : ℤ)) μ)).actOn
      (reflectedObservable ν γ X))
def SizeIsMoment (s : YangMills.Construction.Conventions.StandingParameters) {K : ℕ}
    (ρ ν : BorelProb (YangMills.Construction.PeriodicLattice.meshSize s.L (K : ℤ)))
    (ϖ d R : ℝ) (r : ℕ+) (μ : Fin 4) (γ : reflectionGroup) (X : Tuple) : Prop :=
  ∃ h : Concatenable (mirrorTuple μ γ X) (translatedTuple ϖ μ γ X),
    (concat _ _ h).len = 2 * X.len ∧
    IsAdmissibleAt s d R (concat _ _ h) ∧
    0 ≤ sizeCorr ρ ν r μ γ X ∧
    sizeCorr ρ ν r μ γ X = ((realExpectation ρ (centeredProduct s.L K ν (concat _ _ h)) : ℝ) : ℂ)
def SizesIndependentOfSpacing : Prop :=
  ∀ (s : YangMills.Construction.Conventions.StandingParameters) (K : ℕ+) (β : ℝ)
    (ν ρ : BorelProb (YangMills.Construction.PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ))),
    0 < β → ν.1 ∈ periodicGibbsSet s.L K β → ρ.1 ∈ periodicGibbsSet s.L K β →
    ∀ X : Tuple,
      MomentPartitionExpansion ρ ν X ∧
      (∀ (M d R x : ℝ) (y : ℕ → ℝ), 0 < d → 0 < R → IsAdmissibleAt s d R X →
        ConstantsBound s ρ ν M d R x y → MomentBounded ρ ν M x y X) ∧
      ∀ ϖ ∈ posAdicGridPoints s.L, ∀ d R : ℝ, 0 < d → 0 < R → X ∈ admissibleClass s ϖ d R →
        YangMills.Construction.PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ) ≤ d / 2 →
        ∀ r : ℕ+, (r : ℝ) = ϖ / YangMills.Construction.PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ) →
          (toComplexObs (centeredProduct s.L K ν X) ∈
              regionObservables (YangMills.Construction.PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ))
                (scaledCube (YangMills.Construction.PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ)) r) ∧
            scaledCube (YangMills.Construction.PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ)) r =
              {x | maxNorm x ≤ ϖ}) ∧
          (∀ (μ : Fin 4) (γ : reflectionGroup), SizeIsMoment s ρ ν ϖ d R r μ γ X) ∧
          ∀ (M x : ℝ) (y : ℕ → ℝ), ConstantsBound s ρ ν M d R x y →
            MomentBounded ρ ν M x y X ∧
            0 ≤ scaledCubeReflectionSize (meshSize_pos s.isAdmissible _) ρ.1 r
              (toComplexObs (centeredProduct s.L K ν X)) ∧
            scaledCubeReflectionSize (meshSize_pos s.isAdmissible _) ρ.1 r
              (toComplexObs (centeredProduct s.L K ν X)) ≤
              momentBound x y (2 * X.len) * (X.1.map fun f => sharpNormR4 M f ^ 2).prod
end YangMills.Construction.ReflectionPositivity.SpacingFreeSizes
