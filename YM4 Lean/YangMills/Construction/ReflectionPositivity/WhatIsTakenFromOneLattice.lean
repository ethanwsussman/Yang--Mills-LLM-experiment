import YangMills.Construction.InfiniteLattice.ErgodicPhases
import YangMills.Construction.ReflectionPositivity.OneLatticeAtEverySpacing
import YangMills.Construction.ReflectionPositivity.PicturesCubeVectorsAndReflectionSizesAtASpacing
import YangMills.Construction.ReflectionPositivity.RateConstantAndRateFunction
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate ComplexOrder
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
open YangMills.Construction.InfiniteLattice (GaugeField IsLocalObservable IsBoundedObservable
  LatticeSymmetry LatticePoint condExpShiftInvariant scaledCube closedHalfSpace regionObservables
  plateauPairing pointOfUnit axisStep shift)
open YangMills.Construction.GibbsAtFixedSpacing (BorelProb linfNorm)
open YangMills.Construction.ReflectionPositivity.LatticeAtSpacing (IsErgodicState reflectionPositiveSet)
open YangMills.Construction.SmearingFilter (spectralRateConst spectralRateFn)
variable {a : ℝ}
def ScaledPair.transversePow (ν : Measure (GaugeField a)) (μ : Fin 4)
    (l : TransverseAxis μ) (m : ℤ) : ScaledPair.Hilb ν μ →L[ℂ] ScaledPair.Hilb ν μ :=
  (((ReflectionPair.site.opFamily (unitRepresentative ν) μ).B l ^ m :
    unitary (ScaledPair.Hilb ν μ →L[ℂ] ScaledPair.Hilb ν μ)) :
      ScaledPair.Hilb ν μ →L[ℂ] ScaledPair.Hilb ν μ)
def ScaledPair.energyMomentumOp (ν : Measure (GaugeField a)) (μ : Fin 4)
    (l : TransverseAxis μ) (k : ℕ+) :
    ScaledPair.Hilb ν μ →L[ℂ] ScaledPair.Hilb ν μ :=
  (1 - ScaledPair.transferOp ν μ ^ (k : ℕ)) ^ 2 -
    ScaledPair.transferOp ν μ ^ (k : ℕ) *
      ((2 : ℂ) • 1 - ScaledPair.transversePow ν μ l (k : ℤ) -
        ScaledPair.transversePow ν μ l (-(k : ℤ)))
def reflCorr (ν : BorelProb a) (μ : Fin 4) (F G : GaugeField a → ℂ) : ℂ :=
  ν.integral fun U => conj ((LatticeAtSpacing.coordinateReflect a μ).actOn F U) * G U
def shiftedReflCorr (ν : BorelProb a) (μ : Fin 4) (F : GaugeField a → ℂ) (v : LatticePoint a) : ℂ :=
  reflCorr ν μ F ((shift v).actOn F)
def fivePointCombination (ν : BorelProb a) (μ l : Fin 4) (k : ℕ+) (F : GaugeField a → ℂ) : ℂ :=
  shiftedReflCorr ν μ F 0 - 4 * shiftedReflCorr ν μ F ((k : ℕ) • axisStep a μ) +
    shiftedReflCorr ν μ F ((2 * (k : ℕ)) • axisStep a μ) +
    shiftedReflCorr ν μ F ((k : ℕ) • axisStep a μ + (k : ℕ) • axisStep a l) +
    shiftedReflCorr ν μ F ((k : ℕ) • axisStep a μ - (k : ℕ) • axisStep a l)
def scaledCubeSeparation (r : ℕ+) (y : LatticePoint a) : ℝ :=
  linfNorm (y : InfiniteLattice.AmbientSpace) / a - 2 * (r : ℝ)
def singleLatticeInputs : Prop :=
  ∀ (a : ℝ) (ha : 0 < a) (ν : BorelProb a), ν ∈ reflectionPositiveSet a →
    (∀ F : GaugeField a → ℂ, IsBoundedObservable F → ∀ s : LatticeSymmetry a,
      ν.integral (s.actOn F) = ν.integral F) ∧
    (∀ μ : Fin 4,
      (∀ F F' : GaugeField a → ℂ, IsLocalObservable F → F ∈ regionObservables a (closedHalfSpace μ) →
        IsLocalObservable F' → F' ∈ regionObservables a (closedHalfSpace μ) →
        ∀ (n : ℕ) (w : Fin 4 → ℤ), w μ = 0 →
        inner ℂ (ScaledPair.obsClass ν.1 μ ha F)
            ((ScaledPair.transferOp ν.1 μ ^ n * ScaledPair.shiftMonomial ν.1 μ w)
              (ScaledPair.obsClass ν.1 μ ha F')) =
          reflCorr ν μ F
            ((shift (pointOfUnit a (n • axisStep 1 μ + intPoint w))).actOn F')) ∧
      0 ≤ ScaledPair.transferOp ν.1 μ ∧ ScaledPair.transferOp ν.1 μ ≤ 1) ∧
    (∀ (μ : Fin 4) (l : TransverseAxis μ) (k : ℕ+),
      0 ≤ ScaledPair.energyMomentumOp ν.1 μ l k ∧
      ∀ F : GaugeField a → ℂ, IsLocalObservable F → F ∈ regionObservables a (closedHalfSpace μ) →
        0 ≤ fivePointCombination ν μ l.1 k F ∧
        fivePointCombination ν μ l.1 k F =
          inner ℂ (ScaledPair.obsClass ν.1 μ ha F)
            (ScaledPair.energyMomentumOp ν.1 μ l k
              (ScaledPair.obsClass ν.1 μ ha F))) ∧
    ((∀ u : ℝ, spectralRateFn u = spectralRateConst * (u ^ 2 + u ^ 3)) ∧
      ∀ r : ℕ+, ∀ A ∈ regionObservables a (scaledCube a r),
        ((∀ B ∈ regionObservables a (scaledCube a r), ∀ y : LatticePoint a,
            1 ≤ scaledCubeSeparation r y →
            ‖(ν.integral fun U => conj (A U) * (shift y).actOn B U) -
                plateauPairing ν.1 A B‖ ≤
              spectralRateFn ((r : ℝ) / scaledCubeSeparation r y) *
                scaledCubeReflectionSize ha ν.1 r A ^ (1 / 2 : ℝ) *
                scaledCubeReflectionSize ha ν.1 r B ^ (1 / 2 : ℝ)) ∧
          (∀ B ∈ regionObservables a (scaledCube a r),
            plateauPairing ν.1 A B = ν.integral fun U =>
              conj (condExpShiftInvariant ν.1 A U) * condExpShiftInvariant ν.1 B U) ∧
          IsGreatest (Set.range fun p : Fin 4 × axisReflectionGroup =>
              reflCorr ν p.1
                ((axisReflectionGroup.toLatticeSymmetry a p.2).actOn A)
                ((shift ((2 * (r : ℕ)) • axisStep a p.1)).actOn
                  ((axisReflectionGroup.toLatticeSymmetry a p.2).actOn A)))
            (scaledCubeReflectionSize ha ν.1 r A : ℂ) ∧
          0 ≤ scaledCubeReflectionSize ha ν.1 r A ∧
          ∀ (μ : Fin 4) (γ : axisReflectionGroup),
            reflCorr ν μ
                ((axisReflectionGroup.toLatticeSymmetry a γ).actOn A)
                ((shift ((2 * (r : ℕ)) • axisStep a μ)).actOn
                  ((axisReflectionGroup.toLatticeSymmetry a γ).actOn A)) =
              ((‖ScaledPair.cubeVector ν.1 μ ha r
                ((axisReflectionGroup.toLatticeSymmetry a γ).actOn A)‖ ^ 2 :
                  ℝ) : ℂ))) ∧
    (IsErgodicState ν →
      (∀ B : GaugeField a → ℂ, IsBoundedObservable B →
        condExpShiftInvariant ν.1 B =ᵐ[ν.1] fun _ => ν.integral B) ∧
      ∀ A B : GaugeField a → ℂ, IsBoundedObservable A → IsBoundedObservable B →
        plateauPairing ν.1 A B = conj (ν.integral A) * ν.integral B) ∧
    (∀ F : GaugeField a → ℂ, IsBoundedObservable F → ∀ (μ : Fin 4) (v : LatticePoint a),
      condExpShiftInvariant ν.1 ((LatticeAtSpacing.coordinateReflect a μ).actOn F)
          =ᵐ[ν.1] condExpShiftInvariant ν.1 F ∧
        condExpShiftInvariant ν.1 F =ᵐ[ν.1]
          condExpShiftInvariant ν.1 ((shift v).actOn F))
end YangMills.Construction.ReflectionPositivity.DirectionPictures
