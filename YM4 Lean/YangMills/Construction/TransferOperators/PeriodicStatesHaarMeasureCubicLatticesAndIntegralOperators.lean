import YangMills.Construction.TransferOperators.CubicToriAndProductsOfOperatorsOnPowersOfG
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory
open InfiniteLattice SpinHarmonics Schatten Matrices.ComplexMatrix2
namespace TransferOperators.GibbsHaarKernels
def invertAt {J : Type} (c : J) (u : J → specialUnitary) : J → specialUnitary :=
  open Classical in fun b => if b = c then (u b)⁻¹ else u b
def kernelConvolution {J : Type} [Countable J]
    (A A' : (J → specialUnitary) × (J → specialUnitary) → ℂ) :
    (J → specialUnitary) × (J → specialUnitary) → ℂ :=
  fun z => ∫ w, A (z.1, w) * A' (w, z.2) ∂haarPi J
def GibbsStatesCharacterized (β : ℝ) : Prop :=
  ∀ ν : Measure (GaugeField 1), IsProbabilityMeasure ν →
    (IsGibbs β ν ↔ ν ∈ gibbsClass zero_lt_one β) ∧
    (IsPeriodicGibbs β ν ↔ ν ∈ periodicGibbsClass zero_lt_one β) ∧
    (ν ∈ periodicGibbsClass zero_lt_one β ↔
      ∃ Q : AddSubgroup (LatticePoint 1), Q.FiniteIndex ∧
        ν ∈ subgroupInvariantGibbsClass zero_lt_one β Q)
def HaarPiInvariance (J : Type) [Finite J] : Prop :=
  (∀ g g' : J → specialUnitary,
    MeasurePreserving (fun (u : J → specialUnitary) (b : J) => g b * u b * g' b)
      (haarPi J) (haarPi J)) ∧
  (∀ c : J, MeasurePreserving (invertAt c) (haarPi J) (haarPi J)) ∧
  (∀ O : Set (J → specialUnitary), IsOpen O → O.Nonempty → 0 < haarPi J O) ∧
  ∀ f f' : (J → specialUnitary) → ℂ, Continuous f → Continuous f' →
    f =ᵐ[haarPi J] f' → f = f'
def CubicPeriodSublatticeIffThreeLe : Prop :=
  ∀ s : ℕ, 1 ≤ s →
    ((∃ Γ : PeriodSublattice 1, Γ.periods = cubicSublattice 1 (s : ℝ)) ↔ 3 ≤ s)
def ContinuousKernelOperatorProps (J : Type) [Finite J]
    (A : (J → specialUnitary) × (J → specialUnitary) → ℂ) : Prop :=
  (∀ φ : HaarL2 J, Continuous (kernelApply (haarPi J) A φ)) ∧
  HasKernel (haarPi J) A (kernelOp (haarPi J) A) ∧
  ‖kernelOp (haarPi J) A‖ ≤ ⨆ z, ‖A z‖ ∧
  ((∀ z, (A z).im = 0) → IsRealPreserving (kernelOp (haarPi J) A)) ∧
  ((∀ z, (A z).im = 0) → (∀ u u', A (u, u') = A (u', u)) →
    IsSymmetricOp (kernelOp (haarPi J) A))
def ContinuousKernelCompAndUniqueness (J : Type) [Finite J] : Prop :=
  (∀ A A' : (J → specialUnitary) × (J → specialUnitary) → ℂ, Continuous A → Continuous A' →
    Continuous (kernelConvolution A A') ∧
      (kernelOp (haarPi J) A).comp (kernelOp (haarPi J) A') =
        kernelOp (haarPi J) (kernelConvolution A A')) ∧
  ∀ A A' : (J → specialUnitary) × (J → specialUnitary) → ℂ, Continuous A → Continuous A' →
    kernelOp (haarPi J) A = kernelOp (haarPi J) A' → A = A'
def Statement : Prop :=
  (∀ β : ℝ, 0 < β → GibbsStatesCharacterized β) ∧
  (∀ (J : Type) [Finite J] [Nonempty J], HaarPiInvariance J) ∧
  CubicPeriodSublatticeIffThreeLe ∧
  (∀ (J : Type) [Finite J] [Nonempty J],
    (∀ A : (J → specialUnitary) × (J → specialUnitary) → ℂ, Continuous A →
      ContinuousKernelOperatorProps J A) ∧
      ContinuousKernelCompAndUniqueness J)
end TransferOperators.GibbsHaarKernels
end YangMills.Construction
end
