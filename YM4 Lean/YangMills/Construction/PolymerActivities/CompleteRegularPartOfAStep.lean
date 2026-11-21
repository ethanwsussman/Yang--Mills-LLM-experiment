import YangMills.Construction.Lattice.BackgroundAndRecursionOfAStep
import YangMills.Construction.Lattice.DiracFactorAtABlockField
import YangMills.Construction.Lattice.GaugeFixingFactor
import YangMills.Construction.PolymerActivities.EffectiveActionOfALabel
import Mathlib
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open ParameterChoice Matrices
open AverageFibres (PositiveBondField submersionSet diracFibreMeasure)
namespace PeriodicLattice
structure CompletedSteps (L m K : ℕ) where
  unmarked : (i : ℕ) → RootedLocalActivities L m K i
  marked : (i : ℕ) → RootedLocalActivities L m K i
  remainder : ℕ → LocalActivities L m K
  unmarkedShift : ℕ → ℝ
  markedShift : ℕ → ℝ
variable {L m K : ℕ}
namespace CompletedSteps
variable (P : CompletedSteps L m K)
def regularSum (i : ℕ) : RootedLocalActivities L m K i :=
  fun X z Q => P.unmarked i X z Q + P.marked i X z Q
end CompletedSteps
structure ChoiceConstants (c : ChoiceUpToDegreeConstants) extends AnalyticityConstants where
  regRadius_eq : regRadius = c.εv
  regThreshold_eq : regThreshold = c.εBar
  blockExp_eq : blockExp = Nat.log c.L c.blockNumber
  gapExp_eq : gapExp = Nat.log c.L c.gapNumber
  sizeExp_eq : sizeExp = Nat.log c.L c.M₁
  cubeExp_eq : cubeExp = Nat.log c.L c.M
  gaugeBound_eq : gaugeBound = c.cubeSizeConst
  cubeFactor_eq : cubeFactor = c.Cg
  layerDecay_eq : layerDecay = c.βs
def ChoiceConstants.ofFullChoice (T : DerivedConstants) (a : FullChoice) :
    ChoiceConstants
      a.toChoiceUpToDegreeConstants where
  toAnalyticityConstants := AnalyticityConstants.ofChoice T a
  regRadius_eq := rfl
  regThreshold_eq := rfl
  blockExp_eq := rfl
  gapExp_eq := rfl
  sizeExp_eq := rfl
  cubeExp_eq := rfl
  gaugeBound_eq := rfl
  cubeFactor_eq := rfl
  layerDecay_eq := rfl
def coarseCubeDomains (r : ℕ) (x : ℕ → ℝ) (K m' i : ℕ) : Set (Set (FourTorus L m)) :=
  {X | X ∈ connectedRegions L m (coarseCubeIndex K m' i) ∧
    IsScaledCubeUnion K i (m' + Nat.log L (Thresholds.minBlockSize L r x i)) X}
def lastAgedLevel (L r : ℕ) (x : ℕ → ℝ) (m' k : ℕ) : ℕ :=
  sSup {i | 1 ≤ i ∧ i ≤ k ∧
    ((L : ℝ) ^ (k - i))⁻¹ * ((L : ℝ) ^ m' * (Thresholds.minBlockSize L r x i : ℝ)) ≤ L}
namespace CubesOfStep
variable (c : ChoiceUpToDegreeConstants) (x : ℕ → ℝ) {m K k : ℕ}
def pureStepData (V : BondAtLevel c.L m K k → ComplexMatrix2)
    (W : BondAtLevel c.L m K (k + 1) → ComplexMatrix2) : StepData c.L m K k where
  domains := fun _ => univ
  region := univ
  lowerFields := fun _ _ => 1
  current := V
  next := W
def torusFluctuationTest (V : BondAtLevel c.L m K k → ComplexMatrix2)
    (W : BondAtLevel c.L m K (k + 1) → ComplexMatrix2) : ℝ :=
  ∏ᶠ b ∈ nonPivotBonds K k (univ : Set (FourTorus c.L m)),
    bondIndicator c x (pureStepData c V W) b
def stepWeight (V : BondAtLevel c.L m K k → ComplexMatrix2)
    (W : BondAtLevel c.L m K (k + 1) → ComplexMatrix2) : ℝ :=
  axialGaugeFactor c.A₀ c.𝔭₀ x K k V univ * torusFluctuationTest c x V W
def fibreIntegrand (w : (BondAtLevel c.L m K k → ComplexMatrix2) → ℝ)
    (F : (BondAtLevel c.L m K k → ComplexMatrix2) → ℂ)
    (W : BondAtLevel c.L m K (k + 1) → ComplexMatrix2) (p : PositiveBondField c.L m K k) : ℂ :=
  open Classical in
  if blockAverageStep (Averaging.smoothingRadius c.L) k (gaugeFieldOfPositive p) = W ∧
      w (gaugeFieldOfPositive p) ≠ 0 then
    (w (gaugeFieldOfPositive p) : ℂ) * F (gaugeFieldOfPositive p)
  else 0
structure HasFibreIntegral (w : (BondAtLevel c.L m K k → ComplexMatrix2) → ℝ)
    (𝒟 : Set (BondAtLevel c.L m K k → ComplexMatrix2))
    (F : (BondAtLevel c.L m K k → ComplexMatrix2) → ℂ)
    (W : BondAtLevel c.L m K (k + 1) → ComplexMatrix2) (q : PositiveBondField c.L m K (k + 1))
    (a : ℂ) : Prop where
  mem_domain : ∀ V ∈ gaugeFieldsAtLevel c.L m K k,
    blockAverageStep (Averaging.smoothingRadius c.L) k V = W → w V ≠ 0 → V ∈ 𝒟
  measurable : Measurable (fibreIntegrand c w F W)
  eq_zero_of_not_mem : ∀ p, p ∉ submersionSet c.L m K k → fibreIntegrand c w F W p = 0
  integrable : Integrable (fibreIntegrand c w F W) (diracFibreMeasure q)
  integral_eq : ∫ p, fibreIntegrand c w F W p ∂diracFibreMeasure q = a
def HasStepIntegral (𝒟 : Set (BondAtLevel c.L m K k → ComplexMatrix2))
    (F : (BondAtLevel c.L m K k → ComplexMatrix2) → ℂ)
    (W : BondAtLevel c.L m K (k + 1) → ComplexMatrix2) (a : ℂ) : Prop :=
  ∃ q : PositiveBondField c.L m K (k + 1), gaugeFieldOfPositive q = W ∧
    HasFibreIntegral c (fun V => stepWeight c x V W) 𝒟 F W q a
def StepIntegralDefined (𝒟 : Set (BondAtLevel c.L m K k → ComplexMatrix2))
    (F : (BondAtLevel c.L m K k → ComplexMatrix2) → ℂ)
    (W : BondAtLevel c.L m K (k + 1) → ComplexMatrix2) : Prop :=
  ∃ a, HasStepIntegral c x 𝒟 F W a
def stepIntegral (𝒟 : Set (BondAtLevel c.L m K k → ComplexMatrix2))
    (F : (BondAtLevel c.L m K k → ComplexMatrix2) → ℂ)
    (W : BondAtLevel c.L m K (k + 1) → ComplexMatrix2) : ℂ :=
  Classical.epsilon fun a => HasStepIntegral c x 𝒟 F W a
def HasTorusBackground {i : ℕ} (V : BondAtLevel c.L m K i → ComplexMatrix2) : Prop :=
  CriticalFieldsFormOneOrbit (Averaging.smoothingRadius c.L) c.εv K i (fun _ => univ)
    (datumOnLevel K i V)
def torusBackground {i : ℕ} (V : BondAtLevel c.L m K i → ComplexMatrix2) :
    BondAtLevel c.L m K 0 → ComplexMatrix2 :=
  PeriodicLattice.backgroundField (Averaging.smoothingRadius c.L) c.εv K i V
variable (S : (BondAtLevel c.L m K 0 → ComplexMatrix2) → ℂ)
  (Sdefined : (BondAtLevel c.L m K 0 → ComplexMatrix2) → Prop)
def regularIntegrandDomain : Set (BondAtLevel c.L m K k → ComplexMatrix2) :=
  {V | HasTorusBackground c V ∧ Sdefined (torusBackground c V)}
def regularIntegrand (V : BondAtLevel c.L m K k → ComplexMatrix2) : ℂ :=
  Complex.exp (-(x k : ℂ) * totalEnergy (torusBackground c V) + S (torusBackground c V))
def regularPartOf (W : BondAtLevel c.L m K (k + 1) → ComplexMatrix2) : ℂ :=
  Complex.log (stepIntegral c x (regularIntegrandDomain c Sdefined)
      (regularIntegrand c x S) W) +
    (x k : ℂ) * totalEnergy (torusBackground c W) - S (torusBackground c W)
def regularPartDomainOf : Set (BondAtLevel c.L m K (k + 1) → ComplexMatrix2) :=
  {W | StepIntegralDefined c x (regularIntegrandDomain c Sdefined) (regularIntegrand c x S) W ∧
    (∃ r : ℝ, 0 < r ∧
      stepIntegral c x (regularIntegrandDomain c Sdefined) (regularIntegrand c x S) W = r) ∧
    HasTorusBackground c W ∧ Sdefined (torusBackground c W)}
variable (N : ChoiceConstants c) (C : Fin 2 → ℝ) (s : ActivityDomainKind)
  (P : CompletedSteps c.L m K)
structure AreCompletedFamilies (k : ℕ) (E₀ : ℝ) : Prop where
  unmarked_mem : ∀ i ∈ Finset.Icc 1 k, N.IsRootedActivityFamily C c.q x s K i
    (connectedRegions c.L m (coarseCubeIndex K N.cubeExp i)) (P.unmarked i)
  marked_mem : ∀ i ∈ Finset.Icc 1 k, N.IsRootedActivityFamily C c.q x s K i
    (connectedRegions c.L m (coarseCubeIndex K N.cubeExp i)) (P.marked i)
  regular_mem : ∀ i ∈ Finset.Icc 1 k, P.regularSum i ∈ N.rootedBoundedClass C c.q x s K i c.κ E₀
    (connectedRegions c.L m (coarseCubeIndex K N.cubeExp i))
  remainder_mem : ∀ i ∈ Finset.Icc 1 k, P.remainder i ∈ N.couplingClass C c.q x s K i c.κ c.κ₀
    (coarseCubeDomains c.r x K N.cubeExp i)
def backgroundPairRestrict (W : BondAtLevel c.L m K (k + 1) → ComplexMatrix2)
    (X : Set (FourTorus c.L m)) : FieldCurrentPair c.L m K :=
  restrictPairTo X (configurationPair (k + 1) (torusBackground c W))
end CubesOfStep
end PeriodicLattice
end YangMills.Construction
