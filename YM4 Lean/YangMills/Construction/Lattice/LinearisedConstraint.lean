import YangMills.Construction.Lattice.BlockAveraging
import YangMills.Construction.Matrices.GroupLieProducts
import Mathlib
open Set
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open YangMills.Construction.Matrices
variable {L m : ℕ} {j j' : ℤ}
def logRatioCurve (M : (Bond L m j' → ComplexMatrix2) → Bond L m j → ComplexMatrix2)
    (V A : Bond L m j' → ComplexMatrix2) (c : Bond L m j) : ℝ → ComplexMatrix2 :=
  fun t => ComplexMatrix2.logSeries (M (expTwist ((t : ℂ) • A) V) c * (M V c)⁻¹)
def constraintDerivativeForm (M : (Bond L m j' → ComplexMatrix2) → Bond L m j → ComplexMatrix2)
    (V A : Bond L m j' → ComplexMatrix2) : Bond L m j → ComplexMatrix2 :=
  open Classical in
  fun c => if c.IsPositivelyOriented then (Complex.I * (L : ℂ))⁻¹ • deriv (logRatioCurve M V A c) 0
    else -((Complex.I * (L : ℂ))⁻¹ • deriv (logRatioCurve M V A c.opposite) 0)
def linearizedConstraint (V A : Bond L m j' → ComplexMatrix2) : Bond L m j → ComplexMatrix2 :=
  constraintDerivativeForm complexBlockAverage V A
def linearizedConstraintReal (ω : ℝ) (V A : Bond L m j' → ComplexMatrix2) :
    Bond L m j → ComplexMatrix2 :=
  constraintDerivativeForm (blockAverage ω) V A
def IsRegularAveragingNear (ω : ℝ) (V : Bond L m j' → ComplexMatrix2) (c : Bond L m j) : Prop :=
  IsGaugeField compactGaugeGroup (bondsInDoubleBlock c) V ∧
    ∀ᶠ U in 𝓝[{U | IsGaugeField compactGaugeGroup (bondsInDoubleBlock c) U}] V,
      IsRegularAveragingCase ω U c
def RealConstraintDefined (ω : ℝ) (V : Bond L m j' → ComplexMatrix2) (S : Set (Bond L m j)) :
    Prop :=
  ∀ c ∈ S, IsRegularAveragingNear ω V c ∧ ∀ A : Bond L m j' → ComplexMatrix2,
    IsBondForm compactLieAlgebra A →
      DifferentiableAt ℝ (logRatioCurve (blockAverage ω) V A c) 0
def ComplexConstraintDefined (V : Bond L m j' → ComplexMatrix2) (S : Set (Bond L m j)) : Prop :=
  ∀ c ∈ S, V ∈ complexAveragingDomainNearOne c
def singleBondForm (b : Bond L m j') (X : ComplexMatrix2) : Bond L m j' → ComplexMatrix2 :=
  open Classical in
  fun e => if e = b then X else if e = b.opposite then -X else 0
def pivotCoeff (V : Bond L m j' → ComplexMatrix2) (c : Bond L m j) (X : ComplexMatrix2) :
    ComplexMatrix2 :=
  linearizedConstraint V (singleBondForm (pivot c) X) c
def restrictEndomorphism {𝕜 E : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (W : Submodule 𝕜 E) (f : E → E) : Module.End 𝕜 W :=
  open Classical in
  if h : ∃ T : Module.End 𝕜 W, ∀ x : W, (T x : E) = f x then h.choose else 0
def PivotCoeffInvertible (V : Bond L m j' → ComplexMatrix2) (c : Bond L m j) : Prop :=
  ∃ T : ComplexMatrix2.traceless ≃ₗ[ℂ] ComplexMatrix2.traceless,
    ∀ X : ComplexMatrix2.traceless, (T X : ComplexMatrix2) = pivotCoeff V c X
def pivotCoeffInv (V : Bond L m j' → ComplexMatrix2) (c : Bond L m j) :
    ComplexMatrix2 → ComplexMatrix2 :=
  Function.invFunOn (pivotCoeff V c) (ComplexMatrix2.traceless : Set ComplexMatrix2)
def IsPivotBondOf (S : Set (Bond L m j)) (b : Bond L m j') : Prop :=
  ∃ c ∈ S, b = pivot c ∨ b = (pivot c).opposite
def IsEliminatedForm (V : Bond L m j' → ComplexMatrix2) (S : Set (Bond L m j))
    (A B : Bond L m j' → ComplexMatrix2) : Prop :=
  (∀ b, ¬ IsPivotBondOf S b → B b = A b) ∧
    (∀ c ∈ S, B (pivot c) ∈ ComplexMatrix2.traceless ∧ B (pivot c).opposite = -B (pivot c)) ∧
    ∀ c ∈ S, linearizedConstraint V B c = 0
def eliminate (V : Bond L m j' → ComplexMatrix2) (S : Set (Bond L m j))
    (A : Bond L m j' → ComplexMatrix2) : Bond L m j' → ComplexMatrix2 :=
  Classical.epsilon (IsEliminatedForm V S A)
def eliminationWeight (V : Bond L m j' → ComplexMatrix2) (c : Bond L m j) : ℝ :=
  open Classical in
  if IsGaugeField compactGaugeGroup (bondsInDoubleBlock c) V then
    |LinearMap.det (restrictEndomorphism ComplexMatrix2.hermitianTraceless (pivotCoeff V c))|⁻¹
  else ‖LinearMap.det (restrictEndomorphism ComplexMatrix2.traceless (pivotCoeff V c))‖⁻¹
def eliminationWeightProd (V : Bond L m j' → ComplexMatrix2) (S : Set (Bond L m j)) : ℝ :=
  ∏ᶠ c ∈ S, eliminationWeight V c
def doubleBlockSupport (j' : ℤ) (S : Set (Bond L m j)) : Set (Bond L m j') :=
  ⋃ c ∈ S, bondsInDoubleBlock c
abbrev SupportBond (j' : ℤ) (S : Set (Bond L m j)) : Type :=
  {b : Bond L m j' // b ∈ doubleBlockSupport j' S ∧ b.IsPositivelyOriented}
def extendForm {S : Set (Bond L m j)} (B : SupportBond j' S → ComplexMatrix2) :
    Bond L m j' → ComplexMatrix2 :=
  open Classical in
  fun b => if h : b ∈ doubleBlockSupport j' S ∧ b.IsPositivelyOriented then B ⟨b, h⟩
    else if h' : b.opposite ∈ doubleBlockSupport j' S ∧ b.opposite.IsPositivelyOriented then
      -B ⟨b.opposite, h'⟩
    else 0
def constraintMap (V B' : Bond L m j' → ComplexMatrix2) (c : Bond L m j) : ComplexMatrix2 :=
  Complex.I⁻¹ • ComplexMatrix2.logSeries
    (complexBlockAverage (expTwist B' V) c * (complexBlockAverage V c)⁻¹)
def ConstraintMapDefined (V B' : Bond L m j' → ComplexMatrix2) (c : Bond L m j) : Prop :=
  expTwist B' V ∈ complexAveragingDomainNearOne c ∧
    complexBlockAverage (expTwist B' V) c * (complexBlockAverage V c)⁻¹ ∈ ComplexMatrix2.logBall
def constraintQuadratic (V B' : Bond L m j' → ComplexMatrix2) (c : Bond L m j) : ComplexMatrix2 :=
  (1 / 2 : ℂ) • iteratedDeriv 2 (fun t : ℂ => constraintMap V (t • B') c) 0
def constraintBilinear (V B₁ B₂ : Bond L m j' → ComplexMatrix2) (c : Bond L m j) :
    ComplexMatrix2 :=
  (1 / 2 : ℂ) • (constraintQuadratic V (B₁ + B₂) c - constraintQuadratic V B₁ c -
    constraintQuadratic V B₂ c)
def pivotCorrectionLift (V : Bond L m j' → ComplexMatrix2) (S : Set (Bond L m j))
    (ν : ↥S → ComplexMatrix2) : SupportBond j' S → ComplexMatrix2 :=
  open Classical in
  fun b => if h : ∃ c : ↥S, (b : Bond L m j') = pivot (c : Bond L m j) then
      ((L : ℂ)⁻¹) • pivotCoeffInv V (h.choose : Bond L m j) (ν h.choose)
    else 0
def IsHolomorphicOnSupportForms {S : Set (Bond L m j)} (N : Set (SupportBond j' S → ComplexMatrix2))
    (D : (SupportBond j' S → ComplexMatrix2) → ↥S → ComplexMatrix2) : Prop :=
  ∃ (_ : Fintype (SupportBond j' S)) (_ : Fintype ↥S),
    ∀ (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (ν : ↥S ≃ Fin (Fintype.card ↥S)),
      GroupLieProduct.IsHolomorphicOnTraceless b (GroupLieProduct.matrixPiEquiv ν) N D
def IsLinearizingCorrection (V : Bond L m j' → ComplexMatrix2) (S : Set (Bond L m j))
    (N : Set (SupportBond j' S → ComplexMatrix2))
    (D : (SupportBond j' S → ComplexMatrix2) → ↥S → ComplexMatrix2) : Prop :=
  0 ∈ N ∧ IsHolomorphicOnSupportForms N D ∧ (∀ B ∈ N, D B ∈ GroupLieProduct.tracelessPi ↥S) ∧
    D 0 = 0 ∧ ∀ B ∈ N, ∀ c : ↥S,
      ConstraintMapDefined V (extendForm (B - pivotCorrectionLift V S (D B))) (c : Bond L m j) ∧
        constraintMap V (extendForm (B - pivotCorrectionLift V S (D B))) (c : Bond L m j) =
          (L : ℂ) • linearizedConstraint V (extendForm B) (c : Bond L m j)
def linearizingCorrection (V : Bond L m j' → ComplexMatrix2) (S : Set (Bond L m j)) :
    (SupportBond j' S → ComplexMatrix2) → ↥S → ComplexMatrix2 :=
  Classical.epsilon fun D => ∃ N, IsLinearizingCorrection V S N D
def linearizingChange (V : Bond L m j' → ComplexMatrix2) (S : Set (Bond L m j))
    (B : SupportBond j' S → ComplexMatrix2) : SupportBond j' S → ComplexMatrix2 :=
  B - pivotCorrectionLift V S (linearizingCorrection V S B)
def supportForms (j' : ℤ) (S : Set (Bond L m j)) :
    Submodule ℂ (SupportBond j' S → ComplexMatrix2) :=
  Submodule.pi univ fun _ => ComplexMatrix2.traceless
end YangMills.Construction.PeriodicLattice
