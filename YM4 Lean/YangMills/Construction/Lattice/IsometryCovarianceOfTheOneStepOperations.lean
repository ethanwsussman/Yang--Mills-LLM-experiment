import YangMills.Construction.Averaging.SmoothingRadius
import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.LinearisedConstraint
import YangMills.Construction.Lattice.MapsOfTheTwistedAction
import Mathlib
set_option autoImplicit false
open Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ} {j j' : ℤ}
def IsOrientedImage (σ : FourTorus L m ≃ FourTorus L m) (b b' : Bond L m j) : Prop :=
  b'.IsPositivelyOriented ∧ (b' = bondImage σ b ∨ b' = (bondImage σ b).opposite)
def orientedImage (σ : FourTorus L m ≃ FourTorus L m) (Γ : Set (Bond L m j)) : Set (Bond L m j) :=
  {b' | ∃ b ∈ Γ, IsOrientedImage σ b b'}
structure LinearizedObjectsDefined (r : ℝ) (V : Bond L m j' → Matrices.ComplexMatrix2)
    (Γ : Set (Bond L m j)) : Prop where
  positive : ∀ b ∈ Γ, b.IsPositivelyOriented
  real_defined : RealConstraintDefined r V Γ
  complex_defined : ComplexConstraintDefined V Γ
  pivotCoeff_invertible : ∀ b ∈ Γ, PivotCoeffInvertible V b
def twistedTransportSupportForm (σ : FourTorus L m ≃ FourTorus L m)
    (V : Bond L m j' → Matrices.ComplexMatrix2)
    {Γ : Set (Bond L m j)} (F : SupportBond j' Γ → Matrices.ComplexMatrix2) :
    SupportBond j' (orientedImage σ Γ) → Matrices.ComplexMatrix2 :=
  fun e => twistedTransportForm σ V (extendForm F) e
def twistedTransportCoarse (σ : FourTorus L m ≃ FourTorus L m)
    (W : Bond L m j → Matrices.ComplexMatrix2)
    {Γ : Set (Bond L m j)} (f : ↥Γ → Matrices.ComplexMatrix2) :
    ↥(orientedImage σ Γ) → Matrices.ComplexMatrix2 :=
  fun e => twistedFormValue σ W (Function.extend Subtype.val f 0) e
structure IsometryCovariantAt (σ : FourTorus L m ≃ FourTorus L m) {K k : ℕ}
    (V : BondAtLevel L m K k → Matrices.ComplexMatrix2)
    (Γ : Set (BondAtLevel L m K (k + 1))) : Prop where
  defined : LinearizedObjectsDefined (Averaging.smoothingRadius L) (transportGaugeField σ V)
    (orientedImage σ Γ)
  linearized_comm : ∀ A : BondAtLevel L m K k → Matrices.ComplexMatrix2,
    IsBondForm complexLieAlgebra A →
    ∀ e ∈ orientedImage σ Γ,
      linearizedConstraint (transportGaugeField σ V) (twistedTransportForm σ V A) e =
        twistedTransportForm σ (blockAverage (Averaging.smoothingRadius L) V)
          (linearizedConstraint V A) e
  linearizedReal_comm : ∀ A : BondAtLevel L m K k → Matrices.ComplexMatrix2,
    IsBondForm compactLieAlgebra A →
    ∀ e ∈ orientedImage σ Γ,
      linearizedConstraintReal (Averaging.smoothingRadius L) (transportGaugeField σ V)
          (twistedTransportForm σ V A) e =
        twistedTransportForm σ (blockAverage (Averaging.smoothingRadius L) V)
          (linearizedConstraintReal (Averaging.smoothingRadius L) V A) e
  constraintMap_comm : ∀ F : BondAtLevel L m K k → Matrices.ComplexMatrix2,
    IsBondForm complexLieAlgebra F →
    ∀ b ∈ Γ, ∀ e, IsOrientedImage σ b e → ConstraintMapDefined V F b →
      ConstraintMapDefined (transportGaugeField σ V) (twistedTransportForm σ V F) e →
      constraintMap (transportGaugeField σ V) (twistedTransportForm σ V F) e =
        twistedFormValue σ (blockAverage (Averaging.smoothingRadius L) V) (constraintMap V F) e
  constraintMap_defined_iff : ∀ F : BondAtLevel L m K k → Matrices.ComplexMatrix2,
    IsBondForm compactLieAlgebra F →
    ∀ b ∈ Γ, ∀ e, IsOrientedImage σ b e →
      (ConstraintMapDefined V F b ↔
        ConstraintMapDefined (transportGaugeField σ V) (twistedTransportForm σ V F) e)
  eliminate_comm : ∀ A : BondAtLevel L m K k → Matrices.ComplexMatrix2,
    IsBondForm complexLieAlgebra A →
    eliminate (transportGaugeField σ V) (orientedImage σ Γ) (twistedTransportForm σ V A) =
      twistedTransportForm σ V (eliminate V Γ A)
  pivotCorrectionLift_comm : ∀ f : ↥Γ → Matrices.ComplexMatrix2,
    (∀ b, f b ∈ complexLieAlgebra) →
    pivotCorrectionLift (transportGaugeField σ V) (orientedImage σ Γ)
        (twistedTransportCoarse σ (blockAverage (Averaging.smoothingRadius L) V) f) =
      twistedTransportSupportForm σ V (pivotCorrectionLift V Γ f)
  linearizingCorrection_comm :
    ∀ᶠ F in 𝓝[(supportForms (levelDepth K k) Γ :
        Set (SupportBond (levelDepth K k) Γ → Matrices.ComplexMatrix2))] 0,
      linearizingCorrection (transportGaugeField σ V) (orientedImage σ Γ)
          (twistedTransportSupportForm σ V F) =
        twistedTransportCoarse σ (blockAverage (Averaging.smoothingRadius L) V)
          (linearizingCorrection V Γ F)
  linearizingChange_comm :
    ∀ᶠ F in 𝓝[(supportForms (levelDepth K k) Γ :
        Set (SupportBond (levelDepth K k) Γ → Matrices.ComplexMatrix2))] 0,
      linearizingChange (transportGaugeField σ V) (orientedImage σ Γ)
          (twistedTransportSupportForm σ V F) =
        twistedTransportSupportForm σ V (linearizingChange V Γ F)
  pivotCoeff_conj : ∀ b ∈ Γ, ∀ e, IsOrientedImage σ b e →
    ∀ X : ↥Matrices.ComplexMatrix2.traceless,
    ∃ Y : ↥Matrices.ComplexMatrix2.traceless, (Y : Matrices.ComplexMatrix2) = pivotCoeff V b X ∧
      pivotCoeff (transportGaugeField σ V) e
          (twistedLinkMap σ V (pivot b) X : ↥Matrices.ComplexMatrix2.traceless) =
        (twistedLinkMap σ (blockAverage (Averaging.smoothingRadius L) V) b Y :
          ↥Matrices.ComplexMatrix2.traceless)
  eliminationWeight_eq : ∀ b ∈ Γ, ∀ e, IsOrientedImage σ b e →
    eliminationWeight (transportGaugeField σ V) e = eliminationWeight V b
  constraintBilinear_comm : ∀ F₁ F₂ : BondAtLevel L m K k → Matrices.ComplexMatrix2,
    IsBondForm complexLieAlgebra F₁ →
    IsBondForm complexLieAlgebra F₂ → ∀ e ∈ orientedImage σ Γ,
      constraintBilinear (transportGaugeField σ V)
          (twistedTransportForm σ V F₁) (twistedTransportForm σ V F₂) e =
        twistedFormValue σ (blockAverage (Averaging.smoothingRadius L) V)
          (constraintBilinear V F₁ F₂) e
def IsometryCovarianceOneStep : Prop :=
  ∀ (L m K k : ℕ) (i : ℤ) (σ : FourTorus L m ≃ FourTorus L m),
    Conventions.IsAdmissibleBlockingFactor L → 0 < m →
    -(m : ℤ) ≤ i → σ ∈ latticeIsometries L m i → k < K → i ≤ levelDepth K (k + 1) →
    ∀ (V : BondAtLevel L m K k → Matrices.ComplexMatrix2) (Γ : Set (BondAtLevel L m K (k + 1))),
      LinearizedObjectsDefined (Averaging.smoothingRadius L) V Γ → IsometryCovariantAt σ V Γ
end YangMills.Construction.PeriodicLattice
