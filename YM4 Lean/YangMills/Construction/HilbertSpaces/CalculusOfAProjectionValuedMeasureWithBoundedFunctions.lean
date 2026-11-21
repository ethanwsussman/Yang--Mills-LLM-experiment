import YangMills.Construction.EuclideanSpectral.ProjMeasureBoundedIntegral
import YangMills.Construction.HilbertSpaces.CompletionsAdjointsProjectionValuedMeasuresAndWeakIntegrals
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology
open scoped ComplexConjugate InnerProductSpace
noncomputable section
namespace YangMills.Construction
namespace PVMCalculus
open OneLoopNotation ComplexHilbert HilbertToolkit ProjectionMeasures
def IsFinPosBorelMeasure (ν : FourBorelSet → ℂ) : Prop :=
  ∃ m : Measure (Fin 4 → ℝ), IsFiniteMeasure m ∧ ∀ S : FourBorelSet, ν S = ((m S.1).toReal : ℂ)
def dotFour (a x : Fin 4 → ℝ) : ℝ := ∑ k, a k * x k
def expChar (a x : Fin 4 → ℝ) : ℂ := Complex.exp (Complex.I * (dotFour a x : ℂ))
def ofEuclideanBorel (B : EuclideanSpectral.BorelSubset 4) : FourBorelSet :=
  ⟨MeasurableEquiv.toLp 2 (Fin 4 → ℝ) ⁻¹' B.1, (MeasurableEquiv.toLp 2 (Fin 4 → ℝ)).measurable B.2⟩
def ComplexMeasureDeterminedByCharFun : Prop :=
  ∀ ν : FourBorelSet → ℂ, IsFinComplexMeasure ν →
    (∀ a : Fin 4 → ℝ, complexMeasureIntegral ν (expChar a) = 0) → ∀ S : FourBorelSet, ν S = 0
section Calculus
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
def HasWeakIntegrals (P : FourBorelSet → BddOp H) (f : (Fin 4 → ℝ) → ℂ)
    (A : BddOp H) : Prop :=
  ∀ x y : H, ⟪x, A y⟫_ℂ = complexMeasureIntegral (spectralScalarMeasure P x y) f
def pvmIntegral (P : FourBorelSet → BddOp H) (f : (Fin 4 → ℝ) → ℂ) : BddOp H :=
  Classical.epsilon (HasWeakIntegrals P f)
def ScalarMeasureFacts (P : FourBorelSet → BddOp H) (S₀ : FourBorelSet) : Prop :=
  P ⟨∅, MeasurableSet.empty⟩ = 0 ∧
  (∀ S T : FourBorelSet, P S * P T = P ⟨S.1 ∩ T.1, S.2.inter T.2⟩) ∧
  (∀ x : H, IsFinPosBorelMeasure (spectralScalarMeasure P x x) ∧
    spectralScalarMeasure P x x FourBorelSet.univ = ((‖x‖ ^ 2 : ℝ) : ℂ) ∧
    spectralScalarMeasure P x x S₀.compl = 0) ∧
  ∀ x y : H,
    (∀ S : FourBorelSet, spectralScalarMeasure P x y S =
      (1 / 4 : ℂ) * ∑ k ∈ Finset.range 4, Complex.I ^ (-(k : ℤ)) *
        spectralScalarMeasure P (x + Complex.I ^ k • y) (x + Complex.I ^ k • y) S) ∧
    IsFinComplexMeasure (spectralScalarMeasure P x y)
def PvmIntegralBasic (P : FourBorelSet → BddOp H) (S₀ : FourBorelSet) : Prop :=
  (∀ f, IsBddMeasurableFun f →
    HasWeakIntegrals P f (pvmIntegral P f) ∧
    (∀ A, HasWeakIntegrals P f A → A = pvmIntegral P f) ∧
    opNormOf (pvmIntegral P f) ≤ ⨆ x : S₀.1, ‖f x‖) ∧
  ∀ (c d : ℂ) (f g : (Fin 4 → ℝ) → ℂ), IsBddMeasurableFun f → IsBddMeasurableFun g →
    pvmIntegral P (fun x => c * f x + d * g x) =
      c • pvmIntegral P f + d • pvmIntegral P g
def PvmIntegralRules (P : FourBorelSet → BddOp H) : Prop :=
  (∀ f g : (Fin 4 → ℝ) → ℂ, IsBddMeasurableFun f → IsBddMeasurableFun g →
    pvmIntegral P (fun x => f x * g x) = pvmIntegral P f * pvmIntegral P g) ∧
  (∀ f : (Fin 4 → ℝ) → ℂ, IsBddMeasurableFun f →
    adjointOp (pvmIntegral P f) = pvmIntegral P (fun x => conj (f x))) ∧
  (∀ S : FourBorelSet, pvmIntegral P (S.1.indicator fun _ => (1 : ℂ)) = P S) ∧
  pvmIntegral P (fun _ => (1 : ℂ)) = idOp H
def PvmIntegralNormAndConvergence (P : FourBorelSet → BddOp H) (S₀ : FourBorelSet) : Prop :=
  (∀ (f : (Fin 4 → ℝ) → ℂ), IsBddMeasurableFun f → ∀ x : H,
    ((‖pvmIntegral P f x‖ ^ 2 : ℝ) : ℂ) =
      complexMeasureIntegral (spectralScalarMeasure P x x) (fun p => ((‖f p‖ ^ 2 : ℝ) : ℂ))) ∧
  ∀ (T : Type) (g : T → (Fin 4 → ℝ) → ℂ) (s : ℕ → T) (f : (Fin 4 → ℝ) → ℂ),
    (∀ t, IsBddMeasurableFun (g t)) →
    (∃ b : ℝ, ∀ t, ∀ p ∈ S₀.1, ‖g t p‖ ≤ b) →
    (∀ p ∈ S₀.1, Tendsto (fun n => g (s n) p) atTop (𝓝 (f p))) →
      (∀ x : H, Tendsto (fun n => pvmIntegral P (g (s n)) x) atTop
        (𝓝 (pvmIntegral P (S₀.1.indicator f) x))) ∧
      (IsBddMeasurableFun f → ∀ x : H, Tendsto (fun n => pvmIntegral P (g (s n)) x) atTop
        (𝓝 (pvmIntegral P f x)))
def pushforward (P : FourBorelSet → BddOp H) (φ : (Fin 4 → ℝ) → (Fin 4 → ℝ))
    (hφ : Measurable φ) (S : FourBorelSet) : BddOp H :=
  P ⟨φ ⁻¹' S.1, hφ S.2⟩
def PushforwardFacts (P : FourBorelSet → BddOp H) (S₀ : FourBorelSet) : Prop :=
  ∀ (φ : (Fin 4 → ℝ) → (Fin 4 → ℝ)) (hφ : Measurable φ),
    IsPVM (pushforward P φ hφ) ∧
    (∀ S₁ : FourBorelSet, S₀.1 ⊆ φ ⁻¹' S₁.1 → IsSupportedOn (pushforward P φ hφ) S₁) ∧
    ∀ f, IsBddMeasurableFun f →
      pvmIntegral (pushforward P φ hφ) f = pvmIntegral P (f ∘ φ)
section Conjugate
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
def unitaryIsometry {U : K →ₗ[ℂ] H} (hU : IsUnitaryMap U) : K ≃ₗᵢ[ℂ] H :=
  ⟨hU.toLinearEquiv, hU.isometric⟩
def unitaryConj {U : K →ₗ[ℂ] H} (hU : IsUnitaryMap U) (A : BddOp H) :
    BddOp K :=
  ((unitaryIsometry hU).symm.toContinuousLinearEquiv : H →L[ℂ] K).comp
    (A.comp ((unitaryIsometry hU).toContinuousLinearEquiv : K →L[ℂ] H))
end Conjugate
def UnitaryConjFacts (P : FourBorelSet → BddOp H) (S₀ : FourBorelSet) : Prop :=
  ∀ (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (U : K →ₗ[ℂ] H) (hU : IsUnitaryMap U),
    IsPVM (fun S => unitaryConj hU (P S)) ∧
    IsSupportedOn (fun S => unitaryConj hU (P S)) S₀ ∧
    ∀ f, IsBddMeasurableFun f →
      pvmIntegral (fun S => unitaryConj hU (P S)) f =
        unitaryConj hU (pvmIntegral P f)
def restrictInvariant (Y : Submodule ℂ H) [CompleteSpace Y] (A : BddOp H)
    (hA : ∀ y ∈ Y, A y ∈ Y) : BddOp Y :=
  (A.comp Y.subtypeL).codRestrict Y fun y => hA y y.2
def RestrictionFacts (P : FourBorelSet → BddOp H) (S₀ : FourBorelSet) : Prop :=
  ∀ (Y : Submodule ℂ H), IsClosed (Y : Set H) → ∀ hY : (∀ S, ∀ y ∈ Y, P S y ∈ Y),
    CompleteSpace Y ∧ ∀ [CompleteSpace Y],
      IsPVM (fun S => restrictInvariant Y (P S) (hY S)) ∧
      IsSupportedOn (fun S => restrictInvariant Y (P S) (hY S)) S₀ ∧
      ∀ f, IsBddMeasurableFun f → ∀ y : Y,
        ((pvmIntegral (fun S => restrictInvariant Y (P S) (hY S)) f y : Y) : H) =
          pvmIntegral P f y
def diagDouble (A : BddOp H) : BddOp (WithLp 2 (H × H)) :=
  ((WithLp.prodContinuousLinearEquiv 2 ℂ H H).symm : H × H →L[ℂ] WithLp 2 (H × H)).comp
    ((A.prodMap A).comp (WithLp.prodContinuousLinearEquiv 2 ℂ H H : WithLp 2 (H × H) →L[ℂ] H × H))
def DoubleFacts (P : FourBorelSet → BddOp H) (S₀ : FourBorelSet) : Prop :=
  IsPVM (fun S => diagDouble (P S)) ∧
  IsSupportedOn (fun S => diagDouble (P S)) S₀ ∧
  ∀ f, IsBddMeasurableFun f →
    pvmIntegral (fun S => diagDouble (P S)) f = diagDouble (pvmIntegral P f)
def PvmDeterminedByCharFun (P : FourBorelSet → BddOp H) : Prop :=
  ∀ Q : FourBorelSet → BddOp H, IsPVM Q →
    (∀ a : Fin 4 → ℝ, pvmIntegral Q (expChar a) = pvmIntegral P (expChar a)) →
    Q = P
variable (H) in
def ProjectionNotionsAgree : Prop :=
  (∀ f : H → H, (∃ A : BddOp H, IsOrthProjection A ∧ ⇑A = f) ↔
    ∃ R : H →ₗ[ℂ] H, EuclideanSpectral.IsOrthProj R ∧ ⇑R = f) ∧
  ∀ F : FourBorelSet → H → H,
    (∃ P : FourBorelSet → BddOp H, IsPVM P ∧ ∀ S, ⇑(P S) = F S) ↔
    ∃ Q : EuclideanSpectral.ProjMeasure H 4,
      ∀ B, ⇑(Q B) = F (ofEuclideanBorel B)
def PvmNotionsAgree (P : FourBorelSet → BddOp H) : Prop :=
  ∀ Q : EuclideanSpectral.ProjMeasure H 4,
    (∀ B, ⇑(Q B) = ⇑(P (ofEuclideanBorel B))) →
    (∀ B, IsSupportedOn P (ofEuclideanBorel B) ↔
      EuclideanSpectral.ProjMeasure.Supports B Q) ∧
    (∀ (x : H) (B), spectralScalarMeasure P x x (ofEuclideanBorel B) = Q.diag x B) ∧
    ∀ f, IsBddMeasurableFun f →
      ⇑(pvmIntegral P f) = ⇑(Q.boundedIntegral (f ∘ (MeasurableEquiv.toLp 2 (Fin 4 → ℝ)).symm))
end Calculus
def BoundedFunctionalCalculus : Prop :=
  ComplexMeasureDeterminedByCharFun ∧
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    ProjectionNotionsAgree H ∧
    ∀ (P : FourBorelSet → BddOp H) (S₀ : FourBorelSet), IsPVM P →
      IsSupportedOn P S₀ →
      ScalarMeasureFacts P S₀ ∧
      PvmIntegralBasic P S₀ ∧
      PvmIntegralRules P ∧
      PvmIntegralNormAndConvergence P S₀ ∧
      PushforwardFacts P S₀ ∧
      UnitaryConjFacts P S₀ ∧
      RestrictionFacts P S₀ ∧
      DoubleFacts P S₀ ∧
      PvmDeterminedByCharFun P ∧
      PvmNotionsAgree P
end PVMCalculus
end YangMills.Construction
