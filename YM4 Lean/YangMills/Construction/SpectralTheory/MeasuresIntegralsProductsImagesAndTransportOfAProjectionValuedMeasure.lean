import YangMills.Construction.SpectralTheory.MatrixMeasuresAndCommutation
import YangMills.Construction.MeasureTheory.FourMeasureIntegral
import YangMills.Construction.SpectralTheory.BorelFunctionalCalculusLaws
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ComplexOrder InnerProductSpace
noncomputable section
namespace YangMills.Construction.SpectralMeasureCalculus
open YangMills.Construction.BorelSpectral YangMills.Construction.BorelSpectral.SpectralMeasure
open YangMills.Construction.SetFunctions (IsCountablyAdditive)
open YangMills.Construction.BorelCalculus (IsBoundedFn IsRealValued conjFn)
open YangMills.Construction.SpectralTheorem
  (IsSpectralIntegralOf spectralIntegralOp pushforwardToLine coordVar IntegralsAgree)
variable {n : ℕ} {Y : Set (Fin n → ℝ)} {H H' : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
def normLeSet {f : Y → ℂ} (hf : Measurable f) (m : ℕ) : BorelSubsets Y :=
  ⟨{y | ‖f y‖ ≤ m}, measurableSet_le hf.norm measurable_const⟩
structure IsSpectralMeasureLike {X : Type*} [MeasurableSpace X] (P : BorelSubsets X → H →L[ℂ] H) :
    Prop where
  isStarProjection : ∀ A, IsStarProjection (P A)
  map_univ : P ⟨univ, MeasurableSet.univ⟩ = 1
  map_inter : ∀ A B : BorelSubsets X, P ⟨A.1 ∩ B.1, A.2.inter B.2⟩ = P A * P B
  countablyAdditive : ∀ (x : H) (A : ℕ → BorelSubsets X),
    (Pairwise fun i j => Disjoint (A i).1 (A j).1) →
      HasSum (fun i => ⟪x, P (A i) x⟫_ℂ)
        ⟪x, P ⟨⋃ i, (A i).1, MeasurableSet.iUnion fun i => (A i).2⟩ x⟫_ℂ
structure MeasureLaws (E : SpectralMeasure Y H) : Prop where
  isFiniteMeasure : ∀ x, IsFiniteMeasure (E.diagMeasure x)
  real_apply : ∀ (x : H) (A : BorelSubsets Y), (E.diagMeasure x).real A.1 = ‖E A x‖ ^ 2
  real_univ : ∀ x : H, (E.diagMeasure x).real univ = ‖x‖ ^ 2
  value_empty : E ⟨∅, MeasurableSet.empty⟩ = 0
  orthogonal : ∀ (ι : Type) [Countable ι] (A : ι → BorelSubsets Y) (x : H),
    (Pairwise fun i j => Disjoint (A i).1 (A j).1) →
      Pairwise fun i j => ⟪E (A i) x, E (A j) x⟫_ℂ = 0
  hasSum : ∀ (ι : Type) [Countable ι] (A : ι → BorelSubsets Y) (x : H),
    (Pairwise fun i j => Disjoint (A i).1 (A j).1) →
      HasSum (fun i => E (A i) x) (E ⟨⋃ i, (A i).1, MeasurableSet.iUnion fun i => (A i).2⟩ x)
  complexMeasure_eq : ∀ (u x : H) (A : BorelSubsets Y), E.matrixCoeff u x A =
    (1 / 4 : ℂ) * ∑ j ∈ Finset.range 4,
      Complex.I ^ j * (((E.diagMeasure (x + Complex.I ^ j • u)).real A.1 : ℝ) : ℂ)
  isComplexMeasure : ∀ u x : H, IsCountablyAdditive (E.matrixCoeff u x)
  value_iUnion : ∀ (ι : Type) [Countable ι] (A : ι → BorelSubsets Y), (∀ i, E (A i) = 0) →
    E ⟨⋃ i, (A i).1, MeasurableSet.iUnion fun i => (A i).2⟩ = 0
  real_add_le : ∀ (u x : H) (A : BorelSubsets Y), (E.diagMeasure (x + u)).real A.1 ≤
    2 * (E.diagMeasure x).real A.1 + 2 * (E.diagMeasure u).real A.1
  real_smul : ∀ (c : ℂ) (x : H) (A : BorelSubsets Y),
    (E.diagMeasure (c • x)).real A.1 = ‖c‖ ^ 2 * (E.diagMeasure x).real A.1
  integral_eq : ∀ (f : Y → ℂ) (u x : H), Measurable f →
    (∀ j ∈ Finset.range 4, Integrable f (E.diagMeasure (u + Complex.I ^ j • x))) →
      BorelComplexMeasures.integralOf (E.matrixCoeff u x) f = E.polarizedIntegral f u x
structure BoundedCalculusLaws (E : SpectralMeasure Y H) : Prop where
  existsUnique_operator : ∀ f : Y → ℂ, Measurable f → IsBoundedFn f →
    ∃! T : H →L[ℂ] H, ∀ u x : H,
      ⟪u, T x⟫_ℂ = BorelComplexMeasures.integralOf (E.matrixCoeff u x) f
  inner_eq : ∀ f : Y → ℂ, Measurable f → IsBoundedFn f → ∀ u x : H,
    ⟪u, E.integralOp f x⟫_ℂ = BorelComplexMeasures.integralOf (E.matrixCoeff u x) f
  add : ∀ f f' : Y → ℂ, Measurable f → IsBoundedFn f → Measurable f' →
    IsBoundedFn f' → E.integralOp (f + f') = E.integralOp f + E.integralOp f'
  smul : ∀ (c : ℂ) (f : Y → ℂ), Measurable f → IsBoundedFn f →
    E.integralOp (c • f) = c • E.integralOp f
  mul : ∀ f f' : Y → ℂ, Measurable f → IsBoundedFn f → Measurable f' →
    IsBoundedFn f' → E.integralOp (f * f') = E.integralOp f * E.integralOp f'
  conjugate : ∀ f : Y → ℂ, Measurable f → IsBoundedFn f →
    E.integralOp (conjFn f) = star (E.integralOp f)
  indicator : ∀ A : BorelSubsets Y, E.integralOp (A.1.indicator 1) = E A
  norm_sq : ∀ f : Y → ℂ, Measurable f → IsBoundedFn f → ∀ x : H,
    ‖E.integralOp f x‖ ^ 2 = ∫ y, ‖f y‖ ^ 2 ∂E.diagMeasure x
  norm_le : ∀ (f : Y → ℂ) (S : BorelSubsets Y), Measurable f → IsBoundedFn f → E.IsCarriedBy S →
    ‖E.integralOp f‖ ≤ ⨆ y : S.1, ‖f y‖
  congr : ∀ (f f' : Y → ℂ) (S : BorelSubsets Y), Measurable f → IsBoundedFn f → Measurable f' →
    IsBoundedFn f' → E.IsCarriedBy S → (∀ y ∈ S.1, f y = f' y) →
      E.integralOp f = E.integralOp f'
  tendsto : ∀ (F : ℕ → Y → ℂ) (f : Y → ℂ) (c : ℝ) (S : BorelSubsets Y), (∀ i, Measurable (F i)) →
    Measurable f → (∀ i y, ‖F i y‖ ≤ c) → (∀ y, ‖f y‖ ≤ c) → E.IsCarriedBy S →
    (∀ y ∈ S.1, Tendsto (fun i => F i y) atTop (𝓝 (f y))) →
      ∀ x : H, Tendsto (fun i => E.integralOp (F i) x) atTop (𝓝 (E.integralOp f x))
  commute : ∀ (B : H →L[ℂ] H) (f : Y → ℂ), OpCommutes B E → Measurable f →
    IsBoundedFn f → Commute B (E.integralOp f)
structure UnboundedCalculusLaws (E : SpectralMeasure Y H) : Prop where
  dense_domain : ∀ f : Y → ℂ, Measurable f → Dense (E.integralDom f)
  isIntegralOf : ∀ f : Y → ℂ, Measurable f → IsSpectralIntegralOf (spectralIntegralOp E f) E f
  range_subset_domain : ∀ (f : Y → ℂ) (hf : Measurable f) (m : ℕ),
    range (E (normLeSet hf m)) ⊆ E.integralDom f
  domain_conjugate : ∀ f : Y → ℂ, Measurable f →
    E.integralDom (conjFn f) = E.integralDom f
  domain_modulus : ∀ f : Y → ℂ, Measurable f →
    E.integralDom (fun y => ((‖f y‖ : ℝ) : ℂ)) = E.integralDom f
  tendsto_truncation : ∀ f : Y → ℂ, Measurable f → ∀ x ∈ E.integralDom f,
    Tendsto (fun m => E.integralOp (truncate f m) x) atTop (𝓝 (E.integralApply f x))
  of_bounded : ∀ f : Y → ℂ, Measurable f → IsBoundedFn f →
    E.integralDom f = univ ∧ ∀ x, E.integralApply f x = E.integralOp f x
  norm_sq : ∀ f : Y → ℂ, Measurable f → ∀ x ∈ E.integralDom f,
    ‖E.integralApply f x‖ ^ 2 = ∫ y, ‖f y‖ ^ 2 ∂E.diagMeasure x
  norm_sub_sq : ∀ f f' : Y → ℂ, Measurable f → Measurable f' → IsBoundedFn f' →
    ∀ x ∈ E.integralDom f, ‖E.integralApply f x - E.integralOp f' x‖ ^ 2 =
      ∫ y, ‖f y - f' y‖ ^ 2 ∂E.diagMeasure x
  integrable : ∀ f : Y → ℂ, Measurable f → ∀ x ∈ E.integralDom f,
    Integrable f (E.diagMeasure x)
  inner_self : ∀ f : Y → ℂ, Measurable f → ∀ x ∈ E.integralDom f,
    ⟪x, E.integralApply f x⟫_ℂ = ∫ y, f y ∂E.diagMeasure x
  inner_conjugate : ∀ f : Y → ℂ, Measurable f → ∀ u ∈ E.integralDom f,
    ∀ x ∈ E.integralDom f,
      ⟪u, E.integralApply f x⟫_ℂ = ⟪E.integralApply (conjFn f) u, x⟫_ℂ
  congr : ∀ (f f' : Y → ℂ) (S : BorelSubsets Y), Measurable f → Measurable f' → E.IsCarriedBy S →
    (∀ y ∈ S.1, f y = f' y) → IntegralsAgree E f E f'
structure ProductLaws (E : SpectralMeasure Y H) : Prop where
  real_boundedIntegral : ∀ f' : Y → ℂ, Measurable f' → IsBoundedFn f' →
    ∀ (x : H) (A : BorelSubsets Y), (E.diagMeasure (E.integralOp f' x)).real A.1 =
      ∫ y in A.1, ‖f' y‖ ^ 2 ∂E.diagMeasure x
  real_value : ∀ (x : H) (A B : BorelSubsets Y),
    (E.diagMeasure (E A x)).real B.1 = (E.diagMeasure x).real (A.1 ∩ B.1)
  boundedIntegral_mem : ∀ f f' : Y → ℂ, Measurable f → Measurable f' → IsBoundedFn f' →
    ∀ x ∈ E.integralDom (f * f'), E.integralOp f' x ∈ E.integralDom f
  integralValue_boundedIntegral : ∀ f f' : Y → ℂ, Measurable f → Measurable f' →
    IsBoundedFn f' → ∀ x ∈ E.integralDom (f * f'),
      E.integralApply f (E.integralOp f' x) = E.integralApply (f * f') x
  boundedIntegral_integralValue : ∀ f f' : Y → ℂ, Measurable f → Measurable f' →
    IsBoundedFn f' → ∀ x ∈ E.integralDom (f * f'), x ∈ E.integralDom f →
      E.integralApply (f * f') x = E.integralOp f' (E.integralApply f x)
structure PushforwardAndSupportLaws (E : SpectralMeasure Y H) : Prop where
  scalarMeasure_image : ∀ {m : ℕ} {Z : Set (Fin m → ℝ)} (hm : 1 ≤ m) (hZ : MeasurableSet Z)
    (κ : Y → Z) (hκ : Measurable κ) (x : H),
    (E.pushforward hm hZ κ hκ).diagMeasure x = (E.diagMeasure x).map κ
  integral_image : ∀ {m : ℕ} {Z : Set (Fin m → ℝ)} (hm : 1 ≤ m) (hZ : MeasurableSet Z)
    (κ : Y → Z) (hκ : Measurable κ) (h : Z → ℂ), Measurable h →
    IntegralsAgree (E.pushforward hm hZ κ hκ) h E (h ∘ κ)
  value_carrier : ∀ S : BorelSubsets Y, E.IsCarriedBy S → E S = 1
  value_inter_carrier : ∀ S A : BorelSubsets Y, E.IsCarriedBy S →
    E A = E ⟨A.1 ∩ S.1, A.2.inter S.2⟩
  restriction : ∀ S : BorelSubsets Y, E.IsCarriedBy S → IsSpectralMeasureLike (E.restrictTo S)
def UnitaryConjugationLaw (E : SpectralMeasure Y H) {U : H →ₗ[ℂ] H'}
    (hU : OperatorTransport.IsUnitaryMap U) : Prop :=
  ∃ E' : SpectralMeasure Y H',
    (∀ A, ((E' A : H' →L[ℂ] H') : H' →ₗ[ℂ] H') = E.unitaryPushforward hU A) ∧
    (∀ x : H, E'.diagMeasure (U x) = E.diagMeasure x) ∧
    ∀ f : Y → ℂ, Measurable f →
      spectralIntegralOp E' f = OperatorTransport.conjOp hU (spectralIntegralOp E f)
structure RealFunctionLaws (E : SpectralMeasure Y H) : Prop where
  isSelfAdjoint : ∀ f : Y → ℂ, Measurable f → IsRealValued f →
    OperatorTransport.IsSelfAdjointUnbounded (spectralIntegralOp E f)
  eq_integral_lineImage : ∀ (f : Y → ℂ) (hf : Measurable f), IsRealValued f →
    spectralIntegralOp E f = spectralIntegralOp
      (pushforwardToLine E (fun y => (f y).re) (Complex.measurable_re.comp hf)) coordVar
  isNonnegative : ∀ (f : Y → ℂ) (S : BorelSubsets Y), Measurable f → IsRealValued f →
    E.IsCarriedBy S → (∀ y ∈ S.1, 0 ≤ f y) →
      OperatorTransport.IsNonnegUnbounded (spectralIntegralOp E f)
structure ComposedMeasureLaws (E : SpectralMeasure Y H) : Prop where
  isComplexMeasure : ∀ (B : H →L[ℂ] H) (u x : H),
    IsCountablyAdditive fun A : BorelSubsets Y => ⟪u, B (E A x)⟫_ℂ
  integral_eq : ∀ (B : H →L[ℂ] H) (u x : H) (f : Y → ℂ), Measurable f → IsBoundedFn f →
    BorelComplexMeasures.integralOf (fun A : BorelSubsets Y => ⟪u, B (E A x)⟫_ℂ) f =
      ⟪u, B (E.integralOp f x)⟫_ℂ
def CalculusTheorem : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (n : ℕ)
    (Y : Set (Fin n → ℝ)) (E : SpectralMeasure Y H),
    MeasureLaws E ∧ BoundedCalculusLaws E ∧ UnboundedCalculusLaws E ∧ ProductLaws E ∧
    PushforwardAndSupportLaws E ∧
    (∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
      (U : H →ₗ[ℂ] H') (hU : OperatorTransport.IsUnitaryMap U), UnitaryConjugationLaw E hU) ∧
    RealFunctionLaws E ∧ ComposedMeasureLaws E
end YangMills.Construction.SpectralMeasureCalculus
