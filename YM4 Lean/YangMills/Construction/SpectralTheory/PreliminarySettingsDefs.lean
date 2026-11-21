import YangMills.Construction.EuclideanSpectral.BorelFunctionOperator
import YangMills.Construction.MeasureTheory.FourMeasureIntegral
import YangMills.Construction.SpectralTheory.BorelFunctionalCalculusLaws
import YangMills.Construction.SpectralTheory.FunctionsOfSelfAdjointOperators
import YangMills.Construction.SpectralTheory.ResolvedOperatorsAndTheirJointSpectralMeasure
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace NNReal ComplexOrder
noncomputable section
namespace YangMills.Construction.SettingsComparison
open BorelSpectral
open HilbertSpaceBasics (UnboundedOp ofBounded)
open SpectralTheorem
  (IsSpectralIntegralOf IsSpectralMeasureFor RealLineSet spectralIntegralOp coordVar spectralMeasure)
open BorelCalculus (IsBoundedFn)
open SelfAdjointFunctions (FullSpace)
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
def IsProjFn (P : K → K) : Prop :=
  ∃ B : K →L[ℂ] K, ⇑B = P ∧ OperatorTransport.IsProjectionCLM B
def IsBoundedOrthProjFn (P : K → K) : Prop :=
  ∃ B : K →L[ℂ] K, ⇑B = P ∧ HilbertSpaceBasics.IsOrthProjOp B
def IsLinearOrthProjFn (P : K → K) : Prop :=
  ∃ p : K →ₗ[ℂ] K, ⇑p = P ∧ EuclideanSpectral.IsOrthProj p
def IsUnitaryFn (V : K → K) : Prop :=
  ∃ v : K →ₗ[ℂ] K, ⇑v = V ∧ OperatorTransport.IsUnitaryMap v
def IsBoundedUnitaryFn (V : K → K) : Prop :=
  ∃ B : K →L[ℂ] K, ⇑B = V ∧ HilbertSpaceBasics.IsUnitaryOp B
def IsIsometricUnitaryFn (V : K → K) : Prop :=
  ∃ u : K →ₗ[ℂ] K, ⇑u = V ∧ EuclideanSpectral.IsUnitaryMap u
def IsUnitaryGroupFn (U : ℝ → K → K) : Prop :=
  ∃ v : ℝ → K →ₗ[ℂ] K, (∀ s, ⇑(v s) = U s) ∧ OperatorTransport.IsUnitaryGroup v
def IsContUnitaryGroupFn (U : ℝ → K → K) : Prop :=
  ∃ B : ℝ → K →L[ℂ] K, (∀ s, ⇑(B s) = U s) ∧ HilbertSpaceBasics.IsUnitaryRep B ∧
    HilbertSpaceBasics.IsStronglyCont B
def totalOp (T : K →ₗ[ℂ] K) : UnboundedOp K :=
  ⟨⊤, T.comp (Submodule.subtype ⊤)⟩
structure IsProjValuedBorelMeasure {X : Type*} [MeasurableSpace X]
    (E : BorelSubsets X → K → K) : Prop where
  proj : ∀ Δ, IsProjFn (E Δ)
  apply_univ : E ⟨univ, MeasurableSet.univ⟩ = id
  apply_inter : ∀ Δ Δ' : BorelSubsets X, E ⟨Δ.1 ∩ Δ'.1, Δ.2.inter Δ'.2⟩ = E Δ ∘ E Δ'
  diag_countablyAdditive : ∀ ψ : K, SetFunctions.IsCountablyAdditive fun Δ => ⟪ψ, E Δ ψ⟫_ℂ
def FnIsCarriedBy {X : Type*} [MeasurableSpace X] (E : BorelSubsets X → K → K)
    (C : BorelSubsets X) : Prop :=
  E ⟨C.1ᶜ, C.2.compl⟩ = 0
variable {n : ℕ} {X : Set (Fin n → ℝ)}
def valueFn (F : SpectralMeasure X K) (Δ : BorelSubsets X) : K → K := ⇑(F Δ)
def IsBoundedIntegralViaCoeffs (F : SpectralMeasure X K) (g : X → ℂ)
    (T : K →L[ℂ] K) : Prop :=
  ∀ φ ψ : K, ⟪φ, T ψ⟫_ℂ =
    BorelComplexMeasures.integralOf (SpectralMeasure.matrixCoeff F φ ψ) g
def IsIntegralViaCoeffs (F : SpectralMeasure X K) (g : X → ℂ)
    (A : UnboundedOp K) : Prop :=
  (∀ ψ, ψ ∈ A.domain ↔ ∫⁻ y, ‖g y‖ₑ ^ 2 ∂F.diagMeasure ψ < ∞) ∧
    ∃ T : ℕ → K →L[ℂ] K,
      (∀ k : ℕ, IsBoundedIntegralViaCoeffs F ({y | ‖g y‖ ≤ k}.indicator g) (T k)) ∧
        ∀ ψ : A.domain, Tendsto (fun k => T k (ψ : K)) atTop (𝓝 (A ψ))
def euclideanToCoords (B : EuclideanSpectral.BorelSubset n) : BorelSubsets (FullSpace n) :=
  ⟨{y | (WithLp.toLp 2 y.1 : EuclideanSpace ℝ (Fin n)) ∈ B.1},
    ((MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurable.comp measurable_subtype_coe) B.2⟩
def liftToCoords (f : EuclideanSpace ℝ (Fin n) → ℂ) (y : FullSpace n) : ℂ :=
  f (WithLp.toLp 2 y.1)
def IsSameMeasure [NeZero n] (F : SpectralMeasure (FullSpace n) K)
    (G : EuclideanSpectral.ProjMeasure K n) : Prop :=
  ∀ B, ⇑(G B) = ⇑(F (euclideanToCoords B))
structure BoundedOpsAgree (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] : Prop where
  isBoundedAdjoint_iff : ∀ B B' : K →L[ℂ] K, OperatorTransport.IsBoundedAdjoint B' B ↔ B' = star B
  isSelfAdjointCLM_iff : ∀ B : K →L[ℂ] K,
    OperatorTransport.IsSelfAdjointCLM B ↔ _root_.IsSelfAdjoint B
  norm_le_one_iff : ∀ B : K →L[ℂ] K, ‖B‖ ≤ 1 ↔ HilbertSpaceBasics.IsContraction B
  mul_comm_iff : ∀ B B' : K →L[ℂ] K, B * B' = B' * B ↔ Commute B B'
  proj_iff : ∀ P : K → K, (IsProjFn P ↔ IsBoundedOrthProjFn P) ∧
    (IsBoundedOrthProjFn P ↔ IsLinearOrthProjFn P)
  unitary_iff : ∀ V : K → K, (IsUnitaryFn V ↔ IsBoundedUnitaryFn V) ∧
    (IsBoundedUnitaryFn V ↔ IsIsometricUnitaryFn V)
  inv_isInverse : ∀ (v : K →ₗ[ℂ] K) (hv : OperatorTransport.IsUnitaryMap v),
    Function.LeftInverse hv.inv v ∧ Function.RightInverse hv.inv v
  star_isInverse : ∀ B : K →L[ℂ] K, HilbertSpaceBasics.IsUnitaryOp B →
    Function.LeftInverse ⇑(star B : K →L[ℂ] K) ⇑B ∧
      Function.RightInverse ⇑(star B : K →L[ℂ] K) ⇑B
  euclideanInv_isInverse : ∀ (u : K →ₗ[ℂ] K)
    (hu : EuclideanSpectral.IsUnitaryMap u),
    Function.LeftInverse hu.inv u ∧ Function.RightInverse hu.inv u
  isContractionSemigroup_iff : ∀ T : ℝ≥0 → K →L[ℂ] K,
    OperatorTransport.IsContractionSemigroup T ↔
      HilbertSpaceBasics.IsOpSemigroup T ∧ (∀ t, _root_.IsSelfAdjoint (T t)) ∧
        (∀ t, HilbertSpaceBasics.IsContraction (T t)) ∧ HilbertSpaceBasics.IsStronglyCont T
  isUnitaryGroupFn_iff : ∀ U : ℝ → K → K,
    IsUnitaryGroupFn U ↔ IsContUnitaryGroupFn U
  inner_isSesquilinear : HilbertSpaceBasics.IsSesquilinear fun φ ψ : K => ⟪φ, ψ⟫_ℂ
  norm_eq_formSeminorm : ∀ ψ : K, ‖ψ‖ = HilbertSpaceBasics.formSeminorm (fun φ χ : K => ⟪φ, χ⟫_ℂ) ψ
  opNorm_eq_sSup : ∀ B : K →L[ℂ] K, ‖B‖ = sSup {x : ℝ | ∃ ψ : K, ‖ψ‖ ≤ 1 ∧ x = ‖B ψ‖}
structure UnboundedOpsAgree (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] : Prop where
  isSelfAdjoint_iff : ∀ A : UnboundedOp K,
    OperatorTransport.IsSelfAdjointUnbounded A ↔ HilbertSpaceBasics.IsSelfAdjointOp A
  isNonneg_iff : ∀ A : UnboundedOp K, OperatorTransport.IsSelfAdjointUnbounded A →
    (OperatorTransport.IsNonnegUnbounded A ↔ HilbertSpaceBasics.IsNonnegOp A)
  conjOp_eq : ∀ A : UnboundedOp K, OperatorTransport.IsSelfAdjointUnbounded A →
    ∀ (v : K →ₗ[ℂ] K) (hv : OperatorTransport.IsUnitaryMap v) (B : K →L[ℂ] K), ⇑B = ⇑v →
      OperatorTransport.conjOp hv A = HilbertSpaceBasics.conjByUnitary B A
  ext_iff_domain : ∀ A A' : UnboundedOp K, A = A' ↔ A.domain = A'.domain ∧
    ∀ (ψ : A.domain) (ψ' : A'.domain), (ψ : K) = ψ' → A ψ = A' ψ'
  eq_iff_le_le : ∀ A A' : UnboundedOp K, A = A' ↔ A ≤ A' ∧ A' ≤ A
structure BorelSetMeasuresAgree (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] {n : ℕ} (X : Set (Fin n → ℝ)) : Prop where
  isProjValued_iff : ∀ E : BorelSubsets X → K → K,
    IsProjValuedBorelMeasure E ↔ ∃ F : SpectralMeasure X K, valueFn F = E
  matrixCoeff_self : ∀ (F : SpectralMeasure X K) (ψ : K) (Δ : BorelSubsets X),
    SpectralMeasure.matrixCoeff F ψ ψ Δ = (((F.diagMeasure ψ).real Δ.1 : ℝ) : ℂ)
  fnIsCarriedBy_iff : ∀ (F : SpectralMeasure X K) (C : BorelSubsets X),
    FnIsCarriedBy (valueFn F) C ↔ F.IsCarriedBy C
  boundedViaCoeffs_iff : ∀ (F : SpectralMeasure X K) (g : X → ℂ), Measurable g →
    IsBoundedFn g → ∀ T : K →L[ℂ] K,
      IsBoundedIntegralViaCoeffs F g T ↔ F.IsDiagonalIntegral g T
  boundedViaCoeffs_iff_eq : ∀ (F : SpectralMeasure X K) (g : X → ℂ), Measurable g →
    IsBoundedFn g → ∀ T : K →L[ℂ] K,
      IsBoundedIntegralViaCoeffs F g T ↔ T = F.integralOp g
  viaCoeffs_iff : ∀ (F : SpectralMeasure X K) (g : X → ℂ), Measurable g →
    ∀ A : UnboundedOp K, IsIntegralViaCoeffs F g A ↔ IsSpectralIntegralOf A F g
  setIntegralOp_spec : ∀ (F : SpectralMeasure X K) (C : BorelSubsets X) (g : C.1 → ℂ),
    Measurable g → F.IsCarriedBy C →
      (∀ ψ, ψ ∈ (SpectralMeasure.setIntegralOp F C g).domain ↔
        ψ ∈ F.integralDomOn C g) ∧
      ∀ ψ : (SpectralMeasure.setIntegralOp F C g).domain,
        SpectralMeasure.setIntegralOp F C g ψ = F.integralApplyOn C g ψ
  valueFn_pushforward : ∀ (F : SpectralMeasure X K) {n' : ℕ} {X' : Set (Fin n' → ℝ)} (hn' : 1 ≤ n')
    (hX' : MeasurableSet X') (κ : X → X') (hκ : Measurable κ) (Δ' : BorelSubsets X'),
    valueFn (F.pushforward hn' hX' κ hκ) Δ' = valueFn F ⟨κ ⁻¹' Δ'.1, hκ Δ'.2⟩
  valueFn_extendCarrier : ∀ (F : SpectralMeasure X K) {X' : Set (Fin n → ℝ)} (hX : X ⊆ X')
    (hX' : MeasurableSet X') (Δ' : BorelSubsets X'),
    valueFn (F.extendCarrier hX hX') Δ' =
      valueFn F ⟨inclusion hX ⁻¹' Δ'.1, measurable_subtype_coe.subtype_mk Δ'.2⟩
  integralOf_matrixCoeff : ∀ (F : SpectralMeasure X K) (g : X → ℂ) (φ ψ : K),
    Measurable g → (∀ k ∈ Finset.range 4, Integrable g (F.diagMeasure (φ + Complex.I ^ k • ψ))) →
      BorelComplexMeasures.integralOf (SpectralMeasure.matrixCoeff F φ ψ) g =
        F.polarizedIntegral g φ ψ
structure FullSpaceMeasuresAgree (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (n : ℕ) [NeZero n] : Prop where
  isProjValued_iff : ∀ E : BorelSubsets (FullSpace n) → K → K, IsProjValuedBorelMeasure E ↔
    ∃ G : EuclideanSpectral.ProjMeasure K n,
      ∀ B, ⇑(G B) = E (euclideanToCoords B)
  diag_eq : ∀ (F : SpectralMeasure (FullSpace n) K)
    (G : EuclideanSpectral.ProjMeasure K n), IsSameMeasure F G →
    ∀ (ψ : K) (B : EuclideanSpectral.BorelSubset n),
      G.diag ψ B = (((F.diagMeasure ψ).real (euclideanToCoords B).1 : ℝ) : ℂ)
  diagMeasure_eq : ∀ (F : SpectralMeasure (FullSpace n) K)
    (G : EuclideanSpectral.ProjMeasure K n), IsSameMeasure F G →
    ∀ (ψ : K) (B : EuclideanSpectral.BorelSubset n),
      G.diagMeasure ψ B.1 = F.diagMeasure ψ (euclideanToCoords B).1
  supports_iff : ∀ (F : SpectralMeasure (FullSpace n) K)
    (G : EuclideanSpectral.ProjMeasure K n), IsSameMeasure F G →
    ∀ B : EuclideanSpectral.BorelSubset n,
      EuclideanSpectral.ProjMeasure.Supports B G ↔
        F.IsCarriedBy (euclideanToCoords B)
  integralOp_eq : ∀ (F : SpectralMeasure (FullSpace n) K)
    (G : EuclideanSpectral.ProjMeasure K n), IsSameMeasure F G →
    ∀ f : EuclideanSpace ℝ (Fin n) → ℂ, Measurable f → IsBoundedFn f →
      ⇑(F.integralOp (liftToCoords f)) = ⇑(G.boundedIntegral f)
  setIntegralOp_eq : ∀ (F : SpectralMeasure (FullSpace n) K)
    (G : EuclideanSpectral.ProjMeasure K n), IsSameMeasure F G →
    ∀ (C : EuclideanSpectral.BorelSubset n) (f : EuclideanSpace ℝ (Fin n) → ℂ),
      Measurable f → (∃ c : ℝ, ∀ x ∈ C.1, ‖f x‖ ≤ c) →
        SpectralMeasure.setIntegralOp F (euclideanToCoords C)
            (fun y => liftToCoords f y.1) = totalOp (G.boundedIntegralOn C f)
  spectralIntegralOp_eq : ∀ (F : SpectralMeasure (FullSpace n) K)
    (G : EuclideanSpectral.ProjMeasure K n), IsSameMeasure F G →
    ∀ f : EuclideanSpace ℝ (Fin n) → ℂ, Measurable f →
      spectralIntegralOp F (liftToCoords f) = ⟨G.fnDomain f, G.borelFnOp f⟩
structure SpectralMeasuresAgree (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] : Prop where
  isDiagonalized : ∀ A : UnboundedOp K, OperatorTransport.IsSelfAdjointUnbounded A →
    ResolvedOps.IsDiagonalized A
  viaCoeffs_iff_eq_spectralMeasure : ∀ A : UnboundedOp K,
    OperatorTransport.IsSelfAdjointUnbounded A →
    ∀ E : SpectralMeasure RealLineSet K,
      IsIntegralViaCoeffs E coordVar A ↔ E = spectralMeasure A
  viaCoeffs_iff_eq_fnCalc : ∀ A : UnboundedOp K, OperatorTransport.IsSelfAdjointUnbounded A →
    ∀ u : ℝ → ℂ, Measurable u → ∀ B : UnboundedOp K,
      IsIntegralViaCoeffs (spectralMeasure A) (fun y => u (y.1 0)) B ↔
        B = SelfAdjointFunctions.fnCalc A u
  setIntegralOp_eq_fnCalcOn : ∀ A : UnboundedOp K, OperatorTransport.IsSelfAdjointUnbounded A →
    ∀ (C : BorelSubsets ℝ) (u : C.1 → ℂ), Measurable u →
      (spectralMeasure A).IsCarriedBy (realLineSet C) →
        SpectralMeasure.setIntegralOp (spectralMeasure A) (realLineSet C)
            (fun y => u ⟨y.1.1 0, y.2⟩) = SelfAdjointFunctions.fnCalcOn A C u
  fnCalc_cexp_eq_expI : ∀ A : UnboundedOp K, OperatorTransport.IsSelfAdjointUnbounded A →
    ∀ s : ℝ,
    SelfAdjointFunctions.fnCalc A
        (fun x => Complex.exp (Complex.I * s * (x : ℝ))) =
      ofBounded (SelfAdjointFunctions.expI A s)
  fnCalc_abs_eq_absOp : ∀ A : UnboundedOp K, OperatorTransport.IsSelfAdjointUnbounded A →
    SelfAdjointFunctions.fnCalc A (fun x => ((|x| : ℝ) : ℂ)) =
      SelfAdjointFunctions.absOp A
  expComplex_eq_expNeg : ∀ A : UnboundedOp K, OperatorTransport.IsSelfAdjointUnbounded A →
    OperatorTransport.IsNonnegUnbounded A → ∀ t : ℝ≥0,
      ResolvedOps.expComplex A ((t : ℝ) : ℂ) =
        SelfAdjointFunctions.expNeg A t
  stronglyCommute_iff : ∀ A A' : UnboundedOp K, OperatorTransport.IsSelfAdjointUnbounded A →
    OperatorTransport.IsSelfAdjointUnbounded A' →
      (ResolvedOps.StronglyCommute A A' ↔
        SelfAdjointFunctions.PairwiseStronglyCommute ![A, A'])
structure CommutingBoundedOpsAgree (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] : Prop where
  stronglyCommute : ∀ {r : ℕ}, 1 ≤ r → ∀ A : Fin r → K →L[ℂ] K,
    (∀ k, OperatorTransport.IsSelfAdjointCLM (A k)) →
    (∀ i j, Commute (A i) (A j)) →
      ∀ i j, ResolvedOps.StronglyCommute (ofBounded (A i)) (ofBounded (A j))
  jointSpectralMeasure_eq : ∀ {r : ℕ} (hr : 1 ≤ r) (A : Fin r → K →L[ℂ] K),
    (∀ k, OperatorTransport.IsSelfAdjointCLM (A k)) →
    (∀ i j, Commute (A i) (A j)) →
      ResolvedOps.jointSpectralMeasure hr (fun k => ofBounded (A k)) =
        JointSpectral.jointMeasureOnSpace hr A
end YangMills.Construction.SettingsComparison
