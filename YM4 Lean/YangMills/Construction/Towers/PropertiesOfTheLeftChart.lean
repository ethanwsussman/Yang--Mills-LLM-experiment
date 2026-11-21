import YangMills.Construction.Towers.TheLeftChart
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open Matrices
namespace Tower
def compositeDomain {α β : Type*} (D₁ : Set α) (D₂ : Set β) (m₁ : α → β) : Set α :=
  D₁ ∩ m₁ ⁻¹' D₂
def expVertexFn {ι : Type*} (l : ι → ComplexMatrix2) : ι → ComplexMatrix2 :=
  fun x => ComplexMatrix2.matExp (Complex.I • l x)
namespace LeftChartFacts
def biInvariantMetric (g v w : ComplexMatrix2) : ℂ :=
  ComplexMatrix2.halfTrace ((Complex.I⁻¹ • (v * g⁻¹)) * (Complex.I⁻¹ • (w * g⁻¹)))
def IsBiInvariantMetric : Prop :=
  (∀ X ∈ ComplexMatrix2.hermitianTraceless, ∀ Y ∈ ComplexMatrix2.hermitianTraceless,
    biInvariantMetric 1 (Complex.I • X) (Complex.I • Y) = ComplexMatrix2.halfTrace (X * Y)) ∧
  ∀ g ∈ PeriodicLattice.compactGaugeGroup, ∀ h ∈ PeriodicLattice.compactGaugeGroup,
    ∀ v w : ComplexMatrix2,
    biInvariantMetric (h * g) (h * v) (h * w) = biInvariantMetric g v w ∧
      biInvariantMetric (g * h) (v * h) (w * h) = biInvariantMetric g v w
def IsOrthogonalOn {V : Type*} [AddCommGroup V] [Module ℝ V] (S : Submodule ℝ V)
    (p : V → V → ℂ) (T : V → V) : Prop :=
  ∃ e : S ≃ₗ[ℝ] S, (∀ x : S, (e x : V) = T x) ∧ ∀ x y : S, p (T x) (T y) = p x y
section FiniteSide
variable {L n k j j' : ℕ}
def TangentSpaceIsoForms (L n k j : ℕ) : Prop :=
  ∀ [Fintype (PositiveEdge L n k j)] (U : Edge L n k j → ComplexMatrix2), U ∈ fieldSpace L n k j →
    (∃ e : edgeFormSpace L n k j ≃ₗ[ℝ] tangentAt U, ∀ B : edgeFormSpace L n k j,
      (e B : PositiveEdge L n k j → ComplexMatrix2) = leftChartTangent U B) ∧
    ∀ B ∈ edgeFormSpace L n k j, ∀ B' ∈ edgeFormSpace L n k j,
      ∑ b : PositiveEdge L n k j,
        biInvariantMetric (U b) (leftChartTangent U B b) (leftChartTangent U B' b) =
          edgeFormPairing B B'
def MapDerivAlongCurves (𝒢 : Set ComplexMatrix2)
    (m : (Edge L n k j → ComplexMatrix2) → Edge L n k j' → ComplexMatrix2)
    (U : Edge L n k j → ComplexMatrix2)
    (m' : (Edge L n k j → ComplexMatrix2) → Edge L n k j' → ComplexMatrix2) : Prop :=
  ∀ (I : Set ℝ) (γ : ℝ → Edge L n k j → ComplexMatrix2), IsDifferentiableFieldCurve 𝒢 I γ →
    γ 0 = U →
    (∀ c : Edge L n k j', c.IsPositivelyOriented → DifferentiableAt ℝ (fun t => m (γ t) c) 0) ∧
      curveTangent (fun t => m (γ t)) = m' (curveTangent γ)
def FnDerivAlongCurves (𝒢 : Set ComplexMatrix2) (F : (Edge L n k j → ComplexMatrix2) → ℂ)
    (U : Edge L n k j → ComplexMatrix2) (d : (Edge L n k j → ComplexMatrix2) → ℂ) : Prop :=
  ∀ (I : Set ℝ) (γ : ℝ → Edge L n k j → ComplexMatrix2), IsDifferentiableFieldCurve 𝒢 I γ →
    γ 0 = U → HasDerivAt (fun t => F (γ t)) (d (curveTangent γ)) 0
def DifferentialsFromCurves (L n k j j' : ℕ) : Prop :=
  (∀ (D : Set (Edge L n k j → ComplexMatrix2))
    (m : (Edge L n k j → ComplexMatrix2) → Edge L n k j' → ComplexMatrix2),
    IsDifferentiableFieldMap D m → ∀ U ∈ D,
      MapDerivAlongCurves PeriodicLattice.compactGaugeGroup m U (leftDifferential m U)) ∧
  (∀ (D : Set (Edge L n k j → ComplexMatrix2)) (F : (Edge L n k j → ComplexMatrix2) → ℂ),
    IsDifferentiableFn D F → ∀ U ∈ D,
      FnDerivAlongCurves PeriodicLattice.compactGaugeGroup F U (leftDeriv F U)) ∧
  (∀ (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (D : Set (Edge L n k j → ComplexMatrix2))
    (m : (Edge L n k j → ComplexMatrix2) → Edge L n k j' → ComplexMatrix2),
    IsHolomorphicFieldMap β D m → ∀ U ∈ D,
      MapDerivAlongCurves PeriodicLattice.complexGaugeGroup m U (holLeftDifferential m U)) ∧
  ∀ (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (D : Set (Edge L n k j → ComplexMatrix2))
    (F : (Edge L n k j → ComplexMatrix2) → ℂ),
    IsHolomorphicFn β (Equiv.funUnique (Fin 1) ℂ).symm D F → ∀ U ∈ D,
      FnDerivAlongCurves PeriodicLattice.complexGaugeGroup F U (holLeftDeriv F U)
def CompChainRule (L n k j j' j'' : ℕ) : Prop :=
  (∀ (D₁ : Set (Edge L n k j → ComplexMatrix2)) (D₂ : Set (Edge L n k j' → ComplexMatrix2))
    (m₁ : (Edge L n k j → ComplexMatrix2) → Edge L n k j' → ComplexMatrix2)
    (m₂ : (Edge L n k j' → ComplexMatrix2) → Edge L n k j'' → ComplexMatrix2),
    IsDifferentiableFieldMap D₁ m₁ → IsDifferentiableFieldMap D₂ m₂ →
      IsDifferentiableFieldMap (compositeDomain D₁ D₂ m₁) (m₂ ∘ m₁) ∧
      ∀ U ∈ compositeDomain D₁ D₂ m₁, ∀ B ∈ edgeFormSpace L n k j,
        leftDifferential (m₂ ∘ m₁) U B = leftDifferential m₂ (m₁ U) (leftDifferential m₁ U B)) ∧
  ∀ (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (D₁ : Set (Edge L n k j → ComplexMatrix2)) (D₂ : Set (Edge L n k j' → ComplexMatrix2))
    (m₁ : (Edge L n k j → ComplexMatrix2) → Edge L n k j' → ComplexMatrix2)
    (m₂ : (Edge L n k j' → ComplexMatrix2) → Edge L n k j'' → ComplexMatrix2),
    IsHolomorphicFieldMap β D₁ m₁ → IsHolomorphicFieldMap β D₂ m₂ →
      IsHolomorphicFieldMap β (compositeDomain D₁ D₂ m₁) (m₂ ∘ m₁) ∧
      ∀ U ∈ compositeDomain D₁ D₂ m₁, ∀ B ∈ complexEdgeForms L n k j,
        holLeftDifferential (m₂ ∘ m₁) U B =
          holLeftDifferential m₂ (m₁ U) (holLeftDifferential m₁ U B)
def GaugeOrbitTangent (L n k j : ℕ) : Prop :=
  (∀ U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup, ∀ l : Vertex L n k j → ComplexMatrix2,
    (∀ x, l x ∈ ComplexMatrix2.traceless) →
    (∀ b : Edge L n k j, b.IsPositivelyOriented → ∃ C r : ℝ, 0 < r ∧ ∀ t : ℂ, ‖t‖ < r →
      ∃ X ∈ ComplexMatrix2.traceless, ComplexMatrix2.operatorNorm X ≤ C * ‖t‖ ^ 2 ∧
        PeriodicLattice.gaugeTransform (expVertexFn (t • l)) U b =
          ComplexMatrix2.matExp (Complex.I • (-(t • covDiff U l b) + X)) * U b) ∧
    (∀ b : Edge L n k j, b.IsPositivelyOriented → DifferentiableAt ℝ
      (fun t : ℝ => PeriodicLattice.gaugeTransform (expVertexFn ((t : ℂ) • l)) U b) 0) ∧
    curveTangent (fun t : ℝ => PeriodicLattice.gaugeTransform (expVertexFn ((t : ℂ) • l)) U) =
      -covDiff U l ∧
    ∀ (x : Vertex L n k j) (μ : Fin 4), (PeriodicLattice.Bond.forwardFrom x μ).IsPositivelyOriented →
      covDiff U l (PeriodicLattice.Bond.forwardFrom x μ) =
        ((meshAt L k j : ℝ) : ℂ) • PeriodicLattice.covDeriv (meshAt L k j) U μ l x) ∧
  ∀ l : Vertex L n k j → ComplexMatrix2,
    covDiff (fun _ : Edge L n k j => (1 : ComplexMatrix2)) l = vertexCoboundary l
def GaugeEquivarianceForms (L n k j : ℕ) : Prop :=
  ∀ u : Vertex L n k j → ComplexMatrix2, PeriodicLattice.IsGaugeMap PeriodicLattice.complexGaugeGroup u →
    (∀ U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup, ∀ B ∈ complexEdgeForms L n k j,
      PeriodicLattice.expTwist (adjointForm u B) (PeriodicLattice.gaugeTransform u U) =
        PeriodicLattice.gaugeTransform u (PeriodicLattice.expTwist B U)) ∧
    (∀ B ∈ complexEdgeForms L n k j, ∀ B' ∈ complexEdgeForms L n k j,
      edgeFormPairing (adjointForm u B) (adjointForm u B') = edgeFormPairing B B') ∧
    (∀ l l' : Vertex L n k j → ComplexMatrix2, (∀ x, l x ∈ ComplexMatrix2.traceless) →
      (∀ x, l' x ∈ ComplexMatrix2.traceless) →
      traceFinsumPairing (adjointVertexFn u l) (adjointVertexFn u l') = traceFinsumPairing l l') ∧
    (u ∈ gaugeGroupAt L n k j →
      IsOrthogonalOn (edgeFormSpace L n k j) edgeFormPairing (adjointForm u) ∧
        IsOrthogonalOn (vertexFunctionSpace L n k j) traceFinsumPairing (adjointVertexFn u))
def IsometryEquivarianceForms (L n k j : ℕ) : Prop :=
  ∀ f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n, IsDistancePreserving f →
    MapsSublatticeOnto k j f →
    ∀ U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
      (∀ B ∈ complexEdgeForms L n k j,
        PeriodicLattice.expTwist (isometryOnTangent f U B) (pushField f U) =
          pushField f (PeriodicLattice.expTwist B U)) ∧
      (U ∈ fieldSpace L n k j →
        IsOrthogonalOn (edgeFormSpace L n k j) edgeFormPairing (isometryOnTangent f U))
end FiniteSide
end LeftChartFacts
namespace FullSpace.LeftChartFacts
variable {L k j j' : ℕ}
def PresentationValuesAlongCurve {E : Type} (𝒢 : Set ComplexMatrix2)
    (D : Set (Edge L k j → ComplexMatrix2)) (K : PresentationClass L k j E)
    (h : (Edge L k j → ComplexMatrix2) → E) (U : Edge L k j → ComplexMatrix2)
    (γ : ℝ → Edge L k j → ComplexMatrix2) : Prop :=
  (∀ (S : Finset (Edge L k j)) (O : Set (S → ComplexMatrix2)) (f : (S → ComplexMatrix2) → E),
    IsLocalPresentation 𝒢 D h U S O f → K S O f → ∀ᶠ t in 𝓝 (0 : ℝ), restrictToEdges S (γ t) ∈ O) ∧
  (∀ (S₁ : Finset (Edge L k j)) (O₁ : Set (S₁ → ComplexMatrix2)) (f₁ : (S₁ → ComplexMatrix2) → E)
    (S₂ : Finset (Edge L k j)) (O₂ : Set (S₂ → ComplexMatrix2)) (f₂ : (S₂ → ComplexMatrix2) → E),
    IsLocalPresentation 𝒢 D h U S₁ O₁ f₁ → K S₁ O₁ f₁ →
    IsLocalPresentation 𝒢 D h U S₂ O₂ f₂ → K S₂ O₂ f₂ →
      ∀ᶠ t in 𝓝 (0 : ℝ), f₁ (restrictToEdges S₁ (γ t)) = f₂ (restrictToEdges S₂ (γ t))) ∧
  ∀ (S : Finset (Edge L k j)) (O : Set (S → ComplexMatrix2)) (f : (S → ComplexMatrix2) → E),
    IsLocalPresentation 𝒢 D h U S O f → K S O f → ∀ t : ℝ, restrictToEdges S (γ t) ∈ O →
      γ t ∈ D → f (restrictToEdges S (γ t)) = h (γ t)
def MapDerivAlongCurves (𝒢 : Set ComplexMatrix2) (D : Set (Edge L k j → ComplexMatrix2))
    (K : PresentationClass L k j ComplexMatrix2)
    (m : (Edge L k j → ComplexMatrix2) → Edge L k j' → ComplexMatrix2)
    (U : Edge L k j → ComplexMatrix2)
    (m' : (Edge L k j → ComplexMatrix2) → Edge L k j' → ComplexMatrix2) : Prop :=
  ∀ (I : Set ℝ) (γ : ℝ → Edge L k j → ComplexMatrix2), IsDifferentiableFieldCurve 𝒢 I γ →
    γ 0 = U → ∀ c : Edge L k j', c.IsPositivelyOriented →
      PresentationValuesAlongCurve 𝒢 D K (fun U' => m U' c) U γ ∧
      ∀ (S : Finset (Edge L k j)) (O : Set (S → ComplexMatrix2))
        (f : (S → ComplexMatrix2) → ComplexMatrix2),
        IsLocalPresentation 𝒢 D (fun U' => m U' c) U S O f → K S O f →
          HasDerivAt (fun t => f (restrictToEdges S (γ t)) * (m U c)⁻¹)
            (Complex.I • m' (curveTangent γ) c) 0
def FnDerivAlongCurves (𝒢 : Set ComplexMatrix2) (D : Set (Edge L k j → ComplexMatrix2))
    (K : PresentationClass L k j ℂ) (F : (Edge L k j → ComplexMatrix2) → ℂ)
    (U : Edge L k j → ComplexMatrix2) (d : (Edge L k j → ComplexMatrix2) → ℂ) : Prop :=
  ∀ (I : Set ℝ) (γ : ℝ → Edge L k j → ComplexMatrix2), IsDifferentiableFieldCurve 𝒢 I γ →
    γ 0 = U →
    PresentationValuesAlongCurve 𝒢 D K F U γ ∧
    ∀ (S : Finset (Edge L k j)) (O : Set (S → ComplexMatrix2)) (f : (S → ComplexMatrix2) → ℂ),
      IsLocalPresentation 𝒢 D F U S O f → K S O f →
        HasDerivAt (fun t => f (restrictToEdges S (γ t))) (d (curveTangent γ)) 0
def DifferentialsFromCurves (L k j j' : ℕ) : Prop :=
  (∀ (D : Set (Edge L k j → ComplexMatrix2))
    (m : (Edge L k j → ComplexMatrix2) → Edge L k j' → ComplexMatrix2),
    IsDifferentiableFieldMap D m → ∀ U ∈ D,
      MapDerivAlongCurves PeriodicLattice.compactGaugeGroup D
        (differentiablePresentations L k j ComplexMatrix2) m U (leftDifferential D m U)) ∧
  (∀ (D : Set (Edge L k j → ComplexMatrix2)) (F : (Edge L k j → ComplexMatrix2) → ℂ),
    IsDifferentiableFn D F → ∀ U ∈ D,
      FnDerivAlongCurves PeriodicLattice.compactGaugeGroup D
        (differentiablePresentations L k j ℂ) F U (leftDeriv D F U)) ∧
  (∀ (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (D : Set (Edge L k j → ComplexMatrix2))
    (m : (Edge L k j → ComplexMatrix2) → Edge L k j' → ComplexMatrix2),
    IsHolomorphicFieldMap β D m → ∀ U ∈ D,
      MapDerivAlongCurves PeriodicLattice.complexGaugeGroup D
        (holomorphicPresentations L k j β Coordinates.ComplexCoordinates.matrixEquiv) m U
        (holLeftDifferential β D m U)) ∧
  ∀ (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (D : Set (Edge L k j → ComplexMatrix2))
    (F : (Edge L k j → ComplexMatrix2) → ℂ),
    IsHolomorphicFn β (Equiv.funUnique (Fin 1) ℂ).symm D F → ∀ U ∈ D,
      FnDerivAlongCurves PeriodicLattice.complexGaugeGroup D
        (holomorphicPresentations L k j β (Equiv.funUnique (Fin 1) ℂ).symm) F U
        (holLeftDeriv β (Equiv.funUnique (Fin 1) ℂ).symm D F U)
def CompChainRule (L k j j' j'' : ℕ) : Prop :=
  (∀ (D₁ : Set (Edge L k j → ComplexMatrix2)) (D₂ : Set (Edge L k j' → ComplexMatrix2))
    (m₁ : (Edge L k j → ComplexMatrix2) → Edge L k j' → ComplexMatrix2)
    (m₂ : (Edge L k j' → ComplexMatrix2) → Edge L k j'' → ComplexMatrix2),
    IsDifferentiableFieldMap D₁ m₁ → IsDifferentiableFieldMap D₂ m₂ →
    IsFinitelyOpen PeriodicLattice.compactGaugeGroup (compositeDomain D₁ D₂ m₁) →
      IsDifferentiableFieldMap (compositeDomain D₁ D₂ m₁) (m₂ ∘ m₁) ∧
      ∀ U ∈ compositeDomain D₁ D₂ m₁, ∀ B ∈ edgeFormSpace (meshAt L k j),
        leftDifferential (compositeDomain D₁ D₂ m₁) (m₂ ∘ m₁) U B =
          leftDifferential D₂ m₂ (m₁ U) (leftDifferential D₁ m₁ U B)) ∧
  ∀ (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (D₁ : Set (Edge L k j → ComplexMatrix2)) (D₂ : Set (Edge L k j' → ComplexMatrix2))
    (m₁ : (Edge L k j → ComplexMatrix2) → Edge L k j' → ComplexMatrix2)
    (m₂ : (Edge L k j' → ComplexMatrix2) → Edge L k j'' → ComplexMatrix2),
    IsHolomorphicFieldMap β D₁ m₁ → IsHolomorphicFieldMap β D₂ m₂ →
    IsFinitelyOpen PeriodicLattice.complexGaugeGroup (compositeDomain D₁ D₂ m₁) →
      IsHolomorphicFieldMap β (compositeDomain D₁ D₂ m₁) (m₂ ∘ m₁) ∧
      ∀ U ∈ compositeDomain D₁ D₂ m₁, ∀ B ∈ complexEdgeForms (meshAt L k j),
        holLeftDifferential β (compositeDomain D₁ D₂ m₁) (m₂ ∘ m₁) U B =
          holLeftDifferential β D₂ m₂ (m₁ U) (holLeftDifferential β D₁ m₁ U B)
def presentedPoint {S₂ : Finset (Edge L k j')} (w : S₂ → LocalData L k j ComplexMatrix2)
    (U X : Edge L k j → ComplexMatrix2) : S₂ → ComplexMatrix2 :=
  fun c' => (w c').fn fun b => ComplexMatrix2.matExp (Complex.I • X b) * U b
variable {j'' : ℕ}
def LeftFormulaViaPresentations (𝕜 : Type) [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ]
    [NormedSpace 𝕜 ComplexMatrix2] (𝒢 : Set ComplexMatrix2) (D₁ : Set (Edge L k j → ComplexMatrix2))
    (D₂ : Set (Edge L k j' → ComplexMatrix2)) (K₁ : PresentationClass L k j ComplexMatrix2)
    (K₂ : PresentationClass L k j' ComplexMatrix2)
    (m₁ : (Edge L k j → ComplexMatrix2) → Edge L k j' → ComplexMatrix2)
    (m₂ : (Edge L k j' → ComplexMatrix2) → Edge L k j'' → ComplexMatrix2)
    (U B : Edge L k j → ComplexMatrix2) (c : Edge L k j'') (v : ComplexMatrix2) : Prop :=
  ∀ (S₂ : Finset (Edge L k j')) (O₂ : Set (S₂ → ComplexMatrix2))
    (f₂ : (S₂ → ComplexMatrix2) → ComplexMatrix2) (w : S₂ → LocalData L k j ComplexMatrix2),
    IsLocalPresentation 𝒢 D₂ (fun W => m₂ W c) (m₁ U) S₂ O₂ f₂ → K₂ S₂ O₂ f₂ →
    (∀ c' : S₂, IsLocalPresentation 𝒢 D₁ (fun U' => m₁ U' c') U (w c').support (w c').region
        (w c').fn ∧
      K₁ (w c').support (w c').region (w c').fn) →
    (∀ᶠ t in 𝓝 (0 : 𝕜), presentedPoint w U (algebraMap 𝕜 ℂ t • B) ∈ O₂) ∧
      logDirectionalDeriv 𝕜 (fun X => f₂ (presentedPoint w U X))
        (f₂ (presentedPoint w U 0)) B = v
def ChainRuleViaPresentations (L k j j' j'' : ℕ) : Prop :=
  (∀ (D₁ : Set (Edge L k j → ComplexMatrix2)) (D₂ : Set (Edge L k j' → ComplexMatrix2))
    (m₁ : (Edge L k j → ComplexMatrix2) → Edge L k j' → ComplexMatrix2)
    (m₂ : (Edge L k j' → ComplexMatrix2) → Edge L k j'' → ComplexMatrix2),
    IsDifferentiableFieldMap D₁ m₁ → IsDifferentiableFieldMap D₂ m₂ →
    ∀ U ∈ compositeDomain D₁ D₂ m₁, ∀ B ∈ edgeFormSpace (meshAt L k j),
    ∀ c : Edge L k j'', c.IsPositivelyOriented →
      LeftFormulaViaPresentations ℝ PeriodicLattice.compactGaugeGroup D₁ D₂
        (differentiablePresentations L k j ComplexMatrix2)
        (differentiablePresentations L k j' ComplexMatrix2) m₁ m₂ U B c
        (leftDifferential D₂ m₂ (m₁ U) (leftDifferential D₁ m₁ U B) c)) ∧
  ∀ (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (D₁ : Set (Edge L k j → ComplexMatrix2)) (D₂ : Set (Edge L k j' → ComplexMatrix2))
    (m₁ : (Edge L k j → ComplexMatrix2) → Edge L k j' → ComplexMatrix2)
    (m₂ : (Edge L k j' → ComplexMatrix2) → Edge L k j'' → ComplexMatrix2),
    IsHolomorphicFieldMap β D₁ m₁ → IsHolomorphicFieldMap β D₂ m₂ →
    ∀ U ∈ compositeDomain D₁ D₂ m₁, ∀ B ∈ complexEdgeForms (meshAt L k j),
    ∀ c : Edge L k j'', c.IsPositivelyOriented →
      LeftFormulaViaPresentations ℂ PeriodicLattice.complexGaugeGroup D₁ D₂
        (holomorphicPresentations L k j β Coordinates.ComplexCoordinates.matrixEquiv)
        (holomorphicPresentations L k j' β Coordinates.ComplexCoordinates.matrixEquiv) m₁ m₂ U B c
        (holLeftDifferential β D₂ m₂ (m₁ U) (holLeftDifferential β D₁ m₁ U B) c)
def GaugeOrbitTangent (L k j : ℕ) : Prop :=
  (∀ U ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup,
    ∀ l : Vertex L k j → ComplexMatrix2, (∀ x, l x ∈ ComplexMatrix2.traceless) →
    (∀ b : Edge L k j, b.IsPositivelyOriented → ∃ C r : ℝ, 0 < r ∧ ∀ t : ℂ, ‖t‖ < r →
      ∃ X ∈ ComplexMatrix2.traceless, ComplexMatrix2.operatorNorm X ≤ C * ‖t‖ ^ 2 ∧
        gaugeAct (expVertexFn (t • l)) U b =
          ComplexMatrix2.matExp (Complex.I • (-(t • covDiff U l b) + X)) * U b) ∧
    (∀ b : Edge L k j, b.IsPositivelyOriented → DifferentiableAt ℝ
      (fun t : ℝ => gaugeAct (expVertexFn ((t : ℂ) • l)) U b) 0) ∧
    curveTangent (fun t : ℝ => gaugeAct (expVertexFn ((t : ℂ) • l)) U) = -covDiff U l ∧
    ∀ (x : Vertex L k j) (μ : Fin 4), (InfiniteLattice.Link.forwardFrom x μ).IsPositivelyOriented →
      covDiff U l (InfiniteLattice.Link.forwardFrom x μ) =
        ((meshAt L k j : ℝ) : ℂ) • (((meshAt L k j)⁻¹ : ℝ) : ℂ) •
          (ComplexMatrix2.conjugateBy (U (InfiniteLattice.Link.forwardFrom x μ))
            (l (x + InfiniteLattice.axisStep (meshAt L k j) μ)) - l x)) ∧
  ∀ l : Vertex L k j → ComplexMatrix2,
    covDiff (fun _ : Edge L k j => (1 : ComplexMatrix2)) l = vertexCoboundary l
def GaugeEquivarianceForms (L k j : ℕ) : Prop :=
  ∀ u : Vertex L k j → ComplexMatrix2, (∀ x, u x ∈ PeriodicLattice.complexGaugeGroup) →
    (∀ U ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup,
      ∀ B ∈ complexEdgeForms (meshAt L k j),
        expTwist (adjointForm u B) (gaugeAct u U) = gaugeAct u (expTwist B U)) ∧
    (∀ B ∈ complexEdgeForms (meshAt L k j), ∀ B' ∈ complexEdgeForms (meshAt L k j),
      HasFiniteSupp (restrictToPositiveEdges B) ∨ HasFiniteSupp (restrictToPositiveEdges B') →
        finiteEdgePairing (adjointForm u B) (adjointForm u B') = finiteEdgePairing B B') ∧
    ∀ l l' : Vertex L k j → ComplexMatrix2, (∀ x, l x ∈ ComplexMatrix2.traceless) →
      (∀ x, l' x ∈ ComplexMatrix2.traceless) →
      HasFiniteSupp l ∨ HasFiniteSupp l' →
        traceFinsumPairing (adjointVertexFn u l) (adjointVertexFn u l') = traceFinsumPairing l l'
def IsometryEquivarianceForms (L k j : ℕ) : Prop :=
  ∀ f : InfiniteLattice.AmbientSpace → InfiniteLattice.AmbientSpace, IsDistancePreserving f →
    MapsSublatticeOnto (meshAt L k j) f →
    ∀ U ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup,
      ∀ B ∈ complexEdgeForms (meshAt L k j),
        expTwist (isometryOnTangent f U B) (pushField f U) = pushField f (expTwist B U)
end FullSpace.LeftChartFacts
end Tower
end YangMills.Construction
end
