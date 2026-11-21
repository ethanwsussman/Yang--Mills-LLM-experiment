import YangMills.Construction.HilbertSpace.FormsAndOperators
import YangMills.Construction.SpectralTheory.BorelProjectionValuedMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ComplexConjugate ComplexOrder ENNReal InnerProductSpace
noncomputable section
namespace YangMills.Construction.BorelCalculus
open BorelSpectral
open HilbertSpaceBasics (UnboundedOp IsAdjointOf IsPositiveOp IsSelfAdjointOp IsUnitaryOp)
variable {n : ℕ} {Y : Set (Fin n → ℝ)} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
def IsBoundedFn {X : Type*} (f : X → ℂ) : Prop := ∃ c : ℝ, ∀ x, ‖f x‖ ≤ c
def IsRealValued {X : Type*} (f : X → ℂ) : Prop := ∀ x, (f x).im = 0
def conjFn {X : Type*} (f : X → ℂ) : X → ℂ := fun x => conj (f x)
def HasDomainAndAction (T : UnboundedOp H) (D : Set H) (w : H → H) : Prop :=
  (T.domain : Set H) = D ∧ ∀ v : T.domain, T v = w v
def zeroLocus {f : Y → ℂ} (hf : Measurable f) : BorelSubsets Y :=
  ⟨f ⁻¹' {0}, hf (measurableSet_singleton 0)⟩
def nonzeroLocus {f : Y → ℂ} (hf : Measurable f) : BorelSubsets Y :=
  ⟨(f ⁻¹' {0})ᶜ, (hf (measurableSet_singleton 0)).compl⟩
def negativeLocus {f : Y → ℂ} (hf : Measurable f) : BorelSubsets Y :=
  ⟨{y | (f y).re < 0}, measurableSet_lt (Complex.measurable_re.comp hf) measurable_const⟩
def traceOfClosed (Y : Set (Fin n → ℝ)) {Z : Set (Fin n → ℝ)} (hZ : IsClosed Z) : BorelSubsets Y :=
  ⟨Subtype.val ⁻¹' Z, measurable_subtype_coe hZ.measurableSet⟩
def boxProduct (S : Fin n → BorelSubsets ℝ) : BorelSubsets (Set.univ : Set (Fin n → ℝ)) :=
  ⟨{y | ∀ i, y.1 i ∈ (S i).1}, by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i =>
      ((measurable_pi_apply i).comp measurable_subtype_coe) (S i).2⟩
variable [CompleteSpace H]
structure BoundedFunctionalCalculus (E : SpectralMeasure Y H) : Prop where
  existsUnique_op : ∀ f : Y → ℂ, Measurable f → IsBoundedFn f →
    ∃! T : H →L[ℂ] H, E.IsDiagonalIntegral f T
  indicator : ∀ S : BorelSubsets Y, E.integralOp (S.1.indicator 1) = E S
  add : ∀ f g : Y → ℂ, Measurable f → IsBoundedFn f → Measurable g → IsBoundedFn g →
    E.integralOp (f + g) = E.integralOp f + E.integralOp g
  smul : ∀ (z : ℂ) (f : Y → ℂ), Measurable f → IsBoundedFn f →
    E.integralOp (z • f) = z • E.integralOp f
  mul : ∀ f g : Y → ℂ, Measurable f → IsBoundedFn f → Measurable g → IsBoundedFn g →
    E.integralOp (f * g) = E.integralOp f * E.integralOp g
  star_eq : ∀ f : Y → ℂ, Measurable f → IsBoundedFn f →
    E.integralOp (conjFn f) = star (E.integralOp f)
  inner_eq : ∀ f : Y → ℂ, Measurable f → IsBoundedFn f → ∀ u v : H,
    ⟪u, E.integralOp f v⟫_ℂ = E.polarizedIntegral f u v
  diagMeasure_eq : ∀ f : Y → ℂ, Measurable f → IsBoundedFn f → ∀ (v : H) (S : BorelSubsets Y),
    E.diagMeasure (E.integralOp f v) S.1 = ∫⁻ y in S.1, ‖f y‖ₑ ^ 2 ∂E.diagMeasure v
  norm_sq : ∀ f : Y → ℂ, Measurable f → IsBoundedFn f → ∀ v : H,
    ‖E.integralOp f v‖ ^ 2 = ∫ y, ‖f y‖ ^ 2 ∂E.diagMeasure v
  integral_le : ∀ f : Y → ℂ, Measurable f → IsBoundedFn f → ∀ v : H,
    ∫ y, ‖f y‖ ^ 2 ∂E.diagMeasure v ≤ (⨆ y, ‖f y‖) ^ 2 * ‖v‖ ^ 2
  isSelfAdjoint : ∀ f : Y → ℂ, Measurable f → IsBoundedFn f → IsRealValued f →
    IsSelfAdjoint (E.integralOp f)
  isPositive : ∀ f : Y → ℂ, Measurable f → IsBoundedFn f → (∀ y, 0 ≤ f y) →
    IsPositiveOp (E.integralOp f)
  isUnitary : ∀ f : Y → ℂ, Measurable f → (∀ y, ‖f y‖ = 1) → IsUnitaryOp (E.integralOp f)
  diagMeasure_compl : ∀ (S : BorelSubsets Y) (v : H), v ∈ Set.range (E S) →
    E.diagMeasure v S.1ᶜ = 0
  apply_empty : E ⟨∅, MeasurableSet.empty⟩ = 0
  apply_subset : ∀ S S' : BorelSubsets Y, E S = 0 → S'.1 ⊆ S.1 → E S' = 0
  apply_iUnion : ∀ (ι : Type) [Countable ι] (S : ι → BorelSubsets Y), (∀ i, E (S i) = 0) →
    E ⟨⋃ i, (S i).1, MeasurableSet.iUnion fun i => (S i).2⟩ = 0
def StrongConvergence (E : SpectralMeasure Y H) : Prop :=
  ∀ (f : ℕ → Y → ℂ) (g : Y → ℂ) (c : ℝ) (S₀ : BorelSubsets Y), (∀ r, Measurable (f r)) →
    Measurable g → (∀ r y, ‖f r y‖ ≤ c) → E.IsCarriedBy S₀ →
    (∀ y ∈ S₀.1, Tendsto (fun r => f r y) atTop (𝓝 (g y))) →
    E.integralDom g = Set.univ ∧
      ∀ v, Tendsto (fun r => E.integralOp (f r) v) atTop (𝓝 (E.integralApply g v))
def CommutesWithIntegralOps (E : SpectralMeasure Y H) : Prop :=
  ∀ B : H →L[ℂ] H, (∀ S, Commute B (E S)) → ∀ f : Y → ℂ, Measurable f → IsBoundedFn f →
    Commute B (E.integralOp f)
structure UnboundedFunctionalCalculus (E : SpectralMeasure Y H) : Prop where
  exists_op : ∀ f : Y → ℂ, Measurable f → ∃ T : UnboundedOp H,
    Dense (T.domain : Set H) ∧ HasDomainAndAction T (E.integralDom f) (E.integralApply f)
  tendsto_truncate : ∀ f : Y → ℂ, Measurable f → ∀ v ∈ E.integralDom f,
    Tendsto (fun r => E.integralOp (truncate f r) v) atTop (𝓝 (E.integralApply f v))
  norm_sub_sq : ∀ f g : Y → ℂ, Measurable f → Measurable g → IsBoundedFn g →
    ∀ v ∈ E.integralDom f,
      ‖E.integralApply f v - E.integralOp g v‖ ^ 2 = ∫ y, ‖f y - g y‖ ^ 2 ∂E.diagMeasure v
  norm_sq : ∀ f : Y → ℂ, Measurable f → ∀ v ∈ E.integralDom f,
    ‖E.integralApply f v‖ ^ 2 = ∫ y, ‖f y‖ ^ 2 ∂E.diagMeasure v
  inner_eq : ∀ f : Y → ℂ, Measurable f → ∀ v ∈ E.integralDom f,
    ⟪v, E.integralApply f v⟫_ℂ = ∫ y, f y ∂E.diagMeasure v
  adjoint : ∀ f : Y → ℂ, Measurable f → ∀ T T' : UnboundedOp H,
    HasDomainAndAction T (E.integralDom f) (E.integralApply f) →
    HasDomainAndAction T' (E.integralDom (conjFn f))
      (E.integralApply (conjFn f)) → IsAdjointOf T' T
  isSelfAdjoint : ∀ f : Y → ℂ, Measurable f → IsRealValued f → ∀ T : UnboundedOp H,
    HasDomainAndAction T (E.integralDom f) (E.integralApply f) → IsSelfAdjointOp T
  integralOp_mem : ∀ f g : Y → ℂ, Measurable f → Measurable g → IsBoundedFn g →
    ∀ v ∈ E.integralDom f, E.integralOp g v ∈ E.integralDom f
  integralApply_integralOp : ∀ f g : Y → ℂ, Measurable f → Measurable g →
    IsBoundedFn g → ∀ v ∈ E.integralDom f,
      E.integralApply f (E.integralOp g v) = E.integralOp g (E.integralApply f v)
  integralApply_mul : ∀ f g : Y → ℂ, Measurable f → Measurable g → IsBoundedFn g →
    ∀ v ∈ E.integralDom f, v ∈ E.integralDom (f * g) ∧
      E.integralApply f (E.integralOp g v) = E.integralApply (f * g) v
  range_subset_dom : ∀ f g : Y → ℂ, Measurable f → Measurable g → IsBoundedFn g →
    IsBoundedFn (f * g) → ∀ v, E.integralOp g v ∈ E.integralDom f ∧
      E.integralApply f (E.integralOp g v) = E.integralOp (f * g) v
  dom_subset : ∀ f g : Y → ℂ, Measurable f → Measurable g → ∀ S₀ : BorelSubsets Y,
    E.IsCarriedBy S₀ → (∀ y ∈ S₀.1, ‖f y‖ ≤ ‖g y‖) → E.integralDom g ⊆ E.integralDom f
  congr : ∀ f g : Y → ℂ, Measurable f → Measurable g → ∀ S₀ : BorelSubsets Y, E.IsCarriedBy S₀ →
    (∀ y ∈ S₀.1, f y = g y) → E.integralDom f = E.integralDom g ∧
      ∀ v ∈ E.integralDom f, E.integralApply f v = E.integralApply g v
structure KernelAndPositivity (E : SpectralMeasure Y H) : Prop where
  kernel_eq : ∀ (f : Y → ℂ) (hf : Measurable f),
    {v | v ∈ E.integralDom f ∧ E.integralApply f v = 0} = Set.range (E (zeroLocus hf))
  eq_zero_iff : ∀ (f : Y → ℂ) (hf : Measurable f),
    (∀ v ∈ E.integralDom f, E.integralApply f v = 0) ↔ E (nonzeroLocus hf) = 0
  nonneg_iff : ∀ (f : Y → ℂ) (hf : Measurable f), IsRealValued f →
    ((∀ v ∈ E.integralDom f, 0 ≤ ⟪v, E.integralApply f v⟫_ℂ) ↔ E (negativeLocus hf) = 0)
structure PushforwardProperties (E : SpectralMeasure Y H) : Prop where
  diagMeasure_pushforward : ∀ {m : ℕ} {Y' : Set (Fin m → ℝ)} (hm : 1 ≤ m) (hY' : MeasurableSet Y')
    (p : Y → Y') (hp : Measurable p) (v : H),
    (E.pushforward hm hY' p hp).diagMeasure v = (E.diagMeasure v).map p
  integral_pushforward : ∀ {m : ℕ} {Y' : Set (Fin m → ℝ)} (hm : 1 ≤ m) (hY' : MeasurableSet Y')
    (p : Y → Y') (hp : Measurable p) (f : Y' → ℂ), Measurable f →
    (E.pushforward hm hY' p hp).integralDom f = E.integralDom (f ∘ p) ∧
      ∀ v ∈ E.integralDom (f ∘ p),
        (E.pushforward hm hY' p hp).integralApply f v = E.integralApply (f ∘ p) v
  pushforward_pushforward : ∀ {m m' : ℕ} {Y' : Set (Fin m → ℝ)} {Y'' : Set (Fin m' → ℝ)}
    (hm : 1 ≤ m) (hm' : 1 ≤ m') (hY' : MeasurableSet Y') (hY'' : MeasurableSet Y'') (p : Y → Y')
    (q : Y' → Y'') (hp : Measurable p) (hq : Measurable q),
    (E.pushforward hm hY' p hp).pushforward hm' hY'' q hq =
      E.pushforward hm' hY'' (q ∘ p) (hq.comp hp)
  pushforward_congr : ∀ {m : ℕ} {Y' : Set (Fin m → ℝ)} (hm : 1 ≤ m) (hY' : MeasurableSet Y')
    (p p₂ : Y → Y') (hp : Measurable p) (hp₂ : Measurable p₂) (S₀ : BorelSubsets Y),
    E.IsCarriedBy S₀ → (∀ y ∈ S₀.1, p y = p₂ y) → E.pushforward hm hY' p hp = E.pushforward hm hY' p₂ hp₂
structure EssSupportProperties (E : SpectralMeasure Y H) : Prop where
  isClosed_essSupport : IsClosed E.essSupport
  isCarriedBy_essSupport : ∀ h : IsClosed E.essSupport, E.IsCarriedBy (traceOfClosed Y h)
  essSupport_subset : ∀ (Z : Set (Fin n → ℝ)) (hZ : IsClosed Z), E.IsCarriedBy (traceOfClosed Y hZ) →
    E.essSupport ⊆ Z
  isCarriedBy_iff : ∀ (Z : Set (Fin n → ℝ)) (hZ : IsClosed Z),
    E.IsCarriedBy (traceOfClosed Y hZ) ↔ E.essSupport ⊆ Z
structure MarginalProperties (E : SpectralMeasure (Set.univ : Set (Fin n → ℝ)) H) : Prop where
  apply_boxProduct : ∀ S : Fin n → BorelSubsets ℝ,
    E (boxProduct S) = (List.ofFn fun i => E.coordMarginal i (realLineSet (S i))).prod
  commute : ∀ (i j : Fin n) (S S' : BorelSubsets (Set.univ : Set (Fin 1 → ℝ))),
    Commute (E.coordMarginal i S) (E.coordMarginal j S')
  eq_of_coordMarginal_eq : ∀ E' : SpectralMeasure (Set.univ : Set (Fin n → ℝ)) H,
    (∀ i, E'.coordMarginal i = E.coordMarginal i) → E' = E
end YangMills.Construction.BorelCalculus
