import YangMills.Construction.Lattice.BondsWithTheirReverses
import YangMills.Construction.Lattice.ContinuationOfTheMinimiserUnderIsometriesProof
import YangMills.Construction.Lattice.HolomorphicMapsEqualNearRealPointsAreEqual
import YangMills.Construction.Lattice.InnerBareBondsReachANode
import YangMills.Construction.Lattice.IsometryCovarianceOfRegularSetsAndAxialRepresentatives
import YangMills.Construction.Lattice.IsometryCovarianceOfTowersAndCubesOfAStep
import YangMills.Construction.Lattice.TowerConfigurationsOfTheContinuationUnderIsometriesProof
import YangMills.Construction.Matrices.RepresentationsFieldsAndSmoothFunctionsOnG
import YangMills.Construction.RunningCouplingSlope.PlainIteratesAreHolomorphicAtARadiusProof
import YangMills.Construction.Towers.ConfigurationsOnFiniteBondSetsProof
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice
namespace ContinuationOrbits
open Coordinates Matrices Matrices.GroupLieProduct
section Holomorphy
variable {N : ℕ} {ι τ : Type}
def IsSeparatelyHolomorphic {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (O : Set (ComplexCoordinates N)) (h : ComplexCoordinates N → E) : Prop :=
  ContinuousOn h O ∧ ∀ a ∈ O, ∀ j : Fin N, ∀ᶠ ζ in 𝓝 (0 : ℂ),
    DifferentiableAt ℂ (fun ζ : ℂ => h (a + ζ • ComplexCoordinates.stdBasisVector j)) ζ
theorem IsSeparatelyHolomorphic.const {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (O : Set (ComplexCoordinates N)) (X : E) : IsSeparatelyHolomorphic O fun _ => X :=
  ⟨continuousOn_const, fun _ _ _ => Eventually.of_forall fun _ => differentiableAt_const _⟩
theorem IsSeparatelyHolomorphic.mul {O : Set (ComplexCoordinates N)}
    {f₁ f₂ : ComplexCoordinates N → ComplexMatrix2}
    (a₁ : IsSeparatelyHolomorphic O f₁) (a₂ : IsSeparatelyHolomorphic O f₂) :
    IsSeparatelyHolomorphic O fun w => f₁ w * f₂ w :=
  ⟨a₁.1.mul a₂.1, fun a ha j => ((a₁.2 a ha j).and (a₂.2 a ha j)).mono fun _ x => x.1.mul x.2⟩
theorem IsSeparatelyHolomorphic.clm {O : Set (ComplexCoordinates N)}
    {f : ComplexCoordinates N → ComplexMatrix2}
    (T : ComplexMatrix2 →L[ℂ] ComplexMatrix2) (a₁ : IsSeparatelyHolomorphic O f) :
    IsSeparatelyHolomorphic O fun w => T (f w) :=
  ⟨T.continuous.comp_continuousOn a₁.1, fun a ha j => (a₁.2 a ha j).mono fun _ x =>
    T.differentiableAt.comp _ x⟩
theorem IsSeparatelyHolomorphic.component [Fintype τ] {O : Set (ComplexCoordinates N)}
    {f : ComplexCoordinates N → τ → ComplexMatrix2} (a₁ : IsSeparatelyHolomorphic O f) (c : τ) :
    IsSeparatelyHolomorphic O fun w => f w c :=
  ⟨(continuous_apply c).comp_continuousOn a₁.1, fun a ha j => (a₁.2 a ha j).mono fun _ x =>
    differentiableAt_pi.1 x c⟩
theorem IsSeparatelyHolomorphic.of_components [Fintype τ] {O : Set (ComplexCoordinates N)}
    {f : ComplexCoordinates N → τ → ComplexMatrix2}
    (H : ∀ c, IsSeparatelyHolomorphic O fun w => f w c) :
    IsSeparatelyHolomorphic O f :=
  ⟨continuousOn_pi.2 fun c => (H c).1, fun a ha j =>
    (eventually_all.2 fun c => (H c).2 a ha j).mono fun _ x => differentiableAt_pi.2 x⟩
def matrixPiLinearEquiv {k : ℕ} (ν : τ ≃ Fin k) :
    (τ → ComplexMatrix2) ≃ₗ[ℂ] ComplexCoordinates
      (ComplexCoordinates.productDim fun _ : Fin k => ComplexCoordinates.Component.matrix) :=
  { matrixPiEquiv ν with
    map_add' := fun x y => by funext j; rfl
    map_smul' := fun c x => by funext j; rfl }
theorem isHolomorphicIn_iff [Fintype τ] {k : ℕ} (ν : τ ≃ Fin k) (O : Set (ComplexCoordinates N))
    (f : ComplexCoordinates N → τ → ComplexMatrix2) :
    ComplexCoordinates.IsHolomorphicIn O (matrixPiEquiv ν ∘ f) ↔
      IsOpen O ∧ IsSeparatelyHolomorphic O f := by
  let φ := (matrixPiLinearEquiv ν).toContinuousLinearEquiv
  constructor
  · rintro ⟨ho, hc, hd⟩
    refine ⟨ho, φ.comp_continuousOn_iff.1 hc, fun a ha j => (hd a ha j).mono fun ζ x => ?_⟩
    exact φ.comp_differentiableAt_iff.1 x
  · rintro ⟨ho, hc, hd⟩
    refine ⟨ho, φ.comp_continuousOn_iff.2 hc, fun a ha j => (hd a ha j).mono fun ζ x => ?_⟩
    exact φ.comp_differentiableAt_iff.2 x
def adjugateLinearMap : ComplexMatrix2 →ₗ[ℂ] ComplexMatrix2 where
  toFun := Matrix.adjugate
  map_add' X Y := by
    simp only [Matrix.adjugate_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring
  map_smul' c X := by
    simp only [Matrix.adjugate_fin_two, RingHom.id_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
variable [Fintype ι]
def HolOn (O : Set (ι → ComplexMatrix2)) (f : (ι → ComplexMatrix2) → ComplexMatrix2) : Prop :=
  ∀ (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (ν : ι ≃ Fin (Fintype.card ι)),
    IsSeparatelyHolomorphic (tupleOfCoords b ν ⁻¹' O) (f ∘ tupleOfCoords b ν)
theorem HolOn.const (O : Set (ι → ComplexMatrix2)) (X : ComplexMatrix2) : HolOn O fun _ => X :=
  fun _ _ => IsSeparatelyHolomorphic.const _ X
theorem HolOn.mul {O : Set (ι → ComplexMatrix2)} {f₁ f₂ : (ι → ComplexMatrix2) → ComplexMatrix2}
    (a₁ : HolOn O f₁) (a₂ : HolOn O f₂) :
    HolOn O fun B => f₁ B * f₂ B :=
  fun b ν => (a₁ b ν).mul (a₂ b ν)
theorem HolOn.adjugate {O : Set (ι → ComplexMatrix2)} {f : (ι → ComplexMatrix2) → ComplexMatrix2}
    (a₁ : HolOn O f) :
    HolOn O fun B => Matrix.adjugate (f B) :=
  fun b ν => (a₁ b ν).clm (LinearMap.toContinuousLinearMap adjugateLinearMap)
variable [Fintype τ]
theorem holOn_component {O : Set (ι → ComplexMatrix2)} {f : (ι → ComplexMatrix2) → τ → ComplexMatrix2}
    (hf : IsHolomorphicMatrixValued O f) (c : τ) : HolOn O fun B => f B c :=
  fun b ν => (((isHolomorphicIn_iff _ _ _).1 ((hf b (Fintype.equivFin τ)).2 ν)).2).component c
theorem isHolomorphicMatrixValued_of_holOn {O : Set (ι → ComplexMatrix2)}
    {f g : (ι → ComplexMatrix2) → τ → ComplexMatrix2}
    (hf : IsHolomorphicMatrixValued O f) (hg : ∀ c, HolOn O fun B => g B c) :
    IsHolomorphicMatrixValued O g :=
  fun b ν => ⟨(hf b ν).1, fun ν' => (isHolomorphicIn_iff ν _ _).2
    ⟨((hf b ν).2 ν').1, IsSeparatelyHolomorphic.of_components fun c => hg c b ν'⟩⟩
end Holomorphy
section Chains
variable {L m : ℕ} {j : ℤ} {ι : Type} [Fintype ι]
def IsGaugeRelating (ℬ : Set (Bond L m j)) (P : Site L m j → Prop) (W₁ W₂ : Bond L m j → ComplexMatrix2)
    (u : Site L m j → ComplexMatrix2) : Prop :=
  (∀ x, (u x).det = 1) ∧ (∀ x, P x → u x = 1) ∧
    ∀ c ∈ ℬ, W₁ c = u c.source * W₂ c * (u c.target)⁻¹
theorem inv_eq_adjugate_of_det_eq_one {X : ComplexMatrix2} (h : X.det = 1) :
    X⁻¹ = Matrix.adjugate X := by apply _root_.YangMills.SharedProofs.p104891 <;> assumption
theorem target_gauge_eq {w₁ w₂ p q : ComplexMatrix2} (h₁ : w₁.det = 1) (hq : q.det = 1)
    (h : w₁ = p * w₂ * q⁻¹) : q = Matrix.adjugate w₁ * p * w₂ := by
  have hu : IsUnit q.det := by rw [hq]; exact isUnit_one
  have e₁ : w₁ * q = p * w₂ := by
    rw [h, mul_assoc (p * w₂), Matrix.nonsing_inv_mul _ hu, mul_one]
  have e₂ : Matrix.adjugate w₁ * w₁ = 1 := by rw [Matrix.adjugate_mul, h₁, one_smul]
  calc q = (Matrix.adjugate w₁ * w₁) * q := by rw [e₂, one_mul]
    _ = Matrix.adjugate w₁ * (w₁ * q) := by rw [mul_assoc]
    _ = _ := by rw [e₁, mul_assoc]
variable {O S : Set (ι → ComplexMatrix2)} {ℬ : Set (Bond L m j)} {P : Site L m j → Prop}
  {W₁ W₂ : (ι → ComplexMatrix2) → Bond L m j → ComplexMatrix2}
theorem exists_holOn_gauge_value (hSO : S ⊆ O) (h₁ : ∀ c ∈ ℬ, HolOn O fun B => W₁ B c)
    (h₂ : ∀ c ∈ ℬ, HolOn O fun B => W₂ B c) (d₁ : ∀ B ∈ O, ∀ c ∈ ℬ, (W₁ B c).det = 1)
    (d₂ : ∀ B ∈ O, ∀ c ∈ ℬ, (W₂ B c).det = 1) {a x : Site L m j} (hP : P a)
    (hr : Relation.ReflTransGen (fun x y : Site L m j => ∃ c ∈ ℬ, c.source = x ∧ c.target = y) a x) :
    ∃ h : (ι → ComplexMatrix2) → ComplexMatrix2, HolOn O h ∧ (∀ B ∈ O, (h B).det = 1) ∧
      ∀ B ∈ S, ∀ u, IsGaugeRelating ℬ P (W₁ B) (W₂ B) u → h B = u x := by
  induction hr with
  | refl =>
    exact ⟨fun _ => 1, HolOn.const _ _, fun _ _ => Matrix.det_one,
      fun B _ u hu => (hu.2.1 a hP).symm⟩
  | tail _ hstep ih =>
    obtain ⟨c, hc, e₁, e₂⟩ := hstep
    subst e₁ e₂
    obtain ⟨h, hh, hd, hu⟩ := ih
    refine ⟨fun B => Matrix.adjugate (W₁ B c) * h B * W₂ B c,
      ((h₁ c hc).adjugate.mul hh).mul (h₂ c hc), fun B hB => ?_, fun B hB u hg => ?_⟩
    · simp [Matrix.det_mul, Matrix.det_adjugate, d₁ B hB c hc, d₂ B hB c hc, hd B hB]
    · change Matrix.adjugate (W₁ B c) * h B * W₂ B c = u c.target
      rw [hu B hB u hg]
      exact (target_gauge_eq (d₁ B (hSO hB) c hc) (hg.1 _) (hg.2.2 c hc)).symm
theorem exists_holOn_gauge (hSO : S ⊆ O) (h₁ : ∀ c ∈ ℬ, HolOn O fun B => W₁ B c)
    (h₂ : ∀ c ∈ ℬ, HolOn O fun B => W₂ B c) (d₁ : ∀ B ∈ O, ∀ c ∈ ℬ, (W₁ B c).det = 1)
    (d₂ : ∀ B ∈ O, ∀ c ∈ ℬ, (W₂ B c).det = 1) (hrev : ∀ c ∈ ℬ, c.opposite ∈ ℬ)
    (hreach : ∀ c ∈ ℬ, ∃ a, P a ∧ Relation.ReflTransGen
      (fun x y : Site L m j => ∃ c ∈ ℬ, c.source = x ∧ c.target = y) a c.source)
    (hreal : ∀ B ∈ S, ∃ u, IsGaugeRelating ℬ P (W₁ B) (W₂ B) u) :
    ∃ F : Site L m j → (ι → ComplexMatrix2) → ComplexMatrix2, (∀ x, HolOn O (F x)) ∧
      (∀ x, ∀ B ∈ O, (F x B).det = 1) ∧
      (∀ x, P x → ∀ B, F x B = 1) ∧ (∀ x, (∀ c ∈ ℬ, c.source ≠ x) → ∀ B, F x B = 1) ∧
      ∀ B ∈ S, ∀ c ∈ ℬ,
        W₁ B c = F c.source B * W₂ B c * Matrix.adjugate (F c.target B) := by
  classical
  have key : ∀ x, ∃ h : (ι → ComplexMatrix2) → ComplexMatrix2, HolOn O h ∧
      (∀ B ∈ O, (h B).det = 1) ∧
      (P x → ∀ B, h B = 1) ∧ ((∀ c ∈ ℬ, c.source ≠ x) → ∀ B, h B = 1) ∧
      ∀ B ∈ S, ∀ u, IsGaugeRelating ℬ P (W₁ B) (W₂ B) u → (∃ c ∈ ℬ, c.source = x) → h B = u x := by
    intro x
    by_cases hx : ¬P x ∧ ∃ c ∈ ℬ, c.source = x
    · obtain ⟨hn, c, hc, rfl⟩ := hx
      obtain ⟨a, ha, hr⟩ := hreach c hc
      obtain ⟨h, hh, hd, hu⟩ := exists_holOn_gauge_value hSO h₁ h₂ d₁ d₂ ha hr
      exact ⟨h, hh, hd, fun h' => absurd h' hn, fun h' => absurd rfl (h' c hc),
        fun B hB u hg _ => hu B hB u hg⟩
    · refine ⟨fun _ => 1, HolOn.const _ _, fun _ _ => Matrix.det_one, fun _ _ => rfl,
        fun _ _ => rfl, fun B _ u hg hc => ?_⟩
      exact (hg.2.1 x (by_contra fun hn => hx ⟨hn, hc⟩)).symm
  choose F hF₁ hF₂ hF₃ hF₄ hF₅ using key
  refine ⟨F, hF₁, hF₂, hF₃, hF₄, fun B hB c hc => ?_⟩
  obtain ⟨u, hu⟩ := hreal B hB
  rw [hF₅ c.source B hB u hu ⟨c, hc, rfl⟩, hF₅ c.target B hB u hu ⟨c.opposite, hrev c hc, rfl⟩,
    ← inv_eq_adjugate_of_det_eq_one (hu.1 _)]
  exact hu.2.2 c hc
theorem gauge_relation_on_ball (hid : RealIdentityPrinciple.Statement) {r : ℝ}
    [Fintype ℬ] (hf₁ : IsHolomorphicMatrixValued (supBall ι r) fun B (c : ℬ) => W₁ B c)
    (hf₂ : IsHolomorphicMatrixValued (supBall ι r) fun B (c : ℬ) => W₂ B c)
    (d₁ : ∀ B ∈ supBall ι r, ∀ c ∈ ℬ, (W₁ B c).det = 1)
    (d₂ : ∀ B ∈ supBall ι r, ∀ c ∈ ℬ, (W₂ B c).det = 1) (hrev : ∀ c ∈ ℬ, c.opposite ∈ ℬ)
    (hreach : ∀ c ∈ ℬ, ∃ a, P a ∧ Relation.ReflTransGen
      (fun x y : Site L m j => ∃ c ∈ ℬ, c.source = x ∧ c.target = y) a c.source)
    (hS : S ⊆ supBall ι r ∩ selfAdjointFunctions ι) (hne : S.Nonempty)
    (hopen : ComplexMatrix2.IsRelativelyOpen (selfAdjointFunctions ι) S)
    (hreal : ∀ B ∈ S, ∃ u, IsGaugeRelating ℬ P (W₁ B) (W₂ B) u) :
    ∀ B ∈ supBall ι r, ∃ u : Site L m j → ComplexMatrix2, (∀ x, (u x).det = 1) ∧
      (∀ x, P x → u x = 1) ∧
      (∀ x, (∀ c ∈ ℬ, c.source ≠ x) → u x = 1) ∧
      ∀ c ∈ ℬ, W₁ B c = u c.source * W₂ B c * (u c.target)⁻¹ := by
  have hSO : S ⊆ supBall ι r := fun B hB => (hS hB).1
  have c₁ : ∀ c ∈ ℬ, HolOn (supBall ι r) fun B => W₁ B c :=
    fun c hc => holOn_component hf₁ ⟨c, hc⟩
  have c₂ : ∀ c ∈ ℬ, HolOn (supBall ι r) fun B => W₂ B c :=
    fun c hc => holOn_component hf₂ ⟨c, hc⟩
  obtain ⟨F, hF₁, hF₂, hF₃, hF₄, hF₅⟩ := exists_holOn_gauge hSO c₁ c₂ d₁ d₂ hrev hreach hreal
  have hg : IsHolomorphicMatrixValued (supBall ι r) fun B (c : ℬ) =>
      F (c : Bond L m j).source B * W₂ B c * Matrix.adjugate (F (c : Bond L m j).target B) :=
    isHolomorphicMatrixValued_of_holOn hf₁ fun c => ((hF₁ _).mul (c₂ c c.2)).mul (hF₁ _).adjugate
  have heq := hid ι ℬ r _ _ S hf₁ hg hS hne hopen fun B hB => funext fun c => hF₅ B hB c c.2
  intro B hB
  refine ⟨fun x => F x B, fun x => hF₂ x B hB, fun x hx => hF₃ x hx B,
    fun x hx => hF₄ x hx B, fun c hc => ?_⟩
  rw [inv_eq_adjugate_of_det_eq_one (hF₂ _ B hB)]
  exact congrFun (heq hB) ⟨c, hc⟩
end Chains
section Orbits
variable {L m K : ℕ} {Ω : ℕ → Set (FourTorus L m)} {S : Set (Σ j : ℕ, BondAtLevel L m K j)}
theorem inv_mem_compact {g : ComplexMatrix2} (hg : g ∈ compactGaugeGroup) :
    g⁻¹ ∈ compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
theorem det_eq_one_of_mem_compact {g : ComplexMatrix2} (hg : g ∈ compactGaugeGroup) : g.det = 1 := by apply _root_.YangMills.SharedProofs.p157 <;> assumption
theorem self_mem_orbit {T : BondAtLevel L m K 0 → ComplexMatrix2}
    (hT : ∀ b ∉ (bondsInside (Ω 0) : Set (BondAtLevel L m K 0)), T b = 1) :
    T ∈ endpointFixingOrbit Ω S T := by
  refine ⟨fun _ => 1, ⟨fun _ _ => one_mem _, fun _ _ => rfl, fun _ _ => rfl⟩, ?_⟩
  funext b
  by_cases hb : b ∈ (bondsInside (Ω 0) : Set (BondAtLevel L m K 0))
  · simp [extendByOne, if_pos hb, gaugeTransform]
  · simp only [extendByOne, if_neg hb]
    exact hT b hb
theorem mem_orbit_trans {W T R : BondAtLevel L m K 0 → ComplexMatrix2}
    (h₁ : W ∈ endpointFixingOrbit Ω S T)
    (h₂ : T ∈ endpointFixingOrbit Ω S R) : W ∈ endpointFixingOrbit Ω S R := by
  obtain ⟨u, hu, rfl⟩ := h₁
  obtain ⟨v, hv, rfl⟩ := h₂
  refine ⟨fun x => u x * v x, ⟨fun x hx => mul_mem (hu.1 x hx) (hv.1 x hx),
    fun x hx => by simp [hu.2.1 x hx, hv.2.1 x hx],
    fun x hx => by simp [hu.2.2 x hx, hv.2.2 x hx]⟩, ?_⟩
  funext b
  by_cases hb : b ∈ (bondsInside (Ω 0) : Set (BondAtLevel L m K 0))
  · simp only [extendByOne, if_pos hb, gaugeTransform, Matrix.mul_inv_rev, mul_assoc]
  · simp only [extendByOne, if_neg hb]
theorem mem_orbit_symm {W T : BondAtLevel L m K 0 → ComplexMatrix2}
    (h : W ∈ endpointFixingOrbit Ω S T)
    (hT : ∀ b ∉ (bondsInside (Ω 0) : Set (BondAtLevel L m K 0)), T b = 1) :
    T ∈ endpointFixingOrbit Ω S W := by
  obtain ⟨u, hu, rfl⟩ := h
  have hunit : ∀ x, IsUnit (u x).det := by
    intro x
    by_cases hx : x ∈ (sitesIn (Ω 0) : Set (SiteAtLevel L m K 0))
    · rw [det_eq_one_of_mem_compact (hu.1 x hx)]
      exact isUnit_one
    · rw [hu.2.1 x hx, Matrix.det_one]
      exact isUnit_one
  refine ⟨fun x => (u x)⁻¹, ⟨fun x hx => inv_mem_compact (hu.1 x hx),
    fun x hx => by simp [hu.2.1 x hx], fun x hx => by simp [hu.2.2 x hx]⟩, ?_⟩
  funext b
  by_cases hb : b ∈ (bondsInside (Ω 0) : Set (BondAtLevel L m K 0))
  · simp only [extendByOne, if_pos hb, gaugeTransform]
    rw [Matrix.nonsing_inv_nonsing_inv _ (hunit _)]
    have e₁ : (u b.source)⁻¹ * u b.source = 1 := Matrix.nonsing_inv_mul _ (hunit _)
    have e₂ : (u b.target)⁻¹ * u b.target = 1 := Matrix.nonsing_inv_mul _ (hunit _)
    calc T b = ((u b.source)⁻¹ * u b.source) * T b * ((u b.target)⁻¹ * u b.target) := by
          rw [e₁, e₂, one_mul, mul_one]
      _ = _ := by simp only [mul_assoc]
  · simp only [extendByOne, if_neg hb]
    exact hT b hb
end Orbits
section Twisted
variable {L m K : ℕ} {j : ℤ}
theorem opposite_positive_of_not
    (hor : ∀ b : Bond L m j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {b : Bond L m j} (h : ¬b.IsPositivelyOriented) : b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.PeriodicLattice.isPositivelyOriented_opposite <;> assumption
theorem opposite_not_positive
    (hor : ∀ b : Bond L m j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {b : Bond L m j} (h : b.IsPositivelyOriented) : ¬b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.PeriodicLattice.not_isPositivelyOriented_opposite <;> assumption
theorem twistedFormValue_congr
    (hor : ∀ b : Bond L m j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {σ : FourTorus L m ≃ FourTorus L m} {V₀ A a : Bond L m j → ComplexMatrix2}
    (h : ∀ b, b.IsPositivelyOriented → A b = a b) (b' : Bond L m j) :
    twistedFormValue σ V₀ A b' = twistedFormValue σ V₀ a b' := by
  unfold twistedFormValue
  split_ifs with hp
  · exact h _ hp
  · rw [h _ (opposite_positive_of_not hor hp)]
theorem expTwist_congr
    (hor : ∀ b : Bond L m j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {A a U : Bond L m j → ComplexMatrix2} (h : ∀ b, b.IsPositivelyOriented → A b = a b) :
    expTwist A U = expTwist a U := by
  funext b
  unfold expTwist
  split_ifs with hp
  · rw [h _ hp]
  · rw [h _ (opposite_positive_of_not hor hp)]
theorem transport_expTwist_eq
    (hor : ∀ b : Bond L m j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {σ : FourTorus L m ≃ FourTorus L m} {ℬ : Set (Bond L m j)} (hcl : IsReversalClosed ℬ)
    (hcl' : IsReversalClosed (bondSetTransport σ ℬ)) {V₀ : Bond L m j → ComplexMatrix2}
    (hT : IsTwistedTransportOn σ ℬ V₀) {a a' : Bond L m j → ComplexMatrix2}
    (ha : ∀ b, b.IsPositivelyOriented → a b ∈ complexLieAlgebra) (hsup : ∀ b, b ∉ ℬ → a b = 0)
    (hpos : ∀ b' ∈ bondSetTransport σ ℬ, b'.IsPositivelyOriented →
      a' b' = twistedFormValue σ V₀ a b') :
    ∀ b' ∈ bondSetTransport σ ℬ, transportGaugeField σ (expTwist a V₀) b' =
      expTwist a' (transportGaugeField σ V₀) b' := by
  classical
  intro b' hb'
  have hApos : ∀ b, b.IsPositivelyOriented → bondFormOfPositive a b = a b := fun b hb => by
    simp only [bondFormOfPositive, if_pos hb]
  have hAneg : ∀ b, ¬b.IsPositivelyOriented → bondFormOfPositive a b = -a b.opposite :=
    fun b hb => by
    simp only [bondFormOfPositive, if_neg hb]
  have hform : bondFormOfPositive a ∈ complexFormsOn ℬ := by
    refine ⟨⟨fun b hb => ?_, fun b => ?_⟩, ?_⟩
    · rw [hApos b hb]
      exact ha b hb
    · by_cases hb : b.IsPositivelyOriented
      · rw [hAneg _ (opposite_not_positive hor hb), hApos _ hb]
        rfl
      · rw [hApos _ (opposite_positive_of_not hor hb), hAneg _ hb, neg_neg]
    · funext b
      by_cases hb : b ∈ ℬ
      · exact Set.indicator_of_mem hb _
      · rw [Set.indicator_of_notMem hb]
        by_cases hp : b.IsPositivelyOriented
        · rw [hApos b hp, hsup b hb]
        · rw [hAneg b hp, hsup _ (fun h => hb (hcl b.opposite h)), neg_zero]
  have e₁ := hT.transport_expTwist _ hform b' hb'
  rw [expTwist_congr hor hApos] at e₁
  rw [e₁]
  have hval : ∀ c ∈ bondSetTransport σ ℬ, c.IsPositivelyOriented →
      twistedTransportForm σ V₀ (bondFormOfPositive a) c = a' c := fun c hc hp => by
    rw [hpos c hc hp]
    simp only [twistedTransportForm, if_pos hp]
    exact twistedFormValue_congr hor hApos c
  simp only [expTwist]
  split_ifs with hp
  · rw [hval b' hb' hp]
  · rw [hval _ (hcl' _ hb') (opposite_positive_of_not hor hp)]
theorem matExp_I_smul_mem {X : ComplexMatrix2} (hX : X ∈ compactLieAlgebra) :
    ComplexMatrix2.matExp (Complex.I • X) ∈ compactGaugeGroup := by
  obtain ⟨h₁, h₂⟩ := hX
  refine SpinHarmonics.matExp_mem_of_skewAdjoint ?_ ?_
  · rw [star_smul, Matrix.star_eq_conjTranspose, ← h₁]
    simp
  · simp only [ComplexMatrix2.fullTrace, Matrix.trace_smul] at h₂ ⊢
    rw [h₂, smul_zero]
theorem expTwist_mem_compact
    (hor : ∀ b : Bond L m j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {ℬ : Set (Bond L m j)} (hcl : IsReversalClosed ℬ) {V₀ a : Bond L m j → ComplexMatrix2}
    (hV : IsGaugeField compactGaugeGroup ℬ V₀) (ha : ∀ b, a b ∈ compactLieAlgebra) :
    ∀ b ∈ ℬ, expTwist a V₀ b ∈ compactGaugeGroup ∧
      expTwist a V₀ b.opposite = (expTwist a V₀ b)⁻¹ := by
  have hp : ∀ c ∈ ℬ, ComplexMatrix2.matExp (Complex.I • a c) * V₀ c ∈ compactGaugeGroup :=
    fun c hc => mul_mem (matExp_I_smul_mem (ha c)) (hV.1 c hc)
  intro b hb
  by_cases h : b.IsPositivelyOriented
  · simp only [expTwist, if_pos h, if_neg (opposite_not_positive hor h)]
    exact ⟨hp b hb, rfl⟩
  · simp only [expTwist, if_neg h, if_pos (opposite_positive_of_not hor h)]
    have hq := hp _ (hcl _ hb)
    refine ⟨inv_mem_compact hq, (Matrix.nonsing_inv_nonsing_inv _ ?_).symm⟩
    rw [det_eq_one_of_mem_compact hq]
    exact isUnit_one
theorem twistedFormValue_mem_compact {σ : FourTorus L m ≃ FourTorus L m}
    {V₀ a : Bond L m j → ComplexMatrix2} {b' : Bond L m j}
    (ha : ∀ b, a b ∈ compactLieAlgebra) (hV : V₀ (bondPreimage σ b').opposite ∈ compactGaugeGroup) :
    twistedFormValue σ V₀ a b' ∈ compactLieAlgebra := by
  unfold twistedFormValue
  split_ifs with hp
  · exact ha _
  · exact ComplexMatrix2.hermitianTraceless.neg_mem
      (ComplexMatrix2.conjugateBy_mem_hermitianTraceless (inv_mem_compact hV) _ (ha _))
variable {k : ℕ} {Ω : ℕ → Set (FourTorus L m)}
theorem activeBondsAt_reversalClosed {q : ℕ} : IsReversalClosed (activeBondsAt K k Ω q) := by
  rintro b ⟨⟨h₁, h₂⟩, h₃⟩
  refine ⟨⟨h₁.symm, h₂.2, h₂.1⟩, fun hi => h₃ ?_⟩
  have hi' : IsInwardPointingBond K k Ω q b.opposite := hi
  exact ⟨hi'.1, ⟨hi'.2.1.1.symm, hi'.2.1.2.2, hi'.2.1.2.1⟩, hi'.2.2.symm⟩
theorem familyAtLevel_mem_compact {S : Set (Σ j : ℕ, BondAtLevel L m K j)}
    {B : PositiveBondIn S → ComplexMatrix2}
    (hB : B ∈ selfAdjointFunctions (PositiveBondIn S)) (q : ℕ) (b : BondAtLevel L m K q) :
    familyAtLevel B q b ∈ compactLieAlgebra := by
  simp only [familyAtLevel]
  split_ifs with h
  · exact ⟨(congrFun hB.2 ⟨⟨q, b⟩, h⟩).symm, hB.1 _⟩
  · exact ComplexMatrix2.hermitianTraceless.zero_mem
theorem continuous_familyAtLevel {S : Set (Σ j : ℕ, BondAtLevel L m K j)} (q : ℕ)
    (b : BondAtLevel L m K q) :
    Continuous fun B : PositiveBondIn S → ComplexMatrix2 => familyAtLevel B q b := by
  classical
  by_cases h : (⟨q, b⟩ : Σ j : ℕ, BondAtLevel L m K j) ∈ S ∧ b.IsPositivelyOriented
  · simp only [familyAtLevel, dif_pos h]
    exact continuous_apply _
  · simp only [familyAtLevel, dif_neg h]
    exact continuous_const
theorem continuous_twistedActiveFamily (σ : FourTorus L m ≃ FourTorus L m)
    (V₀ : ∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2) :
    Continuous (twistedActiveFamily σ V₀ : ActiveFamily L m K k Ω →
      ActiveFamily L m K k (imageChain σ Ω)) := by
  classical
  refine continuous_pi fun p => ?_
  simp only [twistedActiveFamily, twistedFormValue]
  by_cases hp : (bondPreimage σ p.1.2).IsPositivelyOriented
  · simp only [if_pos hp]
    exact continuous_familyAtLevel _ _
  · simp only [if_neg hp, ComplexMatrix2.conjugateBy]
    exact ((continuous_const.mul (continuous_familyAtLevel _ _)).mul continuous_const).neg
theorem twistedActiveFamily_zero (σ : FourTorus L m ≃ FourTorus L m)
    (V₀ : ∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2) :
    twistedActiveFamily σ V₀ (0 : ActiveFamily L m K k Ω) = 0 := by
  have hfam : ∀ (q : ℕ) (c : BondAtLevel L m K q),
      familyAtLevel (0 : ActiveFamily L m K k Ω) q c = 0 := by
    intro q c
    simp only [familyAtLevel]
    split_ifs <;> rfl
  funext p
  simp only [twistedActiveFamily, twistedFormValue, hfam, ComplexMatrix2.conjugateBy]
  split_ifs <;> simp
theorem isOpen_supNorm_lt {ι : Type} [Fintype ι] {r : ℝ} (hr : 0 < r) :
    IsOpen {B : ι → ComplexMatrix2 | supNorm B < r} := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.isOpen_supNorm_lt <;> assumption
theorem regularConstrainedCriticalSet_congr {V V' : ∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2}
    (ε : ℝ) (h : ∀ q ∈ activeBondSet K k Ω, V q.1 q.2 = V' q.1 q.2) :
    regularConstrainedCriticalSet (Averaging.smoothingRadius L) ε K k Ω (activeBondSet K k Ω) V =
      regularConstrainedCriticalSet (Averaging.smoothingRadius L) ε K k Ω (activeBondSet K k Ω) V' := by apply _root_.YangMills.Construction.PeriodicLattice.ContinuedTowerFieldIsometry.regularConstrainedCriticalSet_congr <;> assumption
theorem bondPreimage_bondImage {σ : FourTorus L m ≃ FourTorus L m}
    (hσ : ∀ b : Bond L m j, ((bondImage σ b).source : FourTorus L m) = σ b.source ∧
      ((bondImage σ b).target : FourTorus L m) = σ b.target) (b : Bond L m j) :
    bondPreimage σ (bondImage σ b) = b := by apply _root_.YangMills.Construction.PeriodicLattice.MinimizerContinuationIsometry.bondPreimage_bondImage <;> assumption
theorem bondImage_mem_bondsInside_iff {σ : FourTorus L m ≃ FourTorus L m}
    (hσ : ∀ b : Bond L m j, ((bondImage σ b).source : FourTorus L m) = σ b.source ∧
      ((bondImage σ b).target : FourTorus L m) = σ b.target) (X : Set (FourTorus L m))
    (b : Bond L m j) :
    bondImage σ b ∈ (bondsInside (σ '' X) : Set (Bond L m j)) ↔
      b ∈ (bondsInside X : Set (Bond L m j)) := by apply _root_.YangMills.Construction.PeriodicLattice.MinimizerContinuationIsometry.bondImage_mem_bondsInside_iff <;> assumption
end Twisted
theorem main
    (hHol : ContinuationsUnderIsometriesHolomorphic)
    (hId : RealIdentityPrinciple.Statement)
    (hReach : InnerBondsReachEndpoint)
    (hReg : IsometryCovariantRegularSetsAndAxialGauge)
    (hTw : TwistedTransportIsometryInvariance)
    (hTow : IsometriesPreserveTowersAndStepCubes)
    (hIso : LatticeIsometryGroupActionStatement)
    (hOr : BondOrientationDichotomy) :
    IsometricContinuationsInOneComplexOrbit := by
  classical
  intro L m hL hm i hi σ hσ ε εBar rB hε hεBar hrB K k e r Ω hF hS V₀ h₁ h₂
  obtain ⟨⟨_, _, hW₁, hW₂⟩, hball⟩ :=
    hHol L m hL hm i hi σ hσ ε εBar rB hε hεBar hrB K k e r Ω hF hS V₀ h₁ h₂
  have hiK : i ≤ levelDepth K 0 := by
    obtain ⟨c, hc, hc', -⟩ := hF.2.2.2.2 0 (Nat.zero_le k)
    exact hc.trans hc'
  have hK : 0 < K := by
    have h₃ := hF.2.1
    have h₄ := hF.2.2.1
    omega
  have hG := hIso L m i hL hm hi
  have hends : ∀ b : BondAtLevel L m K 0, ((bondImage σ b).source : FourTorus L m) = σ b.source ∧
      ((bondImage σ b).target : FourTorus L m) = σ b.target :=
    (hG.2.2.2.2 σ hσ _ hiK).1.2.2.2.1
  have hσs : σ.symm ∈ latticeIsometries L m i := by
    obtain ⟨⟨H, hH⟩, -⟩ := hG.1
    have h₀ : σ ∈ H := by
      have : σ ∈ (H : Set (Equiv.Perm (FourTorus L m))) := hH ▸ hσ
      exact this
    have h₁' : σ⁻¹ ∈ H := H.inv_mem h₀
    have : σ⁻¹ ∈ (H : Set (Equiv.Perm (FourTorus L m))) := h₁'
    rw [hH] at this
    exact this
  have hends' : ∀ b : BondAtLevel L m K 0,
      ((bondImage σ.symm b).source : FourTorus L m) = σ.symm b.source ∧
      ((bondImage σ.symm b).target : FourTorus L m) = σ.symm b.target :=
    (hG.2.2.2.2 σ.symm hσs _ hiK).1.2.2.2.1
  have himage : ∀ c : BondAtLevel L m K 0, bondImage σ (bondPreimage σ c) = c :=
    fun c => bondPreimage_bondImage hends' c
  have hinner : ∀ c : BondAtLevel L m K 0,
      bondImage σ c ∈ (bondsInside (imageChain σ Ω 0) : Set (BondAtLevel L m K 0)) ↔
        c ∈ (bondsInside (Ω 0) : Set (BondAtLevel L m K 0)) :=
    fun c => bondImage_mem_bondsInside_iff hends (Ω 0) c
  have hDet : IsDeterminingChainFrom K k i Ω := ⟨hF.2.2.1, hF.2.2.2.1, hF.2.2.2.2⟩
  have hset := (hTow.1 L m i σ hL hm hi hσ).2.2.1 K k Ω hDet
  have hmem : ∀ q ≤ k, activeBondsAt K k (imageChain σ Ω) q =
      bondSetTransport σ (activeBondsAt K k Ω q) := hset.2.2.1
  have hnode : ∀ x, IsEndpointOf (activeBondSet K k (imageChain σ Ω)) (σ x) ↔
      IsEndpointOf (activeBondSet K k Ω) x := hset.2.2.2.1
  have hspec₁ : IsMinimizerContinuation ε εBar rB K k Ω V₀
      (minimizerContinuation ε εBar rB K k Ω V₀) := by
    obtain ⟨Φ, hΦ, -⟩ := id h₁
    exact Classical.epsilon_spec ⟨Φ, hΦ⟩
  have hspec₂ : IsMinimizerContinuation ε εBar rB K k (imageChain σ Ω) (datumImage σ V₀)
      (minimizerContinuation ε εBar rB K k (imageChain σ Ω) (datumImage σ V₀)) := by
    obtain ⟨Φ, hΦ, -⟩ := id h₂
    exact Classical.epsilon_spec ⟨Φ, hΦ⟩
  obtain ⟨⟨hreg, -⟩, -, hcfg₁, N₁, ⟨hN₁, D₁, ⟨O₁, hO₁, hD₁⟩, h0₁, hDN₁⟩, hrep₁⟩ := hspec₁
  obtain ⟨-, -, hcfg₂, N₂, ⟨hN₂, D₂, ⟨O₂, hO₂, hD₂⟩, h0₂, hDN₂⟩, hrep₂⟩ := hspec₂
  have hlevel : ∀ q ≤ k, -(m : ℤ) < levelDepth K q ∧ i ≤ levelDepth K q := by
    intro q hq
    obtain ⟨c, hc, hc', -⟩ := hF.2.2.2.2 q hq
    have h₃ := hF.2.2.1
    refine ⟨?_, hc.trans hc'⟩
    simp only [levelDepth]
    omega
  have hτreal : ∀ B : ActiveFamily L m K k Ω,
      B ∈ selfAdjointFunctions (PositiveBondIn (activeBondSet K k Ω)) →
      twistedActiveFamily σ V₀ B ∈
        selfAdjointFunctions (PositiveBondIn (activeBondSet K k (imageChain σ Ω))) := by
    intro B hB
    have hval : ∀ p : PositiveBondIn (activeBondSet K k (imageChain σ Ω)),
        twistedActiveFamily σ V₀ B p ∈ compactLieAlgebra := by
      rintro ⟨⟨q, b'⟩, hq, hp⟩
      have hql : q ≤ k := hq.1.1
      have hb' : b' ∈ activeBondsAt K k (imageChain σ Ω) q := ⟨hq.1.2, hq.2⟩
      rw [hmem q hql] at hb'
      obtain ⟨c, hc, rfl⟩ := hb'
      have hσq := (hG.2.2.2.2 σ hσ _ (hlevel q hql).2).1.2.2.2.1
      refine twistedFormValue_mem_compact (familyAtLevel_mem_compact hB q) ?_
      rw [bondPreimage_bondImage hσq]
      exact (hreg.1 q hql).1 _ (activeBondsAt_reversalClosed _ hc)
    refine ⟨fun p => ?_, funext fun p => ?_⟩
    · exact (hval p).2
    · exact ((hval p).1).symm
  have hcongr : ∀ B : ActiveFamily L m K k Ω,
      B ∈ selfAdjointFunctions (PositiveBondIn (activeBondSet K k Ω)) →
      ∀ q ∈ activeBondSet K k (imageChain σ Ω),
        datumImage σ (expTwistedDatum B V₀) q.1 q.2 =
          expTwistedDatum (twistedActiveFamily σ V₀ B) (datumImage σ V₀) q.1 q.2 := by
    rintro B hB ⟨q, b'⟩ hq
    have hql : q ≤ k := hq.1.1
    have hb' : b' ∈ activeBondsAt K k (imageChain σ Ω) q := ⟨hq.1.2, hq.2⟩
    have himg := hmem q hql
    have hcl' : IsReversalClosed (bondSetTransport σ (activeBondsAt K k Ω q)) := by
      rw [← himg]
      exact activeBondsAt_reversalClosed
    have hconf : IsGaugeField complexGaugeGroup (activeBondsAt K k Ω q) (V₀ q) :=
      ⟨fun b hb => det_eq_one_of_mem_compact ((hreg.1 q hql).1 b hb), (hreg.1 q hql).2⟩
    have hT := ((hTw L m i σ hL hm hi hσ).2.2.1 (levelDepth K q) (hlevel q hql).1 (hlevel q hql).2 _
      activeBondsAt_reversalClosed).2.2.1 (V₀ q) hconf
    refine transport_expTwist_eq (hOr L m hL hm _ (hlevel q hql).1) activeBondsAt_reversalClosed
      hcl' hT (fun b _ => (familyAtLevel_mem_compact hB q b).2) (fun b hb => ?_)
      (fun c hc hp => ?_) b' (himg ▸ hb')
    · simp only [familyAtLevel]
      rw [dif_neg]
      exact fun h => hb ⟨h.1.1.2, h.1.2⟩
    · rw [← himg] at hc
      have hc' : (⟨q, c⟩ : Σ j : ℕ, BondAtLevel L m K j) ∈ activeBondSet K k (imageChain σ Ω) ∧
          c.IsPositivelyOriented := ⟨⟨⟨hql, hc.1⟩, hc.2⟩, hp⟩
      simp only [familyAtLevel, dif_pos hc']
      rfl
  let S : Set (ActiveFamily L m K k Ω) :=
    (O₁ ∩ twistedActiveFamily σ V₀ ⁻¹' O₂ ∩ {B | supNorm B < rB}) ∩
      selfAdjointFunctions (PositiveBondIn (activeBondSet K k Ω))
  have hSball : S ⊆ complexFamilyBall (activeBondSet K k Ω) rB ∩
      selfAdjointFunctions (PositiveBondIn (activeBondSet K k Ω)) :=
    fun B hB => ⟨⟨hB.2.1, hB.1.2⟩, hB.2⟩
  have hSN : ∀ B ∈ S, B ∈ N₁ ∧ twistedActiveFamily σ V₀ B ∈ N₂ := by
    intro B hB
    refine ⟨hDN₁ ?_, hDN₂ ?_⟩
    · rw [hD₁]
      exact ⟨hB.1.1.1, hSball hB⟩
    · rw [hD₂]
      exact ⟨hB.1.1.2, hball B (hSball hB).1, hτreal B hB.2⟩
  have hSne : S.Nonempty := by
    have h0 : (0 : ActiveFamily L m K k Ω) ∈ D₁ := h0₁
    rw [hD₁] at h0
    refine ⟨0, ⟨⟨h0.1, ?_⟩, ?_⟩, h0.2.2⟩
    · change twistedActiveFamily σ V₀ 0 ∈ O₂
      rw [twistedActiveFamily_zero]
      have h0' : (0 : ActiveFamily L m K k (imageChain σ Ω)) ∈ D₂ := h0₂
      rw [hD₂] at h0'
      exact h0'.1
    · exact h0.2.1.2
  have hSopen : ComplexMatrix2.IsRelativelyOpen
      (selfAdjointFunctions (PositiveBondIn (activeBondSet K k Ω))) S :=
    ⟨_, (hO₁.inter (hO₂.preimage (continuous_twistedActiveFamily σ V₀))).inter
      (isOpen_supNorm_lt hrB), rfl⟩
  have hreal : ∀ B ∈ S, ∃ u, IsGaugeRelating
      (bondsInside (imageChain σ Ω 0) : Set (BondAtLevel L m K 0))
      (fun x => IsEndpointOf (activeBondSet K k (imageChain σ Ω)) (x : FourTorus L m))
      (continuedMinimalField ε εBar rB K k (imageChain σ Ω)
        (datumImage σ V₀) (twistedActiveFamily σ V₀ B))
      (transportGaugeField σ (continuedMinimalField ε εBar rB K k Ω V₀ B))
      u := by
    intro B hB
    obtain ⟨hB₁, hB₂⟩ := hSN B hB
    obtain ⟨hr₁, e₁⟩ := hrep₁ B hB₁
    obtain ⟨hr₂, e₂⟩ := hrep₂ _ hB₂
    have hU : continuedMinimalField ε εBar rB K k Ω V₀ B ∈
        regularConstrainedCriticalSet (Averaging.smoothingRadius L) ε K k Ω (activeBondSet K k Ω)
          (expTwistedDatum B V₀) := by
      change minimizerContinuation ε εBar rB K k Ω V₀ B ∈ _
      rw [e₁]
      exact (Classical.epsilon_spec hr₁.2.exists).1
    have hcrit := regularConstrainedCriticalSet_congr (Ω := imageChain σ Ω) ε (hcongr B hB.2)
    have hU' : continuedMinimalField ε εBar rB K k (imageChain σ Ω)
          (datumImage σ V₀) (twistedActiveFamily σ V₀ B) ∈
        regularConstrainedCriticalSet (Averaging.smoothingRadius L) ε K k (imageChain σ Ω)
          (activeBondSet K k (imageChain σ Ω))
          (datumImage σ (expTwistedDatum B V₀)) := by
      rw [hcrit]
      change minimizerContinuation ε εBar rB K k (imageChain σ Ω) (datumImage σ V₀) _ ∈ _
      rw [e₂]
      exact (Classical.epsilon_spec hr₂.2.exists).1
    have hdatum : IsLinkDatum (activeBondSet K k Ω) (expTwistedDatum B V₀) := by
      rintro ⟨q, b⟩ hq
      have hql : q ≤ k := hq.1.1
      have h := expTwist_mem_compact (hOr L m hL hm _ (hlevel q hql).1) activeBondsAt_reversalClosed
        (hreg.1 q hql) (familyAtLevel_mem_compact hB.2 q) b ⟨hq.1.2, hq.2⟩
      exact ⟨h.1, fun _ => h.2⟩
    obtain ⟨hiff, hval⟩ := (hReg L m K hL hm hK i σ hi hσ).1 ε k Ω _ hε hDet hdatum
    obtain ⟨U₀, hU₀, hEq⟩ := hiff.1 hr₁.1
    have hoff : ∀ T ∈ regularConstrainedCriticalSet (Averaging.smoothingRadius L) ε K k
        (imageChain σ Ω) (activeBondSet K k (imageChain σ Ω))
        (datumImage σ (expTwistedDatum B V₀)),
        ∀ b ∉ (bondsInside (imageChain σ Ω 0) : Set (BondAtLevel L m K 0)), T b = 1 :=
      fun T hT => hT.1.1.1.2
    set W := continuedMinimalField ε εBar rB K k (imageChain σ Ω)
      (datumImage σ V₀) (twistedActiveFamily σ V₀ B) with hWdef
    have hinv : IsResidualInvariant ε K k (imageChain σ Ω)
        (datumImage σ (expTwistedDatum B V₀))
        (fun T => T ∈ endpointFixingOrbit (imageChain σ Ω) (activeBondSet K k (imageChain σ Ω)) W) := by
      intro T hT T' hT'
      have hTW : T ∈ endpointFixingOrbit (imageChain σ Ω) (activeBondSet K k (imageChain σ Ω)) W :=
        mem_orbit_trans (hEq ▸ hT) (mem_orbit_symm (hEq ▸ hU') (hoff _ hU₀))
      exact propext ⟨fun _ => hTW, fun _ => mem_orbit_trans hT' hTW⟩
    have hval' : (W ∈ endpointFixingOrbit (imageChain σ Ω) (activeBondSet K k (imageChain σ Ω)) W) =
        (transportGaugeField σ (continuedMinimalField ε εBar rB K k Ω V₀ B) ∈
          endpointFixingOrbit (imageChain σ Ω) (activeBondSet K k (imageChain σ Ω)) W) :=
      hval hr₁.1 Prop _ hinv W hU' _ hU
    have hmemW := Eq.mp hval' (self_mem_orbit (hoff _ hU'))
    obtain ⟨u, hu, hue⟩ := mem_orbit_symm hmemW (hoff _ hU')
    refine ⟨u, fun x => ?_, fun x hx => hu.2.2 x hx, fun c hc => ?_⟩
    · by_cases hx : x ∈ (sitesIn (imageChain σ Ω 0) : Set (SiteAtLevel L m K 0))
      · exact det_eq_one_of_mem_compact (hu.1 x hx)
      · rw [hu.2.1 x hx, Matrix.det_one]
    · have := congrFun hue c
      simpa only [extendByOne, if_pos hc, gaugeTransform] using this
  have hrev : ∀ c ∈ (bondsInside (imageChain σ Ω 0) : Set (BondAtLevel L m K 0)),
      c.opposite ∈ (bondsInside (imageChain σ Ω 0) : Set (BondAtLevel L m K 0)) :=
    fun c hc => ⟨hc.2, hc.1⟩
  have hpull : ∀ c ∈ (bondsInside (imageChain σ Ω 0) : Set (BondAtLevel L m K 0)),
      bondPreimage σ c ∈ (bondsInside (Ω 0) : Set (BondAtLevel L m K 0)) := by
    intro c hc
    rw [← himage c] at hc
    exact (hinner _).1 hc
  have hreach : ∀ c ∈ (bondsInside (imageChain σ Ω 0) : Set (BondAtLevel L m K 0)),
      ∃ a : SiteAtLevel L m K 0,
        IsEndpointOf (activeBondSet K k (imageChain σ Ω)) (a : FourTorus L m) ∧
        Relation.ReflTransGen (fun x y : SiteAtLevel L m K 0 => ∃ c ∈
          (bondsInside (imageChain σ Ω 0) : Set (BondAtLevel L m K 0)),
            c.source = x ∧ c.target = y) a c.source := by
    intro c hc
    obtain ⟨a, ha, hr⟩ := hReach L m hL hm i K k e r Ω hF hS _ (hpull c hc)
    have hlat := (hG.2.2.2.2 σ hσ _ hiK).1.1
    have ha' : σ (a : FourTorus L m) ∈ (sublattice L m (levelDepth K 0) : Set (FourTorus L m)) := by
      rw [← hlat]
      exact mem_image_of_mem σ a.2
    have key : ∀ x : SiteAtLevel L m K 0, Relation.ReflTransGen (fun x y : SiteAtLevel L m K 0 =>
        ∃ c ∈ (bondsInside (Ω 0) : Set (BondAtLevel L m K 0)), c.source = x ∧ c.target = y) a x →
        ∃ x' : SiteAtLevel L m K 0, (x' : FourTorus L m) = σ x ∧
          Relation.ReflTransGen (fun x y : SiteAtLevel L m K 0 => ∃ c ∈
            (bondsInside (imageChain σ Ω 0) : Set (BondAtLevel L m K 0)),
              c.source = x ∧ c.target = y) ⟨σ a, ha'⟩ x' := by
      intro x hx
      induction hx with
      | refl => exact ⟨⟨σ a, ha'⟩, rfl, Relation.ReflTransGen.refl⟩
      | tail _ hstep ih =>
        obtain ⟨c₀, hc₀, e₁, e₂⟩ := hstep
        subst e₁ e₂
        obtain ⟨x', ex, hr'⟩ := ih
        refine ⟨(bondImage σ c₀).target, (hends c₀).2, hr'.tail
          ⟨bondImage σ c₀, (hinner c₀).2 hc₀, Subtype.ext ?_, rfl⟩⟩
        rw [ex]
        exact (hends c₀).1
    obtain ⟨x', ex, hr'⟩ := key _ hr
    have hx' : x' = c.source := by
      apply Subtype.ext
      rw [ex, ← (hends _).1, himage c]
    exact ⟨⟨σ a, ha'⟩, (hnode a).2 ha, hx' ▸ hr'⟩
  intro B hB
  obtain ⟨u, hdet, hnd, hof, hrel⟩ := gauge_relation_on_ball
    (ι := PositiveBondIn (activeBondSet K k Ω))
    (ℬ := (bondsInside (imageChain σ Ω 0) : Set (BondAtLevel L m K 0)))
    (P := fun x => IsEndpointOf (activeBondSet K k (imageChain σ Ω)) (x : FourTorus L m))
    (W₁ := fun B => continuedMinimalField ε εBar rB K k (imageChain σ Ω)
      (datumImage σ V₀) (twistedActiveFamily σ V₀ B))
    (W₂ := fun B => transportGaugeField σ
      (continuedMinimalField ε εBar rB K k Ω V₀ B))
    (r := rB) (S := S) hId hW₁ hW₂
    (fun B hB c hc => (hcfg₂ _ (hball B hB)).1.1 c hc)
    (fun B hB c hc => (hcfg₁ B hB).1.1 _ (hpull c hc)) hrev hreach hSball hSne hSopen hreal
    B hB
  refine ⟨u, ⟨fun x _ => hdet x, fun x hx => hof x fun c hc e => hx (e ▸ hc.1), hnd⟩, ?_⟩
  funext c
  by_cases hc : c ∈ (bondsInside (imageChain σ Ω 0) : Set (BondAtLevel L m K 0))
  · simp only [extendByOne, if_pos hc, gaugeTransform]
    exact hrel c hc
  · simp only [extendByOne, if_neg hc]
    exact (hcfg₂ _ (hball B hB)).2 c hc
end ContinuationOrbits
theorem isometricContinuationsInOneComplexOrbit_holds
    (hHol : ContinuationsUnderIsometriesHolomorphic)
    (hId : RealIdentityPrinciple.Statement)
    (hReach : InnerBondsReachEndpoint)
    (hReg : IsometryCovariantRegularSetsAndAxialGauge)
    (hTw : TwistedTransportIsometryInvariance)
    (hTow : IsometriesPreserveTowersAndStepCubes)
    (hIso : LatticeIsometryGroupActionStatement)
    (hOr : BondOrientationDichotomy) :
    IsometricContinuationsInOneComplexOrbit := by apply _root_.YangMills.Construction.PeriodicLattice.ContinuationOrbits.main <;> assumption
end YangMills.Construction.PeriodicLattice
