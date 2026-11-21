import YangMills.Construction.Lattice.DomainsOfTheTwoSchemesProof
import YangMills.Construction.Lattice.MatrixValuedFormOperators
import YangMills.Construction.Matrices.CalculusOfHolomorphicMaps
import YangMills.Construction.Matrices.ExponentialChartsOfPowersOfG
import YangMills.Construction.Towers.ChainRuleAtAFiniteSideInTheLeftChart
import YangMills.Construction.Towers.ConfigurationsUnderTheLeftChart
import YangMills.Construction.Towers.CurvesAtAFiniteSideInTheLeftChart
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter
open scoped Matrix.Norms.L2Operator Topology ContDiff
noncomputable section
namespace YangMills.Construction.Tower.FiniteLevelChainRule
open Matrices Matrices.GroupLieProduct Matrices.PowerExpCharts
open LeftChartFields (leftExpMul)
open LeftChartFacts (MapDerivAlongCurves)
section Powers
variable {σ τ υ : Type} [Fintype σ] [Fintype τ] [Fintype υ]
theorem exists_clm_leftInverse_toMatrix :
    ∃ π : (τ → ComplexMatrix2) →L[ℝ] (τ → ComplexMatrix2.LieElement),
      ∀ Y : τ → ComplexMatrix2.LieElement, π (fun s => (Y s).toMatrix) = Y := by
  let M : (τ → ComplexMatrix2.LieElement) →ₗ[ℝ] (τ → ComplexMatrix2) :=
    { toFun := fun Y s => (Y s).toMatrix, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hker : LinearMap.ker M = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun Y hY => ?_
    funext s
    exact Subtype.ext (congrFun hY s)
  obtain ⟨g, hg⟩ := M.exists_leftInverse_of_injective hker
  exact ⟨LinearMap.toContinuousLinearMap g, fun Y => LinearMap.congr_fun hg Y⟩
theorem exists_local_chart_inverse (hc : PowerCharts τ) {q₀ : τ → ComplexMatrix2}
    (hq : q₀ ∈ specialUnitaryPower τ) :
    ∃ (A : Set (τ → ComplexMatrix2)) (κ : (τ → ComplexMatrix2) → τ → ComplexMatrix2.LieElement),
      IsOpen A ∧ q₀ ∈ A ∧ κ q₀ = 0 ∧
      DifferentiableOn ℝ κ A ∧ ∀ q ∈ A, q ∈ specialUnitaryPower τ → expChartI q₀ (κ q) = q := by
  obtain ⟨π, hπ⟩ := exists_clm_leftInverse_toMatrix (τ := τ)
  obtain ⟨-, hall, hε⟩ := hc q₀ hq
  have hpos : (0 : ℝ) < Real.log (19 / 10) := Real.log_pos (by norm_num)
  obtain ⟨-, ⟨A₀, hA₀, himg⟩, hmem, -, hlogo, hlogd, hsub, hinv, -⟩ :=
    hε _ hpos (Real.exp_log (by norm_num)).le
  have hkey : ∀ Y ∈ smallBall τ (Real.log (19 / 10)),
      π (logChart q₀ (expChartI q₀ Y)) = Y := fun Y hY => by
    rw [hinv Y hY]
    exact hπ Y
  have h0 : expChartI q₀ 0 = q₀ := by
    rw [(hall 0).2.1]
    funext s
    show ComplexMatrix2.matExp (Complex.I • (0 : ComplexMatrix2)) * q₀ s = q₀ s
    simp
  have h0s : (0 : τ → ComplexMatrix2.LieElement) ∈ smallBall τ (Real.log (19 / 10)) := fun s => by
    have : ((0 : τ → ComplexMatrix2.LieElement) s).toMatrix = 0 := rfl
    rw [this]
    simpa using hpos
  have hq₀A : q₀ ∈ A₀ ∩ specialUnitaryPower τ := himg ▸ hmem
  refine ⟨A₀ ∩ logDomain q₀, fun q => π (logChart q₀ q), hA₀.inter hlogo,
    ⟨hq₀A.1, hsub hmem⟩, ?_, ?_, ?_⟩
  · have := hkey 0 h0s
    rwa [h0] at this
  · exact (π.differentiable.comp_differentiableOn (hlogd.differentiableOn (by simp))).mono
      inter_subset_right
  · intro q hqA hqM
    have hq' : q ∈ expChartI q₀ '' smallBall τ (Real.log (19 / 10)) := by
      rw [himg]
      exact ⟨hqA.1, hqM⟩
    obtain ⟨Y, hY, rfl⟩ := hq'
    show expChartI q₀ (π (logChart q₀ (expChartI q₀ Y))) = _
    rw [hkey Y hY]
theorem differentiableOn_component {O : Set (σ → ComplexMatrix2)}
    {f : (σ → ComplexMatrix2) → τ → ComplexMatrix2}
    (h : EmbeddedSubmanifold.DifferentiableOnOpen (specialUnitaryPower σ) O f) (e : τ) :
    EmbeddedSubmanifold.DifferentiableOnOpen (specialUnitaryPower σ) O fun p => f p e :=
  ⟨h.1, fun c => (differentiableOn_pi.1 (h.2 c)) e⟩
theorem continuousOn_of_differentiableOn (hc : PowerCharts σ) (hr : ReadInCharts σ ComplexMatrix2)
    {O : Set (σ → ComplexMatrix2)} (hO : specialUnitaryPower.IsOpenSubset O)
    {f : (σ → ComplexMatrix2) → ComplexMatrix2}
    (hf : EmbeddedSubmanifold.DifferentiableOnOpen (specialUnitaryPower σ) O f) :
    ContinuousOn f O := by
  intro p₀ hp
  have hOM : O ⊆ specialUnitaryPower σ := by
    obtain ⟨A, -, e⟩ := hO
    rw [e]
    exact inter_subset_right
  obtain ⟨A, κ, hA, hpA, hκ0, hκd, hκ⟩ := exists_local_chart_inverse hc (hOM hp)
  obtain ⟨-, hiff, -, -⟩ := hr O f hO
  obtain ⟨N, hN, -, hd⟩ := hiff.1 hf p₀ hp
  have hd0 : ContinuousAt (f ∘ expChartI p₀) 0 := (hd.differentiableAt hN).continuousAt
  have hκc : ContinuousAt κ p₀ := (hκd.differentiableAt (hA.mem_nhds hpA)).continuousAt
  have hcomp : ContinuousAt ((f ∘ expChartI p₀) ∘ κ) p₀ :=
    ContinuousAt.comp (by rwa [hκ0]) hκc
  refine hcomp.continuousWithinAt.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [mem_nhdsWithin_of_mem_nhds (hA.mem_nhds hpA), self_mem_nhdsWithin]
      with p hpA' hpO
    simp only [Function.comp_apply]
    rw [hκ p hpA' (hOM hpO)]
  · simp only [Function.comp_apply]
    rw [hκ p₀ hpA (hOM hp)]
theorem isDifferentiableInto_comp (hcσ : PowerCharts σ) (hcτ : PowerCharts τ)
    (hrσ : ReadInCharts σ ComplexMatrix2) (hrτ : ReadInCharts τ ComplexMatrix2)
    {O₁ : Set (σ → ComplexMatrix2)} {O₂ : Set (τ → ComplexMatrix2)}
    {f₁ : (σ → ComplexMatrix2) → τ → ComplexMatrix2}
    {f₂ : (τ → ComplexMatrix2) → υ → ComplexMatrix2}
    (h₁ : specialUnitaryPower.IsDifferentiableInto O₁ f₁)
    (h₂ : specialUnitaryPower.IsDifferentiableInto O₂ f₂) :
    specialUnitaryPower.IsDifferentiableInto (O₁ ∩ f₁ ⁻¹' O₂) (f₂ ∘ f₁) := by
  have hO₁ : specialUnitaryPower.IsOpenSubset O₁ := h₁.1.1
  have hO₂ : specialUnitaryPower.IsOpenSubset O₂ := h₂.1.1
  have hcont : ContinuousOn f₁ O₁ :=
    continuousOn_pi.2 fun e => continuousOn_of_differentiableOn hcσ hrσ hO₁
      (differentiableOn_component h₁.1 e)
  have hopen : ComplexMatrix2.IsRelativelyOpen (specialUnitaryPower σ) (O₁ ∩ f₁ ⁻¹' O₂) := by
    obtain ⟨A₁, hA₁, e₁⟩ := hO₁
    obtain ⟨A₂, hA₂, e₂⟩ := hO₂
    obtain ⟨u, hu, hue⟩ := continuousOn_iff'.1 hcont A₂ hA₂
    refine ⟨u ∩ A₁, hu.inter hA₁, ?_⟩
    ext p
    constructor
    · rintro ⟨hp₁, hp₂⟩
      have hp₁' : p ∈ A₁ ∩ specialUnitaryPower σ := e₁ ▸ hp₁
      have hp₂' : f₁ p ∈ A₂ ∩ specialUnitaryPower τ := e₂ ▸ hp₂
      have : p ∈ f₁ ⁻¹' A₂ ∩ O₁ := ⟨hp₂'.1, hp₁⟩
      rw [hue] at this
      exact ⟨⟨this.1, hp₁'.1⟩, hp₁'.2⟩
    · rintro ⟨⟨hpu, hpA⟩, hpM⟩
      have hp₁ : p ∈ O₁ := by
        rw [e₁]
        exact ⟨hpA, hpM⟩
      have : p ∈ f₁ ⁻¹' A₂ ∩ O₁ := by
        rw [hue]
        exact ⟨hpu, hp₁⟩
      refine ⟨hp₁, ?_⟩
      show f₁ p ∈ O₂
      rw [e₂]
      exact ⟨this.1, h₁.2 hp₁⟩
  refine ⟨⟨hopen, fun c => ?_⟩, fun p hp => h₂.2 hp.2⟩
  intro u hu
  have hg : DifferentiableWithinAt ℝ (c.pullback f₁) (c.coords (O₁ ∩ f₁ ⁻¹' O₂)) u :=
    ((h₁.1.2 c).mono fun v hv => ⟨hv.1, hv.2.1⟩) u hu
  have hq₀O : f₁ (c.param u) ∈ O₂ := hu.2.2
  have hq₀ : f₁ (c.param u) ∈ specialUnitaryPower τ := h₁.2 hu.2.1
  obtain ⟨A, κ, hA, hqA, hκ0, hκd, hκ⟩ := exists_local_chart_inverse hcτ hq₀
  refine differentiableWithinAt_pi.2 fun e => ?_
  obtain ⟨-, hiff, -, -⟩ := hrτ O₂ (fun q => f₂ q e) hO₂
  obtain ⟨N, hN, -, hd⟩ := hiff.1 (differentiableOn_component h₂.1 e) _ hq₀O
  have hgA : ∀ᶠ v in 𝓝[c.coords (O₁ ∩ f₁ ⁻¹' O₂)] u, c.pullback f₁ v ∈ A :=
    hg.continuousWithinAt (hA.mem_nhds hqA)
  have hh : DifferentiableWithinAt ℝ (κ ∘ c.pullback f₁) (c.coords (O₁ ∩ f₁ ⁻¹' O₂)) u :=
    (hκd.differentiableAt (hA.mem_nhds hqA)).comp_differentiableWithinAt u hg
  have hh0 : (κ ∘ c.pullback f₁) u = 0 := hκ0
  have hcomp := DifferentiableAt.comp_differentiableWithinAt (g := (fun q => f₂ q e) ∘
    expChartI (f₁ (c.param u))) u (by rw [hh0]; exact hd.differentiableAt hN) hh
  refine hcomp.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [hgA, self_mem_nhdsWithin] with v hvA hvS
    have := hκ _ hvA (h₁.2 hvS.2.1)
    simp only [Function.comp_apply]
    rw [this]
    rfl
  · have := hκ _ hqA hq₀
    simp only [Function.comp_apply]
    show _ = f₂ (expChartI (f₁ (c.param u)) (κ (f₁ (c.param u)))) e
    rw [this]
    rfl
theorem isDifferentiableInto_congr {O : Set (σ → ComplexMatrix2)}
    {f g : (σ → ComplexMatrix2) → τ → ComplexMatrix2}
    (h : specialUnitaryPower.IsDifferentiableInto O f) (he : ∀ p ∈ O, g p = f p) :
    specialUnitaryPower.IsDifferentiableInto O g :=
  ⟨⟨h.1.1, fun c => (h.1.2 c).congr fun _ hu => he _ hu.2⟩, fun p hp => he p hp ▸ h.2 hp⟩
end Powers
section Holomorphic
variable {ι κ : Type} [Fintype ι] [Fintype κ]
theorem isHolomorphicIn_congr {N N' : ℕ} {O : Set (Coordinates.ComplexCoordinates N)}
    {f g : Coordinates.ComplexCoordinates N → Coordinates.ComplexCoordinates N'}
    (h : Coordinates.ComplexCoordinates.IsHolomorphicIn O f)
    (he : ∀ a ∈ O, g a = f a) : Coordinates.ComplexCoordinates.IsHolomorphicIn O g := by apply _root_.YangMills.SharedProofs.p63802 <;> assumption
theorem isHolomorphicOnTraceless_congr {σ E : Type} [Fintype σ] {l : ℕ}
    {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
    {e : E ≃ Coordinates.ComplexCoordinates l} {O : Set (σ → ComplexMatrix2)}
    {f g : (σ → ComplexMatrix2) → E}
    (h : IsHolomorphicOnTraceless b e O f) (he : ∀ A ∈ O, g A = f A) :
    IsHolomorphicOnTraceless b e O g :=
  ⟨h.1, fun ν => isHolomorphicIn_congr (h.2 ν) fun a ha => by
    simp only [Function.comp_apply]
    rw [he _ ha]⟩
theorem isHolomorphicToUnimodular_congr {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
    {W : Set (ι ⊕ κ → ComplexMatrix2)}
    {Φ Φ' : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2} (h : IsHolomorphicToUnimodular b W Φ)
    (he : ∀ p ∈ W, Φ' p = Φ p) : IsHolomorphicToUnimodular b W Φ' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, fun p hp => he p hp ▸ h2 hp, h3.congr he, fun p hp => ?_⟩
  obtain ⟨O, h0, hO, hh⟩ := h4 p hp
  refine ⟨O, h0, fun A hA => ?_, isHolomorphicOnTraceless_congr hh fun A hA => ?_⟩
  · rw [he _ (hO A hA).1, he p hp]
    exact hO A hA
  · show ComplexMatrix2.logSeries (Φ' _ * (Φ' p)⁻¹) = ComplexMatrix2.logSeries (Φ _ * (Φ p)⁻¹)
    rw [he _ (hO A hA).1, he p hp]
theorem isHolomorphicToProduct_congr {ι' : Type}
    {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
    {W : Set (ι ⊕ κ → ComplexMatrix2)} {Ψ Ψ' : (ι ⊕ κ → ComplexMatrix2) → ι' ⊕ Empty → ComplexMatrix2}
    (h : IsHolomorphicToProduct b W Ψ) (he : ∀ p ∈ W, Ψ' p = Ψ p) :
    IsHolomorphicToProduct b W Ψ' :=
  ⟨h.1, fun i => isHolomorphicToUnimodular_congr (h.2.1 i) fun p hp => congrFun (he p hp) _,
    fun k => k.elim⟩
end Holomorphic
section Lattice
variable {L n k j j' j'' : ℕ}
abbrev ExactlyOneOriented (L n k j : ℕ) : Prop :=
  ∀ b : Edge L n k j, (b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented) ∧
    (¬ b.IsPositivelyOriented → b.opposite.IsPositivelyOriented)
theorem exactlyOneOriented (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hj : j ≤ k) : ExactlyOneOriented L n k j := fun b => by
  rcases PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite (by have := hL.2; omega)
    (by show -(n : ℤ) < (k : ℤ) - (j : ℤ); omega) b with ⟨h, h'⟩ | ⟨h', h⟩
  · exact ⟨fun _ => h', fun h₂ => absurd h h₂⟩
  · exact ⟨fun h₂ => absurd h₂ h, fun _ => h'⟩
structure IsMatrixGroup (𝒢 : Set ComplexMatrix2) : Prop where
  isUnit_det : ∀ g ∈ 𝒢, IsUnit g.det
  inv_mem : ∀ g ∈ 𝒢, g⁻¹ ∈ 𝒢
theorem isMatrixGroup_compact : IsMatrixGroup PeriodicLattice.compactGaugeGroup where
  isUnit_det g hg := by
    rw [(Matrix.mem_specialUnitaryGroup_iff.1 hg).2]
    exact isUnit_one
  inv_mem M hM := by
    have hA : M⁻¹ = (((⟨M, hM⟩ : ComplexMatrix2.specialUnitary)⁻¹ :
        ComplexMatrix2.specialUnitary) : ComplexMatrix2) :=
      Matrix.inv_eq_right_inv
        (congrArg Subtype.val (mul_inv_cancel (⟨M, hM⟩ : ComplexMatrix2.specialUnitary)))
    rw [hA]
    exact Subtype.prop _
theorem isMatrixGroup_complex : IsMatrixGroup PeriodicLattice.complexGaugeGroup where
  isUnit_det g hg := by
    have hg' : g.det = 1 := hg
    rw [hg']
    exact isUnit_one
  inv_mem M hM := by
    have hM' : M.det = 1 := hM
    change (M⁻¹).det = 1
    rw [Matrix.det_nonsing_inv, hM']
    simp
theorem fieldOfPositiveValues_restrict (ho : ExactlyOneOriented L n k j) {𝒢 : Set ComplexMatrix2}
    (hG : IsMatrixGroup 𝒢) {V : Edge L n k j → ComplexMatrix2} (hV : V ∈ fieldsIn L n k j 𝒢) :
    fieldOfPositiveValues (restrictToPositiveEdges V) = V := by
  funext b
  unfold fieldOfPositiveValues
  by_cases hb : b.IsPositivelyOriented
  · rw [dif_pos hb]
    rfl
  · have hr := (ho b).2 hb
    rw [dif_neg hb, dif_pos hr]
    have h : V b.opposite = (V b)⁻¹ := hV.2 b trivial
    show (V b.opposite)⁻¹ = V b
    rw [h, Matrix.nonsing_inv_nonsing_inv _ (hG.isUnit_det _ (hV.1 b trivial))]
theorem eq_of_restrict_eq (ho : ExactlyOneOriented L n k j) {𝒢 : Set ComplexMatrix2}
    (hG : IsMatrixGroup 𝒢) {U V : Edge L n k j → ComplexMatrix2} (hU : U ∈ fieldsIn L n k j 𝒢)
    (hV : V ∈ fieldsIn L n k j 𝒢)
    (h : restrictToPositiveEdges U = restrictToPositiveEdges V) : U = V := by
  have := congrArg fieldOfPositiveValues h
  rwa [fieldOfPositiveValues_restrict ho hG hU, fieldOfPositiveValues_restrict ho hG hV] at this
theorem hasDerivAt_leftExpMul (X V : ComplexMatrix2) (t : ℝ) :
    HasDerivAt (fun s : ℝ => leftExpMul ((s : ℂ) • X) V)
      (ComplexMatrix2.matExp ((t : ℂ) • (Complex.I • X)) * (Complex.I • X) * V) t := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℂ) (Complex.I • X) (t : ℂ)
  have h2 := h.mul_const V
  have h3 : HasDerivAt (fun s : ℂ => leftExpMul (s • X) V)
      (ComplexMatrix2.matExp ((t : ℂ) • (Complex.I • X)) * (Complex.I • X) * V)
      (Complex.ofRealCLM t) := by
    refine HasDerivAt.congr_of_eventuallyEq h2 (Eventually.of_forall fun s => ?_)
    simp only [leftExpMul, ComplexMatrix2.matExp, smul_comm Complex.I s X]
  have h4 := HasDerivAt.scomp t h3 Complex.ofRealCLM.hasDerivAt
  simpa [Function.comp_def] using h4
def leftExpCurve (U B : Edge L n k j → ComplexMatrix2) (t : ℝ) : Edge L n k j → ComplexMatrix2 :=
  PeriodicLattice.expTwist ((t : ℂ) • B) U
theorem leftExpCurve_pos (U B : Edge L n k j → ComplexMatrix2) (t : ℝ) {b : Edge L n k j}
    (hb : b.IsPositivelyOriented) : leftExpCurve U B t b = leftExpMul ((t : ℂ) • B b) (U b) :=
  if_pos hb
theorem leftExpCurve_neg (U B : Edge L n k j → ComplexMatrix2) (t : ℝ) {b : Edge L n k j}
    (hb : ¬ b.IsPositivelyOriented) :
    leftExpCurve U B t b = (leftExpMul ((t : ℂ) • B b.opposite) (U b.opposite))⁻¹ :=
  if_neg hb
theorem leftExpCurve_isDifferentiable (ho : ExactlyOneOriented L n k j) {𝒢 : Set ComplexMatrix2}
    (hG : IsMatrixGroup 𝒢) {U B : Edge L n k j → ComplexMatrix2}
    (hval : ∀ b : Edge L n k j, b.IsPositivelyOriented → ∀ t : ℝ,
      leftExpMul ((t : ℂ) • B b) (U b) ∈ 𝒢) :
    IsDifferentiableFieldCurve 𝒢 univ (leftExpCurve U B) := by
  refine ⟨⟨isOpen_univ, ordConnected_univ, mem_univ _⟩, fun t _ => ⟨fun b _ => ?_, fun b _ => ?_⟩,
    fun b hb => ?_⟩
  · by_cases hb : b.IsPositivelyOriented
    · rw [leftExpCurve_pos U B t hb]
      exact hval b hb t
    · rw [leftExpCurve_neg U B t hb]
      exact hG.inv_mem _ (hval _ ((ho b).2 hb) t)
  · by_cases hb : b.IsPositivelyOriented
    · rw [leftExpCurve_neg U B t ((ho b).1 hb), leftExpCurve_pos U B t hb]
      rfl
    · rw [leftExpCurve_neg U B t hb, leftExpCurve_pos U B t ((ho b).2 hb),
        Matrix.nonsing_inv_nonsing_inv _ (hG.isUnit_det _ (hval _ ((ho b).2 hb) t))]
  · have he : (fun t => leftExpCurve U B t b) = fun t : ℝ => leftExpMul ((t : ℂ) • B b) (U b) :=
      funext fun t => leftExpCurve_pos U B t hb
    rw [he]
    exact fun t _ => (hasDerivAt_leftExpMul (B b) (U b) t).differentiableAt.differentiableWithinAt
theorem leftExpCurve_zero {𝒢 : Set ComplexMatrix2} (hG : IsMatrixGroup 𝒢)
    {U : Edge L n k j → ComplexMatrix2} (hU : U ∈ fieldsIn L n k j 𝒢)
    (B : Edge L n k j → ComplexMatrix2) :
    leftExpCurve U B 0 = U := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · rw [leftExpCurve_pos U B 0 hb]
    simp [leftExpMul]
  · rw [leftExpCurve_neg U B 0 hb]
    have h : U b.opposite = (U b)⁻¹ := hU.2 b trivial
    simp only [leftExpMul, Complex.ofReal_zero, zero_smul, smul_zero, ComplexMatrix2.matExp,
      NormedSpace.exp_zero, one_mul]
    rw [h, Matrix.nonsing_inv_nonsing_inv _ (hG.isUnit_det _ (hU.1 b trivial))]
theorem leftExpCurve_tangent (ho : ExactlyOneOriented L n k j) {𝒢 : Set ComplexMatrix2}
    (hG : IsMatrixGroup 𝒢) {U B : Edge L n k j → ComplexMatrix2} (hU : U ∈ fieldsIn L n k j 𝒢)
    (hrev : ∀ b : Edge L n k j, B b.opposite = -B b) : curveTangent (leftExpCurve U B) = B := by
  have key : ∀ b : Edge L n k j, b.IsPositivelyOriented →
      Complex.I⁻¹ • (deriv (fun t => leftExpCurve U B t b) 0 * (leftExpCurve U B 0 b)⁻¹) = B b := by
    intro b hb
    have he : (fun t => leftExpCurve U B t b) = fun t : ℝ => leftExpMul ((t : ℂ) • B b) (U b) :=
      funext fun t => leftExpCurve_pos U B t hb
    rw [he, (hasDerivAt_leftExpMul (B b) (U b) 0).deriv, leftExpCurve_zero hG hU B]
    simp only [Complex.ofReal_zero, zero_smul, ComplexMatrix2.matExp, NormedSpace.exp_zero, one_mul]
    rw [Matrix.mul_nonsing_inv_cancel_right _ _ (hG.isUnit_det _ (hU.1 b trivial))]
    exact inv_smul_smul₀ Complex.I_ne_zero _
  funext b
  unfold curveTangent extendOddly
  by_cases hb : b.IsPositivelyOriented
  · rw [if_pos hb]
    exact key b hb
  · rw [if_neg hb]
    beta_reduce
    rw [key _ ((ho b).2 hb), hrev, neg_neg]
theorem exists_curve_mem_of_open (ho : ExactlyOneOriented L n k j) {𝒢 : Set ComplexMatrix2}
    (hG : IsMatrixGroup 𝒢)
    {𝔇 : Set (Edge L n k j → ComplexMatrix2)} (h𝔇 : IsOpenFieldSet 𝒢 𝔇)
    {γ : ℝ → Edge L n k j → ComplexMatrix2}
    (hγ : IsDifferentiableFieldCurve 𝒢 univ γ) (h0 : γ 0 ∈ 𝔇) :
    ∃ ε > 0, ∀ t : ℝ, |t| < ε → γ t ∈ 𝔇 := by
  obtain ⟨hsub, A, hA, hAe⟩ := h𝔇
  have hc : Continuous fun t => restrictToPositiveEdges (γ t) :=
    continuous_pi fun b => (differentiableOn_univ.1 (hγ.2.2 b.1 b.2)).continuous
  have hmem : restrictToPositiveEdges (γ 0) ∈ A := by
    have h : restrictToPositiveEdges (γ 0) ∈ restrictToPositiveEdges '' 𝔇 := mem_image_of_mem _ h0
    rw [hAe] at h
    exact h.1
  obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.1
    (hc.continuousAt.eventually_mem (hA.mem_nhds hmem))
  refine ⟨ε, hε, fun t ht => ?_⟩
  have hconf : γ t ∈ fieldsIn L n k j 𝒢 := hγ.2.1 (mem_univ t)
  have hin : restrictToPositiveEdges (γ t) ∈ restrictToPositiveEdges '' 𝔇 := by
    rw [hAe]
    exact ⟨h (by simpa [Real.dist_eq] using ht), fun b => hconf.1 b trivial⟩
  obtain ⟨V, hV, hVe⟩ := hin
  rwa [← eq_of_restrict_eq ho hG (hsub hV) hconf hVe]
theorem isDifferentiableFieldCurve_shift {𝒢 : Set ComplexMatrix2}
    {γ : ℝ → Edge L n k j → ComplexMatrix2}
    (hγ : IsDifferentiableFieldCurve 𝒢 univ γ) (t₀ : ℝ) :
    IsDifferentiableFieldCurve 𝒢 univ fun s => γ (t₀ + s) :=
  ⟨hγ.1, fun _ _ => hγ.2.1 (mem_univ _), fun b hb =>
    ((differentiableOn_univ.1 (hγ.2.2 b hb)).comp
      (differentiable_const t₀ |>.add differentiable_id)).differentiableOn⟩
theorem derivs_comp_of_curve {𝒢 : Set ComplexMatrix2} {𝔇₁ : Set (Edge L n k j → ComplexMatrix2)}
    {𝔇₂ : Set (Edge L n k j' → ComplexMatrix2)}
    {m₁ : (Edge L n k j → ComplexMatrix2) → Edge L n k j' → ComplexMatrix2}
    {m₂ : (Edge L n k j' → ComplexMatrix2) → Edge L n k j'' → ComplexMatrix2}
    {d₁ : (Edge L n k j → ComplexMatrix2) → (Edge L n k j → ComplexMatrix2) →
      Edge L n k j' → ComplexMatrix2}
    {d₂ : (Edge L n k j' → ComplexMatrix2) → (Edge L n k j' → ComplexMatrix2) →
      Edge L n k j'' → ComplexMatrix2}
    {d : (Edge L n k j → ComplexMatrix2) → Edge L n k j'' → ComplexMatrix2}
    {U : Edge L n k j → ComplexMatrix2}
    (c₁ : ∀ U ∈ 𝔇₁, MapDerivAlongCurves 𝒢 m₁ U (d₁ U))
    (c₂ : ∀ V ∈ 𝔇₂, MapDerivAlongCurves 𝒢 m₂ V (d₂ V))
    (c : MapDerivAlongCurves 𝒢 (m₂ ∘ m₁) U d)
    (hm : MapsTo m₁ 𝔇₁ (fieldsIn L n k j' 𝒢)) (hU₁ : U ∈ 𝔇₁) (hU₂ : m₁ U ∈ 𝔇₂)
    {γ : ℝ → Edge L n k j → ComplexMatrix2} (hγ : IsDifferentiableFieldCurve 𝒢 univ γ)
    (h0 : γ 0 = U) {ε : ℝ}
    (hε : 0 < ε) (hin : ∀ t : ℝ, |t| < ε → γ t ∈ 𝔇₁) :
    d (curveTangent γ) = d₂ (m₁ U) (d₁ U (curveTangent γ)) := by
  have hball : ∀ t ∈ Metric.ball (0 : ℝ) ε, γ t ∈ 𝔇₁ := fun t ht =>
    hin t (by simpa [Real.dist_eq] using ht)
  have hcurve : IsDifferentiableFieldCurve 𝒢 (Metric.ball (0 : ℝ) ε) fun t => m₁ (γ t) := by
    refine ⟨⟨Metric.isOpen_ball, (convex_ball (0 : ℝ) ε).ordConnected, Metric.mem_ball_self hε⟩,
      fun t ht => hm (hball t ht), fun b hb t₀ ht₀ => ?_⟩
    have hd := ((c₁ _ (hball t₀ ht₀)) univ _ (isDifferentiableFieldCurve_shift hγ t₀)
      (by simp)).1 b hb
    have hs : DifferentiableAt ℝ (fun t : ℝ => t - t₀) t₀ :=
      differentiableAt_id.sub_const t₀
    have hcomp : DifferentiableAt ℝ
        ((fun s => m₁ (γ (t₀ + s)) b) ∘ fun t : ℝ => t - t₀) t₀ :=
      DifferentiableAt.comp t₀ (by simpa using hd) hs
    have he : ((fun s => m₁ (γ (t₀ + s)) b) ∘ fun t : ℝ => t - t₀) = fun t => m₁ (γ t) b := by
      funext t
      simp
    rw [he] at hcomp
    exact hcomp.differentiableWithinAt
  have e₁ := ((c₁ U hU₁) univ γ hγ h0).2
  have e₂ := ((c₂ _ hU₂) _ (fun t => m₁ (γ t)) hcurve (by simp [h0])).2
  have e := (c univ γ hγ h0).2
  rw [← e, ← e₁, ← e₂]
  rfl
theorem restrict_image_compositeDomain (ho : ExactlyOneOriented L n k j)
    (ho' : ExactlyOneOriented L n k j') {𝒢 : Set ComplexMatrix2}
    (hG : IsMatrixGroup 𝒢) {𝔇₁ : Set (Edge L n k j → ComplexMatrix2)}
    {𝔇₂ : Set (Edge L n k j' → ComplexMatrix2)}
    {m₁ : (Edge L n k j → ComplexMatrix2) → Edge L n k j' → ComplexMatrix2}
    (h₁ : 𝔇₁ ⊆ fieldsIn L n k j 𝒢) (h₂ : 𝔇₂ ⊆ fieldsIn L n k j' 𝒢)
    (hm : MapsTo m₁ 𝔇₁ (fieldsIn L n k j' 𝒢)) :
    restrictToPositiveEdges '' compositeDomain 𝔇₁ 𝔇₂ m₁ =
      restrictToPositiveEdges '' 𝔇₁ ∩
        (fun w => restrictToPositiveEdges (m₁ (fieldOfPositiveValues w))) ⁻¹'
          (restrictToPositiveEdges '' 𝔇₂) := by
  ext w
  constructor
  · rintro ⟨U, hU, rfl⟩
    refine ⟨⟨U, hU.1, rfl⟩, ?_⟩
    show restrictToPositiveEdges (m₁ (fieldOfPositiveValues (restrictToPositiveEdges U))) ∈
      restrictToPositiveEdges '' 𝔇₂
    rw [fieldOfPositiveValues_restrict ho hG (h₁ hU.1)]
    exact ⟨_, hU.2, rfl⟩
  · rintro ⟨⟨U, hU, rfl⟩, hw⟩
    have hw' : restrictToPositiveEdges (m₁ (fieldOfPositiveValues (restrictToPositiveEdges U))) ∈
        restrictToPositiveEdges '' 𝔇₂ := hw
    rw [fieldOfPositiveValues_restrict ho hG (h₁ hU)] at hw'
    obtain ⟨V, hV, hVe⟩ := hw'
    have hVm : V = m₁ U := eq_of_restrict_eq ho' hG (h₂ hV) (hm hU) hVe
    subst hVm
    exact ⟨U, ⟨hU, hV⟩, rfl⟩
theorem isDifferentiableFieldMap_comp (hch : ExpChartsStatement)
    (ho : ExactlyOneOriented L n k j) (ho' : ExactlyOneOriented L n k j')
    [Nonempty (PositiveEdge L n k j)] [Nonempty (PositiveEdge L n k j')]
    {𝔇₁ : Set (Edge L n k j → ComplexMatrix2)} {𝔇₂ : Set (Edge L n k j' → ComplexMatrix2)}
    {m₁ : (Edge L n k j → ComplexMatrix2) → Edge L n k j' → ComplexMatrix2}
    {m₂ : (Edge L n k j' → ComplexMatrix2) → Edge L n k j'' → ComplexMatrix2}
    (h₁ : IsDifferentiableFieldMap 𝔇₁ m₁) (h₂ : IsDifferentiableFieldMap 𝔇₂ m₂) :
    IsDifferentiableFieldMap (compositeDomain 𝔇₁ 𝔇₂ m₁) (m₂ ∘ m₁) := by
  obtain ⟨⟨hs₁, -⟩, hm₁, f1, f1', hd₁⟩ := h₁
  obtain ⟨⟨hs₂, -⟩, hm₂, f2, f2', hd₂⟩ := h₂
  obtain rfl : f2 = f1' := Subsingleton.elim _ _
  have hcomp := isDifferentiableInto_comp (hch (PositiveEdge L n k j) (PositiveEdge L n k j)).1
    (hch (PositiveEdge L n k j') (PositiveEdge L n k j')).1
    (hch (PositiveEdge L n k j) (PositiveEdge L n k j)).2.2.2.1
    (hch (PositiveEdge L n k j') (PositiveEdge L n k j')).2.2.2.1 hd₁ hd₂
  have he := restrict_image_compositeDomain (𝔇₂ := 𝔇₂) ho ho' isMatrixGroup_compact hs₁ hs₂ hm₁
  refine ⟨⟨fun U hU => hs₁ hU.1, ?_⟩, fun U hU => hm₂ hU.2, f1, f2', ?_⟩
  · rw [he]
    exact hcomp.1.1
  · rw [he]
    refine isDifferentiableInto_congr hcomp fun w hw => ?_
    obtain ⟨⟨U, hU, rfl⟩, -⟩ := hw
    simp only [Function.comp_apply]
    rw [fieldOfPositiveValues_restrict ho' isMatrixGroup_compact (V := m₁ _)]
    rw [fieldOfPositiveValues_restrict ho isMatrixGroup_compact (hs₁ hU)]
    exact hm₁ hU
theorem asGroupFactors_injective {σ : Type} : Function.Injective (asGroupFactors (σ := σ)) :=
  fun _ _ h => funext fun b => congrFun h (.inl b)
theorem isHolomorphicFieldMap_comp (hco : HolomorphicCalculus.Properties)
    (ho : ExactlyOneOriented L n k j) (ho' : ExactlyOneOriented L n k j')
    {β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
    {𝔇₁ : Set (Edge L n k j → ComplexMatrix2)} {𝔇₂ : Set (Edge L n k j' → ComplexMatrix2)}
    {m₁ : (Edge L n k j → ComplexMatrix2) → Edge L n k j' → ComplexMatrix2}
    {m₂ : (Edge L n k j' → ComplexMatrix2) → Edge L n k j'' → ComplexMatrix2}
    (h₁ : IsHolomorphicFieldMap β 𝔇₁ m₁) (h₂ : IsHolomorphicFieldMap β 𝔇₂ m₂) :
    IsHolomorphicFieldMap β (compositeDomain 𝔇₁ 𝔇₂ m₁) (m₂ ∘ m₁) := by
  obtain ⟨⟨hs₁, -⟩, hm₁, f1, f1', hd₁⟩ := h₁
  obtain ⟨⟨hs₂, -⟩, hm₂, f2, f2', hd₂⟩ := h₂
  obtain rfl : f2 = f1' := Subsingleton.elim _ _
  obtain ⟨-, ⟨A, hA, hAe⟩, hhol⟩ := hco.2.1 (PositiveEdge L n k j) Empty (PositiveEdge L n k j')
    Empty (PositiveEdge L n k j'') Empty β _ _ hd₁.1 hd₁ _ _ hd₂
  have hc : ∀ {U : Edge L n k j → ComplexMatrix2}, U ∈ 𝔇₁ →
      fieldOfPositiveValues (fun b => asGroupFactors (restrictToPositiveEdges U) (.inl b)) = U :=
    fun hU => fieldOfPositiveValues_restrict ho isMatrixGroup_complex (hs₁ hU)
  have hset : asGroupFactors '' (restrictToPositiveEdges '' compositeDomain 𝔇₁ 𝔇₂ m₁) =
      (asGroupFactors '' (restrictToPositiveEdges '' 𝔇₁)) ∩
        (fun p => asGroupFactors (restrictToPositiveEdges
          (m₁ (fieldOfPositiveValues fun b => p (.inl b))))) ⁻¹'
          (asGroupFactors '' (restrictToPositiveEdges '' 𝔇₂)) := by
    ext p
    constructor
    · rintro ⟨_, ⟨U, hU, rfl⟩, rfl⟩
      refine ⟨⟨_, ⟨U, hU.1, rfl⟩, rfl⟩, ?_⟩
      show asGroupFactors (restrictToPositiveEdges (m₁ (fieldOfPositiveValues fun b =>
        asGroupFactors (restrictToPositiveEdges U) (.inl b)))) ∈
          asGroupFactors '' (restrictToPositiveEdges '' 𝔇₂)
      rw [hc hU.1]
      exact ⟨_, ⟨_, hU.2, rfl⟩, rfl⟩
    · rintro ⟨⟨_, ⟨U, hU, rfl⟩, rfl⟩, hp⟩
      have hp' : asGroupFactors (restrictToPositiveEdges (m₁ (fieldOfPositiveValues fun b =>
        asGroupFactors (restrictToPositiveEdges U) (.inl b)))) ∈
          asGroupFactors '' (restrictToPositiveEdges '' 𝔇₂) := hp
      rw [hc hU] at hp'
      obtain ⟨_, ⟨V, hV, rfl⟩, hVe⟩ := hp'
      have hVm : V = m₁ U := eq_of_restrict_eq ho' isMatrixGroup_complex (hs₂ hV) (hm₁ hU)
        (asGroupFactors_injective hVe)
      subst hVm
      exact ⟨_, ⟨U, ⟨hU, hV⟩, rfl⟩, rfl⟩
  refine ⟨⟨fun U hU => hs₁ hU.1, ?_⟩, fun U hU => hm₂ hU.2, f1, f2', ?_⟩
  · refine ⟨asGroupFactors ⁻¹' A, hA.preimage ?_, ?_⟩
    · refine continuous_pi fun i => ?_
      rcases i with b | e
      · exact continuous_apply b
      · exact e.elim
    · ext w
      constructor
      · intro hw
        have hin : asGroupFactors w ∈ A ∩ GroupLieProduct (PositiveEdge L n k j) Empty := by
          rw [← hAe, ← hset]
          exact mem_image_of_mem _ hw
        obtain ⟨U, hU, rfl⟩ := hw
        exact ⟨hin.1, fun b => (hs₁ hU.1).1 b trivial⟩
      · rintro ⟨hwA, hwG⟩
        have hG : asGroupFactors w ∈ GroupLieProduct (PositiveEdge L n k j) Empty := by
          intro i
          rcases i with b | e
          · exact hwG b
          · exact e.elim
        have hin : asGroupFactors w ∈
            asGroupFactors '' (restrictToPositiveEdges '' compositeDomain 𝔇₁ 𝔇₂ m₁) := by
          rw [hset, hAe]
          exact ⟨hwA, hG⟩
        obtain ⟨w', hw', hwe⟩ := hin
        rwa [← asGroupFactors_injective hwe]
  · rw [hset]
    refine isHolomorphicToProduct_congr hhol fun p hp => ?_
    obtain ⟨⟨_, ⟨U, hU, rfl⟩, rfl⟩, -⟩ := hp
    simp only [Function.comp_apply]
    rw [hc hU]
    have hc' : fieldOfPositiveValues
        (fun b => asGroupFactors (restrictToPositiveEdges (m₁ U)) (.inl b)) = m₁ U :=
      fieldOfPositiveValues_restrict ho' isMatrixGroup_complex (hm₁ hU)
    rw [hc']
end Lattice
theorem statement_holds
    (curves : FiniteLevelCurveDifferentials.Statement)
    (left : LeftChartFields.Claim)
    (charts : ExpChartsStatement)
    (holo : HolomorphicCalculus.Properties) :
    Statement := by
  intro L k j j' j'' hL hj hj' hj'' n hn
  have ho := exactlyOneOriented (L := L) (n := n) (k := k) (j := j) hL hn hj
  have ho' := exactlyOneOriented (L := L) (n := n) (k := k) (j := j') hL hn hj'
  have hne : ∀ i : ℕ, Nonempty (PositiveEdge L n k i) := fun i =>
    ⟨⟨PeriodicLattice.Bond.forwardFrom 0 0, ⟨0, by simp [PeriodicLattice.Bond.forwardFrom]⟩⟩⟩
  have := hne j
  have := hne j'
  have hlv := ((left.2.2 L k j hL hj).1 n hn).1.1
  refine ⟨fun 𝔇₁ 𝔇₂ m₁ m₂ h₁ h₂ => ?_, fun β 𝔇₁ 𝔇₂ m₁ m₂ h₁ h₂ => ?_⟩
  · have h₁₂ := isDifferentiableFieldMap_comp charts ho ho' h₁ h₂
    refine ⟨h₁₂, fun U hU B hB => ?_⟩
    have hUc : U ∈ fieldsIn L n k j PeriodicLattice.compactGaugeGroup := h₁.1.1 hU.1
    have hγ := leftExpCurve_isDifferentiable (U := U) (B := B) ho isMatrixGroup_compact
      fun b hb t => (hlv.1 U hUc B hB ⟨b, hb⟩).1 t
    have h0 := leftExpCurve_zero isMatrixGroup_compact hUc B
    obtain ⟨ε, hε, hin⟩ :=
      exists_curve_mem_of_open ho isMatrixGroup_compact h₁.1 hγ (by rw [h0]; exact hU.1)
    have key := derivs_comp_of_curve
      ((curves L k j j' hL hj hj' n hn).1 𝔇₁ m₁ h₁)
      ((curves L k j' j'' hL hj' hj'' n hn).1 𝔇₂ m₂ h₂)
      ((curves L k j j'' hL hj hj'' n hn).1 _ _ h₁₂ U hU)
      h₁.2.1 hU.1 hU.2 hγ h0 hε hin
    rwa [leftExpCurve_tangent ho isMatrixGroup_compact hUc hB.2] at key
  · have h₁₂ := isHolomorphicFieldMap_comp holo ho ho' h₁ h₂
    refine ⟨h₁₂, fun U hU B hB => ?_⟩
    have hUc : U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup := h₁.1.1 hU.1
    have hγ := leftExpCurve_isDifferentiable (U := U) (B := B) ho isMatrixGroup_complex
      fun b hb t => (hlv.2 U hUc B hB ⟨b, hb⟩).1 t
    have h0 := leftExpCurve_zero isMatrixGroup_complex hUc B
    obtain ⟨ε, hε, hin⟩ :=
      exists_curve_mem_of_open ho isMatrixGroup_complex h₁.1 hγ (by rw [h0]; exact hU.1)
    have key := derivs_comp_of_curve
      ((curves L k j j' hL hj hj' n hn).2.2.1 β 𝔇₁ m₁ h₁)
      ((curves L k j' j'' hL hj' hj'' n hn).2.2.1 β 𝔇₂ m₂ h₂)
      ((curves L k j j'' hL hj hj'' n hn).2.2.1 β _ _ h₁₂ U hU)
      h₁.2.1 hU.1 hU.2 hγ h0 hε hin
    rwa [leftExpCurve_tangent ho isMatrixGroup_complex hUc hB.2] at key
end YangMills.Construction.Tower.FiniteLevelChainRule
end
