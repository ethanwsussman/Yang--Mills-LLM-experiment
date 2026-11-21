import YangMills.Construction.Towers.ChainRuleAtAFiniteSideInTheLeftChart
import YangMills.Construction.Towers.FibresOfARealAnalyticSubmersion
import YangMills.Construction.Towers.RealAnalyticMapsAlongPathsProof
import YangMills.Construction.Towers.TwoStagesOfAConstraintOnATower
import YangMills.Construction.Towers.TwoStagesOfAConstraintProof
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.TwoStageOnLevels
open YangMills.Construction.Matrices YangMills.Construction.Matrices.EmbeddedSubmanifold YangMills.Construction.Manifolds
section Submanifolds
variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
private theorem hasDerivAt_comp_curve (hS : Manifolds.LocalSmoothCalculus)
    {M O : Set E} (hM : IsChartedSubset M) {f : E → E'} (hf : IsSmoothOnOpen M O f) {γ : ℝ → E}
    {p : E} (hγ : DifferentiableAt ℝ γ 0) (hev : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ M) (h0 : γ 0 = p)
    (hp : p ∈ O) (hpM : p ∈ M) :
    ∃ h : deriv γ 0 ∈ tangentSpace M p,
      HasDerivAt (fun t => f (γ t)) (tangentDifferential M f p ⟨deriv γ 0, h⟩) 0 := by
  obtain ⟨h1, h2, h3, h4, -, h6, -⟩ := hS
  obtain ⟨c, u, hu, rfl⟩ := hM p hpM
  have hpar := h6 E M c
  obtain ⟨Ω, ρ, hΩ, hpΩ, hρ, hinv⟩ := h1 E (Fin c.dim → ℝ) M c.source c.param u hpar hu
  have hρu : ρ (c.param u) = u := by
    obtain ⟨ha, hb⟩ := hinv _ ⟨hpM, hpΩ⟩
    exact c.injOn_param ha hu hb
  have hcont : ContinuousAt γ 0 := hγ.continuousAt
  have hevΩ : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ Ω :=
    hcont.eventually (by rw [h0]; exact hΩ.mem_nhds hpΩ)
  have hρd : DifferentiableAt ℝ ρ (γ 0) := by
    rw [h0]
    exact (hρ.contDiffAt (hΩ.mem_nhds hpΩ)).differentiableAt (by simp)
  set a := fderiv ℝ ρ (γ 0) (deriv γ 0) with ha
  have hδ : HasDerivAt (fun t => ρ (γ t)) a 0 :=
    hρd.hasFDerivAt.comp_hasDerivAt 0 hγ.hasDerivAt
  have hδ0 : ρ (γ 0) = u := by rw [h0, hρu]
  have hφat : ContDiffAt ℝ ∞ c.param u :=
    c.contDiffOn_param.contDiffAt (c.isOpen_source.mem_nhds hu)
  have hφd : DifferentiableAt ℝ c.param u := hφat.differentiableAt (by simp)
  have hback : (fun t => c.param (ρ (γ t))) =ᶠ[𝓝 0] γ := by
    filter_upwards [hev, hevΩ] with t h₁ h₂
    exact (hinv _ ⟨h₁, h₂⟩).2
  have hderiv : deriv γ 0 = fderiv ℝ c.param u a := by
    have : HasDerivAt (fun t => c.param (ρ (γ t))) (fderiv ℝ c.param u a) 0 := by
      have hφ' : HasFDerivAt c.param (fderiv ℝ c.param u) (ρ (γ 0)) := by
        rw [hδ0]
        exact hφd.hasFDerivAt
      exact hφ'.comp_hasDerivAt 0 hδ
    exact (hγ.hasDerivAt.unique (this.congr_of_eventuallyEq hback.symm))
  have hmanN : ∀ᶠ u' in 𝓝 u, c.param u' ∈ M := by
    filter_upwards [c.isOpen_source.mem_nhds hu] with u' hu'
    obtain ⟨-, -, -, hmaps, -⟩ := hpar.1
    exact hmaps hu'
  have hfφ : ContDiffAt ℝ ∞ (f ∘ c.param) u :=
    h2 E E' (Fin c.dim → ℝ) M O f c.param u hM hf hφat hmanN hp
  have hmem : deriv γ 0 ∈ tangentSpace M (c.param u) := by
    rw [h3 E (Fin c.dim → ℝ) M c.source c.param u hM hpar hu, hderiv]
    exact ⟨a, rfl⟩
  refine ⟨hmem, ?_⟩
  have hval := h4 E E' (Fin c.dim → ℝ) M O f c.source c.param u a ⟨deriv γ 0, hmem⟩
    hM hf hpar hu hp hderiv
  rw [hval]
  have hfd : DifferentiableAt ℝ (f ∘ c.param) u := hfφ.differentiableAt (by simp)
  have hcomp : HasDerivAt (fun t => (f ∘ c.param) (ρ (γ t)))
      (fderiv ℝ (f ∘ c.param) u a) 0 := by
    have hf' : HasFDerivAt (f ∘ c.param) (fderiv ℝ (f ∘ c.param) u)
        (ρ (γ 0)) := by
      rw [hδ0]
      exact hfd.hasFDerivAt
    exact hf'.comp_hasDerivAt 0 hδ
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [hback] with t ht
  show f (γ t) = f (c.param (ρ (γ t)))
  rw [ht]
private theorem deriv_mem_tangentSpace (hS : Manifolds.LocalSmoothCalculus)
    {M : Set E} (hM : IsChartedSubset M) {γ : ℝ → E} {p : E}
    (hγ : DifferentiableAt ℝ γ 0) (hev : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ M) (h0 : γ 0 = p)
    (hpM : p ∈ M) : deriv γ 0 ∈ tangentSpace M p := by
  have hid : IsSmoothOnOpen M M (id : E → E) := by
    refine ⟨⟨univ, isOpen_univ, by simp⟩, fun c => ?_⟩
    exact c.contDiffOn_param.mono inter_subset_left
  exact (hasDerivAt_comp_curve hS hM hid hγ hev h0 hpM hpM).1
private theorem tangentSpace_of_relOpen (hS : Manifolds.LocalSmoothCalculus)
    {M O : Set E} (hM : IsChartedSubset M) (hO : ComplexMatrix2.IsRelativelyOpen M O) {p : E}
    (hp : p ∈ O) (hOM : O ⊆ M) : tangentSpace O p = tangentSpace M p := by
  obtain ⟨-, -, h3, -, h5, h6, h7⟩ := id hS
  obtain ⟨c, u, hu, rfl⟩ := hM p (hOM hp)
  have hpar := h6 E M c
  have hpar' := h7 E (Fin c.dim → ℝ) M O c.source c.param hpar hO
  rw [h3 E (Fin c.dim → ℝ) M c.source c.param u hM hpar hu,
    h3 E (Fin c.dim → ℝ) O _ c.param u (h5 E M O hM hO) hpar' ⟨hu, hp⟩]
private theorem param_mem {M : Set E} (c : Chart M) {u : Fin c.dim → ℝ}
    (hu : u ∈ c.source) : c.param u ∈ M := by apply _root_.YangMills.Construction.Matrices.LocalParametrization.param_mem <;> assumption
private def chartOfRelOpen {M O : Set E} (hO : ComplexMatrix2.IsRelativelyOpen M O)
    (c : Chart O) : Chart M where
  dim := c.dim
  source := c.source
  param := c.param
  isOpen_source := c.isOpen_source
  contDiffOn_param := c.contDiffOn_param
  injective_fderiv_param := c.injective_fderiv_param
  injOn_param := c.injOn_param
  isRelativelyOpen_image W hW hop := by
    obtain ⟨A, hA, e⟩ := c.isRelativelyOpen_image W hW hop
    obtain ⟨B, hB, e'⟩ := hO
    exact ⟨A ∩ B, hA.inter hB, by rw [e, e', inter_assoc]⟩
private theorem isRelativelyOpen_of_subset {P O O' : Set E}
    (h : ComplexMatrix2.IsRelativelyOpen P O) (h' : ComplexMatrix2.IsRelativelyOpen P O')
    (hsub : O ⊆ O') : ComplexMatrix2.IsRelativelyOpen O' O := by
  obtain ⟨A, hA, e⟩ := h
  obtain ⟨B, -, e'⟩ := h'
  refine ⟨A, hA, ?_⟩
  ext p
  constructor
  · intro hp
    exact ⟨(e ▸ hp : p ∈ A ∩ P).1, hsub hp⟩
  · rintro ⟨h₁, h₂⟩
    rw [e]
    exact ⟨h₁, (e' ▸ h₂ : p ∈ B ∩ P).2⟩
private theorem isC2_of_smooth {M : Set E} {f : E → ℝ} (h : IsSmoothOnOpen M M f) :
    IsC2OnCharted M f := by apply _root_.YangMills.Construction.TwoStageConstraint.isC2OnCharted_of_isSmoothOnOpen <;> assumption
private theorem contDiffOn_comp_smooth (hS : Manifolds.LocalSmoothCalculus) {P : Type}
    [NormedAddCommGroup P] [NormedSpace ℝ P] {M : Set E} (hM : IsChartedSubset M) {g : E → ℝ}
    (hg : IsSmoothOnOpen M M g) {D : Set P} (hD : IsOpen D) {h : P → E}
    (hh : ContDiffOn ℝ ∞ h D) (hmaps : MapsTo h D M) : ContDiffOn ℝ ∞ (g ∘ h) D := fun u hu =>
  (hS.2.1 E ℝ P M M g h u hM hg (hh.contDiffAt (hD.mem_nhds hu))
    (by filter_upwards [hD.mem_nhds hu] with v hv using hmaps hv) (hmaps hu)).contDiffWithinAt
end Submanifolds
section EdgeValue
variable {L n k j : ℕ}
private theorem positive_or_opposite (b : Edge L n k j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
private theorem field_restrict {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) : fieldOfPositiveValues (restrictToPositiveEdges V) = V := by apply _root_.YangMills.SharedProofs.p407 <;> assumption
private theorem field_apply_positive (w : PositiveEdge L n k j → ComplexMatrix2)
    {b : Edge L n k j} (hb : b.IsPositivelyOriented) :
    fieldOfPositiveValues w b = w ⟨b, hb⟩ := by
  simp [fieldOfPositiveValues, hb]
private def leftFamily (U : Edge L n k j → ComplexMatrix2) :
    (Edge L n k j → ComplexMatrix2) →ₗ[ℝ] PositiveEdge L n k j → ComplexMatrix2 where
  toFun B := fun b => (Complex.I • B b) * U b
  map_add' B B' := by
    funext b
    simp [smul_add, add_mul]
  map_smul' r B := by
    funext b
    simp [smul_comm Complex.I r]
private theorem extendOddly_eq {f A : Edge L n k j → ComplexMatrix2}
    (hA : A ∈ edgeFormSpace L n k j)
    (h : ∀ b : Edge L n k j, b.IsPositivelyOriented → extendOddly f b = A b) :
    extendOddly f = A := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · exact h b hb
  · have hb' := (positive_or_opposite b).resolve_left hb
    have h2 := h _ hb'
    have hrr : b.opposite.opposite = b := PeriodicLattice.Bond.ext rfl rfl
    have h3 := hA.2 b.opposite
    rw [hrr] at h3
    rw [h3, ← h2]
    simp [extendOddly, hb, hb']
private theorem inv_mul_self_of_mem {u : ComplexMatrix2}
    (hu : u ∈ PeriodicLattice.compactGaugeGroup) : u⁻¹ * u = 1 := by apply _root_.YangMills.SharedProofs.p14555 <;> assumption
private theorem cancel_leftFamily_term {A A' u : ComplexMatrix2}
    (hu : u ∈ PeriodicLattice.compactGaugeGroup)
    (h : (Complex.I • A) * u = (Complex.I • A') * u) : A = A' := by
  have h1 : u * u⁻¹ = 1 := by
    have : IsUnit u.det := by
      have := hu.2
      simp_all
    exact Matrix.mul_nonsing_inv u this
  have h2 : Complex.I • A = Complex.I • A' := by
    calc Complex.I • A = (Complex.I • A) * u * u⁻¹ := by rw [mul_assoc, h1, mul_one]
      _ = Complex.I • A' := by rw [h, mul_assoc, h1, mul_one]
  exact smul_right_injective _ Complex.I_ne_zero h2
set_option linter.unusedSectionVars false
private theorem edgeForm_ext {A A' : Edge L n k j → ComplexMatrix2}
    (hA : A ∈ edgeFormSpace L n k j) (hA' : A' ∈ edgeFormSpace L n k j)
    (h : ∀ b : Edge L n k j, b.IsPositivelyOriented → A b = A' b) : A = A' := by apply _root_.YangMills.SharedProofs.p88895 <;> assumption
private theorem leftFamily_injective {U B B' : Edge L n k j → ComplexMatrix2}
    (hU : U ∈ fieldSpace L n k j) (hB : B ∈ edgeFormSpace L n k j)
    (hB' : B' ∈ edgeFormSpace L n k j) (h : leftFamily U B = leftFamily U B') : B = B' :=
  edgeForm_ext hB hB' fun b hb =>
    cancel_leftFamily_term (hU.1 b (mem_univ _)) (congrFun h ⟨b, hb⟩)
private theorem deriv_entry {γ : ℝ → Edge L n k j → ComplexMatrix2}
    (h0 : γ 0 ∈ fieldSpace L n k j) {b : Edge L n k j} (hb : b.IsPositivelyOriented) :
    deriv (fun t => γ t b) 0 = (Complex.I • curveTangent γ b) * γ 0 b := by
  have hu : (γ 0 b)⁻¹ * γ 0 b = 1 := inv_mul_self_of_mem (h0.1 b (mem_univ _))
  simp only [curveTangent, extendOddly, if_pos hb]
  rw [smul_smul, mul_inv_cancel₀ Complex.I_ne_zero, one_smul, mul_assoc, hu, mul_one]
variable [Fintype (PositiveEdge L n k j)]
private theorem deriv_restrict {γ : ℝ → Edge L n k j → ComplexMatrix2}
    (h0 : γ 0 ∈ fieldSpace L n k j)
    (hd : ∀ b : Edge L n k j, b.IsPositivelyOriented → DifferentiableAt ℝ (fun t => γ t b) 0) :
    DifferentiableAt ℝ (fun t => restrictToPositiveEdges (γ t)) 0 ∧
      deriv (fun t => restrictToPositiveEdges (γ t)) 0 = leftFamily (γ 0) (curveTangent γ) := by
  refine ⟨differentiableAt_pi.2 fun b => hd b.1 b.2, ?_⟩
  have e : deriv (fun t => restrictToPositiveEdges (γ t)) 0 =
      fun b => deriv (fun t => γ t b.1) 0 :=
    deriv_pi (φ := fun t => restrictToPositiveEdges (γ t)) fun b => hd b.1 b.2
  rw [e]
  funext b
  have hu : (γ 0 b.1)⁻¹ * γ 0 b.1 = 1 := inv_mul_self_of_mem (h0.1 b.1 (mem_univ _))
  show deriv (fun t => γ t b.1) 0 = (Complex.I • curveTangent γ b.1) * γ 0 b.1
  simp only [curveTangent, extendOddly, if_pos b.2]
  rw [smul_smul, mul_inv_cancel₀ Complex.I_ne_zero, one_smul, mul_assoc, hu, mul_one]
private theorem deriv_pi_on {I : Set ℝ} (hI : IsOpen I)
    {w : ℝ → PositiveEdge L n k j → ComplexMatrix2}
    (hw : DifferentiableOn ℝ w I) {t : ℝ} (ht : t ∈ I) :
    deriv w t = fun b => deriv (fun s => w s b) t :=
  deriv_pi fun b => differentiableAt_pi.1 (hw.differentiableAt (hI.mem_nhds ht)) b
private theorem restrict_isCurve {N : Set (Edge L n k j → ComplexMatrix2)} {I : Set ℝ}
    {γ : ℝ → Edge L n k j → ComplexMatrix2} (hc : (fieldCurveData L n k j).IsCurve I γ)
    (hm : MapsTo γ I N) :
    (vectorCurveData (PositiveEdge L n k j → ComplexMatrix2)).IsCurve I
        (fun t => restrictToPositiveEdges (γ t)) ∧
      MapsTo (fun t => restrictToPositiveEdges (γ t)) I (restrictToPositiveEdges '' N) :=
  ⟨⟨hc.1, differentiableOn_pi.2 fun b => hc.2.2 b.1 b.2⟩, fun t ht => ⟨γ t, hm ht, rfl⟩⟩
private theorem restrict_isTwiceDiffCurve {I : Set ℝ} {γ : ℝ → Edge L n k j → ComplexMatrix2}
    (hc : (fieldCurveData L n k j).IsTwiceDiffCurve I γ) :
    (vectorCurveData (PositiveEdge L n k j → ComplexMatrix2)).IsTwiceDiffCurve I
      (fun t => restrictToPositiveEdges (γ t)) := by
  obtain ⟨h1, h2⟩ := hc
  have hw : DifferentiableOn ℝ (fun t => restrictToPositiveEdges (γ t)) I :=
    differentiableOn_pi.2 fun b => h1.2.2 b.1 b.2
  refine ⟨h1.1, hw, ?_⟩
  refine (differentiableOn_pi.2 fun b => h2 b.1 b.2).congr fun t ht => ?_
  exact deriv_pi_on h1.1.1 hw ht
private theorem field_isCurve {N : Set (Edge L n k j → ComplexMatrix2)}
    (hN : N ⊆ fieldSpace L n k j)
    {I : Set ℝ} {w : ℝ → PositiveEdge L n k j → ComplexMatrix2}
    (hc : (vectorCurveData (PositiveEdge L n k j → ComplexMatrix2)).IsCurve I w)
    (hm : MapsTo w I (restrictToPositiveEdges '' N)) :
    (fieldCurveData L n k j).IsCurve I (fun t => fieldOfPositiveValues (w t)) ∧
      MapsTo (fun t => fieldOfPositiveValues (w t)) I N ∧
      ∀ t ∈ I, restrictToPositiveEdges (fieldOfPositiveValues (w t)) = w t := by
  have hval : ∀ t ∈ I, ∃ V ∈ N, restrictToPositiveEdges V = w t ∧
      fieldOfPositiveValues (w t) = V := by
    intro t ht
    obtain ⟨V, hV, e⟩ := hm ht
    exact ⟨V, hV, e, by rw [← e, field_restrict (hN hV)]⟩
  have hmaps : MapsTo (fun t => fieldOfPositiveValues (w t)) I N := by
    intro t ht
    obtain ⟨V, hV, -, e⟩ := hval t ht
    show fieldOfPositiveValues (w t) ∈ N
    rwa [e]
  refine ⟨⟨hc.1, fun t ht => hN (hmaps ht), fun b hb => ?_⟩, hmaps, fun t ht => ?_⟩
  · have : (fun t => fieldOfPositiveValues (w t) b) = fun t => w t ⟨b, hb⟩ :=
      funext fun t => field_apply_positive _ hb
    rw [this]
    exact differentiableOn_pi.1 hc.2 ⟨b, hb⟩
  · obtain ⟨V, -, e₁, e₂⟩ := hval t ht
    rw [e₂, e₁]
private theorem field_isTwiceDiffCurve {I : Set ℝ}
    {w : ℝ → PositiveEdge L n k j → ComplexMatrix2}
    (hc : (vectorCurveData (PositiveEdge L n k j → ComplexMatrix2)).IsTwiceDiffCurve I w)
    (hcurve : (fieldCurveData L n k j).IsCurve I (fun t => fieldOfPositiveValues (w t))) :
    (fieldCurveData L n k j).IsTwiceDiffCurve I
      (fun t => fieldOfPositiveValues (w t)) := by
  refine ⟨hcurve, fun b hb => ?_⟩
  have e : (fun t => fieldOfPositiveValues (w t) b) = fun t => w t ⟨b, hb⟩ :=
    funext fun t => field_apply_positive _ hb
  rw [e]
  refine (differentiableOn_pi.1 hc.2.2 ⟨b, hb⟩).congr fun t ht => ?_
  exact (congrFun (deriv_pi_on hc.1.1 hc.2.1 ht) ⟨b, hb⟩).symm
private theorem eventually_value {N : Set (Edge L n k j → ComplexMatrix2)}
    {F : (Edge L n k j → ComplexMatrix2) → ℝ}
    {F' : (PositiveEdge L n k j → ComplexMatrix2) → ℝ}
    (hF : ∀ V ∈ N, F' (restrictToPositiveEdges V) = F V)
    {I : Set ℝ} (hI : IsOpenIntervalAroundZero I) {γ : ℝ → Edge L n k j → ComplexMatrix2}
    (hm : MapsTo γ I N) :
    (fun t => F' (restrictToPositiveEdges (γ t))) =ᶠ[𝓝 0] fun t => F (γ t) := by
  filter_upwards [hI.1.mem_nhds hI.2.2] with t ht
  exact hF _ (hm ht)
private theorem isCriticalOn_iff {N : Set (Edge L n k j → ComplexMatrix2)}
    (hN : N ⊆ fieldSpace L n k j)
    {F : (Edge L n k j → ComplexMatrix2) → ℝ} {F' : (PositiveEdge L n k j → ComplexMatrix2) → ℝ}
    (hF : ∀ V ∈ N, F' (restrictToPositiveEdges V) = F V) {x : Edge L n k j → ComplexMatrix2}
    (hx : x ∈ fieldSpace L n k j) :
    (fieldCurveData L n k j).IsCriticalOn N F x ↔
      (vectorCurveData (PositiveEdge L n k j → ComplexMatrix2)).IsCriticalOn
        (restrictToPositiveEdges '' N) F' (restrictToPositiveEdges x) := by
  constructor
  · rintro ⟨hxN, h⟩
    refine ⟨⟨x, hxN, rfl⟩, fun I w hw hm h0 => ?_⟩
    obtain ⟨hc, hmaps, hback⟩ := field_isCurve hN hw hm
    have h₀ : fieldOfPositiveValues (w 0) = x := by rw [h0, field_restrict hx]
    refine (Filter.EventuallyEq.deriv_eq ?_).trans (h I _ hc hmaps h₀)
    have hev := eventually_value hF hw.1 hmaps
    filter_upwards [hev, hw.1.1.mem_nhds hw.1.2.2] with t h₁ h₂
    rw [← h₁, hback t h₂]
  · rintro ⟨⟨V, hV, e⟩, h⟩
    have hVx : V = x := by
      rw [← field_restrict (hN hV), e, field_restrict hx]
    subst hVx
    refine ⟨hV, fun I γ hc hm h0 => ?_⟩
    obtain ⟨hw, hwm⟩ := restrict_isCurve hc hm
    exact ((eventually_value hF hc.1 hm).deriv_eq).symm.trans (h I _ hw hwm (by simp only [h0]))
private theorem isHessianFormAt_iff {N : Set (Edge L n k j → ComplexMatrix2)}
    (hN : N ⊆ fieldSpace L n k j) {F : (Edge L n k j → ComplexMatrix2) → ℝ}
    {F' : (PositiveEdge L n k j → ComplexMatrix2) → ℝ}
    (hF : ∀ V ∈ N, F' (restrictToPositiveEdges V) = F V)
    {x : Edge L n k j → ComplexMatrix2} (hx : x ∈ fieldSpace L n k j) {S : Type*}
    (ι : S → Edge L n k j → ComplexMatrix2) (hι : ∀ v, ι v ∈ edgeFormSpace L n k j)
    (Q : S → ℝ) :
    (fieldCurveData L n k j).IsHessianFormAt ι N F x Q ↔
      (vectorCurveData (PositiveEdge L n k j → ComplexMatrix2)).IsHessianFormAt
        (fun v => leftFamily x (ι v)) (restrictToPositiveEdges '' N) F'
        (restrictToPositiveEdges x) Q := by
  constructor
  · intro h I w v hw hm h0 ht
    have hcu : (vectorCurveData (PositiveEdge L n k j → ComplexMatrix2)).IsCurve I w :=
      ⟨hw.1, hw.2.1⟩
    obtain ⟨hc, hmaps, hback⟩ := field_isCurve hN hcu hm
    have h₀ : fieldOfPositiveValues (w 0) = x := by rw [h0, field_restrict hx]
    have htw := field_isTwiceDiffCurve hw hc
    set γ : ℝ → Edge L n k j → ComplexMatrix2 := fun t => fieldOfPositiveValues (w t) with hγ
    have hγ0 : γ 0 = x := h₀
    have heq : (fun t => restrictToPositiveEdges (γ t)) =ᶠ[𝓝 0] w := by
      filter_upwards [hw.1.1.mem_nhds hw.1.2.2] with t h₂
      exact hback t h₂
    have hd := (deriv_restrict (γ := γ) (by rw [hγ0]; exact hx)
      fun b hb => (hc.2.2 b hb).differentiableAt (hw.1.1.mem_nhds hw.1.2.2)).2
    have htan : (fieldCurveData L n k j).tangent γ = ι v := by
      refine extendOddly_eq
        (f := fun b => Complex.I⁻¹ • (deriv (fun t => γ t b) 0 * (γ 0 b)⁻¹))
        (hι v) fun b hb => ?_
      have h1 : leftFamily x (curveTangent γ) = leftFamily x (ι v) := by
        rw [← hγ0, ← hd, heq.deriv_eq, hγ0]
        exact ht
      exact cancel_leftFamily_term (hx.1 b (mem_univ _)) (congrFun h1 ⟨b, hb⟩)
    rw [h I γ v htw hmaps hγ0 htan]
    have hev : (fun t => F (γ t)) =ᶠ[𝓝 0] fun t => F' (w t) := by
      filter_upwards [eventually_value hF hc.1 hmaps, heq] with t h₁ h₂
      rw [← h₁, h₂]
    exact (hev.deriv).deriv_eq
  · intro h I γ v hc hm h0 ht
    have hw := restrict_isTwiceDiffCurve hc
    have hwm := (restrict_isCurve hc.1 hm).2
    have hd := (deriv_restrict (γ := γ) (by rw [h0]; exact hx)
      fun b hb => (hc.1.2.2 b hb).differentiableAt (hc.1.1.1.mem_nhds hc.1.1.2.2)).2
    rw [h I _ v hw hwm (by simp only [h0]) (by
      show deriv _ 0 = _
      rw [hd, h0]
      exact congrArg _ ht)]
    exact ((eventually_value hF hc.1.1 hm).deriv).deriv_eq
private theorem hessianForm_eq {N : Set (Edge L n k j → ComplexMatrix2)}
    (hN : N ⊆ fieldSpace L n k j) {F : (Edge L n k j → ComplexMatrix2) → ℝ}
    {F' : (PositiveEdge L n k j → ComplexMatrix2) → ℝ}
    (hF : ∀ V ∈ N, F' (restrictToPositiveEdges V) = F V)
    {x : Edge L n k j → ComplexMatrix2} (hx : x ∈ fieldSpace L n k j) {S : Type*}
    [AddCommGroup S] [Module ℝ S] (ι : S → Edge L n k j → ComplexMatrix2)
    (hι : ∀ v, ι v ∈ edgeFormSpace L n k j) :
    (fieldCurveData L n k j).hessianForm ι N F x =
      (vectorCurveData (PositiveEdge L n k j → ComplexMatrix2)).hessianForm
        (fun v => leftFamily x (ι v)) (restrictToPositiveEdges '' N) F'
        (restrictToPositiveEdges x) := by
  unfold Geometry.CurveData.hessianForm
  congr 1
  funext Q
  exact propext (isHessianFormAt_iff hN hF hx ι hι Q)
private theorem map_tangentSpan {N : Set (Edge L n k j → ComplexMatrix2)}
    (hN : N ⊆ fieldSpace L n k j) {x : Edge L n k j → ComplexMatrix2}
    (hx : x ∈ fieldSpace L n k j) :
    ((fieldCurveData L n k j).tangentSpan N x).map (leftFamily x) =
      (vectorCurveData (PositiveEdge L n k j → ComplexMatrix2)).tangentSpan
        (restrictToPositiveEdges '' N) (restrictToPositiveEdges x) := by
  apply le_antisymm
  · rw [Geometry.CurveData.tangentSpan, Submodule.map_span]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨v, ⟨I, γ, hc, hm, h0, rfl⟩, rfl⟩
    obtain ⟨hw, hwm⟩ := restrict_isCurve hc hm
    have hd := (deriv_restrict (γ := γ) (by rw [h0]; exact hx)
      fun b hb => (hc.2.2 b hb).differentiableAt (hc.1.1.mem_nhds hc.1.2.2)).2
    refine Submodule.subset_span ⟨I, _, hw, hwm, by simp only [h0], ?_⟩
    rw [← h0]
    exact hd
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨I, w, hw, hm, h0, rfl⟩
    obtain ⟨hc, hmaps, hback⟩ := field_isCurve hN hw hm
    have h₀ : fieldOfPositiveValues (w 0) = x := by rw [h0, field_restrict hx]
    have heq : (fun t => restrictToPositiveEdges (fieldOfPositiveValues (w t))) =ᶠ[𝓝 0] w := by
      filter_upwards [hw.1.1.mem_nhds hw.1.2.2] with t h₂
      exact hback t h₂
    have hd := (deriv_restrict (γ := fun t => fieldOfPositiveValues (w t))
      (by simp only [h₀]; exact hx)
      fun b hb => (hc.2.2 b hb).differentiableAt (hw.1.1.mem_nhds hw.1.2.2)).2
    refine ⟨_, Submodule.subset_span ⟨I, _, hc, hmaps, h₀, rfl⟩, ?_⟩
    show leftFamily x (curveTangent _) = deriv w 0
    rw [← heq.deriv_eq, hd]
    simp only [h₀]
end EdgeValue
section PowerEvaluation
variable {L n k a b : ℕ}
private theorem finrank_traceless : Module.finrank ℂ ComplexMatrix2.traceless = 3 := by apply _root_.YangMills.SharedProofs.p8292 <;> assumption
private theorem nonempty_positiveEdge (hE : BondSetFields.ProductStructureHolds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : a ≤ k) :
    Nonempty (PositiveEdge L n k a) := by apply _root_.YangMills.SharedProofs.p12312 <;> assumption
private theorem holomorphicScalar_of_coords {σ : Type} [Fintype σ]
    {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {W : Set (σ ⊕ Empty → ComplexMatrix2)}
    {Φ : (σ ⊕ Empty → ComplexMatrix2) → Coordinates.ComplexCoordinates 1}
    (h : GroupLieProduct.IsHolomorphicToCoords b (Equiv.refl _) W Φ) :
    PowerExpCharts.HolomorphicScalar b W fun q => Φ q 0 := by apply _root_.YangMills.SharedProofs.p9409 <;> assumption
private theorem isChartedSubset_power (hC : PowerExpCharts.ExpChartsStatement) (σ : Type)
    [Fintype σ] [Nonempty σ] : IsChartedSubset (specialUnitaryPower σ) := by
  intro p hp
  obtain ⟨-, hY, hε⟩ := (hC σ σ).1 p hp
  have hpos : 0 < Real.log (19 / 10) := Real.log_pos (by norm_num)
  obtain ⟨-, -, -, -, -, -, -, -, c, ν, hdom, hpar⟩ :=
    hε _ hpos (by rw [Real.exp_log (by norm_num)])
  have h0 : PowerExpCharts.ofCoeffs (fun s a => (0 : Fin c.dim → ℝ) (ν (s, a))) = 0 := by
    funext s
    simp [PowerExpCharts.ofCoeffs]
  have hz : (0 : ComplexMatrix2.LieElement).toMatrix = 0 := rfl
  have hmem : (0 : Fin c.dim → ℝ) ∈ c.source := by
    rw [hdom]
    show PowerExpCharts.ofCoeffs _ ∈ PowerExpCharts.smallBall σ _
    rw [h0]
    intro s
    show ComplexMatrix2.operatorNorm (0 : ComplexMatrix2.LieElement).toMatrix < _
    rw [hz]
    simpa [ComplexMatrix2.operatorNorm] using hpos
  refine ⟨c, 0, hmem, ?_⟩
  rw [hpar 0 hmem, h0, (hY 0).2.2 |> fun _ => (hY 0).2.1]
  funext s
  show ComplexMatrix2.matExp (Complex.I • (0 : ComplexMatrix2.LieElement).toMatrix) * p s = p s
  rw [hz]
  simp [ComplexMatrix2.matExp]
private abbrev restrictMap (m : (Edge L n k a → ComplexMatrix2) → Edge L n k b → ComplexMatrix2) :
    (PositiveEdge L n k a → ComplexMatrix2) → PositiveEdge L n k b → ComplexMatrix2 :=
  fun w => restrictToPositiveEdges (m (fieldOfPositiveValues w))
private theorem restrictMap_restrict
    {m : (Edge L n k a → ComplexMatrix2) → Edge L n k b → ComplexMatrix2}
    {U : Edge L n k a → ComplexMatrix2} (hU : U ∈ fieldSpace L n k a) :
    restrictMap m (restrictToPositiveEdges U) = restrictToPositiveEdges (m U) := by
  simp only [restrictMap, field_restrict hU]
variable [i₁ : Fintype (PositiveEdge L n k a)] [i₂ : Fintype (PositiveEdge L n k b)]
private theorem contDiffOn_restrictMap (hC : PowerExpCharts.ExpChartsStatement)
    (hE : BondSetFields.ProductStructureHolds) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (ha : a ≤ k) (hb : b ≤ k) {𝒰 : Set (Edge L n k a → ComplexMatrix2)}
    {m : (Edge L n k a → ComplexMatrix2) → Edge L n k b → ComplexMatrix2}
    (hm : IsAnalyticFieldMap 𝒰 m) (c : Chart (specialUnitaryPower (PositiveEdge L n k a))) :
    ContDiffOn ℝ ∞ (c.pullback (restrictMap m)) (c.coords (restrictToPositiveEdges '' 𝒰)) := by
  obtain ⟨hopen, hmaps, f₁, f₂, hra⟩ := hm
  have e₁ : f₁ = i₁ := Subsingleton.elim _ _
  have e₂ : f₂ = i₂ := Subsingleton.elim _ _
  subst e₁ e₂
  have := nonempty_positiveEdge hE hL hn ha
  have := nonempty_positiveEdge hE hL hn hb
  let β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless :=
    Module.finBasisOfFinrankEq ℂ ComplexMatrix2.traceless finrank_traceless
  have hread := ((hC (PositiveEdge L n k a) (PositiveEdge L n k b)).2.2.2.2.2.2.2 β).1
  have hconf : ∀ {U}, U ∈ 𝒰 → fieldOfPositiveValues (restrictToPositiveEdges U) = U :=
    fun hU => field_restrict (hopen.1 hU)
  have hinto : MapsTo (restrictMap m) (restrictToPositiveEdges '' 𝒰)
      (specialUnitaryPower (PositiveEdge L n k b)) := by
    rintro _ ⟨U, hU, rfl⟩
    show restrictToPositiveEdges (m (fieldOfPositiveValues (restrictToPositiveEdges U))) ∈ _
    rw [hconf hU]
    exact fun c => (hmaps hU).1 c (mem_univ _)
  have hrest : PowerExpCharts.IsLocallyHolomorphicRestriction
      (GroupLieProduct.IsHolomorphicToProduct β) GroupLieProduct.asGroupFactors
      (restrictToPositiveEdges '' 𝒰) (restrictMap m) := by
    rintro _ ⟨U, hU, rfl⟩
    have hq : GroupLieProduct.asGroupFactors (restrictToPositiveEdges U) ∈
        {q : PositiveEdge L n k a ⊕ Empty → ComplexMatrix2 |
          fieldOfPositiveValues (GroupLieProduct.Subspaces.groupComponent q) ∈ 𝒰} := by
      show fieldOfPositiveValues (restrictToPositiveEdges U) ∈ 𝒰
      rw [hconf hU]
      exact hU
    obtain ⟨𝒳, hp𝒳, -, -, Ψ, hΨ, heq⟩ := hra.2.2.2 _ hq
    refine ⟨𝒳, Ψ, hp𝒳, hΨ β, ?_⟩
    rintro _ ⟨V, hV, rfl⟩ hx
    refine heq ⟨hx, ?_, ?_⟩
    · exact (Submodule.mem_bot ℝ).2 (funext fun e => e.elim)
    · exact fun c => (hopen.1 hV).1 c (mem_univ _)
  exact ((hread _ hopen.2).2.2.2 _ hinto hrest).1.2 c
private theorem contDiffOn_restrictFunction (hC : PowerExpCharts.ExpChartsStatement)
    (hE : BondSetFields.ProductStructureHolds) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (ha : a ≤ k) {𝒰 : Set (Edge L n k a → ComplexMatrix2)}
    {F : (Edge L n k a → ComplexMatrix2) → ℝ}
    (hF : IsAnalyticFieldFunction 𝒰 F) (c : Chart (specialUnitaryPower (PositiveEdge L n k a))) :
    ContDiffOn ℝ ∞ (c.pullback fun w => F (fieldOfPositiveValues w))
      (c.coords (restrictToPositiveEdges '' 𝒰)) := by
  obtain ⟨hopen, f₁, hra⟩ := hF
  have e₁ : f₁ = i₁ := Subsingleton.elim _ _
  subst e₁
  have := nonempty_positiveEdge hE hL hn ha
  let β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless :=
    Module.finBasisOfFinrankEq ℂ ComplexMatrix2.traceless finrank_traceless
  have hread := ((hC (PositiveEdge L n k a) (PositiveEdge L n k a)).2.2.2.2.2.2.2 β).1
  have hconf : ∀ {U}, U ∈ 𝒰 → fieldOfPositiveValues (restrictToPositiveEdges U) = U :=
    fun hU => field_restrict (hopen.1 hU)
  have hrest : PowerExpCharts.IsLocallyHolomorphicRestriction
      (PowerExpCharts.HolomorphicScalar β) Complex.ofReal
      (restrictToPositiveEdges '' 𝒰) (fun w => F (fieldOfPositiveValues w)) := by
    rintro _ ⟨U, hU, rfl⟩
    have hq : GroupLieProduct.asGroupFactors (restrictToPositiveEdges U) ∈
        {q : PositiveEdge L n k a ⊕ Empty → ComplexMatrix2 |
          fieldOfPositiveValues (GroupLieProduct.Subspaces.groupComponent q) ∈ 𝒰} := by
      show fieldOfPositiveValues (restrictToPositiveEdges U) ∈ 𝒰
      rw [hconf hU]
      exact hU
    obtain ⟨𝒳, hp𝒳, -, -, Φ, hΦ, heq⟩ := hra.2 _ hq
    refine ⟨𝒳, fun q => Φ q 0, hp𝒳, holomorphicScalar_of_coords (hΦ β), ?_⟩
    rintro _ ⟨U', hU', rfl⟩ hx
    have hval := heq ⟨hx, (Submodule.mem_bot ℝ).2 (funext fun e => e.elim),
      fun c => (hopen.1 hU').1 c (mem_univ _)⟩
    exact congrFun hval 0
  exact (((hread _ hopen.2).1 _ hrest).1.2 c)
private theorem isSmoothOnOpen_restrict {𝒴 𝒰 : Set (Edge L n k a → ComplexMatrix2)}
    (h𝒴 : IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒴)
    (h𝒰 : IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰)
    (hsub : 𝒰 ⊆ 𝒴) {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : (PositiveEdge L n k a → ComplexMatrix2) → F}
    (hf : ∀ c : Chart (specialUnitaryPower (PositiveEdge L n k a)),
      ContDiffOn ℝ ∞ (c.pullback f) (c.coords (restrictToPositiveEdges '' 𝒰))) :
    IsSmoothOnOpen (restrictToPositiveEdges '' 𝒴) (restrictToPositiveEdges '' 𝒰) f :=
  ⟨isRelativelyOpen_of_subset h𝒰.2 h𝒴.2 (image_mono hsub),
    fun c => hf (chartOfRelOpen (M := specialUnitaryPower (PositiveEdge L n k a)) h𝒴.2 c)⟩
private theorem isChartedSubset_image (hS : Manifolds.LocalSmoothCalculus)
    (hC : PowerExpCharts.ExpChartsStatement) (hE : BondSetFields.ProductStructureHolds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (ha : a ≤ k)
    {𝒳 : Set (Edge L n k a → ComplexMatrix2)}
    (h𝒳 : IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒳) :
    IsChartedSubset (restrictToPositiveEdges '' 𝒳) := by
  have := nonempty_positiveEdge hE hL hn ha
  exact hS.2.2.2.2.1 _ _ _ (isChartedSubset_power hC _) h𝒳.2
private theorem fieldSpace_isOpen (hA : LeftChartFields.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (ha : a ≤ k) :
    IsOpenFieldSet PeriodicLattice.compactGaugeGroup (fieldSpace L n k a) := by
  have hT := ((hA.2.2 L k a hL ha).1 n hn).2.1
  refine ⟨subset_rfl, ?_⟩
  rw [hT.2.1.image_eq]
  exact ⟨univ, isOpen_univ, by simp [edgePower_compactGaugeGroup]⟩
private theorem mem_tangentSpace_iff (hS : Manifolds.LocalSmoothCalculus)
    (hC : PowerExpCharts.ExpChartsStatement) (hE : BondSetFields.ProductStructureHolds)
    (hA : LeftChartFields.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (ha : a ≤ k)
    {𝒳 : Set (Edge L n k a → ComplexMatrix2)}
    (h𝒳 : IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒳) {U : Edge L n k a → ComplexMatrix2}
    (hU : U ∈ 𝒳) (Y : PositiveEdge L n k a → ComplexMatrix2) :
    Y ∈ tangentSpace (restrictToPositiveEdges '' 𝒳) (restrictToPositiveEdges U) ↔
      ∃ B ∈ edgeFormSpace L n k a, leftFamily U B = Y := by
  have := nonempty_positiveEdge hE hL hn ha
  have hT := (hA.2.2 L k a hL ha).1 n hn
  have hUc := h𝒳.1 hU
  have hman := isChartedSubset_power hC (PositiveEdge L n k a)
  have hsub : restrictToPositiveEdges '' 𝒳 ⊆ specialUnitaryPower (PositiveEdge L n k a) := by
    rintro _ ⟨V, hV, rfl⟩
    exact fun c => (h𝒳.1 hV).1 c (mem_univ _)
  rw [tangentSpace_of_relOpen hS hman h𝒳.2 ⟨U, hU, rfl⟩ hsub]
  have h1 := Set.ext_iff.1 (hT.2.1.2.2 i₁ U hUc).1 Y
  have h2 := ((hT.1.2.1 U hUc).1 Y)
  refine h1.trans (h2.trans ?_)
  constructor
  · rintro ⟨B, hB, e⟩
    exact ⟨B, hB, funext fun b => (e b).symm⟩
  · rintro ⟨B, hB, e⟩
    exact ⟨B, hB, fun b => (congrFun e b).symm⟩
private theorem exists_curve_tangent (hA : LeftChartFields.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (ha : a ≤ k)
    {U B : Edge L n k a → ComplexMatrix2}
    (hU : U ∈ fieldSpace L n k a) (hB : B ∈ edgeFormSpace L n k a) :
    ∃ (I : Set ℝ) (γ : ℝ → Edge L n k a → ComplexMatrix2), (fieldCurveData L n k a).IsCurve I γ ∧
      γ 0 = U ∧ curveTangent γ = B := by
  have hT := (hA.2.2 L k a hL ha).1 n hn
  have key : ∃ (I : Set ℝ) (γ : ℝ → Edge L n k a → ComplexMatrix2),
      IsDifferentiableFieldCurve PeriodicLattice.compactGaugeGroup I γ ∧ γ 0 = U ∧
        ∀ b : PositiveEdge L n k a, deriv (fun t => γ t b.1) 0 = leftFamily U B b :=
    ((hT.1.2.1 U hU).1 (leftFamily U B)).2 ⟨B, hB, fun b => rfl⟩
  obtain ⟨I, γ, hc, rfl, hd⟩ := key
  refine ⟨I, γ, hc, rfl, ?_⟩
  refine extendOddly_eq
    (f := fun b => Complex.I⁻¹ • (deriv (fun t => γ t b) 0 * (γ 0 b)⁻¹)) hB fun b hb => ?_
  exact cancel_leftFamily_term (hU.1 b (mem_univ _))
    ((deriv_entry hU hb).symm.trans (hd ⟨b, hb⟩))
end PowerEvaluation
section LeftDifferentials
private structure Inputs : Prop where
  smooth : Manifolds.LocalSmoothCalculus
  charts : PowerExpCharts.ExpChartsStatement
  edges : BondSetFields.ProductStructureHolds
  left : LeftChartFields.Claim
  curves : FiniteLevelCurveDifferentials.Statement
  differentiable : AnalyticMapDifferentiableStatement
variable {L n k a b : ℕ} [i₁ : Fintype (PositiveEdge L n k a)]
  [i₂ : Fintype (PositiveEdge L n k b)]
private theorem curveTangent_mem (H : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (ha : a ≤ k) {γ : ℝ → Edge L n k a → ComplexMatrix2}
    (h0 : γ 0 ∈ fieldSpace L n k a)
    (hev : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ fieldSpace L n k a)
    (hd : ∀ b : Edge L n k a, b.IsPositivelyOriented → DifferentiableAt ℝ (fun t => γ t b) 0) :
    curveTangent γ ∈ edgeFormSpace L n k a := by
  have hcfg := fieldSpace_isOpen H.left hL hn ha
  have hman := isChartedSubset_image H.smooth H.charts H.edges hL hn ha hcfg
  obtain ⟨hw, e⟩ := deriv_restrict h0 hd
  have hmem := deriv_mem_tangentSpace H.smooth hman hw
    (hev.mono fun t ht => ⟨γ t, ht, rfl⟩) rfl ⟨γ 0, h0, rfl⟩
  obtain ⟨B, hB, e'⟩ :=
    (mem_tangentSpace_iff H.smooth H.charts H.edges H.left hL hn ha hcfg h0 _).1 hmem
  have : curveTangent γ = B :=
    extendOddly_eq (f := fun b => Complex.I⁻¹ • (deriv (fun t => γ t b) 0 * (γ 0 b)⁻¹)) hB
      fun b hb => cancel_leftFamily_term (h0.1 b (mem_univ _))
        (congrFun (e.symm.trans e'.symm) ⟨b, hb⟩)
  rw [this]
  exact hB
private theorem leftDifferential_mem_and_eq (H : Inputs)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (ha : a ≤ k) (hb : b ≤ k) {𝒳 : Set (Edge L n k a → ComplexMatrix2)}
    {m : (Edge L n k a → ComplexMatrix2) → Edge L n k b → ComplexMatrix2}
    (hm : IsAnalyticFieldMap 𝒳 m)
    {U B : Edge L n k a → ComplexMatrix2} (hU : U ∈ 𝒳) (hB : B ∈ edgeFormSpace L n k a) :
    leftDifferential m U B ∈ edgeFormSpace L n k b ∧
      ∃ h : leftFamily U B ∈ tangentSpace (restrictToPositiveEdges '' 𝒳)
          (restrictToPositiveEdges U),
        tangentDifferential (restrictToPositiveEdges '' 𝒳) (restrictMap m)
            (restrictToPositiveEdges U) ⟨leftFamily U B, h⟩ =
          leftFamily (m U) (leftDifferential m U B) := by
  have h𝒳 := hm.1
  have hUc := h𝒳.1 hU
  obtain ⟨I, γ, hc, rfl, rfl⟩ := exists_curve_tangent H.left hL hn ha hUc hB
  have hIn : I ∈ 𝓝 (0 : ℝ) := hc.1.1.mem_nhds hc.1.2.2
  have hγat : ∀ b' : Edge L n k a, b'.IsPositivelyOriented →
      DifferentiableAt ℝ (fun t => γ t b') 0 :=
    fun b' hb' => (hc.2.2 b' hb').differentiableAt hIn
  obtain ⟨hw, hder⟩ := deriv_restrict hUc hγat
  have hman := isChartedSubset_image H.smooth H.charts H.edges hL hn ha h𝒳
  obtain ⟨O, hO, e⟩ := h𝒳.2
  have hcont : ContinuousAt (fun t => restrictToPositiveEdges (γ t)) 0 := hw.continuousAt
  have hmemO : restrictToPositiveEdges (γ 0) ∈ O := by
    have : restrictToPositiveEdges (γ 0) ∈ restrictToPositiveEdges '' 𝒳 := ⟨_, hU, rfl⟩
    rw [e] at this
    exact this.1
  have hγX : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ 𝒳 := by
    filter_upwards [hcont.eventually (hO.mem_nhds hmemO), hIn] with t h₁ h₂
    have hct : γ t ∈ fieldSpace L n k a := hc.2.1 h₂
    have hi : restrictToPositiveEdges (γ t) ∈ restrictToPositiveEdges '' 𝒳 := by
      rw [e]
      exact ⟨h₁, fun c => hct.1 c (mem_univ _)⟩
    obtain ⟨V, hV, eV⟩ := hi
    have hVt : V = γ t := by
      rw [← field_restrict (h𝒳.1 hV), eV, field_restrict hct]
    exact hVt ▸ hV
  have hsm := isSmoothOnOpen_restrict h𝒳 h𝒳 subset_rfl
    (contDiffOn_restrictMap H.charts H.edges hL hn ha hb hm)
  obtain ⟨hmem, hderiv⟩ := hasDerivAt_comp_curve H.smooth hman hsm hw
    (hγX.mono fun t ht => ⟨_, ht, rfl⟩) rfl ⟨_, hU, rfl⟩ ⟨_, hU, rfl⟩
  obtain ⟨hmd, hmt⟩ := (H.curves L k a b hL ha hb n hn).1 𝒳 m
    (H.differentiable L n k a b hL hn ha hb 𝒳 m hm) _ hU I γ hc rfl
  have hmU : m (γ 0) ∈ fieldSpace L n k b := hm.2.1 hU
  obtain ⟨hw₂, hder₂⟩ := deriv_restrict (γ := fun t => m (γ t)) hmU hmd
  have hform : leftDifferential m (γ 0) (curveTangent γ) ∈ edgeFormSpace L n k b := by
    rw [← hmt]
    exact curveTangent_mem H hL hn hb hmU (hγX.mono fun t ht => hm.2.1 ht) hmd
  have heq : (fun t => restrictMap m (restrictToPositiveEdges (γ t))) =ᶠ[𝓝 0]
      fun t => restrictToPositiveEdges (m (γ t)) := by
    filter_upwards [hγX] with t ht
    exact restrictMap_restrict (h𝒳.1 ht)
  have hval := hderiv.unique (hw₂.hasDerivAt.congr_of_eventuallyEq heq)
  refine ⟨hform, hder ▸ hmem, ?_⟩
  have hs : (⟨leftFamily (γ 0) (curveTangent γ), hder ▸ hmem⟩ :
      tangentSpace (restrictToPositiveEdges '' 𝒳) (restrictToPositiveEdges (γ 0))) =
        ⟨_, hmem⟩ :=
    Subtype.ext hder.symm
  rw [hs, hval, hder₂, hmt]
private theorem leftDifferentialLinear_apply (H : Inputs)
    (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (ha : a ≤ k) (hb : b ≤ k) {𝒳 : Set (Edge L n k a → ComplexMatrix2)}
    {m : (Edge L n k a → ComplexMatrix2) → Edge L n k b → ComplexMatrix2}
    (hm : IsAnalyticFieldMap 𝒳 m)
    {U : Edge L n k a → ComplexMatrix2} (hU : U ∈ 𝒳) (B : edgeFormSpace L n k a) :
    (leftDifferentialLinear m U B : Edge L n k b → ComplexMatrix2) = leftDifferential m U B := by
  have hmU : m U ∈ fieldSpace L n k b := hm.2.1 hU
  have hf := fun B : edgeFormSpace L n k a =>
    leftDifferential_mem_and_eq H hL hn ha hb hm hU B.2
  let v : edgeFormSpace L n k a →
      tangentSpace (restrictToPositiveEdges '' 𝒳) (restrictToPositiveEdges U) :=
    fun B => ⟨leftFamily U B, (hf B).2.choose⟩
  have hval : ∀ B : edgeFormSpace L n k a, leftFamily (m U) (leftDifferential m U B) =
      tangentDifferential (restrictToPositiveEdges '' 𝒳) (restrictMap m)
        (restrictToPositiveEdges U) (v B) :=
    fun B => (hf B).2.choose_spec.symm
  have hadd : ∀ B B' : edgeFormSpace L n k a, v (B + B') = v B + v B' :=
    fun B B' => Subtype.ext (map_add (leftFamily U) _ _)
  have hsmul : ∀ (r : ℝ) (B : edgeFormSpace L n k a), v (r • B) = r • v B :=
    fun r B => Subtype.ext (map_smul (leftFamily U) r _)
  let T : edgeFormSpace L n k a →ₗ[ℝ] edgeFormSpace L n k b :=
    { toFun := fun B => ⟨leftDifferential m U B, (hf B).1⟩
      map_add' := fun B B' => Subtype.ext (leftFamily_injective hmU (hf _).1
        (add_mem (hf B).1 (hf B').1) (by
          show leftFamily (m U) (leftDifferential m U (B + B' : edgeFormSpace L n k a)) =
            leftFamily (m U) (leftDifferential m U B + leftDifferential m U B')
          rw [hval, hadd, map_add, map_add (leftFamily (m U)), hval, hval]))
      map_smul' := fun r B => Subtype.ext (leftFamily_injective hmU (hf _).1
        (Submodule.smul_mem _ r (hf B).1) (by
          show leftFamily (m U) (leftDifferential m U (r • B : edgeFormSpace L n k a)) =
            leftFamily (m U) (r • leftDifferential m U B)
          rw [hval, hsmul, map_smul, map_smul (leftFamily (m U)), hval])) }
  exact Classical.epsilon_spec (p := fun T : edgeFormSpace L n k a →ₗ[ℝ] edgeFormSpace L n k b =>
    ∀ B : edgeFormSpace L n k a, (T B : Edge L n k b → ComplexMatrix2) = leftDifferential m U B)
    ⟨T, fun B => rfl⟩ B
private theorem restrictMap_isSmoothSubmersion (H : Inputs)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (ha : a ≤ k) (hb : b ≤ k) {𝒳 : Set (Edge L n k a → ComplexMatrix2)}
    {𝒴 : Set (Edge L n k b → ComplexMatrix2)}
    (h𝒴 : IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒴)
    {m : (Edge L n k a → ComplexMatrix2) → Edge L n k b → ComplexMatrix2}
    (hm : IsAnalyticFieldMap 𝒳 m)
    (hmaps : MapsTo m 𝒳 𝒴) (honto : ∀ V ∈ 𝒳, HasSurjectiveDifferential m V) :
    IsSmoothSubmersion (restrictToPositiveEdges '' 𝒳) (restrictToPositiveEdges '' 𝒴)
      (restrictMap m) := by
  have h𝒳 := hm.1
  refine ⟨?_, isSmoothOnOpen_restrict h𝒳 h𝒳 subset_rfl
    (contDiffOn_restrictMap H.charts H.edges hL hn ha hb hm), ?_⟩
  · rintro _ ⟨U, hU, rfl⟩
    rw [restrictMap_restrict (h𝒳.1 hU)]
    exact ⟨_, hmaps hU, rfl⟩
  · rintro _ ⟨U, hU, rfl⟩
    rw [restrictMap_restrict (h𝒳.1 hU)]
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      obtain ⟨B, hB, e⟩ :=
        (mem_tangentSpace_iff H.smooth H.charts H.edges H.left hL hn ha h𝒳 hU v.1).1 v.2
      obtain ⟨hf, h, hd⟩ := leftDifferential_mem_and_eq H hL hn ha hb hm hU hB
      have hv : v = ⟨leftFamily U B, h⟩ := Subtype.ext e.symm
      rw [hv]
      show tangentDifferential _ _ _ _ ∈ _
      rw [hd]
      exact (mem_tangentSpace_iff H.smooth H.charts H.edges H.left hL hn hb h𝒴 (hmaps hU) _).2
        ⟨_, hf, rfl⟩
    · intro Y hY
      obtain ⟨B', hB', e⟩ := (mem_tangentSpace_iff H.smooth H.charts H.edges H.left hL hn hb h𝒴
        (hmaps hU) Y).1 hY
      obtain ⟨B, hB, eB⟩ := honto U hU B' hB'
      obtain ⟨hf, h, hd⟩ := leftDifferential_mem_and_eq H hL hn ha hb hm hU hB
      exact ⟨⟨leftFamily U B, h⟩, by
        show tangentDifferential _ _ _ _ = _
        rw [hd, eB, e]⟩
private theorem image_fibreWithin {𝒳 : Set (Edge L n k a → ComplexMatrix2)}
    {m : (Edge L n k a → ComplexMatrix2) → Edge L n k b → ComplexMatrix2}
    {r : (PositiveEdge L n k a → ComplexMatrix2) → PositiveEdge L n k b → ComplexMatrix2}
    (hr : ∀ V ∈ 𝒳, r (restrictToPositiveEdges V) = restrictToPositiveEdges (m V))
    (hmaps : MapsTo m 𝒳 (fieldSpace L n k b)) {y : Edge L n k b → ComplexMatrix2}
    (hy : y ∈ fieldSpace L n k b) :
    restrictToPositiveEdges '' fibreWithin 𝒳 m y =
      fiber (restrictToPositiveEdges '' 𝒳) r (restrictToPositiveEdges y) := by
  ext w
  constructor
  · rintro ⟨V, ⟨hV, e⟩, rfl⟩
    exact ⟨⟨V, hV, rfl⟩, by rw [hr V hV, e]⟩
  · rintro ⟨⟨V, hV, rfl⟩, e⟩
    refine ⟨V, ⟨hV, ?_⟩, rfl⟩
    rw [hr V hV] at e
    have := congrArg fieldOfPositiveValues e
    rwa [field_restrict (hmaps hV), field_restrict hy] at this
private theorem mem_tangentSpan_fibre_iff (H : Inputs) (hFib : SubmersionFibresAreSubmanifolds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (ha : a ≤ k) (hb : b ≤ k)
    {𝒳 : Set (Edge L n k a → ComplexMatrix2)}
    {m : (Edge L n k a → ComplexMatrix2) → Edge L n k b → ComplexMatrix2}
    (hm : IsAnalyticFieldMap 𝒳 m) (honto : ∀ V ∈ 𝒳, HasSurjectiveDifferential m V)
    {x : Edge L n k a → ComplexMatrix2} (hx : x ∈ 𝒳) {W : Edge L n k b → ComplexMatrix2}
    (hW : m x = W) (Y : PositiveEdge L n k a → ComplexMatrix2) :
    Y ∈ (vectorCurveData (PositiveEdge L n k a → ComplexMatrix2)).tangentSpan
        (restrictToPositiveEdges '' fibreWithin 𝒳 m W) (restrictToPositiveEdges x) ↔
      ∃ v : LinearMap.ker (leftDifferentialLinear m x), leftFamily x v.1.1 = Y := by
  have hN : fibreWithin 𝒳 m W ⊆ fieldSpace L n k a := fun V hV => hm.1.1 hV.1
  have hfib := (hFib L n k a b hL hn ha hb 𝒳 m hm honto W).2 x hx hW
  rw [← map_tangentSpan hN (hm.1.1 hx), Submodule.mem_map]
  constructor
  · rintro ⟨B, hB, rfl⟩
    obtain ⟨hBf, h0⟩ := (hfib B).1 hB
    refine ⟨⟨⟨B, hBf⟩, ?_⟩, rfl⟩
    rw [LinearMap.mem_ker]
    refine Subtype.ext ?_
    rw [leftDifferentialLinear_apply H hL hn ha hb hm hx]
    exact h0
  · rintro ⟨v, rfl⟩
    refine ⟨v.1.1, (hfib _).2 ⟨v.1.2, ?_⟩, rfl⟩
    rw [← leftDifferentialLinear_apply H hL hn ha hb hm hx v.1]
    exact congrArg Subtype.val (LinearMap.mem_ker.1 v.2)
private theorem hessianForm_transport {X T S : Type} [AddCommGroup T] [Module ℝ T]
    [AddCommGroup S] [Module ℝ S] (R : Geometry.CurveData X T) {N : Set X} {F : X → ℝ} {x : X}
    (e : S ≃ₗ[ℝ] R.tangentSpan N x) (ι : S → T) (hι : ∀ v, ι v = e v)
    (hH : R.HasUniqueHessianAt N F x) :
    R.hessianForm ι N F x =
      (R.restrictedHessian N F x).comp (e : S →ₗ[ℝ] R.tangentSpan N x) := by
  obtain ⟨Q, hQ, hu⟩ := id hH
  have hQ₀ : R.IsHessianFormAt Subtype.val N F x (R.restrictedHessian N F x) :=
    Classical.epsilon_spec (p := fun Q : QuadraticForm ℝ (R.tangentSpan N x) =>
      R.IsHessianFormAt Subtype.val N F x Q) ⟨Q, hQ⟩
  have h1 : R.IsHessianFormAt ι N F x
      ((R.restrictedHessian N F x).comp (e : S →ₗ[ℝ] R.tangentSpan N x)) :=
    fun I γ v t₁ t₂ t₃ t₄ => hQ₀ I γ (e v) t₁ t₂ t₃ (t₄.trans (hι v))
  have h2 : R.IsHessianFormAt ι N F x (R.hessianForm ι N F x) :=
    Classical.epsilon_spec (p := fun Q : QuadraticForm ℝ S => R.IsHessianFormAt ι N F x Q)
      ⟨_, h1⟩
  have h3 : R.IsHessianFormAt Subtype.val N F x
      ((R.hessianForm ι N F x).comp (e.symm : R.tangentSpan N x →ₗ[ℝ] S)) :=
    fun I γ u t₁ t₂ t₃ t₄ => h2 I γ (e.symm u) t₁ t₂ t₃ (by rw [hι]; simpa using t₄)
  have h4 := (hu _ h3).trans (hu _ hQ₀).symm
  ext v
  have := congrArg (fun Q' : QuadraticForm ℝ (R.tangentSpan N x) => Q' (e v)) h4
  simpa using this
private theorem fibreHessian_eq_comp (M : edgeFormSpace L n k a →ₗ[ℝ] edgeFormSpace L n k b)
    {N : Set (Edge L n k a → ComplexMatrix2)} (hN : N ⊆ fieldSpace L n k a)
    {F : (Edge L n k a → ComplexMatrix2) → ℝ} {F' : (PositiveEdge L n k a → ComplexMatrix2) → ℝ}
    (hF : ∀ V ∈ N, F' (restrictToPositiveEdges V) = F V) {x : Edge L n k a → ComplexMatrix2}
    (hx : x ∈ fieldSpace L n k a)
    (htan : ∀ Y, Y ∈ (vectorCurveData (PositiveEdge L n k a → ComplexMatrix2)).tangentSpan
        (restrictToPositiveEdges '' N) (restrictToPositiveEdges x) ↔
      ∃ v : LinearMap.ker M, leftFamily x v.1.1 = Y)
    (hH : (vectorCurveData (PositiveEdge L n k a → ComplexMatrix2)).HasUniqueHessianAt
      (restrictToPositiveEdges '' N) F' (restrictToPositiveEdges x)) :
    ∃ e : LinearMap.ker M ≃ₗ[ℝ] (vectorCurveData (PositiveEdge L n k a → ComplexMatrix2)).tangentSpan
        (restrictToPositiveEdges '' N) (restrictToPositiveEdges x),
      (∀ v, (e v : PositiveEdge L n k a → ComplexMatrix2) = leftFamily x v.1.1) ∧
      fibreHessianOnKernel M N F x =
        ((vectorCurveData (PositiveEdge L n k a → ComplexMatrix2)).restrictedHessian
          (restrictToPositiveEdges '' N) F' (restrictToPositiveEdges x)).comp (e : _ →ₗ[ℝ] _) := by
  let g : LinearMap.ker M →ₗ[ℝ] (vectorCurveData (PositiveEdge L n k a → ComplexMatrix2)).tangentSpan
      (restrictToPositiveEdges '' N) (restrictToPositiveEdges x) :=
    LinearMap.codRestrict _ ((leftFamily x).comp ((edgeFormSpace L n k a).subtype.comp
      (LinearMap.ker M).subtype)) fun v => (htan _).2 ⟨v, rfl⟩
  have hbij : Function.Bijective g := by
    constructor
    · intro v v' h
      have h' : leftFamily x v.1.1 = leftFamily x v'.1.1 := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext (leftFamily_injective hx v.1.2 v'.1.2 h'))
    · intro Y
      obtain ⟨v, e⟩ := (htan Y.1).1 Y.2
      exact ⟨v, Subtype.ext e⟩
  let e := LinearEquiv.ofBijective g hbij
  refine ⟨e, fun v => rfl, ?_⟩
  unfold fibreHessianOnKernel
  rw [hessianForm_eq hN hF hx (fun B : LinearMap.ker M => B.1.1) fun v => v.1.2]
  exact hessianForm_transport (S := LinearMap.ker M) _ e _ (fun v => rfl) hH
private theorem posDef_comp_equiv {V W : Type} [AddCommMonoid V] [Module ℝ V] [AddCommMonoid W]
    [Module ℝ W] (e : V ≃ₗ[ℝ] W) (Q : QuadraticForm ℝ W) :
    (Q.comp (e : V →ₗ[ℝ] W)).PosDef ↔ Q.PosDef := by
  constructor
  · intro h w hw
    have := h (e.symm w) (by simpa using hw)
    simpa using this
  · intro h v hv
    exact h (e v) (by simpa using hv)
end LeftDifferentials
section GaussianFactors
private theorem gaussian_mul_of_cores (hG : TwoStageConstraint.GaussianProduct)
    {V₁ V₂ V₃ : Type}
    [AddCommGroup V₁] [Module ℝ V₁] [FiniteDimensional ℝ V₁] [AddCommGroup V₂] [Module ℝ V₂]
    [FiniteDimensional ℝ V₂] [AddCommGroup V₃] [Module ℝ V₃] [FiniteDimensional ℝ V₃]
    (c₁ : InnerProductSpace.Core ℝ V₁) (c₂ : InnerProductSpace.Core ℝ V₂)
    (c₃ : InnerProductSpace.Core ℝ V₃) (M : V₁ →ₗ[ℝ] V₂) (N : V₂ →ₗ[ℝ] V₃)
    (T : QuadraticForm ℝ (LinearMap.ker (N ∘ₗ M))) (T₁ : QuadraticForm ℝ (LinearMap.ker M))
    (T₂ : QuadraticForm ℝ (LinearMap.ker N)) (hM : Function.Surjective M)
    (hN : Function.Surjective N) (hT : T.PosDef)
    (h₁ : T₁ = T.comp (Submodule.inclusion (LinearMap.ker_le_ker_comp M N)))
    (h₂ : ∀ ζ : LinearMap.ker N,
      IsLeast {t | ∃ ξ : LinearMap.ker (N ∘ₗ M), M (ξ : V₁) = (ζ : V₂) ∧ T ξ = t} (T₂ ζ)) :
    GaussianConstraint.constrainedGaussianNumberOfCores c₁ c₃ (N ∘ₗ M) T =
      GaussianConstraint.constrainedGaussianNumberOfCores c₁ c₂ M T₁ *
        GaussianConstraint.constrainedGaussianNumberOfCores c₂ c₃ N T₂ := by
  let _ := c₁.toNormedAddCommGroup
  let _ := InnerProductSpace.ofCore c₁.toCore
  let _ := c₂.toNormedAddCommGroup
  let _ := InnerProductSpace.ofCore c₂.toCore
  let _ := c₃.toNormedAddCommGroup
  let _ := InnerProductSpace.ofCore c₃.toCore
  obtain ⟨T₂', -, hl, he⟩ := hG V₁ V₂ V₃ M N T hM hN hT
  have e₂ : T₂' = T₂ := by
    ext ζ
    exact (hl ζ).unique (h₂ ζ)
  subst e₂
  subst h₁
  exact he
end GaussianFactors
section Composite
variable {L n k a b c : ℕ} [i₁ : Fintype (PositiveEdge L n k a)]
  [i₂ : Fintype (PositiveEdge L n k b)] [i₃ : Fintype (PositiveEdge L n k c)]
private theorem restrict_injOn {V W : Edge L n k a → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k a) (hW : W ∈ fieldSpace L n k a)
    (h : restrictToPositiveEdges V = restrictToPositiveEdges W) : V = W := by
  rw [← field_restrict hV, h, field_restrict hW]
private theorem curveTangent_eq_zero_of_const {γ : ℝ → Edge L n k c → ComplexMatrix2} {I : Set ℝ}
    (hI : IsOpenIntervalAroundZero I) {p : Edge L n k c → ComplexMatrix2}
    (h : ∀ t ∈ I, γ t = p) : curveTangent γ = 0 := by
  have hd : ∀ b, deriv (fun t => γ t b) 0 = 0 := by
    intro b
    have : (fun t => γ t b) =ᶠ[𝓝 0] fun _ => p b := by
      filter_upwards [hI.1.mem_nhds hI.2.2] with t ht
      rw [h t ht]
    rw [this.deriv_eq]
    simp
  funext b
  simp [curveTangent, extendOddly, hd]
private theorem twoStage_onLevels (H : Inputs) (hTwo : TwoStageConstraint.Claim)
    (hY : RestrictionHessian.Statement) (hCo : Manifolds.CoordinatesOfTwoSubmersions)
    (hNb : FibreNeighbourhoodsOfSteps)
    (hChain : FiniteLevelChainRule.Statement)
    (hFib : SubmersionFibresAreSubmanifolds)
    (hEa : EdgeFormsEuclidean L n k a) (hEb : EdgeFormsEuclidean L n k b)
    (hEc : EdgeFormsEuclidean L n k c)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (ha : a ≤ k) (hb : b ≤ k)
    (hc : c ≤ k)
    {𝒳 : Set (Edge L n k a → ComplexMatrix2)} {𝒴 𝒰 : Set (Edge L n k b → ComplexMatrix2)}
    {m : (Edge L n k a → ComplexMatrix2) → Edge L n k b → ComplexMatrix2}
    {q : (Edge L n k b → ComplexMatrix2) → Edge L n k c → ComplexMatrix2}
    {F : (Edge L n k a → ComplexMatrix2) → ℝ}
    {f g : (Edge L n k b → ComplexMatrix2) → ℝ}
    {x : (Edge L n k b → ComplexMatrix2) → Edge L n k a → ComplexMatrix2}
    {y₀ : Edge L n k b → ComplexMatrix2} (hD : TwoStageData 𝒳 𝒴 𝒰 m q F f g x) (hy₀ : y₀ ∈ 𝒰)
    (hcrit : (fieldCurveData L n k b).IsCriticalOn
      (fibreWithin 𝒴 q (q y₀) ∩ 𝒰) (fun y => f y + g y) y₀)
    (hpos : (fibreHessianOnKernel (leftDifferentialLinear q y₀)
      (fibreWithin 𝒴 q (q y₀) ∩ 𝒰) (fun y => f y + g y) y₀).PosDef) :
    (fieldCurveData L n k a).IsCriticalOn (fibreWithin 𝒳 (q ∘ m) (q y₀))
        (fun U => F U + g (m U)) (x y₀) ∧
      (fibreHessianOnKernel (leftDifferentialLinear q y₀ ∘ₗ leftDifferentialLinear m (x y₀))
        (fibreWithin 𝒳 (q ∘ m) (q y₀)) (fun U => F U + g (m U)) (x y₀)).PosDef ∧
      constrainedGaussianOnEdgeForms
        (leftDifferentialLinear q y₀ ∘ₗ leftDifferentialLinear m (x y₀))
        (fibreHessianOnKernel (leftDifferentialLinear q y₀ ∘ₗ leftDifferentialLinear m (x y₀))
          (fibreWithin 𝒳 (q ∘ m) (q y₀)) (fun U => F U + g (m U)) (x y₀)) =
      constrainedGaussianOnEdgeForms (leftDifferentialLinear m (x y₀))
        (fibreHessianOnKernel (leftDifferentialLinear m (x y₀))
          (fibreWithin 𝒳 m y₀) F (x y₀)) *
      constrainedGaussianOnEdgeForms (leftDifferentialLinear q y₀)
        (fibreHessianOnKernel (leftDifferentialLinear q y₀)
          (fibreWithin 𝒴 q (q y₀) ∩ 𝒰) (fun y => f y + g y) y₀) := by
  have hm := hD.analytic_first
  have hq := hD.analytic_second
  have hXo := hm.1
  have hYo := hq.1
  have hUo := hD.analytic_section.1
  have hZo := fieldSpace_isOpen (a := c) H.left hL hn hc
  have hXc : 𝒳 ⊆ fieldSpace L n k a := hXo.1
  have hYc : 𝒴 ⊆ fieldSpace L n k b := hYo.1
  have hUc : 𝒰 ⊆ fieldSpace L n k b := hUo.1
  have hmC : MapsTo m 𝒳 (fieldSpace L n k b) := hm.2.1
  have hqC : MapsTo q 𝒴 (fieldSpace L n k c) := hq.2.1
  have hmanX := isChartedSubset_image H.smooth H.charts H.edges hL hn ha hXo
  have hmanY := isChartedSubset_image H.smooth H.charts H.edges hL hn hb hYo
  have hmanU := isChartedSubset_image H.smooth H.charts H.edges hL hn hb hUo
  have hmanZ := isChartedSubset_image H.smooth H.charts H.edges hL hn hc hZo
  have sm₁ := restrictMap_isSmoothSubmersion H hL hn ha hb hYo hm hD.mapsTo hD.surjective_first
  have sm₂ := restrictMap_isSmoothSubmersion H hL hn hb hc hZo hq hq.2.1 hD.surjective_second
  have hF' : IsSmoothOnOpen (restrictToPositiveEdges '' 𝒳) (restrictToPositiveEdges '' 𝒳)
      (fun w => F (fieldOfPositiveValues w)) := isSmoothOnOpen_restrict hXo hXo subset_rfl
    (contDiffOn_restrictFunction H.charts H.edges hL hn ha hD.analytic_fn)
  have hg' : IsSmoothOnOpen (restrictToPositiveEdges '' 𝒴) (restrictToPositiveEdges '' 𝒴)
      (fun w => g (fieldOfPositiveValues w)) := isSmoothOnOpen_restrict hYo hYo subset_rfl
    (contDiffOn_restrictFunction H.charts H.edges hL hn hb hD.analytic_add)
  have hx' : IsSmoothOnOpen (restrictToPositiveEdges '' 𝒴) (restrictToPositiveEdges '' 𝒰)
      (restrictMap x) :=
    isSmoothOnOpen_restrict hYo hUo hD.subset
      (contDiffOn_restrictMap H.charts H.edges hL hn hb ha hD.analytic_section)
  have hxmaps : MapsTo (restrictMap x) (restrictToPositiveEdges '' 𝒰)
      (restrictToPositiveEdges '' 𝒳) := by
    rintro _ ⟨v, hv, rfl⟩
    rw [restrictMap_restrict (hUc hv)]
    exact ⟨_, hD.section_mapsTo hv, rfl⟩
  have hsec : ∀ y ∈ restrictToPositiveEdges '' 𝒰, restrictMap m (restrictMap x y) = y := by
    rintro _ ⟨v, hv, rfl⟩
    rw [restrictMap_restrict (hUc hv), restrictMap_restrict (hXc (hD.section_mapsTo hv)),
      hD.section_right_inv v hv]
  have himg₁ : ∀ {y}, y ∈ fieldSpace L n k b →
      restrictToPositiveEdges '' fibreWithin 𝒳 m y =
        fiber (restrictToPositiveEdges '' 𝒳) (restrictMap m) (restrictToPositiveEdges y) :=
    fun hy => image_fibreWithin (fun V hV => restrictMap_restrict (hXc hV)) hmC hy
  have himg₂ : ∀ {y}, y ∈ fieldSpace L n k c →
      restrictToPositiveEdges '' fibreWithin 𝒴 q y =
        fiber (restrictToPositiveEdges '' 𝒴) (restrictMap q) (restrictToPositiveEdges y) :=
    fun hy => image_fibreWithin (fun V hV => restrictMap_restrict (hYc hV)) hqC hy
  have hman₁ : ∀ {y}, y ∈ fieldSpace L n k b →
      IsChartedSubset (restrictToPositiveEdges '' fibreWithin 𝒳 m y) := by
    intro y hy
    rw [himg₁ hy]
    exact hCo.1 _ _ _ _ _ _ hmanX hmanY sm₁
  have hman₂ : ∀ {y}, y ∈ fieldSpace L n k c →
      IsChartedSubset (restrictToPositiveEdges '' fibreWithin 𝒴 q y) := by
    intro y hy
    rw [himg₂ hy]
    exact hCo.1 _ _ _ _ _ _ hmanY hmanZ sm₂
  have hFa : ∀ {N : Set (Edge L n k a → ComplexMatrix2)}, N ⊆ fieldSpace L n k a → ∀ V ∈ N,
      F (fieldOfPositiveValues (restrictToPositiveEdges V)) = F V := by
    intro N hN V hV
    rw [field_restrict (hN hV)]
  have hfirst : ∀ v ∈ 𝒰,
      (vectorCurveData (PositiveEdge L n k a → ComplexMatrix2)).IsCriticalOn
        (restrictToPositiveEdges '' fibreWithin 𝒳 m v) (fun w => F (fieldOfPositiveValues w))
        (restrictToPositiveEdges (x v)) ∧
      ∃ e : LinearMap.ker (leftDifferentialLinear m (x v)) ≃ₗ[ℝ]
          (vectorCurveData (PositiveEdge L n k a → ComplexMatrix2)).tangentSpan
            (restrictToPositiveEdges '' fibreWithin 𝒳 m v) (restrictToPositiveEdges (x v)),
        (∀ u, (e u : PositiveEdge L n k a → ComplexMatrix2) = leftFamily (x v) u.1.1) ∧
        fibreHessianOnKernel (leftDifferentialLinear m (x v)) (fibreWithin 𝒳 m v) F (x v) =
          ((vectorCurveData (PositiveEdge L n k a → ComplexMatrix2)).restrictedHessian
            (restrictToPositiveEdges '' fibreWithin 𝒳 m v)
            (fun w => F (fieldOfPositiveValues w)) (restrictToPositiveEdges (x v))).comp
              (e : _ →ₗ[ℝ] _) := by
    intro v hv
    have hvc := hUc hv
    have hN : fibreWithin 𝒳 m v ⊆ fieldSpace L n k a := fun V hV => hXc hV.1
    have hxv := hXc (hD.section_mapsTo hv)
    have hcr := (isCriticalOn_iff hN (F' := fun w => F (fieldOfPositiveValues w)) (hFa hN)
      hxv).1 (hD.critical v hv)
    refine ⟨hcr, ?_⟩
    have hsub : restrictToPositiveEdges '' fibreWithin 𝒳 m v ⊆ restrictToPositiveEdges '' 𝒳 :=
      image_mono fun V hV => hV.1
    have hH := ((hY.1 _ _ _ _ hmanX ⟨hsub, hman₁ hvc⟩ (isC2_of_smooth hF')).2.2.1 _ hcr)
    exact fibreHessian_eq_comp _ hN (F' := fun w => F (fieldOfPositiveValues w)) (hFa hN) hxv
      (mem_tangentSpan_fibre_iff H hFib hL hn ha hb hm hD.surjective_first
        (hD.section_mapsTo hv) (hD.section_right_inv v hv)) hH
  have hfib : ∀ y ∈ restrictToPositiveEdges '' 𝒰,
      (vectorCurveData (PositiveEdge L n k a → ComplexMatrix2)).IsCriticalPosDefOn
        (fiber (restrictToPositiveEdges '' 𝒳) (restrictMap m) y)
        (fun w => F (fieldOfPositiveValues w)) (restrictMap x y) := by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨hcr, e, -, hh⟩ := hfirst v hv
    have hp := hD.posDef v hv
    rw [hh] at hp
    rw [restrictMap_restrict (hUc hv), ← himg₁ (hUc hv)]
    exact ⟨hcr, (posDef_comp_equiv e _).1 hp⟩
  have hy₀c := hUc hy₀
  have hx₀ := hD.section_mapsTo hy₀
  have hx₀c := hXc hx₀
  have hy₀Y := hD.subset hy₀
  have hqy := hqC hy₀Y
  have hm₀ : m (x y₀) = y₀ := hD.section_right_inv y₀ hy₀
  have hNQ : fibreWithin 𝒴 q (q y₀) ∩ 𝒰 ⊆ fieldSpace L n k b :=
    fun V hV => hUc hV.2
  have himgQ : restrictToPositiveEdges '' (fibreWithin 𝒴 q (q y₀) ∩ 𝒰) =
      fiber (restrictToPositiveEdges '' 𝒴) (restrictMap q) (restrictToPositiveEdges (q y₀)) ∩
        restrictToPositiveEdges '' 𝒰 := by
    rw [image_inter_on fun V hV W hW h => restrict_injOn (hUc hV) (hYc hW.1) h, himg₂ hqy]
  have hfgA : ∀ V ∈ fibreWithin 𝒴 q (q y₀) ∩ 𝒰,
      (fun y => F (fieldOfPositiveValues (restrictMap x y)) + g (fieldOfPositiveValues y))
        (restrictToPositiveEdges V) = f V + g V := by
    intro V hV
    show F (fieldOfPositiveValues (restrictMap x (restrictToPositiveEdges V))) +
      g (fieldOfPositiveValues (restrictToPositiveEdges V)) = _
    rw [restrictMap_restrict (hUc hV.2), field_restrict (hXc (hD.section_mapsTo hV.2)),
      field_restrict (hUc hV.2), hD.value_eq V hV.2]
  have hcrQ := (isCriticalOn_iff hNQ
    (F' := fun y => F (fieldOfPositiveValues (restrictMap x y)) + g (fieldOfPositiveValues y))
    hfgA hy₀c).1 hcrit
  have hopenQ : ComplexMatrix2.IsRelativelyOpen (restrictToPositiveEdges '' fibreWithin 𝒴 q (q y₀))
      (restrictToPositiveEdges '' (fibreWithin 𝒴 q (q y₀) ∩ 𝒰)) := by
    obtain ⟨O, hO, e⟩ := hUo.2
    refine ⟨O, hO, ?_⟩
    ext w
    constructor
    · rintro ⟨V, hV, rfl⟩
      have hi : restrictToPositiveEdges V ∈ restrictToPositiveEdges '' 𝒰 := ⟨V, hV.2, rfl⟩
      rw [e] at hi
      exact ⟨hi.1, ⟨V, hV.1, rfl⟩⟩
    · rintro ⟨h₁, ⟨V, hV, rfl⟩⟩
      have hVc := hYc hV.1
      have hi : restrictToPositiveEdges V ∈ restrictToPositiveEdges '' 𝒰 := by
        rw [e]
        exact ⟨h₁, fun c => hVc.1 c (mem_univ _)⟩
      obtain ⟨W, hW, eW⟩ := hi
      have hWV := restrict_injOn (hUc hW) hVc eW
      exact ⟨V, ⟨hV, hWV ▸ hW⟩, rfl⟩
  have hnb := (hNb.1 (PositiveEdge L n k b → ComplexMatrix2) (PositiveEdge L n k b → ComplexMatrix2)
    (vectorCurveData (PositiveEdge L n k b → ComplexMatrix2)) (hNb.2.1 _) _ _ _ hopenQ
    (restrictToPositiveEdges y₀)).2 hcrQ
  have htanQ : ∀ Y, Y ∈ (vectorCurveData (PositiveEdge L n k b → ComplexMatrix2)).tangentSpan
      (restrictToPositiveEdges '' (fibreWithin 𝒴 q (q y₀) ∩ 𝒰)) (restrictToPositiveEdges y₀) ↔
      ∃ v : LinearMap.ker (leftDifferentialLinear q y₀), leftFamily y₀ v.1.1 = Y := fun Y => by
    rw [hnb.1]
    exact mem_tangentSpan_fibre_iff H hFib hL hn hb hc hq hD.surjective_second hy₀Y rfl Y
  have hmanQ := H.smooth.2.2.2.2.1 _ _ _ (hman₂ hqy) hopenQ
  have hC2 : IsC2OnCharted (restrictToPositiveEdges '' 𝒰)
      (fun y => F (fieldOfPositiveValues (restrictMap x y)) + g (fieldOfPositiveValues y)) := by
    intro ch
    let cY := chartOfRelOpen hx'.1 ch
    have h1 : ContDiffOn ℝ ∞ (restrictMap x ∘ ch.param) ch.source :=
      (hx'.2 cY).mono fun u hu => ⟨hu, param_mem ch hu⟩
    have h2 := contDiffOn_comp_smooth H.smooth hmanX hF' ch.isOpen_source h1
      fun u hu => hxmaps (param_mem ch hu)
    have h3 : ContDiffOn ℝ ∞ ((fun w => g (fieldOfPositiveValues w)) ∘ ch.param)
        ch.source := (hg'.2 cY).mono fun u hu =>
      ⟨hu, image_mono hD.subset (param_mem ch hu)⟩
    exact (h2.add h3).of_le (WithTop.coe_le_coe.2 le_top)
  have hH₂ := (hY.1 _ _ _ _ hmanU ⟨image_mono inter_subset_right, hmanQ⟩ hC2).2.2.1 _ hcrQ
  obtain ⟨e₂, he₂, hh₂⟩ := fibreHessian_eq_comp (leftDifferentialLinear q y₀) hNQ
    (F' := fun y => F (fieldOfPositiveValues (restrictMap x y)) + g (fieldOfPositiveValues y))
    hfgA hy₀c htanQ hH₂
  have hposQ := hpos
  rw [hh₂] at hposQ
  have hout := hTwo.2 (PositiveEdge L n k a → ComplexMatrix2) (PositiveEdge L n k b → ComplexMatrix2)
    (PositiveEdge L n k c → ComplexMatrix2) _ _ _ (restrictMap m) (restrictMap q)
    (fun w => F (fieldOfPositiveValues w)) (fun w => g (fieldOfPositiveValues w))
    (restrictToPositiveEdges '' 𝒰) (restrictMap x) (restrictToPositiveEdges y₀) hmanX hmanY
    hmanZ sm₁ sm₂ hF' hg' ⟨y₀, hy₀, rfl⟩ hx' hxmaps hsec hfib (by
      rw [restrictMap_restrict hy₀c, ← himgQ]
      exact ⟨hcrQ, (posDef_comp_equiv e₂ _).1 hposQ⟩)
  have himgP : restrictToPositiveEdges '' fibreWithin 𝒳 (q ∘ m) (q y₀) =
      fiber (restrictToPositiveEdges '' 𝒳) (restrictMap q ∘ restrictMap m)
        (restrictToPositiveEdges (q y₀)) :=
    image_fibreWithin (fun V hV => by
      show restrictMap q (restrictMap m (restrictToPositiveEdges V)) = _
      rw [restrictMap_restrict (hXc hV), restrictMap_restrict (hYc (hD.mapsTo hV))])
      (fun V hV => hqC (hD.mapsTo hV)) hqy
  dsimp only at hout
  rw [restrictMap_restrict (m := q) hy₀c, restrictMap_restrict (m := x) hy₀c, ← himgP,
    ← himg₁ hy₀c, ← himgQ] at hout
  obtain ⟨hcrP, hTpos, ⟨hle, hres⟩, hleast⟩ := hout
  have hNP : fibreWithin 𝒳 (q ∘ m) (q y₀) ⊆ fieldSpace L n k a :=
    fun V hV => hXc hV.1
  have hGa : ∀ V ∈ fibreWithin 𝒳 (q ∘ m) (q y₀),
      (fun p => F (fieldOfPositiveValues p) + g (fieldOfPositiveValues (restrictMap m p)))
        (restrictToPositiveEdges V) = F V + g (m V) := by
    intro V hV
    show F (fieldOfPositiveValues (restrictToPositiveEdges V)) +
      g (fieldOfPositiveValues (restrictMap m (restrictToPositiveEdges V))) = _
    rw [field_restrict (hXc hV.1), restrictMap_restrict (hXc hV.1),
      field_restrict (hmC hV.1)]
  have happM := leftDifferentialLinear_apply H hL hn ha hb hm hx₀
  have happN := leftDifferentialLinear_apply H hL hn hb hc hq hy₀Y
  obtain ⟨hcr₁, e₁, he₁, hh₁⟩ := hfirst y₀ hy₀
  have htanP : ∀ Y, Y ∈ (vectorCurveData (PositiveEdge L n k a → ComplexMatrix2)).tangentSpan
      (restrictToPositiveEdges '' fibreWithin 𝒳 (q ∘ m) (q y₀)) (restrictToPositiveEdges (x y₀)) ↔
      ∃ v : LinearMap.ker (leftDifferentialLinear q y₀ ∘ₗ leftDifferentialLinear m (x y₀)),
        leftFamily (x y₀) v.1.1 = Y := by
    intro Y
    constructor
    · intro hYt
      rw [← map_tangentSpan hNP hx₀c, Submodule.mem_map] at hYt
      obtain ⟨B, hB, rfl⟩ := hYt
      have hK : (fieldCurveData L n k a).tangentSpan (fibreWithin 𝒳 (q ∘ m) (q y₀))
          (x y₀) ≤ (LinearMap.ker (leftDifferentialLinear q y₀ ∘ₗ
            leftDifferentialLinear m (x y₀))).map (edgeFormSpace L n k a).subtype := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨I, γ, hcv, hmp, h0, rfl⟩
        have hIn : I ∈ 𝓝 (0 : ℝ) := hcv.1.1.mem_nhds hcv.1.2.2
        have hγat : ∀ b' : Edge L n k a, b'.IsPositivelyOriented →
            DifferentiableAt ℝ (fun t => γ t b') 0 :=
          fun b' hb' => (hcv.2.2 b' hb').differentiableAt hIn
        have hform : curveTangent γ ∈ edgeFormSpace L n k a :=
          curveTangent_mem H hL hn ha (h0 ▸ hx₀c)
            (by filter_upwards [hIn] with t ht using hcv.2.1 ht) hγat
        obtain ⟨hdc, hch⟩ := (hChain L k a b c hL ha hb hc n hn).1 𝒳 𝒴 m q
          (H.differentiable L n k a b hL hn ha hb 𝒳 m hm)
          (H.differentiable L n k b c hL hn hb hc 𝒴 q hq)
        have hdom : x y₀ ∈ compositeDomain 𝒳 𝒴 m := ⟨hx₀, hD.mapsTo hx₀⟩
        obtain ⟨-, hmt⟩ := (H.curves L k a c hL ha hc n hn).1 _ (q ∘ m) hdc _ hdom I γ hcv h0
        have hzero : curveTangent (fun t => (q ∘ m) (γ t)) = 0 :=
          curveTangent_eq_zero_of_const hcv.1 fun t ht => (hmp ht).2
        have hcomp := hch _ hdom _ hform
        rw [hm₀] at hcomp
        refine ⟨⟨_, hform⟩, ?_, rfl⟩
        rw [SetLike.mem_coe, LinearMap.mem_ker]
        refine Subtype.ext ?_
        show (leftDifferentialLinear q y₀ (leftDifferentialLinear m (x y₀) ⟨_, hform⟩) :
          Edge L n k c → ComplexMatrix2) = 0
        rw [happN, happM]
        show leftDifferential q y₀ (leftDifferential m (x y₀) (curveTangent γ)) = 0
        rw [← hcomp, ← hmt, hzero]
      obtain ⟨B', hB', rfl⟩ := hK hB
      exact ⟨⟨B', hB'⟩, rfl⟩
    · rintro ⟨⟨B, hB⟩, rfl⟩
      have hNB : leftDifferentialLinear m (x y₀) B ∈
          LinearMap.ker (leftDifferentialLinear q y₀) :=
        hB
      obtain ⟨ξ, ξ', h₁, h₂, -⟩ := (hleast (e₂ ⟨_, hNB⟩)).1
      obtain ⟨B', hB', eB'⟩ :=
        (mem_tangentSpace_iff H.smooth H.charts H.edges H.left hL hn ha hXo hx₀ _).1 ξ'.2
      obtain ⟨hf, h, hd⟩ := leftDifferential_mem_and_eq H hL hn ha hb hm hx₀ hB'
      have hξ' : ξ' = ⟨leftFamily (x y₀) B', h⟩ := Subtype.ext eB'.symm
      rw [hξ', hd, he₂, hm₀] at h₂
      have hMB : leftDifferential m (x y₀) B' = (leftDifferentialLinear m (x y₀) B : _) :=
        leftFamily_injective hy₀c hf (leftDifferentialLinear m (x y₀) B).2 h₂
      have hBd : B - ⟨B', hB'⟩ ∈ LinearMap.ker (leftDifferentialLinear m (x y₀)) := by
        rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
        refine Subtype.ext ?_
        rw [happM ⟨B', hB'⟩]
        exact hMB.symm
      have hin := (mem_tangentSpan_fibre_iff H hFib hL hn ha hb hm hD.surjective_first hx₀ hm₀
        _).2 ⟨⟨_, hBd⟩, rfl⟩
      have hin₂ := hle hin
      have hξ : leftFamily (x y₀) B' ∈
          (vectorCurveData (PositiveEdge L n k a → ComplexMatrix2)).tangentSpan
            (restrictToPositiveEdges '' fibreWithin 𝒳 (q ∘ m) (q y₀))
            (restrictToPositiveEdges (x y₀)) := by
        rw [eB', h₁]
        exact ξ.2
      have hsum : leftFamily (x y₀) B.1 =
          leftFamily (x y₀) (B - ⟨B', hB'⟩).1 + leftFamily (x y₀) B' := by
        rw [← map_add]
        congr 1
        simp
      show leftFamily (x y₀) B.1 ∈ _
      rw [hsum]
      exact add_mem hin₂ hξ
  have hC2P : IsC2OnCharted (restrictToPositiveEdges '' 𝒳)
      (fun p => F (fieldOfPositiveValues p) + g (fieldOfPositiveValues (restrictMap m p))) := by
    intro ch
    have hdom : ch.source ⊆ ch.coords (restrictToPositiveEdges '' 𝒳) :=
      fun u hu => ⟨hu, param_mem ch hu⟩
    have h1 := (hF'.2 ch).mono hdom
    have h2 : ContDiffOn ℝ ∞ (restrictMap m ∘ ch.param) ch.source :=
      (sm₁.smooth.2 ch).mono hdom
    have h3 := contDiffOn_comp_smooth H.smooth hmanY hg' ch.isOpen_source h2
      fun u hu => sm₁.mapsTo (param_mem ch hu)
    exact (h1.add h3).of_le (WithTop.coe_le_coe.2 le_top)
  have hmanP : IsChartedSubset (restrictToPositiveEdges '' fibreWithin 𝒳 (q ∘ m) (q y₀)) := by
    rw [himgP]
    exact hCo.1 _ _ _ _ _ _ hmanX hmanZ (hCo.2.1 _ _ _ _ _ _ _ _ hmanX hmanY hmanZ sm₁ sm₂)
  have hHP := (hY.1 _ _ _ _ hmanX ⟨image_mono fun V hV => hV.1, hmanP⟩ hC2P).2.2.1 _ hcrP
  obtain ⟨eP, heP, hhP⟩ := fibreHessian_eq_comp
    (leftDifferentialLinear q y₀ ∘ₗ leftDifferentialLinear m (x y₀)) hNP
    (F' := fun p => F (fieldOfPositiveValues p) + g (fieldOfPositiveValues (restrictMap m p)))
    hGa hx₀c htanP hHP
  have hTK : (fibreHessianOnKernel (leftDifferentialLinear q y₀ ∘ₗ leftDifferentialLinear m (x y₀))
      (fibreWithin 𝒳 (q ∘ m) (q y₀)) (fun U => F U + g (m U)) (x y₀)).PosDef := by
    rw [hhP]
    exact (posDef_comp_equiv eP _).2 hTpos
  refine ⟨(isCriticalOn_iff hNP (F' := fun p => F (fieldOfPositiveValues p) +
    g (fieldOfPositiveValues (restrictMap m p))) hGa hx₀c).2 hcrP, hTK, ?_⟩
  have hMs : Function.Surjective (leftDifferentialLinear m (x y₀)) := by
    intro B'
    obtain ⟨B, hB, e⟩ := hD.surjective_first _ hx₀ B'.1 B'.2
    exact ⟨⟨B, hB⟩, Subtype.ext ((happM _).trans e)⟩
  have hNs : Function.Surjective (leftDifferentialLinear q y₀) := by
    intro B'
    obtain ⟨B, hB, e⟩ := hD.surjective_second _ hy₀Y B'.1 B'.2
    exact ⟨⟨B, hB⟩, Subtype.ext ((happN _).trans e)⟩
  have h₁ : fibreHessianOnKernel (leftDifferentialLinear m (x y₀)) (fibreWithin 𝒳 m y₀) F
      (x y₀) =
      (fibreHessianOnKernel (leftDifferentialLinear q y₀ ∘ₗ leftDifferentialLinear m (x y₀))
        (fibreWithin 𝒳 (q ∘ m) (q y₀)) (fun U => F U + g (m U)) (x y₀)).comp
        (Submodule.inclusion (LinearMap.ker_le_ker_comp _ _)) := by
    ext v
    rw [hh₁, hhP, ← hres]
    simp only [QuadraticMap.comp_apply]
    congr 1
    refine Subtype.ext ?_
    show _ = (eP _ : PositiveEdge L n k a → ComplexMatrix2)
    rw [heP]
    exact he₁ v
  have h₂ : ∀ ζ : LinearMap.ker (leftDifferentialLinear q y₀),
      IsLeast {t | ∃ ξ : LinearMap.ker (leftDifferentialLinear q y₀ ∘ₗ
          leftDifferentialLinear m (x y₀)),
            leftDifferentialLinear m (x y₀) (ξ : edgeFormSpace L n k a) =
              (ζ : edgeFormSpace L n k b) ∧
          fibreHessianOnKernel (leftDifferentialLinear q y₀ ∘ₗ leftDifferentialLinear m (x y₀))
            (fibreWithin 𝒳 (q ∘ m) (q y₀)) (fun U => F U + g (m U)) (x y₀) ξ = t}
        (fibreHessianOnKernel (leftDifferentialLinear q y₀)
          (fibreWithin 𝒴 q (q y₀) ∩ 𝒰) (fun y => f y + g y) y₀ ζ) := by
    intro ζ
    have hl := hleast (e₂ ζ)
    rw [hh₂]
    convert hl using 1
    ext t
    constructor
    · rintro ⟨v, hv, ht⟩
      obtain ⟨hf, h, hd⟩ := leftDifferential_mem_and_eq H hL hn ha hb hm hx₀ v.1.2
      refine ⟨eP v, ⟨leftFamily (x y₀) v.1.1, h⟩, (heP v).symm, ?_, ?_⟩
      · rw [hd, he₂, hm₀, ← happM, hv]
      · rw [hhP] at ht
        exact ht
    · rintro ⟨ξ, ξ', h₁', h₂', h₃⟩
      have hev : leftFamily (x y₀) (eP.symm ξ).1.1 = ξ := by
        rw [← heP]
        simp
      obtain ⟨hf, h, hd⟩ := leftDifferential_mem_and_eq H hL hn ha hb hm hx₀ (eP.symm ξ).1.2
      have hξ' : ξ' = ⟨leftFamily (x y₀) (eP.symm ξ).1.1, h⟩ :=
        Subtype.ext (h₁'.trans hev.symm)
      rw [hξ', hd, he₂, hm₀] at h₂'
      refine ⟨eP.symm ξ, ?_, ?_⟩
      · exact Subtype.ext ((happM _).trans (leftFamily_injective hy₀c hf ζ.1.2 h₂'))
      · rw [hhP]
        simpa using h₃
    rfl
  unfold constrainedGaussianOnEdgeForms
  rw [dif_pos (⟨hEa, hEc⟩ : EdgeFormsEuclidean L n k a ∧ EdgeFormsEuclidean L n k c),
    dif_pos (⟨hEa, hEb⟩ : EdgeFormsEuclidean L n k a ∧ EdgeFormsEuclidean L n k b),
    dif_pos (⟨hEb, hEc⟩ : EdgeFormsEuclidean L n k b ∧ EdgeFormsEuclidean L n k c)]
  have := hEa.1
  have := hEb.1
  have := hEc.1
  exact gaussian_mul_of_cores hTwo.1 _ _ _ _ _ _ _ _ hMs hNs hTK h₁ h₂
end Composite
section Conclusion
private theorem edgeFormsEuclidean_of (hSp : FiniteSideFormSpaces) {L n k j : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) :
    EdgeFormsEuclidean L n k j := by
  obtain ⟨-, hfd, -, c, hc⟩ := hSp L n k j hL hn hj
  refine ⟨hfd, c, fun B B' => ?_⟩
  rw [hc]
  simp
theorem twoStageConstraintHolds (hTwo : TwoStageConstraint.Claim)
    (hY : RestrictionHessian.Statement)
    (hCo : Manifolds.CoordinatesOfTwoSubmersions)
    (hNb : FibreNeighbourhoodsOfSteps)
    (hS : Manifolds.LocalSmoothCalculus)
    (hC : PowerExpCharts.ExpChartsStatement)
    (hE : BondSetFields.ProductStructureHolds)
    (hA : LeftChartFields.Claim)
    (hCu : FiniteLevelCurveDifferentials.Statement)
    (hChain : FiniteLevelChainRule.Statement)
    (hRD : AnalyticMapDifferentiableStatement)
    (hFib : SubmersionFibresAreSubmanifolds)
    (hSp : FiniteSideFormSpaces) : TwoStageConstraintHolds := by
  intro L n k a b c hL hn ha hb hc 𝒳 𝒴 𝒰 m q F f g x y₀ hD hy₀ hcrit hpos
  have := (hSp L n k a hL hn ha).1
  have := (hSp L n k b hL hn hb).1
  have := (hSp L n k c hL hn hc).1
  let _ : Fintype (PositiveEdge L n k a) := Fintype.ofFinite _
  let _ : Fintype (PositiveEdge L n k b) := Fintype.ofFinite _
  let _ : Fintype (PositiveEdge L n k c) := Fintype.ofFinite _
  exact twoStage_onLevels ⟨hS, hC, hE, hA, hCu, hRD⟩ hTwo hY hCo hNb hChain hFib
    (edgeFormsEuclidean_of hSp hL hn ha) (edgeFormsEuclidean_of hSp hL hn hb)
    (edgeFormsEuclidean_of hSp hL hn hc) hL hn ha hb hc hD hy₀ hcrit hpos
end Conclusion
end YangMills.Construction.Tower.TwoStageOnLevels
end
