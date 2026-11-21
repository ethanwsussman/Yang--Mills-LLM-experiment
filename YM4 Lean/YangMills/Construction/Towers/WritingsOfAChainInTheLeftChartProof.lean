import YangMills.Construction.Matrices.LinearMapsCompositesAndCoordinatesOfRealAnalyticMapsProof
import YangMills.Construction.Towers.ChainRuleAtAFiniteSideInTheLeftChartProof
import YangMills.Construction.Towers.PolydiscsOfDoubleBlocksProof
import YangMills.Construction.Lattice.ElementaryBoundsOfOneStepProof
import YangMills.Construction.Towers.ChainRuleAtTheSideInfinityInTheLeftChartProof
import YangMills.Construction.Towers.CurvesAtTheSideInfinityInTheLeftChartProof
import YangMills.Construction.Towers.MapOfAWritingNearThePointProof
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.ChainRule
open YangMills.Construction.Matrices
variable {L k j j' : ℕ}
theorem meshAt_pos (hL : Conventions.IsAdmissibleBlockingFactor L) : 0 < meshAt L k j := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.meshAt_pos <;> assumption
theorem opposite_isPositivelyOriented_iff {a : ℝ} (ha : 0 < a) (e : InfiniteLattice.Link a) :
    e.opposite.IsPositivelyOriented ↔ ¬ e.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.link_opposite_positive_iff <;> assumption
theorem inv_mem_compactGaugeGroup (M : ComplexMatrix2) (hM : M ∈ PeriodicLattice.compactGaugeGroup) :
    M⁻¹ ∈ PeriodicLattice.compactGaugeGroup ∧ M⁻¹⁻¹ = M := by apply _root_.YangMills.Construction.LocalPresentations.inv_mem_compactGaugeGroup <;> assumption
theorem inv_mem_complexGaugeGroup (M : ComplexMatrix2) (hM : M ∈ PeriodicLattice.complexGaugeGroup) :
    M⁻¹ ∈ PeriodicLattice.complexGaugeGroup ∧ M⁻¹⁻¹ = M := by apply _root_.YangMills.Construction.LocalPresentations.inv_mem_complexGaugeGroup <;> assumption
theorem expTwist_of_pos {a : ℝ} {X V : InfiniteLattice.Link a → ComplexMatrix2} {e : InfiniteLattice.Link a}
    (he : e.IsPositivelyOriented) :
    expTwist X V e = ComplexMatrix2.matExp (Complex.I • X e) * V e := if_pos he
theorem expTwist_of_not_pos {a : ℝ} {X V : InfiniteLattice.Link a → ComplexMatrix2} {e : InfiniteLattice.Link a}
    (he : ¬ e.IsPositivelyOriented) :
    expTwist X V e = (ComplexMatrix2.matExp (Complex.I • X e.opposite) * V e.opposite)⁻¹ := if_neg he
theorem extendOddly_opposite {a : ℝ} (ha : 0 < a) (g : InfiniteLattice.Link a → ComplexMatrix2)
    (e : InfiniteLattice.Link a) : extendOddly g e.opposite = -extendOddly g e := by apply _root_.YangMills.Construction.Tower.FullSpace.CurveDerivatives.extendOddly_opposite <;> assumption
def twistedValues (F : Finset (Edge L k j)) (V X : Edge L k j → ComplexMatrix2) : F → ComplexMatrix2 :=
  fun e => ComplexMatrix2.matExp (Complex.I • X e) * V e
theorem restrictToEdges_expTwist {F : Finset (Edge L k j)} (hF : IsFinitePositiveEdgeSet F)
    (V X : Edge L k j → ComplexMatrix2) : restrictToEdges F (expTwist X V) = twistedValues F V X :=
  funext fun e => expTwist_of_pos (hF.2 e e.2)
theorem twistedValues_zero (F : Finset (Edge L k j)) (V A : Edge L k j → ComplexMatrix2) :
    twistedValues F V (((0 : ℝ) : ℂ) • A) = restrictToEdges F V := by
  funext e
  simp [twistedValues, restrictToEdges]
theorem expTwist_zero {G : Set ComplexMatrix2} {V : Edge L k j → ComplexMatrix2}
    (hV : V ∈ fieldsValuedIn L k j G) (A : Edge L k j → ComplexMatrix2) :
    expTwist (((0 : ℝ) : ℂ) • A) V = V := by
  funext e
  by_cases he : e.IsPositivelyOriented
  · rw [expTwist_of_pos he]
    simp
  · rw [expTwist_of_not_pos he]
    have h := hV.2 e.opposite
    rw [InfiniteLattice.Link.opposite_opposite] at h
    simp [h]
theorem expTwist_mem {G : Set ComplexMatrix2} (ha : 0 < meshAt L k j)
    (hinv : ∀ M ∈ G, M⁻¹ ∈ G ∧ M⁻¹⁻¹ = M) {V X : Edge L k j → ComplexMatrix2}
    (hX : ∀ e : Edge L k j, e.IsPositivelyOriented → ComplexMatrix2.matExp (Complex.I • X e) * V e ∈ G) :
    expTwist X V ∈ fieldsValuedIn L k j G := by
  refine ⟨fun e => ?_, fun e => ?_⟩
  · by_cases he : e.IsPositivelyOriented
    · rw [expTwist_of_pos he]
      exact hX e he
    · rw [expTwist_of_not_pos he]
      exact (hinv _ (hX _ ((opposite_isPositivelyOriented_iff ha e).2 he))).1
  · by_cases he : e.IsPositivelyOriented
    · have hr : ¬ e.opposite.IsPositivelyOriented := fun h => (opposite_isPositivelyOriented_iff ha e).1 h he
      rw [expTwist_of_not_pos hr, expTwist_of_pos he, InfiniteLattice.Link.opposite_opposite]
    · have hr := (opposite_isPositivelyOriented_iff ha e).2 he
      rw [expTwist_of_pos hr, expTwist_of_not_pos he]
      exact ((hinv _ (hX _ hr)).2).symm
theorem replaceOn_of_pos {F : Finset (Edge L k j)} {V : Edge L k j → ComplexMatrix2}
    {y : F → ComplexMatrix2} {e : Edge L k j} (he : e.IsPositivelyOriented) :
    LocalPresentations.replaceOn F V y e = LocalPresentations.positiveEdgeValue F V y e := by
  simp [LocalPresentations.replaceOn, he]
theorem replaceOn_of_mem {F : Finset (Edge L k j)} (hF : IsFinitePositiveEdgeSet F)
    {V : Edge L k j → ComplexMatrix2} {y : F → ComplexMatrix2} {e : Edge L k j} (he : e ∈ F) :
    LocalPresentations.replaceOn F V y e = y ⟨e, he⟩ := by apply _root_.YangMills.Construction.LocalPresentations.replaceOn_of_mem <;> assumption
theorem replaceOn_of_not_mem {F : Finset (Edge L k j)} {V : Edge L k j → ComplexMatrix2}
    {y : F → ComplexMatrix2} {e : Edge L k j} (he : e.IsPositivelyOriented) (heF : e ∉ F) :
    LocalPresentations.replaceOn F V y e = V e := by apply _root_.YangMills.Construction.LocalPresentations.replaceOn_of_not_mem <;> assumption
theorem replaceOn_self {G : Set ComplexMatrix2} {F : Finset (Edge L k j)} {V : Edge L k j → ComplexMatrix2}
    (hV : V ∈ fieldsValuedIn L k j G) : LocalPresentations.replaceOn F V (restrictToEdges F V) = V := by
  have hval : ∀ e, LocalPresentations.positiveEdgeValue F V (restrictToEdges F V) e = V e := by
    intro e
    unfold LocalPresentations.positiveEdgeValue
    split_ifs with he
    · rfl
    · rfl
  funext e
  by_cases he : e.IsPositivelyOriented
  · rw [replaceOn_of_pos he, hval]
  · have h := hV.2 e.opposite
    rw [InfiniteLattice.Link.opposite_opposite] at h
    simp only [LocalPresentations.replaceOn, if_neg he, hval]
    exact h.symm
theorem hasDerivAt_expMul (X V : ComplexMatrix2) (s : ℝ) :
    HasDerivAt (fun t : ℝ => ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • X)) * V)
      (ComplexMatrix2.matExp ((s : ℂ) • (Complex.I • X)) * (Complex.I • X) * V) s := by apply _root_.YangMills.Construction.Tower.FiniteLevelChainRule.hasDerivAt_leftExpMul <;> assumption
theorem hasDerivAt_expMul_zero (X V : ComplexMatrix2) :
    HasDerivAt (fun t : ℝ => ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • X)) * V)
      (Complex.I • X * V) 0 := by
  simpa using hasDerivAt_expMul X V 0
def TwistStaysIn (L k j : ℕ) (G 𝔤 : Set ComplexMatrix2) : Prop :=
  ∀ V ∈ fieldsValuedIn L k j G, ∀ A : Edge L k j → ComplexMatrix2, IsEdgeFormIn 𝔤 A →
    ∀ e : Edge L k j, e.IsPositivelyOriented → ∀ t : ℝ,
      ComplexMatrix2.matExp (Complex.I • (((t : ℂ) • A) e)) * V e ∈ G
theorem isUnit_det_of_compact (M : ComplexMatrix2) (hM : M ∈ PeriodicLattice.compactGaugeGroup) :
    IsUnit M.det := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.det_isUnit_of_mem <;> assumption
theorem isUnit_det_of_complex (M : ComplexMatrix2) (hM : M ∈ PeriodicLattice.complexGaugeGroup) :
    IsUnit M.det := by
  have hd : M.det = 1 := hM
  rw [hd]
  exact isUnit_one
structure GroupHypotheses (L k j : ℕ) (G 𝔤 : Set ComplexMatrix2) : Prop where
  mesh_pos : 0 < meshAt L k j
  inv_mem : ∀ M ∈ G, M⁻¹ ∈ G ∧ M⁻¹⁻¹ = M
  isUnit_det : ∀ M ∈ G, IsUnit M.det
  twist : TwistStaysIn L k j G 𝔤
  logs : ∀ D : Set ℝ, IsOpenIntervalAroundZero D → LeftChartFields.CurveLogDerivative ℝ D G 𝔤
  presentations : LocalPresentations.NearPointProperties L k j G
    ({LocalPresentations.realEntryMatrices, G} : Set (Set ComplexMatrix2))
variable {G 𝔤 : Set ComplexMatrix2}
theorem isDifferentiableFieldCurve_twist (P : GroupHypotheses L k j G 𝔤) {V : Edge L k j → ComplexMatrix2}
    (hV : V ∈ fieldsValuedIn L k j G) {A : Edge L k j → ComplexMatrix2} (hA : IsEdgeFormIn 𝔤 A)
    {I : Set ℝ} (hI : IsOpenIntervalAroundZero I) :
    IsDifferentiableFieldCurve G I (fun t : ℝ => expTwist ((t : ℂ) • A) V) := by
  refine ⟨hI, fun t _ => expTwist_mem P.mesh_pos P.inv_mem fun e he =>
    P.twist V hV A hA e he t, fun e he => ?_⟩
  have h : (fun t : ℝ => expTwist ((t : ℂ) • A) V e) =
      fun t : ℝ => ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • A e)) * V e := by
    funext t
    rw [expTwist_of_pos he]
    rfl
  rw [h]
  exact fun t _ => (hasDerivAt_expMul (A e) (V e) t).differentiableAt.differentiableWithinAt
theorem curveTangent_eq {a : ℝ} (ha : 0 < a) {γ : ℝ → InfiniteLattice.Link a → ComplexMatrix2}
    {A : InfiniteLattice.Link a → ComplexMatrix2} (hA : ∀ e, A e.opposite = -A e)
    (h : ∀ e : InfiniteLattice.Link a, e.IsPositivelyOriented →
      HasDerivAt (fun t => γ t e) (Complex.I • A e * γ 0 e) 0)
    (hu : ∀ e : InfiniteLattice.Link a, e.IsPositivelyOriented → IsUnit (γ 0 e).det) :
    curveTangent γ = A := by
  have hval : ∀ e : InfiniteLattice.Link a, e.IsPositivelyOriented →
      Complex.I⁻¹ • (deriv (fun t => γ t e) 0 * (γ 0 e)⁻¹) = A e := by
    intro e he
    rw [(h e he).deriv, mul_assoc, Matrix.mul_nonsing_inv _ (hu e he), mul_one, smul_smul,
      inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
  funext e
  unfold curveTangent extendOddly
  by_cases he : e.IsPositivelyOriented
  · rw [if_pos he]
    exact hval e he
  · have hr := (opposite_isPositivelyOriented_iff ha e).2 he
    rw [if_neg he]
    beta_reduce
    rw [hval _ hr, hA, neg_neg]
theorem hasDerivAt_presentation (P : GroupHypotheses L k j G 𝔤) {𝔇 : Set (Edge L k j → ComplexMatrix2)}
    {K : PresentationClass L k j ComplexMatrix2} {m : (Edge L k j → ComplexMatrix2) → Edge L k j' → ComplexMatrix2}
    {V m' : _} (hV : V ∈ fieldsValuedIn L k j G) (hK : LeftChartFacts.MapDerivAlongCurves G 𝔇 K m V m')
    {A : Edge L k j → ComplexMatrix2} (hA : IsEdgeFormIn 𝔤 A) {c : Edge L k j'} (hc : c.IsPositivelyOriented)
    (hu : IsUnit (m V c).det) {S : Finset (Edge L k j)} {O : Set (S → ComplexMatrix2)}
    {f : (S → ComplexMatrix2) → ComplexMatrix2} (hp : IsLocalPresentation G 𝔇 (fun V' => m V' c) V S O f)
    (hk : K S O f) :
    HasDerivAt (fun t : ℝ => f (twistedValues S V ((t : ℂ) • A))) (Complex.I • m' A c * m V c) 0 := by
  have hI : IsOpenIntervalAroundZero (univ : Set ℝ) :=
    ⟨isOpen_univ, ordConnected_univ, mem_univ _⟩
  have hγ := isDifferentiableFieldCurve_twist P hV hA hI
  have h0 : expTwist (((0 : ℝ) : ℂ) • A) V = V := expTwist_zero hV A
  have ht : curveTangent (fun t : ℝ => expTwist ((t : ℂ) • A) V) = A := by
    refine curveTangent_eq P.mesh_pos hA.2 (fun e he => ?_) fun e he => ?_
    · have hd := hasDerivAt_expMul_zero (A e) (V e)
      simp only [h0]
      refine hd.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
      simp only
      rw [expTwist_of_pos he]
      rfl
    · simp only [h0]
      exact P.isUnit_det _ (hV.1 e)
  have h := ((hK univ _ hγ h0 c hc).2 S O f hp hk).mul_const (m V c)
  rw [ht] at h
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  simp only
  rw [restrictToEdges_expTwist hp.1, mul_assoc, Matrix.nonsing_inv_mul _ hu, mul_one]
theorem continuous_twistedValues (S : Finset (Edge L k j)) (V A : Edge L k j → ComplexMatrix2) :
    Continuous fun t : ℝ => twistedValues S V ((t : ℂ) • A) :=
  continuous_pi fun e => continuous_iff_continuousAt.2 fun t =>
    (hasDerivAt_expMul (A e) (V e) t).continuousAt
theorem eventually_twistedValues_mem {S : Finset (Edge L k j)} {V A : Edge L k j → ComplexMatrix2}
    {O : Set (S → ComplexMatrix2)} (hO : ComplexMatrix2.IsRelativelyOpen (edgeProduct G S) O)
    (hV : restrictToEdges S V ∈ O)
    (hstay : ∀ t : ℝ, twistedValues S V ((t : ℂ) • A) ∈ edgeProduct G S) :
    ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), twistedValues S V ((t : ℂ) • A) ∈ O := by
  obtain ⟨W, hW, rfl⟩ := hO
  have hc := (continuous_twistedValues S V A).continuousAt (x := (0 : ℝ))
  have h0 : W ∈ 𝓝 (twistedValues S V (((0 : ℝ) : ℂ) • A)) := by
    rw [twistedValues_zero]
    exact hW.mem_nhds hV.1
  filter_upwards [hc.eventually (show ∀ᶠ x in 𝓝 _, x ∈ W from h0)] with t ht
  exact ⟨ht, hstay t⟩
theorem twistedValues_mem_edgeProduct (P : GroupHypotheses L k j G 𝔤) {S : Finset (Edge L k j)}
    (hS : IsFinitePositiveEdgeSet S) {V A : Edge L k j → ComplexMatrix2}
    (hV : V ∈ fieldsValuedIn L k j G) (hA : IsEdgeFormIn 𝔤 A) (t : ℝ) :
    twistedValues S V ((t : ℂ) • A) ∈ edgeProduct G S :=
  fun e => P.twist V hV A hA e (hS.2 e e.2) t
theorem twistedValues_add (S : Finset (Edge L k j)) (V A : Edge L k j → ComplexMatrix2) (s t : ℝ)
    {V₀ : Edge L k j → ComplexMatrix2} (hV₀ : restrictToEdges S V₀ = twistedValues S V ((t : ℂ) • A)) :
    twistedValues S V₀ ((s : ℂ) • A) = twistedValues S V (((s + t : ℝ) : ℂ) • A) := by
  funext e
  have h : V₀ e = ComplexMatrix2.matExp (Complex.I • (((t : ℂ) • A) e)) * V e := congrFun hV₀ e
  have hcomm : Commute (Complex.I • ((s : ℂ) • A e)) (Complex.I • ((t : ℂ) • A e)) :=
    (((Commute.refl (A e)).smul_left _).smul_left _).smul_right _ |>.smul_right _
  let +nondep : NormedAlgebra ℚ ComplexMatrix2 := .restrictScalars ℚ ℂ ComplexMatrix2
  have hadd := NormedSpace.exp_add_of_commute hcomm
  have harg : Complex.I • ((s : ℂ) • A e) + Complex.I • ((t : ℂ) • A e) =
      Complex.I • (((s + t : ℝ) : ℂ) • A e) := by
    push_cast
    rw [add_smul, smul_add]
  rw [harg] at hadd
  change ComplexMatrix2.matExp (Complex.I • ((s : ℂ) • A e)) * V₀ e =
    ComplexMatrix2.matExp (Complex.I • (((s + t : ℝ) : ℂ) • A e)) * V e
  rw [h, ← mul_assoc]
  change NormedSpace.exp (Complex.I • ((s : ℂ) • A e)) *
    NormedSpace.exp (Complex.I • ((t : ℂ) • A e)) * V e = _
  rw [← hadd]
theorem eventually_differentiableAt_presentation (P : GroupHypotheses L k j G 𝔤)
    {𝔇 : Set (Edge L k j → ComplexMatrix2)} (hopen : IsFinitelyOpen G 𝔇)
    {K : PresentationClass L k j ComplexMatrix2}
    {m : (Edge L k j → ComplexMatrix2) → Edge L k j' → ComplexMatrix2}
    {D : (Edge L k j → ComplexMatrix2) → (Edge L k j → ComplexMatrix2) → Edge L k j' → ComplexMatrix2}
    (hK : ∀ V ∈ 𝔇, LeftChartFacts.MapDerivAlongCurves G 𝔇 K m V (D V)) {V : Edge L k j → ComplexMatrix2}
    (hV : V ∈ 𝔇) {A : Edge L k j → ComplexMatrix2} (hA : IsEdgeFormIn 𝔤 A) {c : Edge L k j'}
    (hc : c.IsPositivelyOriented) (hu : ∀ V ∈ 𝔇, IsUnit (m V c).det) {S : Finset (Edge L k j)}
    {O : Set (S → ComplexMatrix2)} {f : (S → ComplexMatrix2) → ComplexMatrix2}
    (hp : IsLocalPresentation G 𝔇 (fun V' => m V' c) V S O f) (hk : K S O f) :
    ∀ᶠ t : ℝ in 𝓝 (0 : ℝ),
      DifferentiableAt ℝ (fun s : ℝ => f (twistedValues S V ((s : ℂ) • A))) t := by
  have hVc := hopen.1 hV
  obtain ⟨ε, hε, hnear⟩ := hopen.2 V hV S hp.1
  have hstay := twistedValues_mem_edgeProduct P hp.1 hVc hA
  have hinO := eventually_twistedValues_mem hp.2.1 hp.2.2.1 hstay
  have hclose : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), ∀ e : S,
      ComplexMatrix2.operatorNorm (twistedValues S V ((t : ℂ) • A) e - V e) < ε := by
    refine eventually_all.2 fun e => ?_
    have hc' : Continuous fun t : ℝ => ‖twistedValues S V ((t : ℂ) • A) e - V e‖ :=
      (((continuous_apply e).comp (continuous_twistedValues S V A)).sub continuous_const).norm
    have h0 : ‖twistedValues S V (((0 : ℝ) : ℂ) • A) e - V e‖ < ε := by
      rw [twistedValues_zero]
      simpa [restrictToEdges] using hε
    exact hc'.continuousAt.eventually (gt_mem_nhds h0)
  filter_upwards [hinO, hclose] with t ht hct
  set V₀ := LocalPresentations.replaceOn S V (twistedValues S V ((t : ℂ) • A)) with hV₀def
  have hV₀c : V₀ ∈ fieldsValuedIn L k j G :=
    (P.presentations 𝔇 (fun _ => (0 : ComplexMatrix2)) V hopen hV).1 S _ hp.1 (hstay t)
  have hbv : restrictToEdges S V₀ = twistedValues S V ((t : ℂ) • A) :=
    funext fun e => replaceOn_of_mem hp.1 e.2
  have hV₀ : V₀ ∈ 𝔇 := by
    refine hnear V₀ hV₀c (fun e he heS => replaceOn_of_not_mem he heS) fun e he => ?_
    rw [hV₀def, replaceOn_of_mem hp.1 he]
    exact hct ⟨e, he⟩
  have hp₀ : IsLocalPresentation G 𝔇 (fun V' => m V' c) V₀ S O f :=
    ⟨hp.1, hp.2.1, hbv ▸ ht, hp.2.2.2⟩
  have h := hasDerivAt_presentation P hV₀c (hK V₀ hV₀) hA hc (hu V₀ hV₀) hp₀ hk
  have h' : HasDerivAt (fun s : ℝ => f (twistedValues S V₀ ((s : ℂ) • A)))
      (Complex.I • D V₀ A c * m V₀ c) (t - t) := by
    simpa using h
  have h2 := HasDerivAt.comp_sub_const t t h'
  refine h2.differentiableAt.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  simp only
  rw [twistedValues_add S V A (s - t) t hbv, sub_add_cancel]
theorem eventually_presentation_mem (P : GroupHypotheses L k j G 𝔤)
    {𝔇 : Set (Edge L k j → ComplexMatrix2)} (hopen : IsFinitelyOpen G 𝔇)
    {g : (Edge L k j → ComplexMatrix2) → ComplexMatrix2} (hval : ∀ V' ∈ 𝔇, g V' ∈ G)
    {V : Edge L k j → ComplexMatrix2} (hV : V ∈ 𝔇) {A : Edge L k j → ComplexMatrix2}
    (hA : IsEdgeFormIn 𝔤 A) {S : Finset (Edge L k j)} {O : Set (S → ComplexMatrix2)}
    {f : (S → ComplexMatrix2) → ComplexMatrix2} (hp : IsLocalPresentation G 𝔇 g V S O f) :
    ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), f (twistedValues S V ((t : ℂ) • A)) ∈ G := by
  obtain ⟨O', hO', -, hVO', -, hkept⟩ := ((P.presentations 𝔇 g V hopen hV).2.2 S O f hp).1
  have hin := eventually_twistedValues_mem hO' hVO' (twistedValues_mem_edgeProduct P hp.1 (hopen.1 hV) hA)
  exact hin.mono fun t ht => hkept G (by simp) hval _ ht
theorem logSeries_deriv_formula {𝕜 : Type} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 ComplexMatrix2]
    {D : Set 𝕜} {g : 𝕜 → ComplexMatrix2} {d M : ComplexMatrix2}
    (hlog : LeftChartFields.CurveLogDerivative 𝕜 D G 𝔤) (hmaps : MapsTo g D G)
    (hd : HasDerivAt g (Complex.I • d * M) 0) (h0 : g 0 = M) (hu : IsUnit M.det) :
    Complex.I⁻¹ • deriv (fun t => ComplexMatrix2.logSeries (g t * M⁻¹)) 0 = d ∧ d ∈ 𝔤 := by
  obtain ⟨-, -, h3, h4⟩ := hlog g hmaps hd.differentiableAt
  have hv : Complex.I⁻¹ • (deriv g 0 * (g 0)⁻¹) = d := by
    rw [hd.deriv, h0, mul_assoc, Matrix.mul_nonsing_inv _ hu, mul_one, smul_smul,
      inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
  rw [hv] at h3 h4
  rw [h0] at h3
  exact ⟨h3, h4⟩
theorem isOpenIntervalAroundZero_ball {δ : ℝ} (hδ : 0 < δ) :
    IsOpenIntervalAroundZero (Metric.ball (0 : ℝ) δ) :=
  ⟨Metric.isOpen_ball, (convex_ball 0 δ).ordConnected, Metric.mem_ball_self hδ⟩
theorem leftDifferential_mem (P : GroupHypotheses L k j G 𝔤) {𝔇 : Set (Edge L k j → ComplexMatrix2)}
    (hopen : IsFinitelyOpen G 𝔇) {K : PresentationClass L k j ComplexMatrix2}
    {m : (Edge L k j → ComplexMatrix2) → Edge L k j' → ComplexMatrix2}
    {V m' : _} (hV : V ∈ 𝔇) (hK : LeftChartFacts.MapDerivAlongCurves G 𝔇 K m V m')
    {A : Edge L k j → ComplexMatrix2} (hA : IsEdgeFormIn 𝔤 A) {c : Edge L k j'}
    (hc : c.IsPositivelyOriented) (hval : ∀ V' ∈ 𝔇, m V' c ∈ G) (hu : IsUnit (m V c).det)
    {S : Finset (Edge L k j)} {O : Set (S → ComplexMatrix2)} {f : (S → ComplexMatrix2) → ComplexMatrix2}
    (hp : IsLocalPresentation G 𝔇 (fun V' => m V' c) V S O f) (hk : K S O f) : m' A c ∈ 𝔤 := by
  have hin := eventually_presentation_mem P hopen hval hV hA hp
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 hin
  have hd := hasDerivAt_presentation P (hopen.1 hV) hK hA hc hu hp hk
  have h0 : f (twistedValues S V (((0 : ℝ) : ℂ) • A)) = m V c := by
    rw [twistedValues_zero]
    exact (hp.2.2.2 V hV hp.2.2.1).symm
  exact (logSeries_deriv_formula (P.logs _ (isOpenIntervalAroundZero_ball hδ))
    (fun t ht => hball t ht) hd h0 hu).2
section Chain
variable {j'' : ℕ}
theorem presentedPoint_zero {𝔇₁ : Set (Edge L k j → ComplexMatrix2)}
    {m₁ : (Edge L k j → ComplexMatrix2) → Edge L k j' → ComplexMatrix2} {V : Edge L k j → ComplexMatrix2}
    (hV : V ∈ 𝔇₁) {S₂ : Finset (Edge L k j')} {w : S₂ → LocalData L k j ComplexMatrix2}
    (hw : ∀ c' : S₂, IsLocalPresentation G 𝔇₁ (fun V' => m₁ V' c') V (w c').support (w c').region
      (w c').fn) :
    LeftChartFacts.presentedPoint w V 0 = restrictToEdges S₂ (m₁ V) := by
  funext c'
  have h := (hw c').2.2.2 V hV (hw c').2.2.1
  have e : (fun b : (w c').support =>
      ComplexMatrix2.matExp (Complex.I • (0 : Edge L k j → ComplexMatrix2) b) * V b) =
        restrictToEdges (w c').support V := by
    funext b
    simp [restrictToEdges]
  change (w c').fn (fun b : (w c').support =>
    ComplexMatrix2.matExp (Complex.I • (0 : Edge L k j → ComplexMatrix2) b) * V b) = m₁ V c'
  rw [e]
  exact h.symm
theorem chain_along_real_line (P : GroupHypotheses L k j G 𝔤) (P' : GroupHypotheses L k j' G 𝔤)
    {𝔇₁ : Set (Edge L k j → ComplexMatrix2)} {𝔇₂ : Set (Edge L k j' → ComplexMatrix2)}
    {K₁ : PresentationClass L k j ComplexMatrix2} {K₂ : PresentationClass L k j' ComplexMatrix2}
    {m₁ : (Edge L k j → ComplexMatrix2) → Edge L k j' → ComplexMatrix2}
    {m₂ : (Edge L k j' → ComplexMatrix2) → Edge L k j'' → ComplexMatrix2}
    {D₁ : (Edge L k j → ComplexMatrix2) → (Edge L k j → ComplexMatrix2) → Edge L k j' → ComplexMatrix2}
    {D₂ : (Edge L k j' → ComplexMatrix2) → Edge L k j'' → ComplexMatrix2}
    (hopen₁ : IsFinitelyOpen G 𝔇₁)
    (hmap₁ : MapsTo m₁ 𝔇₁ (fieldsValuedIn L k j' G))
    (hK₁ : ∀ V ∈ 𝔇₁, LeftChartFacts.MapDerivAlongCurves G 𝔇₁ K₁ m₁ V (D₁ V))
    (hform : ∀ V A (b : Edge L k j'), D₁ V A b.opposite = -D₁ V A b)
    (hpres : ∀ V ∈ 𝔇₁, ∀ c' : Edge L k j', c'.IsPositivelyOriented →
      ∃ (F : Finset (Edge L k j)) (O : Set (F → ComplexMatrix2)) (f : (F → ComplexMatrix2) → ComplexMatrix2),
        IsLocalPresentation G 𝔇₁ (fun V' => m₁ V' c') V F O f ∧ K₁ F O f)
    {V : Edge L k j → ComplexMatrix2} (hV : V ∈ 𝔇₁) {A : Edge L k j → ComplexMatrix2}
    (hA : IsEdgeFormIn 𝔤 A)
    (hK₂ : LeftChartFacts.MapDerivAlongCurves G 𝔇₂ K₂ m₂ (m₁ V) D₂)
    {c : Edge L k j''} (hc : c.IsPositivelyOriented) (hu₂ : IsUnit (m₂ (m₁ V) c).det)
    {S₂ : Finset (Edge L k j')} {O₂ : Set (S₂ → ComplexMatrix2)} {f₂ : (S₂ → ComplexMatrix2) → ComplexMatrix2}
    {w : S₂ → LocalData L k j ComplexMatrix2}
    (hp₂ : IsLocalPresentation G 𝔇₂ (fun W => m₂ W c) (m₁ V) S₂ O₂ f₂) (hk₂ : K₂ S₂ O₂ f₂)
    (hw : ∀ c' : S₂, IsLocalPresentation G 𝔇₁ (fun V' => m₁ V' c') V (w c').support (w c').region
        (w c').fn ∧ K₁ (w c').support (w c').region (w c').fn) :
    (∀ O' : Set (S₂ → ComplexMatrix2), ComplexMatrix2.IsRelativelyOpen (edgeProduct G S₂) O' →
      restrictToEdges S₂ (m₁ V) ∈ O' →
      ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), LeftChartFacts.presentedPoint w V ((t : ℂ) • A) ∈ O') ∧
    HasDerivAt (fun t : ℝ => f₂ (LeftChartFacts.presentedPoint w V ((t : ℂ) • A)))
      (Complex.I • D₂ (D₁ V A) c * m₂ (m₁ V) c) 0 := by
  classical
  have hVc := hopen₁.1 hV
  have hval₁ : ∀ c' : Edge L k j', ∀ V' ∈ 𝔇₁, m₁ V' c' ∈ G :=
    fun c' V' hV' => (hmap₁ hV').1 c'
  have hunit₁ : ∀ c' : Edge L k j', ∀ V' ∈ 𝔇₁, IsUnit (m₁ V' c').det :=
    fun c' V' hV' => P'.isUnit_det _ (hval₁ c' V' hV')
  have hpos : ∀ c' : S₂, (c' : Edge L k j').IsPositivelyOriented := fun c' => hp₂.1.2 c' c'.2
  have hderiv : ∀ c' : S₂, HasDerivAt (fun t : ℝ => LeftChartFacts.presentedPoint w V ((t : ℂ) • A) c')
      (Complex.I • D₁ V A c' * m₁ V c') 0 := fun c' =>
    hasDerivAt_presentation P hVc (hK₁ V hV) hA (hpos c') (hunit₁ c' V hV) (hw c').1 (hw c').2
  have hdiff : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), ∀ c' : S₂,
      DifferentiableAt ℝ (fun s : ℝ => LeftChartFacts.presentedPoint w V ((s : ℂ) • A) c') t :=
    eventually_all.2 fun c' => eventually_differentiableAt_presentation P hopen₁ hK₁ hV hA (hpos c')
      (hunit₁ c') (hw c').1 (hw c').2
  have hmemG : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), ∀ c' : S₂,
      LeftChartFacts.presentedPoint w V ((t : ℂ) • A) c' ∈ G :=
    eventually_all.2 fun c' => eventually_presentation_mem P hopen₁ (hval₁ c') hV hA (hw c').1
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hdiff.and hmemG)
  have hI := isOpenIntervalAroundZero_ball hδ
  have hA₁ : IsEdgeFormIn 𝔤 (D₁ V A) := by
    refine ⟨fun b hb => ?_, hform V A⟩
    obtain ⟨F, O, f, h₁, h₂⟩ := hpres V hV b hb
    exact leftDifferential_mem P hopen₁ hV (hK₁ V hV) hA hb (hval₁ b) (hunit₁ b V hV) h₁ h₂
  have hWc : m₁ V ∈ fieldsValuedIn L k j' G := hmap₁ hV
  have hp0 : LeftChartFacts.presentedPoint w V (((0 : ℝ) : ℂ) • A) = restrictToEdges S₂ (m₁ V) := by
    have h := presentedPoint_zero hV (fun c' => (hw c').1)
    simpa using h
  let base : ℝ → Edge L k j' → ComplexMatrix2 := fun t => expTwist ((t : ℂ) • D₁ V A) (m₁ V)
  let γ : ℝ → Edge L k j' → ComplexMatrix2 :=
    fun t => LocalPresentations.replaceOn S₂ (base t) (LeftChartFacts.presentedPoint w V ((t : ℂ) • A))
  have hbase : ∀ t, base t ∈ fieldsValuedIn L k j' G := fun t =>
    expTwist_mem P'.mesh_pos P'.inv_mem fun b hb => P'.twist _ hWc _ hA₁ b hb t
  have hopenAll : IsFinitelyOpen G (fieldsValuedIn L k j' G) :=
    ⟨Subset.rfl, fun _ _ _ _ => ⟨1, one_pos, fun _ h _ _ => h⟩⟩
  have hγ_in : ∀ b (hb : b ∈ S₂) t,
      γ t b = LeftChartFacts.presentedPoint w V ((t : ℂ) • A) ⟨b, hb⟩ := fun b hb t =>
    replaceOn_of_mem hp₂.1 hb
  have hγ_out : ∀ b, b.IsPositivelyOriented → b ∉ S₂ → ∀ t : ℝ,
      γ t b = ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • D₁ V A b)) * m₁ V b := fun b hb hbS t => by
    have h := replaceOn_of_not_mem (V := base t)
      (y := LeftChartFacts.presentedPoint w V ((t : ℂ) • A)) hb hbS
    rw [show γ t b = _ from h]
    exact expTwist_of_pos hb
  have hγ0 : γ 0 = m₁ V := by
    have e : base 0 = m₁ V := expTwist_zero hWc _
    change LocalPresentations.replaceOn S₂ (base 0)
      (LeftChartFacts.presentedPoint w V (((0 : ℝ) : ℂ) • A)) = m₁ V
    rw [e, hp0]
    exact replaceOn_self hWc
  have hcurve : IsDifferentiableFieldCurve G (Metric.ball (0 : ℝ) δ) γ := by
    refine ⟨hI, fun t ht => ?_, fun b hb => ?_⟩
    · exact (P'.presentations (fieldsValuedIn L k j' G) (fun _ => (0 : ComplexMatrix2)) (base t)
        hopenAll (hbase t)).1 S₂ _ hp₂.1 (hball t ht).2
    · by_cases hbS : b ∈ S₂
      · have e : (fun t => γ t b) =
            fun t : ℝ => LeftChartFacts.presentedPoint w V ((t : ℂ) • A) ⟨b, hbS⟩ :=
          funext fun t => hγ_in b hbS t
        rw [e]
        exact fun t ht => ((hball t ht).1 ⟨b, hbS⟩).differentiableWithinAt
      · have e : (fun t => γ t b) =
            fun t : ℝ => ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • D₁ V A b)) * m₁ V b :=
          funext fun t => hγ_out b hb hbS t
        rw [e]
        exact fun t _ =>
          (hasDerivAt_expMul (D₁ V A b) (m₁ V b) t).differentiableAt.differentiableWithinAt
  have htan : curveTangent γ = D₁ V A := by
    refine curveTangent_eq P'.mesh_pos hA₁.2 (fun b hb => ?_) fun b _ => ?_
    · rw [hγ0]
      by_cases hbS : b ∈ S₂
      · have e : (fun t => γ t b) =
            fun t : ℝ => LeftChartFacts.presentedPoint w V ((t : ℂ) • A) ⟨b, hbS⟩ :=
          funext fun t => hγ_in b hbS t
        rw [e]
        exact hderiv ⟨b, hbS⟩
      · have e : (fun t => γ t b) =
            fun t : ℝ => ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • D₁ V A b)) * m₁ V b :=
          funext fun t => hγ_out b hb hbS t
        rw [e]
        exact hasDerivAt_expMul_zero _ _
    · rw [hγ0]
      exact P'.isUnit_det _ (hWc.1 b)
  have hvals : ∀ t, restrictToEdges S₂ (γ t) = LeftChartFacts.presentedPoint w V ((t : ℂ) • A) :=
    fun t => funext fun c' => hγ_in c' c'.2 t
  have hfin := hK₂ _ γ hcurve hγ0 c hc
  refine ⟨fun O' hO' hWO' => ?_, ?_⟩
  · obtain ⟨W, hW, rfl⟩ := hO'
    have hcont : ContinuousAt (fun t : ℝ => LeftChartFacts.presentedPoint w V ((t : ℂ) • A)) 0 :=
      continuousAt_pi.2 fun c' => (hderiv c').continuousAt
    have h0 : W ∈ 𝓝 (LeftChartFacts.presentedPoint w V (((0 : ℝ) : ℂ) • A)) := by
      rw [hp0]
      exact hW.mem_nhds hWO'.1
    filter_upwards [hcont.eventually (show ∀ᶠ x in 𝓝 _, x ∈ W from h0), hmemG] with t ht ht'
    exact ⟨ht, ht'⟩
  · have h := (hfin.2 S₂ O₂ f₂ hp₂ hk₂).mul_const (m₂ (m₁ V) c)
    rw [htan] at h
    refine h.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    simp only
    rw [hvals, mul_assoc, Matrix.nonsing_inv_mul _ hu₂, mul_one]
end Chain
theorem leftFormula_real {j'' : ℕ} (hc₁ : LeftChartFacts.DifferentialsFromCurves L k j j')
    (hc₂ : LeftChartFacts.DifferentialsFromCurves L k j' j'')
    (P : GroupHypotheses L k j PeriodicLattice.compactGaugeGroup PeriodicLattice.compactLieAlgebra)
    (P' : GroupHypotheses L k j' PeriodicLattice.compactGaugeGroup PeriodicLattice.compactLieAlgebra)
    {𝔇₁ : Set (Edge L k j → ComplexMatrix2)} {𝔇₂ : Set (Edge L k j' → ComplexMatrix2)}
    {m₁ : (Edge L k j → ComplexMatrix2) → Edge L k j' → ComplexMatrix2}
    {m₂ : (Edge L k j' → ComplexMatrix2) → Edge L k j'' → ComplexMatrix2}
    (h₁ : IsDifferentiableFieldMap 𝔇₁ m₁) (h₂ : IsDifferentiableFieldMap 𝔇₂ m₂)
    {V : Edge L k j → ComplexMatrix2} (hV : V ∈ compositeDomain 𝔇₁ 𝔇₂ m₁)
    {A : Edge L k j → ComplexMatrix2} (hA : A ∈ edgeFormSpace (meshAt L k j))
    {c : Edge L k j''} (hc : c.IsPositivelyOriented) :
    LeftChartFacts.LeftFormulaViaPresentations ℝ PeriodicLattice.compactGaugeGroup 𝔇₁ 𝔇₂
      (differentiablePresentations L k j ComplexMatrix2)
      (differentiablePresentations L k j' ComplexMatrix2) m₁ m₂ V A c
      (leftDifferential 𝔇₂ m₂ (m₁ V) (leftDifferential 𝔇₁ m₁ V A) c) := by
  intro S₂ O₂ f₂ w hp₂ hk₂ hw
  have hval₂ : ∀ W ∈ 𝔇₂, m₂ W c ∈ PeriodicLattice.compactGaugeGroup := fun W hW => (h₂.2.1 hW).1 c
  have hu₂ : IsUnit (m₂ (m₁ V) c).det := (isUnit_det_of_compact _ (hval₂ _ hV.2))
  have hfacts := chain_along_real_line P P' h₁.1 h₁.2.1 (fun V' hV' => hc₁.1 𝔇₁ m₁ h₁ V' hV')
    (fun _ _ b => extendOddly_opposite P'.mesh_pos _ b)
    (fun V' hV' c' hc' => (h₁.2.2 c' hc').2 V' hV') hV.1 hA
    (hc₂.1 𝔇₂ m₂ h₂ _ hV.2) hc hu₂ hp₂ hk₂ hw
  obtain ⟨O', hO', -, hWO', -, hkept⟩ :=
    ((P'.presentations 𝔇₂ (fun W => m₂ W c) (m₁ V) h₂.1 hV.2).2.2 S₂ O₂ f₂ hp₂).1
  have hG : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), f₂ (LeftChartFacts.presentedPoint w V ((t : ℂ) • A)) ∈
      PeriodicLattice.compactGaugeGroup :=
    (hfacts.1 O' hO' hWO').mono fun t ht => hkept _ (by simp) hval₂ _ ht
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 hG
  have hM : f₂ (LeftChartFacts.presentedPoint w V 0) = m₂ (m₁ V) c := by
    rw [presentedPoint_zero hV.1 fun c' => (hw c').1]
    exact (hp₂.2.2.2 _ hV.2 hp₂.2.2.1).symm
  have h0 : (fun t : ℝ => f₂ (LeftChartFacts.presentedPoint w V ((t : ℂ) • A))) 0 = m₂ (m₁ V) c := by
    simpa using hM
  have hform := logSeries_deriv_formula (P.logs _ (isOpenIntervalAroundZero_ball hδ))
    (fun t ht => hball t ht) hfacts.2 h0 hu₂
  refine ⟨hfacts.1 O₂ hp₂.2.1 hp₂.2.2.1, ?_⟩
  unfold logDirectionalDeriv
  rw [hM]
  exact hform.1
section Holomorphic
open Matrices.GroupLieProduct
def matrixEntriesCLE : ComplexMatrix2 ≃L[ℂ] Coordinates.ComplexCoordinates 4 :=
  LinearEquiv.toContinuousLinearEquiv
    { Coordinates.ComplexCoordinates.matrixEquiv with
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
def matrixPiCLE {σ : Type} [Fintype σ] {n : ℕ} (ν : σ ≃ Fin n) :
    (σ → ComplexMatrix2) ≃L[ℂ] Coordinates.ComplexCoordinates
      (Coordinates.ComplexCoordinates.productDim
        fun _ : Fin n => Coordinates.ComplexCoordinates.Component.matrix) :=
  LinearEquiv.toContinuousLinearEquiv
    { matrixPiEquiv ν with
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
theorem isHolomorphicIn_univ {N N' : ℕ}
    {f : Coordinates.ComplexCoordinates N → Coordinates.ComplexCoordinates N'}
    (hf : Differentiable ℂ f) : Coordinates.ComplexCoordinates.IsHolomorphicIn univ f :=
  ⟨isOpen_univ, hf.continuous.continuousOn, fun a _ n => Eventually.of_forall fun ζ =>
    DifferentiableAt.comp ζ (hf _) (by unfold Coordinates.ComplexCoordinates.stdBasisVector; fun_prop)⟩
theorem asGroupFactors_inl {σ : Type} (p : σ ⊕ Empty → ComplexMatrix2) :
    asGroupFactors (fun b => p (.inl b)) = p := by apply _root_.YangMills.DeltaSharedProofs.p4358 <;> assumption
theorem asGroupFactors_injective {σ : Type} {x y : σ → ComplexMatrix2}
    (h : asGroupFactors x = asGroupFactors y) : x = y :=
  funext fun b => congrFun h (.inl b)
theorem isRelativelyOpen_asGroupFactors_image {σ : Type} {O : Set (σ → ComplexMatrix2)}
    (h : ComplexMatrix2.IsRelativelyOpen (unimodularPi σ) O) :
    ComplexMatrix2.IsRelativelyOpen (Matrices.GroupLieProduct σ Empty) (asGroupFactors '' O) := by apply _root_.YangMills.Construction.Tower.FullSpaceChainRule.isRelativelyOpen_image_asGroupFactors <;> assumption
theorem isHolomorphicToProduct_select (hC : Matrices.GroupLieProduct.HolomorphicCalculus.Properties)
    {ι τ : Type} [Fintype ι] [Fintype τ] (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (idx : τ → ι) {W : Set (ι ⊕ Empty → ComplexMatrix2)}
    (hW : ComplexMatrix2.IsRelativelyOpen (Matrices.GroupLieProduct ι Empty) W)
    (hsub : W ⊆ Matrices.GroupLieProduct ι Empty) :
    IsHolomorphicToProduct β W
      (fun q => asGroupFactors fun t => q (.inl (idx t)) :
        (ι ⊕ Empty → ComplexMatrix2) → τ ⊕ Empty → ComplexMatrix2) := by
  classical
  let h : (ι ⊕ Empty → ComplexMatrix2) → τ ⊕ Empty → ComplexMatrix2 :=
    fun q => asGroupFactors fun t => q (.inl (idx t))
  let ν := Fintype.equivFin (ι ⊕ Empty)
  let ν' := Fintype.equivFin (τ ⊕ Empty)
  have hdiff : Differentiable ℂ h := by
    refine differentiable_pi.2 fun i => ?_
    rcases i with t | e
    · exact differentiable_apply (Sum.inl (idx t) : ι ⊕ Empty)
    · exact e.elim
  have hthrough : Coordinates.ComplexCoordinates.IsHolomorphicVia (matrixPiEquiv ν)
      (matrixPiEquiv ν') univ h := by
    unfold Coordinates.ComplexCoordinates.IsHolomorphicVia
    rw [image_univ_of_surjective (matrixPiEquiv ν).surjective]
    exact isHolomorphicIn_univ ((matrixPiCLE ν').differentiable.comp
      (hdiff.comp (matrixPiCLE ν).symm.differentiable))
  have hmaps : MapsTo h (univ ∩ Matrices.GroupLieProduct ι Empty) (Matrices.GroupLieProduct τ Empty) := by
    intro q hq i
    rcases i with t | e
    · exact hq.2 (.inl (idx t))
    · exact e.elim
  have hh := hC.2.2.2.1 ι Empty τ Empty _ _ ν ν' univ h hthrough hmaps β
  exact hC.2.2.2.2.2.2.2.2.1 ι Empty τ Empty β _ W h hh hW fun q hq => ⟨trivial, hsub hq⟩
theorem isHolomorphicToCoords_entry {ι κ : Type} [Fintype ι] [Fintype κ]
    (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) {W : Set (ι ⊕ κ → ComplexMatrix2)}
    {Φ : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2}
    (h : IsHolomorphicToCoords β Coordinates.ComplexCoordinates.matrixEquiv W Φ) (r s : Fin 2) :
    IsHolomorphicToCoords β LeftChartFields.scalarCoords W (fun p => Φ p r s) := by apply _root_.YangMills.DeltaSharedProofs.p501989 <;> assumption
theorem differentiableAt_of_entries {g : ℂ → ComplexMatrix2} {z : ℂ}
    (h : ∀ r s, DifferentiableAt ℂ (fun t => g t r s) z) : DifferentiableAt ℂ g z := by
  have h1 : DifferentiableAt ℂ (fun t => matrixEntriesCLE (g t)) z :=
    differentiableAt_pi.2 fun i =>
      h (Coordinates.ComplexCoordinates.entryIndex.symm i).1
        (Coordinates.ComplexCoordinates.entryIndex.symm i).2
  have h2 := DifferentiableAt.comp z matrixEntriesCLE.symm.differentiable.differentiableAt h1
  simpa [Function.comp_def] using h2
theorem presentedPoint_holomorphic (hC : Matrices.GroupLieProduct.HolomorphicCalculus.Properties)
    (hH : Matrices.GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (hA : (LeftChartFields.fullData L k j).HolomorphicGradientExists)
    (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) {V : Edge L k j → ComplexMatrix2}
    (hV : V ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup) {A : Edge L k j → ComplexMatrix2}
    (hB : A ∈ complexEdgeForms (meshAt L k j)) {S₂ : Finset (Edge L k j')}
    (hS₂ : S₂.Nonempty) {O₂ : Set (S₂ → ComplexMatrix2)} {f₂ : (S₂ → ComplexMatrix2) → ComplexMatrix2}
    (hk₂ : IsHolomorphicToCoords β Coordinates.ComplexCoordinates.matrixEquiv (asGroupFactors '' O₂)
      fun p => f₂ fun b => p (.inl b))
    {w : S₂ → LocalData L k j ComplexMatrix2} (hwF : ∀ c', IsFinitePositiveEdgeSet (w c').support)
    {O : ∀ c', Set ((w c').support → ComplexMatrix2)}
    (hO : ∀ c', ComplexMatrix2.IsRelativelyOpen
      (edgeProduct PeriodicLattice.complexGaugeGroup (w c').support) (O c'))
    (hk : ∀ c', IsHolomorphicToCoords β Coordinates.ComplexCoordinates.matrixEquiv
      (asGroupFactors '' O c') fun p => (w c').fn fun b => p (.inl b))
    (hval : ∀ c', ∀ x ∈ O c', (w c').fn x ∈ PeriodicLattice.complexGaugeGroup)
    (hVO : ∀ c', restrictToEdges (w c').support V ∈ O c')
    (hpt : (fun c' => (w c').fn (restrictToEdges (w c').support V)) ∈ O₂) :
    (∀ᶠ t : ℂ in 𝓝 (0 : ℂ), LeftChartFacts.presentedPoint w V (t • A) ∈ O₂) ∧
      DifferentiableAt ℂ (fun t : ℂ => f₂ (LeftChartFacts.presentedPoint w V (t • A))) 0 := by
  classical
  let Fc : Finset (Edge L k j) := Finset.univ.biUnion fun c' : S₂ => (w c').support
  have hmem : ∀ (c' : S₂) (b : (w c').support), (b : Edge L k j) ∈ Fc := fun c' b =>
    Finset.mem_biUnion.2 ⟨c', Finset.mem_univ _, b.2⟩
  have hpos : ∀ b ∈ Fc, b.IsPositivelyOriented := by
    intro b hb
    obtain ⟨c', -, hb'⟩ := Finset.mem_biUnion.1 hb
    exact (hwF c').2 b hb'
  have hne : 0 < Fc.card := by
    obtain ⟨c₀, hc₀⟩ := hS₂
    obtain ⟨b, hb⟩ := (hwF ⟨c₀, hc₀⟩).1
    exact Finset.card_pos.2 ⟨b, hmem ⟨c₀, hc₀⟩ ⟨b, hb⟩⟩
  let ν : Fc ≃ Fin Fc.card := Fc.equivFin
  let idx : ∀ c' : S₂, (w c').support → Fin Fc.card := fun c' b => ν ⟨b, hmem c' b⟩
  let bs : Fin Fc.card → (LeftChartFields.fullData L k j).PosLink :=
    fun i => ⟨(ν.symm i).1, hpos _ (ν.symm i).2⟩
  have hbs : ∀ (c' : S₂) (b : (w c').support), (bs (idx c' b)).1 = b := by
    intro c' b
    simp [bs, idx]
  let cut : ∀ c' : S₂, (Fin Fc.card ⊕ Empty → ComplexMatrix2) → (w c').support → ComplexMatrix2 :=
    fun c' q b => q (.inl (idx c' b))
  choose U hUo hU using hO
  let W₀ : Set (Fin Fc.card ⊕ Empty → ComplexMatrix2) :=
    (⋂ c', {q | cut c' q ∈ U c'}) ∩ Matrices.GroupLieProduct (Fin Fc.card) Empty
  have hW₀ : ComplexMatrix2.IsRelativelyOpen (Matrices.GroupLieProduct (Fin Fc.card) Empty) W₀ := by
    refine ⟨_, isOpen_iInter_of_finite fun c' => (hUo c').preimage ?_, rfl⟩
    exact continuous_pi fun b => continuous_apply _
  have hcutO : ∀ c', ∀ q ∈ W₀, cut c' q ∈ O c' := by
    intro c' q hq
    rw [hU c']
    exact ⟨mem_iInter.1 hq.1 c', fun b => hq.2 (.inl _)⟩
  let Φ : ∀ c' : S₂, (Fin Fc.card ⊕ Empty → ComplexMatrix2) → ComplexMatrix2 :=
    fun c' q => (w c').fn (cut c' q)
  have hcoord : ∀ c', IsHolomorphicToCoords β Coordinates.ComplexCoordinates.matrixEquiv W₀ (Φ c') := by
    intro c'
    have hsel := isHolomorphicToProduct_select hC β (idx c') hW₀ inter_subset_right
    have h := (hC.1 _ _ _ _ β W₀ _ hW₀ hsel ComplexMatrix2 4 Coordinates.ComplexCoordinates.matrixEquiv
      _ _ (hk c')).2.2
    have e : W₀ ∩ (fun q => asGroupFactors fun t => q (.inl (idx c' t))) ⁻¹' (asGroupFactors '' O c') =
        W₀ := inter_eq_left.2 fun q hq => ⟨cut c' q, hcutO c' q hq, rfl⟩
    rw [e] at h
    exact h
  have hgrp : ∀ c', IsHolomorphicToUnimodular β W₀ (Φ c') := fun c' =>
    ((hH.2.2.2.1 (Fin Fc.card) Empty).2.1 β W₀ (Φ c') hW₀
      fun q hq => hval c' _ (hcutO c' q hq)).2 (hcoord c')
  let Ψ : (Fin Fc.card ⊕ Empty → ComplexMatrix2) → S₂ ⊕ Empty → ComplexMatrix2 :=
    fun q => asGroupFactors fun c' => Φ c' q
  have hΨ : IsHolomorphicToProduct β W₀ Ψ := ⟨hW₀, hgrp, fun e => e.elim⟩
  obtain ⟨-, hW₁, hhol⟩ := hC.1 _ _ _ _ β W₀ Ψ hW₀ hΨ ComplexMatrix2 4
    Coordinates.ComplexCoordinates.matrixEquiv _ _ hk₂
  set W₁ := W₀ ∩ Ψ ⁻¹' (asGroupFactors '' O₂) with hW₁def
  let Φf : (Fin Fc.card ⊕ Empty → ComplexMatrix2) → ComplexMatrix2 := (fun p => f₂ fun b => p (.inl b)) ∘ Ψ
  let O₃ : Set (Fin Fc.card → ComplexMatrix2) := {x | asGroupFactors x ∈ W₁}
  have hsubP : W₁ ⊆ Matrices.GroupLieProduct (Fin Fc.card) Empty := fun q hq => hq.1.2
  have hO₃ : ComplexMatrix2.IsRelativelyOpen (unimodularPi (Fin Fc.card)) O₃ := by
    obtain ⟨U₁, hU₁, he⟩ := hW₁
    refine ⟨asGroupFactors ⁻¹' U₁, hU₁.preimage ?_, ?_⟩
    · refine continuous_pi fun i => ?_
      rcases i with i | e
      · exact continuous_apply i
      · exact e.elim
    · ext x
      change asGroupFactors x ∈ W₁ ↔ _
      rw [he]
      constructor
      · rintro ⟨h₁, h₂⟩
        exact ⟨h₁, fun i => h₂ (.inl i)⟩
      · rintro ⟨h₁, h₂⟩
        refine ⟨h₁, fun i => ?_⟩
        rcases i with i | e
        · exact h₂ i
        · exact e.elim
  have himg : asGroupFactors '' O₃ = W₁ := by
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hq
      refine ⟨fun i => q (.inl i), ?_, asGroupFactors_inl q⟩
      change asGroupFactors _ ∈ W₁
      rw [asGroupFactors_inl]
      exact hq
  have hcut : ∀ (X : Edge L k j → ComplexMatrix2) (c' : S₂),
      cut c' (asGroupFactors (LeftChartFields.LatticeData.leftPoint
        (Λ := LeftChartFields.fullData L k j) bs V X)) =
        fun b : (w c').support => ComplexMatrix2.matExp (Complex.I • X b) * V b := by
    intro X c'
    funext b
    change LeftChartFields.leftExpMul (X (bs (idx c' b)).1) (V (bs (idx c' b)).1) = _
    rw [hbs]
    rfl
  have hΨpoint : ∀ X : Edge L k j → ComplexMatrix2,
      (fun c' => Φ c' (asGroupFactors (LeftChartFields.LatticeData.leftPoint
        (Λ := LeftChartFields.fullData L k j) bs V X))) =
        LeftChartFacts.presentedPoint w V X := fun X =>
    funext fun c' => congrArg (w c').fn (hcut X c')
  have hΦf : ∀ X : Edge L k j → ComplexMatrix2,
      Φf (asGroupFactors (LeftChartFields.LatticeData.leftPoint
        (Λ := LeftChartFields.fullData L k j) bs V X)) =
        f₂ (LeftChartFacts.presentedPoint w V X) := fun X =>
    congrArg f₂ (hΨpoint X)
  have hVpt : (fun i => LeftChartFields.LatticeData.onPositive
      (Λ := LeftChartFields.fullData L k j) V (bs i)) ∈ O₃ := by
    have hc' : ∀ c' : S₂, cut c' (asGroupFactors fun i =>
        LeftChartFields.LatticeData.onPositive (Λ := LeftChartFields.fullData L k j) V (bs i)) =
          restrictToEdges (w c').support V := by
      intro c'
      funext b
      change V (bs (idx c' b)).1 = V b
      rw [hbs]
    have hP : (asGroupFactors fun i =>
        LeftChartFields.LatticeData.onPositive (Λ := LeftChartFields.fullData L k j) V (bs i)) ∈
        Matrices.GroupLieProduct (Fin Fc.card) Empty := by
      intro i
      rcases i with i | e
      · exact hV.1 _
      · exact e.elim
    refine ⟨⟨mem_iInter.2 fun c' => ?_, hP⟩, ?_⟩
    · have h := hVO c'
      rw [hU c'] at h
      change cut c' _ ∈ U c'
      rw [hc' c']
      exact h.1
    · refine ⟨_, hpt, ?_⟩
      change _ = asGroupFactors fun c' => (w c').fn (cut c' _)
      congr 1
      funext c'
      rw [hc' c']
  have hpair : ∀ r s : Fin 2, LeftChartFields.LatticeData.LeftDerivEqPair ℂ
      (LeftChartFields.fullData L k j).cforms bs O₃ (fun x => Φf (asGroupFactors x) r s) V := by
    intro r s
    refine hA β Fc.card hne bs O₃ _ V hO₃ ?_ hV hVpt
    rw [himg]
    exact isHolomorphicToCoords_entry β hhol r s
  constructor
  · refine ((hpair 0 0).1 A hB).mono fun t ht => ?_
    obtain ⟨y, hy, he⟩ := ht.2
    have h2 : y = LeftChartFacts.presentedPoint w V (t • A) :=
      (asGroupFactors_injective he).trans (hΨpoint (t • A))
    exact h2 ▸ hy
  · refine differentiableAt_of_entries fun r s => ?_
    have h := (hpair r s).2.1 A hB
    refine h.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    exact congrFun (congrFun (hΦf (t • A)).symm r) s
theorem leftFormula_complex {j'' : ℕ} (hC : Matrices.GroupLieProduct.HolomorphicCalculus.Properties)
    (hH : Matrices.GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (hA : (LeftChartFields.fullData L k j).HolomorphicGradientExists)
    (hlogs : ∀ ρ : ℝ, 0 < ρ → LeftChartFields.CurveLogDerivative ℂ (Metric.ball 0 ρ)
      PeriodicLattice.complexGaugeGroup PeriodicLattice.complexLieAlgebra)
    (hc₁ : LeftChartFacts.DifferentialsFromCurves L k j j')
    (hc₂ : LeftChartFacts.DifferentialsFromCurves L k j' j'')
    (P : GroupHypotheses L k j PeriodicLattice.complexGaugeGroup PeriodicLattice.complexLieAlgebra)
    (P' : GroupHypotheses L k j' PeriodicLattice.complexGaugeGroup PeriodicLattice.complexLieAlgebra)
    {β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
    {𝔇₁ : Set (Edge L k j → ComplexMatrix2)} {𝔇₂ : Set (Edge L k j' → ComplexMatrix2)}
    {m₁ : (Edge L k j → ComplexMatrix2) → Edge L k j' → ComplexMatrix2}
    {m₂ : (Edge L k j' → ComplexMatrix2) → Edge L k j'' → ComplexMatrix2}
    (h₁ : IsHolomorphicFieldMap β 𝔇₁ m₁) (h₂ : IsHolomorphicFieldMap β 𝔇₂ m₂)
    {V : Edge L k j → ComplexMatrix2} (hV : V ∈ compositeDomain 𝔇₁ 𝔇₂ m₁)
    {B : Edge L k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms (meshAt L k j))
    {c : Edge L k j''} (hc : c.IsPositivelyOriented) :
    LeftChartFacts.LeftFormulaViaPresentations ℂ PeriodicLattice.complexGaugeGroup 𝔇₁ 𝔇₂
      (holomorphicPresentations L k j β Coordinates.ComplexCoordinates.matrixEquiv)
      (holomorphicPresentations L k j' β Coordinates.ComplexCoordinates.matrixEquiv) m₁ m₂ V B c
      (holLeftDifferential β 𝔇₂ m₂ (m₁ V) (holLeftDifferential β 𝔇₁ m₁ V B) c) := by
  intro S₂ O₂ f₂ w hp₂ hk₂ hw
  have hval₂ : ∀ W ∈ 𝔇₂, m₂ W c ∈ PeriodicLattice.complexGaugeGroup := fun W hW => (h₂.2.1 hW).1 c
  have hu₂ : IsUnit (m₂ (m₁ V) c).det := isUnit_det_of_complex _ (hval₂ _ hV.2)
  have hfacts := chain_along_real_line P P' h₁.1 h₁.2.1 (fun V' hV' => hc₁.2.2.1 β 𝔇₁ m₁ h₁ V' hV')
    (fun _ _ b => extendOddly_opposite P'.mesh_pos _ b)
    (fun V' hV' c' hc' => (h₁.2.2 c' hc').2 V' hV') hV.1 hB
    (hc₂.2.2.1 β 𝔇₂ m₂ h₂ _ hV.2) hc hu₂ hp₂ hk₂ hw
  obtain ⟨O₂', hO₂', hsub₂, hW₂, -, hkept₂⟩ :=
    ((P'.presentations 𝔇₂ (fun W => m₂ W c) (m₁ V) h₂.1 hV.2).2.2 S₂ O₂ f₂ hp₂).1
  have hvalO₂ : ∀ x ∈ O₂', f₂ x ∈ PeriodicLattice.complexGaugeGroup := fun x hx =>
    hkept₂ _ (by simp) hval₂ x hx
  have hdim : ∀ c' : S₂, ∃ O' : Set ((w c').support → ComplexMatrix2),
      ComplexMatrix2.IsRelativelyOpen (edgeProduct PeriodicLattice.complexGaugeGroup (w c').support) O' ∧
        O' ⊆ (w c').region ∧ restrictToEdges (w c').support V ∈ O' ∧
        ∀ x ∈ O', (w c').fn x ∈ PeriodicLattice.complexGaugeGroup := fun c' => by
    obtain ⟨O', e₁, e₂, e₃, -, e₅⟩ :=
      ((P.presentations 𝔇₁ (fun V' => m₁ V' c') V h₁.1 hV.1).2.2 _ _ _ (hw c').1).1
    exact ⟨O', e₁, e₂, e₃, fun x hx => e₅ _ (by simp) (fun V' hV' => (h₁.2.1 hV').1 c') x hx⟩
  choose O' hO'o hO's hO'V hO'v using hdim
  have hk₂' := hC.2.2.2.2.2.2.2.1 S₂ Empty β _ (asGroupFactors '' O₂') ComplexMatrix2 4
    Coordinates.ComplexCoordinates.matrixEquiv _ hk₂ (isRelativelyOpen_asGroupFactors_image hO₂')
    (image_mono hsub₂)
  have hk' := fun c' : S₂ => hC.2.2.2.2.2.2.2.1 (w c').support Empty β _ (asGroupFactors '' O' c')
    ComplexMatrix2 4 Coordinates.ComplexCoordinates.matrixEquiv _ (hw c').2
    (isRelativelyOpen_asGroupFactors_image (hO'o c')) (image_mono (hO's c'))
  have hpt : (fun c' => (w c').fn (restrictToEdges (w c').support V)) ∈ O₂' := by
    have e : (fun c' => (w c').fn (restrictToEdges (w c').support V)) = restrictToEdges S₂ (m₁ V) :=
      funext fun c' => ((hw c').1.2.2.2 V hV.1 (hw c').1.2.2.1).symm
    rw [e]
    exact hW₂
  obtain ⟨hin, hdz⟩ := presentedPoint_holomorphic hC hH hA β (h₁.1.1 hV.1) hB hp₂.1.1 hk₂'
    (fun c' => (hw c').1.1) hO'o hk' hO'v hO'V hpt
  let g : ℂ → ComplexMatrix2 := fun t => f₂ (LeftChartFacts.presentedPoint w V (t • B))
  have hg : HasDerivAt g (deriv g 0) 0 := hdz.hasDerivAt
  have hreal : HasDerivAt (fun t : ℝ => g t) (deriv g 0) 0 := by
    have h : HasDerivAt g (deriv g 0) (Complex.ofRealCLM (0 : ℝ)) := by
      simpa using hg
    have h2 := HasDerivAt.scomp (0 : ℝ) h Complex.ofRealCLM.hasDerivAt
    simpa [Function.comp_def] using h2
  have hvalue := hreal.unique hfacts.2
  rw [hvalue] at hg
  have hG : ∀ᶠ t : ℂ in 𝓝 (0 : ℂ), g t ∈ PeriodicLattice.complexGaugeGroup :=
    hin.mono fun t ht => hvalO₂ _ ht
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.1 hG
  have hM : f₂ (LeftChartFacts.presentedPoint w V 0) = m₂ (m₁ V) c := by
    rw [presentedPoint_zero hV.1 fun c' => (hw c').1]
    exact (hp₂.2.2.2 _ hV.2 hp₂.2.2.1).symm
  have h0 : g 0 = m₂ (m₁ V) c := by
    simpa [g] using hM
  have hform := logSeries_deriv_formula (hlogs ρ hρ) (fun t ht => hball t ht) hg h0 hu₂
  refine ⟨hin.mono fun t ht => hsub₂ ht, ?_⟩
  unfold logDirectionalDeriv
  rw [hM]
  exact hform.1
end Holomorphic
theorem groupHypotheses_compact (hcfg : LeftChartFields.Claim)
    (hp : LocalPresentations.LocalPresentationNearPoint)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j ≤ k) :
    GroupHypotheses L k j PeriodicLattice.compactGaugeGroup PeriodicLattice.compactLieAlgebra :=
  ⟨meshAt_pos hL, inv_mem_compactGaugeGroup, isUnit_det_of_compact,
    fun V hV A hA e he t => ((hcfg.2.2 L k j hL hj).2.1.1.1 V hV A hA ⟨e, he⟩).1 t,
    fun D hD => (hcfg.1 D hD).1, (hp L hL k j hj).2.1⟩
theorem groupHypotheses_complex (hcfg : LeftChartFields.Claim)
    (hp : LocalPresentations.LocalPresentationNearPoint)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j ≤ k) :
    GroupHypotheses L k j PeriodicLattice.complexGaugeGroup PeriodicLattice.complexLieAlgebra :=
  ⟨meshAt_pos hL, inv_mem_complexGaugeGroup, isUnit_det_of_complex,
    fun V hV A hA e he t => ((hcfg.2.2 L k j hL hj).2.1.1.2 V hV A hA ⟨e, he⟩).1 (t : ℂ),
    fun D hD => (hcfg.1 D hD).2, (hp L hL k j hj).2.2.2⟩
end YangMills.Construction.Tower.FullSpace.ChainRule
namespace YangMills.Construction.Tower
open FullSpace.ChainRule in
theorem leftChartChainRule_holds
    (curves : FullSpaceCurveDifferentials.Statement)
    (configurations : LeftChartFields.Claim)
    (presentations : LocalPresentations.LocalPresentationNearPoint)
    (charts : Matrices.GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (calculus : Matrices.GroupLieProduct.HolomorphicCalculus.Properties) :
    LeftChartChainRule := by
  intro L k j j' j'' hL hj hj' _
  have hc₁ := curves L k j j' hL hj hj'
  have hc₂ := curves L k j' j'' hL hj' ‹_›
  refine ⟨fun 𝔇₁ 𝔇₂ m₁ m₂ h₁ h₂ V hV A hA c hc => ?_,
    fun β 𝔇₁ 𝔇₂ m₁ m₂ h₁ h₂ V hV A hA c hc => ?_⟩
  · exact leftFormula_real hc₁ hc₂ (groupHypotheses_compact configurations presentations hL hj)
      (groupHypotheses_compact configurations presentations hL hj') h₁ h₂ hV hA hc
  · exact leftFormula_complex calculus charts (configurations.2.2 L k j hL hj).2.1.2.2.2
      (fun ρ hρ => configurations.2.1 ρ hρ) hc₁ hc₂
      (groupHypotheses_complex configurations presentations hL hj)
      (groupHypotheses_complex configurations presentations hL hj') h₁ h₂ hV hA hc
end YangMills.Construction.Tower
