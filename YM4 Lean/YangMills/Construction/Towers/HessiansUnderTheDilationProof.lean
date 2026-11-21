import YangMills.Construction.Towers.CurvesUnderTheDilationProof
import YangMills.Construction.Towers.HessianOfARestriction
import YangMills.Construction.Towers.HessiansUnderTheDilation
import YangMills.Construction.Towers.RealAnalyticFunctionsAreOfClassTwoOnSubsets
import Mathlib
set_option autoImplicit false
open Set Filter Topology
noncomputable section
namespace YangMills.Construction.Tower.HessianScaling
open YangMills.Construction.Matrices YangMills.Construction.Geometry
variable {L n k l n' k' l' : ℕ}
structure PreservesEdges (e : Edge L n k l ≃ Edge L n' k' l') : Prop where
  orientation_iff : ∀ b, (e b).IsPositivelyOriented ↔ b.IsPositivelyOriented
  map_opposite : ∀ b, e b.opposite = (e b).opposite
theorem PreservesEdges.symm {e : Edge L n k l ≃ Edge L n' k' l'} (he : PreservesEdges e) :
    PreservesEdges e.symm where
  orientation_iff b := by
    have := he.orientation_iff (e.symm b)
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  map_opposite b := by
    apply e.injective
    rw [he.map_opposite]
    simp
variable {e : Edge L n k l ≃ Edge L n' k' l'}
theorem transportTotal_symm_transportTotal (e : Edge L n k l ≃ Edge L n' k' l')
    (U : Edge L n k l → ComplexMatrix2) :
    transportTotal e.symm (transportTotal e U) = U := by apply _root_.YangMills.Construction.Tower.EdgeTransport.transportTotal_symm_transportTotal <;> assumption
theorem transportTotal_mem_fieldsIn (he : PreservesEdges e) {G : Set ComplexMatrix2}
    {U : Edge L n k l → ComplexMatrix2}
    (hU : U ∈ fieldsIn L n k l G) : transportTotal e U ∈ fieldsIn L n' k' l' G := by
  refine ⟨fun b hb => hU.1 _ (mem_univ _), fun b hb => ?_⟩
  have h := hU.2 (e.symm b) (mem_univ _)
  have hr := he.symm.map_opposite b
  simp only [transportTotal, Function.comp_apply]
  rw [hr]
  exact h
theorem isCurve_transport (he : PreservesEdges e) {I : Set ℝ}
    {γ : ℝ → Edge L n k l → ComplexMatrix2}
    (h : (fieldCurveData L n k l).IsCurve I γ) :
    (fieldCurveData L n' k' l').IsCurve I fun t => transportTotal e (γ t) :=
  ⟨h.1, fun _ ht => transportTotal_mem_fieldsIn he (h.2.1 ht),
    fun b hb => h.2.2 (e.symm b) ((he.symm.orientation_iff b).2 hb)⟩
theorem isTwiceDiffCurve_transport (he : PreservesEdges e) {I : Set ℝ}
    {γ : ℝ → Edge L n k l → ComplexMatrix2}
    (h : (fieldCurveData L n k l).IsTwiceDiffCurve I γ) :
    (fieldCurveData L n' k' l').IsTwiceDiffCurve I fun t => transportTotal e (γ t) :=
  ⟨isCurve_transport he h.1, fun b hb => h.2 (e.symm b) ((he.symm.orientation_iff b).2 hb)⟩
theorem tangent_transport (he : PreservesEdges e) (γ : ℝ → Edge L n k l → ComplexMatrix2) :
    (fieldCurveData L n' k' l').tangent (fun t => transportTotal e (γ t)) =
      transportTotal e ((fieldCurveData L n k l).tangent γ) := by
  funext b'
  obtain ⟨b, rfl⟩ := e.surjective b'
  change curveTangent (fun t => transportTotal e (γ t)) (e b) =
    transportTotal e (curveTangent γ) (e b)
  rw [transportTotal_apply]
  simp only [curveTangent, extendOddly]
  by_cases hb : b.IsPositivelyOriented
  · rw [if_pos ((he.orientation_iff b).2 hb), if_pos hb]
    simp only [transportTotal_apply]
  · rw [if_neg (fun h => hb ((he.orientation_iff b).1 h)), if_neg hb, ← he.map_opposite]
    simp only [transportTotal_apply]
def transportLinear (e : Edge L n k l ≃ Edge L n' k' l') :
    (Edge L n k l → ComplexMatrix2) →ₗ[ℝ] Edge L n' k' l' → ComplexMatrix2 where
  toFun := transportTotal e
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem transport_mem_tangentSpan (he : PreservesEdges e) {N : Set (Edge L n k l → ComplexMatrix2)}
    {N' : Set (Edge L n' k' l' → ComplexMatrix2)} (hN : MapsTo (transportTotal e) N N')
    {x : Edge L n k l → ComplexMatrix2} {x' : Edge L n' k' l' → ComplexMatrix2}
    (hx : transportTotal e x = x')
    {v : Edge L n k l → ComplexMatrix2} (hv : v ∈ (fieldCurveData L n k l).tangentSpan N x) :
    transportTotal e v ∈ (fieldCurveData L n' k' l').tangentSpan N' x' := by
  have hle : (fieldCurveData L n k l).tangentSpan N x ≤
      ((fieldCurveData L n' k' l').tangentSpan N' x').comap (transportLinear e) := by
    refine Submodule.span_le.2 ?_
    rintro v ⟨I, γ, hc, hm, h0, ht⟩
    refine Submodule.subset_span ⟨I, fun t => transportTotal e (γ t), isCurve_transport he hc,
      fun t ht' => hN (hm ht'), ?_, ?_⟩
    · change transportTotal e (γ 0) = x'
      rw [h0, hx]
    · rw [tangent_transport he, ht]
      rfl
  exact hle hv
theorem isHessianFormAt_of_transport (he : PreservesEdges e)
    {N : Set (Edge L n k l → ComplexMatrix2)}
    {N' : Set (Edge L n' k' l' → ComplexMatrix2)} (hN : MapsTo (transportTotal e) N N')
    {F : (Edge L n k l → ComplexMatrix2) → ℝ} {F' : (Edge L n' k' l' → ComplexMatrix2) → ℝ}
    (hF : ∀ V ∈ N, F' (transportTotal e V) = F V) {x : Edge L n k l → ComplexMatrix2}
    {x' : Edge L n' k' l' → ComplexMatrix2} (hx : transportTotal e x = x')
    {S S' : Type} {ι : S → Edge L n k l → ComplexMatrix2}
    {ι' : S' → Edge L n' k' l' → ComplexMatrix2} {f : S → S'}
    (hf : ∀ s, ι' (f s) = transportTotal e (ι s)) {Q' : S' → ℝ}
    (hQ : (fieldCurveData L n' k' l').IsHessianFormAt ι' N' F' x' Q') :
    (fieldCurveData L n k l).IsHessianFormAt ι N F x (Q' ∘ f) := by
  intro I γ s hc hm h0 ht
  have h := hQ I (fun t => transportTotal e (γ t)) (f s) (isTwiceDiffCurve_transport he hc)
    (fun t ht' => hN (hm ht')) (by rw [h0, hx])
    (by rw [tangent_transport he, ht, hf])
  have hI : I ∈ 𝓝 (0 : ℝ) := hc.1.1.1.mem_nhds hc.1.1.2.2
  have hev : (fun t => F' (transportTotal e (γ t))) =ᶠ[𝓝 0] fun t => F (γ t) :=
    eventually_of_mem hI fun t ht' => hF _ (hm ht')
  rw [Function.comp_apply, h, hev.deriv.deriv_eq]
theorem isHessianFormAt_hessianForm_of_exists
    {R : CurveData (Edge L n k l → ComplexMatrix2) (Edge L n k l → ComplexMatrix2)}
    {S : Type} [AddCommGroup S] [Module ℝ S] {ι : S → Edge L n k l → ComplexMatrix2}
    {N : Set (Edge L n k l → ComplexMatrix2)} {F : (Edge L n k l → ComplexMatrix2) → ℝ}
    {x : Edge L n k l → ComplexMatrix2}
    {Q : QuadraticForm ℝ S} (hQ : R.IsHessianFormAt ι N F x Q) :
    R.IsHessianFormAt ι N F x (R.hessianForm ι N F x) :=
  Classical.epsilon_spec (p := fun Q : QuadraticForm ℝ S => R.IsHessianFormAt ι N F x Q) ⟨Q, hQ⟩
theorem hasPosDefHessian_image (he : PreservesEdges e) {N : Set (Edge L n k l → ComplexMatrix2)}
    {F : (Edge L n k l → ComplexMatrix2) → ℝ} {F' : (Edge L n' k' l' → ComplexMatrix2) → ℝ}
    (hF : ∀ V ∈ N, F' (transportTotal e V) = F V) {x : Edge L n k l → ComplexMatrix2}
    (hH : (fieldCurveData L n k l).HasUniqueHessianAt N F x)
    (hP : HasPosDefHessian N F x) :
    HasPosDefHessian (transportTotal e '' N) F' (transportTotal e x) := by
  set N' := transportTotal e '' N with hN'
  set x' := transportTotal e x with hx'
  have hmap : MapsTo (transportTotal e) N N' := fun V hV => mem_image_of_mem _ hV
  have hback : MapsTo (transportTotal e.symm) N' N := by
    rintro _ ⟨V, hV, rfl⟩
    rwa [transportTotal_symm_transportTotal]
  have hxb : transportTotal e.symm x' = x := transportTotal_symm_transportTotal e x
  have hFb : ∀ V' ∈ N', F (transportTotal e.symm V') = F' V' := by
    rintro _ ⟨V, hV, rfl⟩
    rw [transportTotal_symm_transportTotal, hF V hV]
  let f : (fieldCurveData L n k l).tangentSpan N x →ₗ[ℝ]
      (fieldCurveData L n' k' l').tangentSpan N' x' :=
    (transportLinear e).restrict fun v hv => transport_mem_tangentSpan he hmap rfl hv
  let g : (fieldCurveData L n' k' l').tangentSpan N' x' →ₗ[ℝ]
      (fieldCurveData L n k l).tangentSpan N x :=
    (transportLinear e.symm).restrict fun v hv => transport_mem_tangentSpan he.symm hback hxb hv
  have hfg : ∀ v, f (g v) = v := fun v => Subtype.ext (by
    change transportTotal e (transportTotal e.symm (v : Edge L n' k' l' → ComplexMatrix2)) = v
    funext b
    simp [transportTotal])
  obtain ⟨Q₀, hQ₀, huniq⟩ := hH
  set Q := (fieldCurveData L n k l).hessianForm
    (S := (fieldCurveData L n k l).tangentSpan N x) Subtype.val N F x with hQdef
  have hQ : (fieldCurveData L n k l).IsHessianFormAt Subtype.val N F x Q :=
    isHessianFormAt_hessianForm_of_exists hQ₀
  have hQ' : (fieldCurveData L n' k' l').IsHessianFormAt Subtype.val N' F' x' (Q.comp g) :=
    isHessianFormAt_of_transport (ι := Subtype.val) (ι' := Subtype.val) (f := g) he.symm hback
      hFb hxb (fun _ => rfl) hQ
  set H := (fieldCurveData L n' k' l').hessianForm
    (S := (fieldCurveData L n' k' l').tangentSpan N' x') Subtype.val N' F' x' with hHdef
  have hHp : (fieldCurveData L n' k' l').IsHessianFormAt Subtype.val N' F' x' H :=
    isHessianFormAt_hessianForm_of_exists hQ'
  have hHf : (fieldCurveData L n k l).IsHessianFormAt Subtype.val N F x (H.comp f) :=
    isHessianFormAt_of_transport (ι := Subtype.val) (ι' := Subtype.val) (f := f) he hmap hF rfl
      (fun _ => rfl) hHp
  have hEq : H.comp f = Q := (huniq _ hHf).trans (huniq _ hQ).symm
  intro v hv
  have hgv : g v ≠ 0 := fun h0 => hv (by rw [← hfg v, h0, map_zero])
  have hpos : 0 < Q (g v) := hP _ hgv
  rw [← hEq] at hpos
  simpa [QuadraticMap.comp_apply, hfg] using hpos
theorem holds (h₁ : ScalingPropertiesStatement)
    (h₂ : RestrictionHessian.Statement)
    (h₃ : AnalyticIsC2OnSubsetsStatement) :
    Statement := by
  intro L n k j hL hj hS hn l hl U N F F' hF hN hNU hFF x hx hP
  have hat := ((h₁ L k j hS hj).1 n hn).atLevel l hl
  have keeps : PreservesEdges (scaleEdge (n := n) hL hj l) :=
    { orientation_iff := fun b => by
        have himg := hat.image_positive
        constructor
        · intro hb
          have hmem : scaleEdge (n := n) hL hj l b ∈
              scaleEdge (n := n) hL hj l '' {b | b.IsPositivelyOriented} := by
            rw [himg]
            exact hb
          obtain ⟨b', hb', hE⟩ := hmem
          rw [← (scaleEdge (n := n) hL hj l).injective hE]
          exact hb'
        · intro hb
          have hmem : scaleEdge (n := n) hL hj l b ∈
              scaleEdge (n := n) hL hj l '' {b | b.IsPositivelyOriented} :=
            mem_image_of_mem _ hb
          rw [himg] at hmem
          exact hmem
      map_opposite := hat.edge_opposite }
  obtain ⟨_, hM⟩ := hN.2
  have hC2 := h₃ L n k l hS hn (hl.trans hj) U N F hF hNU
  have hH := (h₂.2 L n k l N N F hN hN subset_rfl hC2).2.2.1 x hx
  exact hasPosDefHessian_image keeps hFF hH hP
end YangMills.Construction.Tower.HessianScaling
end
