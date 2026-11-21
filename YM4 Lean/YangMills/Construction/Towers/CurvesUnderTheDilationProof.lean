import YangMills.Construction.Towers.CurvesUnderTheDilation
import YangMills.Construction.Towers.PropertiesOfTheDilationOfATower
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.Tower
namespace EdgeTransport
variable {L n k i n₂ k₂ i₂ : ℕ}
structure PreservesOrientation (e : Edge L n k i ≃ Edge L n₂ k₂ i₂) : Prop where
  orientation_iff : ∀ b, (e b).IsPositivelyOriented ↔ b.IsPositivelyOriented
  map_opposite : ∀ b, e b.opposite = (e b).opposite
theorem PreservesOrientation.symm {e : Edge L n k i ≃ Edge L n₂ k₂ i₂}
    (he : PreservesOrientation e) : PreservesOrientation e.symm where
  orientation_iff b := by rw [← he.orientation_iff, e.apply_symm_apply]
  map_opposite b := by
    apply e.injective
    rw [he.map_opposite, e.apply_symm_apply, e.apply_symm_apply]
theorem transportTotal_symm_transportTotal (e : Edge L n k i ≃ Edge L n₂ k₂ i₂)
    (f : Edge L n k i → Matrices.ComplexMatrix2) : transportTotal e.symm (transportTotal e f) = f := by
  funext x
  simp [transportTotal]
theorem image_symm_image (e : Edge L n k i ≃ Edge L n₂ k₂ i₂)
    (S : Set (Edge L n k i → Matrices.ComplexMatrix2)) :
    transportTotal e.symm '' (transportTotal e '' S) = S := by
  rw [image_image]
  simp only [transportTotal_symm_transportTotal, image_id']
def transportLinear (e : Edge L n k i ≃ Edge L n₂ k₂ i₂) :
    (Edge L n k i → Matrices.ComplexMatrix2) →ₗ[ℝ] Edge L n₂ k₂ i₂ → Matrices.ComplexMatrix2 where
  toFun := transportTotal e
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem isCurve_transport {e : Edge L n k i ≃ Edge L n₂ k₂ i₂} (he : PreservesOrientation e)
    {I : Set ℝ} {γ : ℝ → Edge L n k i → Matrices.ComplexMatrix2}
    (h : (fieldCurveData L n k i).IsCurve I γ) :
    (fieldCurveData L n₂ k₂ i₂).IsCurve I fun t => transportTotal e (γ t) := by
  obtain ⟨hI, hm, hd⟩ := h
  refine ⟨hI, fun t ht => ⟨fun b _ => (hm ht).1 _ (mem_univ _), fun b _ => ?_⟩, fun b hb => ?_⟩
  · change γ t (e.symm b.opposite) = (γ t (e.symm b))⁻¹
    rw [he.symm.map_opposite]
    exact (hm ht).2 _ (mem_univ _)
  · exact hd (e.symm b) ((he.symm.orientation_iff b).2 hb)
theorem curveTangent_transport {e : Edge L n k i ≃ Edge L n₂ k₂ i₂} (he : PreservesOrientation e)
    (γ : ℝ → Edge L n k i → Matrices.ComplexMatrix2) :
    curveTangent (fun t => transportTotal e (γ t)) = transportTotal e (curveTangent γ) := by
  funext b
  have hp := he.symm.orientation_iff b
  simp only [curveTangent, extendOddly, transportTotal, Function.comp]
  by_cases h : b.IsPositivelyOriented
  · rw [if_pos h, if_pos (hp.2 h)]
  · rw [if_neg h, if_neg (mt hp.1 h), he.symm.map_opposite]
theorem transport_mem_tangentSpan {e : Edge L n k i ≃ Edge L n₂ k₂ i₂} (he : PreservesOrientation e)
    {N : Set (Edge L n k i → Matrices.ComplexMatrix2)} {x B : Edge L n k i → Matrices.ComplexMatrix2}
    (hB : B ∈ (fieldCurveData L n k i).tangentSpan N x) :
    transportTotal e B ∈
      (fieldCurveData L n₂ k₂ i₂).tangentSpan (transportTotal e '' N) (transportTotal e x) := by
  have hle : ((fieldCurveData L n k i).tangentSpan N x).map (transportLinear e) ≤
      (fieldCurveData L n₂ k₂ i₂).tangentSpan (transportTotal e '' N) (transportTotal e x) := by
    rw [Geometry.CurveData.tangentSpan, Submodule.map_span]
    apply Submodule.span_mono
    rintro _ ⟨v, ⟨I, γ, hγ, hm, h0, rfl⟩, rfl⟩
    exact ⟨I, fun t => transportTotal e (γ t), isCurve_transport he hγ,
      fun t ht => mem_image_of_mem _ (hm ht), congrArg _ h0, curveTangent_transport he γ⟩
  exact hle (Submodule.mem_map_of_mem hB)
theorem isCriticalOn_transport {e : Edge L n k i ≃ Edge L n₂ k₂ i₂} (he : PreservesOrientation e)
    {N : Set (Edge L n k i → Matrices.ComplexMatrix2)} {x : Edge L n k i → Matrices.ComplexMatrix2}
    {F : (Edge L n k i → Matrices.ComplexMatrix2) → ℝ}
    {F' : (Edge L n₂ k₂ i₂ → Matrices.ComplexMatrix2) → ℝ}
    (hF : ∀ V ∈ N, F' (transportTotal e V) = F V)
    (h : (fieldCurveData L n k i).IsCriticalOn N F x) :
    (fieldCurveData L n₂ k₂ i₂).IsCriticalOn (transportTotal e '' N) F' (transportTotal e x) := by
  refine ⟨mem_image_of_mem _ h.1, fun I γ hγ hm h0 => ?_⟩
  have hback : ∀ t ∈ I, transportTotal e.symm (γ t) ∈ N := fun t ht => by
    obtain ⟨V, hV, hE⟩ := hm ht
    rw [← hE, transportTotal_symm_transportTotal]
    exact hV
  have hcrit := h.2 I (fun t => transportTotal e.symm (γ t)) (isCurve_transport he.symm hγ) hback
    (by simp only [h0, transportTotal_symm_transportTotal])
  have hI : I ∈ 𝓝 (0 : ℝ) := hγ.1.1.mem_nhds hγ.1.2.2
  have hEq : (fun t => F' (γ t)) =ᶠ[𝓝 0] fun t => F (transportTotal e.symm (γ t)) := by
    filter_upwards [hI] with t ht
    rw [← hF _ (hback t ht)]
    congr 1
    funext b
    simp [transportTotal]
  rw [hEq.deriv_eq]
  exact hcrit
end EdgeTransport
open EdgeTransport in
theorem scaling_preserves_tangents_and_critical_points (hProps : ScalingPropertiesStatement) :
    ScalingPreservesTangentsAndCriticalPoints := by
  intro L n k j hL hj hS hn l hl N x
  have hat := ((hProps L k j hS hj).1 n hn).atLevel l hl
  have he : PreservesOrientation (scaleEdge (n := n) hL hj l) :=
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
            Set.mem_image_of_mem _ hb
          rw [himg] at hmem
          exact hmem
      map_opposite := hat.edge_opposite }
  refine ⟨fun B => ⟨transport_mem_tangentSpan he, fun h => ?_⟩, fun F F' hF => ⟨
    isCriticalOn_transport he hF, fun h => ?_⟩⟩
  · have hback := transport_mem_tangentSpan he.symm h
    rwa [image_symm_image, transportTotal_symm_transportTotal,
      transportTotal_symm_transportTotal] at hback
  · have hback := isCriticalOn_transport he.symm (F := F') (F' := F) (fun V' hV' => by
      obtain ⟨V, hV, rfl⟩ := hV'
      rw [transportTotal_symm_transportTotal, hF V hV]) h
    rwa [image_symm_image, transportTotal_symm_transportTotal] at hback
end YangMills.Construction.Tower
end
