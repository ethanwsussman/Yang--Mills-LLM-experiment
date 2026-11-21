import YangMills.Construction.TestFunctions.RationalBoxFamilies
import YangMills.Construction.ToriAtArbitraryCouplings.ClassC1OnASupportIsCompleteProof
import YangMills.Construction.ToriAtArbitraryCouplings.SupportsAreCompactAndCarryTheirClasses
import YangMills.Construction.TorusOrFourSpace.ClassesAreVectorSpacesWithTheSharpNormProof
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.MetricNotions
noncomputable section
namespace YangMills.Construction.ToriAtArbitraryCouplings
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
namespace CompactSupports
section Metric
variable {X : Type*} {d : X → X → ℝ}
theorem closureWrt_subset_of_subset {Q Z : Set X} (hQ : IsClosedWrt d Q) (hZ : Z ⊆ Q) :
    closureWrt d Z ⊆ Q := by
  intro x hx
  by_contra hxQ
  obtain ⟨r, hr, h⟩ := hQ x hxQ
  obtain ⟨y, hy, hxy⟩ := hx r hr
  exact h y hxy (hZ hy)
theorem subset_closureWrt (h0 : ∀ x, d x x = 0) (Z : Set X) : Z ⊆ closureWrt d Z :=
  fun x hx r hr => ⟨x, hx, by rwa [h0]⟩
theorem isClosedWrt_closureWrt (htri : ∀ x y z, d x z ≤ d x y + d y z) (Z : Set X) :
    IsClosedWrt d (closureWrt d Z) := by apply _root_.YangMills.SharedProofs.p11892 <;> assumption
theorem isCompactWrt_of_isClosedWrt_subset {C Q : Set X} (hQ : IsCompactWrt d Q)
    (hC : IsClosedWrt d C) (hCQ : C ⊆ Q) : IsCompactWrt d C := by
  intro 𝒰 hU hcov
  obtain ⟨𝒱, h𝒱, hfin, hsub⟩ := hQ (insert Cᶜ 𝒰)
    (by
      rintro U (rfl | hUmem)
      · exact hC
      · exact hU U hUmem)
    (by
      intro x _
      by_cases hx : x ∈ C
      · obtain ⟨U, hUmem, hxU⟩ := hcov hx
        exact ⟨U, Or.inr hUmem, hxU⟩
      · exact ⟨Cᶜ, Or.inl rfl, hx⟩)
  refine ⟨𝒱 ∩ 𝒰, inter_subset_right, hfin.inter_of_left _, fun x hx => ?_⟩
  obtain ⟨U, hUmem, hxU⟩ := hsub (hCQ hx)
  rcases h𝒱 hUmem with rfl | hU𝒰
  · exact absurd hx hxU
  · exact ⟨U, ⟨hUmem, hU𝒰⟩, hxU⟩
end Metric
variable (s : TorusSide)
theorem pointDist_self (E : Ambient) (x : s.Point E) : s.pointDist E x x = 0 := by
  cases E
  · exact YangMills.Construction.AmbientPoints.torusEuclidNorm_sub_self x
  · exact YangMills.Construction.AmbientPoints.euclidNormVec_sub_self x
theorem pointDist_triangle (E : Ambient) (x y z : s.Point E) :
    s.pointDist E x z ≤ s.pointDist E x y + s.pointDist E y z := by
  cases E
  · exact YangMills.Construction.AmbientPoints.torusEuclidNorm_sub_le x y z
  · exact YangMills.Construction.AmbientPoints.euclidNormVec_sub_le x y z
theorem isCompact_of_isRationalBox {P : Set (Fin 4 → ℝ)} (hP : IsRationalBox P) : IsCompact P := by apply _root_.YangMills.Construction.TestFunctions.IsRatBox.isCompact <;> assumption
theorem continuous_proj : Continuous s.proj :=
  continuous_pi fun μ => (AddCircle.continuous_mk' _).comp (continuous_apply μ)
theorem isCompact_of_mem_torusSupportFamily {Q : Set s.asMirrorData.Torus}
    (hQ : Q ∈ s.torusSupportFamily) : IsCompact Q := by
  obtain ⟨B, hB, hP, rfl⟩ := hQ
  exact hB.isCompact_biUnion fun P hPB =>
    (isCompact_of_isRationalBox (hP P hPB).1).image (continuous_proj s)
theorem isCompact_of_mem_euclidSupportFamily {Q : Set (Fin 4 → ℝ)} (hQ : Q ∈ euclidSupportFamily) :
    IsCompact Q := by apply _root_.YangMills.SharedProofs.p23763 <;> assumption
theorem isCompactWrt_and_isClosedWrt (E : Ambient) {Q : Set (s.Point E)}
    (hQ : Q ∈ s.supportFamily E) : s.IsCompactWrt E Q ∧ s.IsClosedWrt E Q := by
  cases E
  · have : Fact (0 < s.length) := ⟨s.length_pos⟩
    have hc : IsCompact (X := YangMills.Construction.TorusMetric.Torus4 s.length) Q :=
      isCompact_of_mem_torusSupportFamily s hQ
    refine ⟨(TorusSide.isCompactWrt_euclidDistTorus_iff (ℓ := s.length) Q).2 hc, ?_⟩
    have hopen : @IsOpen _ (YangMills.Construction.TorusAnalysis.euclidTopology s.length) Qᶜ := by
      rw [YangMills.Construction.TorusAnalysis.euclidTopology_eq_instTopology]
      exact hc.isClosed.isOpen_compl
    intro x hx
    obtain ⟨r, hr, h⟩ := hopen x hx
    exact ⟨r, hr, fun y hxy => h y
      ((YangMills.Construction.AmbientPoints.torusEuclidNorm_sub_comm (S := s.length) y x).trans_lt hxy)⟩
  · have hc : IsCompact (X := Fin 4 → ℝ) Q := isCompact_of_mem_euclidSupportFamily hQ
    refine ⟨(YangMills.Construction.SeparatedTuplesR4.isCompactWrt_euclid_iff (fun _ _ => rfl) Q).2 hc, ?_⟩
    exact (YangMills.Construction.SeparatedTuplesR4.isOpenWrt_euclid_iff (fun _ _ => rfl) Qᶜ).2
      hc.isClosed.isOpen_compl
theorem statement_holds : Statement := by
  intro s E Q hQ
  obtain ⟨hcompact, hclosed⟩ := isCompactWrt_and_isClosedWrt s E hQ
  refine ⟨hcompact, ?_⟩
  ext f
  constructor
  · rintro ⟨hf, hvan⟩
    have hsupp : s.closedSupport E f ⊆ Q := closureWrt_subset_of_subset hclosed fun x hx => by
      by_contra hxQ
      exact hx (hvan x hxQ)
    exact ⟨hf, isCompactWrt_of_isClosedWrt_subset hcompact
      (isClosedWrt_closureWrt (pointDist_triangle s E) _) hsupp, hsupp⟩
  · rintro ⟨hf, -, hsupp⟩
    refine ⟨hf, fun x hxQ => ?_⟩
    by_contra hne
    exact hxQ (hsupp (subset_closureWrt (pointDist_self s E) _ hne))
end CompactSupports
end YangMills.Construction.ToriAtArbitraryCouplings
end
