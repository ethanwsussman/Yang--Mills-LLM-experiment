import YangMills.Construction.TorusOrFourSpace.DistinctPointsAndProductsOfAdmissibleFamilies
import YangMills.Construction.TorusOrFourSpace.DistributionOfAMemberIsDeterminedAndInvariant
import YangMills.Construction.TorusOrFourSpace.GluingOfTheDistributionsOfAHierarchy
import YangMills.Construction.TorusOrFourSpace.SmallFactsOnLiftsProductsAndDistributions
import YangMills.Construction.TorusOrFourSpace.SmoothRealFunctionsInTheTwoSenses
import YangMills.Construction.TorusOrFourSpace.ThreeKindsOfMapsOfSeveralPoints
import YangMills.Construction.TorusOrFourSpace.ValuesAtTensorsOfSeparatedSmoothTuples
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.PeriodicSpace.Kind.OffDiagDistribUniqueInvariant
theorem isCompactWrt_preimage_of_symm_isometry {X : Type*} (d : X → X → ℝ) {g g' : X → X}
    (hIso : ∀ a b, d (g' a) (g' b) = d a b) (hRight : ∀ x, g (g' x) = x)
    (hLeft : ∀ x, g' (g x) = x) {K : Set X} (hK : MetricNotions.IsCompactWrt d K) :
    MetricNotions.IsCompactWrt d (g ⁻¹' K) := by
  intro 𝒰 hU hc
  have hOpen : ∀ V ∈ (fun U : Set X => g' ⁻¹' U) '' 𝒰, MetricNotions.IsOpenWrt d V := by
    rintro _ ⟨U, hUm, rfl⟩ x hx
    obtain ⟨r, hr, h⟩ := hU U hUm (g' x) hx
    exact ⟨r, hr, fun y hy => h _ (by rwa [hIso])⟩
  have hCover : K ⊆ ⋃₀ ((fun U : Set X => g' ⁻¹' U) '' 𝒰) := by
    intro x hx
    have hx' : g' x ∈ g ⁻¹' K := by
      change g (g' x) ∈ K
      rwa [hRight]
    obtain ⟨U, hUm, hxU⟩ := hc hx'
    exact ⟨g' ⁻¹' U, ⟨U, hUm, rfl⟩, hxU⟩
  obtain ⟨𝒰', hSub, hFin, hCov⟩ :=
    Set.exists_subset_image_finite_and.1 (hK _ hOpen hCover)
  refine ⟨𝒰', hSub, hFin, fun y hy => ?_⟩
  obtain ⟨_, ⟨U, hUm, rfl⟩, hyU⟩ := hCov hy
  refine ⟨U, hUm, ?_⟩
  have : g' (g y) ∈ U := hyU
  rwa [hLeft] at this
theorem actFns_map_values {D : Params} {E : Kind} {n : ℕ+} {Z Z' : Type*} (c : Z → Z')
    (ψ : TupleMap D E n) (f : Fin (n : ℕ) → E.Pt D → Z) :
    ψ.actFns (fun i y => c (f i y)) = fun i y => c (ψ.actFns f i y) := by
  cases ψ <;> rfl
theorem holds
    (gluing : OffDiagDistribGluing)
    (values : SepSmoothTensorValues)
    (points : AdmissibleProductFacts)
    (facts : LiftsProductsDistributions.Statement)
    (maps : TupleMapFacts.Claim)
    (smooth : SmoothIffSmoothAsTuple) : OffDiagDistribUniqueInvariant := by
  intro D E C S hS n hn T hT
  have hUnique : ∀ T' : Tuple.testFns D E (pairwiseDistinct D E n) → ℂ,
      Tuple.IsDistrib T' →
      (∀ f ∈ sepC1Tuples D E (n : ℕ), (∀ i, IsSmoothFn D E (f i)) →
        S.ValueAtTensor hn T' f) → T' = T := by
    intro T' hT' hVal
    have hMem : S.IsOffDiagDistrib hn T' := by
      refine ⟨hT', fun G hG => ?_⟩
      obtain ⟨h, hFam⟩ := hT.2 G hG
      obtain ⟨hOpenAll, hProd, -, -, -⟩ := points D E n
      refine ⟨h, ?_, fun φ hφ => ?_⟩
      · exact ((facts D E).2.2.2.2.2.1 n _ _ (hProd G hG).1 hOpenAll h T' hT').2.1
      · obtain ⟨hSep, hF, -⟩ := hFam.2 φ hφ
        have hSmooth : ∀ i, IsSmoothFn D E (φ i) := fun i => (smooth D E (φ i)).2 (hφ i).1
        obtain ⟨hSep', hF', hVal'⟩ := hVal φ hSep hSmooth
        exact ⟨hSep, hF, hVal'⟩
    exact (gluing D E C S hS n hn).1.unique hMem hT
  refine ⟨hUnique, fun ψ hψ => ?_⟩
  obtain ⟨-, -, ⟨hBij, hIso, hLeft, hRight, hImg⟩, ⟨hSupp, hClass, -, hTest, hAdd, hSmul⟩,
    ⟨hSepψ, -, -, hTensψ⟩⟩ := maps D E n ψ
  obtain ⟨-, -, ⟨-, -, hLeft', -, -⟩, -, ⟨hSep', hSm', -, hTens'⟩⟩ := maps D E n ψ.symm
  have hPts : ψ.symm.symm.actPts = ψ.actPts := by
    funext y
    have := hLeft' (ψ.actPts y)
    rwa [hLeft y] at this
  have hBack : ∀ g : Fin (n : ℕ) → E.Pt D → ℂ,
      ψ.actFns (ψ.symm.actFns g) = g := by
    intro g
    have h1 := (hTensψ (ψ.symm.actFns g)).2
    have h2 := (hTens' (ψ.actFns (ψ.symm.actFns g))).2
    rw [h1] at h2
    have h3 := (hTens' g).2
    rw [← h2, h3]
  have hBackReal : ∀ h : FnTuple D E (n : ℕ), ψ.actFns (ψ.symm.actFns h) = h := by
    intro h
    have h1 := hBack fun i y => ((h i y : ℝ) : ℂ)
    rw [actFns_map_values (fun x : ℝ => (x : ℂ)) ψ.symm h,
      actFns_map_values (fun x : ℝ => (x : ℂ)) ψ] at h1
    funext i y
    exact Complex.ofReal_injective (congrFun (congrFun h1 i) y)
  let Tψ : Tuple.testFns D E (pairwiseDistinct D E n) → ℂ :=
    fun F => T ⟨F.1 ∘ ψ.actPts, hTest F.1 F.2⟩
  have hLin : Tuple.IsComplexLinearForm Tψ := by
    refine ⟨fun F G H hH => ?_, fun c F H hH => ?_⟩
    · refine hT.1.1.1 ⟨_, hTest F.1 F.2⟩ ⟨_, hTest G.1 G.2⟩ ⟨_, hTest H.1 H.2⟩ ?_
      change H.1 ∘ ψ.actPts = F.1 ∘ ψ.actPts + G.1 ∘ ψ.actPts
      rw [hH]
      exact hAdd _ _
    · refine hT.1.1.2 c ⟨_, hTest F.1 F.2⟩ ⟨_, hTest H.1 H.2⟩ ?_
      change H.1 ∘ ψ.actPts = c • (F.1 ∘ ψ.actPts)
      rw [hH]
      exact hSmul _ _
  have hDist : Tuple.IsDistrib Tψ := by
    refine ⟨hLin, fun K hK hKsub => ?_⟩
    have hK' : Tuple.IsCompactT D E (ψ.actPts ⁻¹' K) := by
      refine isCompactWrt_preimage_of_symm_isometry (Tuple.tupleDist D E) (g' := ψ.symm.actPts)
        (fun a b => ?_) hRight hLeft hK
      rw [← hIso, hRight a, hRight b]
    have hK'sub : ψ.actPts ⁻¹' K ⊆ pairwiseDistinct D E n := by
      intro y hy
      have : ψ.actPts y ∈ ψ.actPts '' pairwiseDistinct D E n := by
        rw [hImg]
        exact hKsub hy
      obtain ⟨z, hz, hzy⟩ := this
      rwa [← hBij.1 hzy]
    obtain ⟨ν, c, hb⟩ := hT.1.2 _ hK' hK'sub
    refine ⟨ν, c, fun F hFK => ?_⟩
    have hSub : Tuple.supportT D E (F.1 ∘ ψ.actPts) ⊆ ψ.actPts ⁻¹' K := by
      rw [hSupp]
      exact Set.preimage_mono hFK
    have h1 := hb ⟨_, hTest F.1 F.2⟩ hSub
    rwa [show Tuple.cNorm D E ν (F.1 ∘ ψ.actPts) =
      Tuple.cNorm D E ν F.1 from (hClass ν F.1 (F.2.1 ν)).2] at h1
  have hValψ : ∀ h ∈ sepC1Tuples D E (n : ℕ), (∀ i, IsSmoothFn D E (h i)) →
      S.ValueAtTensor hn Tψ h := by
    intro h hh hsm
    obtain ⟨-, hFh, -⟩ := values D E C S hS n hn T hT h hh hsm
    have hf : ψ.symm.actFns h ∈ sepC1Tuples D E (n : ℕ) := hSep' h hh
    have hfs : ∀ i, IsSmoothFn D E (ψ.symm.actFns h i) := fun i =>
      (smooth D E _).2 (hSm' h (fun j => (smooth D E (h j)).1 (hsm j)) i)
    obtain ⟨hf', hFf, hv⟩ := values D E C S hS n hn T hT _ hf hfs
    refine ⟨hh, hFh, ?_⟩
    have hTensor : Tuple.cutoffTensor D E (ψ.symm.actFns h) =
        Tuple.cutoffTensor D E h ∘ ψ.actPts := by
      have h1 := (hTens' fun i y => ((h i y : ℝ) : ℂ)).1
      rw [hPts, actFns_map_values (fun x : ℝ => (x : ℂ)) ψ.symm h] at h1
      exact h1
    have hInv := hψ ⟨_, hf⟩ (hSepψ _ hf)
    have hT1 : Tψ ⟨_, hFh⟩ = T ⟨_, hFf⟩ := by
      change T _ = T _
      congr 1
      exact Subtype.ext hTensor.symm
    rw [hT1, hv, ← hInv]
    congr 2
    exact Subtype.ext (hBackReal h)
  have hTψ := hUnique Tψ hDist hValψ
  intro F hF
  exact congrFun hTψ F
end YangMills.Construction.PeriodicSpace.Kind.OffDiagDistribUniqueInvariant
