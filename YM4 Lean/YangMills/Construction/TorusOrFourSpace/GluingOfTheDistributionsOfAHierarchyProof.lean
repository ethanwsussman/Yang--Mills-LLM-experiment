import YangMills.Construction.TorusOrFourSpace.FunctionalBoundedInTheSharpNormIsADistributionProof
import YangMills.Construction.TorusOrFourSpace.GluingOfTheDistributionsOfAHierarchy
import YangMills.Construction.TorusOrFourSpace.PartsAtAFamilyWithAnEmptyMember
import YangMills.Construction.TorusOrFourSpace.PartsAtAFamilyWithNoEmptyMember
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind.OffDiagGluing
open Tuple
variable {D : Params} {E : Kind} {n : ℕ+}
theorem isCutoffFamily_mono {G H : Fin (n : ℕ) → Set (E.Pt D)} (hGH : ∀ i, H i ⊆ G i)
    {χ : Fin (n : ℕ) → E.Pt D → ℝ} (h : IsCutoffFamily D E H χ) : IsCutoffFamily D E G χ := by apply _root_.YangMills.Construction.PeriodicSpace.Kind.SharpBoundedParts.isCutoffFamily_mono <;> assumption
theorem restrictDistrib_isBoxDistrib
    (hF : LiftsProductsDistributions.Statement) (S : Hierarchy D E)
    (hn : 2 ≤ (n : ℕ)) {G H : Fin (n : ℕ) → Set (E.Pt D)}
    (hG : Tuple.IsOpenT D E (boxSet D E G))
    (hH : Tuple.IsOpenT D E (boxSet D E H))
    (hGH : ∀ i, H i ⊆ G i) (hsub : boxSet D E H ⊆ boxSet D E G)
    {T₀ : testFns D E (boxSet D E H) → ℂ} (hT₀ : S.IsBoxDistrib hn H T₀)
    {T : testFns D E (boxSet D E G) → ℂ} (hT : S.IsBoxDistrib hn G T) :
    S.IsBoxDistrib hn H (restrictDistrib hsub T) := by
  refine ⟨((hF D E).2.2.2.2.2.1 n _ _ hH hG hsub T hT.1).2.1, fun φ hφ => ?_⟩
  obtain ⟨h1, h2, -⟩ := hT₀.2 φ hφ
  obtain ⟨h3, h4, h5⟩ := hT.2 φ (isCutoffFamily_mono hGH hφ)
  exact ⟨h1, h2, h5⟩
theorem offDiagDistribGluing_holds (hF : LiftsProductsDistributions.Statement)
    (hE : EmptyMemberBoxProperties.Statement)
    (hN : NonemptyMembersBoxProperties.Statement)
    (hO : AdmissibleProductFacts)
    (hGl : Tuple.DistribGluing.Statement) : OffDiagDistribGluing := by
  intro D E C S hS n hn
  obtain ⟨hOpenΩ, hProd, -, hCover, hInter⟩ := hO D E n
  have parts : ∀ (R d : ℝ) (G : Fin (n : ℕ) → Set (E.Pt D)),
      AdmissibleWith D E R d G → S.BoxProperties C hn R d G := by
    intro R d G hG
    by_cases h : ∃ i, G i = ∅
    · exact hE D E C S hS n hn R d G hG h
    · exact hN D E C S hS n hn R d G hG fun i =>
        Set.nonempty_iff_ne_empty.2 fun hi => h ⟨i, hi⟩
  have exU : ∀ G : Fin (n : ℕ) → Set (E.Pt D), Admissible D E G →
      ∃! T, S.IsBoxDistrib hn G T := by
    rintro G ⟨R, d, hG⟩
    exact (parts R d G hG).1
  have ord : ∀ G : Fin (n : ℕ) → Set (E.Pt D), Admissible D E G →
      ∀ T, S.IsBoxDistrib hn G T →
        IsDistribOfOrderLE (5 * (n : ℕ) + 1) T := by
    rintro G ⟨R, d, hG⟩ T hT
    exact ((parts R d G hG).2.2.2 T hT).2.2
  let Γ : Type := {G : Fin (n : ℕ) → Set (E.Pt D) // Admissible D E G}
  let O : Γ → Set (E.Tuple D n) := fun γ => boxSet D E γ.1
  have hΩ : ⋃ γ, O γ = pairwiseDistinct D E n := by
    apply Set.Subset.antisymm
    · exact Set.iUnion_subset fun γ => (hProd γ.1 γ.2).2
    · intro y hy
      obtain ⟨G, hG, hyG⟩ := hCover y hy
      exact Set.mem_iUnion.2 ⟨⟨G, hG⟩, hyG⟩
  have hOopen : ∀ γ, Tuple.IsOpenT D E (O γ) := fun γ => (hProd γ.1 γ.2).1
  choose T hT using fun γ : Γ => (exU γ.1 γ.2).exists
  have hAgree : ∀ (γ γ' : Γ) (F : testFns D E (O γ ∩ O γ')),
      restrictDistrib Set.inter_subset_left (T γ) F =
        restrictDistrib Set.inter_subset_right (T γ') F := by
    intro γ γ' F
    obtain ⟨R, d, hRd⟩ := γ.2
    obtain ⟨hH, hHeq⟩ := hInter R d γ.1 γ'.1 hRd γ'.2
    have hHadm : Admissible D E (memberInter D E γ.1 γ'.1) := ⟨R, d, hH⟩
    have s1 : boxSet D E (memberInter D E γ.1 γ'.1) ⊆
        boxSet D E γ.1 := hHeq.subset.trans Set.inter_subset_left
    have s2 : boxSet D E (memberInter D E γ.1 γ'.1) ⊆
        boxSet D E γ'.1 := hHeq.subset.trans Set.inter_subset_right
    obtain ⟨T₀, hT₀, -⟩ := exU _ hHadm
    have e1 := restrictDistrib_isBoxDistrib hF S hn (hOopen γ) (hProd _ hHadm).1
      (fun i => Set.inter_subset_left) s1 hT₀ (hT γ)
    have e2 := restrictDistrib_isBoxDistrib hF S hn (hOopen γ') (hProd _ hHadm).1
      (fun i => Set.inter_subset_right) s2 hT₀ (hT γ')
    have key : restrictDistrib s1 (T γ) = restrictDistrib s2 (T γ') := (exU _ hHadm).unique e1 e2
    have hFH : F.1 ∈ testFns D E
        (boxSet D E (memberInter D E γ.1 γ'.1)) :=
      ⟨F.2.1, F.2.2.1, F.2.2.2.trans hHeq.superset⟩
    exact congrFun key ⟨F.1, hFH⟩
  obtain ⟨⟨T₁, ⟨hT₁d, hT₁r⟩, hT₁u⟩, hOrd⟩ :=
    hGl D E n (5 * (n : ℕ) + 1) Γ (pairwiseDistinct D E n) O hΩ hOpenΩ hOopen T
      (fun γ => (hT γ).1) hAgree
  have member : ∀ T' : testFns D E (pairwiseDistinct D E n) → ℂ,
      S.IsOffDiagDistrib hn T' → IsDistrib T' ∧
        ∀ γ, restrictDistrib ((Set.subset_iUnion O γ).trans hΩ.subset) T' = T γ := by
    rintro T' ⟨hd, hr⟩
    refine ⟨hd, fun γ => ?_⟩
    obtain ⟨h, hf⟩ := hr γ.1 γ.2
    exact (exU γ.1 γ.2).unique hf (hT γ)
  have hT₁ : S.IsOffDiagDistrib hn T₁ := by
    refine ⟨hT₁d, fun G hG => ⟨(hProd G hG).2, ?_⟩⟩
    have h := hT ⟨G, hG⟩
    rw [← hT₁r ⟨G, hG⟩] at h
    exact h
  refine ⟨⟨T₁, hT₁, fun T' hT' => hT₁u T' (member T' hT')⟩, fun T' hT' => ⟨fun G hG => ?_, ?_⟩⟩
  · obtain ⟨h, hf⟩ := hT'.2 G hG
    exact ⟨h, ord G hG _ hf⟩
  · exact hOrd (fun γ => ord γ.1 γ.2 _ (hT γ)) T' (member T' hT').1 (member T' hT').2
end YangMills.Construction.PeriodicSpace.Kind.OffDiagGluing
