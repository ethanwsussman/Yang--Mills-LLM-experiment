import YangMills.Construction.InfiniteLattice.FactsOfTheSignsAtACutoffProof
import YangMills.Construction.TorusOrFourSpace.ContinuousPartialsUnderTranslationsSumsAndProducts
import YangMills.Construction.TorusOrFourSpace.DerivativesOfFunctionsOfSeveralPoints
import YangMills.Construction.TorusOrFourSpace.DistanceAndLiftsOfSeveralPoints
import YangMills.Construction.TorusOrFourSpace.SumsProductsAndTestFunctionsOfSeveralPoints
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.PeriodicSpace.AlgebraOfTestFns
open Kind MetricNotions
section Metric
variable {X : Type*} (d : X → X → ℝ)
theorem closureWrt_mono {A B : Set X} (hAB : A ⊆ B) : closureWrt d A ⊆ closureWrt d B := by apply _root_.YangMills.Construction.AtCutoff.SignFacts.closureWrt_mono <;> assumption
theorem closureWrt_union_subset (A B : Set X) :
    closureWrt d (A ∪ B) ⊆ closureWrt d A ∪ closureWrt d B := by apply _root_.YangMills.Construction.AtCutoff.SignFacts.closureWrt_union_subset <;> assumption
theorem isClosedWrt_closureWrt (htri : ∀ a b c, d a c ≤ d a b + d b c) (S : Set X) :
    IsClosedWrt d (closureWrt d S) := by apply _root_.YangMills.SharedProofs.p11892 <;> assumption
theorem isCompactWrt_of_isClosedWrt_subset {C S : Set X} (hC : IsCompactWrt d C)
    (hS : IsClosedWrt d S) (hSC : S ⊆ C) : IsCompactWrt d S := by apply _root_.YangMills.SharedProofs.p5019 <;> assumption
theorem isCompactWrt_union {A B : Set X} (hA : IsCompactWrt d A) (hB : IsCompactWrt d B) :
    IsCompactWrt d (A ∪ B) := by apply _root_.YangMills.SharedProofs.p57694 <;> assumption
end Metric
theorem contPartialsUpTo_zero {p : ℕ+} (k : ℕ) :
    Coords.ContPartialsUpTo k (0 : Coords p → ℂ) := by
  induction k with
  | zero => exact continuous_zero
  | succ n ih =>
    refine ⟨continuous_zero, fun j => ⟨fun x => ?_, ?_⟩⟩
    · exact (differentiableAt_const (0 : ℂ) :
        DifferentiableAt ℝ (0 : Coords p → ℂ) x).lineDifferentiableAt
    · have hz : Coords.partialAlong j (0 : Coords p → ℂ) = 0 := by
        funext x
        simp [Coords.partialAlong, lineDeriv]
      rw [hz]
      exact ih
theorem claim_holds
    (hder : TupleDerivatives.Statement)
    (hpart : PartialsAlgebra.Statement)
    (hlift : TupleMetric.QuotientDistanceAndLifts) : Claim := by
  intro D E p
  obtain ⟨⟨hsurj, -⟩, -, ⟨-, hdist0, -, htri⟩, -, -⟩ := hlift D E p
  obtain ⟨hdr, hfin⟩ := hder D E p
  obtain ⟨-, -, hcl⟩ := hpart p
  have hsupp : ∀ (F H : E.Tuple D p → ℂ) (a b : ℂ),
      Tuple.supportT D E (a • F + b • H) ⊆
          Tuple.supportT D E F ∪ Tuple.supportT D E H ∧
        Tuple.supportT D E (F * H) ⊆
          Tuple.supportT D E F ∩ Tuple.supportT D E H := by
    intro F H a b
    refine ⟨?_, Set.subset_inter ?_ ?_⟩
    · refine (closureWrt_mono _ ?_).trans (closureWrt_union_subset _ _ _)
      intro y hy
      by_contra hn
      rw [Set.mem_union, not_or] at hn
      have hF0 : F y = 0 := not_not.1 hn.1
      have hH0 : H y = 0 := not_not.1 hn.2
      exact hy (by simp [hF0, hH0])
    · refine closureWrt_mono _ ?_
      intro y hy hF0
      exact hy (by simp [hF0])
    · refine closureWrt_mono _ ?_
      intro y hy hH0
      exact hy (by simp [hH0])
  have hclass : ∀ (k : ℕ) (F H : E.Tuple D p → ℂ), Tuple.IsClassC D E k F →
      Tuple.IsClassC D E k H →
        (∀ a b : ℂ, Tuple.IsClassC D E k (a • F + b • H)) ∧
        Tuple.IsClassC D E k (F * H) ∧
        Tuple.IsClassC D E k (fun y => ((F y).re : ℂ)) ∧
        Tuple.IsClassC D E k (fun y => ((F y).im : ℂ)) ∧
        ∀ α : CoordIndex p, α.degree ≤ k →
          Tuple.partialDeriv D E α (fun y => ((F y).re : ℂ)) =
              (fun y => ((Tuple.partialDeriv D E α F y).re : ℂ)) ∧
            Tuple.partialDeriv D E α (fun y => ((F y).im : ℂ)) =
              fun y => ((Tuple.partialDeriv D E α F y).im : ℂ) := by
    intro k F H hF hH
    obtain ⟨e1, e2, e3, e4, e5⟩ := hcl k _ _ hF hH
    have hRe : Tuple.IsClassC D E k (fun y => ((F y).re : ℂ)) := e3
    have hIm : Tuple.IsClassC D E k (fun y => ((F y).im : ℂ)) := e4
    refine ⟨fun a b => e1 a b, e2, hRe, hIm, fun α hα => ⟨?_, ?_⟩⟩
    · funext y
      obtain ⟨x, rfl⟩ := hsurj y
      have q1 := congrFun (hdr k _ hRe α hα).2.1 x
      have q2 := congrFun (hdr k _ hF α hα).2.1 x
      have q3 := congrFun (e5 α hα).1 x
      calc Tuple.partialDeriv D E α (fun y => ((F y).re : ℂ))
              (Tuple.proj D E x)
          = Coords.iterPartial α
              ((fun y => ((F y).re : ℂ)) ∘ Tuple.proj D E) x := q1
        _ = ((Coords.iterPartial α (F ∘ Tuple.proj D E) x).re : ℂ) := q3
        _ = ((Tuple.partialDeriv D E α F (Tuple.proj D E x)).re : ℂ) := by
            rw [← q2]
            rfl
    · funext y
      obtain ⟨x, rfl⟩ := hsurj y
      have q1 := congrFun (hdr k _ hIm α hα).2.1 x
      have q2 := congrFun (hdr k _ hF α hα).2.1 x
      have q3 := congrFun (e5 α hα).2 x
      calc Tuple.partialDeriv D E α (fun y => ((F y).im : ℂ))
              (Tuple.proj D E x)
          = Coords.iterPartial α
              ((fun y => ((F y).im : ℂ)) ∘ Tuple.proj D E) x := q1
        _ = ((Coords.iterPartial α (F ∘ Tuple.proj D E) x).im : ℂ) := q3
        _ = ((Tuple.partialDeriv D E α F (Tuple.proj D E x)).im : ℂ) := by
            rw [← q2]
            rfl
  have hsmall : ∀ F G : E.Tuple D p → ℂ,
      Tuple.IsCompactT D E (Tuple.supportT D E G) →
      Tuple.supportT D E F ⊆ Tuple.supportT D E G →
        Tuple.IsCompactT D E (Tuple.supportT D E F) := fun F _ hG hFG =>
    isCompactWrt_of_isClosedWrt_subset _ hG (isClosedWrt_closureWrt _ htri _) hFG
  have hzero : ∀ Ω : Set (E.Tuple D p),
      (0 : E.Tuple D p → ℂ) ∈ Tuple.testFns D E Ω := by
    intro Ω
    have hempty : Tuple.supportT D E (0 : E.Tuple D p → ℂ) = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun y hy => ?_
      obtain ⟨z, hz, -⟩ := hy 1 one_pos
      exact hz rfl
    refine ⟨fun k => contPartialsUpTo_zero k, ?_, ?_⟩
    · rw [hempty]
      exact fun 𝒰 _ _ => ⟨∅, Set.empty_subset _, Set.finite_empty, Set.empty_subset _⟩
    · rw [hempty]
      exact Set.empty_subset _
  have hlin : ∀ (Ω : Set (E.Tuple D p)) (F H : E.Tuple D p → ℂ) (a b : ℂ),
      F ∈ Tuple.testFns D E Ω → H ∈ Tuple.testFns D E Ω →
        a • F + b • H ∈ Tuple.testFns D E Ω := by
    intro Ω F H a b hF hH
    have hsub := (hsupp F H a b).1
    refine ⟨fun k => (hclass k F H (hF.1 k) (hH.1 k)).1 a b, ?_, ?_⟩
    · exact isCompactWrt_of_isClosedWrt_subset _ (isCompactWrt_union _ hF.2.1 hH.2.1)
        (isClosedWrt_closureWrt _ htri _) hsub
    · exact hsub.trans (Set.union_subset hF.2.2 hH.2.2)
  refine ⟨hsupp, hclass, fun Ω _ => ⟨?_, ?_⟩, ?_⟩
  · refine ⟨{ carrier := Tuple.testFns D E Ω
              add_mem' := ?_
              zero_mem' := hzero Ω
              smul_mem' := ?_ }, rfl⟩
    · intro F H hF hH
      have hs := hlin Ω F H 1 1 hF hH
      simpa using hs
    · intro c F hF
      have hs := hlin Ω F F c 0 hF hF
      simpa using hs
  · intro F hF
    obtain ⟨hsm, hK, hΩ⟩ := hF
    have hreSub : Tuple.supportT D E (fun y => ((F y).re : ℂ)) ⊆
        Tuple.supportT D E F := by
      refine closureWrt_mono _ ?_
      intro y hy hFy
      exact hy (by simp [hFy])
    have himSub : Tuple.supportT D E (fun y => ((F y).im : ℂ)) ⊆
        Tuple.supportT D E F := by
      refine closureWrt_mono _ ?_
      intro y hy hFy
      exact hy (by simp [hFy])
    refine ⟨⟨fun k => (hclass k F F (hsm k) (hsm k)).2.2.1, hsmall _ F hK hreSub,
        hreSub.trans hΩ⟩,
      ⟨fun k => (hclass k F F (hsm k) (hsm k)).2.2.2.1, hsmall _ F hK himSub, himSub.trans hΩ⟩,
      fun α => ?_, fun H hH => ?_, fun k => hfin k F (hsm k) hK⟩
    · have hdSub := (hdr α.degree F (hsm _) α le_rfl).2.2.2.2.2
      refine ⟨fun k => ?_, hsmall _ F hK hdSub, hdSub.trans hΩ⟩
      have hs := (hdr (k + α.degree) F (hsm _) α (Nat.le_add_left _ _)).2.2.2.1
      rwa [Nat.add_sub_cancel] at hs
    · have hpSub := ((hsupp H F 0 0).2).trans Set.inter_subset_right
      exact ⟨fun k => (hclass k H F (hH k) (hsm k)).2.1, hsmall _ F hK hpSub, hpSub.trans hΩ⟩
  · ext F
    constructor
    · rintro ⟨-, -, hs⟩
      funext y
      by_contra hy
      have hmem : y ∈ Tuple.supportT D E F :=
        fun ε hε => ⟨y, hy, by rw [(hdist0 y y).2 rfl]; exact hε⟩
      exact hs hmem
    · intro hs
      rw [Set.mem_singleton_iff] at hs
      rw [hs]
      exact hzero _
end YangMills.Construction.PeriodicSpace.AlgebraOfTestFns
