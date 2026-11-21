import YangMills.Construction.TorusOrFourSpace.ChartsOfAnAdmissibleFamily
import YangMills.Construction.TorusOrFourSpace.DistanceOpenSetsDerivativesAndTensorsOfSeveralPoints
import YangMills.Construction.TorusOrFourSpace.FiniteSumsOfTensorsAreDenseOnAProduct
import YangMills.Construction.TorusOrFourSpace.MultilinearFormBoundedInTheC1Norms
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind.TensorDensity
open Tuple
theorem apply_eq_zero_of_not_mem (hT : TupleFacts.AllFacts)
    {P : Params} {K : Kind} {U : Set (K.Pt P)} {g : K.Pt P → ℂ}
    (hg : g ∈ singleTestFns P K U) {p : K.Pt P} (hp : p ∉ U) : g p = 0 := by
  by_contra hne
  have hmem : (fun _ => p : K.Tuple P 1) ∈
      Tuple.supportT P K (ofSingle P K g) := by
    intro r hr
    refine ⟨fun _ => p, hne, ?_⟩
    rw [((hT P K 1).2.2.1.2.1 _ _).2 rfl]
    exact hr
  exact hp (hg.2.2 hmem)
theorem tensorSpanDenseOnBoxes_holds (hCh : AdmissibleCharts.Claim)
    (hT : TupleFacts.AllFacts)
    (hF : C1BoundedFormDistribution) : TensorSpanDenseOnBoxes := by
  intro P K n R d U hU hne Φ
  obtain ⟨c, hc⟩ : ∃ c : Fin (n : ℕ) → Fin 4 → ℝ, ∀ i, K.quotMap P (c i) ∈ U i := by
    obtain ⟨x, hx⟩ := (hT P K n).1.1 fun i => (hne i).some
    refine ⟨fun i => x.block i, fun i => ?_⟩
    have h : K.quotMap P (x.block i) = (hne i).some := congrFun hx i
    show K.quotMap P (x.block i) ∈ U i
    rw [h]
    exact (hne i).some_mem
  obtain ⟨hfac, hhom, -, -, hiso, hconv, hfm⟩ := hCh P K n R d U c hU hne hc
  have hV := hfac.2.2.2
  have form := hF P n (2 * R) 0 (by have := hU.radius_pos; linarith) le_rfl
    (fun i => chartSource P K (c i) (U i)) (fun i => (hV i).1)
    (fun i u hu => (hV i).2.2.2.2.2.1 ((hV i).2.2.2.2.1 hu)) (fun _ => (0 : ℝ))
    (by intro g i u v w a b _; simp) (by intro g; simp)
  let Ψ : testFns P euclidean (chartSources P K c U) :=
    ⟨pullback P K c U Φ.1, hiso.1.mapsTo Φ.2⟩
  obtain ⟨hcut, ⟨χ, hχ, hχ1⟩, hdense⟩ := form.1 Ψ
  obtain ⟨Fs, hsum, hlim⟩ := hdense χ (hcut χ hχ hχ1)
  have hpush : ∀ Ψ' ∈ testFns P euclidean (chartSources P K c U),
      pushforward P K c U Ψ' ∈ testFns P K (boxSet P K U) ∧
        pullback P K c U (pushforward P K c U Ψ') = Ψ' := by
    intro Ψ' h
    obtain ⟨Φ', hΦ', rfl⟩ := hiso.1.surjOn h
    exact ⟨by rw [hiso.2.1.1 hΦ']; exact hΦ', hiso.2.1.2 h⟩
  refine ⟨fun t => ⟨pushforward P K c U (Fs t).1, (hpush _ (Fs t).2).1⟩, ?_, ?_⟩
  · intro t
    obtain ⟨m, φ, hφ, he⟩ := hsum t
    have hex : ∀ l i, ∃ g ∈ singleTestFns P K (U i),
        singlePullback P K (c i) (U i) g = φ l i := by
      intro l i
      have h := (hφ l i).1
      rw [← (hfm.1 i).1] at h
      exact h
    choose g hg hgφ using hex
    refine ⟨m, g, hg, ?_⟩
    show pushforward P K c U (Fs t).1 = ∑ k, tensorProd P K (g k)
    have htens : ∀ l, tensorProd P euclidean (φ l) = pullback P K c U (tensorProd P K (g l)) := by
      intro l
      rw [hfm.2.1 (g l) (hg l)]
      congr 1
      funext i
      exact (hgφ l i).symm
    funext y
    by_cases hy : y ∈ boxSet P K U
    · obtain ⟨h, hh, -, -⟩ := hhom
      have hyim : y ∈ prodChart P K c '' chartSources P K c U := by
        refine ⟨(h.symm ⟨y, hy⟩).1, (h.symm ⟨y, hy⟩).2, ?_⟩
        rw [← hh]
        simp
      have hmem := Function.invFunOn_mem hyim
      have heq := Function.invFunOn_eq hyim
      unfold Tuple.pushforward
      rw [Set.indicator_of_mem hy, Function.comp_apply, he, Finset.sum_apply, Finset.sum_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [htens l]
      unfold Tuple.pullback
      rw [Set.indicator_of_mem hmem, Function.comp_apply, heq]
    · have hzero : pushforward P K c U (Fs t).1 y = 0 := by
        unfold Tuple.pushforward
        exact Set.indicator_of_notMem hy _
      rw [hzero, Finset.sum_apply]
      symm
      refine Finset.sum_eq_zero fun l _ => ?_
      obtain ⟨i, hi⟩ : ∃ i, y i ∉ U i := by
        by_contra hall
        exact hy fun i => not_not.mp fun h => hall ⟨i, h⟩
      exact Finset.prod_eq_zero (Finset.mem_univ i) (apply_eq_zero_of_not_mem hT (hg l i) hi)
  · exact (hconv.1 _ Φ Fs Ψ (fun t => ((hpush _ (Fs t).2).2).symm) rfl).2 hlim
end YangMills.Construction.PeriodicSpace.Kind.TensorDensity
