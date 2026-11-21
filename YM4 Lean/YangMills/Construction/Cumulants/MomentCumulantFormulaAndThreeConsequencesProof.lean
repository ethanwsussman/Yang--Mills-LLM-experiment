import YangMills.Construction.Cumulants.GeneratingFunctionOfBoundedRandomVariables
import YangMills.Construction.Cumulants.MomentCumulantFormulaAndThreeConsequences
import YangMills.Construction.Cumulants.MomentsAndCentredMomentsThroughCumulants
import YangMills.Construction.Cumulants.SmallestPartitionsBlocksAndTransportByABijection
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.Cumulants.MomentCumulantFormula
open YangMills.Construction.Probability (IsBoundedRealRV subfamilyCumulant complexExpectation)
open YangMills.Construction.SetPartition (Partitions)
variable {Ω : Type} [MeasurableSpace Ω]
private theorem uniform_bound_of_bounded {n : ℕ} {X : Fin n → Ω → ℝ}
    (hX : ∀ i, IsBoundedRealRV (X i)) : ∃ M : ℝ, 0 < M ∧ ∀ i ω, |X i ω| ≤ M := by
  choose C hC using fun i => (hX i).bounded
  refine ⟨1 + ∑ i, |C i|, by positivity, fun i ω => ?_⟩
  have hle : |C i| ≤ ∑ j, |C j| :=
    Finset.single_le_sum (f := fun j => |C j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have hCi := (hC i ω).trans (le_abs_self _)
  linarith
private theorem mixedPartialLogCumulant_eq_subfamilyCumulant
    (hGen : BoundedVariables.BoundedGeneratingFunctionTheorem)
    (μ : Measure Ω) [IsProbabilityMeasure μ] {k : ℕ} (X : Fin k → Ω → ℝ)
    (hX : ∀ i, IsBoundedRealRV (X i)) (S : Finset (Fin k)) (hS : S.Nonempty) :
    mixedPartialLogCumulant μ X S = subfamilyCumulant μ X S := by
  obtain ⟨M, hM, hMX⟩ := uniform_bound_of_bounded hX
  have hk : 1 ≤ k := by
    obtain ⟨i, _⟩ := hS
    exact Nat.succ_le_of_lt i.pos
  exact (hGen Ω μ k X M hk hX hM hMX).2.2.1.cumulant_eq S hS
private theorem mixedCumulant_congr_cast {n m : ℕ} (h : n = m) (μ : Measure Ω)
    (f : Fin n → Ω → ℝ) (g : Fin m → Ω → ℝ) (hfg : ∀ a, f a = g (Fin.cast h a)) :
    mixedCumulant μ f = mixedCumulant μ g := by
  subst h
  have hfg' : f = g := funext fun a => by simpa using hfg a
  rw [hfg']
private theorem finsetCumulant_restrictTuple (μ : Measure Ω) {k : ℕ} (X : Fin k → Ω → ℝ)
    (S : Finset (Fin k)) (T : Finset (Fin S.card)) :
    finsetCumulant μ (restrictTuple X S) T =
      finsetCumulant μ X (T.map (S.orderEmbOfFin rfl).toEmbedding) := by
  have hcard : T.card = (T.map (S.orderEmbOfFin rfl).toEmbedding).card :=
    (Finset.card_map _).symm
  refine mixedCumulant_congr_cast hcard μ _ _ fun a => ?_
  have huniq := Finset.orderEmbOfFin_unique (s := T.map (S.orderEmbOfFin rfl).toEmbedding) rfl
    (f := fun b => S.orderEmbOfFin rfl (T.orderEmbOfFin rfl (Fin.cast hcard.symm b)))
    (fun b => Finset.mem_map_of_mem _ (Finset.orderEmbOfFin_mem T rfl _))
    (fun b b' hbb => (S.orderEmbOfFin rfl).strictMono ((T.orderEmbOfFin rfl).strictMono hbb))
  have hat := congrFun huniq (Fin.cast hcard a)
  have hcast : Fin.cast hcard.symm (Fin.cast hcard a) = a := Fin.ext rfl
  simp only [hcast] at hat
  exact congrArg X hat
private theorem complexExpectation_ofReal (μ : Measure Ω) (f : Ω → ℝ) :
    complexExpectation μ (fun ω => (f ω : ℂ)) = ((∫ ω, f ω ∂μ : ℝ) : ℂ) :=
  integral_complex_ofReal
private theorem moment_eq_sum_partitions (hMom : MomentsViaCumulants)
    (hPart : SetPartition.Elementary.BasicFacts)
    (μ : Measure Ω) [IsProbabilityMeasure μ] {k : ℕ} (X : Fin k → Ω → ℝ)
    (hX : ∀ i, IsBoundedRealRV (X i)) (S : Finset (Fin k)) :
    complexExpectation μ (fun ω => ((∏ i ∈ S, X i ω : ℝ) : ℂ)) =
      ∑ P : Partitions S, ∏ T ∈ P.parts, finsetCumulant μ X T := by
  have hbase := (hMom Ω μ S.card (restrictTuple X S) fun l => hX _).1
  have hprod : ∀ ω, ∏ l, restrictTuple X S l ω = ∏ i ∈ S, X i ω := fun ω =>
    (Fintype.prod_equiv (S.orderIsoOfFin rfl).toEquiv _ (fun i : S => X i ω) fun _ => rfl).trans
      (Finset.prod_coe_sort S fun i => X i ω)
  let e : (Finset.univ : Finset (Fin S.card)) ≃ S :=
    (Equiv.subtypeUnivEquiv fun _ => Finset.mem_univ _).trans (S.orderIsoOfFin rfl).toEquiv
  have he : ∀ l, (e l : Fin k) = S.orderEmbOfFin rfl l.1 := fun _ => rfl
  have himage : ∀ T, SetPartition.blockImage e T = T.map (S.orderEmbOfFin rfl).toEmbedding := by
    intro T
    ext y
    rw [SetPartition.mem_blockImage, Finset.mem_map]
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact ⟨l.1, hl, (he l).symm⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, Finset.mem_univ a⟩, ha, he _⟩
  have htrans := hPart.2.2.1 (Fin S.card) (Fin k) Finset.univ S e
  have hfactor : ∀ P : Partitions (Finset.univ : Finset (Fin S.card)),
      ∏ T ∈ P.parts, finsetCumulant μ (restrictTuple X S) T =
        ∏ B ∈ SetPartition.partitionImage e P, finsetCumulant μ X B := by
    intro P
    rw [SetPartition.partitionImage, Finset.prod_image (htrans.2 P).1.injOn]
    exact Finset.prod_congr rfl fun T _ => by rw [himage, finsetCumulant_restrictTuple]
  have hlift : ∀ P : Partitions (Finset.univ : Finset (Fin S.card)),
      ∃ Q : Partitions S, Q.parts = SetPartition.partitionImage e P :=
    fun P => htrans.1.mapsTo (Set.mem_univ P)
  choose Ψ hΨ using hlift
  rw [complexExpectation_ofReal]
  simp only [← hprod]
  rw [hbase]
  refine Finset.sum_bij (fun P _ => Ψ P) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro P _ P' _ hPP
    exact htrans.1.injOn (Set.mem_univ _) (Set.mem_univ _) (by rw [← hΨ, ← hΨ, hPP])
  · intro Q _
    obtain ⟨P, _, hP⟩ := htrans.1.surjOn
      (show Q.parts ∈ SetPartition.partitionSets S from ⟨Q, rfl⟩)
    exact ⟨P, Finset.mem_univ _, Finpartition.ext (by rw [hΨ, hP])⟩
  · intro P _
    rw [hfactor, ← hΨ]
private theorem sum_partitions_of_pair {k : ℕ} {i j : Fin k} (hij : i ≠ j)
    (F : Finset (Finset (Fin k)) → ℂ) :
    ∑ P : Partitions ({i, j} : Finset (Fin k)), F P.parts =
      F {{i, j}} + F {{i}, {j}} := by
  have hi : i ∈ ({i, j} : Finset (Fin k)) := by simp
  have hj : j ∈ ({i, j} : Finset (Fin k)) := by simp
  have hmem : ∀ y ∈ ({i, j} : Finset (Fin k)), y = i ∨ y = j := by simp
  let P₁ : Partitions ({i, j} : Finset (Fin k)) :=
    Finpartition.indiscrete (Finset.ne_empty_of_mem hi)
  let P₂ : Partitions ({i, j} : Finset (Fin k)) := ⊥
  have hP₁ : P₁.parts = {{i, j}} := rfl
  have hP₂ : P₂.parts = {{i}, {j}} := by
    rw [Finpartition.parts_bot]
    ext C
    simp
  have hne : P₁ ≠ P₂ := by
    intro hEq
    have hC : ({i, j} : Finset (Fin k)) ∈ P₂.parts := by
      rw [← hEq, hP₁]
      exact Finset.mem_singleton_self _
    rw [hP₂] at hC
    simp only [Finset.mem_insert, Finset.mem_singleton] at hC
    rcases hC with hC | hC
    · exact hij (Finset.mem_singleton.1 (hC ▸ hj)).symm
    · exact hij (Finset.mem_singleton.1 (hC ▸ hi))
  have hcases : ∀ P : Partitions ({i, j} : Finset (Fin k)), P = P₁ ∨ P = P₂ := by
    intro P
    obtain ⟨B, hB, hiB⟩ := P.exists_mem hi
    obtain ⟨B', hB', hjB'⟩ := P.exists_mem hj
    have hcover : ∀ C ∈ P.parts, C = B ∨ C = B' := by
      intro C hC
      obtain ⟨y, hy⟩ := P.nonempty_of_mem_parts hC
      rcases hmem y (P.le hC hy) with rfl | rfl
      · exact Or.inl (P.eq_of_mem_parts hC hB hy hiB)
      · exact Or.inr (P.eq_of_mem_parts hC hB' hy hjB')
    by_cases hBB : B = B'
    · subst hBB
      have hBfull : B = {i, j} := by
        refine Finset.Subset.antisymm (P.le hB) fun y hy => ?_
        rcases hmem y hy with rfl | rfl
        · exact hiB
        · exact hjB'
      refine Or.inl (Finpartition.ext ?_)
      rw [hP₁]
      ext C
      rw [Finset.mem_singleton]
      constructor
      · intro hC
        rcases hcover C hC with rfl | rfl <;> exact hBfull
      · intro hC
        rw [hC.trans hBfull.symm]
        exact hB
    · have hjB : j ∉ B := fun hh => hBB (P.eq_of_mem_parts hB hB' hh hjB')
      have hiB' : i ∉ B' := fun hh => hBB (P.eq_of_mem_parts hB hB' hiB hh)
      have hBi : B = {i} := by
        ext y
        rw [Finset.mem_singleton]
        constructor
        · intro hy
          rcases hmem y (P.le hB hy) with rfl | rfl
          · rfl
          · exact absurd hy hjB
        · rintro rfl
          exact hiB
      have hBj : B' = {j} := by
        ext y
        rw [Finset.mem_singleton]
        constructor
        · intro hy
          rcases hmem y (P.le hB' hy) with rfl | rfl
          · exact absurd hy hiB'
          · rfl
        · rintro rfl
          exact hjB'
      refine Or.inr (Finpartition.ext ?_)
      rw [hP₂]
      ext C
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hC
        rcases hcover C hC with rfl | rfl
        · exact Or.inl hBi
        · exact Or.inr hBj
      · rintro (hC | hC)
        · rw [hC.trans hBi.symm]
          exact hB
        · rw [hC.trans hBj.symm]
          exact hB'
  have huniv : (Finset.univ : Finset (Partitions ({i, j} : Finset (Fin k)))) = {P₁, P₂} := by
    ext P
    simpa using hcases P
  rw [huniv, Finset.sum_pair hne, hP₁, hP₂]
theorem claim_of_generatingFunction_and_moments
    (hGen : BoundedVariables.BoundedGeneratingFunctionTheorem)
    (hMom : MomentsViaCumulants)
    (hPart : SetPartition.Elementary.BasicFacts) :
    Claim := by
  intro Ω _ μ k X hXμ
  obtain ⟨hμ, hX⟩ := hXμ
  have hX' : ∀ i, IsBoundedRealRV (X i) := hX
  have hmoment : ∀ S : Finset (Fin k), complexExpectation μ (fun ω => ((∏ i ∈ S, X i ω : ℝ) : ℂ)) =
      ∑ P : Partitions S, ∏ T ∈ P.parts, mixedPartialLogCumulant μ X T := by
    intro S
    rw [moment_eq_sum_partitions hMom hPart μ X hX' S]
    refine Finset.sum_congr rfl fun P _ => Finset.prod_congr rfl fun T hT => ?_
    exact (mixedPartialLogCumulant_eq_subfamilyCumulant hGen μ X hX' T
      (P.nonempty_of_mem_parts hT)).symm
  have hsingleton : ∀ i : Fin k,
      mixedPartialLogCumulant μ X {i} = complexExpectation μ fun ω => (X i ω : ℂ) := by
    intro i
    rw [mixedPartialLogCumulant_eq_subfamilyCumulant hGen μ X hX' {i}
      (Finset.singleton_nonempty i)]
    have hcard : ({i} : Finset (Fin k)).card = 1 := Finset.card_singleton i
    obtain ⟨M, hM, hMX⟩ := uniform_bound_of_bounded (X := restrictTuple X {i}) fun _ => hX' _
    have hmean := (hGen Ω μ _ (restrictTuple X {i}) M hcard.ge (fun _ => hX' _) hM
      hMX).2.2.2.2.mean hcard ⟨0, by rw [hcard]; exact Nat.one_pos⟩
    have hX0 : restrictTuple X {i} ⟨0, by rw [hcard]; exact Nat.one_pos⟩ = X i :=
      congrArg X (Finset.mem_singleton.1 (Finset.orderEmbOfFin_mem {i} rfl _))
    rw [complexExpectation_ofReal]
    refine Eq.trans hmean ?_
    rw [hX0]
  refine ⟨fun T hT => mixedPartialLogCumulant_eq_subfamilyCumulant hGen μ X hX' T hT, hmoment,
    hsingleton, ?_, ?_⟩
  · intro T c hT
    have hTne : T.Nonempty := Finset.card_pos.1 (by omega)
    have hXc : ∀ i, IsBoundedRealRV (fun ω => X i ω + c i) := by
      intro i
      obtain ⟨C, hC⟩ := (hX' i).bounded
      exact ⟨(hX' i).measurable.add_const _, C + |c i|, fun ω =>
        (abs_add_le _ _).trans (add_le_add (hC ω) le_rfl)⟩
    rw [mixedPartialLogCumulant_eq_subfamilyCumulant hGen μ _ hXc T hTne,
      mixedPartialLogCumulant_eq_subfamilyCumulant hGen μ X hX' T hTne]
    obtain ⟨M, hM, hMX⟩ := uniform_bound_of_bounded (X := restrictTuple X T) fun _ => hX' _
    exact (hGen Ω μ _ (restrictTuple X T) M (by omega) (fun _ => hX' _) hM
      hMX).2.2.2.2.shift hT fun a => c (T.orderEmbOfFin rfl a)
  · intro i j hij
    have hpair := hmoment {i, j}
    rw [sum_partitions_of_pair hij fun Q => ∏ T ∈ Q, mixedPartialLogCumulant μ X T,
      Finset.prod_singleton,
      Finset.prod_pair (fun hEq => hij (Finset.singleton_injective hEq)), hsingleton,
      hsingleton] at hpair
    have hprod : (fun ω => ((∏ l ∈ ({i, j} : Finset (Fin k)), X l ω : ℝ) : ℂ)) =
        fun ω => (X i ω : ℂ) * (X j ω : ℂ) := by
      funext ω
      rw [Finset.prod_pair hij]
      push_cast
      rfl
    rw [hprod] at hpair
    have hcov : mixedPartialLogCumulant μ X {i, j} =
        complexExpectation μ (fun ω => (X i ω : ℂ) * (X j ω : ℂ)) -
          complexExpectation μ (fun ω => (X i ω : ℂ)) *
            complexExpectation μ (fun ω => (X j ω : ℂ)) := by
      rw [hpair]
      ring
    exact ⟨hcov, hcov⟩
end YangMills.Construction.Cumulants.MomentCumulantFormula
