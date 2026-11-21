import YangMills.Construction.TorusOrFourSpace.ApproximationInTheStockAndAChoiceWithTheStabilities
import YangMills.Construction.TorusOrFourSpace.CountableChoicesAndFamiliesOfDenseSets
import YangMills.Construction.TorusOrFourSpace.CountableClosedSaturatedChoicesAndTheirFamily
import YangMills.Construction.TorusOrFourSpace.CountableFamilyOfACountableChoice
import YangMills.Construction.TorusOrFourSpace.DisjointMembersOfTheStock
import YangMills.Construction.TorusOrFourSpace.SpacesC1OfTheStock
import YangMills.Construction.TorusOrFourSpace.TwoFormsOfTheFamilyOnFourSpace
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.EuclideanFamilyForms
open Kind SupportAdapted StableEntriesUnstableFamily
variable (P : Params)
theorem countable_finTuples_of_countable (A : Set (euclidean.Pt P → ℝ)) (hA : A.Countable) :
    {t : Σ n : ℕ, Fin n → euclidean.Pt P → ℝ | ∀ j, t.2 j ∈ A}.Countable := by
  have : Countable A := hA.to_subtype
  refine (Set.countable_range
    (fun t : (Σ n : ℕ, Fin n → A) =>
      (⟨t.1, fun j => (t.2 j : euclidean.Pt P → ℝ)⟩ :
        Σ n : ℕ, Fin n → euclidean.Pt P → ℝ))).mono ?_
  rintro ⟨n, u⟩ hu
  exact ⟨⟨n, fun j => ⟨u j, hu j⟩⟩, rfl⟩
theorem familyWithNil_facts
    (hFam : CountableChoiceFamilyFacts)
    (C : supportStock P euclidean → Set (euclidean.Pt P → ℝ))
    (hC : IsCountableDenseChoice P euclidean C) :
    familyWithNil_subset_and_countable P C := by
  obtain ⟨⟨hStk, -⟩, -, -, hMembers⟩ := hFam P euclidean
  have hEnt : (choiceComponents P euclidean C).Countable := by
    have : Countable (supportStock P euclidean) := hStk.to_subtype
    exact Set.countable_iUnion hC.2
  have hsub : familyWithNil P C ⊆ sepComponentTuplesWithNil P C := by
    refine Set.insert_subset_insert ?_
    rintro ⟨n, u⟩ ⟨hn, Q, hQ⟩
    exact ⟨hn, ((hMembers C hC).2 n u Q ⟨hn, Q, hQ⟩ hQ).1,
      fun j => Set.mem_iUnion.2 ⟨Q j, hQ.2 j⟩⟩
  have hbig : (sepComponentTuplesWithNil P C).Countable := by
    refine (countable_finTuples_of_countable P _ hEnt).mono ?_
    rintro t (rfl | ht)
    · intro j
      exact Fin.elim0 j
    · exact ht.2.2
  exact ⟨hsub, hbig.mono hsub, hbig⟩
theorem tendsto_ofReal_inv_pnat :
    Filter.Tendsto (fun m : ℕ+ => ENNReal.ofReal (1 / ((m : ℕ) : ℝ))) Filter.atTop (nhds 0) := by
  have hlim : Filter.Tendsto (fun m : ℕ+ => (1 : ℝ) / ((m : ℕ) : ℝ)) Filter.atTop (nhds 0) :=
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp tendsto_PNat_val_atTop_atTop
  simpa using ENNReal.tendsto_ofReal hlim
theorem approximatesSepTuples_of_choice
    (hFam : CountableChoiceFamilyFacts)
    (hDis : DisjointStockMembers.Statement)
    (hApx : SupportAdapted.ApproxAndSymmetricChoice)
    (hSp : C1OfStock.Holds)
    (C : supportStock P euclidean → Set (euclidean.Pt P → ℝ))
    (hC : IsCountableDenseChoice P euclidean C) :
    ApproximatesSepTuples P C := by
  intro n hn g hg W hW hgW
  obtain ⟨-, hStkSp, -, -⟩ := hFam P euclidean
  obtain ⟨Q, hQ, hQdis, hQW⟩ := hDis P euclidean n hn
    (fun j => supportQ P euclidean (g j)) W hg.2.1 (fun j k hjk => hg.2.2 j k hjk) hW hgW
  have hSeq : ∀ j, g j ∈ c1VanishingOutside P euclidean (Q j) ∧
      ∃ u : ℕ+ → euclidean.Pt P → ℝ, (∀ k, u k ∈ C ⟨Q j, hQ j⟩) ∧
        (∀ k : ℕ+, SupportAdapted.c1EuclidNorm P euclidean (g j - u k) <
          ENNReal.ofReal (1 / ((k : ℕ) : ℝ))) ∧
        ∀ k, supportQ P euclidean (u k) ⊆ Q j ∧ Q j ⊆ W j := fun j =>
    ((hApx P euclidean).1 C hC (g j) (hg.1 j) (hg.2.1 j) (W j) (hW j) (hgW j)).2
      ⟨Q j, hQ j⟩ (hQW j).1 (hQW j).2
  choose hgQ u hu hclose hsupp using hSeq
  have hmem : ∀ m : ℕ+, (⟨n, fun j => u j m⟩ : Σ n : ℕ, Fin n → euclidean.Pt P → ℝ) ∈
      tupleFamily P euclidean C := fun m =>
    ⟨hn, fun j => ⟨Q j, hQ j⟩, hQdis, fun j => hu j m⟩
  have hlim : ∀ j, Filter.Tendsto
      (fun m : ℕ+ => SupportAdapted.c1EuclidNorm P euclidean (u j m - g j))
      Filter.atTop (nhds 0) := by
    intro j
    have hNrm := (hStkSp (Q j) (hQ j)).2.2.1.1
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_ofReal_inv_pnat (fun _ => zero_le) (fun m => ?_)
    have huV : u j m ∈ c1VanishingOutside P euclidean (Q j) := (hC.1 ⟨Q j, hQ j⟩).1 (hu j m)
    have hsubV : g j - u j m ∈ c1VanishingOutside P euclidean (Q j) := by
      simpa [sub_eq_add_neg] using hNrm.lincomb_mem _ (hgQ j) _ huV 1 (-1)
    have hflip : u j m - g j = (-1 : ℝ) • (g j - u j m) := by
      simp
    have hsymm : SupportAdapted.c1EuclidNorm P euclidean (u j m - g j) =
        SupportAdapted.c1EuclidNorm P euclidean (g j - u j m) := by
      rw [hflip]
      simpa using hNrm.homog _ hsubV (-1)
    rw [hsymm]
    exact (hclose j m).le
  refine ⟨fun m j => u j m, fun m => Or.inr (hmem m), fun m => ?_,
    fun m j => (hsupp j m).1.trans (hQW j).2, hlim, fun j => ?_⟩
  · exact (familyWithNil_facts P hFam C hC).1 (Or.inr (hmem m))
  · have hNrm := (hStkSp (Q j) (hQ j)).2.2.1.1
    have hmul : Filter.Tendsto
        (fun m : ℕ+ => ENNReal.ofReal (40 * P.M) *
          SupportAdapted.c1EuclidNorm P euclidean (u j m - g j))
        Filter.atTop (nhds 0) := by
      simpa using ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (40 * P.M)) (hlim j)
        (Or.inr ENNReal.ofReal_ne_top)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmul
      (fun _ => zero_le) (fun m => ?_)
    have huV : u j m ∈ c1VanishingOutside P euclidean (Q j) := (hC.1 ⟨Q j, hQ j⟩).1 (hu j m)
    have hsubV : u j m - g j ∈ c1VanishingOutside P euclidean (Q j) := by
      simpa [sub_eq_add_neg] using hNrm.lincomb_mem _ huV _ (hgQ j) 1 (-1)
    exact (hSp P euclidean (Q j) (hQ j)).2.2 _ hsubV
theorem existsStrictGap_holds
    (hDense : Kind.CountableDenseFamilies.Statement)
    (hFam : CountableChoiceFamilyFacts)
    (hSp : C1OfStock.Holds)
    (hSat : SaturatedChoices.Claim)
    (hUnst : StableEntriesUnstableFamily.Statement) :
    ExistsStrictGap P := by
  obtain ⟨C, hC, hCl, hCs⟩ := (hSat P euclidean).1
  obtain ⟨-, ⟨⟨a, b, hab⟩, habFacts⟩, -, hOthers⟩ := hUnst P euclidean C hC hCl hCs
  obtain ⟨⟨hC', hEnt, -, hNotSat, -⟩, -, ⟨-, -, -, -, -, hOut⟩, -, -⟩ := hOthers a b hab
  obtain ⟨-, -, hApart, -⟩ := habFacts a b hab
  obtain ⟨⟨hA, ha⟩, -⟩ := hab.1
  obtain ⟨⟨hB, hb⟩, -⟩ := hab.2
  have hreg : ∀ (Q : supportStock P euclidean) (h : euclidean.Pt P → ℝ), h ∈ C Q →
      IsC1Fn P euclidean h ∧ IsCompactQ P euclidean (supportQ P euclidean h) := by
    intro Q h hh
    have hin := (hC.1 Q).1 hh
    exact ⟨hin.1, ((hSp P euclidean Q Q.2).1.2 h hin).1⟩
  have hsub := (familyWithNil_facts P hFam _ hC').1
  have hpairSep : ![a, b] ∈ sepC1Tuples P euclidean 2 := by
    refine ⟨?_, ?_, ?_⟩
    · intro j
      fin_cases j
      · exact (hreg _ _ ha).1
      · exact (hreg _ _ hb).1
    · intro j
      fin_cases j
      · exact (hreg _ _ ha).2
      · exact (hreg _ _ hb).2
    · intro j k hjk
      fin_cases j <;> fin_cases k
      · exact absurd rfl hjk
      · exact hApart
      · exact hApart.symm
      · exact absurd rfl hjk
  have hpairEnt : ∀ j, (![a, b] : Fin 2 → euclidean.Pt P → ℝ) j ∈
      choiceComponents P euclidean (choiceErase P euclidean C a) := by
    intro j
    rw [hEnt]
    fin_cases j
    · exact Set.mem_iUnion.2 ⟨_, ha⟩
    · exact Set.mem_iUnion.2 ⟨_, hb⟩
  refine ⟨choiceErase P euclidean C a, hC', hNotSat,
    (Set.ssubset_iff_of_subset hsub).2 ⟨⟨2, ![a, b]⟩, Or.inr ⟨by norm_num, hpairSep, hpairEnt⟩, ?_⟩,
    C, a, b, hC, hCl, hCs, hab, rfl⟩
  rintro (h | h)
  · exact absurd (congrArg Sigma.fst h) (by simp [nilTuple])
  · refine hOut ?_
    rw [(hDense P euclidean).2.1 _ hC']
    exact h
theorem statement_holds
    (hDense : Kind.CountableDenseFamilies.Statement)
    (hFam : CountableChoiceFamilyFacts)
    (hDis : DisjointStockMembers.Statement)
    (hApx : SupportAdapted.ApproxAndSymmetricChoice)
    (hSp : C1OfStock.Holds)
    (hSat : SaturatedChoices.Claim)
    (hUnst : StableEntriesUnstableFamily.Statement) :
    Statement := by
  intro P
  exact ⟨fun C hC => ⟨((hDense P euclidean).2.1 C hC).symm,
      familyWithNil_facts P hFam C hC,
      approximatesSepTuples_of_choice P hFam hDis hApx hSp C hC⟩,
    existsStrictGap_holds P hDense hFam hSp hSat hUnst⟩
end YangMills.Construction.PeriodicSpace.EuclideanFamilyForms
