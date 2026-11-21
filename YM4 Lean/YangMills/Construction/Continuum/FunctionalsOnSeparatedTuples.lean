import YangMills.Construction.ClusterExpansion.PolymerGraphs
import YangMills.Construction.Continuum.CentredFunctionalOfAFamily
import YangMills.Construction.TestSpaces.PointsAndSeparatedTuples
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
namespace TestSpaces
variable {n : ℕ}
abbrev SepTupleOfCard (n : ℕ) : Type := disjointSupportTuples (Set.univ : Set (Fin 4 → ℝ)) n
abbrev SepTuple : Type := Σ n, SepTupleOfCard n
def sepTupleNil : SepTuple :=
  ⟨0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
theorem sepTuple_ext {m m' : ℕ} (Y : SepTupleOfCard m) (Y' : SepTupleOfCard m') (hm : m = m')
    (hY : ∀ k, Y.1 k = Y'.1 (Fin.cast hm k)) : (⟨m, Y⟩ : SepTuple) = ⟨m', Y'⟩ := by
  subst hm
  exact congrArg _ (Subtype.ext (funext hY))
theorem restrictTuple_mem_disjointSupportTuples {O : Set (Fin 4 → ℝ)}
    {f : Fin n → (Fin 4 → ℝ) → ℝ}
    (hf : f ∈ disjointSupportTuples O n) (J : Finset (Fin n)) :
    SchwingerFunctions.restrictTuple f J ∈ disjointSupportTuples O J.card :=
  ⟨fun _ => hf.1 _, fun _ _ h => hf.2 fun e => h ((J.orderEmbOfFin rfl).injective e)⟩
def sepRestrict (f : SepTupleOfCard n) (J : Finset (Fin n)) : SepTupleOfCard J.card :=
  ⟨SchwingerFunctions.restrictTuple f.1 J, restrictTuple_mem_disjointSupportTuples f.2 J⟩
theorem sepRestrict_empty (f : SepTupleOfCard n) :
    (⟨_, sepRestrict f ∅⟩ : SepTuple) = sepTupleNil :=
  sepTuple_ext _ _ rfl fun k => k.elim0
theorem sepRestrict_univ (f : SepTupleOfCard n) :
    (⟨_, sepRestrict f Finset.univ⟩ : SepTuple) = ⟨n, f⟩ := by
  refine sepTuple_ext _ _ (by simp) fun k => ?_
  have hk : (Finset.univ : Finset (Fin n)).orderEmbOfFin rfl k = Fin.cast (by simp) k :=
    (congrFun (Finset.orderEmbOfFin_unique (s := Finset.univ) rfl (f := Fin.cast (by simp))
      (fun _ => Finset.mem_univ _) fun _ _ h => h) k).symm
  simp only [sepRestrict, SchwingerFunctions.restrictTuple, hk]
def IsMultilinearOnSep (Φ : SepTupleOfCard n → ℝ) : Prop :=
  ∀ (i : Fin n) (a a' : ℝ) (f f' f'' : SepTupleOfCard n),
    (∀ j, j ≠ i → f.1 j = f'.1 j) → f''.1 i = a • f.1 i + a' • f'.1 i →
      (∀ j, j ≠ i → f''.1 j = f.1 j) → Φ f'' = a * Φ f + a' * Φ f'
theorem update_linComb_mem_disjointSupportTuples (i : Fin n) (a a' : ℝ)
    (f f' : SepTupleOfCard n) (hff' : ∀ j, j ≠ i → f.1 j = f'.1 j) :
    Function.update f.1 i (a • f.1 i + a' • f'.1 i) ∈
      disjointSupportTuples (Set.univ : Set (Fin 4 → ℝ)) n := by
  have hsub : tsupport (a • f.1 i + a' • f'.1 i) ⊆ tsupport (f.1 i) ∪ tsupport (f'.1 i) := by
    refine closure_minimal ?_ ((isClosed_tsupport _).union (isClosed_tsupport _))
    intro u hu
    by_contra hn
    simp only [Set.mem_union, not_or] at hn
    exact hu (by simp [image_eq_zero_of_notMem_tsupport hn.1,
      image_eq_zero_of_notMem_tsupport hn.2])
  have hc : a • f.1 i + a' • f'.1 i ∈
      c1CompactSupp (Set.univ : Set (Fin 4 → ℝ)) := by
    obtain ⟨h₁, h₂, -⟩ := f.2.1 i
    obtain ⟨h₃, h₄, -⟩ := f'.2.1 i
    exact ⟨(h₁.const_smul a).add (h₃.const_smul a'),
      (h₂.mono (Function.support_const_smul_subset a _)).add
        (h₄.mono (Function.support_const_smul_subset a' _)), Set.subset_univ _⟩
  have hdis : ∀ j, j ≠ i →
      Disjoint (tsupport (a • f.1 i + a' • f'.1 i)) (tsupport (f.1 j)) := by
    intro j hj
    refine Disjoint.mono_left hsub (Set.disjoint_union_left.2 ⟨f.2.2 hj.symm, ?_⟩)
    rw [hff' j hj]
    exact f'.2.2 hj.symm
  refine ⟨fun j => ?_, fun j j' hjj' => ?_⟩
  · by_cases hj : j = i
    · subst hj
      simpa using hc
    · simpa [Function.update_of_ne hj] using f.2.1 j
  · by_cases hj : j = i
    · subst hj
      have hj' : j' ≠ j := hjj'.symm
      simpa [Function.update_of_ne hj'] using hdis j' hj'
    · by_cases hj' : j' = i
      · subst hj'
        simpa [Function.update_of_ne hj] using (hdis j hj).symm
      · simpa [Function.update_of_ne hj, Function.update_of_ne hj'] using f.2.2 hjj'
def IsSepFunctional (σ : SepTuple → ℝ) : Prop :=
  σ sepTupleNil = 1 ∧ ∀ n, 1 ≤ n → IsMultilinearOnSep fun f : SepTupleOfCard n => σ ⟨n, f⟩
def partitionsNoSingletons (E : Type*) [Fintype E] : Finset (Finset (Finset E)) :=
  (ClusterExpansion.SymGraph.partitions E).filter fun P => ∀ B ∈ P, 2 ≤ B.card
theorem partitionsNoSingletons_of_isEmpty (E : Type*) [Fintype E] [IsEmpty E] :
    partitionsNoSingletons E = {∅} := by
  ext P
  simp only [partitionsNoSingletons, ClusterExpansion.SymGraph.partitions,
    ClusterExpansion.SymGraph.IsPartition,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hne, -, -⟩, -⟩
    refine Finset.eq_empty_of_forall_notMem fun B hB => ?_
    obtain ⟨e, -⟩ := hne B hB
    exact isEmptyElim e
  · rintro rfl
    simp [Finset.univ_eq_empty]
theorem partitionsNoSingletons_fin_one : partitionsNoSingletons (Fin 1) = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun P hP => ?_
  simp only [partitionsNoSingletons, ClusterExpansion.SymGraph.partitions,
    ClusterExpansion.SymGraph.IsPartition,
    Finset.mem_filter, Finset.mem_univ, true_and] at hP
  obtain ⟨⟨-, -, hU⟩, h2⟩ := hP
  have h0 := Finset.mem_univ (0 : Fin 1)
  rw [← hU] at h0
  obtain ⟨B, hB, -⟩ : ∃ B ∈ P, (0 : Fin 1) ∈ B := by simpa using h0
  have hcard : B.card ≤ 1 := by simpa using Finset.card_le_univ B
  exact absurd (h2 B hB) (by omega)
theorem partitions_fin_one :
    ClusterExpansion.SymGraph.partitions (Fin 1) = {{Finset.univ}} := by
  have huniv : ∀ B : Finset (Fin 1), B.Nonempty → B = Finset.univ := fun B ⟨e, he⟩ =>
    Finset.eq_univ_of_forall fun k => Subsingleton.elim e k ▸ he
  ext P
  simp only [ClusterExpansion.SymGraph.partitions, ClusterExpansion.SymGraph.IsPartition,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨hne, -, hU⟩
    have h0 := Finset.mem_univ (0 : Fin 1)
    rw [← hU] at h0
    obtain ⟨B, hB, -⟩ : ∃ B ∈ P, (0 : Fin 1) ∈ B := by simpa using h0
    have hBu : Finset.univ ∈ P := huniv B (hne B hB) ▸ hB
    exact Finset.eq_singleton_iff_unique_mem.2 ⟨hBu, fun K hK => huniv K (hne K hK)⟩
  · rintro rfl
    simp
def cumulant (σ : SepTuple → ℝ) (f : SepTupleOfCard n) : ℝ :=
  ∑ P ∈ ClusterExpansion.SymGraph.partitions (Fin n),
    (-1 : ℝ) ^ (P.card - 1) * ((P.card - 1).factorial : ℝ) *
      ∏ B ∈ P, σ ⟨B.card, sepRestrict f B⟩
theorem two_le_card_of_mem_partitionsNoSingletons {E : Type*} [Fintype E]
    {P : Finset (Finset E)} {B : Finset E} (hP : P ∈ partitionsNoSingletons E) (hB : B ∈ P) :
    2 ≤ B.card :=
  (Finset.mem_filter.1 hP).2 B hB
def centredOfCumulants (S : (n : ℕ) → 2 ≤ n → SepTupleOfCard n → ℝ) (f : SepTuple) : ℝ :=
  ∑ P ∈ (partitionsNoSingletons (Fin f.1)).attach, ∏ B ∈ P.1.attach,
    S B.1.card (two_le_card_of_mem_partitionsNoSingletons P.2 B.2) (sepRestrict f.2 B.1)
theorem centredOfCumulants_nil (S : (n : ℕ) → 2 ≤ n → SepTupleOfCard n → ℝ) :
    centredOfCumulants S sepTupleNil = 1 := by
  have h : partitionsNoSingletons (Fin 0) = {∅} := partitionsNoSingletons_of_isEmpty (Fin 0)
  have hmem : (∅ : Finset (Finset (Fin 0))) ∈ partitionsNoSingletons (Fin 0) := by simp [h]
  unfold centredOfCumulants
  refine (Finset.sum_eq_single_of_mem (⟨∅, hmem⟩ : {P // P ∈ partitionsNoSingletons (Fin 0)})
    (Finset.mem_attach _ _) fun P _ hP => ?_).trans
    (Finset.prod_eq_one fun B _ => (Finset.notMem_empty _ B.2).elim)
  exact absurd (Subtype.ext (Finset.mem_singleton.1 ((Finset.ext_iff.1 h P.1).1 P.2))) hP
theorem centredOfCumulants_single (S : (n : ℕ) → 2 ≤ n → SepTupleOfCard n → ℝ)
    (f : SepTupleOfCard 1) : centredOfCumulants S ⟨1, f⟩ = 0 :=
  Finset.sum_eq_zero fun P _ => absurd P.2 (by
    change P.1 ∉ partitionsNoSingletons (Fin 1)
    simp [partitionsNoSingletons_fin_one])
theorem cumulant_single (σ : SepTuple → ℝ) (f : SepTupleOfCard 1) :
    cumulant σ f = σ ⟨1, f⟩ := by
  simp only [cumulant, partitions_fin_one, Finset.sum_singleton, Finset.card_singleton,
    Nat.sub_self, pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul, Finset.prod_singleton]
  rw [sepRestrict_univ]
def centredPart (σ : SepTuple → ℝ) : SepTuple → ℝ :=
  centredOfCumulants fun _ _ f => cumulant σ f
def IsCLinearOnFlat (T : flatSchwartzSet n → ℂ) : Prop :=
  ∀ (a b : ℂ) (φ ψ χ : flatSchwartzSet n), χ.1 = a • φ.1 + b • ψ.1 →
    T χ = a * T φ + b * T ψ
def IsWeightedBounded (T : flatSchwartzSet n → ℂ) : Prop :=
  ∃ (k : ℕ) (c : ℝ), 0 < k ∧ 0 ≤ c ∧ ∀ φ : flatSchwartzSet n,
    ENNReal.ofReal ‖T φ‖ ≤ ENNReal.ofReal c * weightedSeminorm k φ.1
def tensorProdComplex (f : Fin n → (Fin 4 → ℝ) → ℝ) : PointTuple n → ℂ :=
  fun x => (tensorProd f x : ℝ)
def IsSchwingerFamily (σ : SepTuple → ℝ)
    (T : (n : ℕ) → flatSchwartzSet n → ℂ) : Prop :=
  (∀ n, 1 ≤ n → IsCLinearOnFlat (T n) ∧ IsWeightedBounded (T n) ∧
    ∀ f : SepTupleOfCard n, HasSmoothComponents Set.univ f.1 →
      ∀ h : tensorProdComplex f.1 ∈ flatSchwartzSet n, T n ⟨_, h⟩ = σ ⟨n, f⟩) ∧
  ∀ φ : flatSchwartzSet 0, T 0 φ = φ.1 fun i => i.elim0
def GrowthBound (k : ℕ) (c C ϰ : ℝ) (σ : SepTuple → ℝ) : Prop :=
  0 < k ∧ 0 ≤ c ∧ 0 ≤ C ∧ 0 ≤ ϰ ∧ ∃ T, IsSchwingerFamily σ T ∧
    ∀ n, 1 ≤ n → ∀ φ : flatSchwartzSet n,
      ENNReal.ofReal ‖T n φ‖ ≤
        ENNReal.ofReal (c * C ^ n * (n.factorial : ℝ) ^ ϰ) * weightedSeminorm (k * n) φ.1
end TestSpaces
end YangMills.Construction
