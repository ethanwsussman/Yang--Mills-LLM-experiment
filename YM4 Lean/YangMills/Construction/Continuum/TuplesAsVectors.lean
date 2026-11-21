import YangMills.Construction.Continuum.ClassesOfTuples
import YangMills.Construction.Continuum.IsometriesOfFourSpaceAndOfATorusReflectionsAndInducedMaps
import YangMills.Construction.Continuum.ReflectionOfTestFunctionsTensorsAndOrderZero
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.TorusTransport.TupleVectors
open TestFunctionOrders
abbrev FnTuple : Type := AnyTuple (RealFun (Fin 4 → ℝ))
variable (D : TransportData)
abbrev entrySupp (g : RealFun (Fin 4 → ℝ)) : Set (Fin 4 → ℝ) :=
  Domain.euclidean.fnSupport D g
def sepTuples (U : Set (Fin 4 → ℝ)) : Set FnTuple :=
  {nilTuple _} ∪
    ⋃ n : ℕ+, (fun g : Domain.euclidean.FnFamily D n ℝ => (⟨n, g⟩ : FnTuple)) '' sepC1FamiliesIn D n U
abbrev SepTuple (U : Set (Fin 4 → ℝ)) : Type := ↥(sepTuples D U)
theorem nilTuple_mem_sepTuples (U : Set (Fin 4 → ℝ)) : nilTuple _ ∈ sepTuples D U :=
  Or.inl rfl
theorem sepC1FamiliesIn_univ (n : ℕ+) :
    sepC1FamiliesIn D n Set.univ = Domain.euclidean.sepC1Families D n := by
  ext g
  simp [sepC1FamiliesIn, Domain.FamilySupportedIn]
theorem mem_sepTuples_iff (U : Set (Fin 4 → ℝ)) (t : FnTuple) :
    t ∈ sepTuples D U ↔
      (∀ i, Domain.euclidean.LipschitzOn D (t.2 i)) ∧
      (∀ i, Domain.euclidean.IsCompactSubset D (entrySupp D (t.2 i))) ∧
      (Pairwise fun i k => Disjoint (entrySupp D (t.2 i)) (entrySupp D (t.2 k))) ∧
      (∀ i, Domain.euclidean.IsC1On D (t.2 i)) ∧
      ∀ i, entrySupp D (t.2 i) ⊆ U := by
  constructor
  · rintro (rfl | hmem)
    · exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
        fun i => i.elim0⟩
    · obtain ⟨n, g, ⟨⟨hsep, hreg⟩, hsub⟩, rfl⟩ := Set.mem_iUnion.mp hmem
      exact ⟨hsep.lipschitzOn, hsep.isCompact_support, fun i k hik => hsep.pairwise_disjoint i k hik,
        hreg, hsub⟩
  · obtain ⟨m, g⟩ := t
    rintro ⟨hlip, hcpt, hdisj, hreg, hsub⟩
    cases m with
    | zero => exact Or.inl ((fst_eq_zero_iff _).mp rfl)
    | succ m =>
      refine Or.inr (Set.mem_iUnion.mpr ⟨⟨m + 1, Nat.succ_pos m⟩, g, ⟨⟨⟨hlip, hcpt, ?_⟩, hreg⟩, hsub⟩, rfl⟩)
      exact fun i k hik => hdisj hik
theorem sepTuples_mono {U V : Set (Fin 4 → ℝ)} (hUV : U ⊆ V) :
    sepTuples D U ⊆ sepTuples D V := fun t ht => by
  obtain ⟨hlip, hcpt, hdisj, hreg, hsub⟩ := (mem_sepTuples_iff D U t).mp ht
  exact (mem_sepTuples_iff D V t).mpr ⟨hlip, hcpt, hdisj, hreg, fun i => (hsub i).trans hUV⟩
def inclusionMap {U V : Set (Fin 4 → ℝ)} (hUV : U ⊆ V) (g : SepTuple D U) :
    SepTuple D V :=
  ⟨g.1, sepTuples_mono D hUV g.2⟩
def compAny (t : FnTuple) (s : (Fin 4 → ℝ) → Fin 4 → ℝ) : FnTuple :=
  ⟨t.1, familyComp t.2 s⟩
def actAny {s : (Fin 4 → ℝ) → Fin 4 → ℝ} (hs : IsEuclideanMotion s) (t : FnTuple) :
    FnTuple :=
  ⟨t.1, familyAct hs t.2⟩
theorem actAny_nilTuple {s : (Fin 4 → ℝ) → Fin 4 → ℝ} (hs : IsEuclideanMotion s) :
    actAny hs (nilTuple _) = nilTuple _ :=
  (fst_eq_zero_iff _).mp rfl
def tupleAppend (a b : FnTuple) : FnTuple := ⟨a.1 + b.1, Fin.append a.2 b.2⟩
theorem forall_tupleAppend_iff {a b : FnTuple} {P : RealFun (Fin 4 → ℝ) → Prop} :
    (∀ i, P ((tupleAppend a b).2 i)) ↔ (∀ i, P (a.2 i)) ∧ ∀ j, P (b.2 j) := by
  constructor
  · intro hall
    refine ⟨fun i => ?_, fun j => ?_⟩
    · simpa [tupleAppend] using hall (Fin.castAdd _ i)
    · simpa [tupleAppend] using hall (Fin.natAdd _ j)
  · rintro ⟨ha, hb⟩ i
    induction i using Fin.addCases with
    | left i => simpa [tupleAppend] using ha i
    | right j => simpa [tupleAppend] using hb j
def AppendDefined (a b : FnTuple) : Prop :=
  Pairwise fun i k => Disjoint (entrySupp D ((tupleAppend a b).2 i))
    (entrySupp D ((tupleAppend a b).2 k))
variable {D}
theorem appendDefined_iff {U V : Set (Fin 4 → ℝ)} {a b : FnTuple}
    (ha : a ∈ sepTuples D U) (hb : b ∈ sepTuples D V) :
    AppendDefined D a b ↔
      ∀ i j, Disjoint (entrySupp D (a.2 i)) (entrySupp D (b.2 j)) := by
  obtain ⟨-, -, da, -, -⟩ := (mem_sepTuples_iff D U a).mp ha
  obtain ⟨-, -, db, -, -⟩ := (mem_sepTuples_iff D V b).mp hb
  constructor
  · intro hdef i j
    have := hdef (i := Fin.castAdd b.1 i) (j := Fin.natAdd a.1 j) (fun e => by
      have := congrArg Fin.val e
      simp only [Fin.val_castAdd, Fin.val_natAdd] at this
      omega)
    simpa [tupleAppend] using this
  · intro hdef i k hik
    induction i using Fin.addCases with
    | left i =>
      induction k using Fin.addCases with
      | left k => simpa [tupleAppend] using da (fun e => hik (by rw [e]))
      | right k => simpa [tupleAppend] using hdef i k
    | right i =>
      induction k using Fin.addCases with
      | left k => simpa [tupleAppend] using (hdef k i).symm
      | right k => simpa [tupleAppend] using db (fun e => hik (by rw [e]))
theorem tupleAppend_mem_sepTuples {a b : FnTuple} (ha : a ∈ sepTuples D Set.univ)
    (hb : b ∈ sepTuples D Set.univ) (hdef : AppendDefined D a b) :
    tupleAppend a b ∈ sepTuples D Set.univ := by
  obtain ⟨la, ka, -, ca, -⟩ := (mem_sepTuples_iff D _ a).mp ha
  obtain ⟨lb, kb, -, cb, -⟩ := (mem_sepTuples_iff D _ b).mp hb
  refine (mem_sepTuples_iff D _ _).mpr ⟨?_, ?_, hdef, ?_, fun _ => Set.subset_univ _⟩
  · exact forall_tupleAppend_iff (P := fun g => Domain.euclidean.LipschitzOn D g).mpr ⟨la, lb⟩
  · exact forall_tupleAppend_iff
      (P := fun g => Domain.euclidean.IsCompactSubset D (entrySupp D g)).mpr ⟨ka, kb⟩
  · exact forall_tupleAppend_iff (P := fun g => Domain.euclidean.IsC1On D g).mpr ⟨ca, cb⟩
def sepAppend (a b : SepTuple D Set.univ) (hdef : AppendDefined D a.1 b.1) :
    SepTuple D Set.univ :=
  ⟨tupleAppend a.1 b.1, tupleAppend_mem_sepTuples a.2 b.2 hdef⟩
theorem nil_tupleAppend (b : FnTuple) : tupleAppend (nilTuple _) b = b := by
  obtain ⟨m, b⟩ := b
  refine Sigma.ext (Nat.zero_add m) ((Fin.heq_fun_iff (Nat.zero_add m)).mpr fun i => ?_)
  have e : i = Fin.natAdd 0 ⟨i, by have := i.2; omega⟩ := by ext; simp
  exact (congrArg (Fin.append (nilTuple (RealFun (Fin 4 → ℝ))).2 b) e).trans
    (Fin.append_right _ _ _)
theorem tupleAppend_nil (b : FnTuple) : tupleAppend b (nilTuple _) = b := by
  obtain ⟨m, b⟩ := b
  refine Sigma.ext rfl (heq_of_eq (funext fun i => ?_))
  exact Fin.append_left b _ i
variable (D) in
abbrev SepSpan (U : Set (Fin 4 → ℝ)) : Type := SepTuple D U →₀ ℂ
section SepSpan
variable {U : Set (Fin 4 → ℝ)}
def basisVec (g : SepTuple D U) : SepSpan D U := Finsupp.single g 1
variable (D U) in
def sepBasis : Module.Basis (SepTuple D U) ℂ (SepSpan D U) :=
  Finsupp.basisSingleOne
theorem sepBasis_apply (g : SepTuple D U) :
    sepBasis D U g = basisVec g := by
  simp [sepBasis, basisVec]
def linComb {ι : Type*} [Fintype ι] (c : ι → ℂ) (g : ι → SepTuple D U) : SepSpan D U :=
  ∑ b, c b • basisVec (g b)
theorem eq_linComb_support (F : SepSpan D U) :
    F = linComb (ι := F.support) (fun b => F b) fun b => b.1 := by
  rw [linComb, Finset.sum_coe_sort F.support fun b => F b • basisVec b]
  simpa [basisVec, Finsupp.sum] using (Finsupp.sum_single F).symm
def linExtend {W : Type*} [AddCommGroup W] [Module ℂ W] (φ : SepTuple D U → W) :
    SepSpan D U →ₗ[ℂ] W :=
  Finsupp.linearCombination ℂ φ
theorem linExtend_basisVec {W : Type*} [AddCommGroup W] [Module ℂ W]
    (φ : SepTuple D U → W) (g : SepTuple D U) :
    linExtend φ (basisVec g) = φ g := by
  simp [linExtend, basisVec]
theorem linExtend_linComb {W : Type*} [AddCommGroup W] [Module ℂ W]
    (φ : SepTuple D U → W) {ι : Type*} [Fintype ι] (c : ι → ℂ)
    (g : ι → SepTuple D U) :
    linExtend φ (linComb c g) = ∑ b, c b • φ (g b) := by
  simp [linComb, linExtend_basisVec]
def spanInclusion {V : Set (Fin 4 → ℝ)} (hUV : U ⊆ V) : SepSpan D U →ₗ[ℂ] SepSpan D V :=
  linExtend fun g => basisVec (inclusionMap D hUV g)
def conjCoeffs (F : SepSpan D U) : SepSpan D U :=
  F.mapRange (starRingEnd ℂ) (map_zero _)
theorem conjCoeffs_linComb {ι : Type*} [Fintype ι] (c : ι → ℂ) (g : ι → SepTuple D U) :
    conjCoeffs (linComb c g) = linComb (fun b => conj (c b)) g := by
  ext x
  simp only [conjCoeffs, Finsupp.mapRange_apply, linComb, Finsupp.finsetSum_apply, map_sum,
    basisVec, Finsupp.smul_apply, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rcases eq_or_ne (g b) x with rfl | hne <;> simp [*]
end SepSpan
open Classical in
def appendOnBasis (a b : SepTuple D Set.univ) : SepSpan D Set.univ :=
  if hdef : AppendDefined D a.1 b.1 then basisVec (sepAppend a b hdef) else 0
def appendBilin : SepSpan D Set.univ →ₗ[ℂ] SepSpan D Set.univ →ₗ[ℂ] SepSpan D Set.univ :=
  linExtend fun a => linExtend fun b => appendOnBasis a b
theorem appendBilin_basisVec (a b : SepTuple D Set.univ) :
    appendBilin (basisVec a) (basisVec b) = appendOnBasis a b := by
  simp [appendBilin, linExtend_basisVec]
end YangMills.Construction.TorusTransport.TupleVectors
end
