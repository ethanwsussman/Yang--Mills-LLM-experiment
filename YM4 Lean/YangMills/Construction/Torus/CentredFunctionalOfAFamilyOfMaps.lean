import YangMills.Construction.Cumulants.PartitionsMomentsAndTheCentredFunctionalOfAFamily
import YangMills.Construction.Torus.MultilinearFunctionalsOnSeparatedTuplesOfTorusOrFourSpace
import YangMills.Construction.Torus.SeparatedTuplesFormsAndDistinctPointsOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
noncomputable section
namespace YangMills.Construction.AmbientPoints
variable {s : Conventions.StandingParameters} {E : Ambient}
variable (s E) in
abbrev TupleMapFamily : Type := (n : ℕ) → 2 ≤ n → separatedTuples s E n → ℝ
def mapFamilyBlockFactor (S : TupleMapFamily s E) {n : ℕ} (f : separatedTuples s E n)
    (J : Finset (Fin n)) : ℝ :=
  if h : 2 ≤ J.card then S J.card h (restrictSeparated f J) else 0
def centredOfMaps (S : TupleMapFamily s E) (X : allSeparatedTuples s E) : ℝ :=
  ∑ π ∈ SetPartition.singletonFree X.1.1,
    ∏ J ∈ π.parts, mapFamilyBlockFactor S ⟨X.1.2, X.2⟩ J
theorem mem_separatedTuples_r4_iff {n : ℕ} (f : Fin n → Pt s .euclidean → ℝ) :
    f ∈ separatedTuples s .euclidean n ↔
      (f : Fin n → (Fin 4 → ℝ) → ℝ) ∈
        TestSpaces.disjointSupportTuples (Set.univ : Set (Fin 4 → ℝ)) n := by
  have hc : ∀ g : Pt s .euclidean → ℝ, IsCompact (tsupport g) ↔
      IsCompact (tsupport (X := Fin 4 → ℝ) g) := fun g => by
    have hid : (homeomorphR4 s) '' tsupport g = tsupport (X := Fin 4 → ℝ) g := by
      rw [← tsupport_eq_of_r4 g]
      ext x
      exact ⟨by rintro ⟨y, hy, rfl⟩; exact hy, fun hx => ⟨x, hx, rfl⟩⟩
    rw [← hid, (homeomorphR4 s).isCompact_image]
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun i => ⟨(h₁ i).1, (hc _).1 (h₁ i).2, Set.subset_univ _⟩, fun i j hij => ?_⟩
    have h : Disjoint (tsupport (f i)) (tsupport (f j)) := h₂ hij
    rw [tsupport_eq_of_r4 (f i), tsupport_eq_of_r4 (f j)] at h
    exact h
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun i => ⟨(h₁ i).1, (hc _).2 (h₁ i).2.1⟩, fun i j hij => ?_⟩
    change Disjoint (tsupport (f i)) (tsupport (f j))
    rw [tsupport_eq_of_r4 (f i), tsupport_eq_of_r4 (f j)]
    exact h₂ hij
def toR4Tuple {n : ℕ} (f : separatedTuples s .euclidean n) :
    TestSpaces.SepTupleOfCard n :=
  ⟨f.1, (mem_separatedTuples_r4_iff f.1).1 f.2⟩
theorem centredOfMaps_r4 (S : TupleMapFamily s .euclidean)
    (S' : (n : ℕ) → 2 ≤ n → TestSpaces.SepTupleOfCard n → ℝ)
    (hS : ∀ (n : ℕ) (hn : 2 ≤ n) (f : separatedTuples s .euclidean n),
      S n hn f = S' n hn (toR4Tuple f))
    {n : ℕ} (f : separatedTuples s .euclidean n) :
    centredOfMaps S (toAllSeparated f) =
      TestSpaces.centredOfCumulants S' ⟨n, toR4Tuple f⟩ := by
  rw [TestSpaces.centredOfCumulants_eq_blockProductSum, TestSpaces.blockProductSum]
  change ∑ π ∈ SetPartition.singletonFree n, ∏ J ∈ π.parts,
    mapFamilyBlockFactor S f J = _
  rw [← SetPartition.atLeastTwoPartitions_univ, ← Finset.sum_attach]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [← Finset.prod_attach]
  refine Finset.prod_congr rfl fun J _ => ?_
  rw [mapFamilyBlockFactor,
    dif_pos (SetPartition.two_le_card_of_mem_atLeastTwoPartitions π.2 J.2), hS]
  rfl
end YangMills.Construction.AmbientPoints
