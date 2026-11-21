import YangMills.Construction.Cumulants.NumberOfBlocksAndImagesOfPartitions
import YangMills.Construction.Torus.SeparatedTuplesAndIsometriesOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open ReflectionPositivity.AxisMirror (Ambient)
namespace AmbientPoints
variable {s : Conventions.StandingParameters} {E : Ambient}
theorem PositivelySeparated.disjoint {A B : Set (Pt s E)} (h : PositivelySeparated s E A B) :
    Disjoint A B := by
  rw [Set.disjoint_left]
  intro x hxA hxB
  refine h (le_antisymm ?_ bot_le)
  calc setDist s E A B ≤ ENNReal.ofReal (pointDist s E x x) :=
        iInf₂_le_of_le x hxA (iInf₂_le x hxB)
    _ = 0 := by rw [pointDist_self, ENNReal.ofReal_zero]
def c1Submodule (A : Set (Pt s E)) : Submodule ℝ (Pt s E → ℝ) where
  carrier := c1CompactlySupportedIn A
  zero_mem' := by
    have hz : tsupport (0 : Pt s E → ℝ) = ∅ := by simp [tsupport]
    refine ⟨contDiff_const, ?_, ?_⟩ <;> simp [hz]
  add_mem' := by
    intro u v hu hv
    have hsub : tsupport (u + v) ⊆ tsupport u ∪ tsupport v :=
      closure_minimal
        ((Function.support_add u v).trans
          (Set.union_subset_union (subset_tsupport u) (subset_tsupport v)))
        ((isClosed_tsupport u).union (isClosed_tsupport v))
    exact ⟨hu.1.add hv.1,
      (hu.2.1.union hv.2.1).of_isClosed_subset (isClosed_tsupport _) hsub,
      hsub.trans (Set.union_subset hu.2.2 hv.2.2)⟩
  smul_mem' := by
    intro c u hu
    have hsub : tsupport (c • u) ⊆ tsupport u :=
      closure_mono (Function.support_const_smul_subset c u)
    exact ⟨contDiff_const.smul hu.1,
      hu.2.1.of_isClosed_subset (isClosed_tsupport _) hsub, hsub.trans hu.2.2⟩
theorem mem_separatedTuples_of_forall_mem_c1 {n : ℕ} {A : Fin n → Set (Pt s E)}
    (hA : Pairwise fun i j => PositivelySeparated s E (A i) (A j)) {f : Fin n → Pt s E → ℝ}
    (hf : ∀ i, f i ∈ c1CompactlySupportedIn (A i)) : f ∈ separatedTuples s E n :=
  ⟨fun i => ⟨(hf i).1, (hf i).2.1⟩, fun _ _ hij =>
    (hA hij).disjoint.mono (hf _).2.2 (hf _).2.2⟩
theorem comp_mem_separatedTuples {m n : ℕ} {f : Fin n → Pt s E → ℝ}
    (hf : f ∈ separatedTuples s E n) {e : Fin m → Fin n} (he : Function.Injective e) :
    f ∘ e ∈ separatedTuples s E m :=
  ⟨fun i => hf.1 (e i), fun _ _ hij => hf.2 (he.ne hij)⟩
theorem permuteTuple_mem {n : ℕ} {f : Fin n → Pt s E → ℝ} (hf : f ∈ separatedTuples s E n)
    (σ : Equiv.Perm (Fin n)) : permuteTuple σ f ∈ separatedTuples s E n :=
  comp_mem_separatedTuples hf σ.injective
theorem restrictTuple_mem {n : ℕ} {f : Fin n → Pt s E → ℝ} (hf : f ∈ separatedTuples s E n)
    (J : Finset (Fin n)) : restrictTuple f J ∈ separatedTuples s E J.card :=
  comp_mem_separatedTuples hf (J.orderEmbOfFin rfl).injective
def restrictSeparated {n : ℕ} (f : separatedTuples s E n) (J : Finset (Fin n)) :
    separatedTuples s E J.card :=
  ⟨restrictTuple f.1 J, restrictTuple_mem f.2 J⟩
def IsTupleMultilinear {n : ℕ} (Ψ : separatedTuples s E n → ℝ) : Prop :=
  ∀ (A : Fin n → Set (Pt s E))
    (hA : Pairwise fun i j => PositivelySeparated s E (A i) (A j)),
    ∃ M : MultilinearMap ℝ (fun i => c1Submodule (A i)) ℝ,
      ∀ g : (i : Fin n) → c1Submodule (A i),
        M g = Ψ ⟨fun i => (g i : Pt s E → ℝ),
          mem_separatedTuples_of_forall_mem_c1 hA fun i => (g i).2⟩
def IsTupleSymmetric {n : ℕ} (Ψ : separatedTuples s E n → ℝ) : Prop :=
  ∀ (f : separatedTuples s E n) (σ : Equiv.Perm (Fin n)),
    Ψ ⟨permuteTuple σ f.1, permuteTuple_mem f.2 σ⟩ = Ψ f
def IsTupleInvariant {n : ℕ} (r : Pt s E ≃ Pt s E) (Ψ : separatedTuples s E n → ℝ) :
    Prop :=
  ∀ f : separatedTuples s E n,
    ∃ h : transportTuple r f.1 ∈ separatedTuples s E n, Ψ ⟨transportTuple r f.1, h⟩ = Ψ f
variable (s E) in
structure ConnectedFamily where
  fn : (n : ℕ) → 2 ≤ n → separatedTuples s E n → ℝ
  fn_multilinear : ∀ (n : ℕ) (hn : 2 ≤ n), IsTupleMultilinear (fn n hn)
theorem two_le_card_of_mem_singletonFree {n : ℕ} {π : SetPartition.PartitionsFin n}
    (hπ : π ∈ SetPartition.singletonFree n) {J : Finset (Fin n)} (hJ : J ∈ π.parts) :
    2 ≤ J.card := by
  rw [SetPartition.singletonFree_eq_nonSingletonPartitions] at hπ
  exact (Finset.mem_filter.1 hπ).2 J hJ
namespace ConnectedFamily
variable (S : ConnectedFamily s E)
def blockFactor {n : ℕ} (f : separatedTuples s E n) (J : Finset (Fin n)) : ℝ :=
  if h : 2 ≤ J.card then S.fn J.card h (restrictSeparated f J) else 0
def centred (X : allSeparatedTuples s E) : ℝ :=
  ∑ π ∈ SetPartition.singletonFree X.1.1,
    ∏ J ∈ π.parts, S.blockFactor ⟨X.1.2, X.2⟩ J
end ConnectedFamily
def toAllSeparated {n : ℕ} (f : separatedTuples s E n) : allSeparatedTuples s E :=
  ⟨⟨n, f.1⟩, f.2⟩
def ofLength (σ : allSeparatedTuples s E → ℝ) (n : ℕ) : separatedTuples s E n → ℝ :=
  fun f => σ (toAllSeparated f)
def IsTupleFunctional (σ : allSeparatedTuples s E → ℝ) : Prop :=
  σ ⟨nilTuple s E, nilTuple_mem_allSeparatedTuples⟩ = 1 ∧
    ∀ n, 1 ≤ n → IsTupleMultilinear (ofLength σ n)
def connectedOf (σ : allSeparatedTuples s E → ℝ) (n : ℕ) (f : separatedTuples s E n) : ℝ :=
  ∑ π : SetPartition.PartitionsFin n,
    (-1 : ℝ) ^ (SetPartition.blockCount π - 1) *
      ((SetPartition.blockCount π - 1).factorial : ℝ) *
        ∏ J ∈ π.parts, σ (toAllSeparated (restrictSeparated f J))
def IsSymmetricTupleFunctional (σ : allSeparatedTuples s E → ℝ) : Prop :=
  ∀ n, 1 ≤ n → IsTupleSymmetric (ofLength σ n)
def IsInvariantTupleFunctional (r : Pt s E ≃ Pt s E) (σ : allSeparatedTuples s E → ℝ) : Prop :=
  ∀ n, 1 ≤ n → IsTupleInvariant r (ofLength σ n)
end AmbientPoints
end YangMills.Construction
