import YangMills.Construction.Geometry.ExpandingTori
import YangMills.Construction.GrowingTori.ClassesOfFunctionsTuplesSeparationAndRadius
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.GrowingTori
namespace Ambient
variable {L : ℕ} (E : Ambient L)
theorem supp_add_subset (g g' : E.Point → ℝ) :
    E.supp (g + g') ⊆ E.supp g ∪ E.supp g' := by
  let _ : TopologicalSpace E.Point := E.topology
  refine closure_minimal (fun x hx => ?_) (IsClosed.union isClosed_closure isClosed_closure)
  by_cases hg : g x = 0
  · refine Or.inr (subset_closure fun hg' => hx ?_)
    simp [hg, hg']
  · exact Or.inl (subset_closure hg)
theorem supp_smul_subset (c : ℝ) (g : E.Point → ℝ) : E.supp (c • g) ⊆ E.supp g := by
  let _ : TopologicalSpace E.Point := E.topology
  refine closure_mono fun x hx hg => hx ?_
  simp [hg]
theorem supp_zero : E.supp (0 : E.Point → ℝ) = ∅ := by
  let _ : TopologicalSpace E.Point := E.topology
  have hempty : {x : E.Point | (0 : E.Point → ℝ) x ≠ 0} = ∅ := by
    ext x
    simp
  simp only [supp, euclidClosure]
  rw [hempty]
  exact closure_empty
theorem isEuclidCompact_supp_of_subset_union {g : E.Point → ℝ} {U V : Set E.Point}
    (hU : E.IsEuclidCompact U) (hV : E.IsEuclidCompact V) (hsub : E.supp g ⊆ U ∪ V) :
    E.IsEuclidCompact (E.supp g) := by
  let _ : TopologicalSpace E.Point := E.topology
  exact IsCompact.of_isClosed_subset (IsCompact.union hU hV) isClosed_closure hsub
def lipSubmodule (S : Set E.Point) : Submodule ℝ (E.Point → ℝ) where
  carrier := E.lipCompact S
  add_mem' := by
    rintro g g' ⟨⟨K, hK, hg⟩, cg, sg⟩ ⟨⟨K', hK', hg'⟩, cg', sg'⟩
    have hsub := E.supp_add_subset g g'
    refine ⟨⟨K + K', add_nonneg hK hK', fun x y => ?_⟩,
      E.isEuclidCompact_supp_of_subset_union cg cg' hsub, hsub.trans (union_subset sg sg')⟩
    calc ‖(g + g') x - (g + g') y‖ = ‖(g x - g y) + (g' x - g' y)‖ := by
          simp only [Pi.add_apply]
          congr 1
          ring
      _ ≤ ‖g x - g y‖ + ‖g' x - g' y‖ := norm_add_le _ _
      _ ≤ _ := by
          rw [add_mul]
          exact add_le_add (hg x y) (hg' x y)
  zero_mem' := by
    refine ⟨⟨0, le_rfl, fun x y => by simp⟩, ?_, ?_⟩
    · rw [supp_zero]
      exact @isCompact_empty _ E.topology
    · rw [supp_zero]
      exact empty_subset _
  smul_mem' := by
    rintro c g ⟨⟨K, hK, hg⟩, cg, sg⟩
    have hsub := E.supp_smul_subset c g
    refine ⟨⟨|c| * K, mul_nonneg (abs_nonneg c) hK, fun x y => ?_⟩,
      E.isEuclidCompact_supp_of_subset_union cg cg (hsub.trans subset_union_left), hsub.trans sg⟩
    calc ‖(c • g) x - (c • g) y‖ = |c| * ‖g x - g y‖ := by
          simp only [Pi.smul_apply, smul_eq_mul, ← mul_sub, norm_mul, Real.norm_eq_abs]
      _ ≤ |c| * (K * E.separation x y) := mul_le_mul_of_nonneg_left (hg x y) (abs_nonneg c)
      _ = _ := by ring
end Ambient
variable (L : ℕ)
def lipTuplesInBall (n : ℕ) (r : ℝ) : Set (Fin n → (Fin 4 → ℝ) → ℝ) :=
  {g | (Ambient.euclidean : Ambient L).IsSeparatedLipTuple g ∧
    ∀ i, (Ambient.euclidean : Ambient L).supp (g i) ⊆ ExpandingTori.openEuclidBall r}
def PairwiseSeparated {n : ℕ} (S : Fin n → Set (Fin 4 → ℝ)) : Prop :=
  ∀ i j, i ≠ j → 0 < (Ambient.euclidean : Ambient L).setDist (S i) (S j)
variable {L}
theorem PairwiseSeparated.disjoint {n : ℕ} {S : Fin n → Set (Fin 4 → ℝ)}
    (hS : PairwiseSeparated L S) {i j : Fin n} (hij : i ≠ j) : Disjoint (S i) (S j) := by
  refine Set.disjoint_left.2 fun x hi hj => (hS i j hij).ne' (nonpos_iff_eq_zero.1 ?_)
  change TestFunctions.setDistR4 (S i) (S j) ≤ 0
  refine (iInf₂_le x hi).trans ((iInf₂_le x hj).trans ?_)
  simp [TorusMetric.euclidNormVec]
theorem comp_perm_mem_lipTuplesInBall {n : ℕ} {r : ℝ} {g : Fin n → (Fin 4 → ℝ) → ℝ}
    (hg : g ∈ lipTuplesInBall L n r) (σ : Equiv.Perm (Fin n)) :
    g ∘ σ ∈ lipTuplesInBall L n r :=
  ⟨⟨hg.1.1, fun i => hg.1.2.1 (σ i), fun i j hij => hg.1.2.2 (σ i) (σ j) (σ.injective.ne hij)⟩,
    fun i => hg.2 (σ i)⟩
theorem mem_lipTuplesInBall_of_pi {n : ℕ} (hn : 2 ≤ n) {r : ℝ}
    {S : Fin n → Set (Fin 4 → ℝ)} (hball : ∀ i, S i ⊆ ExpandingTori.openEuclidBall r)
    (hS : PairwiseSeparated L S)
    (g : (i : Fin n) → (Ambient.euclidean : Ambient L).lipSubmodule (S i)) :
    (fun i => (g i).1) ∈ lipTuplesInBall L n r := by
  refine ⟨⟨by omega, fun i => ?_, fun i j hij => ?_⟩, fun i => (g i).2.2.2.trans (hball i)⟩
  · exact ⟨(g i).2.1, (g i).2.2.1, subset_univ _⟩
  · exact (hS.disjoint hij).mono (g i).2.2.2 (g j).2.2.2
def IsSymmetricOnTuples {n : ℕ} {r : ℝ} (Φ : lipTuplesInBall L n r → ℝ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (g : lipTuplesInBall L n r),
    Φ ⟨g.1 ∘ σ, comp_perm_mem_lipTuplesInBall g.2 σ⟩ = Φ g
def IsMultilinearOnTuples {n : ℕ} (hn : 2 ≤ n) {r : ℝ} (Φ : lipTuplesInBall L n r → ℝ) :
    Prop :=
  ∀ (S : Fin n → Set (Fin 4 → ℝ)) (hball : ∀ i, S i ⊆ ExpandingTori.openEuclidBall r)
    (hS : PairwiseSeparated L S),
    ∃ T : MultilinearMap ℝ (fun i => (Ambient.euclidean : Ambient L).lipSubmodule (S i)) ℝ,
      ∀ g, T g = Φ ⟨fun i => (g i).1, mem_lipTuplesInBall_of_pi hn hball hS g⟩
variable (L)
structure PartialFamily (r : ℝ) where
  radius_pos : 0 < r
  phi : (n : ℕ) → 2 ≤ n → lipTuplesInBall L n r → ℝ
  phi_symm : ∀ (n : ℕ) (hn : 2 ≤ n), IsSymmetricOnTuples (phi n hn)
  phi_multilinear : ∀ (n : ℕ) (hn : 2 ≤ n), IsMultilinearOnTuples hn (phi n hn)
end YangMills.Construction.GrowingTori
end
