import YangMills.Construction.Torus.MultilinearOnSeparatedTuplesSaidByProducts
import Mathlib
set_option autoImplicit false
open Function Set
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
noncomputable section
namespace YangMills.Construction.AmbientPoints.Multilinearity
variable {s : Conventions.StandingParameters} {E : Ambient} {n : ℕ}
theorem positivelySeparated_of_isCompact {K K' : Set (Pt s E)} (hK : IsCompact K)
    (hK' : IsCompact K') (h : Disjoint K K') : PositivelySeparated s E K K' := by
  obtain ⟨r, hr, hlt⟩ := Metric.exists_pos_forall_lt_edist hK hK'.isClosed h
  have hle : (r : ENNReal) ≤ setDist s E K K' := by
    refine le_iInf₂ fun a ha => le_iInf₂ fun b hb => ?_
    have e : edist a b = ENNReal.ofReal (pointDist s E a b) := edist_dist a b
    rw [← e]
    exact (hlt a ha b hb).le
  exact (lt_of_lt_of_le (by exact_mod_cast hr) hle).ne'
def coeTuple {A : Fin n → Set (Pt s E)} (g : (l : Fin n) → c1Submodule (A l)) :
    Fin n → Pt s E → ℝ :=
  fun l => (g l : Pt s E → ℝ)
theorem coeTuple_update {A : Fin n → Set (Pt s E)} (g : (l : Fin n) → c1Submodule (A l))
    (l : Fin n) (z : c1Submodule (A l)) :
    coeTuple (update g l z) = update (coeTuple g) l (z : Pt s E → ℝ) := by
  funext i
  by_cases h : i = l
  · subst h
    simp [coeTuple]
  · simp [coeTuple, update_of_ne h]
theorem apply_update_linearCombination {φ : separatedTuples s E n → ℝ}
    (hφ : IsMultilinearOnSeparated φ) (l : Fin n) (b b' : ℝ)
    (f f' t : separatedTuples s E n) (hag : ∀ i, i ≠ l → f.1 i = f'.1 i)
    (ht : t.1 = update f.1 l (b • f.1 l + b' • f'.1 l)) :
    φ t = b * φ f + b' * φ f' := by
  obtain ⟨t, htm⟩ := t
  simp only at ht
  subst ht
  have h : ((φ ⟨_, htm⟩ : ℝ) : ℂ) = (b : ℂ) * ((φ f : ℝ) : ℂ) + (b' : ℂ) * ((φ f' : ℝ) : ℂ) :=
    hφ l b b' f f' hag htm
  exact_mod_cast h
theorem isTupleMultilinear_of_isMultilinearOnSeparated {φ : separatedTuples s E n → ℝ}
    (hφ : IsMultilinearOnSeparated φ) : IsTupleMultilinear φ := by
  intro A hA
  have hmem : ∀ g : (l : Fin n) → c1Submodule (A l),
      coeTuple g ∈ separatedTuples s E n :=
    fun g => mem_separatedTuples_of_forall_mem_c1 hA fun l => (g l).2
  refine ⟨MultilinearMap.mk' (fun g => φ ⟨coeTuple g, hmem g⟩) ?_ ?_, fun g => rfl⟩
  · intro m i x y
    refine (apply_update_linearCombination hφ i 1 1 ⟨_, hmem (update m i x)⟩
      ⟨_, hmem (update m i y)⟩ ⟨_, hmem (update m i (x + y))⟩ ?_ ?_).trans (by simp)
    · intro j hj
      simp [coeTuple_update, update_of_ne hj]
    · simp [coeTuple_update]
  · intro m i c x
    refine (apply_update_linearCombination hφ i c 0 ⟨_, hmem (update m i x)⟩
      ⟨_, hmem (update m i x)⟩ ⟨_, hmem (update m i (c • x))⟩ (fun _ _ => rfl) ?_).trans
      (by simp)
    simp [coeTuple_update]
def pairSupports (f f' : Fin n → Pt s E → ℝ) (l : Fin n) : Fin n → Set (Pt s E) :=
  update (fun i => tsupport (f i)) l (tsupport (f l) ∪ tsupport (f' l))
theorem pairSupports_self (f f' : Fin n → Pt s E → ℝ) (l : Fin n) :
    pairSupports f f' l l = tsupport (f l) ∪ tsupport (f' l) := by
  simp [pairSupports]
theorem pairSupports_of_ne (f f' : Fin n → Pt s E → ℝ) {l i : Fin n} (h : i ≠ l) :
    pairSupports f f' l i = tsupport (f i) := by
  simp [pairSupports, update_of_ne h]
theorem isCompact_pairSupports (f f' : separatedTuples s E n) (l i : Fin n) :
    IsCompact (pairSupports f.1 f'.1 l i) := by
  by_cases h : i = l
  · subst h
    rw [pairSupports_self]
    exact (f.2.1 i).2.union (f'.2.1 i).2
  · rw [pairSupports_of_ne _ _ h]
    exact (f.2.1 i).2
theorem disjoint_pairSupports {f f' : separatedTuples s E n} {l : Fin n}
    (hag : ∀ i, i ≠ l → f.1 i = f'.1 i) {i j : Fin n} (hij : i ≠ j) :
    Disjoint (pairSupports f.1 f'.1 l i) (pairSupports f.1 f'.1 l j) := by
  have key : ∀ j, j ≠ l →
      Disjoint (tsupport (f.1 l) ∪ tsupport (f'.1 l)) (tsupport (f.1 j)) := by
    intro j hj
    refine disjoint_union_left.2 ⟨f.2.2 hj.symm, ?_⟩
    rw [hag j hj]
    exact f'.2.2 hj.symm
  by_cases hi : i = l
  · subst hi
    rw [pairSupports_self, pairSupports_of_ne _ _ hij.symm]
    exact key j hij.symm
  · by_cases hj : j = l
    · subst hj
      rw [pairSupports_self, pairSupports_of_ne _ _ hij]
      exact (key i hij).symm
    · rw [pairSupports_of_ne _ _ hi, pairSupports_of_ne _ _ hj]
      exact f.2.2 hij
theorem fst_mem_c1_pairSupports (f f' : separatedTuples s E n) (l i : Fin n) :
    f.1 i ∈ c1CompactlySupportedIn (pairSupports f.1 f'.1 l i) := by
  refine ⟨(f.2.1 i).1, (f.2.1 i).2, ?_⟩
  by_cases h : i = l
  · subst h
    rw [pairSupports_self]
    exact subset_union_left
  · rw [pairSupports_of_ne _ _ h]
theorem snd_mem_c1_pairSupports {f f' : separatedTuples s E n} {l : Fin n}
    (hag : ∀ i, i ≠ l → f.1 i = f'.1 i) (i : Fin n) :
    f'.1 i ∈ c1CompactlySupportedIn (pairSupports f.1 f'.1 l i) := by
  refine ⟨(f'.2.1 i).1, (f'.2.1 i).2, ?_⟩
  by_cases h : i = l
  · subst h
    rw [pairSupports_self]
    exact subset_union_right
  · rw [pairSupports_of_ne _ _ h, hag i h]
theorem isMultilinearOnSeparated_of_isTupleMultilinear {φ : separatedTuples s E n → ℝ}
    (hφ : IsTupleMultilinear φ) : IsMultilinearOnSeparated φ := by
  intro l b b' f f' hag h
  have hpos : Pairwise fun i j => PositivelySeparated s E (pairSupports f.1 f'.1 l i)
      (pairSupports f.1 f'.1 l j) := fun i j hij =>
    positivelySeparated_of_isCompact (isCompact_pairSupports f f' l i)
      (isCompact_pairSupports f f' l j) (disjoint_pairSupports hag hij)
  obtain ⟨M, hM⟩ := hφ _ hpos
  let g : (i : Fin n) → c1Submodule (pairSupports f.1 f'.1 l i) :=
    fun i => ⟨f.1 i, fst_mem_c1_pairSupports f f' l i⟩
  let g' : (i : Fin n) → c1Submodule (pairSupports f.1 f'.1 l i) :=
    fun i => ⟨f'.1 i, snd_mem_c1_pairSupports hag i⟩
  have e₂ : update g l (g' l) = g' := by
    funext i
    by_cases hi : i = l
    · subst hi
      simp
    · rw [update_of_ne hi]
      exact Subtype.ext (hag i hi)
  have e₃ : coeTuple (update g l (b • g l + b' • g' l)) =
      update f.1 l (b • f.1 l + b' • f'.1 l) := by
    rw [coeTuple_update]
    rfl
  have v₃ : φ ⟨_, h⟩ = M (update g l (b • g l + b' • g' l)) :=
    (congrArg φ (Subtype.ext e₃.symm)).trans (hM _).symm
  have v₁ : M g = φ f := hM g
  have v₂ : M g' = φ f' := hM g'
  have hval : φ ⟨_, h⟩ = b * φ f + b' * φ f' := by
    rw [v₃, M.map_update_add, M.map_update_smul, M.map_update_smul, update_eq_self, e₂, v₁, v₂]
    simp
  change ((φ ⟨_, h⟩ : ℝ) : ℂ) = (b : ℂ) * ((φ f : ℝ) : ℂ) + (b' : ℂ) * ((φ f' : ℝ) : ℂ)
  exact_mod_cast hval
theorem multilinearOnSeparatedIffProducts_holds : MultilinearOnSeparatedIffProducts :=
  fun _ _ _ _ _ => ⟨isTupleMultilinear_of_isMultilinearOnSeparated,
    isMultilinearOnSeparated_of_isTupleMultilinear⟩
end YangMills.Construction.AmbientPoints.Multilinearity
end
