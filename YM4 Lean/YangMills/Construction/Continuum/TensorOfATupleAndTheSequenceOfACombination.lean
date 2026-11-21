import YangMills.Construction.Continuum.OperationsOnFunctionsOfSeveralPoints
import Mathlib
set_option autoImplicit false
open scoped ContDiff
noncomputable section
namespace YangMills.Construction.ConfigSpace
abbrev SeparatedFamilyIn (O : Set (Fin 4 → ℝ)) : Type :=
  Σ q : ℕ, {f : Fin q → (Fin 4 → ℝ) → ℝ // f ∈ separatedFamilies O q}
abbrev UpperFamily : Type := SeparatedFamilyIn upperHalfSpace
theorem mem_separatedFamilies_upperHalfSpace_iff {q : ℕ} (f : Fin q → (Fin 4 → ℝ) → ℝ) :
    f ∈ separatedFamilies upperHalfSpace q ↔
      f ∈ separatedFamilies Set.univ q ∧ ∀ i, tsupport (f i) ⊆ upperHalfSpace := by
  constructor
  · rintro ⟨hC, hsep⟩
    refine ⟨⟨fun i => ?_, hsep⟩, fun i => (mem_realC1CompactIn_iff.1 (hC i)).2.2.2⟩
    obtain ⟨-, hd, hk, -⟩ := mem_realC1CompactIn_iff.1 (hC i)
    exact mem_realC1CompactIn_iff.2 ⟨isOpen_univ, hd, hk, Set.subset_univ _⟩
  · rintro ⟨⟨hC, hsep⟩, hsupp⟩
    refine ⟨fun i => ?_, hsep⟩
    obtain ⟨-, hd, hk, -⟩ := mem_realC1CompactIn_iff.1 (hC i)
    exact mem_realC1CompactIn_iff.2 ⟨isOpen_upperHalfSpace, hd, hk, hsupp i⟩
namespace UpperFamily
def toSeparatedFamily (X : UpperFamily) : SeparatedFamily :=
  ⟨X.1, X.2.1, ((mem_separatedFamilies_upperHalfSpace_iff X.2.1).1 X.2.2).1⟩
def nil : UpperFamily :=
  ⟨0, nilFamily, by rw [separatedFamilies_zero]; rfl⟩
end UpperFamily
abbrev UpperCombination : Type := UpperFamily →₀ ℂ
namespace UpperCombination
def ofFamily (X : UpperFamily) : UpperCombination := Finsupp.single X 1
open Classical in
def reducedForm (F : UpperCombination) : Finset (ℂ × UpperFamily) :=
  F.support.image fun X => (F X, X)
theorem mem_reducedForm_iff (F : UpperCombination) (c : ℂ) (X : UpperFamily) :
    (c, X) ∈ reducedForm F ↔ F X ≠ 0 ∧ c = F X := by
  classical
  simp only [reducedForm, Finset.mem_image, Finsupp.mem_support_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨Y, hY, rfl, rfl⟩
    exact ⟨hY, rfl⟩
  · rintro ⟨h, rfl⟩
    exact ⟨X, h, rfl, rfl⟩
def HasSmoothFamilies (F : UpperCombination) : Prop :=
  ∀ p ∈ reducedForm F, AllSmoothCompact p.2.2.1
end UpperCombination
def familyLength (X : SeparatedFamily) : ℕ := X.1
def entryTensor : {q : ℕ} → (Fin q → (Fin 4 → ℝ) → ℝ) → FnOrScalar q
  | 0, _ => (1 : ℂ)
  | _ + 1, f => tensorRealFamily f
def familyTensor (X : SeparatedFamily) : FnOrScalar (familyLength X) :=
  entryTensor X.2.1
namespace UpperCombination
def familiesOfLength (F : UpperCombination) (q : ℕ) :
    Finset {f : Fin q → (Fin 4 → ℝ) → ℝ // f ∈ separatedFamilies upperHalfSpace q} :=
  F.support.preimage (fun f => (⟨q, f⟩ : UpperFamily))
    fun _ _ _ _ h => eq_of_heq (Sigma.mk.inj_iff.1 h).2
theorem mem_familiesOfLength_iff (F : UpperCombination) (q : ℕ)
    (f : {f : Fin q → (Fin 4 → ℝ) → ℝ // f ∈ separatedFamilies upperHalfSpace q}) :
    f ∈ familiesOfLength F q ↔ F ⟨q, f⟩ ≠ 0 :=
  Finset.mem_preimage.trans Finsupp.mem_support_iff
end UpperCombination
def combinationSequence (F : UpperCombination) (q : ℕ) : FnOrScalar q :=
  ofConfigFn fun x =>
    ∑ f ∈ F.familiesOfLength q, F ⟨q, f⟩ * toConfigFn (entryTensor f.1) x
theorem combinationSequence_succ (F : UpperCombination) (q : ℕ) (x : Config (q + 1)) :
    (show Config (q + 1) → ℂ from combinationSequence F (q + 1)) x =
      ∑ f ∈ F.familiesOfLength (q + 1), F ⟨q + 1, f⟩ * tensorRealFamily f.1 x :=
  rfl
end YangMills.Construction.ConfigSpace
end
