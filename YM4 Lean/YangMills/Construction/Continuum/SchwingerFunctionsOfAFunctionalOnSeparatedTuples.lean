import YangMills.Construction.Continuum.NormsOfASchwartzFunction
import YangMills.Construction.Continuum.OperationsOnFunctionsOfSeveralPoints
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ConfigSpace
variable {n : ℕ}
abbrev SepFamilyOfLength (n : ℕ) : Type :=
  {f : Fin n → (Fin 4 → ℝ) → ℝ // f ∈ separatedFamilies Set.univ n}
def nilSepFamily : SeparatedFamily :=
  ⟨0, nilFamily, by rw [separatedFamilies_zero]; rfl⟩
def IsMultilinearOnSepFamilies (M : SepFamilyOfLength n → ℝ) : Prop :=
  ∀ (i : Fin n) (b b' : ℝ) (X X' X'' : SepFamilyOfLength n),
    (∀ j, j ≠ i → X.1 j = X'.1 j) → X''.1 i = b • X.1 i + b' • X'.1 i →
      (∀ j, j ≠ i → X''.1 j = X.1 j) → M X'' = b * M X + b' * M X'
theorem update_linComb_mem_separatedFamilies (i : Fin n) (b b' : ℝ) (X X' : SepFamilyOfLength n)
    (hagree : ∀ j, j ≠ i → X.1 j = X'.1 j) :
    Function.update X.1 i (b • X.1 i + b' • X'.1 i) ∈ separatedFamilies Set.univ n := by
  have hsub : tsupport (b • X.1 i + b' • X'.1 i) ⊆ tsupport (X.1 i) ∪ tsupport (X'.1 i) := by
    refine closure_minimal ?_ ((isClosed_tsupport _).union (isClosed_tsupport _))
    intro x hx
    by_contra hnot
    simp only [Set.mem_union, not_or] at hnot
    exact hx (by simp [image_eq_zero_of_notMem_tsupport hnot.1,
      image_eq_zero_of_notMem_tsupport hnot.2])
  have hreg : b • X.1 i + b' • X'.1 i ∈ realC1CompactIn Set.univ := by
    obtain ⟨-, hd₁, hk₁, -⟩ := mem_realC1CompactIn_iff.1 (X.2.1 i)
    obtain ⟨-, hd₂, hk₂, -⟩ := mem_realC1CompactIn_iff.1 (X'.2.1 i)
    exact mem_realC1CompactIn_iff.2 ⟨isOpen_univ,
      (hd₁.const_smul b).add (hd₂.const_smul b'), (hk₁.union hk₂).of_isClosed_subset
        (isClosed_tsupport _) hsub, Set.subset_univ _⟩
  have hdisj : ∀ j, j ≠ i →
      Disjoint (tsupport (b • X.1 i + b' • X'.1 i)) (tsupport (X.1 j)) := by
    intro j hj
    refine Disjoint.mono_left hsub (Set.disjoint_union_left.2 ⟨X.2.2 hj.symm, ?_⟩)
    rw [hagree j hj]
    exact X'.2.2 hj.symm
  refine ⟨fun j => ?_, fun j k hjk => ?_⟩
  · by_cases hj : j = i
    · subst hj
      simpa using hreg
    · simpa [Function.update_of_ne hj] using X.2.1 j
  · by_cases hj : j = i
    · subst hj
      have hk : k ≠ j := hjk.symm
      simpa [Function.update_of_ne hk] using hdisj k hk
    · by_cases hk : k = i
      · subst hk
        simpa [Function.update_of_ne hj] using (hdisj j hj).symm
      · simpa [Function.update_of_ne hj, Function.update_of_ne hk] using X.2.2 hjk
def IsSepFamilyFunctional (σ : SeparatedFamily → ℝ) : Prop :=
  σ nilSepFamily = 1 ∧
    ∀ n, 1 ≤ n → IsMultilinearOnSepFamilies fun X : SepFamilyOfLength n => σ ⟨n, X⟩
def toSchwartzFn (φ : schwartzFlatOffDiagonal n) : SchwartzFn n :=
  ⟨φ.1, φ.2.1⟩
def IsComplexLinearOnFlat (T : schwartzFlatOffDiagonal n → ℂ) : Prop :=
  ∀ (c c' : ℂ) (φ ψ χ : schwartzFlatOffDiagonal n), χ.1 = c • φ.1 + c' • ψ.1 →
    T χ = c * T φ + c' * T ψ
def IsContLinearOnFlat (T : schwartzFlatOffDiagonal n → ℂ) : Prop :=
  IsComplexLinearOnFlat T ∧ ∃ (k : ℕ) (C : ℝ), 1 ≤ k ∧ 0 ≤ C ∧
    ∀ φ : schwartzFlatOffDiagonal n, ‖T φ‖ ≤ C * bracketNorm k (toSchwartzFn φ)
abbrev FlatSequence : Type := (n : ℕ) → flatOffDiagonalAt n → ℂ
def FlatSequence.atSucc (S : FlatSequence) (m : ℕ) :
    schwartzFlatOffDiagonal (m + 1) → ℂ :=
  S (m + 1)
def IsSchwingerSequenceOf (σ : SeparatedFamily → ℝ) (S : FlatSequence) : Prop :=
  IsSepFamilyFunctional σ ∧ (∀ c : flatOffDiagonalAt 0, S 0 c = c.1) ∧
    ∀ m : ℕ, IsContLinearOnFlat (S.atSucc m) ∧
      ∀ X : SepFamilyOfLength (m + 1), AllSmoothCompact X.1 →
        ∀ h : tensorRealFamily X.1 ∈ schwartzFlatOffDiagonal (m + 1),
          S.atSucc m ⟨_, h⟩ = (σ ⟨m + 1, X⟩ : ℂ)
end ConfigSpace
end YangMills.Construction
end
