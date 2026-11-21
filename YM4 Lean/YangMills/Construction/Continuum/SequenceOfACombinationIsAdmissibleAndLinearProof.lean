import YangMills.Construction.Continuum.ClusteringFromTuplesToSchwartzFunctionsProof
import YangMills.Construction.Continuum.CompactSupportAndTensorsOfSeparatedTuples
import YangMills.Construction.Continuum.SequenceOfACombinationIsAdmissibleAndLinear
import YangMills.Construction.Continuum.TheThreeOpenSetsAndTheThreeSpaces
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigSpace
namespace CombinationSequence
open UpperCombination
def evalTensorAt (q : ℕ) (x : Config q) (Y : UpperFamily) : ℂ :=
  if h : Y.1 = q then toConfigFn (entryTensor Y.2.1) (fun j => x (Fin.cast h j)) else 0
theorem combinationSequence_eq_ofConfigFn (F : UpperCombination) (q : ℕ) :
    combinationSequence F q =
      ofConfigFn fun x => Finsupp.linearCombination ℂ (evalTensorAt q x) F := by
  unfold combinationSequence
  congr 1
  funext x
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  have hz : ∀ Y ∈ F.support,
      Y ∉ Set.range (fun f : {f : Fin q → (Fin 4 → ℝ) → ℝ // f ∈ separatedFamilies upperHalfSpace q} =>
        (⟨q, f⟩ : UpperFamily)) → F Y • evalTensorAt q x Y = 0 := by
    rintro ⟨m, f⟩ _ hY
    have hm : m ≠ q := by
      rintro rfl
      exact hY ⟨f, rfl⟩
    simp [evalTensorAt, hm]
  refine Eq.trans ?_ (Finset.sum_preimage
    (fun f : {f : Fin q → (Fin 4 → ℝ) → ℝ // f ∈ separatedFamilies upperHalfSpace q} =>
      (⟨q, f⟩ : UpperFamily)) F.support
    (fun _ _ _ _ h => eq_of_heq (Sigma.mk.inj_iff.1 h).2)
    (fun Y => F Y • evalTensorAt q x Y) hz)
  refine Finset.sum_congr rfl fun f _ => ?_
  show _ = F ⟨q, f⟩ • evalTensorAt q x ⟨q, f⟩
  rw [evalTensorAt, dif_pos rfl]
  rfl
theorem linearCombination_linComb {ι : Type} [Fintype ι] (c : ι → ℂ)
    (X : ι → UpperFamily) (T : UpperFamily → ℂ) :
    Finsupp.linearCombination ℂ T (linComb c X) = ∑ i, c i * T (X i) := by
  simp [linComb, ofFamily, map_sum, Finsupp.linearCombination_single]
theorem combinationSequence_linComb {ι : Type} [Fintype ι] (c : ι → ℂ) (X : ι → UpperFamily)
    (q : ℕ) : combinationSequence (linComb c X) q = lengthPart c X q := by
  rw [combinationSequence_eq_ofConfigFn, lengthPart]
  congr 1
  funext x
  rw [linearCombination_linComb,
    ← Fintype.sum_subtype_add_sum_subtype (fun i => familyLength (X i).toSeparatedFamily = q)
      (fun i => c i * evalTensorAt q x (X i))]
  have hno : ∑ i : {i // ¬ familyLength (X i).toSeparatedFamily = q},
      c i * evalTensorAt q x (X i) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    have h : ¬ (X i).1 = q := i.2
    rw [evalTensorAt, dif_neg h, mul_zero]
  rw [hno, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : (X i).1 = q := i.2
  rw [evalTensorAt, dif_pos h]
  rfl
theorem hasSmoothFamilies_iff (F : UpperCombination) :
    HasSmoothFamilies F ↔ ∀ Y : UpperFamily, F Y ≠ 0 → AllSmoothCompact Y.2.1 := by
  constructor
  · intro h Y hY
    exact h (F Y, Y) ((mem_reducedForm_iff F _ Y).2 ⟨hY, rfl⟩)
  · rintro h ⟨c, Y⟩ hp
    exact h Y ((mem_reducedForm_iff F c Y).1 hp).1
theorem hasSmoothFamilies_linComb {ι : Type} [Fintype ι] (c : ι → ℂ) (X : ι → UpperFamily)
    (hX : ∀ i, AllSmoothCompact (X i).2.1) :
    HasSmoothFamilies (linComb c X) := by
  classical
  rw [hasSmoothFamilies_iff]
  intro Y hY
  obtain ⟨i, rfl⟩ : ∃ i, X i = Y := by
    by_contra hno
    have hne : ∀ i, X i ≠ Y := fun i e => hno ⟨i, e⟩
    exact hY (by simp [linComb, ofFamily, Finsupp.finsetSum_apply, hne])
  exact hX i
theorem combinationSequence_mem (h₁ : CompactSupportTensorFacts)
    (h₂ : OpenLociAndFlatSubspaces) {F : UpperCombination}
    (hF : HasSmoothFamilies F) (q : ℕ) :
    combinationSequence F q ∈ flatOffPosTimeAt q := by
  cases q with
  | zero => exact Set.mem_univ _
  | succ q =>
    obtain ⟨-, -, S, W, Wp, Wm, -, -, hWp, -⟩ := h₂ (q + 1) (Nat.succ_pos _)
    obtain ⟨-, -, hsub, -, htens, -⟩ := h₁ (q + 1) (Nat.succ_pos _)
    have hmem : (∑ f ∈ F.familiesOfLength (q + 1), F ⟨q + 1, f⟩ • tensorRealFamily f.1) ∈ Wp := by
      refine Wp.sum_mem fun f hf => Wp.smul_mem _ ?_
      have hs := (hasSmoothFamilies_iff F).1 hF _ ((mem_familiesOfLength_iff F _ f).1 hf)
      obtain ⟨hu, hp⟩ := (mem_separatedFamilies_upperHalfSpace_iff f.1).1 f.2
      have ht := hsub ((htens f.1 hu hs).2 hp)
      rw [← hWp] at ht
      exact ht
    have hset : (∑ f ∈ F.familiesOfLength (q + 1), F ⟨q + 1, f⟩ • tensorRealFamily f.1) ∈
        schwartzFlatOffPosTime (q + 1) := by
      rw [← hWp]
      exact hmem
    have e : (show Config (q + 1) → ℂ from combinationSequence F (q + 1)) =
        ∑ f ∈ F.familiesOfLength (q + 1), F ⟨q + 1, f⟩ • tensorRealFamily f.1 := by
      funext x
      rw [Finset.sum_apply]
      exact combinationSequence_succ F q x
    show (show Config (q + 1) → ℂ from combinationSequence F (q + 1)) ∈
      schwartzFlatOffPosTime (q + 1)
    rw [e]
    exact hset
theorem ofConfigFn_zero (q : ℕ) :
    ofConfigFn (fun _ : Config q => (0 : ℂ)) = zeroOfDegree q := by apply _root_.YangMills.Construction.AdmissibleClustering.ofConfigFn_zero <;> assumption
theorem finite_nonzero_degrees (F : UpperCombination) :
    {q | combinationSequence F q ≠ zeroOfDegree q}.Finite := by
  refine (F.support.image Sigma.fst).finite_toSet.subset fun q hq => ?_
  by_contra hno
  apply hq
  have hzero : (fun x => Finsupp.linearCombination ℂ (evalTensorAt q x) F) = fun _ => 0 := by
    funext x
    rw [Finsupp.linearCombination_apply]
    refine Finset.sum_eq_zero fun Y hY => ?_
    have hY' : Y.1 ≠ q := fun e => hno (Finset.mem_coe.2 (Finset.mem_image.2 ⟨Y, hY, e⟩))
    simp [evalTensorAt, hY']
  rw [combinationSequence_eq_ofConfigFn, hzero]
  exact ofConfigFn_zero q
theorem ofConfigFn_linComb (a a' : ℂ) {q : ℕ} (g g' : Config q → ℂ) :
    ofConfigFn (fun x => a * g x + a' * g' x) =
      linCombAt a a' (ofConfigFn g) (ofConfigFn g') := by
  cases q <;> rfl
theorem combinationSequence_add_smul (a a' : ℂ) (F F' : UpperCombination) (q : ℕ) :
    combinationSequence (a • F + a' • F') q =
      linCombAt a a' (combinationSequence F q) (combinationSequence F' q) := by
  rw [combinationSequence_eq_ofConfigFn, combinationSequence_eq_ofConfigFn F,
    combinationSequence_eq_ofConfigFn F', ← ofConfigFn_linComb]
  congr 1
  funext x
  simp [map_add, map_smul]
def smoothSubmodule : Submodule ℂ UpperCombination where
  carrier := {F | HasSmoothFamilies F}
  zero_mem' := (hasSmoothFamilies_iff 0).2 fun _ h => absurd rfl h
  add_mem' := by
    intro F G hF hG
    refine (hasSmoothFamilies_iff _).2 fun Y hY => ?_
    by_cases h : F Y = 0
    · refine (hasSmoothFamilies_iff G).1 hG Y fun hG0 => hY ?_
      simp [h, hG0]
    · exact (hasSmoothFamilies_iff F).1 hF Y h
  smul_mem' := by
    intro a F hF
    refine (hasSmoothFamilies_iff _).2 fun Y hY => ?_
    refine (hasSmoothFamilies_iff F).1 hF Y fun h => hY ?_
    simp [h]
theorem hasSmoothFamilies_ofFamily_nil : HasSmoothFamilies (ofFamily UpperFamily.nil) := by
  refine (hasSmoothFamilies_iff _).2 fun Y hY => ?_
  have hE : UpperFamily.nil = Y := by
    by_contra h
    exact hY (Finsupp.single_eq_of_ne (Ne.symm h))
  subst hE
  exact allSmoothCompact_nilFamily
theorem linearCombination_ofFamily (T : UpperFamily → ℂ) (X : UpperFamily) :
    Finsupp.linearCombination ℂ T (ofFamily X) = T X := by
  simp [ofFamily, Finsupp.linearCombination_single]
theorem combinationSequence_nil_zero :
    combinationSequence (ofFamily UpperFamily.nil) 0 = (1 : ℂ) := by
  rw [combinationSequence_eq_ofConfigFn]
  show Finsupp.linearCombination ℂ (evalTensorAt 0 _) (ofFamily UpperFamily.nil) = (1 : ℂ)
  have h : UpperFamily.nil.1 = 0 := rfl
  rw [linearCombination_ofFamily, evalTensorAt, dif_pos h]
  rfl
theorem combinationSequence_nil_of_pos (q : ℕ) (hq : 1 ≤ q) :
    combinationSequence (ofFamily UpperFamily.nil) q = zeroOfDegree q := by
  have hzero : (fun x => Finsupp.linearCombination ℂ (evalTensorAt q x)
      (ofFamily UpperFamily.nil)) = fun _ => 0 := by
    funext x
    have h : ¬ UpperFamily.nil.1 = q := fun e => by
      have h0 : UpperFamily.nil.1 = 0 := rfl
      omega
    rw [linearCombination_ofFamily, evalTensorAt, dif_neg h]
  rw [combinationSequence_eq_ofConfigFn, hzero]
  exact ofConfigFn_zero q
end CombinationSequence
open CombinationSequence in
theorem combinationSequenceAdmissibleLinear_holds
    (h₁ : CompactSupportTensorFacts)
    (h₂ : OpenLociAndFlatSubspaces) :
    CombinationSequenceAdmissibleLinear :=
  ⟨fun _ _ c X hX => hasSmoothFamilies_linComb c X hX,
    fun F hF => ⟨fun _ _ c X _ hFX q => hFX ▸ combinationSequence_linComb c X q,
      fun q => combinationSequence_mem h₁ h₂ hF q, finite_nonzero_degrees F⟩,
    ⟨smoothSubmodule, rfl⟩,
    fun a a' F F' _ _ q => combinationSequence_add_smul a a' F F' q,
    hasSmoothFamilies_ofFamily_nil, combinationSequence_nil_zero, combinationSequence_nil_of_pos⟩
end YangMills.Construction.ConfigSpace
end
