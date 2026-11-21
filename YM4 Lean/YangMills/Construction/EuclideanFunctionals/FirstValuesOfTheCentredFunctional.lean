import YangMills.Construction.EuclideanFunctionals.TuplesIsometriesFreeSpaceAndMirrorOfFourSpace
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.EuclideanFunctionals.CenteredInitialValues
theorem single_mem_sepN {f : R4 → ℝ} (hf : f ∈ C1c ℝ) :
    [f] ∈ sepN 1 :=
  ⟨rfl, fun _ hg => (List.mem_singleton.1 hg).symm ▸ hf, List.pairwise_singleton _ _⟩
theorem pair_mem_sepN {f g : R4 → ℝ} (hf : f ∈ C1c ℝ)
    (hg : g ∈ C1c ℝ) (hfg : Disjoint (supp f) (supp g)) :
    [f, g] ∈ sepN 2 :=
  ⟨rfl, fun _ hk => (List.mem_pair.1 hk).elim (fun e => e.symm ▸ hf) (fun e => e.symm ▸ hg),
    List.pairwise_pair.2 hfg⟩
def singleSep {f : R4 → ℝ} (hf : f ∈ C1c ℝ) : sepAll :=
  ⟨[f], ReflectionPositivity.AxisMirror.Ambient.separatedN_subset_separatedAll _ _ 1
    (single_mem_sepN hf)⟩
def pairSep {f g : R4 → ℝ} (hf : f ∈ C1c ℝ) (hg : g ∈ C1c ℝ)
    (hfg : Disjoint (supp f) (supp g)) : sepAll :=
  ⟨[f, g], ReflectionPositivity.AxisMirror.Ambient.separatedN_subset_separatedAll _ _ 2
    (pair_mem_sepN hf hg hfg)⟩
def InitialValues : Prop :=
  ∀ S : ConnFamily,
    centeredFn S (ReflectionPositivity.AxisMirror.Ambient.emptyList defaultMirrorData
      ReflectionPositivity.AxisMirror.Ambient.euclidean) = 1 ∧
    (∀ (f : R4 → ℝ) (hf : f ∈ C1c ℝ), centeredFn S (singleSep hf) = 0) ∧
    ∀ (f g : R4 → ℝ) (hf : f ∈ C1c ℝ) (hg : g ∈ C1c ℝ)
      (hfg : Disjoint (supp f) (supp g)),
      centeredFn S (pairSep hf hg hfg) =
        S.fn 2 le_rfl ⟨[f, g], pair_mem_sepN hf hg hfg⟩
end YangMills.Construction.EuclideanFunctionals.CenteredInitialValues
