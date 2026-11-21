import YangMills.Construction.TorusOrFourSpace.CountableFamilyOfACountableChoice
import YangMills.Construction.TorusOrFourSpace.MaximumC1NormOnTheSpacesOfTheStock
import YangMills.Construction.TorusOrFourSpace.SpacesC1OfTheStock
import YangMills.Construction.TorusOrFourSpace.TwoNormsOfClassC1
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.MaxC1Norm
theorem exists_submodule_equivalentNormsOn (hTwo : C1NormComparison.statement)
    (hSpaces : C1OfStock.Holds)
    (hFamily : CountableChoiceFamilyFacts)
    (hClasses : VectorClasses.Claim) (P : Params) (K : Kind)
    (Q : Set (K.Pt P)) (hQ : Q ∈ Kind.supportStock P K) :
    ∃ W : Submodule ℝ (K.Pt P → ℝ), (W : Set (K.Pt P → ℝ)) = Kind.c1VanishingOutside P K Q ∧
      C1NormComparison.EquivalentNormsOn P K W := by
  obtain ⟨-, hStock, -, -⟩ := hFamily P K
  obtain ⟨hEq, -, -, -⟩ := hStock Q hQ
  obtain ⟨W, hW⟩ := ((hClasses P K).1 Q).2.1
  have hWQ : (W : Set (K.Pt P → ℝ)) = Kind.c1VanishingOutside P K Q := hW.trans hEq.symm
  refine ⟨W, hWQ, (hTwo P K).2 W fun u hu => ?_⟩
  have huQ : u ∈ Kind.c1VanishingOutside P K Q := hWQ ▸ (show u ∈ (W : Set (K.Pt P → ℝ)) from hu)
  exact ⟨huQ.1, ((hSpaces P K Q hQ).1.2 u huQ).2.2.2⟩
theorem parts_of_mem_supportStock (hTwo : C1NormComparison.statement)
    (hSpaces : C1OfStock.Holds)
    (hFamily : CountableChoiceFamilyFacts)
    (hClasses : VectorClasses.Claim) (P : Params) (K : Kind)
    (Q : Set (K.Pt P)) (hQ : Q ∈ Kind.supportStock P K) :
    NormComparison P K Q ∧ SeparableBanachSameDense P K Q ∧
      CountableFamilyMaxNorm P K Q := by
  obtain ⟨-, hStock, -, -⟩ := hFamily P K
  obtain ⟨hEq, hGrad, hBanach, hSharp⟩ := hStock Q hQ
  obtain ⟨W, hWQ, -, hMax, hSeq, hDense⟩ :=
    exists_submodule_equivalentNormsOn hTwo hSpaces hFamily hClasses P K Q hQ
  rw [hWQ] at hDense
  have hIn : ∀ {f : K.Pt P → ℝ}, f ∈ Kind.c1VanishingOutside P K Q → f ∈ W := fun hf =>
    (show _ ∈ (W : Set (K.Pt P → ℝ)) from hWQ.symm ▸ hf)
  have hOut : ∀ {f : K.Pt P → ℝ}, f ∈ W → f ∈ Kind.c1VanishingOutside P K Q := fun hf =>
    hWQ ▸ (show _ ∈ (W : Set (K.Pt P → ℝ)) from hf)
  obtain ⟨hNormV, hComplete, A, hAV, hAc, hAd⟩ := hBanach
  have hMaxBanach : Kind.IsSeparableBanachWrt P K (SupportAdapted.c1MaxNorm P K)
      (Kind.c1VanishingOutside P K Q) := by
    refine ⟨⟨hNormV.zero_mem, hNormV.lincomb_mem,
      fun f hf => hMax.finite f (hIn hf), fun f hf h0 => (hMax.eq_zero_iff f (hIn hf)).1 h0,
      fun f hf a => hMax.homogeneous a f (hIn hf),
      fun f hf g hg => hMax.triangle f (hIn hf) g (hIn hg)⟩, ?_,
      A, hAV, hAc, (hDense A hAV).1 hAd⟩
    intro s hs hCauchy
    have hsW : ∀ j, s j ∈ W := fun j => hIn (hs j)
    obtain ⟨f, hf, hLimit⟩ := hComplete s hs ((hSeq s hsW).2.2 hCauchy)
    obtain ⟨g, hg, hgLimit⟩ := (hSeq s hsW).1.1 ⟨f, hIn hf, hLimit⟩
    exact ⟨g, hOut hg, hgLimit⟩
  refine ⟨fun f hf => ?_, ⟨⟨fun h hh => hMax.finite h (hIn hh),
    fun h hh => hMax.eq_zero_iff h (hIn hh), fun h hh α => hMax.homogeneous α h (hIn hh),
    fun h hh h' hh' => hMax.triangle h (hIn hh) h' (hIn hh')⟩, hMaxBanach,
    fun B hB => (hDense B hB).symm⟩,
    hEq, hGrad, hMaxBanach, fun B hB hd => hSharp B hB ((hDense B hB).2 hd)⟩
  obtain ⟨-, hCompared, hFinite⟩ := (hTwo P K).1 f hf.1
  obtain ⟨-, -, hBound, hBound'⟩ := hFinite ((hSpaces P K Q hQ).1.2 f hf).1
  exact ⟨hCompared.1, hCompared.2, hBound.trans hBound'⟩
theorem claim_holds (hTwo : C1NormComparison.statement) (hSpaces : C1OfStock.Holds)
    (hFamily : CountableChoiceFamilyFacts)
    (hClasses : VectorClasses.Claim) : Claim := by
  intro P K
  have hParts := parts_of_mem_supportStock hTwo hSpaces hFamily hClasses P K
  refine ⟨hParts, fun C => ⟨fun h Q => ?_, fun h Q => ?_⟩⟩
  · obtain ⟨hSub, hDense⟩ := h Q
    exact ⟨hSub, ((hParts Q.1 Q.2).2.1.2.2 _ hSub).2 hDense⟩
  · obtain ⟨hSub, hDense⟩ := h Q
    exact ⟨hSub, ((hParts Q.1 Q.2).2.1.2.2 _ hSub).1 hDense⟩
end YangMills.Construction.PeriodicSpace.MaxC1Norm
