import YangMills.Construction.Towers.ConfigurationsNearOneHaveSmallIterates
import YangMills.Construction.Towers.SaddleOperatorsOfTheScaledPictureOnTheWhole
import YangMills.Construction.Towers.TheBackgroundKernelAtZero
import YangMills.Construction.Towers.TheOperatorFunctionsAtTheBackgroundFields
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.BackgroundJets
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.LocalKernels (FieldComponent)
namespace OpFunsAtBackground
open YangMills.Construction.Tower.RescaledConditions (sumDiagScale)
variable {L k : ℕ}
theorem backgroundIndex_injective (hL : 0 < L) :
    Function.Injective (backgroundIndex L k hL) := by
  intro a b h
  cases h
  rfl
theorem extendByZero_background (hL : 0 < L) (f : (remainderIndex L k).Carrier → ℂ)
    (i : (remainderIndex L k).Carrier) :
    PeriodicOperators.extendByZero (backgroundIndex L k hL) f (backgroundIndex L k hL i) =
      f i :=
  (backgroundIndex_injective hL).extend_apply f 0 i
theorem extendByZero_off_background (hL : 0 < L) (f : (remainderIndex L k).Carrier → ℂ)
    (j : (fieldPeriodicData L k hL).Carrier) (h : ¬∃ i, backgroundIndex L k hL i = j) :
    PeriodicOperators.extendByZero (backgroundIndex L k hL) f j = 0 :=
  Function.extend_apply' f (0 : (fieldPeriodicData L k hL).Carrier → ℂ) j h
theorem extendByZero_isSupBelow (hL : 0 < L) {f : (remainderIndex L k).Carrier → ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hf : IsSupBelow (remainderIndex L k) f ρ) :
    IsSupBelow (fieldPeriodicData L k hL)
      (PeriodicOperators.extendByZero (backgroundIndex L k hL) f) ρ := by
  obtain ⟨r, hr, hb⟩ := hf
  refine ⟨max r 0, max_lt hr hρ, fun j => ?_⟩
  by_cases h : ∃ i, backgroundIndex L k hL i = j
  · obtain ⟨i, rfl⟩ := h
    rw [extendByZero_background]
    exact (hb i).trans (le_max_left _ _)
  · rw [extendByZero_off_background hL f j h, norm_zero]
    exact le_max_right _ _
theorem backgroundOfCoeffs_extendByZero (hL : 0 < L) (f : (remainderIndex L k).Carrier → ℂ) :
    backgroundOfCoeffs hL (PeriodicOperators.extendByZero (backgroundIndex L k hL) f) =
      (edgePauliCoordinates L k 0).ofCoeffs f := by
  unfold backgroundOfCoeffs
  congr 1
  funext i
  exact extendByZero_background hL f i
theorem ofCoeffs_zero (j : ℕ) :
    (edgePauliCoordinates L k j).ofCoeffs (fun _ => 0) = 0 := by
  funext b
  simp [edgePauliCoordinates, extendOddly, ofPauliCoeffs]
theorem sourceOfCoeffs_extendByZero (hL : 0 < L) (f : (remainderIndex L k).Carrier → ℂ) :
    sourceOfCoeffs hL (PeriodicOperators.extendByZero (backgroundIndex L k hL) f) = 0 := by
  have h : ∀ i : (edgePauliCoordinates L k 0).Index,
      PeriodicOperators.extendByZero (backgroundIndex L k hL) f
        ⟨FieldComponent.source, i⟩ = 0 := by
    intro i
    refine extendByZero_off_background hL f _ ?_
    rintro ⟨x, hx⟩
    cases hx
  exact (congrArg (edgePauliCoordinates L k 0).ofCoeffs (funext h)).trans (ofCoeffs_zero 0)
theorem coarseOfCoeffs_extendByZero (hL : 0 < L) (f : (remainderIndex L k).Carrier → ℂ) :
    coarseOfCoeffs hL (PeriodicOperators.extendByZero (backgroundIndex L k hL) f) = 0 := by
  have h : ∀ i : (edgePauliCoordinates L k k).Index,
      PeriodicOperators.extendByZero (backgroundIndex L k hL) f
        ⟨FieldComponent.coarse, i⟩ = 0 := by
    intro i
    refine extendByZero_off_background hL f _ ?_
    rintro ⟨x, hx⟩
    cases hx
  exact (congrArg (edgePauliCoordinates L k k).ofCoeffs (funext h)).trans (ofCoeffs_zero k)
theorem hessianKernel_zero (hKer : KernelAtZeroSources.ZeroSourceKernel)
    (hs : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    {U : Edge L k 0 → Matrices.ComplexMatrix2} (hU : U ∈ smallIterateFields L k) :
    hessianKernel U 0 0 = backgroundKernel L k U := by
  obtain ⟨-, -, -, -, -, hbk, huniq, -⟩ := hKer L hs k hk U hU
  exact huniq _ (Classical.epsilon_spec (p := IsHessianKernel U 0 0) ⟨_, hbk⟩)
theorem saddleRelations_holds (hSmall : SmallIterates.SmallIteratesNearOne)
    (hKer : KernelAtZeroSources.ZeroSourceKernel)
    (hSad : RescaledSaddleScaling) : SaddleRelations := by
  intro L hL hs k hk
  obtain ⟨ρ, hρ, hsmall⟩ := (hSmall L hL hs k hk).2
  refine ⟨ρ, hρ, fun f hf => ?_⟩
  have hconf : expForm (backgroundOfCoeffs hL
      (PeriodicOperators.extendByZero (backgroundIndex L k hL) f)) =
        gaugeFieldOfForm L k f := by
    rw [backgroundOfCoeffs_extendByZero]
    rfl
  have hU : gaugeFieldOfForm L k f ∈ smallIterateFields L k := by
    have := hsmall _ (extendByZero_isSupBelow hL hρ hf)
    rwa [FieldValueFunctions.gaugeFieldOfCoeffs, hconf] at this
  obtain ⟨hv, hg⟩ := hSad L hs k hk _ hU
  constructor
  · have : vectorOpFn L k hL (PeriodicOperators.extendByZero (backgroundIndex L k hL) f) =
        backgroundSaddle L k (gaugeFieldOfForm L k f) := by
      change hessianSaddle (expForm (backgroundOfCoeffs hL _))
        (sourceOfCoeffs hL _) (coarseOfCoeffs hL _) = _
      rw [hconf, sourceOfCoeffs_extendByZero, coarseOfCoeffs_extendByZero]
      change blockSaddle (hessianKernel _ 0 0) _ = _
      rw [hessianKernel_zero hKer hs hk hU]
      rfl
    exact this.trans hv
  · have : ghostOpFn L k hL (PeriodicOperators.extendByZero (backgroundIndex L k hL) f) =
        laplacianSaddle L k (gaugeFieldOfForm L k f) := by
      change laplacianSaddle L k (expForm (backgroundOfCoeffs hL _)) = _
      rw [hconf]
    exact this.trans hg
end OpFunsAtBackground
end YangMills.Construction.Tower.FullSpace.BackgroundJets
end
