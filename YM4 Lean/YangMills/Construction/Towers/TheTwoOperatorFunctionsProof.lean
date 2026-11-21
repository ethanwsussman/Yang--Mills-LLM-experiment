import YangMills.Construction.Towers.ConfigurationsNearOneHaveSmallIterates
import YangMills.Construction.Towers.DeterminantsOfTheTwoOperatorFunctionsOnTheTorus
import YangMills.Construction.Towers.FieldsAndTheirValues
import YangMills.Construction.Towers.SymbolsOfTheTwoOperatorFunctionsAreInvertible
import YangMills.Construction.Towers.TheBackgroundKernelAndTheCovariantLaplacianAreFormed
import YangMills.Construction.Towers.TheTwoOperatorFunctions
import YangMills.Construction.Towers.TheTwoOperatorFunctionsAreLocal
import YangMills.Construction.Towers.TheTwoOperatorFunctionsAreRealAtRealFields
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.OperatorFunctions
open PeriodicOperators
variable {L k : ℕ}
theorem isSupBelow_of_le {F : PeriodicData} {f : F.Carrier → ℂ} {r r' : ℝ} (h : r ≤ r')
    (hf : IsSupBelow F f r) : IsSupBelow F f r' := by
  obtain ⟨s, hs, hb⟩ := hf
  exact ⟨s, hs.trans_le h, hb⟩
theorem kernelsDefined_of_mem (hK : Tower.ThreeMapKernels.OnFullSpace L k)
    (hF : Tower.FullSpace.HessianLaplacian.HessianKernelAndLaplacianExist)
    (hS : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    {U : Tower.FullSpace.Edge L k 0 → Matrices.ComplexMatrix2}
    (hU : U ∈ Tower.FullSpace.smallIterateFields L k)
    {J : Tower.FullSpace.Edge L k 0 → Matrices.ComplexMatrix2}
    (hJ : J ∈ Tower.FullSpace.complexEdgeForms (Tower.meshAt L k 0))
    {μ : Tower.FullSpace.Edge L k k → Matrices.ComplexMatrix2}
    (hμ : μ ∈ Tower.FullSpace.complexEdgeForms (Tower.meshAt L k k)) :
    Tower.FullSpace.OperatorFunctions.KernelsDefined U J μ := by
  obtain ⟨hX, hD⟩ := hF L hS k hk U hU
  obtain ⟨-, hDiff, -, hMeans⟩ := hK
  have hDU := hDiff U hU.1
  obtain ⟨hQ, hA⟩ := hMeans U hU
  exact ⟨⟨_, (hX J hJ μ hμ).2.2.1⟩, ⟨hQ.represents, hQ.swap_represents⟩,
    ⟨hA.represents, hA.swap_represents⟩, ⟨hDU.represents, hDU.swap_represents⟩, hD.1, hD.2⟩
theorem operatorFunctionsTheorem_of_parts
    (hValues : Tower.FullSpace.FieldValues.FieldsAndValuesClaim)
    (hSmall : Tower.FullSpace.SmallIterates.SmallIteratesNearOne)
    (hFormed : Tower.FullSpace.HessianLaplacian.HessianKernelAndLaplacianExist)
    (hLocal : Tower.FullSpace.OperatorFunctionsAreLocal)
    (hReal : Tower.FullSpace.OperatorFunctionsRealOnCompactFields)
    (hDet : Tower.FullSpace.TorusDeterminants.Claim)
    (hSymbols : Tower.FullSpace.SymbolsInvertibleAtZero)
    (hKernels : Tower.ThreeMapKernels.Claim) :
    Tower.FullSpace.OperatorFunctions.OperatorFunctionsTheorem := by
  intro L hL hS k hk
  obtain ⟨ρ₁, hρ₁, hsmall⟩ := (hSmall L hL hS k hk).2
  obtain ⟨ρ₂, hρ₂, hreal⟩ := hReal L hL hS k hk
  obtain ⟨hv, hg⟩ := hLocal L hL hS k hk
  obtain ⟨hsv, hsg⟩ := hSymbols L hL hS k hk
  refine ⟨⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, ?_, hv, hg⟩, ?_, hsv, hsg⟩
  · intro ζ hζ
    have hU : ζ.gaugeField ∈ Tower.FullSpace.smallIterateFields L k := by
      have h := hsmall _ (isSupBelow_of_le (min_le_left ρ₁ ρ₂) hζ)
      rwa [((hValues L hL k).1 ζ).2.2.2.2.2] at h
    exact ⟨hU, kernelsDefined_of_mem (hKernels L hS k hk).2 hFormed hS hk hU ζ.2.1.2 ζ.2.2.2,
      hreal ζ (isSupBelow_of_le (min_le_right ρ₁ ρ₂) hζ)⟩
  · intro R hRv hRg m hm hR
    obtain ⟨ε, hε, hdet⟩ := hDet L hL hS k hk R hRv hRg m hm hR
    refine ⟨ε, hε, fun ζ r hr hζ => ?_⟩
    obtain ⟨hform, hv', hg'⟩ := hdet ζ r hr hζ
    refine ⟨hform, ?_⟩
    unfold YangMills.Construction.Tower.fieldFunctional
      YangMills.Construction.Tower.backgroundFunctional
      YangMills.Construction.Tower.FullSpace.OperatorFunctions.logDetCombination
    rw [hv', hg']
end YangMills.Construction.Tower.FullSpace.OperatorFunctions
end
