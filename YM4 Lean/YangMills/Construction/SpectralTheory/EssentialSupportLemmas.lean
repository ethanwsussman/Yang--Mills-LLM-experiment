import YangMills.Construction.SpectralTheory.BoundedBorelCalculus
import YangMills.Construction.SpectralTheory.EssentialSupportOfSpectralMeasure
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.EssentialSupport
open BorelSpectral BorelCalculus
variable {n : ℕ} {Y : Set (Fin n → ℝ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
def vanishingOpenSets (E : SpectralMeasure Y H) : Set (Set (Fin n → ℝ)) :=
  {O | ∃ hO : IsOpen O,
    E ⟨Subtype.val ⁻¹' O, measurable_subtype_coe hO.measurableSet⟩ = 0}
theorem compl_essSupport_eq (E : SpectralMeasure Y H) :
    E.essSupportᶜ = ⋃₀ vanishingOpenSets E :=
  compl_compl _
theorem essSupport_isClosed (E : SpectralMeasure Y H) : IsClosed E.essSupport := by
  rw [← isOpen_compl_iff, compl_essSupport_eq]
  exact isOpen_sUnion fun O hO => hO.1
theorem apply_eq_zero_of_disjoint_essSupport (E : SpectralMeasure Y H)
    (hE : BoundedFunctionalCalculus E) (Δ : BorelSubsets Y) (h : ∀ y ∈ Δ.1, y.1 ∉ E.essSupport) :
    E Δ = 0 := by
  obtain ⟨T, hT, hTS, hU⟩ :=
    TopologicalSpace.isOpen_sUnion_countable (vanishingOpenSets E) fun O hO => hO.1
  have : Countable T := hT.to_subtype
  have hz := hE.apply_iUnion T
    (fun O => ⟨Subtype.val ⁻¹' O.1, measurable_subtype_coe (hTS O.2).1.measurableSet⟩)
    (fun O => (hTS O.2).2)
  refine hE.apply_subset _ Δ hz fun y hy => ?_
  have hy' : y.1 ∈ ⋃₀ T := by
    rw [hU, ← compl_essSupport_eq]
    exact h y hy
  obtain ⟨O, hO, hyO⟩ := hy'
  exact mem_iUnion.mpr ⟨⟨O, hO⟩, hyO⟩
theorem essSupport_subset_of_isCarriedBy (E : SpectralMeasure Y H) (Z : Set (Fin n → ℝ))
    (hZ : IsClosed Z) (hC : E.IsCarriedBy (traceOfClosed Y hZ)) : E.essSupport ⊆ Z := by
  intro x hx
  by_contra hxZ
  exact hx ⟨Zᶜ, ⟨hZ.isOpen_compl, hC⟩, hxZ⟩
theorem essSupportHolds_of_bounded
    (hB : SpectralTheory.BoundedBorelCalculus.BoundedBorelCalculusHolds) : EssSupportHolds := by
  intro H _ _ _ n Y E
  have hE := hB H n Y E
  refine ⟨essSupport_isClosed E, fun h => ?_, essSupport_subset_of_isCarriedBy E,
    fun Z hZ => ⟨essSupport_subset_of_isCarriedBy E Z hZ, ?_⟩⟩
  · exact apply_eq_zero_of_disjoint_essSupport E hE _ fun y hy => hy
  · intro hs
    exact apply_eq_zero_of_disjoint_essSupport E hE _ fun y hy hys => hy (hs hys)
end YangMills.Construction.EssentialSupport
