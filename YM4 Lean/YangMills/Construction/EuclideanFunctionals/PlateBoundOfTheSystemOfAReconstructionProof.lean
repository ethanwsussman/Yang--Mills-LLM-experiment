import YangMills.Construction.EuclideanFunctionals.InsertionOfTheSystemOfAReconstruction
import YangMills.Construction.EuclideanFunctionals.PlateBoundOfTheSystemOfAReconstruction
import YangMills.Construction.EuclideanFunctionals.RoomForTheInsertion
import Mathlib
set_option autoImplicit false
open YangMills.Construction.RealPlane
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.ReconSystemProductBound
open DefinitionComparison
variable {m : SharpScale} {S : ConnFamily} {σ : EuclidFunctionalWithRecon m S}
theorem norm_bound_iff (hIns : SystemInsertion.Holds)
    (hRoom : InsertionRoom.Holds) (s : OSDataOf σ) {p c η C : ℝ}
    (hc : c ∈ stripFractionRange) (hη : η ∈ gapWidthRange) {α : RealPlane → ℂ}
    (hα : α ∈ complexProfiles) {φ : RealPlane → ℝ} (hφ : φ ∈ realLabels)
    (hs : tsupport α ⊆ {y : RealPlane | |y 0| < c * η})
    (F F' : freeSpanIn {x | η / 4 < x 3}) :
    ‖insertion S F.1 (productFunction α φ) F'.1‖ ≤
        C * η ^ (-p) * profileL1Norm α * heightNorm σ (η / 4) F.1 * heightNorm σ (η / 4) F'.1 ↔
      ‖stripInsertion S F.1 (productFunction α φ) F'.1‖ ≤
        C * η ^ (-p) * profileL1Norm α *
          loweredNorm s.toSymm (quarter_pos_of_mem_gapWidthRange hη) F *
          loweredNorm s.toSymm (quarter_pos_of_mem_gapWidthRange hη) F' := by
  have set₁ := hRoom.2.2.2 η hη c hc α hα φ hφ hs F.1 F.2 F'.1 F'.2
  have set₂ := hRoom.2.2.2 η hη c hc α hα φ hφ hs F'.1 F'.2 F.1 F.2
  obtain ⟨-, norm₁, value⟩ := hIns m S σ s (η / 4) F.1 F'.1 (productFunction α φ) set₁
  obtain ⟨-, norm₂, -⟩ := hIns m S σ s (η / 4) F'.1 F.1 (productFunction α φ) set₂
  rw [value, norm₁, norm₂]
theorem productBoundWith_iff (hIns : SystemInsertion.Holds)
    (hRoom : InsertionRoom.Holds) (s : OSDataOf σ) {p c : ℝ} (hp : 0 < p)
    (hc : c ∈ productBoundFractions) {φ : RealPlane → ℝ} (hφ : φ ∈ realLabels) (C : ℝ) :
    ProductBoundWith σ hp hc φ C ↔
      SymmProductBoundWith s.toSymm hp (productBoundFractions_subset_stripFractionRange hc) φ C := by
  have hc' := productBoundFractions_subset_stripFractionRange hc
  constructor
  · intro h η hη α hα hs F F'
    exact (norm_bound_iff hIns hRoom s hc' hη hα hφ hs F F').1
      (h η hη α hα hs F.1 (by rw [finCombIn_eq_freeSpanIn]; exact F.2) F'.1
        (by rw [finCombIn_eq_freeSpanIn]; exact F'.2))
  · intro h η hη α hα hs F hF A hA
    rw [finCombIn_eq_freeSpanIn] at hF hA
    exact (norm_bound_iff hIns hRoom s hc' hη hα hφ hs ⟨F, hF⟩ ⟨A, hA⟩).2
      (h η hη α hα hs ⟨F, hF⟩ ⟨A, hA⟩)
theorem productBoundOfOSData_holds (hIns : SystemInsertion.Holds)
    (hRoom : InsertionRoom.Holds) : ProductBoundOfOSData.Holds := by
  intro m S σ s p c hp hc
  have same : ∀ φ ∈ realLabels, ∀ C : ℝ, ProductBoundWith σ hp hc φ C ↔
      SymmProductBoundWith s.toSymm hp (productBoundFractions_subset_stripFractionRange hc) φ C :=
    fun φ hφ C => productBoundWith_iff hIns hRoom s hp hc hφ C
  refine ⟨productBoundFractions_subset_stripFractionRange hc, ?_, same⟩
  rw [hasProductBound_iff]
  exact forall₂_congr fun φ hφ => exists_congr fun C => same φ hφ C
end YangMills.Construction.EuclideanFunctionals.ReconSystemProductBound
