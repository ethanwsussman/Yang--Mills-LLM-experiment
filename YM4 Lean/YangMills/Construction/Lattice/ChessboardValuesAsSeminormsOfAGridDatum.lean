import YangMills.Construction.Lattice.ReflectionPositivityAndChessboardEstimateOfAGridDatum
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace CellGrid
variable {L : ℕ} {κ : ℤ} (d : CellGrid L κ)
theorem smul_mem_cellObservables (c : d.spaceCells) (z : ℂ) {F : d.GaugeConfig → ℂ}
    (hF : F ∈ d.cellObservables c) : (fun U => z * F U) ∈ d.cellObservables c := by
  obtain ⟨f, hf, ⟨C, hC⟩, hFf⟩ := hF
  refine ⟨fun u => z * f u, hf.const_mul z, ⟨‖z‖ * C, fun u => ?_⟩, fun U => ?_⟩
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC u) (norm_nonneg z)
  · simp only [hFf U]
theorem add_mem_cellObservables (c : d.spaceCells) {F G : d.GaugeConfig → ℂ}
    (hF : F ∈ d.cellObservables c) (hG : G ∈ d.cellObservables c) :
    (fun U => F U + G U) ∈ d.cellObservables c := by
  obtain ⟨f, hf, ⟨C, hC⟩, hFf⟩ := hF
  obtain ⟨g, hg, ⟨C', hC'⟩, hGg⟩ := hG
  refine ⟨fun u => f u + g u, hf.add hg, ⟨C + C', fun u => ?_⟩, fun U => ?_⟩
  · exact (norm_add_le _ _).trans (add_le_add (hC u) (hC' u))
  · simp only [hFf U, hGg U]
def cellOne (c : d.spaceCells) : d.cellObservables c :=
  ⟨fun _ => 1, d.const_mem_cellObservables c 1⟩
def cellConj (c : d.spaceCells) (F : d.cellObservables c) : d.cellObservables c :=
  ⟨fun U => starRingEnd ℂ (F.1 U), d.conj_mem_cellObservables c F.2⟩
def cellSmul (c : d.spaceCells) (z : ℂ) (F : d.cellObservables c) : d.cellObservables c :=
  ⟨fun U => z * F.1 U, d.smul_mem_cellObservables c z F.2⟩
def cellAdd (c : d.spaceCells) (F G : d.cellObservables c) : d.cellObservables c :=
  ⟨fun U => F.1 U + G.1 U, d.add_mem_cellObservables c F.2 G.2⟩
end CellGrid
namespace CheckerboardSeminorms
def Statement : Prop :=
  ∀ (L : ℕ) (κ : ℤ) (d : CellGrid L κ) (β : ℝ), 0 < β →
    ∀ (c : d.spaceCells) (F G : d.cellObservables c) (z : ℂ),
      ((∀ c' : d.spaceCells, ∃ h : d.checkerboardCopy c c' F ∈ d.cellObservables c',
          d.checkerboardNorm β c' ⟨d.checkerboardCopy c c' F, h⟩ = d.checkerboardNorm β c F) ∧
        d.checkerboardNorm β c (d.cellConj c F) = d.checkerboardNorm β c F) ∧
      (d.checkerboardNorm β c F ≤ ⨆ U, ‖F.1 U‖ ∧
        d.checkerboardNorm β c (d.cellOne c) = 1) ∧
      (d.checkerboardNorm β c (d.cellSmul c z F) = ‖z‖ * d.checkerboardNorm β c F ∧
        d.checkerboardNorm β c (d.cellAdd c F G) ≤
          d.checkerboardNorm β c F + d.checkerboardNorm β c G) ∧
      ∀ (S : Set d.spaceCells) (H : (c' : S) → d.cellObservables c'.1),
        ‖d.gibbsMean β fun U => ∏ᶠ c' : S, (H c').1 U‖ ≤
          ∏ᶠ c' : S, d.checkerboardNorm β c'.1 (H c')
end CheckerboardSeminorms
end YangMills.Construction
end
