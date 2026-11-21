import YangMills.Construction.Lattice.GroupAndCellsOfAGridDatum
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.CellGrid
variable {L : ℕ} {κ : ℤ} (d : CellGrid L κ)
theorem const_mem_cellObservables (c : d.spaceCells) (z : ℂ) :
    (fun _ => z : d.GaugeConfig → ℂ) ∈ d.cellObservables c :=
  ⟨fun _ => z, measurable_const, ⟨‖z‖, fun _ => le_rfl⟩, fun _ => rfl⟩
theorem conj_mem_cellObservables (c : d.spaceCells) {F : d.GaugeConfig → ℂ}
    (hF : F ∈ d.cellObservables c) : (fun U => starRingEnd ℂ (F U)) ∈ d.cellObservables c := by
  obtain ⟨f, hf, ⟨C, hC⟩, hFf⟩ := hF
  refine ⟨fun u => starRingEnd ℂ (f u), Complex.continuous_conj.measurable.comp hf,
    ⟨C, fun u => ?_⟩, fun U => ?_⟩
  · rw [RCLike.norm_conj]
    exact hC u
  · simp only [hFf U]
def checkerboardCopy (c c' : d.spaceCells) (F : d.cellObservables c) : d.GaugeConfig → ℂ :=
  open Classical in
  if d.inducedSign (d.cellTransporter c.1 c'.1) = 1 then
    (d.symmetryOfMap (d.cellTransporter c.1 c'.1)).actOnObservables F.1
  else
    fun U => starRingEnd ℂ ((d.symmetryOfMap (d.cellTransporter c.1 c'.1)).actOnObservables F.1 U)
theorem checkerboardCopy_of_inducedSign_eq_one {c c' : d.spaceCells} (F : d.cellObservables c)
    (h : d.inducedSign (d.cellTransporter c.1 c'.1) = 1) :
    d.checkerboardCopy c c' F =
      (d.symmetryOfMap (d.cellTransporter c.1 c'.1)).actOnObservables F.1 :=
  if_pos h
theorem checkerboardCopy_of_inducedSign_eq_neg_one {c c' : d.spaceCells} (F : d.cellObservables c)
    (h : d.inducedSign (d.cellTransporter c.1 c'.1) = -1) :
    d.checkerboardCopy c c' F =
      fun U => starRingEnd ℂ
        ((d.symmetryOfMap (d.cellTransporter c.1 c'.1)).actOnObservables F.1 U) :=
  if_neg (by rw [h]; norm_num)
end YangMills.Construction.CellGrid
end
