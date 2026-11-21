import YangMills.Construction.Lattice.BoxLaplacianLowerBound
import YangMills.Construction.Lattice.BoxLaplacianSpectralGap
import Mathlib
noncomputable section
namespace YangMills.Construction.Lattice.BoxLaplacianGap
def cubicPeriods (N : ℕ) : Fin 4 → ℝ := fun _ => (N : ℝ) + 1
instance isCommensurateSpacing_cubicPeriods (N : ℕ) : IsCommensurateSpacing (cubicPeriods N) 1 where
  periods_pos _ := by
    unfold cubicPeriods
    positivity
  spacing_pos := one_pos
  ratio_mem _ := ⟨N + 1, Nat.succ_pos N, by simp [cubicPeriods]⟩
def integerPointSite (N : ℕ) : (Fin 4 → ℤ) →+ LatticeSite (cubicPeriods N) 1 where
  toFun a := ⟨torusMk (cubicPeriods N) (fun i => (a i : ℝ)), AddSubgroup.mem_map_of_mem _ <|
    (AddSubgroup.mem_pi _).mpr fun i _ => AddSubgroup.mem_zmultiples_iff.mpr ⟨a i, by simp⟩⟩
  map_zero' := by
    apply Subtype.ext
    show torusMk (cubicPeriods N) _ = 0
    have : (fun i => (((0 : Fin 4 → ℤ) i : ℤ) : ℝ)) = 0 := by
      funext i
      simp
    rw [this, map_zero]
  map_add' a b := by
    apply Subtype.ext
    show torusMk (cubicPeriods N) _ = torusMk (cubicPeriods N) _ + torusMk (cubicPeriods N) _
    rw [← map_add]
    congr 1
    funext i
    simp
def boxCoordinates {N : ℕ} (k : Fin 4 → Fin N) : Fin 4 → ℤ := fun i => ((k i : ℕ) : ℤ)
def boxSite {N : ℕ} (k : Fin 4 → Fin N) : LatticeSite (cubicPeriods N) 1 :=
  integerPointSite N (boxCoordinates k)
end YangMills.Construction.Lattice.BoxLaplacianGap
end
