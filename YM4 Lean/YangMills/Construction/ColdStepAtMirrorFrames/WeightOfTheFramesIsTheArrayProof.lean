import YangMills.Construction.ColdStepAtMirrorFrames.WeightOfTheFramesIsTheArray
import YangMills.Construction.SummableBoundsOfTheFlow.LeastActionOfAFrameOnItsTorus
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields YangMills.Construction.TorusLumps
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace FrameComparison
theorem mem_sitesOfCells {F : BlockFrame} (hodd : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i)
    {S : Finset F.Cell} (hS : ∀ z : F.Cell, z ∈ S) {j : ℕ} (x : F.Site j) : x ∈ sitesOfCells S j := by apply _root_.YangMills.Construction.FrameTorusAction.mem_sitesOfCells_of_forall_mem <;> assumption
section Casts
variable {a b c : ℕ}
end Casts
section Torus
variable {F : BlockFrame} {m j : ℕ}
def siteOfTorus (j : ℕ) (x : TorusSite m) : F.Site j := siteOfCoords j fun k => ((x k).cast : ℤ)
theorem toTorusSite_siteOfTorus (hp : ∀ i, F.period j i = m) (x : TorusSite m) :
    toTorusSite m (siteOfTorus (F := F) j x) = x := by apply _root_.YangMills.Construction.FrameTorusAction.toTorusSite_siteOfTorusSite <;> assumption
theorem siteOfTorus_toTorusSite (hp : ∀ i, F.period j i = m) (y : F.Site j) :
    siteOfTorus j (toTorusSite m y) = y := by apply _root_.YangMills.Construction.FrameTorusAction.siteOfTorusSite_toTorusSite <;> assumption
theorem isCold_restrictToTorus (hp : ∀ i, F.period j i = m) {s : ℝ} {W : F.GaugeField j}
    (h : IsSmallCurvature s W) : IsCold s (restrictToTorus m W) := by apply _root_.YangMills.Construction.FrameTorusAction.isCold_restrictToTorus <;> assumption
theorem mem_finiteCells (F : BlockFrame) (hs : ∀ i, 0 < F.extent i) (z : F.Cell) : z ∈ finiteCells F := by apply _root_.YangMills.Construction.FrameTorusAction.mem_finiteCells <;> assumption
theorem minimalAction_eq_actionAtLevel {a : ℝ} {L n : ℕ} [NeZero m] (hL : F.blockSide = L) (hodd : Odd L)
    (hs : ∀ i, F.extent i = n) (hn : 0 < n) (hj : j = F.depth) (hp : ∀ i, F.period j i = m)
    (hmn : m = n * L) (W : F.GaugeField j) :
    minimalAction a (finiteCells F) j W = actionAtLevel a L j Finset.univ (restrictToTorus m W) := by apply _root_.YangMills.Construction.FrameTorusAction.minimalAction_eq_actionAtLevel <;> assumption
end Torus
end FrameComparison
open FrameComparison in
theorem boltzmannWeight_eq_functional : BoltzmannWeightEqFunctional := by
  intro ℓ t x D f hF hR F hFr W hW
  obtain ⟨hL, ht, n, hs, hn⟩ := hFr
  have hn0 := hF.n₀_ge
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      omega
    · exact h
  have hper : ∀ i, F.period F.depth i = n * ℓ.side := by
    intro i
    simp [BlockFrame.period, BlockFrame.top, hs, hL]
  have hp : ∀ i, F.period F.depth i = F.period F.depth 0 := fun i => by rw [hper, hper]
  have hm : ℓ.n₀ ≤ F.period F.depth 0 := by rw [hper]; exact hn
  haveI : NeZero (F.period F.depth 0) := ⟨by omega⟩
  have hcold := isCold_restrictToTorus hp hW
  have hpos1 := hR.positive _ hm _ hcold
  have hflat : IsCold ℓ.threshold (trivialField (F.period F.depth 0)) := by
    intro y μ ν _
    simpa [TorusFields.curvature, TorusFields.holonomy, trivialField] using hF.σ_pos
  have hpos0 := hR.positive _ hm _ hflat
  have hform := hR.form _ hm _ hcold
  have hact : minimalAction ℓ.coupling (finiteCells F) F.depth W =
      actionAtLevel ℓ.coupling ℓ.side t Finset.univ (restrictToTorus (F.period F.depth 0) W) := by
    subst ht
    exact minimalAction_eq_actionAtLevel hL hF.L_odd hs hnpos rfl hp (hper 0) W
  have hsum : ∑ y ∈ sitesOfCells (finiteCells F) F.depth, subtractTrivial (localFamilyOfDensity f) F y W =
      ∑ y, centered f (F.period F.depth 0) y (restrictToTorus _ W) := by
    have hposs : ∀ i, 0 < F.extent i := fun i => by rw [hs]; exact hnpos
    have hoddF : Odd F.blockSide := by rw [hL]; exact hF.L_odd
    refine Finset.sum_nbij' (toTorusSite _) (siteOfTorus F.depth) (fun _ _ => Finset.mem_univ _)
      (fun z _ => mem_sitesOfCells hoddF hposs (mem_finiteCells F hposs) _) ?_ ?_ (fun _ _ => rfl)
    · intro y _
      exact siteOfTorus_toTorusSite hp y
    · intro z _
      exact toTorusSite_siteOfTorus hp z
  unfold lowerBoltzmann
  rw [hact, hsum, ← hform, Real.exp_sub, Real.exp_log hpos1, Real.exp_log hpos0]
  field_simp
end YangMills.Construction.ColdStepAtMirrorFrames
end
