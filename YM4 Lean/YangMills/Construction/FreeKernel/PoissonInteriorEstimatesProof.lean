import YangMills.Construction.Dirichlet.LocalRegionGreenEstimatesProof
import YangMills.Construction.FreeKernel.ConvolutionDecayBoundsProof
import YangMills.Construction.FreeKernel.GreenKernelBounds
import Mathlib
set_option autoImplicit false
open scoped ENNReal ContDiff
noncomputable section
namespace YangMills.Construction.PoissonInterior
open YangMills.Construction.InfiniteLattice YangMills.Construction.FreeKernel YangMills.Construction.LatticePoisson YangMills.Construction.Dirichlet
variable {d : ℕ} {ξ : ℝ}
theorem supLength_le_iff [Nonempty (Fin d)] {v : Fin d → ℝ} {s : ℝ} :
    supLength v ≤ s ↔ ∀ μ, |v μ| ≤ s := by apply _root_.YangMills.Construction.Dirichlet.LocalRegion.GridLift.supLength_le_iff <;> assumption
theorem mem_gridCube_iff [Nonempty (Fin d)] {x₀ x : GridSite d ξ} {s : ℝ} :
    x ∈ gridCube x₀ s ↔ ∀ μ, |(x : Fin d → ℝ) μ - (x₀ : Fin d → ℝ) μ| ≤ s := by
  simp only [gridCube, Set.mem_ofPred_eq, supLength_le_iff]
  rfl
def intCoords (x : GridSite d ξ) : Fin d → ℤ := Classical.choose x.2
theorem l1Length_nonneg (v : Fin d → ℝ) : 0 ≤ l1Length v :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _
def cutoff (x₀ : GridSite d ξ) (r : ℝ) : GridSite d ξ → ℝ :=
  fun x => ∏ μ, bumpProfile (((x : Fin d → ℝ) μ - (x₀ : Fin d → ℝ) μ) / r)
theorem cutoff_nonneg (x₀ : GridSite d ξ) (r : ℝ) (x : GridSite d ξ) : 0 ≤ cutoff x₀ r x :=
  Finset.prod_nonneg fun _ _ => bumpProfile_isEvenBump.nonneg _
theorem cutoff_le_one (x₀ : GridSite d ξ) (r : ℝ) (x : GridSite d ξ) : cutoff x₀ r x ≤ 1 :=
  Finset.prod_le_one (fun _ _ => bumpProfile_isEvenBump.nonneg _)
    fun _ _ => bumpProfile_isEvenBump.le_one _
theorem cutoff_eq_one [Nonempty (Fin d)] {r : ℝ} (hr : 0 < r) {x₀ x : GridSite d ξ}
    (hx : x ∈ gridCube x₀ (r / 2)) : cutoff x₀ r x = 1 := by
  refine Finset.prod_eq_one fun μ _ => bumpProfile_isEvenBump.eq_one_of_mem _ ?_
  have := abs_le.1 ((mem_gridCube_iff.1 hx) μ)
  refine Set.mem_Icc.2 ⟨?_, ?_⟩
  · rw [le_div_iff₀ hr]
    linarith [this.1]
  · rw [div_le_iff₀ hr]
    linarith [this.2]
theorem cutoff_eq_zero [Nonempty (Fin d)] {r : ℝ} (hr : 0 < r) {x₀ x : GridSite d ξ}
    (hx : x ∉ gridCube x₀ (2 * r / 3)) : cutoff x₀ r x = 0 := by
  have : ∃ μ, 2 * r / 3 < |(x : Fin d → ℝ) μ - (x₀ : Fin d → ℝ) μ| := by
    by_contra hc
    push Not at hc
    exact hx (mem_gridCube_iff.2 hc)
  obtain ⟨μ, hμ⟩ := this
  refine Finset.prod_eq_zero (Finset.mem_univ μ)
    (bumpProfile_isEvenBump.eq_zero_of_not_mem _ ?_)
  intro hm
  have h1 := Set.mem_Icc.1 hm
  rw [le_div_iff₀ hr, div_le_iff₀ hr] at h1
  have : |(x : Fin d → ℝ) μ - (x₀ : Fin d → ℝ) μ| ≤ 2 * r / 3 :=
    abs_le.2 ⟨by linarith [h1.1], by linarith [h1.2]⟩
  linarith
def IsShellSite (x₀ : GridSite d ξ) (r : ℝ) (z : GridSite d ξ) : Prop :=
  z ∈ gridCube x₀ (3 * r / 4) ∧ ∃ μ, 7 * r / 16 ≤ |(z : Fin d → ℝ) μ - (x₀ : Fin d → ℝ) μ|
section Supports
variable [Nonempty (Fin d)] {r : ℝ} (hξ : 0 < ξ) (hr : 16 * ξ ≤ r) (x₀ : GridSite d ξ)
include hξ hr
end Supports
section Masses
variable [Nonempty (Fin d)] {r N : ℝ} {S : Finset (GridSite d ξ)}
end Masses
theorem zero_le_gridLength (z : GridSite d ξ) : 0 ≤ gridLength z := l1Length_nonneg _
def shellPart (C G₀ : GridSite d ξ → ℝ) (G : Fin d → GridSite d ξ → ℝ)
    (w : List (Fin d ⊕ Fin d)) : GridSite d ξ → ℝ :=
  fun x => latticeConv (iteratedDiff w C) G₀ x +
    ∑ μ, latticeConv (iteratedDiff (w ++ [Sum.inr μ]) C) (G μ) x
def QuarterCubeBound (x₀ : GridSite d ξ) (r N a : ℝ) (b : ℝ → ℝ) (f : GridSite d ξ → ℝ) : Prop :=
  ∀ x ∈ gridCube x₀ (r / 4), ∀ x' ∈ gridCube x₀ (r / 4), |f x| ≤ a * N ∧
    ∀ α : ℝ, 0 < α → α < 1 → |f x - f x'| ≤ b α * holderFactor r α x x' * N
theorem zero_le_holderFactor {r α : ℝ} (hr : 0 < r) (x x' : GridSite d ξ) :
    0 ≤ holderFactor r α x x' :=
  Real.rpow_nonneg (div_nonneg (l1Length_nonneg _) hr.le) _
section QuarterCube
variable {x₀ : GridSite d ξ} {r N a a' : ℝ} {b b' : ℝ → ℝ} {f g : GridSite d ξ → ℝ}
theorem QuarterCubeBound.add (hf : QuarterCubeBound x₀ r N a b f)
    (hg : QuarterCubeBound x₀ r N a' b' g) :
    QuarterCubeBound x₀ r N (a + a') (fun α => b α + b' α) (fun x => f x + g x) := by
  intro x hx x' hx'
  obtain ⟨f₁, f₂⟩ := hf x hx x' hx'
  obtain ⟨g₁, g₂⟩ := hg x hx x' hx'
  refine ⟨(abs_add_le _ _).trans (by linarith), fun α h₀ h₁ => ?_⟩
  have e : f x + g x - (f x' + g x') = (f x - f x') + (g x - g x') := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  have := f₂ α h₀ h₁
  have := g₂ α h₀ h₁
  linarith
theorem QuarterCubeBound.sum {h : Fin d → GridSite d ξ → ℝ}
    (hh : ∀ μ, QuarterCubeBound x₀ r N a b (h μ)) :
    QuarterCubeBound x₀ r N (d * a) (fun α => d * b α) (fun x => ∑ μ, h μ x) := by
  intro x hx x' hx'
  refine ⟨?_, fun α h₀ h₁ => ?_⟩
  · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun μ _ => (hh μ x hx x' hx').1).trans ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    apply le_of_eq
    ring
  · rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun μ _ => (hh μ x hx x' hx').2 α h₀ h₁).trans ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    apply le_of_eq
    ring
theorem QuarterCubeBound.mono (hr : 0 < r) (hN : 0 ≤ N) (ha : a ≤ a')
    (hb : ∀ α, 0 < α → α < 1 → b α ≤ b' α)
    (hf : QuarterCubeBound x₀ r N a b f) : QuarterCubeBound x₀ r N a' b' f := by
  intro x hx x' hx'
  obtain ⟨f₁, f₂⟩ := hf x hx x' hx'
  refine ⟨f₁.trans (mul_le_mul_of_nonneg_right ha hN), fun α h₀ h₁ => (f₂ α h₀ h₁).trans ?_⟩
  refine mul_le_mul_of_nonneg_right ?_ hN
  exact mul_le_mul_of_nonneg_right (hb α h₀ h₁) (zero_le_holderFactor hr x x')
theorem QuarterCubeBound.congr (h : ∀ x ∈ gridCube x₀ (r / 4), f x = g x)
    (hf : QuarterCubeBound x₀ r N a b f) : QuarterCubeBound x₀ r N a b g := by
  intro x hx x' hx'
  rw [← h x hx, ← h x' hx']
  exact hf x hx x' hx'
end QuarterCube
section Terms
variable [Nonempty (Fin d)] {C : GridSite d ξ → ℝ} {cK c r N : ℝ} {cKα : ℝ → ℝ}
  {x₀ : GridSite d ξ}
end Terms
end YangMills.Construction.PoissonInterior
