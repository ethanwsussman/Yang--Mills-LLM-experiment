import YangMills.Construction.OneLoopLaw.DecayOfTheKernelsOfASymbol
import YangMills.Construction.PeriodicOperators.BoundOfTheKernelOfAMatrixFunctionProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter
noncomputable section
namespace YangMills.Construction.OneLoopLaw.SymbolKernelDecay
open YangMills.Construction.PeriodicOperators YangMills.Construction.PeriodicOperators.RiemannSums
open YangMills.Construction.OneLoopLaw.TemperedStiffness
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.TorusMetric (l1NormVec)
def planeWave (u : Fin 4 → ℤ) (κ : Fin 4 → ℂ) : ℂ :=
  Complex.exp (Complex.I * bilinDot κ (toComplexVec (castVec u)))
theorem planeWave_add (u : Fin 4 → ℤ) (κ κ' : Fin 4 → ℂ) :
    planeWave u (κ + κ') = planeWave u κ * planeWave u κ' := by
  simp only [planeWave, ← Complex.exp_add]
  congr 1
  simp only [bilinDot, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring
theorem norm_planeWave (u : Fin 4 → ℤ) (κ : Fin 4 → ℂ) :
    ‖planeWave u κ‖ = Real.exp (-∑ μ, (u μ : ℝ) * (κ μ).im) := by
  rw [planeWave, Complex.norm_exp, Complex.I_mul_re]
  congr 2
  simp [bilinDot, toComplexVec, castVec, Complex.im_sum, mul_comm]
theorem planeWave_eq_one_of_mem_periodLattice (u : Fin 4 → ℤ) {p : AmbientSpace}
    (hp : p ∈ periodLattice) : planeWave u (toComplexVec p) = 1 := by
  obtain ⟨k, hk⟩ := hp
  rw [planeWave, Complex.exp_eq_one_iff]
  refine ⟨∑ μ, k μ * u μ, ?_⟩
  simp only [bilinDot, toComplexVec, castVec, hk]
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun μ _ => ?_
  ring
theorem continuous_planeWave (u : Fin 4 → ℤ) : Continuous (planeWave u) := by
  unfold planeWave bilinDot
  fun_prop
theorem differentiable_planeWave_affine (u : Fin 4 → ℤ) (a e : Fin 4 → ℂ) :
    Differentiable ℂ fun ζ : ℂ => planeWave u (a + ζ • e) := by
  simp only [planeWave, bilinDot, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  fun_prop
theorem holomorphicNearStrip_mul_planeWave {δ : ℝ} {g : (Fin 4 → ℂ) → ℂ}
    (hg : HolomorphicNearStrip δ g) (u : Fin 4 → ℤ) :
    HolomorphicNearStrip δ fun κ => g κ * planeWave u κ := by
  obtain ⟨U, hU, hUo, hcont, hdiff⟩ := hg
  refine ⟨U, hU, hUo, ?_, fun a ha j => ?_⟩
  · refine continuousOn_pi.2 fun _ => ?_
    exact (continuousOn_pi.1 hcont 0).mul (continuous_planeWave u).continuousOn
  · filter_upwards [hdiff a ha j] with ζ hζ
    refine differentiableAt_pi.2 fun _ => ?_
    exact (differentiableAt_pi.1 hζ 0).mul (differentiable_planeWave_affine u a _ ζ)
theorem periodicOnStrip_mul_planeWave {δ : ℝ} {g : (Fin 4 → ℂ) → ℂ} (hg : PeriodicOnStrip δ g)
    (u : Fin 4 → ℤ) : PeriodicOnStrip δ fun κ => g κ * planeWave u κ := by
  intro κ hκ p hper
  show g _ * planeWave u _ = g _ * planeWave u _
  rw [planeWave_add, planeWave_eq_one_of_mem_periodLattice u hper, mul_one, hg κ hκ p hper]
theorem boundedOnStrip_mul_planeWave {δ : ℝ} {g : (Fin 4 → ℂ) → ℂ} (hg : BoundedOnStrip δ g)
    (u : Fin 4 → ℤ) : BoundedOnStrip δ fun κ => g κ * planeWave u κ := by
  obtain ⟨C, hC⟩ := hg
  refine ⟨C * Real.exp (∑ μ, |(u μ : ℝ)| * δ), fun κ hκ => ?_⟩
  rw [norm_mul, norm_planeWave]
  refine mul_le_mul (hC κ hκ) ?_ (Real.exp_pos _).le ((norm_nonneg _).trans (hC κ hκ))
  refine Real.exp_le_exp.2 ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun μ _ => ?_
  calc -((u μ : ℝ) * (κ μ).im) ≤ |(u μ : ℝ) * (κ μ).im| := neg_le_abs _
    _ = |(u μ : ℝ)| * |(κ μ).im| := abs_mul _ _
    _ ≤ |(u μ : ℝ)| * δ := by gcongr; exact hκ μ
theorem norm_torusAverage_le (f : AmbientSpace → ℂ) {C : ℝ} (hC : ∀ κ, ‖f κ‖ ≤ C) :
    ‖torusAverage f‖ ≤ C := by apply _root_.YangMills.Construction.PeriodicOperators.MatrixFunctionKernel.norm_torusAverage_le <;> assumption
def contourShift (δ : ℝ) (u : Fin 4 → ℤ) : Fin 4 → ℂ :=
  fun μ => (((if 0 ≤ u μ then δ else -δ : ℝ)) : ℂ) * Complex.I
theorem contourShift_im (δ : ℝ) (u : Fin 4 → ℤ) (μ : Fin 4) :
    (contourShift δ u μ).im = if 0 ≤ u μ then δ else -δ := by
  simp [contourShift]
theorem contourShift_mem_imStrip {δ : ℝ} (hδ : 0 < δ) (u : Fin 4 → ℤ) :
    contourShift δ u ∈ imStrip δ := by
  intro μ
  rw [contourShift_im]
  split_ifs <;> simp [abs_of_pos hδ]
theorem sum_mul_im_add_contourShift (δ : ℝ) (u : Fin 4 → ℤ) (x : AmbientSpace) :
    ∑ μ, (u μ : ℝ) * ((toComplexVec x + contourShift δ u) μ).im =
      δ * l1NormVec (castVec u) := by
  simp only [l1NormVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have hx : ((toComplexVec x + contourShift δ u) μ).im = (contourShift δ u μ).im := by
    simp [toComplexVec]
  rw [hx, contourShift_im]
  by_cases h : 0 ≤ u μ
  · have h' : (0 : ℝ) ≤ (u μ : ℝ) := by exact_mod_cast h
    simp only [if_pos h, castVec, abs_of_nonneg h']
    ring
  · have h' : (u μ : ℝ) < 0 := by exact_mod_cast not_le.1 h
    simp only [if_neg h, castVec, abs_of_neg h']
    ring
theorem norm_le_stripSup {δ : ℝ} {g : (Fin 4 → ℂ) → ℂ} (hg : BoundedOnStrip δ g)
    {κ : Fin 4 → ℂ} (hκ : κ ∈ imStrip δ) : ‖g κ‖ ≤ stripSup δ g := by
  obtain ⟨C, hC⟩ := hg
  have hbdd : BddAbove (range fun κ : imStrip δ => ‖g κ‖) := by
    refine ⟨C, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact hC x x.2
  exact le_ciSup hbdd (⟨κ, hκ⟩ : imStrip δ)
theorem symbolKernelDecay (hR : RiemannSums.Claim) : SymbolKernelDecayClaim := by
  intro δ g hδ hh hp hb u
  have hshift := (hR 1 δ (fun κ => g κ * planeWave u κ) one_pos hδ
    (holomorphicNearStrip_mul_planeWave hh u) (periodicOnStrip_mul_planeWave hp u)
    (boundedOnStrip_mul_planeWave hb u)).2 (contourShift δ u) (contourShift_mem_imStrip hδ u)
  have hk : symbolKernel g u =
      torusAverage fun κ => g (toComplexVec κ + contourShift δ u) *
        planeWave u (toComplexVec κ + contourShift δ u) := hshift.symm
  rw [hk]
  refine norm_torusAverage_le _ fun κ => ?_
  have hmem : toComplexVec κ + contourShift δ u ∈ imStrip δ := by
    intro μ
    have := contourShift_mem_imStrip hδ u μ
    simpa [toComplexVec] using this
  rw [norm_mul, norm_planeWave, sum_mul_im_add_contourShift, neg_mul_eq_neg_mul]
  exact mul_le_mul_of_nonneg_right (norm_le_stripSup hb hmem) (Real.exp_pos _).le
end YangMills.Construction.OneLoopLaw.SymbolKernelDecay
end
