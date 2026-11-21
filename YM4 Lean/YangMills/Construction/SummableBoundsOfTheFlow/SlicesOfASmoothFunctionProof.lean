import YangMills.Construction.SummableBoundsOfTheFlow.SlicesOfASmoothFunction
import Mathlib
set_option autoImplicit false
noncomputable section
open Topology
namespace YangMills.Construction.SmoothSlices
variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
theorem iteratedFDeriv_comp_affine (f : E → ℝ) (L : E' →L[ℝ] E) (a : E) (x : E') (n : ℕ) (v : Fin n → E')
    (hf : ContDiffAt ℝ n f (a + L x)) :
    iteratedFDeriv ℝ n (fun z => f (a + L z)) x v = iteratedFDeriv ℝ n f (a + L x) fun i => L (v i) := by
  set g : E → ℝ := fun e => f (e + a) with hg
  have hshift : iteratedFDeriv ℝ n g (L x) = iteratedFDeriv ℝ n f (L x + a) :=
    iteratedFDeriv_comp_add_right n a (L x)
  have hgc : ContDiffAt ℝ n g (L x) := by
    have : ContDiffAt ℝ n (fun e : E => e + a) (L x) := contDiffAt_id.add contDiffAt_const
    refine ContDiffAt.comp (g := f) (L x) ?_ this
    simpa [add_comm] using hf
  obtain ⟨u, hu, -, hcd⟩ := (hgc.contDiffWithinAt (s := Set.univ)).contDiffOn le_rfl (by simp)
  rw [Set.insert_eq_of_mem (Set.mem_univ _), nhdsWithin_univ] at hu
  obtain ⟨U, hUu, hUo, hxU⟩ := mem_nhds_iff.mp hu
  have hcdU : ContDiffOn ℝ n g U := hcd.mono hUu
  have hpre : IsOpen (L ⁻¹' U) := hUo.preimage L.continuous
  have hcomp := L.iteratedFDerivWithin_comp_right (f := g) (s := U) (x := x) (n := n) (i := n) hcdU
    hUo.uniqueDiffOn hpre.uniqueDiffOn hxU le_rfl
  have hw1 : iteratedFDerivWithin ℝ n (g ∘ L) (L ⁻¹' U) x = iteratedFDeriv ℝ n (g ∘ L) x :=
    iteratedFDerivWithin_of_isOpen n hpre hxU
  have hw2 : iteratedFDerivWithin ℝ n g U (L x) = iteratedFDeriv ℝ n g (L x) :=
    iteratedFDerivWithin_of_isOpen n hUo hxU
  rw [hw1, hw2, hshift] at hcomp
  have hfun : (fun z => f (a + L z)) = g ∘ L := by
    funext z
    simp [hg, add_comm]
  rw [hfun, hcomp, add_comm]
  rfl
variable {P Q : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q]
theorem iteratedFDeriv_slice_eq (G : P × Q → ℝ) (j : ℕ) (w : Fin j → P) (η : Q) (hG : ContDiffAt ℝ j G (0, η)) :
    iteratedFDeriv ℝ j (fun τ => G (τ, η)) 0 w =
      iteratedFDeriv ℝ j G (0, η) fun i => (w i, 0) := by
  have h := iteratedFDeriv_comp_affine G (ContinuousLinearMap.inl ℝ P Q) ((0 : P), η) (0 : P) j w (by simpa using hG)
  have hfun : (fun z : P => G ((0, η) + ContinuousLinearMap.inl ℝ P Q z)) = fun τ => G (τ, η) := by
    funext z
    simp
  rw [hfun] at h
  rw [h]
  simp
theorem contDiffAt_iteratedFDeriv_slice (G : P × Q → ℝ) (j m : ℕ) (w : Fin j → P) (η₀ : Q)
    (hG : ContDiffAt ℝ (m + j : ℕ) G (0, η₀)) :
    ContDiffAt ℝ m (fun η => iteratedFDeriv ℝ j (fun τ => G (τ, η)) 0 w) η₀ := by
  have hemb : ContDiff ℝ (m : WithTop ℕ∞) (fun η : Q => ((0 : P), η)) := contDiff_const.prodMk contDiff_id
  have hmap : ContDiffAt ℝ m (iteratedFDeriv ℝ j G) ((0 : P), η₀) :=
    hG.iteratedFDeriv_right (by norm_cast)
  have h1 : ContDiffAt ℝ m (fun η : Q => iteratedFDeriv ℝ j G (0, η)) η₀ :=
    ContDiffAt.comp (g := iteratedFDeriv ℝ j G) η₀ hmap hemb.contDiffAt
  have h2 : ContDiffAt ℝ m (fun η : Q => iteratedFDeriv ℝ j G (0, η) fun i => (w i, (0 : Q))) η₀ :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => P × Q) ℝ
      fun i => (w i, (0 : Q))).contDiff.contDiffAt.comp η₀ h1
  refine h2.congr_of_eventuallyEq ?_
  have hnt : ∀ N : ℕ, (N : WithTop ℕ∞) ≠ ((⊤ : ℕ∞) : WithTop ℕ∞) := fun N => by simp
  have hev : ∀ᶠ z in 𝓝 ((0 : P), η₀), ContDiffAt ℝ (m + j : ℕ) G z := hG.eventually (hnt _)
  have hcont : Filter.Tendsto (fun η : Q => ((0 : P), η)) (𝓝 η₀) (𝓝 ((0 : P), η₀)) :=
    (continuous_const.prodMk continuous_id).continuousAt
  filter_upwards [hcont.eventually hev] with η hη
  exact iteratedFDeriv_slice_eq G j w η (hη.of_le (by norm_cast; omega))
theorem fderiv_iteratedFDeriv_slice (G : P × Q → ℝ) (j : ℕ) (w : Fin j → P) (η₀ d : Q)
    (hG : ContDiffAt ℝ (j + 1 : ℕ) G (0, η₀)) :
    fderiv ℝ (fun η => iteratedFDeriv ℝ j (fun τ => G (τ, η)) 0 w) η₀ d =
      iteratedFDeriv ℝ (j + 1) G (0, η₀) (Fin.cons (0, d) fun i => (w i, 0)) := by
  have hev : ∀ᶠ z in 𝓝 ((0 : P), η₀), ContDiffAt ℝ (j + 1 : ℕ) G z := hG.eventually (by simp)
  have hcont : Filter.Tendsto (fun η : Q => ((0 : P), η)) (𝓝 η₀) (𝓝 ((0 : P), η₀)) :=
    (continuous_const.prodMk continuous_id).continuousAt
  have hEq : (fun η => iteratedFDeriv ℝ j (fun τ => G (τ, η)) 0 w) =ᶠ[𝓝 η₀]
      fun η => iteratedFDeriv ℝ j G (0, η) fun i => (w i, (0 : Q)) := by
    filter_upwards [hcont.eventually hev] with η hη
    exact iteratedFDeriv_slice_eq G j w η (hη.of_le (by norm_cast; omega))
  rw [hEq.fderiv_eq]
  have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ j G) ((0 : P), η₀) := by
    have : ContDiffAt ℝ 1 (iteratedFDeriv ℝ j G) ((0 : P), η₀) :=
      hG.iteratedFDeriv_right (by norm_cast; omega)
    exact this.differentiableAt (by simp)
  have hemb : HasFDerivAt (fun η : Q => ((0 : P), η)) (ContinuousLinearMap.inr ℝ P Q) η₀ :=
    (hasFDerivAt_const (0 : P) η₀).prodMk (hasFDerivAt_id η₀) |>.congr_fderiv (by ext <;> simp)
  have hc := hdiff.hasFDerivAt.comp η₀ hemb
  have happ := ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => P × Q) ℝ
      fun i => (w i, (0 : Q))).hasFDerivAt (x := iteratedFDeriv ℝ j G ((0 : P), η₀))).comp η₀ hc
  have hf : fderiv ℝ (fun η : Q => iteratedFDeriv ℝ j G (0, η) fun i => (w i, (0 : Q))) η₀ = _ :=
    happ.fderiv
  rw [hf]
  rw [iteratedFDeriv_succ_apply_left]
  simp [Fin.tail_def, Fin.cons_succ]
theorem iteratedFDerivSlices_holds : IteratedFDerivSlices :=
  ⟨fun _ _ _ _ _ _ f L a x n v hf => iteratedFDeriv_comp_affine f L a x n v hf,
    fun _ _ _ _ _ _ G j m w η₀ hG => contDiffAt_iteratedFDeriv_slice G j m w η₀ hG,
    fun _ _ _ _ _ _ G j w η₀ d hG => fderiv_iteratedFDeriv_slice G j w η₀ d hG⟩
end YangMills.Construction.SmoothSlices
end
