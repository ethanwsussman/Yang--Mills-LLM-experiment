import YangMills.Construction.Lattice.DerivativeOfAHolomorphicMapAndOpenBalls
import YangMills.Construction.PeriodicOperators.CalculusOfSymbolsProof
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped ENNReal Nat Topology
noncomputable section
namespace YangMills.Construction.PeriodicOperators.EntriesDets
open Coordinates (ComplexCoordinates)
open Coordinates.ComplexCoordinates (stdBasisVector)
section Basics
variable {n : ℕ} {O : Set (ComplexCoordinates n)} {u v : ComplexCoordinates n → ℂ}
theorem add_smul_stdBasisVector_shift (a : ComplexCoordinates n) (j : Fin n) (ζ₀ ζ : ℂ) :
    a + ζ₀ • stdBasisVector j + (ζ - ζ₀) • stdBasisVector j = a + ζ • stdBasisVector j := by
  rw [add_assoc, ← add_smul]
  simp
theorem differentiableAt_line_of_translate {a : ComplexCoordinates n} {j : Fin n} {ζ₀ : ℂ}
    (h : DifferentiableAt ℂ (fun ζ : ℂ => u (a + ζ₀ • stdBasisVector j + ζ • stdBasisVector j)) 0) :
    DifferentiableAt ℂ (fun ζ : ℂ => u (a + ζ • stdBasisVector j)) ζ₀ := by
  have e : (fun ζ : ℂ => u (a + ζ • stdBasisVector j)) =
      (fun ξ : ℂ => u (a + ζ₀ • stdBasisVector j + ξ • stdBasisVector j)) ∘ fun ζ : ℂ => ζ - ζ₀ := by
    funext ζ
    simp only [Function.comp_apply, add_smul_stdBasisVector_shift]
  rw [e]
  refine DifferentiableAt.comp ζ₀ ?_ (by fun_prop)
  simpa using h
theorem continuous_coordLine (a : ComplexCoordinates n) (j : Fin n) :
    Continuous fun ζ : ℂ => a + ζ • stdBasisVector j := by
  fun_prop
theorem holomorphicFnOn_iff : HolomorphicFnOn O u ↔
    IsOpen O ∧ ContinuousOn u O ∧ ∀ a ∈ O, ∀ j : Fin n,
      DifferentiableAt ℂ (fun ζ : ℂ => u (a + ζ • stdBasisVector j)) 0 := by
  constructor
  · rintro ⟨hO, hc, hd⟩
    refine ⟨hO, continuousOn_pi.1 hc 0, fun a ha j => ?_⟩
    exact differentiableAt_pi.1 (hd a ha j).self_of_nhds 0
  · rintro ⟨hO, hc, hd⟩
    refine ⟨hO, continuousOn_pi.2 fun _ => hc, fun a ha j => ?_⟩
    have hU : ∀ᶠ ζ in 𝓝 (0 : ℂ), a + ζ • stdBasisVector j ∈ O := by
      have : ContinuousAt (fun ζ : ℂ => a + ζ • stdBasisVector j) 0 :=
        (continuous_coordLine a j).continuousAt
      exact this.eventually_mem (by simpa using hO.mem_nhds ha)
    filter_upwards [hU] with ζ hζ
    exact differentiableAt_pi.2 fun _ => differentiableAt_line_of_translate (hd _ hζ j)
theorem HolomorphicFnOn.isOpen_set (h : HolomorphicFnOn O u) : IsOpen O :=
  (holomorphicFnOn_iff.1 h).1
theorem HolomorphicFnOn.continuousOn (h : HolomorphicFnOn O u) :
    ContinuousOn u O :=
  (holomorphicFnOn_iff.1 h).2.1
theorem HolomorphicFnOn.onLine (h : HolomorphicFnOn O u) {a : ComplexCoordinates n}
    (ha : a ∈ O) (j : Fin n) :
    DifferentiableAt ℂ (fun ζ : ℂ => u (a + ζ • stdBasisVector j)) 0 :=
  (holomorphicFnOn_iff.1 h).2.2 a ha j
theorem HolomorphicFnOn.onLine_at (h : HolomorphicFnOn O u) {a : ComplexCoordinates n}
    {j : Fin n} {ζ₀ : ℂ} (ha : a + ζ₀ • stdBasisVector j ∈ O) :
    DifferentiableAt ℂ (fun ζ : ℂ => u (a + ζ • stdBasisVector j)) ζ₀ :=
  differentiableAt_line_of_translate (h.onLine ha j)
theorem eventually_coordLine_mem (hO : IsOpen O) {a : ComplexCoordinates n} {j : Fin n} {ζ₀ : ℂ}
    (ha : a + ζ₀ • stdBasisVector j ∈ O) :
    ∀ᶠ ζ in 𝓝 ζ₀, a + ζ • stdBasisVector j ∈ O :=
  (continuous_coordLine a j).continuousAt.eventually_mem (hO.mem_nhds ha)
theorem eventually_coordLine_mem_zero (hO : IsOpen O) {a : ComplexCoordinates n} (j : Fin n)
    (ha : a ∈ O) :
    ∀ᶠ ζ in 𝓝 (0 : ℂ), a + ζ • stdBasisVector j ∈ O :=
  eventually_coordLine_mem (ζ₀ := 0) hO (by simpa using ha)
theorem HolomorphicFnOn.congr_on (h : HolomorphicFnOn O u)
    (e : ∀ z ∈ O, v z = u z) : HolomorphicFnOn O v := by
  refine holomorphicFnOn_iff.2 ⟨h.isOpen_set, h.continuousOn.congr e, fun a ha j => ?_⟩
  refine (h.onLine ha j).congr_of_eventuallyEq ?_
  filter_upwards [eventually_coordLine_mem_zero h.isOpen_set j ha] with ζ hζ
  exact e _ hζ
theorem holomorphicFnOn_const (hO : IsOpen O) (c : ℂ) : HolomorphicFnOn O fun _ => c :=
  holomorphicFnOn_iff.2 ⟨hO, continuousOn_const, fun _ _ _ => differentiableAt_const _⟩
theorem HolomorphicFnOn.add (hu : HolomorphicFnOn O u)
    (hv : HolomorphicFnOn O v) : HolomorphicFnOn O fun z => u z + v z :=
  holomorphicFnOn_iff.2 ⟨hu.isOpen_set, hu.continuousOn.add hv.continuousOn, fun _ ha j =>
    (hu.onLine ha j).add (hv.onLine ha j)⟩
theorem HolomorphicFnOn.mul (hu : HolomorphicFnOn O u)
    (hv : HolomorphicFnOn O v) : HolomorphicFnOn O fun z => u z * v z :=
  holomorphicFnOn_iff.2 ⟨hu.isOpen_set, hu.continuousOn.mul hv.continuousOn, fun _ ha j =>
    (hu.onLine ha j).mul (hv.onLine ha j)⟩
theorem HolomorphicFnOn.cexp (hu : HolomorphicFnOn O u) :
    HolomorphicFnOn O fun z => Complex.exp (u z) :=
  holomorphicFnOn_iff.2 ⟨hu.isOpen_set, Complex.continuous_exp.comp_continuousOn hu.continuousOn,
    fun _ ha j => (hu.onLine ha j).cexp⟩
theorem HolomorphicFnOn.inv (hu : HolomorphicFnOn O u) (h0 : ∀ z ∈ O, u z ≠ 0) :
    HolomorphicFnOn O fun z => (u z)⁻¹ :=
  holomorphicFnOn_iff.2 ⟨hu.isOpen_set, hu.continuousOn.inv₀ h0, fun a ha j =>
    (hu.onLine ha j).inv (by simpa using h0 a ha)⟩
theorem holomorphicFnOn_sum {ι : Type} (hO : IsOpen O) (s : Finset ι)
    (w : ι → ComplexCoordinates n → ℂ) (h : ∀ i, HolomorphicFnOn O (w i)) :
    HolomorphicFnOn O fun z => ∑ i ∈ s, w i z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using holomorphicFnOn_const hO 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a).add ih
theorem holomorphicFnOn_prod {ι : Type} (hO : IsOpen O) (s : Finset ι)
    (w : ι → ComplexCoordinates n → ℂ) (h : ∀ i, HolomorphicFnOn O (w i)) :
    HolomorphicFnOn O fun z => ∏ i ∈ s, w i z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using holomorphicFnOn_const hO 1
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a).mul ih
theorem holomorphicFnOn_mvEval {σ : Type} (hO : IsOpen O) (w : σ → ComplexCoordinates n → ℂ)
    (P : MvPolynomial σ ℂ) (h : ∀ i, HolomorphicFnOn O (w i)) :
    HolomorphicFnOn O fun z => MvPolynomial.eval (fun i => w i z) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simpa using holomorphicFnOn_const hO c
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp => simpa using hp.mul (h i)
theorem holomorphicFnOn_coord (j : Fin n) :
    HolomorphicFnOn univ fun z : ComplexCoordinates n => z j := by
  refine holomorphicFnOn_iff.2 ⟨isOpen_univ, (continuous_apply j).continuousOn, fun a _ i => ?_⟩
  have e : (fun ζ : ℂ => (a + ζ • stdBasisVector i) j) =
      fun ζ : ℂ => a j + ζ * stdBasisVector i j := by
    funext ζ
    simp
  simp only [e]
  fun_prop
theorem HolomorphicFnOn.mono_set (h : HolomorphicFnOn O u)
    {O' : Set (ComplexCoordinates n)} (hO' : IsOpen O') (hs : O' ⊆ O) :
    HolomorphicFnOn O' u :=
  holomorphicFnOn_iff.2 ⟨hO', h.continuousOn.mono hs, fun _ ha j => h.onLine (hs ha) j⟩
theorem holomorphicFnOn_of_locally (hO : IsOpen O)
    (h : ∀ z ∈ O, ∃ O' : Set (ComplexCoordinates n), IsOpen O' ∧ z ∈ O' ∧ O' ⊆ O ∧
      HolomorphicFnOn O' u) : HolomorphicFnOn O u := by
  refine holomorphicFnOn_iff.2 ⟨hO, fun z hz => ?_, fun z hz j => ?_⟩
  · obtain ⟨O', hO', hzO', -, hu⟩ := h z hz
    exact ((hu.continuousOn z hzO').continuousAt (hO'.mem_nhds hzO')).continuousWithinAt
  · obtain ⟨O', -, hzO', -, hu⟩ := h z hz
    exact hu.onLine hzO' j
theorem holomorphicFnOn_comp_zero {F : ComplexCoordinates n → ComplexCoordinates 1}
    (h : ComplexCoordinates.IsHolomorphicIn O F) : HolomorphicFnOn O fun z => F z 0 := by
  have e : (fun (z : ComplexCoordinates n) (_ : Fin 1) => F z 0) = F := by
    funext z i
    rw [Subsingleton.elim i 0]
  change ComplexCoordinates.IsHolomorphicIn O fun z _ => F z 0
  rw [e]
  exact h
end Basics
section Partials
variable {n : ℕ} {O : Set (ComplexCoordinates n)} {u v : ComplexCoordinates n → ℂ}
theorem HolomorphicFnOn.differentiableAt
    (hP : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (h : HolomorphicFnOn O u) {z : ComplexCoordinates n} (hz : z ∈ O) :
    DifferentiableAt ℂ u z := by
  obtain ⟨L, hL⟩ := ((hP.1 n O h.isOpen_set).1 1 (fun z _ => u z) h).2.2.1 z hz
  have hL' : HasFDerivAt (fun z (_ : Fin 1) => u z) L z := hasFDerivAt_of_restrictScalars ℝ hL rfl
  exact (hasFDerivAt_pi'.1 hL' 0).differentiableAt
theorem hasDerivAt_complexLine (z : ComplexCoordinates n) (k : ComplexCoordinates n) :
    HasDerivAt (fun ζ : ℂ => z + ζ • k) k 0 := by
  simpa using ((hasDerivAt_id (0 : ℂ)).smul_const k).const_add z
theorem hasDerivAt_realLine (z : ComplexCoordinates n) (k : ComplexCoordinates n) :
    HasDerivAt (fun s : ℝ => z + s • k) k 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).smul_const k).const_add z
theorem hasDerivAt_comp_complexLine {z k : ComplexCoordinates n} (hu : DifferentiableAt ℂ u z) :
    HasDerivAt (fun ζ : ℂ => u (z + ζ • k)) (fderiv ℂ u z k) 0 := by
  have hu' : HasFDerivAt u (fderiv ℂ u z) (z + (0 : ℂ) • k) := by
    simpa using hu.hasFDerivAt
  exact hu'.comp_hasDerivAt (0 : ℂ) (hasDerivAt_complexLine z k)
theorem partialDeriv_eq_fderiv {z : ComplexCoordinates n} (hu : DifferentiableAt ℂ u z)
    (j : Fin n) : partialDeriv j u z = fderiv ℂ u z (stdBasisVector j) :=
  (hasDerivAt_comp_complexLine hu).deriv
theorem partialDeriv_congr (hO : IsOpen O) (e : ∀ z ∈ O, u z = v z)
    {z : ComplexCoordinates n} (hz : z ∈ O) (j : Fin n) :
    partialDeriv j u z = partialDeriv j v z := by
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [eventually_coordLine_mem_zero hO j hz] with ζ hζ using e _ hζ
theorem fderiv_real_single_eq {z k : ComplexCoordinates n} (hu : DifferentiableAt ℂ u z) :
    fderiv ℝ (fun z (_ : Fin 1) => u z) z k 0 = fderiv ℂ u z k := by
  have hpi : HasFDerivAt (fun z (_ : Fin 1) => u z)
      (ContinuousLinearMap.pi fun _ : Fin 1 => fderiv ℂ u z) z :=
    hasFDerivAt_pi.2 fun _ => hu.hasFDerivAt
  rw [(hpi.restrictScalars ℝ).fderiv]
  rfl
theorem holomorphicFnOn_fderiv_apply
    (hD : SeparatedFrame.HolomorphicDerivatives.Claim)
    (h : HolomorphicFnOn O u) (k : ComplexCoordinates n) :
    HolomorphicFnOn O fun z => fderiv ℝ (fun z (_ : Fin 1) => u z) z k 0 :=
  holomorphicFnOn_comp_zero ((hD n 1 O (fun z _ => u z) h).1 k)
theorem holomorphicFnOn_partialDeriv
    (hP : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hD : SeparatedFrame.HolomorphicDerivatives.Claim)
    (h : HolomorphicFnOn O u) (j : Fin n) :
    HolomorphicFnOn O (partialDeriv j u) :=
  (holomorphicFnOn_fderiv_apply hD h (stdBasisVector j)).congr_on fun z hz => by
    rw [partialDeriv_eq_fderiv (h.differentiableAt hP hz),
      fderiv_real_single_eq (h.differentiableAt hP hz)]
theorem partialDeriv_partialDeriv_eq_secondDeriv
    (hP : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hD : SeparatedFrame.HolomorphicDerivatives.Claim)
    (h : HolomorphicFnOn O u) {z : ComplexCoordinates n} (hz : z ∈ O) (i j : Fin n) :
    partialDeriv i (partialDeriv j u) z =
      ComplexCoordinates.secondDeriv (fun z (_ : Fin 1) => u z) z
        (stdBasisVector i) (stdBasisVector j) 0 := by
  set f : ComplexCoordinates n → ComplexCoordinates 1 := fun z _ => u z with hf
  set G : ComplexCoordinates n → ℂ := fun w => fderiv ℝ f w (stdBasisVector j) 0 with hG
  have hGh : HolomorphicFnOn O G := holomorphicFnOn_fderiv_apply hD h (stdBasisVector j)
  have e₁ : partialDeriv i (partialDeriv j u) z = partialDeriv i G z := by
    refine partialDeriv_congr h.isOpen_set (fun w hw => ?_) hz i
    rw [partialDeriv_eq_fderiv (h.differentiableAt hP hw)]
    exact (fderiv_real_single_eq (h.differentiableAt hP hw)).symm
  have hGd := hGh.differentiableAt hP hz
  rw [e₁, partialDeriv_eq_fderiv hGd]
  have hline : HasDerivAt (fun s : ℝ => G (z + s • stdBasisVector i))
      (fderiv ℂ G z (stdBasisVector i)) 0 := by
    have h0 : HasFDerivAt G ((fderiv ℂ G z).restrictScalars ℝ)
        (z + (0 : ℝ) • stdBasisVector i) := by
      simpa using hGd.hasFDerivAt.restrictScalars ℝ
    exact h0.comp_hasDerivAt (0 : ℝ) (hasDerivAt_realLine z (stdBasisVector i))
  have hd := ((hD n 1 O f h).2 z hz).1 (stdBasisVector i) (stdBasisVector j)
  have hd' := (hasDerivAt_pi.1 hd.hasDerivAt) 0
  exact hline.unique hd'
theorem partialDeriv_comm
    (hP : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hD : SeparatedFrame.HolomorphicDerivatives.Claim)
    (h : HolomorphicFnOn O u) {z : ComplexCoordinates n} (hz : z ∈ O) (i j : Fin n) :
    partialDeriv i (partialDeriv j u) z =
      partialDeriv j (partialDeriv i u) z := by
  rw [partialDeriv_partialDeriv_eq_secondDeriv hP hD h hz i j,
    partialDeriv_partialDeriv_eq_secondDeriv hP hD h hz j i,
    ((hD n 1 O (fun z _ => u z) h).2 z hz).2.2 (stdBasisVector i) (stdBasisVector j)]
theorem iteratedPartial_cons (j : Fin n) (l : List (Fin n)) (w : ComplexCoordinates n → ℂ) :
    iteratedPartial (j :: l) w = partialDeriv j (iteratedPartial l w) :=
  rfl
theorem holomorphicFnOn_iteratedPartial
    (hP : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hD : SeparatedFrame.HolomorphicDerivatives.Claim)
    (h : HolomorphicFnOn O u) (l : List (Fin n)) :
    HolomorphicFnOn O (iteratedPartial l u) := by
  induction l with
  | nil => exact h
  | cons j l ih => exact holomorphicFnOn_partialDeriv hP hD ih j
theorem iteratedPartial_perm
    (hP : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hD : SeparatedFrame.HolomorphicDerivatives.Claim)
    (h : HolomorphicFnOn O u) {l l' : List (Fin n)} (hp : l.Perm l') :
    ∀ z ∈ O, iteratedPartial l u z = iteratedPartial l' u z := by
  induction hp with
  | nil => intro z _; rfl
  | cons x _ ih => intro z hz; exact partialDeriv_congr h.isOpen_set ih hz x
  | swap x y l =>
    intro z hz
    exact partialDeriv_comm hP hD (holomorphicFnOn_iteratedPartial hP hD h l) hz y x
  | trans _ _ ih₁ ih₂ => intro z hz; exact (ih₁ z hz).trans (ih₂ z hz)
theorem partialsHolomorphicComm_holds
    (hP : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hD : SeparatedFrame.HolomorphicDerivatives.Claim) :
    PartialsHolomorphicComm O := fun _ h =>
  ⟨fun j => holomorphicFnOn_partialDeriv hP hD h j, fun _ _ hp z hz =>
    iteratedPartial_perm hP hD h hp z hz⟩
theorem iteratedPartial_congr (hO : IsOpen O) (e : ∀ z ∈ O, u z = v z) (l : List (Fin n)) :
    ∀ z ∈ O, iteratedPartial l u z = iteratedPartial l v z := by
  induction l with
  | nil => exact e
  | cons j l ih => intro z hz; exact partialDeriv_congr hO ih hz j
theorem partialDeriv_sum_mul
    {ι : Type} (s : Finset ι) (c : ι → ℂ) (w : ι → ComplexCoordinates n → ℂ)
    (h : ∀ i, HolomorphicFnOn O (w i)) {z : ComplexCoordinates n} (hz : z ∈ O) (j : Fin n) :
    partialDeriv j (fun z => ∑ i ∈ s, c i * w i z) z =
      ∑ i ∈ s, c i * partialDeriv j (w i) z := by
  have hd : ∀ i ∈ s, HasDerivAt (fun ζ : ℂ => c i * w i (z + ζ • stdBasisVector j))
      (c i * partialDeriv j (w i) z) 0 := fun i _ =>
    ((h i).onLine hz j).hasDerivAt.const_mul (c i)
  exact (HasDerivAt.fun_sum hd).deriv
theorem iteratedPartial_sum_mul
    (hP : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hD : SeparatedFrame.HolomorphicDerivatives.Claim)
    (hO : IsOpen O)
    {ι : Type} (s : Finset ι) (c : ι → ℂ) (w : ι → ComplexCoordinates n → ℂ)
    (h : ∀ i, HolomorphicFnOn O (w i)) (l : List (Fin n)) :
    ∀ z ∈ O, iteratedPartial l (fun z => ∑ i ∈ s, c i * w i z) z =
      ∑ i ∈ s, c i * iteratedPartial l (w i) z := by
  induction l with
  | nil => intro z _; rfl
  | cons j l ih =>
    intro z hz
    rw [iteratedPartial_cons, partialDeriv_congr hO ih hz j]
    exact partialDeriv_sum_mul s c _ (fun i => holomorphicFnOn_iteratedPartial hP hD (h i) l) hz j
theorem holomorphicFnOn_sum_mul (hO : IsOpen O) {ι : Type} (s : Finset ι) (c : ι → ℂ)
    (w : ι → ComplexCoordinates n → ℂ) (h : ∀ i, HolomorphicFnOn O (w i)) :
    HolomorphicFnOn O fun z => ∑ i ∈ s, c i * w i z :=
  holomorphicFnOn_sum hO s _ fun i => (holomorphicFnOn_const hO (c i)).mul (h i)
theorem map_linCombPartial
    (hP : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hD : SeparatedFrame.HolomorphicDerivatives.Claim)
    (hO : IsOpen O) {X : Type} [AddCommGroup X] [Module ℂ X] (χ : X →ₗ[ℂ] ℂ) {b : ℕ}
    (w : Fin b → ComplexCoordinates n → ℂ) (x : Fin b → X)
    (h : ∀ i, HolomorphicFnOn O (w i)) (q : Fin n → ℕ) {z : ComplexCoordinates n}
    (hz : z ∈ O) :
    χ (linCombPartial q w x z) =
      multiPartial q (fun z => ∑ i, χ (x i) * w i z) z := by
  rw [multiPartial, iteratedPartial_sum_mul hP hD hO _ _ _ h _ z hz]
  simp only [linCombPartial, linComb, map_sum, map_smul, smul_eq_mul, multiPartial]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _
theorem map_linComb {X : Type} [AddCommGroup X] [Module ℂ X] (χ : X →ₗ[ℂ] ℂ) {b : ℕ}
    (w : Fin b → ComplexCoordinates n → ℂ) (x : Fin b → X) (z : ComplexCoordinates n) :
    χ (linComb w x z) = ∑ i, χ (x i) * w i z := by
  simp only [linComb, map_sum, map_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _
theorem linCombPartialWellDefined_holds
    (hP : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hD : SeparatedFrame.HolomorphicDerivatives.Claim)
    (hO : IsOpen O) (X : Type) [AddCommGroup X] [Module ℂ X] :
    LinCombPartialWellDefined O X := by
  intro b b' x x' w w' hw hw' he q z hz
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun χ => ?_
  rw [map_sub, sub_eq_zero, map_linCombPartial hP hD hO χ w' x' hw' q hz,
    map_linCombPartial hP hD hO χ w x hw q hz]
  refine iteratedPartial_congr hO (fun y hy => ?_) _ z hz
  rw [← map_linComb, ← map_linComb, he y hy]
theorem complexLinCombPartials_holds
    (hP : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hD : SeparatedFrame.HolomorphicDerivatives.Claim)
    (hO : IsOpen O) : ComplexLinCombPartials O := by
  intro b x w hw
  have e : linComb w x = fun z => ∑ i, x i * w i z := by
    funext z
    simp only [linComb, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  refine ⟨e ▸ holomorphicFnOn_sum_mul hO _ _ _ hw, fun q z hz => ?_⟩
  have := map_linCombPartial hP hD hO (LinearMap.id : ℂ →ₗ[ℂ] ℂ) w x hw q hz
  simp only [LinearMap.id_apply] at this
  rw [this, e]
end Partials
section Cauchy
variable {n : ℕ} {O : Set (ComplexCoordinates n)} {u w : ComplexCoordinates n → ℂ}
theorem deriv_comp_coordLine (g : ComplexCoordinates n → ℂ) (z : ComplexCoordinates n) (j : Fin n)
    (ζ : ℂ) :
    deriv (fun ξ : ℂ => g (z + ξ • stdBasisVector j)) ζ =
      partialDeriv j g (z + ζ • stdBasisVector j) := by
  have e : (fun ξ : ℂ => g (z + ξ • stdBasisVector j)) =
      fun ξ : ℂ => (fun η : ℂ => g (z + ζ • stdBasisVector j + η • stdBasisVector j)) (ξ - ζ) := by
    funext ξ
    simp only [add_smul_stdBasisVector_shift]
  rw [e]
  refine (deriv_comp_sub_const
    (fun η : ℂ => g (z + ζ • stdBasisVector j + η • stdBasisVector j)) ζ ζ).trans ?_
  rw [sub_self]
  rfl
theorem iteratedDeriv_comp_coordLine
    (hO : IsOpen O) (z : ComplexCoordinates n) (j : Fin n) (q : ℕ) :
    ∀ ζ : ℂ, z + ζ • stdBasisVector j ∈ O →
      iteratedDeriv q (fun ξ : ℂ => w (z + ξ • stdBasisVector j)) ζ =
        (partialDeriv j)^[q] w (z + ζ • stdBasisVector j) := by
  induction q with
  | zero => intro ζ _; simp
  | succ q ih =>
    intro ζ hζ
    rw [iteratedDeriv_succ, Function.iterate_succ_apply', ← deriv_comp_coordLine]
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [eventually_coordLine_mem hO hζ] with ξ hξ using ih ξ hξ
theorem norm_iterate_partialDeriv_le
    (h : HolomorphicFnOn O w) {r c : ℝ} (hr : 0 < r) {z : ComplexCoordinates n} {j : Fin n}
    (hz : ∀ ζ : ℂ, ‖ζ‖ < r → z + ζ • stdBasisVector j ∈ O ∧ ‖w (z + ζ • stdBasisVector j)‖ ≤ c)
    (q : ℕ) : ‖(partialDeriv j)^[q] w z‖ ≤ (q ! : ℝ) * c / r ^ q := by
  have hm0 : z + (0 : ℂ) • stdBasisVector j ∈ O := (hz 0 (by simpa using hr)).1
  have e0 : (partialDeriv j)^[q] w z =
      iteratedDeriv q (fun ξ : ℂ => w (z + ξ • stdBasisVector j)) 0 := by
    rw [iteratedDeriv_comp_coordLine h.isOpen_set z j q 0 hm0]
    simp
  rw [e0]
  have hdiff : DifferentiableOn ℂ (fun ξ : ℂ => w (z + ξ • stdBasisVector j)) (Metric.ball 0 r) :=
    fun ζ hζ => (h.onLine_at (hz ζ (by simpa using hζ)).1).differentiableWithinAt
  have key : ∀ r' : ℝ, 0 < r' → r' < r →
      ‖iteratedDeriv q (fun ξ : ℂ => w (z + ξ • stdBasisVector j)) 0‖ ≤ (q ! : ℝ) * c / r' ^ q := by
    intro r' h0 h1
    refine Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le q h0
      (hdiff.diffContOnCl_ball (Metric.closedBall_subset_ball h1)) fun ζ hζ => (hz ζ ?_).2
    have : ‖ζ‖ = r' := by simpa using hζ
    linarith
  have ht : Tendsto (fun r' : ℝ => (q ! : ℝ) * c / r' ^ q) (𝓝[<] r)
      (𝓝 ((q ! : ℝ) * c / r ^ q)) :=
    (ContinuousAt.tendsto (continuousAt_const.div (continuousAt_id.pow q)
      (pow_ne_zero _ hr.ne'))).mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsLT hr] with r' hr' using key r' hr'.1 hr'.2
theorem iteratedPartial_replicate_append (j : Fin n) (k : ℕ) (l : List (Fin n))
    (g : ComplexCoordinates n → ℂ) :
    iteratedPartial (List.replicate k j ++ l) g =
      (partialDeriv j)^[k] (iteratedPartial l g) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ← ih]
    rfl
theorem norm_iteratedPartial_flatMap_le
    (hP : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hD : SeparatedFrame.HolomorphicDerivatives.Claim)
    (h : HolomorphicFnOn O u) {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    {a : ComplexCoordinates n} (hsub : openPolydisc ρ a ⊆ O) {c : ℝ}
    (hb : ∀ z ∈ openPolydisc ρ a, ‖u z‖ ≤ c) (q : Fin n → ℕ) (L : List (Fin n)) :
    L.Nodup → ∀ z ∈ openPolydisc ρ a, (∀ j ∈ L, z j = a j) →
      ‖iteratedPartial (L.flatMap fun j => List.replicate (q j) j) u z‖ ≤
        c * (L.map fun j => ((q j)! : ℝ) * ρ j ^ (-(q j : ℤ))).prod := by
  induction L with
  | nil => intro _ z hz _; simpa [iteratedPartial] using hb z hz
  | cons j L ih =>
    intro hnd z hz hzj
    rw [List.flatMap_cons, iteratedPartial_replicate_append, List.map_cons, List.prod_cons]
    have hnot : j ∉ L := (List.nodup_cons.1 hnd).1
    have hndL : L.Nodup := (List.nodup_cons.1 hnd).2
    have hline : ∀ ζ : ℂ, ‖ζ‖ < ρ j → z + ζ • stdBasisVector j ∈ O ∧
        ‖iteratedPartial (L.flatMap fun j => List.replicate (q j) j) u
          (z + ζ • stdBasisVector j)‖ ≤
          c * (L.map fun j => ((q j)! : ℝ) * ρ j ^ (-(q j : ℤ))).prod := by
      intro ζ hζ
      have hm : z + ζ • stdBasisVector j ∈ openPolydisc ρ a := by
        intro k
        by_cases hk : k = j
        · subst hk
          have e := hzj k List.mem_cons_self
          simpa [ComplexCoordinates.stdBasisVector, e] using hζ
        · have := hz k
          simpa [ComplexCoordinates.stdBasisVector, hk] using this
      refine ⟨hsub hm, ih hndL _ hm fun i hi => ?_⟩
      have hij : i ≠ j := fun e => hnot (e ▸ hi)
      simpa [ComplexCoordinates.stdBasisVector, hij] using hzj i (List.mem_cons_of_mem _ hi)
    have hc := norm_iterate_partialDeriv_le (holomorphicFnOn_iteratedPartial hP hD h _) (hρ j)
      hline (q j)
    refine hc.trans (le_of_eq ?_)
    rw [zpow_neg, zpow_natCast]
    ring
theorem norm_multiPartial_le
    (hP : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hD : SeparatedFrame.HolomorphicDerivatives.Claim)
    (h : HolomorphicFnOn O u) {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    {a : ComplexCoordinates n} (hsub : openPolydisc ρ a ⊆ O) {c : ℝ}
    (hb : ∀ z ∈ openPolydisc ρ a, ‖u z‖ ≤ c) (q : Fin n → ℕ) :
    ‖multiPartial q u a‖ ≤ c * ∏ j, ((q j)! : ℝ) * ρ j ^ (-(q j : ℤ)) := by
  have ha : a ∈ openPolydisc ρ a := fun j => by simpa using hρ j
  have := norm_iteratedPartial_flatMap_le hP hD h hρ hsub hb q (List.finRange n)
    (List.nodup_finRange n) a ha (fun _ _ => rfl)
  rw [Fin.prod_univ_def]
  exact this
theorem exists_linearForm_le_seminorm {X : Type} [AddCommGroup X] [Module ℂ X] (p : Seminorm ℂ X)
    (x : X) :
    ∃ χ : X →ₗ[ℂ] ℂ, (∀ y, ‖χ y‖ ≤ p y) ∧ χ x = (p x : ℂ) := by
  let _ : SeminormedAddCommGroup X :=
    AddGroupSeminorm.toSeminormedAddCommGroup p.toAddGroupSeminorm
  let _ : NormedSpace ℂ X := { norm_smul_le := fun c y => (map_smul_eq_mul p c y).le }
  obtain ⟨g, hg, hx⟩ := exists_dual_vector'' ℂ x
  refine ⟨g.toLinearMap, fun y => ?_, hx⟩
  calc ‖g y‖ ≤ ‖g‖ * ‖y‖ := g.le_opNorm y
    _ ≤ 1 * ‖y‖ := by gcongr
    _ = p y := one_mul _
theorem eq_sum_stdBasisVector (d : ComplexCoordinates n) : d = ∑ j, d j • stdBasisVector j := by
  funext k
  simp [Finset.sum_apply, ComplexCoordinates.stdBasisVector, Pi.single_apply]
theorem hasDerivAt_affineSegment (a d : ComplexCoordinates n) (s : ℝ) :
    HasDerivAt (fun s : ℝ => a + (s : ℂ) • d) d s := by
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 s := by
    simpa using (hasDerivAt_id s).ofReal_comp
  simpa using (h1.smul_const d).const_add a
theorem norm_sub_le_of_polydisc_bound
    (hP : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (h : HolomorphicFnOn O u) {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) {c : ℝ}
    {a a' : ComplexCoordinates n}
    (hseg : ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → openPolydisc ρ (a + (s : ℂ) • (a' - a)) ⊆ O ∧
      ∀ z ∈ openPolydisc ρ (a + (s : ℂ) • (a' - a)), ‖u z‖ ≤ c) :
    ‖u a' - u a‖ ≤ c * ∑ j, ‖a' j - a j‖ / ρ j := by
  have hcentre : ∀ (b : ComplexCoordinates n), b ∈ openPolydisc ρ b := fun b j => by
    simpa using hρ j
  have hdiff : ∀ s ∈ Icc (0 : ℝ) 1, DifferentiableAt ℂ u (a + (s : ℂ) • (a' - a)) := fun s hs =>
    h.differentiableAt hP ((hseg s hs).1 (hcentre _))
  have hder : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun s : ℝ => u (a + (s : ℂ) • (a' - a)))
        (fderiv ℂ u (a + (s : ℂ) • (a' - a)) (a' - a)) (Icc (0 : ℝ) 1) s := fun s hs => by
    have h0 : HasFDerivAt u ((fderiv ℂ u (a + (s : ℂ) • (a' - a))).restrictScalars ℝ)
        (a + (s : ℂ) • (a' - a)) := (hdiff s hs).hasFDerivAt.restrictScalars ℝ
    exact (h0.comp_hasDerivAt s (hasDerivAt_affineSegment a (a' - a) s)).hasDerivWithinAt
  have hbound : ∀ s ∈ Ico (0 : ℝ) 1,
      ‖fderiv ℂ u (a + (s : ℂ) • (a' - a)) (a' - a)‖ ≤ c * ∑ j, ‖a' j - a j‖ / ρ j := by
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self hs
    obtain ⟨hsub, hb⟩ := hseg s hs'
    set y := a + (s : ℂ) • (a' - a) with hy
    have hj : ∀ j, ‖fderiv ℂ u y (stdBasisVector j)‖ ≤ c / ρ j := by
      intro j
      have hline : ∀ ζ : ℂ, ‖ζ‖ < ρ j → y + ζ • stdBasisVector j ∈ O ∧
          ‖u (y + ζ • stdBasisVector j)‖ ≤ c := by
        intro ζ hζ
        have hm : y + ζ • stdBasisVector j ∈ openPolydisc ρ y := by
          intro k
          by_cases hk : k = j
          · subst hk
            simpa [ComplexCoordinates.stdBasisVector] using hζ
          · simpa [ComplexCoordinates.stdBasisVector, hk] using hρ k
        exact ⟨hsub hm, hb _ hm⟩
      have := norm_iterate_partialDeriv_le h (hρ j) hline 1
      have e : ((1 ! : ℕ) : ℝ) * c / ρ j ^ 1 = c / ρ j := by simp
      rw [Function.iterate_one, partialDeriv_eq_fderiv (hdiff s hs') j, e] at this
      exact this
    conv_lhs => rw [eq_sum_stdBasisVector (a' - a)]
    rw [map_sum, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [map_smul, norm_smul]
    calc ‖(a' - a) j‖ * ‖fderiv ℂ u y (stdBasisVector j)‖ ≤ ‖(a' - a) j‖ * (c / ρ j) := by
          gcongr
          exact hj j
      _ = c * (‖a' j - a j‖ / ρ j) := by
          simp only [Pi.sub_apply]
          ring
  have := norm_image_sub_le_of_norm_deriv_le_segment_01' hder hbound
  simpa using this
theorem cauchyEstimate_holds
    (hP : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hD : SeparatedFrame.HolomorphicDerivatives.Claim)
    (hO : IsOpen O) {X : Type} [AddCommGroup X] [Module ℂ X] (p : Seminorm ℂ X) :
    CauchyEstimate O p := by
  intro b x f hf ρ c hρ _
  refine ⟨fun a hsub hb q => ?_, fun a a' hseg => ?_⟩
  · obtain ⟨χ, hχ, hχx⟩ := exists_linearForm_le_seminorm p (linCombPartial q f x a)
    have ha : a ∈ O := hsub fun j => by simpa using hρ j
    have hU : HolomorphicFnOn O fun z => ∑ i, χ (x i) * f i z :=
      holomorphicFnOn_sum_mul hO _ _ _ hf
    have hUb : ∀ z ∈ openPolydisc ρ a, ‖∑ i, χ (x i) * f i z‖ ≤ c := fun z hz => by
      rw [← map_linComb]
      exact (hχ _).trans (hb z hz)
    have key := norm_multiPartial_le hP hD hU hρ hsub hUb q
    rw [← map_linCombPartial hP hD hO χ f x hf q ha, hχx] at key
    simpa [abs_of_nonneg (apply_nonneg p _)] using key
  · obtain ⟨χ, hχ, hχx⟩ := exists_linearForm_le_seminorm p (linComb f x a' - linComb f x a)
    have hU : HolomorphicFnOn O fun z => ∑ i, χ (x i) * f i z :=
      holomorphicFnOn_sum_mul hO _ _ _ hf
    have key := norm_sub_le_of_polydisc_bound hP hU hρ (c := c) (a := a) (a' := a')
      fun s hs => ⟨(hseg s hs).1, fun z hz => by
        rw [← map_linComb]
        exact (hχ _).trans ((hseg s hs).2 z hz)⟩
    rw [← map_linComb, ← map_linComb, ← map_sub, hχx] at key
    simpa [abs_of_nonneg (apply_nonneg p _)] using key
theorem weierstrassLimit_holds
    (hP : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hO : IsOpen O) : WeierstrassLimit O := by
  refine ⟨fun f lim hf hloc => ?_, fun H _ f hf hloc => ?_⟩
  · refine holomorphicFnOn_of_locally hO fun z hz => ?_
    obtain ⟨O', ho, hz', hs, ht⟩ := hloc z hz
    refine ⟨O', ho, hz', hs, ?_⟩
    have hu : UniformContinuous (fun c : ℂ => fun _ : Fin 1 => c) :=
      uniformContinuous_pi.2 fun _ => uniformContinuous_id
    exact (hP.1 n O' ho).2 1 (fun m z _ => f m z) (fun z _ => lim z)
      (fun m => (hf m).mono_set ho hs) (hu.comp_tendstoUniformlyOn ht)
  · have hb : ∀ z ∈ O, ∃ O' : Set (ComplexCoordinates n), IsOpen O' ∧ z ∈ O' ∧ O' ⊆ O ∧
        ∃ B : H → ℝ, Summable B ∧ ∀ y, ∀ x ∈ O', ‖f y x‖ ≤ B y := by
      intro z hz
      obtain ⟨O', ho, hz', hs, hfin⟩ := hloc z hz
      refine ⟨O', ho, hz', hs, fun y => (⨆ x ∈ O', ENNReal.ofReal ‖f y x‖).toReal,
        ENNReal.summable_toReal hfin.ne, fun y x hx => ?_⟩
      have hne : (⨆ x ∈ O', ENNReal.ofReal ‖f y x‖) ≠ ∞ := ENNReal.ne_top_of_tsum_ne_top hfin.ne y
      exact (ENNReal.ofReal_le_iff_le_toReal hne).1
        (le_iSup₂ (f := fun x (_ : x ∈ O') => ENNReal.ofReal ‖f y x‖) x hx)
    refine ⟨fun z hz => ?_, holomorphicFnOn_of_locally hO fun z hz => ?_⟩
    · obtain ⟨O', -, hz', -, B, hB, hle⟩ := hb z hz
      exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun y => hle y z hz') hB
    · obtain ⟨O', ho, hz', hs, B, hB, hle⟩ := hb z hz
      refine ⟨O', ho, hz', hs, holomorphicFnOn_iff.2 ⟨ho, ?_, fun a ha j => ?_⟩⟩
      · exact continuousOn_tsum (fun y => (hf y).continuousOn.mono hs) hB hle
      · have hU : IsOpen {ζ : ℂ | a + ζ • stdBasisVector j ∈ O'} :=
          ho.preimage (continuous_coordLine a j)
        have hd := Complex.differentiableOn_tsum_of_summable_norm
          (F := fun y (ζ : ℂ) => f y (a + ζ • stdBasisVector j)) hB
          (fun y ζ hζ => ((hf y).onLine_at (hs hζ)).differentiableWithinAt) hU
          (fun y ζ hζ => hle y _ hζ)
        exact hd.differentiableAt (hU.mem_nhds (by simpa using ha))
end Cauchy
section LinearAlgebra
section Entries
variable {J J' : Type}
open Classical in
theorem apply_eq_finsum_linearMapEntry [Finite J] (M : (J → ℂ) →ₗ[ℂ] (J' → ℂ)) (f : J → ℂ)
    (c' : J') :
    M f c' = ∑ᶠ c, linearMapEntry M c' c * f c := by
  have := Fintype.ofFinite J
  rw [finsum_eq_sum_of_fintype]
  have hf : f = ∑ c, f c • (Pi.single c 1 : J → ℂ) := by
    funext c
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hf]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, linearMapEntry]
  exact Finset.sum_congr rfl fun c _ => mul_comm _ _
theorem linearMapEntry_linearMapOfEntries [Finite J] (K : J' → J → ℂ) :
    linearMapEntry (linearMapOfEntries K) = K := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolCalculus.linearMapEntry_linearMapOfEntries <;> assumption
theorem linearMapOfEntries_apply_finsum [Finite J] (K : J' → J → ℂ) (f : J → ℂ) (c' : J') :
    linearMapOfEntries K f c' = ∑ᶠ c, K c' c * f c := by
  have := Fintype.ofFinite J
  rw [linearMapOfEntries_eq_applyKernel, finsum_eq_sum_of_fintype]
  simp only [applyKernel, tsum_fintype]
end Entries
variable {I I' I'' : PeriodicData}
theorem isInvertibleQuotHom_iff_isUnit (M : QuotHom I I) :
    IsInvertibleQuotHom M ↔ IsUnit (M : Module.End ℂ (I.UnitQuot → ℂ)) := by
  constructor
  · intro h
    refine (Module.End.isUnit_iff _).2 ⟨fun f f' e => ?_, fun g' => (h g').exists⟩
    exact (h (M f)).unique rfl e.symm
  · intro h g
    exact ((Module.End.isUnit_iff _).1 h).existsUnique g
theorem entryFormulas_holds (hI : IsPeriodic I) :
    EntryFormulas I I' I'' := by
  have := hI.finite_quot
  refine ⟨fun M f c' => apply_eq_finsum_linearMapEntry M f c', fun M hM f g => ⟨?_, fun e => ?_⟩,
    fun M M' c' c'' => apply_eq_finsum_linearMapEntry M _ c'⟩
  · rintro rfl
    exact hM.apply_quotHomInverse g
  · exact (hM g).unique (hM.apply_quotHomInverse g) e
theorem ofEntriesSpec_holds (hI : IsPeriodic I) : OfEntriesSpec I I' := by
  have := hI.finite_quot
  exact fun K => ⟨fun f c' => linearMapOfEntries_apply_finsum K f c', fun c' c =>
    congrFun (congrFun (linearMapEntry_linearMapOfEntries K) c') c⟩
section Matrices
variable {N : ℕ}
theorem permQuotient_eq_sign (σ : Equiv.Perm (Fin N)) :
    permQuotient σ = ((Equiv.Perm.sign σ : ℤ) : ℂ) := by
  set x : Fin N → ℂ := fun i => ((i : ℕ) : ℂ) with hx
  have h₁ : (Matrix.vandermonde (x ∘ σ)).det =
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * (Matrix.vandermonde x).det := by
    rw [← Matrix.det_permute]
    rfl
  rw [Matrix.det_vandermonde, Matrix.det_vandermonde] at h₁
  have h₀ : (∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (x j - x i)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j hj => ?_
    have hij : i < j := Finset.mem_Ioi.1 hj
    refine sub_ne_zero.2 fun e => hij.ne ?_
    exact (Fin.ext (Nat.cast_injective e)).symm
  simp only [permQuotient]
  simp_rw [Finset.prod_div_distrib]
  exact (div_eq_iff h₀).2 h₁
def variableMatrix (N : ℕ) : Matrix (Fin N) (Fin N) (MvPolynomial (Fin N × Fin N) ℂ) :=
  Matrix.of fun i j => MvPolynomial.X (i, j)
theorem mapMatrix_variableMatrix (X : Matrix (Fin N) (Fin N) ℂ) :
    (MvPolynomial.eval (matrixAsPoint X)).mapMatrix (variableMatrix N) = X := by
  ext i j
  simp [variableMatrix, matrixAsPoint]
theorem eval_det_variableMatrix (X : Matrix (Fin N) (Fin N) ℂ) :
    MvPolynomial.eval (matrixAsPoint X) (variableMatrix N).det = X.det := by
  rw [RingHom.map_det, mapMatrix_variableMatrix]
theorem eval_adjugate_variableMatrix (X : Matrix (Fin N) (Fin N) ℂ) (α β : Fin N) :
    MvPolynomial.eval (matrixAsPoint X) ((variableMatrix N).adjugate α β) = X.adjugate α β := by
  have h := RingHom.map_adjugate (MvPolynomial.eval (matrixAsPoint X)) (variableMatrix N)
  rw [mapMatrix_variableMatrix] at h
  rw [← h]
  rfl
theorem inv_apply_eq_adjugate_div (X : Matrix (Fin N) (Fin N) ℂ) (α β : Fin N) :
    X⁻¹ α β = MvPolynomial.eval (matrixAsPoint X) ((variableMatrix N).adjugate α β) / X.det := by
  rw [eval_adjugate_variableMatrix, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply,
    smul_eq_mul, div_eq_inv_mul]
theorem emptyMatrixFacts_holds : EmptyMatrixFacts := by
  refine ⟨fun X => ?_, by simp⟩
  have e : X = 1 := Subsingleton.elim _ _
  subst e
  simp
theorem matrixDetFacts_holds (N : ℕ) : MatrixDetFacts N := by
  refine ⟨fun X => ?_, fun _ σ => permQuotient_eq_sign σ,
    ⟨_, eval_det_variableMatrix⟩, Matrix.det_mul, Matrix.det_one, fun X => ?_,
    fun α β => ⟨_, fun X _ => inv_apply_eq_adjugate_div X α β⟩⟩
  · rw [← Matrix.det_transpose, Matrix.det_apply']
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [permQuotient_eq_sign]
    simp [Matrix.transpose_apply]
  · rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
end Matrices
section Hom
variable {N : ℕ}
open Classical in
theorem det_matrixOfEnum [Finite I.UnitQuot] (M : QuotHom I I) (e : Fin N ≃ I.UnitQuot) :
    (matrixOfEnum M e).det = LinearMap.det (M : Module.End ℂ (I.UnitQuot → ℂ)) := by
  let _ := Fintype.ofFinite I.UnitQuot
  have e₁ : matrixOfEnum M e = (LinearMap.toMatrix' M).submatrix e e := by
    ext α β
    simp only [matrixOfEnum, Matrix.of_apply, Matrix.submatrix_apply,
      LinearMap.toMatrix'_apply, linearMapEntry]
  rw [e₁, Matrix.det_submatrix_equiv_self, LinearMap.det_toMatrix']
theorem nonempty_equiv_unitQuot [Finite I.UnitQuot] :
    Nonempty (Fin (Nat.card I.UnitQuot) ≃ I.UnitQuot) :=
  ⟨(Finite.equivFin I.UnitQuot).symm⟩
theorem quotHomDet_eq_det [Finite I.UnitQuot] (M : QuotHom I I) :
    quotHomDet M = LinearMap.det (M : Module.End ℂ (I.UnitQuot → ℂ)) := by
  obtain ⟨e₀⟩ := nonempty_equiv_unitQuot (I := I)
  have hz : ∃ z, ∀ e : Fin (Nat.card I.UnitQuot) ≃ I.UnitQuot, (matrixOfEnum M e).det = z :=
    ⟨_, fun e => det_matrixOfEnum M e⟩
  have hs := Classical.epsilon_spec hz e₀
  change (matrixOfEnum M e₀).det = quotHomDet M at hs
  rw [← hs, det_matrixOfEnum]
theorem isInvertibleQuotHom_iff_det_ne_zero [Finite I.UnitQuot] (M : QuotHom I I) :
    IsInvertibleQuotHom M ↔ quotHomDet M ≠ 0 := by
  rw [isInvertibleQuotHom_iff_isUnit, quotHomDet_eq_det, LinearMap.isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero]
theorem matrixOfEnum_comp [Finite I.UnitQuot] (M M' : QuotHom I I) (e : Fin N ≃ I.UnitQuot) :
    matrixOfEnum (M.comp M') e = matrixOfEnum M e * matrixOfEnum M' e := by
  let _ := Fintype.ofFinite I.UnitQuot
  ext α β
  simp only [matrixOfEnum, Matrix.of_apply, Matrix.mul_apply]
  have h := apply_eq_finsum_linearMapEntry M (M' (by classical exact Pi.single (e β) 1)) (e α)
  rw [finsum_eq_sum_of_fintype] at h
  refine h.trans ?_
  rw [← Equiv.sum_comp e]
  rfl
theorem matrixOfEnum_id (e : Fin N ≃ I.UnitQuot) :
    matrixOfEnum (LinearMap.id : QuotHom I I) e = 1 := by
  classical
  ext α β
  simp [matrixOfEnum, linearMapEntry, Matrix.one_apply, Pi.single_apply]
theorem inv_matrixOfEnum [Finite I.UnitQuot] {M : QuotHom I I}
    (h : IsInvertibleQuotHom M) (e : Fin N ≃ I.UnitQuot) :
    (matrixOfEnum M e)⁻¹ = matrixOfEnum (quotHomInverse M) e := by
  refine Matrix.inv_eq_right_inv ?_
  rw [← matrixOfEnum_comp, ← matrixOfEnum_id e]
  congr 1
  ext1 g
  exact h.apply_quotHomInverse g
theorem quotHomDetFacts_holds (hI : IsPeriodic I) :
    QuotHomDetFacts I := by
  classical
  have := hI.finite_quot
  let _ := Fintype.ofFinite I.UnitQuot
  intro M
  have hdet : ∀ e : Fin (Nat.card I.UnitQuot) ≃ I.UnitQuot,
      (matrixOfEnum M e).det = quotHomDet M := fun e => by
    rw [quotHomDet_eq_det, det_matrixOfEnum]
  have hb : ⇑(Pi.basisFun ℂ I.UnitQuot) = quotIndicator (I := I) := by
    funext c
    simp [quotIndicator, Pi.basisFun_apply]
  refine ⟨hdet, fun _ => ⟨?_, ?_, quotHomDet_eq_det M, fun b => ?_⟩, fun e => ⟨?_, fun h =>
    inv_matrixOfEnum h e⟩, isInvertibleQuotHom_iff_det_ne_zero M⟩
  · rw [← hb]
    exact (Pi.basisFun ℂ I.UnitQuot).linearIndependent
  · rw [← hb]
    exact (Pi.basisFun ℂ I.UnitQuot).span_eq
  · rw [LinearMap.det_toMatrix, quotHomDet_eq_det]
  · rw [isInvertibleQuotHom_iff_det_ne_zero, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, hdet]
theorem matrixFamilyDetInv_holds
    (n N : ℕ) : MatrixFamilyDetInv n N := by
  intro S X hU
  have hdet : ∀ z, MvPolynomial.eval (matrixAsPoint (X z)) (variableMatrix N).det = (X z).det :=
    fun z => eval_det_variableMatrix (X z)
  have hnz : ∀ z ∈ S, (X z).det ≠ 0 := fun z hz => by
    have := (Matrix.isUnit_iff_isUnit_det _).1 (hU z hz)
    exact this.ne_zero
  refine ⟨fun h => ?_, fun hO h => ?_⟩
  · have hc : ∀ P : MvPolynomial (Fin N × Fin N) ℂ,
        ContinuousOn (fun z => MvPolynomial.eval (matrixAsPoint (X z)) P) S := fun P =>
      (MvPolynomial.continuous_eval P).comp_continuousOn (continuousOn_pi.2 h.2)
    have hd : ContinuousOn (fun z => (X z).det) S := by
      simpa only [hdet] using hc (variableMatrix N).det
    refine ⟨hd, h.1, fun e => ?_⟩
    refine ((hc ((variableMatrix N).adjugate e.1 e.2)).div hd hnz).congr fun z _ => ?_
    exact inv_apply_eq_adjugate_div (X z) e.1 e.2
  · obtain ⟨h1, -, hh⟩ := h
    have hc : ∀ P : MvPolynomial (Fin N × Fin N) ℂ, HolomorphicFnOn S
        fun z => MvPolynomial.eval (matrixAsPoint (X z)) P := fun P =>
      holomorphicFnOn_mvEval hO (fun e z => matrixCoeffs (X z) e) P hh
    have hd : HolomorphicFnOn S fun z => (X z).det :=
      (hc (variableMatrix N).det).congr_on fun z _ => (hdet z).symm
    refine ⟨hd, h1, hO, fun e => ?_⟩
    refine ((hc ((variableMatrix N).adjugate e.1 e.2)).mul (hd.inv hnz)).congr_on fun z _ => ?_
    change (X z)⁻¹ e.1 e.2 = _
    rw [inv_apply_eq_adjugate_div, div_eq_mul_inv]
theorem quotHomFamilyDetInv_holds (hI : IsPeriodic I) (n : ℕ) :
    QuotHomFamilyDetInv n I := by
  have := hI.finite_quot
  intro S M hU
  obtain ⟨e⟩ := nonempty_equiv_unitQuot (I := I)
  have hdets := quotHomDetFacts_holds hI
  have hXU : ∀ z ∈ S, IsUnit (matrixOfEnum (M z) e) := fun z hz =>
    ((hdets (M z)).2.2.1 e).1.1 (hU z hz)
  have hmat := matrixFamilyDetInv_holds n _ S
    (fun z => matrixOfEnum (M z) e) hXU
  have hdet : ∀ z, quotHomDet (M z) = (matrixOfEnum (M z) e).det := fun z =>
    ((hdets (M z)).1 e).symm
  have hinv : ∀ z ∈ S, ∀ p : I.UnitQuot × I.UnitQuot,
      quotHomEntries (quotHomInverse (M z)) p =
        matrixCoeffs (matrixOfEnum (M z) e)⁻¹ (e.symm p.1, e.symm p.2) := fun z hz p => by
    rw [inv_matrixOfEnum (hU z hz)]
    simp [matrixCoeffs, matrixOfEnum, quotHomEntries]
  refine ⟨fun h => ?_, fun hO h => ?_⟩
  · obtain ⟨hd, h1, hi⟩ := hmat.1 ⟨h.1, fun p => h.2 (e p.1, e p.2)⟩
    refine ⟨hd.congr fun z _ => hdet z, h1, fun p => (hi (e.symm p.1, e.symm p.2)).congr
      fun z hz => hinv z hz p⟩
  · obtain ⟨hd, h1, -, hi⟩ := hmat.2 hO ⟨h.1, hO, fun p => h.2.2 (e p.1, e p.2)⟩
    refine ⟨hd.congr_on fun z _ => hdet z, h1, hO, fun p => ?_⟩
    exact HolomorphicFnOn.congr_on (hi (e.symm p.1, e.symm p.2)) fun z hz => hinv z hz p
theorem quotHomFamilyInvOnDual_holds (hI : IsPeriodic I) :
    QuotHomFamilyInvOnDual I := by
  intro S M hU
  have h := quotHomFamilyDetInv_holds hI 4 S M hU
  exact ⟨fun hc => (h.1 hc).2, fun hO hh => (h.2 hO hh).2⟩
end Hom
end LinearAlgebra
section Symbols
variable {I I' : PeriodicData}
theorem descendMatrix_mkQuot {F : I'.Carrier → I.Carrier → ℂ} (h : FactorsThroughQuot F)
    (ι' : I'.Carrier) (ι : I.Carrier) :
    descendMatrix I I' 1 F (I'.mkQuot 1 ι') (I.mkQuot 1 ι) = F ι' ι := by
  have hz : ∃ z, ∀ x' x, I'.mkQuot 1 x' = I'.mkQuot 1 ι' → I.mkQuot 1 x = I.mkQuot 1 ι →
      F x' x = z := ⟨F ι' ι, fun x' x e e' => h x' ι' x ι e e'⟩
  exact (Classical.epsilon_spec hz ι' ι rfl rfl).symm
theorem realDualPoints_subset_imStrip {δ : ℝ} (hδ : 0 < δ) : realDualPoints ⊆ strictImStrip δ := by
  intro κ hκ
  have e : imVec κ = 0 := by
    funext μ
    exact hκ μ
  simpa [strictImStrip, e, TorusMetric.euclidNormVec] using hδ
theorem symbolOnRealPoints_holds
    (hS : Symbols.Claim) (hI : IsPeriodic I) :
    SymbolOnRealPoints I := by
  have := hI.finite_quot
  intro T hT
  obtain ⟨_, C, δ, hC, hδ, hb⟩ := id hT
  have hR : IsDecayRate I I T δ := ⟨hδ, C, hC, hb⟩
  have F := hS.1 I I I hI hI hI T T δ hT hR hT hR
  have hsub := realDualPoints_subset_imStrip hδ
  have hdep : ∀ κ ∈ strictImStrip δ,
      FactorsThroughQuot (P := I) (Q := I) (fourierSymbol I I T κ) :=
    fun κ hκ ι₁' ι₂' ι₁ ι₂ e e' =>
      F.eq_of_mkQuot_eq κ (F.summable_on_strip κ hκ) ι₁' ι₂' ι₁ ι₂ e e'
  have hcont : QuotHomFamilyContinuousOn (n := 4) realDualPoints (symbolHom I I T) := by
    refine ⟨by norm_num, fun p => ?_⟩
    obtain ⟨ι', h'⟩ := Quot.exists_rep p.1
    obtain ⟨ι, h⟩ := Quot.exists_rep p.2
    have hc : ContinuousOn (fun κ => fourierSymbol I I T κ ι' ι) (strictImStrip δ) :=
      continuousOn_pi.1 (F.isHolomorphicIn ι' ι).2.1 0
    refine (hc.mono hsub).congr fun κ hκ => ?_
    simp only [quotHomEntries, symbolHom]
    rw [linearMapEntry_linearMapOfEntries, ← h', ← h]
    exact descendMatrix_mkQuot (hdep κ (hsub hκ)) ι' ι
  refine ⟨fun κ hκ => ⟨F.summable_on_strip κ (hsub hκ), hdep κ (hsub hκ)⟩, hcont, fun hU => ?_⟩
  exact ((quotHomFamilyInvOnDual_holds hI) realDualPoints (symbolHom I I T) hU).1 hcont
theorem continuous_toComplexVec : Continuous toComplexVec :=
  continuous_pi fun μ => Complex.continuous_ofReal.comp (continuous_apply μ)
theorem toComplexVec_mem_realDualPoints (κ : InfiniteLattice.AmbientSpace) :
    toComplexVec κ ∈ realDualPoints :=
  fun μ => by simp [toComplexVec]
theorem entryIntegrandFacts_holds : EntryIntegrandFacts I I' := by
  intro M hM ι' ι
  have h₁ : Continuous fun κ : InfiniteLattice.AmbientSpace =>
      carrierEntry (M (toComplexVec κ)) ι' ι :=
    (hM.2 (I'.mkQuot 1 ι', I.mkQuot 1 ι)).comp_continuous continuous_toComplexVec
      toComplexVec_mem_realDualPoints
  have h₂ : Continuous fun κ : InfiniteLattice.AmbientSpace =>
      Complex.exp (-Complex.I *
        bilinDot (toComplexVec κ) (toComplexVec (I.pos ι - I'.pos ι'))) := by
    refine Complex.continuous_exp.comp (continuous_const.mul ?_)
    exact continuous_finsetSum _ fun μ _ =>
      ((continuous_apply μ).comp continuous_toComplexVec).mul continuous_const
  have hc : Continuous (entryIntegrand M ι' ι) := h₁.mul h₂
  exact ⟨hc, hc.continuousOn.integrableOn_compact isCompact_Icc⟩
end Symbols
section Holomorphic
theorem expInvHolomorphic_holds : ExpInvHolomorphic := by
  refine ⟨(holomorphicFnOn_coord 0).cexp, ?_, fun n _ O f hf => ⟨hf.cexp, fun h0 => ?_⟩⟩
  · have hO : IsOpen {z : ComplexCoordinates 1 | z 0 ≠ 0} :=
      isOpen_ne_fun (continuous_apply 0) continuous_const
    exact ((holomorphicFnOn_coord 0).mono_set hO (subset_univ _)).inv fun z hz => hz
  · simpa only [one_div] using hf.inv h0
variable {n : ℕ} {O : Set (ComplexCoordinates n)}
theorem holomorphicTuples_holds (hO : IsOpen O) (b : ℕ) :
    HolomorphicTuples n b O := by
  refine ⟨fun f => ⟨fun h i => ?_, fun h => ?_⟩, fun f h => h.2.1⟩
  · exact holomorphicFnOn_comp_zero
      (F := fun z (_ : Fin 1) => f i z) ⟨h.1, continuousOn_pi.2 fun _ =>
        continuousOn_pi.1 h.2.1 i, fun a ha j => by
          filter_upwards [h.2.2 a ha j] with ζ hζ
          exact differentiableAt_pi.2 fun _ => differentiableAt_pi.1 hζ i⟩
  · refine ⟨hO, continuousOn_pi.2 fun i => (h i).continuousOn, fun a ha j => ?_⟩
    have hall : ∀ᶠ ζ in 𝓝 (0 : ℂ), ∀ i, a + ζ • stdBasisVector j ∈ O ∧
        DifferentiableAt ℂ (fun ζ : ℂ => f i (a + ζ • stdBasisVector j)) ζ := by
      refine eventually_all.2 fun i => ?_
      filter_upwards [eventually_coordLine_mem_zero hO j ha] with ζ hζ
      exact ⟨hζ, (h i).onLine_at hζ⟩
    filter_upwards [hall] with ζ hζ
    exact differentiableAt_pi.2 fun i => (hζ i).2
theorem entrywiseHolomorphicContinuous_holds {Y E : Type} (entries : Y → E → ℂ) :
    EntrywiseHolomorphicContinuous entries O := fun _ h =>
  ⟨h.1, fun e => HolomorphicFnOn.continuousOn (h.2.2 e)⟩
theorem polynomialHolomorphic_holds (hO : IsOpen O) :
    PolynomialHolomorphic n O :=
  ⟨fun _ f P h => holomorphicFnOn_mvEval hO f P h, fun c => holomorphicFnOn_const hO c,
    fun _ f h => ⟨holomorphicFnOn_sum hO _ f h, holomorphicFnOn_prod hO _ f h⟩,
    fun c _ h => (holomorphicFnOn_const hO c).mul h⟩
theorem coordPolyHolomorphic_holds : CoordPolyHolomorphic n :=
  ⟨holomorphicFnOn_coord, fun P => holomorphicFnOn_mvEval isOpen_univ (fun i z => z i) P
    holomorphicFnOn_coord⟩
end Holomorphic
theorem claim_holds (hP : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hD : SeparatedFrame.HolomorphicDerivatives.Claim)
    (hS : Symbols.Claim) : Claim := by
  refine ⟨fun I I' I'' hI _ _ => entryFormulas_holds hI,
    fun I I' hI _ => ⟨ofEntriesSpec_holds hI, entryIntegrandFacts_holds⟩,
    fun I hI => ⟨symbolOnRealPoints_holds hS hI, quotHomDetFacts_holds hI,
      quotHomFamilyInvOnDual_holds hI, fun n _ => quotHomFamilyDetInv_holds hI n⟩,
    emptyMatrixFacts_holds,
    fun N => ⟨matrixDetFacts_holds N, fun n _ =>
      matrixFamilyDetInv_holds n N⟩,
    expInvHolomorphic_holds,
    fun n O _ hO => ⟨fun b _ => holomorphicTuples_holds hO b,
      fun _ _ _ _ => entrywiseHolomorphicContinuous_holds _,
      fun _ _ => entrywiseHolomorphicContinuous_holds _,
      entrywiseHolomorphicContinuous_holds _,
      fun _ _ => entrywiseHolomorphicContinuous_holds _,
      polynomialHolomorphic_holds hO,
      coordPolyHolomorphic_holds,
      partialsHolomorphicComm_holds hP hD,
      fun X _ _ p => ⟨linCombPartialWellDefined_holds hP hD hO X, cauchyEstimate_holds hP hD hO p⟩,
      complexLinCombPartials_holds hP hD hO,
      weierstrassLimit_holds hP hO⟩,
    inferInstance, inferInstance⟩
end YangMills.Construction.PeriodicOperators.EntriesDets
end
