import YangMills.Construction.EuclideanFunctionals.BoundsAndContinuityOfTheMomentsProof
import YangMills.Construction.TwoPoints.LocalKernelOfAFormProof
import YangMills.Construction.EuclideanFunctionals.BracketOfTheParametrix
import YangMills.Construction.EuclideanFunctionals.CauchyEstimateAtARealPoint
import YangMills.Construction.EuclideanFunctionals.CentredFunctionalSeesTensorComponentsOnlyProof
import YangMills.Construction.EuclideanFunctionals.ExpansionTranslationsContinuityAndSmearingOfTheInsertionValue
import YangMills.Construction.RotationInvariance.FunctionalOnTuplesOfRealFunctionsProof
import YangMills.Construction.Towers.PolarisationOfACompositionWithAStepProof
import Mathlib
set_option autoImplicit false
open scoped ContDiff Topology Pointwise
open Filter Set MeasureTheory
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.ParametrixBracket
section Partials
open YangMills.Construction.TestFunctions
variable {U : Set R4} {f g : R4 → ℂ}
theorem hasDerivAt_comp_line (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) {x : R4} (hx : x ∈ U)
    (v : R4) : HasDerivAt (fun t : ℝ => f (x + t • v)) (fderiv ℝ f x v) 0 := by
  have hd : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • v) := by
    rw [zero_smul, add_zero]
    exact ((hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  exact hd.comp_hasDerivAt (0 : ℝ) hl
theorem partialDerivR4_eq_fderiv (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) {x : R4} (hx : x ∈ U)
    (i : Fin 4) : partialDerivR4 i f x = fderiv ℝ f x (Pi.single i (1 : ℝ)) :=
  (hasDerivAt_comp_line hU hf hx _).deriv
theorem partialDerivR4_congr (hU : IsOpen U) (h : EqOn f g U) (i : Fin 4) :
    EqOn (partialDerivR4 i f) (partialDerivR4 i g) U := by
  intro x hx
  have hc : ContinuousAt (fun t : ℝ => x + t • (Pi.single i (1 : ℝ) : R4)) 0 := by fun_prop
  have hm : ∀ᶠ t : ℝ in 𝓝 0, x + t • (Pi.single i (1 : ℝ) : R4) ∈ U :=
    hc.eventually_mem (by simpa using hU.mem_nhds hx)
  have he : (fun t : ℝ => f (x + t • (Pi.single i (1 : ℝ) : R4))) =ᶠ[𝓝 0]
      fun t : ℝ => g (x + t • (Pi.single i (1 : ℝ) : R4)) := by
    filter_upwards [hm] with t ht using h ht
  exact he.deriv_eq
theorem contDiffOn_partialDerivR4 (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (i : Fin 4) :
    ContDiffOn ℝ ∞ (partialDerivR4 i f) U := by
  have h1 : ContDiffOn ℝ ∞ (fun x => fderiv ℝ f x (Pi.single i (1 : ℝ) : R4)) U :=
    (hf.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
  exact h1.congr fun x hx => partialDerivR4_eq_fderiv hU hf hx i
theorem partialDerivR4_partialDerivR4 (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) {x : R4}
    (hx : x ∈ U) (i j : Fin 4) :
    partialDerivR4 i (partialDerivR4 j f) x =
      fderiv ℝ (fderiv ℝ f) x (Pi.single i (1 : ℝ)) (Pi.single j (1 : ℝ)) := by
  rw [partialDerivR4_eq_fderiv hU (contDiffOn_partialDerivR4 hU hf j) hx i]
  have hD : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_of_isOpen (m := ∞) hU (by simp)).contDiffAt (hU.mem_nhds hx)).differentiableAt
      (by simp)
  have hev : partialDerivR4 j f =ᶠ[𝓝 x] fun y => fderiv ℝ f y (Pi.single j (1 : ℝ)) := by
    filter_upwards [hU.mem_nhds hx] with y hy using partialDerivR4_eq_fderiv hU hf hy j
  rw [hev.fderiv_eq, (hD.hasFDerivAt.clm_apply (hasFDerivAt_const _ x)).fderiv]
  simp
theorem partialDerivR4_comm (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (i j : Fin 4) :
    EqOn (partialDerivR4 i (partialDerivR4 j f)) (partialDerivR4 j (partialDerivR4 i f)) U := by
  intro x hx
  rw [partialDerivR4_partialDerivR4 hU hf hx, partialDerivR4_partialDerivR4 hU hf hx]
  have h2 : minSmoothness ℝ 2 ≤ (∞ : WithTop ℕ∞) := by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact ENat.LEInfty.out
  exact ((hf.contDiffAt (hU.mem_nhds hx)).isSymmSndFDerivAt h2) _ _
theorem iterate_partialDerivR4_congr (hU : IsOpen U) (h : EqOn f g U) (i : Fin 4) (n : ℕ) :
    EqOn ((partialDerivR4 i)^[n] f) ((partialDerivR4 i)^[n] g) U := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    exact partialDerivR4_congr hU ih i
theorem contDiffOn_iterate_partialDerivR4 (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (i : Fin 4)
    (n : ℕ) : ContDiffOn ℝ ∞ ((partialDerivR4 i)^[n] f) U := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    exact contDiffOn_partialDerivR4 hU ih i
theorem partialDerivR4_iterate_comm (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (i j : Fin 4)
    (n : ℕ) :
    EqOn (partialDerivR4 i ((partialDerivR4 j)^[n] f)) ((partialDerivR4 j)^[n] (partialDerivR4 i f))
      U := by
  induction n with
  | zero => intro x _; rfl
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    intro x hx
    rw [partialDerivR4_comm hU (contDiffOn_iterate_partialDerivR4 hU hf j n) i j hx]
    exact partialDerivR4_congr hU ih j hx
theorem contDiffOn_iteratedPartial (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (a : Multiindex) :
    ContDiffOn ℝ ∞ (iteratedPartial a f) U :=
  contDiffOn_iterate_partialDerivR4 hU (contDiffOn_iterate_partialDerivR4 hU
    (contDiffOn_iterate_partialDerivR4 hU (contDiffOn_iterate_partialDerivR4 hU hf _ _) _ _) _ _)
    _ _
theorem iteratedPartial_congr (hU : IsOpen U) (h : EqOn f g U) (a : Multiindex) :
    EqOn (iteratedPartial a f) (iteratedPartial a g) U :=
  iterate_partialDerivR4_congr hU (iterate_partialDerivR4_congr hU
    (iterate_partialDerivR4_congr hU (iterate_partialDerivR4_congr hU h _ _) _ _) _ _) _ _
theorem partialDerivR4_iteratedPartial (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (a : Multiindex)
    (i : Fin 4) :
    EqOn (partialDerivR4 i (iteratedPartial a f)) (iteratedPartial (a + Pi.single i 1) f) U := by
  have h3 := contDiffOn_iterate_partialDerivR4 hU hf 3 (a 3)
  have h2 := contDiffOn_iterate_partialDerivR4 hU h3 2 (a 2)
  have h1 := contDiffOn_iterate_partialDerivR4 hU h2 1 (a 1)
  fin_cases i
  · intro x _
    simp [iteratedPartial, Function.iterate_succ_apply']
  · intro x hx
    have e : iteratedPartial (a + Pi.single 1 1) f = (partialDerivR4 0)^[a 0]
        (partialDerivR4 1 ((partialDerivR4 1)^[a 1] ((partialDerivR4 2)^[a 2]
          ((partialDerivR4 3)^[a 3] f)))) := by
      simp [iteratedPartial, Function.iterate_succ_apply']
    simp only [Fin.mk_one, Fin.isValue]
    rw [e]
    exact partialDerivR4_iterate_comm hU h1 1 0 (a 0) hx
  · intro x hx
    have e : iteratedPartial (a + Pi.single 2 1) f = (partialDerivR4 0)^[a 0]
        ((partialDerivR4 1)^[a 1] (partialDerivR4 2 ((partialDerivR4 2)^[a 2]
          ((partialDerivR4 3)^[a 3] f)))) := by
      simp [iteratedPartial, Function.iterate_succ_apply']
    simp only [Fin.isValue, Fin.reduceFinMk]
    rw [e]
    refine (partialDerivR4_iterate_comm hU h1 2 0 (a 0) hx).trans ?_
    exact iterate_partialDerivR4_congr hU (partialDerivR4_iterate_comm hU h2 2 1 (a 1)) 0 (a 0) hx
  · intro x hx
    have e : iteratedPartial (a + Pi.single 3 1) f = (partialDerivR4 0)^[a 0]
        ((partialDerivR4 1)^[a 1] ((partialDerivR4 2)^[a 2] (partialDerivR4 3
          ((partialDerivR4 3)^[a 3] f)))) := by
      simp [iteratedPartial, Function.iterate_succ_apply']
    simp only [Fin.isValue, Fin.reduceFinMk]
    rw [e]
    refine (partialDerivR4_iterate_comm hU h1 3 0 (a 0) hx).trans ?_
    refine iterate_partialDerivR4_congr hU
      ((partialDerivR4_iterate_comm hU h2 3 1 (a 1)).trans ?_) 0 (a 0) hx
    exact iterate_partialDerivR4_congr hU (partialDerivR4_iterate_comm hU h3 3 2 (a 2)) 1 (a 1)
theorem partialDerivR4_sum {ι : Type*} (hU : IsOpen U) (s : Finset ι) (G : ι → R4 → ℂ)
    (hG : ∀ k ∈ s, ContDiffOn ℝ ∞ (G k) U) (i : Fin 4) :
    EqOn (partialDerivR4 i fun x => ∑ k ∈ s, G k x) (fun x => ∑ k ∈ s, partialDerivR4 i (G k) x)
      U := by
  intro x hx
  have h := HasDerivAt.fun_sum (u := s) fun k hk =>
    hasDerivAt_comp_line hU (hG k hk) hx (Pi.single i (1 : ℝ))
  change deriv _ 0 = _
  rw [h.deriv]
  exact Finset.sum_congr rfl fun k hk => (partialDerivR4_eq_fderiv hU (hG k hk) hx i).symm
theorem partialDerivR4_of_eqOn_sum {ι : Type*} [Fintype ι] (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (A : ι → Multiindex)
    (h : EqOn g (fun x => ∑ k, iteratedPartial (A k) f x) U) (i : Fin 4) :
    EqOn (partialDerivR4 i g) (fun x => ∑ k, iteratedPartial (A k + Pi.single i 1) f x) U := by
  intro x hx
  rw [partialDerivR4_congr hU h i hx,
    partialDerivR4_sum hU Finset.univ _ (fun k _ => contDiffOn_iteratedPartial hU hf (A k)) i hx]
  exact Finset.sum_congr rfl fun k _ => partialDerivR4_iteratedPartial hU hf (A k) i hx
def bumpTwice {ι : Type*} (A : ι → Multiindex) (j : ι × Fin 4) : Multiindex :=
  A j.1 + Pi.single j.2 1 + Pi.single j.2 1
theorem laplacianR4_of_eqOn_sum {ι : Type*} [Fintype ι] (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (A : ι → Multiindex)
    (h : EqOn g (fun x => ∑ k, iteratedPartial (A k) f x) U) :
    EqOn (laplacianR4 g) (fun x => ∑ j, iteratedPartial (bumpTwice A j) f x) U := by
  intro x hx
  have h2 : ∀ i : Fin 4, partialDerivR4 i (partialDerivR4 i g) x =
      ∑ k, iteratedPartial (A k + Pi.single i 1 + Pi.single i 1) f x := fun i =>
    partialDerivR4_of_eqOn_sum hU hf (fun k => A k + Pi.single i 1)
      (partialDerivR4_of_eqOn_sum hU hf A h i) i hx
  simp only [laplacianR4, h2]
  rw [Finset.sum_comm, Fintype.sum_prod_type]
  rfl
def cubeIndices : ((Unit × Fin 4) × Fin 4) × Fin 4 → Multiindex :=
  bumpTwice (bumpTwice (bumpTwice fun _ : Unit => 0))
theorem laplacianR4_iterate_three (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) :
    EqOn (laplacianR4^[3] f) (fun x => ∑ j, iteratedPartial (cubeIndices j) f x) U := by
  have h0 : EqOn f
      (fun x => ∑ k : Unit, iteratedPartial ((fun _ : Unit => (0 : Multiindex)) k) f x) U := by
    intro x _
    simp [iteratedPartial]
  exact laplacianR4_of_eqOn_sum hU hf _
    (laplacianR4_of_eqOn_sum hU hf _ (laplacianR4_of_eqOn_sum hU hf _ h0))
theorem order_cubeIndices (j : ((Unit × Fin 4) × Fin 4) × Fin 4) : (cubeIndices j).order = 6 := by
  revert j
  decide +kernel
theorem sum_fact_cubeIndices : ∑ j, (cubeIndices j).fact = 4800 := by
  decide +kernel
end Partials
def orderThreeFinset : Finset Multiindex :=
  (Fintype.piFinset fun _ : Fin 4 => Finset.range 4).filter fun γ => ∑ i, γ i = 3
theorem multiindicesOrderThree_eq : multiindicesOrderThree = orderThreeFinset := by
  ext γ
  simp only [multiindicesOrderThree, Finset.mem_piAntidiag, Finset.mem_univ, implies_true,
    and_true, orderThreeFinset, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  refine ⟨fun h => ⟨fun i => ?_, h⟩, fun h => h.2⟩
  have h3 : γ i ≤ 3 :=
    (Finset.single_le_sum (f := γ) (fun i _ => Nat.zero_le _) (Finset.mem_univ i)).trans h.le
  omega
theorem fact_dvd_six : ∀ γ ∈ orderThreeFinset, γ.fact ∣ 6 := by
  decide +kernel
theorem sum_orderThreeFinset :
    ∑ γ ∈ orderThreeFinset, 6 / γ.fact * Multiindex.fact (Multiindex.twice γ) = 4800 := by
  decide +kernel
theorem laplacianCubedConst_eq : laplacianCubedConst = 4800 := by
  rw [laplacianCubedConst, multiindicesOrderThree_eq]
  have h : ∀ γ ∈ orderThreeFinset, ((Nat.factorial 3 : ℝ) *
      (Multiindex.fact (Multiindex.twice γ) : ℝ)) / (Multiindex.fact γ : ℝ) =
      ((6 / γ.fact * Multiindex.fact (Multiindex.twice γ) : ℕ) : ℝ) := by
    intro γ hγ
    have hd := fact_dvd_six γ hγ
    have hpos : (γ.fact : ℝ) ≠ 0 := by
      have : γ.fact ≠ 0 := by
        intro h0
        rw [h0] at hd
        omega
      exact_mod_cast this
    rw [Nat.cast_mul, Nat.cast_div hd hpos]
    norm_num [Nat.factorial]
    ring
  rw [Finset.sum_congr rfl h, ← Nat.cast_sum, sum_orderThreeFinset]
  norm_num
section Parts
open YangMills.Construction.TestFunctions
variable {U : Set R4} {g w : R4 → ℂ}
theorem continuous_mul_of_tsupport_subset_open (hU : IsOpen U) {a b : R4 → ℂ} (ha : Continuous a)
    (hs : tsupport a ⊆ U) (hb : ContinuousOn b U) : Continuous fun x => a x * b x := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ U
  · exact ha.continuousAt.mul (hb.continuousAt (hU.mem_nhds hx))
  · have hx' : x ∉ tsupport a := fun h => hx (hs h)
    have he : (fun y => a y * b y) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx'] with y hy
      simp [hy]
    exact continuousAt_const.congr he.symm
structure IsTestIn (U : Set R4) (g : R4 → ℂ) : Prop where
  contDiff : ContDiff ℝ ∞ g
  hasCompactSupport : HasCompactSupport g
  tsupport_subset : tsupport g ⊆ U
theorem IsTestIn.integrable_mul (hU : IsOpen U) (hg : IsTestIn U g) (hw : ContinuousOn w U) :
    Integrable fun x => g x * w x :=
  (continuous_mul_of_tsupport_subset_open hU hg.contDiff.continuous hg.tsupport_subset
    hw).integrable_of_hasCompactSupport hg.hasCompactSupport.mul_right
theorem partialDerivR4_eq_zero_of_notMem {x : R4} (hx : x ∉ tsupport g) (i : Fin 4) :
    partialDerivR4 i g x = 0 := by
  have h0 : g =ᶠ[𝓝 x] fun _ => 0 := notMem_tsupport_iff_eventuallyEq.1 hx
  have hd : DifferentiableAt ℝ g x := (differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq h0
  change lineDeriv ℝ g x (Pi.single i 1) = 0
  rw [hd.lineDeriv_eq_fderiv, h0.fderiv_eq]
  simp
theorem IsTestIn.tsupport_subset_of_eq_zero {a : R4 → ℂ} (hg : tsupport g ⊆ U)
    (h : ∀ x, x ∉ tsupport g → a x = 0) : tsupport a ⊆ U := by
  refine subset_trans (closure_minimal ?_ (isClosed_tsupport g)) hg
  intro x hx
  by_contra hn
  exact hx (h x hn)
theorem IsTestIn.of_eq_zero {a : R4 → ℂ} (hg : IsTestIn U g) (ha : ContDiff ℝ ∞ a)
    (h : ∀ x, x ∉ tsupport g → a x = 0) : IsTestIn U a := by
  have hs : tsupport a ⊆ tsupport g := IsTestIn.tsupport_subset_of_eq_zero subset_rfl h
  exact ⟨ha, IsCompact.of_isClosed_subset hg.hasCompactSupport (isClosed_tsupport a) hs,
    hs.trans hg.tsupport_subset⟩
theorem contDiff_partialDerivR4 (hg : ContDiff ℝ ∞ g) (i : Fin 4) :
    ContDiff ℝ ∞ (partialDerivR4 i g) := by apply _root_.YangMills.Construction.TwoPoints.LocalFormKernel.contDiff_partialDerivR4 <;> assumption
theorem IsTestIn.partialDerivR4 (hg : IsTestIn U g) (i : Fin 4) :
    IsTestIn U (TestFunctions.partialDerivR4 i g) :=
  hg.of_eq_zero (contDiff_partialDerivR4 hg.contDiff i) fun _ hx =>
    partialDerivR4_eq_zero_of_notMem hx i
theorem contDiffOn_laplacianR4 (hU : IsOpen U) (hw : ContDiffOn ℝ ∞ w U) :
    ContDiffOn ℝ ∞ (laplacianR4 w) U := by
  unfold laplacianR4
  exact ContDiffOn.sum fun i _ =>
    contDiffOn_partialDerivR4 hU (contDiffOn_partialDerivR4 hU hw i) i
theorem IsTestIn.laplacianR4 (hg : IsTestIn U g) : IsTestIn U (TestFunctions.laplacianR4 g) := by
  refine hg.of_eq_zero ?_ fun x hx => ?_
  · rw [← contDiffOn_univ]
    exact contDiffOn_laplacianR4 isOpen_univ hg.contDiff.contDiffOn
  · have h : ∀ i : Fin 4, x ∉ tsupport (TestFunctions.partialDerivR4 i g) := fun i hn =>
      hx (IsTestIn.tsupport_subset_of_eq_zero subset_rfl
        (fun _ hy => partialDerivR4_eq_zero_of_notMem hy i) hn)
    simp [TestFunctions.laplacianR4, partialDerivR4_eq_zero_of_notMem (h _)]
theorem integral_partialDerivR4_mul (hU : IsOpen U) (hg : IsTestIn U g) (hw : ContDiffOn ℝ ∞ w U)
    (i : Fin 4) :
    ∫ x, partialDerivR4 i g x * w x = -∫ x, g x * partialDerivR4 i w x := by
  have hwc : ContinuousOn w U := hw.continuousOn
  have hpc : ContinuousOn (partialDerivR4 i w) U :=
    (contDiffOn_partialDerivR4 hU hw i).continuousOn
  have i1 : Integrable fun x => partialDerivR4 i g x * w x :=
    (hg.partialDerivR4 i).integrable_mul hU hwc
  have i2 : Integrable fun x => g x * partialDerivR4 i w x := hg.integrable_mul hU hpc
  have i3 : Integrable fun x => g x * w x := hg.integrable_mul hU hwc
  have hline : ∀ x, HasLineDerivAt ℝ (fun y => g y * w y)
      (partialDerivR4 i g x * w x + g x * partialDerivR4 i w x) x (Pi.single i (1 : ℝ)) := by
    intro x
    by_cases hx : x ∈ U
    · have hgU : ContDiffOn ℝ ∞ g U := hg.contDiff.contDiffOn
      have h1 := hasDerivAt_comp_line hU hgU hx (Pi.single i (1 : ℝ))
      have h2 := hasDerivAt_comp_line hU hw hx (Pi.single i (1 : ℝ))
      rw [partialDerivR4_eq_fderiv hU hgU hx, partialDerivR4_eq_fderiv hU hw hx]
      simpa [HasLineDerivAt] using h1.fun_mul h2
    · have hx' : x ∉ tsupport g := fun h => hx (hg.tsupport_subset h)
      have hz : (fun y => g y * w y) =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx'] with y hy
        simp [hy]
      have hc : Tendsto (fun t : ℝ => x + t • (Pi.single i (1 : ℝ) : R4)) (𝓝 0) (𝓝 x) := by
        have h0 : ContinuousAt (fun t : ℝ => x + t • (Pi.single i (1 : ℝ) : R4)) 0 := by fun_prop
        simpa using h0.tendsto
      rw [partialDerivR4_eq_zero_of_notMem hx', image_eq_zero_of_notMem_tsupport hx']
      simp only [zero_mul, add_zero]
      exact (hasDerivAt_const (0 : ℝ) (0 : ℂ)).congr_of_eventuallyEq (hc.eventually hz)
  have i12 : Integrable fun x => partialDerivR4 i g x * w x + g x * partialDerivR4 i w x :=
    i1.add i2
  have hz := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := (volume : Measure R4)) (B := ContinuousLinearMap.mul ℝ ℂ)
    (f := fun y => g y * w y)
    (f' := fun x => partialDerivR4 i g x * w x + g x * partialDerivR4 i w x)
    (g := fun _ => (1 : ℂ)) (g' := fun _ => (0 : ℂ)) (v := Pi.single i (1 : ℝ))
    (by simpa only [ContinuousLinearMap.mul_apply', mul_one] using i12) (by simp)
    (by simpa only [ContinuousLinearMap.mul_apply', mul_one] using i3)
    (fun x _ => hline x) (fun x _ => hasDerivAt_const _ _)
  simp only [ContinuousLinearMap.mul_apply', mul_zero, integral_zero, mul_one] at hz
  rw [integral_add i1 i2] at hz
  linear_combination hz
theorem integral_laplacianR4_mul (hU : IsOpen U) (hg : IsTestIn U g) (hw : ContDiffOn ℝ ∞ w U) :
    ∫ x, laplacianR4 g x * w x = ∫ x, g x * laplacianR4 w x := by
  have hp : ∀ i : Fin 4, ∫ x, partialDerivR4 i (partialDerivR4 i g) x * w x =
      ∫ x, g x * partialDerivR4 i (partialDerivR4 i w) x := fun i => by
    rw [integral_partialDerivR4_mul hU (hg.partialDerivR4 i) hw i,
      integral_partialDerivR4_mul hU hg (contDiffOn_partialDerivR4 hU hw i) i, neg_neg]
  simp only [laplacianR4, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ =>
      ((hg.partialDerivR4 i).partialDerivR4 i).integrable_mul hU hw.continuousOn,
    integral_finsetSum _ fun i _ => hg.integrable_mul hU
      (contDiffOn_partialDerivR4 hU (contDiffOn_partialDerivR4 hU hw i) i).continuousOn]
  exact Finset.sum_congr rfl fun i _ => hp i
theorem integral_laplacianR4_iterate_three_mul (hU : IsOpen U) (hg : IsTestIn U g)
    (hw : ContDiffOn ℝ ∞ w U) :
    ∫ x, laplacianR4^[3] g x * w x = ∫ x, g x * laplacianR4^[3] w x := by
  have w1 := contDiffOn_laplacianR4 hU hw
  have w2 := contDiffOn_laplacianR4 hU w1
  have g1 := hg.laplacianR4
  have g2 := g1.laplacianR4
  calc ∫ x, laplacianR4^[3] g x * w x
      = ∫ x, laplacianR4 (laplacianR4 g) x * laplacianR4 w x :=
        integral_laplacianR4_mul hU g2 hw
    _ = ∫ x, laplacianR4 g x * laplacianR4 (laplacianR4 w) x :=
        integral_laplacianR4_mul hU g1 w1
    _ = ∫ x, g x * laplacianR4^[3] w x := integral_laplacianR4_mul hU hg w2
end Parts
section Classes
open YangMills.Construction.TorusMetric YangMills.Construction.MetricNotions
theorem norm_le_euclidNormVec (v : R4) : ‖v‖ ≤ euclidNormVec v := by apply _root_.YangMills.Construction.EuclideanFunctionals.Moments.norm_le_euclidNormVec <;> assumption
theorem euclidNormVec_le_two_mul_norm (v : R4) : euclidNormVec v ≤ 2 * ‖v‖ := by apply _root_.YangMills.Construction.EuclideanFunctionals.Moments.euclidNormVec_le_two_mul_norm <;> assumption
abbrev r4Metric : R4 → R4 → ℝ :=
  ReflectionPositivity.AxisMirror.Ambient.metric defaultMirrorData
    ReflectionPositivity.AxisMirror.Ambient.euclidean
theorem closureWrt_eq (Z : Set R4) : closureWrt r4Metric Z = closure Z := by apply _root_.YangMills.Construction.EuclideanFunctionals.Moments.closureWrt_r4Metric_eq <;> assumption
theorem supp_eq_tsupport {𝕜 : Type*} [RCLike 𝕜] (f : R4 → 𝕜) : supp f = tsupport f :=
  closureWrt_eq _
theorem mem_C1c_iff {𝕜 : Type*} [RCLike 𝕜] (f : R4 → 𝕜) :
    f ∈ C1c 𝕜 ↔ ContDiff ℝ 1 f ∧ HasCompactSupport f := by apply _root_.YangMills.Construction.EuclideanFunctionals.Moments.mem_C1c_iff_contDiff <;> assumption
theorem ofReal_mem_C1c {k : R4 → ℝ} (hk : k ∈ C1c ℝ) : (fun x => (k x : ℂ)) ∈ C1c ℂ := by apply _root_.YangMills.Construction.EuclideanFunctionals.RealTuples.ofReal_mem_C1c <;> assumption
theorem tsupport_ofReal_comp (k : R4 → ℝ) : tsupport (fun x => (k x : ℂ)) = tsupport k := by apply _root_.YangMills.Construction.EuclideanFunctionals.TensorComponents.tsupport_ofReal_comp <;> assumption
theorem abs_apply_three_le (z : R4) : |z 3| ≤ euclidNormVec z := by
  refine Real.abs_le_sqrt ?_
  exact Finset.single_le_sum (f := fun i => z i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ 3)
theorem isOpen_timeSlab (r : ℝ) : IsOpen (timeSlab r) :=
  isOpen_lt (continuous_apply 3).abs continuous_const
theorem isRealAnalyticIn_congr {D : Set (Coordinates.ComplexCoordinates 4)}
    {f f' : Coordinates.ComplexCoordinates 4 → Coordinates.ComplexCoordinates 1}
    (hf : Coordinates.ComplexCoordinates.IsRealAnalyticIn D f) (h : EqOn f f' D) :
    Coordinates.ComplexCoordinates.IsRealAnalyticIn D f' := by
  refine ⟨hf.1, fun a ha => ?_⟩
  obtain ⟨c, hc⟩ := hf.2 a ha
  refine ⟨c, ?_⟩
  obtain ⟨O, hO, rfl⟩ := hf.1
  filter_upwards [hc, inter_mem_nhdsWithin (Coordinates.ComplexCoordinates.realLocus 4)
    (hO.mem_nhds ha.1)] with z hz hm
  rw [← h ⟨hm.2, hm.1⟩]
  exact hz
end Classes
section Kernels
open YangMills.Construction.RealCoordinates YangMills.Construction.EuclideanFunctionals.CauchyEstimate YangMills.Construction.Coordinates.ComplexCoordinates.PowerSeriesHolomorphy
variable {m : SharpScale} {S : ConnFamily} {σ : EuclidFunctionalWithRecon m S}
  {p C cI cS cPar cCau η : ℝ} {F A : FreeSep}
theorem preimage_complexExtensionDomain (η : ℝ) :
    complexify ⁻¹' complexExtensionDomain η = timeSlab (η / 8) := by
  ext x
  simp [complexExtensionDomain, complexify]
theorem realLocus_strip_eq (η : ℝ) :
    {z : Coordinates.ComplexCoordinates 4 |
        z ∈ Coordinates.ComplexCoordinates.realLocus 4 ∧ |(z 3).re| < η / 8} =
      complexExtensionDomain η ∩ Coordinates.ComplexCoordinates.realLocus 4 := by
  ext z
  simp only [complexExtensionDomain, mem_ofPred_eq, mem_inter_iff]
  constructor
  · rintro ⟨hz, h⟩
    refine ⟨?_, hz⟩
    have him : ∀ j, (z j).im = 0 := hz
    simpa [him] using h
  · rintro ⟨h, hz⟩
    refine ⟨hz, ?_⟩
    have him : ∀ j, (z j).im = 0 := hz
    simpa [him] using h
theorem closedPolydisk_subset_complexExtensionDomain (hFr : ProductBoundParams p C cI cS cPar cCau)
    (h0 : 0 < η) {x : R4} (hx : x ∈ thinSlab cS η) :
    closedPolydisk (complexify x) (cauchyRadius cCau η) ⊆ complexExtensionDomain η := by
  intro z hz
  have hρ : ∀ j, ‖z j - complexify x j‖ ≤ cCau * η := hz
  have him : ∀ j, |(z j).im| ≤ cCau * η := fun j => by
    have h := (Complex.abs_im_le_norm (z j - complexify x j)).trans (hρ j)
    simpa [complexify] using h
  have hre : |(z 3).re| ≤ |x 3| + cCau * η := by
    have h := (Complex.abs_re_le_norm (z 3 - complexify x 3)).trans (hρ 3)
    have e : (z 3 - complexify x 3).re = (z 3).re - x 3 := by simp [complexify]
    rw [e] at h
    have h2 : |(z 3).re| ≤ |(z 3).re - x 3| + |x 3| := by
      simpa using abs_add_le ((z 3).re - x 3) (x 3)
    linarith
  have hxs : |x 3| < cS * η := hx
  have hsum : ∑ j : Fin 3, |(z j.castSucc).im| ≤ 3 * (cCau * η) := by
    calc ∑ j : Fin 3, |(z j.castSucc).im| ≤ ∑ _j : Fin 3, cCau * η :=
          Finset.sum_le_sum fun j _ => him _
      _ = 3 * (cCau * η) := by simp
  have hF3 := hFr.cS_add_cCau_le
  change |(z 3).re| + ∑ j : Fin 3, |(z j.castSucc).im| < η / 8
  nlinarith
theorem smallKernel_facts (hC : CauchyBound) (hU : TripleContinuation.ExtensionExists)
    (hcone : σ.ConeCondition) (hI : InsertionBoundHolds σ p C cI)
    (hFr : ProductBoundParams p C cI cS cPar cCau) (h0 : 0 < η) (h1 : η ≤ 1)
    (hF : F ∈ finCombIn {y | η / 4 < y 3}) (hA : A ∈ finCombIn {y | η / 4 < y 3})
    {k : R4 → ℝ} (hk : IsSmallKernel (paramRadius cPar η) k) :
    ExtendableTriple cI η F k A ∧ InsertionFnDerivBounds σ p C cS cCau η k F A := by
  have hT : ExtendableTriple cI η F k A := by
    refine ⟨h0, h1, hk.mem_C1c, fun z hz => ?_, hF, hA⟩
    have h := hk.supp_subset hz
    have e : TorusMetric.euclidNormVec z ≤ cPar * η := h
    have hF1 := hFr.cPar_le
    change TorusMetric.euclidNormVec z ≤ 1 / 2 * cI * η
    nlinarith
  refine ⟨hT, ?_⟩
  obtain ⟨u, -, -, hhol, heq, hb⟩ := hU σ hcone p C cI hI η F k A hT
  have hO : IsOpen (complexExtensionDomain η) := hhol.1
  obtain ⟨⟨hsm, han⟩, hest⟩ := hC (complexExtensionDomain η) u hO hhol
  have hopen := isOpen_timeSlab (η / 8)
  have hr : EqOn (tripleInsertionFn S F k A) (realRestriction u) (timeSlab (η / 8)) :=
    fun x hx => (heq x (le_of_lt hx)).symm
  have hslab : thinSlab cS η ⊆ timeSlab (η / 8) := fun x hx => by
    have h2 : |x 3| < cS * η := hx
    have h3 := hFr.cS_lt_eighth
    change |x 3| < η / 8
    nlinarith
  refine ⟨?_, fun γ => ?_, fun x hx γ => ?_⟩
  · rw [preimage_complexExtensionDomain] at hsm
    exact hsm.congr hr
  · have hgoal : Coordinates.ComplexCoordinates.IsRealAnalyticIn
        {z : Coordinates.ComplexCoordinates 4 |
          z ∈ Coordinates.ComplexCoordinates.realLocus 4 ∧ |(z 3).re| < η / 8}
        (viaRealParts (iteratedPartial γ (tripleInsertionFn S F k A))) := by
      rw [realLocus_strip_eq η]
      refine isRealAnalyticIn_congr (han γ) fun z hz => ?_
      have hzs : rePart z ∈ timeSlab (η / 8) := by
        rw [← realLocus_strip_eq η] at hz
        exact hz.2
      funext i
      exact (iteratedPartial_congr hopen hr γ hzs).symm
    exact hgoal
  · have hx8 := hslab hx
    rw [iteratedPartial_congr hopen hr γ hx8]
    have hxO : complexify x ∈ complexExtensionDomain η := by
      have : x ∈ complexify ⁻¹' complexExtensionDomain η :=
        (preimage_complexExtensionDomain η).symm ▸ hx8
      exact this
    have hsub := closedPolydisk_subset_complexExtensionDomain hFr h0 hx
    have hc : ∀ z ∈ complexExtensionDomain η, ‖u z‖ ≤ insertionMajorant σ p C η k F A :=
      fun z hz => hb z (le_of_lt (show complexExtensionGauge z < η / 8 from hz))
    have hρ : 0 < cauchyRadius cCau η := mul_pos hFr.cCau_pos h0
    exact hest x _ _ hxO hρ ((norm_nonneg _).trans (hc _ hxO)) hsub (fun z hz => hc z (hsub hz)) γ
end Kernels
section Smearing
open YangMills.Construction.TorusMetric
variable {m : SharpScale} {S : ConnFamily} {σ : EuclidFunctionalWithRecon m S}
  {p C cI cS cPar cCau η : ℝ} {F A : FreeSep}
theorem supp_add_supp_subset (hFr : ProductBoundParams p C cI cS cPar cCau) (h0 : 0 < η)
    {φ : R4 → ℂ} {k : R4 → ℝ} (hφ : supp φ ⊆ thinSlab cS η)
    (hk : IsSmallKernel (paramRadius cPar η) k) :
    supp φ + supp (fun x => (k x : ℂ)) ⊆ timeSlab (η / 8) := by
  rintro _ ⟨a, ha, b, hb, rfl⟩
  have h1 : |a 3| < cS * η := hφ ha
  rw [supp_eq_tsupport, tsupport_ofReal_comp, ← supp_eq_tsupport] at hb
  have h2 : euclidNormVec b ≤ cPar * η := hk.supp_subset hb
  have h3 := abs_apply_three_le b
  have h4 : |(a + b) 3| ≤ |a 3| + |b 3| := abs_add_le _ _
  have hF2 := hFr.cS_add_cPar_le
  change |(a + b) 3| < η / 8
  nlinarith
theorem smearIntegrand_eq (φ u : R4 → ℂ) : smearIntegrand φ u = fun x => φ x * u x := by
  funext x
  by_cases hx : x ∈ supp φ
  · simp only [smearIntegrand]
    rw [indicator_of_mem hx]
  · have h0 : φ x = 0 := by
      rw [supp_eq_tsupport] at hx
      exact image_eq_zero_of_notMem_tsupport hx
    simp only [smearIntegrand]
    rw [indicator_of_notMem hx]
    simp [h0]
theorem timeSlab_subset (hFr : ProductBoundParams p C cI cS cPar cCau) (h0 : 0 < η) :
    thinSlab cS η ⊆ timeSlab (η / 8) := fun x hx => by
  have h2 : |x 3| < cS * η := hx
  have h3 := hFr.cS_lt_eighth
  change |x 3| < η / 8
  nlinarith
theorem smearingFormula_holds (hE : InsertionForm.InsertionFormTheorem)
    (σ : EuclidFunctionalWithRecon m S)
    (hFr : ProductBoundParams p C cI cS cPar cCau) (h0 : 0 < η)
    (hF : F ∈ finCombIn {y | η / 4 < y 3}) (hA : A ∈ finCombIn {y | η / 4 < y 3})
    {k : R4 → ℝ} (hk : IsSmallKernel (paramRadius cPar η) k)
    (hu : ContDiffOn ℝ ∞ (tripleInsertionFn S F k A) (timeSlab (η / 8)))
    {φ : R4 → ℂ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hs : supp φ ⊆ thinSlab cS η) : ParametrixBracket.SmearingFormula S η φ k F A := by
  have hsub := supp_add_supp_subset hFr h0 hs hk
  have hsub4 : supp φ + supp (fun x => (k x : ℂ)) ⊆ timeSlab (η / 4) :=
    fun x hx => by
      have h1 : |x 3| < η / 8 := hsub hx
      change |x 3| < η / 4
      linarith
  obtain ⟨-, -, -, -, -, hS⟩ := hE m S σ (η / 4) (by positivity) F hF A hA
  obtain ⟨m1, m2, -, -, m5⟩ := hS φ _ hφ hφc (ofReal_mem_C1c hk.mem_C1c) hsub4
  have hts : tsupport φ ⊆ timeSlab (η / 8) := by
    rw [← supp_eq_tsupport]
    exact hs.trans (timeSlab_subset hFr h0)
  refine ⟨m1, m2.trans hsub, ?_, ?_⟩
  · rw [smearIntegrand_eq]
    exact (continuous_mul_of_tsupport_subset_open (isOpen_timeSlab _) hφ hts
      hu.continuousOn).integrable_of_hasCompactSupport hφc.mul_right
  · have hm : MeasurableSet (supp φ) := by
      rw [supp_eq_tsupport]
      exact (isClosed_tsupport φ).measurableSet
    rw [m5]
    simp only [smearIntegrand]
    rw [integral_indicator hm]
    rfl
end Smearing
section Transfer
open YangMills.Construction.EuclideanAnalysis YangMills.Construction.EuclideanAnalysis.CubedLaplacian YangMills.Construction.TestFunctions
def euclideanEquiv : R4 ≃L[ℝ] RealSpace 4 := (EuclideanSpace.equiv (Fin 4) ℝ).symm
theorem norm_toLp_eq_euclidNormVec (x : R4) :
    ‖(WithLp.toLp 2 x : RealSpace 4)‖ = TorusMetric.euclidNormVec x := by
  simp [EuclideanSpace.norm_eq, TorusMetric.euclidNormVec, sq_abs]
theorem continuous_euclidNormVec : Continuous TorusMetric.euclidNormVec := by apply _root_.YangMills.Construction.SeparatedTuples.continuous_euclidNormVec <;> assumption
theorem isSmallKernel_of_contDiff {r : ℝ} {f : RealSpace 4 → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ Metric.ball 0 r) :
    IsSmallKernel r (fun x => f (WithLp.toLp 2 x)) := by
  refine ⟨(mem_C1c_iff _).2 ⟨hf.comp euclideanEquiv.contDiff, ?_⟩, ?_⟩
  · exact hc.comp_isClosedEmbedding euclideanEquiv.toHomeomorph.isClosedEmbedding
  · rw [supp_eq_tsupport]
    refine closure_minimal (fun x hx => ?_) (isClosed_le continuous_euclidNormVec continuous_const)
    have h1 : WithLp.toLp 2 x ∈ tsupport f := subset_tsupport f hx
    have h2 := hs h1
    rw [mem_ball_zero_iff, norm_toLp_eq_euclidNormVec] at h2
    exact le_of_lt h2
theorem isSmallKernel_parametrixFn {r : ℝ} (hr : KernelsRegularAndLocal r) :
    IsSmallKernel r (parametrixFn r) :=
  isSmallKernel_of_contDiff hr.1 hr.2.2.2.1 hr.2.2.2.2.1
theorem isSmallKernel_remainderFn {r : ℝ} (hr : KernelsRegularAndLocal r) :
    IsSmallKernel r (remainderFn r) := by
  refine isSmallKernel_of_contDiff (f := fun y => (remainderDensity r y).re) ?_ ?_ ?_
  · exact Complex.reCLM.contDiff.comp (hr.2.1.of_le (by simp))
  · exact hr.2.2.2.2.2.1.comp_left Complex.zero_re
  · exact (tsupport_comp_subset (g := Complex.re) Complex.zero_re _).trans hr.2.2.2.2.2.2
theorem ofReal_remainderFn {r : ℝ} (hr : KernelsRegularAndLocal r) (x : R4) :
    ((remainderFn r x : ℝ) : ℂ) = remainderDensity r (WithLp.toLp 2 x) := by
  apply Complex.ext
  · simp [remainderFn]
  · simp [hr.2.2.1]
theorem partialDeriv_comp_ofLp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : R4 → E) (i : Fin 4) :
    EuclideanAnalysis.partialDeriv i (fun y : RealSpace 4 => G (WithLp.ofLp y)) =
      fun y => partialDerivR4 i G (WithLp.ofLp y) := by
  funext y
  simp only [EuclideanAnalysis.partialDeriv, lineDeriv, partialDerivR4,
    EuclideanAnalysis.stdBasisVector]
  congr 1
theorem partialDerivR4_comp_toLp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : RealSpace 4 → E) (i : Fin 4) (x : R4) :
    partialDerivR4 i (fun y => f (WithLp.toLp 2 y)) x =
      EuclideanAnalysis.partialDeriv i f (WithLp.toLp 2 x) := by
  have h := congrFun (partialDeriv_comp_ofLp (fun y => f (WithLp.toLp 2 y)) i) (WithLp.toLp 2 x)
  simpa using h.symm
theorem laplacian_comp_ofLp (G : R4 → ℂ) :
    EuclideanAnalysis.laplacian (fun y : RealSpace 4 => G (WithLp.ofLp y)) =
      fun y => laplacianR4 G (WithLp.ofLp y) := by
  funext y
  simp only [EuclideanAnalysis.laplacian, laplacianR4, partialDeriv_comp_ofLp]
theorem testLaplacian_coe {φ : SmoothTestFunction} {G : R4 → ℂ}
    (h : (φ : RealSpace 4 → ℂ) = fun y => G (WithLp.ofLp y)) :
    (testLaplacian φ : RealSpace 4 → ℂ) = fun y => laplacianR4 G (WithLp.ofLp y) := by
  funext y
  rw [testLaplacian_apply, h, laplacian_comp_ofLp]
theorem testLaplacianCubed_coe {φ : SmoothTestFunction} {G : R4 → ℂ}
    (h : (φ : RealSpace 4 → ℂ) = fun y => G (WithLp.ofLp y)) :
    (testLaplacianCubed φ : RealSpace 4 → ℂ) =
      fun y => laplacianR4^[3] G (WithLp.ofLp y) :=
  testLaplacian_coe (testLaplacian_coe (testLaplacian_coe h))
def toSmoothTestFunction {g : R4 → ℂ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    SmoothTestFunction :=
  ⟨fun y => g (WithLp.ofLp y), hg.comp euclideanEquiv.symm.contDiff,
    hc.comp_isClosedEmbedding euclideanEquiv.symm.toHomeomorph.isClosedEmbedding, by simp⟩
theorem conv_comm (a b : R4 → ℂ) : «conv» a b = «conv» b a := by
  funext x
  have h := integral_sub_left_eq_self (fun y => a y * b (x - y)) (volume : Measure R4) x
  simp only [sub_sub_cancel] at h
  unfold «conv»
  rw [← h]
  exact integral_congr_ae (Eventually.of_forall fun y => mul_comm _ _)
theorem convolution_comp_ofLp (a b : R4 → ℂ) (x : R4) :
    EuclideanAnalysis.convolution (fun y : RealSpace 4 => a (WithLp.ofLp y))
      (fun y : RealSpace 4 => b (WithLp.ofLp y)) (WithLp.toLp 2 x) = «conv» a b x := by
  rw [conv_comm]
  have hp := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 4)).symm
  have h := hp.integral_comp' (fun y : RealSpace 4 =>
    a (WithLp.ofLp (WithLp.toLp 2 x - y)) * b (WithLp.ofLp y))
  simp only [EuclideanAnalysis.convolution, «conv»]
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp [mul_comm]
theorem reproducing_identity_R4 {r : ℝ} (hP : ReproducingIdentity r) (hr : KernelsRegularAndLocal r)
    {g : R4 → ℂ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (x : R4) :
    g x = «conv» (laplacianR4^[3] g) (fun y => (parametrixFn r y : ℂ)) x +
      «conv» g (fun y => (remainderFn r y : ℂ)) x := by
  have h := hP (toSmoothTestFunction hg hc) (WithLp.toLp 2 x)
  have e0 : ((toSmoothTestFunction hg hc : SmoothTestFunction) : RealSpace 4 → ℂ) =
      fun y => g (WithLp.ofLp y) := rfl
  rw [show ((toSmoothTestFunction hg hc : SmoothTestFunction) : RealSpace 4 → ℂ)
      (WithLp.toLp 2 x) = g x from rfl, testLaplacianCubed_coe e0, e0] at h
  have e1 : (fun y : RealSpace 4 => ((laplacianCubedParametrix r y : ℝ) : ℂ)) =
      fun y => ((parametrixFn r (WithLp.ofLp y) : ℝ) : ℂ) := by
    funext y
    simp [parametrixFn]
  have e2 : remainderDensity r = fun y => ((remainderFn r (WithLp.ofLp y) : ℝ) : ℂ) := by
    funext y
    rw [ofReal_remainderFn hr]
  rw [e1, e2, convolution_comp_ofLp (laplacianR4^[3] g) (fun y => (parametrixFn r y : ℂ)),
    convolution_comp_ofLp g (fun y => (remainderFn r y : ℂ))] at h
  exact h
theorem deriv_ofReal_comp_zero (G : ℝ → ℝ) :
    deriv (fun t => (G t : ℂ)) 0 = ((deriv G 0 : ℝ) : ℂ) := by apply _root_.YangMills.Construction.Tower.HessianOfStepComposite.deriv_ofReal_comp_zero <;> assumption
theorem partialDerivR4_ofReal (f : R4 → ℝ) (i : Fin 4) :
    partialDerivR4 i (fun x => (f x : ℂ)) = fun x => ((partialDerivR4 i f x : ℝ) : ℂ) := by
  funext x
  simp only [partialDerivR4]
  exact deriv_ofReal_comp_zero _
theorem laplacianR4_ofReal (f : R4 → ℝ) :
    laplacianR4 (fun x => (f x : ℂ)) = fun x => ((laplacianR4 f x : ℝ) : ℂ) := by
  funext x
  simp only [laplacianR4, partialDerivR4_ofReal, Complex.ofReal_sum]
theorem laplacianR4_iterate_three_ofReal (f : R4 → ℝ) :
    laplacianR4^[3] (fun x => (f x : ℂ)) = fun x => ((laplacianR4^[3] f x : ℝ) : ℂ) := by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id,
    laplacianR4_ofReal]
end Transfer
section Form
open YangMills.Construction.TestFunctions YangMills.Construction.EuclideanAnalysis YangMills.Construction.EuclideanAnalysis.CubedLaplacian
variable {m : SharpScale} {S : ConnFamily} {p C cI cS cPar cCau η : ℝ} {F A : FreeSep}
theorem weightedIntegrand_eq {h g : R4 → ℝ} (u : R4 → ℂ)
    (hz : ∀ x, x ∉ tsupport h → g x = 0) :
    weightedIntegrand h g u = fun x => (g x : ℂ) * u x := by
  funext x
  by_cases hx : x ∈ supp h
  · simp only [weightedIntegrand]
    rw [indicator_of_mem hx]
  · have h0 := hz x (by rwa [← supp_eq_tsupport])
    simp only [weightedIntegrand]
    rw [indicator_of_notMem hx]
    simp [h0]
theorem parametrixRepresentation_holds (hE : InsertionForm.InsertionFormTheorem)
    (σ : EuclidFunctionalWithRecon m S)
    (hFr : ProductBoundParams p C cI cS cPar cCau) (h0 : 0 < η)
    (hF : F ∈ finCombIn {y | η / 4 < y 3}) (hA : A ∈ finCombIn {y | η / 4 < y 3})
    (hPi : ReproducingIdentity (paramRadius cPar η))
    (hr : KernelsRegularAndLocal (paramRadius cPar η))
    (hun : ContDiffOn ℝ ∞ (tripleInsertionFn S F
      (parametrixFn (paramRadius cPar η)) A) (timeSlab (η / 8)))
    (hus : ContDiffOn ℝ ∞ (tripleInsertionFn S F
      (remainderFn (paramRadius cPar η)) A) (timeSlab (η / 8)))
    {h : R4 → ℝ} (hh : h ∈ smoothCompactSupp R4 ℝ)
    (hs : supp h ⊆ thinSlab cS η) :
    ParametrixRepresentation S (paramRadius cPar η) h F A := by
  have hn := isSmallKernel_parametrixFn hr
  have hsk := isSmallKernel_remainderFn hr
  set r := paramRadius cPar η with hrdef
  set Un := tripleInsertionFn S F (parametrixFn r) A with hUn
  set Us := tripleInsertionFn S F (remainderFn r) A with hUs
  set g : R4 → ℂ := fun x => (h x : ℂ) with hgdef
  have hWo := isOpen_timeSlab (η / 8)
  have hgs : ContDiff ℝ ∞ g := Complex.ofRealCLM.contDiff.comp hh.1
  have hgc : HasCompactSupport g := hh.2.comp_left Complex.ofReal_zero
  have htsg : tsupport g = tsupport h := tsupport_ofReal_comp h
  have hs1 : tsupport g ⊆ thinSlab cS η := by
    rw [htsg, ← supp_eq_tsupport]
    exact hs
  have hW : tsupport g ⊆ timeSlab (η / 8) := hs1.trans (timeSlab_subset hFr h0)
  have hT0 : IsTestIn (tsupport g) g := ⟨hgs, hgc, subset_rfl⟩
  have hT3 : IsTestIn (tsupport g) (laplacianR4^[3] g) :=
    hT0.laplacianR4.laplacianR4.laplacianR4
  have hT : IsTestIn (timeSlab (η / 8)) g := ⟨hgs, hgc, hW⟩
  have hT3W : IsTestIn (timeSlab (η / 8)) (laplacianR4^[3] g) :=
    ⟨hT3.contDiff, hT3.hasCompactSupport, hT3.tsupport_subset.trans hW⟩
  have e3 : ∀ x, ((laplacianR4^[3] h x : ℝ) : ℂ) = laplacianR4^[3] g x := fun x =>
    (congrFun (laplacianR4_iterate_three_ofReal h) x).symm
  have z3 : ∀ x, x ∉ tsupport h → laplacianR4^[3] h x = 0 := by
    intro x hx
    have h3 : laplacianR4^[3] g x = 0 :=
      image_eq_zero_of_notMem_tsupport fun hm => hx (htsg ▸ hT3.tsupport_subset hm)
    rw [← e3] at h3
    exact_mod_cast h3
  have z1 : ∀ x, x ∉ tsupport h → h x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have a1 : weightedIntegrand h (laplacianR4^[3] h) Un =
      fun x => laplacianR4^[3] g x * Un x := by
    rw [weightedIntegrand_eq _ z3]
    funext x
    rw [e3]
  have a2 : weightedIntegrand h h Us = fun x => g x * Us x :=
    weightedIntegrand_eq _ z1
  have a3 : weightedIntegrand h h (bracketFn S r F A) = fun x => g x * bracketFn S r F A x :=
    weightedIntegrand_eq _ z1
  have w1 : ContDiffOn ℝ ∞ (laplacianR4^[3] Un) (timeSlab (η / 8)) :=
    contDiffOn_laplacianR4 hWo (contDiffOn_laplacianR4 hWo (contDiffOn_laplacianR4 hWo hun))
  have i1 := hT.integrable_mul hWo w1.continuousOn
  have i2 := hT.integrable_mul hWo hus.continuousOn
  have i0 := hT3W.integrable_mul hWo hun.continuousOn
  have hb : ContinuousOn (bracketFn S r F A) (timeSlab (η / 8)) :=
    w1.continuousOn.add hus.continuousOn
  have hs3 : supp (laplacianR4^[3] g) ⊆ thinSlab cS η := by
    rw [supp_eq_tsupport]
    exact hT3.tsupport_subset.trans hs1
  have hsg : supp g ⊆ thinSlab cS η := by
    rw [supp_eq_tsupport]
    exact hs1
  have s1 := smearingFormula_holds hE σ hFr h0 hF hA hn hun hT3.contDiff.continuous
    hT3.hasCompactSupport hs3
  have s2 := smearingFormula_holds hE σ hFr h0 hF hA hsk hus hgs.continuous hgc hsg
  obtain ⟨-, hL, -, -, -, -⟩ := hE m S σ (η / 4) (by positivity) F hF A hA
  have hmono : timeSlab (η / 8) ⊆ timeSlab (η / 4) := fun x hx => by
    have h8 : |x 3| < η / 8 := hx
    change |x 3| < η / 4
    linarith
  have hlin := (hL.2 1 1 _ _
    (⟨s1.mem_C1c, s1.supp_subset.trans hmono⟩ : InsertionForm.IsSlabInsert (η / 4) _)
    (⟨s2.mem_C1c, s2.supp_subset.trans hmono⟩ : InsertionForm.IsSlabInsert (η / 4) _)).2
  have eg : g = (1 : ℂ) • («conv» (laplacianR4^[3] g) fun y => (parametrixFn r y : ℂ)) +
      (1 : ℂ) • («conv» g fun y => (remainderFn r y : ℂ)) := by
    funext x
    simpa using reproducing_identity_R4 hPi hr hgs hgc x
  have ev : insertion S F g A = insertion S F
      ((1 : ℂ) • («conv» (laplacianR4^[3] g) fun y => (parametrixFn r y : ℂ)) +
        (1 : ℂ) • («conv» g fun y => (remainderFn r y : ℂ))) A :=
    congrArg (fun f => insertion S F f A) eg
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [a1]
    exact i0
  · rw [a2]
    exact i2
  · rw [a3]
    exact hT.integrable_mul hWo hb
  · rw [a1, a2]
    change insertion S F g A = _
    rw [ev, hlin, s1.eq_integral, s2.eq_integral, smearIntegrand_eq, smearIntegrand_eq, one_mul,
      one_mul]
  · rw [a1, a2, a3, integral_laplacianR4_iterate_three_mul hWo hT hun, ← integral_add i1 i2]
    exact integral_congr_ae (Eventually.of_forall fun x => (mul_add _ _ _).symm)
end Form
section Bounds
open YangMills.Construction.TestFunctions YangMills.Construction.EuclideanAnalysis YangMills.Construction.EuclideanAnalysis.CubedLaplacian
variable {m : SharpScale} {S : ConnFamily} {σ : EuclidFunctionalWithRecon m S}
  {p C cI cS cPar cCau η : ℝ} {F A : FreeSep}
theorem sharpNorm_ofReal_comp (c : SharpScale) (k : R4 → ℝ) :
    c.sharpNorm (fun x => (k x : ℂ)) = c.sharpNorm k := by
  simp only [SharpScale.sharpNorm, sharpNormR4, uniformNorm, lipConstR4, bestLipschitzConstant,
    ← Complex.ofReal_sub, Complex.norm_real]
theorem uniformNorm_comp_toLp {E : Type*} [Norm E] (f : RealSpace 4 → E) :
    uniformNorm (fun x : R4 => f (WithLp.toLp 2 x)) = uniformNorm f :=
  euclideanEquiv.toEquiv.iSup_comp (g := fun y => ‖f y‖)
theorem gradSup_comp_toLp (f : RealSpace 4 → ℂ) :
    SharpNormC1.gradSup (fun x => f (WithLp.toLp 2 x)) = EuclideanAnalysis.gradUniformNorm f := by
  have e : ∀ y, ‖gradNorm f y‖ = gradNorm f y := fun y =>
    Real.norm_of_nonneg (Real.sqrt_nonneg _)
  have e2 : ∀ (i : Fin 4) (x : R4), partialDerivR4 i (fun y => f (WithLp.toLp 2 y)) x =
      EuclideanAnalysis.partialDeriv i f (WithLp.toLp 2 x) := partialDerivR4_comp_toLp f
  simp only [EuclideanAnalysis.gradUniformNorm, uniformNorm, e, SharpNormC1.gradSup, e2]
  exact euclideanEquiv.toEquiv.iSup_comp (g := gradNorm f)
theorem gradUniformNorm_ofReal_comp (f : RealSpace 4 → ℝ) :
    EuclideanAnalysis.gradUniformNorm (fun y => (f y : ℂ)) =
      EuclideanAnalysis.gradUniformNorm f := by
  have e : ∀ (i : Fin 4) (y : RealSpace 4),
      EuclideanAnalysis.partialDeriv i (fun y => (f y : ℂ)) y =
        ((EuclideanAnalysis.partialDeriv i f y : ℝ) : ℂ) := fun i y => deriv_ofReal_comp_zero _
  have e2 : gradNorm (fun y => (f y : ℂ)) = gradNorm f := by
    funext y
    simp only [gradNorm, e, Complex.norm_real]
  simp only [EuclideanAnalysis.gradUniformNorm, e2]
theorem sharpNorm_parametrixFn_le (hN : SharpNormC1.Main) (c : SharpScale)
    {r : ℝ} (hk : parametrixFn r ∈ C1c ℝ) :
    c.sharpNorm (parametrixFn r) ≤
      max (uniformNorm (laplacianCubedParametrix r))
        (40 * c.M * EuclideanAnalysis.gradUniformNorm (laplacianCubedParametrix r)) := by
  have h := ((hN.2 c).1 _ (ofReal_mem_C1c hk)).2
  have e1 : uniformNorm (fun x => ((parametrixFn r x : ℝ) : ℂ)) =
      uniformNorm (laplacianCubedParametrix r) := by
    simp only [uniformNorm, Complex.norm_real]
    exact uniformNorm_comp_toLp (laplacianCubedParametrix r)
  have e2 : SharpNormC1.gradSup (fun x => ((parametrixFn r x : ℝ) : ℂ)) =
      EuclideanAnalysis.gradUniformNorm (laplacianCubedParametrix r) := by
    rw [← gradUniformNorm_ofReal_comp]
    exact gradSup_comp_toLp (fun y => (laplacianCubedParametrix r y : ℂ))
  rwa [sharpNorm_ofReal_comp, e1, e2] at h
theorem sharpNorm_remainderFn_le (hN : SharpNormC1.Main) (c : SharpScale)
    {r : ℝ} (hr : KernelsRegularAndLocal r) (hk : remainderFn r ∈ C1c ℝ) :
    c.sharpNorm (remainderFn r) ≤
      max (uniformNorm (remainderDensity r))
        (40 * c.M * EuclideanAnalysis.gradUniformNorm (remainderDensity r)) := by
  have h := ((hN.2 c).1 _ (ofReal_mem_C1c hk)).2
  have e : (fun x => ((remainderFn r x : ℝ) : ℂ)) =
      fun x => remainderDensity r (WithLp.toLp 2 x) := funext (ofReal_remainderFn hr)
  rw [sharpNorm_ofReal_comp, e, uniformNorm_comp_toLp (remainderDensity r),
    gradSup_comp_toLp (remainderDensity r)] at h
  exact h
theorem uniformNorm_nonneg {X E : Type*} [NormedAddCommGroup E] (f : X → E) :
    0 ≤ uniformNorm f :=
  Real.iSup_nonneg fun _ => norm_nonneg _
theorem add_le_of_factor_bounds {Wt L Cd a c X Y e T1 T2 : ℝ} (hW : 0 ≤ Wt) (hL : 0 ≤ L)
    (hCd : 0 ≤ Cd) (ha : 0 ≤ a) (hc : 0 ≤ c) (he : 0 ≤ e)
    (h1 : T1 ≤ Cd * (X * e) * (Wt * (L * a))) (h2 : T2 ≤ Wt * (L * (Y * e) * c)) :
    T1 + T2 ≤ L * Wt * e * max X Y * (Cd * a + c) := by
  have b1 : L * Wt * e * (Cd * a) * X ≤ L * Wt * e * (Cd * a) * max X Y :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
  have b2 : L * Wt * e * c * Y ≤ L * Wt * e * c * max X Y :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
  nlinarith
theorem bracketBounds_holds (hN : SharpNormC1.Main)
    (hFr : ProductBoundParams p C cI cS cPar cCau) (h0 : 0 < η) (h1 : η ≤ 1)
    (hr : KernelsRegularAndLocal (paramRadius cPar η))
    (hScale : KernelNormsScaling (paramRadius cPar η))
    (dn : InsertionFnDerivBounds σ p C cS cCau η (parametrixFn (paramRadius cPar η)) F A)
    (ds : InsertionFnDerivBounds σ p C cS cCau η (remainderFn (paramRadius cPar η)) F A)
    {x : R4} (hx : x ∈ thinSlab cS η) : BracketBounds σ p C cPar cCau η F A x := by
  have hn := isSmallKernel_parametrixFn hr
  have hsk := isSmallKernel_remainderFn hr
  have hr0 : 0 < paramRadius cPar η := mul_pos hFr.cPar_pos h0
  have hρ0 : 0 < cauchyRadius cCau η := mul_pos hFr.cCau_pos h0
  have hcp : cPar ≤ 1 := by
    have a1 := hFr.cPar_le
    have a2 := hFr.cI_lt
    linarith
  have hr1 : paramRadius cPar η ≤ 1 := by
    have := hFr.cPar_pos
    change cPar * η ≤ 1
    nlinarith
  obtain ⟨n1, n2, n3, n4⟩ := hScale
  have x8 := timeSlab_subset hFr h0 hx
  have e3 := laplacianR4_iterate_three (isOpen_timeSlab (η / 8)) dn.contDiffOn x8
  set r := paramRadius cPar η with hrdef
  set ρ := cauchyRadius cCau η with hρdef
  set Un := tripleInsertionFn S F (parametrixFn r) A with hUn
  set Us := tripleInsertionFn S F (remainderFn r) A with hUs
  set NF := heightNorm σ (η / 4) F with hNF
  set NA := heightNorm σ (η / 4) A with hNA
  have hNF0 : 0 ≤ NF := norm_nonneg _
  have hNA0 : 0 ≤ NA := norm_nonneg _
  set Wt := (2 : ℝ) ^ p * C * η ^ (-p) * NF * NA with hWt
  have hW0 : 0 ≤ Wt := by
    have := hFr.constant_nonneg
    positivity
  have hbnd : ∀ k : R4 → ℝ, insertionMajorant σ p C η k F A = Wt * m.sharpNorm k := fun k => by
    simp only [insertionMajorant, hWt, hNF, hNA]
    ring
  have hsum : (∑ j, ((cubeIndices j).fact : ℝ)) = 4800 := by
    exact_mod_cast sum_fact_cubeIndices
  have hT : ‖laplacianR4^[3] Un x‖ ≤
      laplacianCubedConst * ρ ^ (-6 : ℤ) * insertionMajorant σ p C η (parametrixFn r) F A := by
    rw [e3, laplacianCubedConst_eq]
    calc ‖∑ j, iteratedPartial (cubeIndices j) Un x‖
        ≤ ∑ j, ‖iteratedPartial (cubeIndices j) Un x‖ := norm_sum_le _ _
      _ ≤ ∑ j, ((cubeIndices j).fact : ℝ) * ρ ^ (-6 : ℤ) *
            insertionMajorant σ p C η (parametrixFn r) F A := by
          refine Finset.sum_le_sum fun j _ => ?_
          have hb := dn.norm_le x hx (cubeIndices j)
          rw [order_cubeIndices] at hb
          exact_mod_cast hb
      _ = 4800 * ρ ^ (-6 : ℤ) * insertionMajorant σ p C η (parametrixFn r) F A := by
          rw [← Finset.sum_mul, ← Finset.sum_mul, hsum]
  have hSr : ‖Us x‖ ≤ insertionMajorant σ p C η (remainderFn r) F A := by
    have hb := ds.norm_le x hx 0
    simpa [iteratedPartial, Multiindex.fact, Multiindex.order] using hb
  refine ⟨hT, hSr, ?_⟩
  set a := uniformNorm parametrixOne with ha
  set b := EuclideanAnalysis.gradUniformNorm parametrixOne with hb
  set c := uniformNorm remainderDensityOne with hc
  set d := EuclideanAnalysis.gradUniformNorm remainderDensityOne with hd
  have ha0 : 0 ≤ a := uniformNorm_nonneg _
  have hb0 : 0 ≤ b := uniformNorm_nonneg _
  have hc0 : 0 ≤ c := uniformNorm_nonneg _
  have hd0 : 0 ≤ d := uniformNorm_nonneg _
  set L := 40 * m.M with hL
  have hL1 : 1 ≤ L := by
    have := m.one_le
    rw [hL]
    linarith
  have hnS : m.sharpNorm (parametrixFn r) ≤ L * r * (a + b) := by
    have h := sharpNorm_parametrixFn_le hN m hn.mem_C1c
    rw [n1, n2] at h
    refine h.trans (max_le ?_ ?_)
    · have t1 : r ^ 2 ≤ L * r := by nlinarith
      calc r ^ 2 * a ≤ L * r * a := mul_le_mul_of_nonneg_right t1 ha0
        _ ≤ L * r * (a + b) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    · have t1 : L * (r * b) = L * r * b := by ring
      rw [t1]
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hsS : m.sharpNorm (remainderFn r) ≤ L * (r ^ 5)⁻¹ * (c + d) := by
    have h := sharpNorm_remainderFn_le hN m hr hsk.mem_C1c
    rw [n3, n4] at h
    refine h.trans (max_le ?_ ?_)
    · have t0 : (r ^ 4)⁻¹ = r * (r ^ 5)⁻¹ := by
        field_simp
      have t2 : 0 ≤ (r ^ 5)⁻¹ := by positivity
      have t1 : (r ^ 4)⁻¹ ≤ L * (r ^ 5)⁻¹ := by
        rw [t0]
        exact mul_le_mul_of_nonneg_right (hr1.trans hL1) t2
      calc (r ^ 4)⁻¹ * c ≤ L * (r ^ 5)⁻¹ * c := mul_le_mul_of_nonneg_right t1 hc0
        _ ≤ L * (r ^ 5)⁻¹ * (c + d) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    · have t1 : L * ((r ^ 5)⁻¹ * d) = L * (r ^ 5)⁻¹ * d := by ring
      rw [t1]
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hcp0 := hFr.cPar_pos
  have hcc0 := hFr.cCau_pos
  have hρr : ρ ^ (-6 : ℤ) * r = (cCau ^ 6)⁻¹ * cPar * (η ^ 5)⁻¹ := by
    rw [hρdef, hrdef, zpow_neg]
    simp only [cauchyRadius, paramRadius]
    norm_cast
    field_simp
  have hr5 : (r ^ 5)⁻¹ = (cPar ^ 5)⁻¹ * (η ^ 5)⁻¹ := by
    rw [hrdef, paramRadius, mul_pow, mul_inv]
  have hexp : η ^ (-productExponent p) = η ^ (-p) * (η ^ 5)⁻¹ := by
    rw [productExponent, neg_add, Real.rpow_add h0, Real.rpow_neg h0.le]
    norm_num
  have hCd : (0 : ℝ) ≤ laplacianCubedConst := by
    rw [laplacianCubedConst_eq]
    norm_num
  have b1 : ‖laplacianR4^[3] Un x‖ ≤
      laplacianCubedConst * ((cCau ^ 6)⁻¹ * cPar * (η ^ 5)⁻¹) * (Wt * (L * (a + b))) := by
    refine hT.trans ?_
    rw [hbnd, ← hρr]
    calc laplacianCubedConst * ρ ^ (-6 : ℤ) * (Wt * m.sharpNorm (parametrixFn r))
        ≤ laplacianCubedConst * ρ ^ (-6 : ℤ) * (Wt * (L * r * (a + b))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hnS hW0) (by positivity)
      _ = laplacianCubedConst * (ρ ^ (-6 : ℤ) * r) * (Wt * (L * (a + b))) := by ring
  have b2 : ‖Us x‖ ≤ Wt * (L * ((cPar ^ 5)⁻¹ * (η ^ 5)⁻¹) * (c + d)) := by
    refine hSr.trans ?_
    rw [hbnd, ← hr5]
    exact mul_le_mul_of_nonneg_left hsS hW0
  have hfin := add_le_of_factor_bounds hW0 (by linarith) hCd (by linarith : 0 ≤ a + b)
    (by linarith : 0 ≤ c + d) (by positivity : 0 ≤ (η ^ 5)⁻¹) b1 b2
  refine hfin.trans (le_of_eq ?_)
  rw [hexp]
  simp only [productConst, productAbsConst, hWt, hL]
  ring
end Bounds
theorem main_holds (hC : CauchyEstimate.CauchyBound) (hU : TripleContinuation.ExtensionExists)
    (hE : InsertionForm.InsertionFormTheorem)
    (hP : EuclideanAnalysis.CubedLaplacian.ParametrixSpec)
    (hN : SharpNormC1.Main) : Main := by
  intro m S σ p C cI cS cPar cCau hcone hI hFr η h0 h1 F hF A hA
  have hr0 : 0 < paramRadius cPar η := mul_pos hFr.cPar_pos h0
  obtain ⟨-, -, hreg, hid, -⟩ := hP
  have hr := hreg _ hr0
  obtain ⟨hPi, hSc⟩ := hid _ hr0
  have hn := isSmallKernel_parametrixFn hr
  have hsk := isSmallKernel_remainderFn hr
  have facts := fun (k : R4 → ℝ) (hk : IsSmallKernel (paramRadius cPar η) k) =>
    smallKernel_facts (F := F) (A := A) (S := S) hC hU hcone hI hFr h0 h1 hF hA hk
  refine ⟨facts, fun k hk φ hφ hφc hsu =>
      smearingFormula_holds hE σ hFr h0 hF hA hk (facts k hk).2.contDiffOn hφ hφc hsu, hn, hsk,
    fun h hh hsu => parametrixRepresentation_holds hE σ hFr h0 hF hA hPi hr
      (facts _ hn).2.contDiffOn (facts _ hsk).2.contDiffOn hh hsu,
    fun x hx => bracketBounds_holds hN hFr h0 h1 hr hSc (facts _ hn).2 (facts _ hsk).2 hx⟩
end YangMills.Construction.EuclideanFunctionals.ParametrixBracket
