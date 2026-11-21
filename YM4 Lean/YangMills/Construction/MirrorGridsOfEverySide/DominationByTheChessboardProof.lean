import YangMills.Construction.ChessboardTori.ChessboardEstimateAndSubadditivityProof
import YangMills.Construction.MirrorGridsOfEverySide.ChessboardEstimateOnGridsOfEverySide
import YangMills.Construction.MirrorGridsOfEverySide.DominationByTheChessboard
import YangMills.Construction.MirrorGridsOfEverySide.FactsOfAMirrorGrid
import YangMills.Construction.MirrorGridsOfEverySide.JensenInequalityFromThePeriodsOfTheState
import Mathlib
set_option autoImplicit false
open Filter Set MeasureTheory
open scoped Topology ComplexConjugate
noncomputable section
namespace YangMills.Construction.MirrorGridsAllSides
open ChessboardTori (ReflectionGrid)
namespace ChessboardDomination
theorem le_liminf_of_forall_sub_eventually {ι : Type*} {l : Filter ι} [l.NeBot] {q : ι → ℝ}
    {A B : ℝ} (hB : ∀ᶠ k in l, q k ≤ B) (h : ∀ η : ℝ, 0 < η → ∀ᶠ k in l, A - η ≤ q k) :
    A ≤ liminf q l := by
  have hbd : IsCoboundedUnder (· ≥ ·) l q :=
    (isBoundedUnder_of_eventually_le hB).isCoboundedUnder_ge
  refine le_of_forall_pos_sub_le fun η hη => ?_
  exact le_liminf_of_le hbd (h η hη)
theorem liminf_finset_prod_le_prod_limsup {ι α : Type*} {l : Filter ι} [l.NeBot] (O : Finset α)
    (f : α → ι → ℝ) (B : α → ℝ) (h0 : ∀ a ∈ O, ∀ᶠ k in l, 0 ≤ f a k)
    (hB : ∀ a ∈ O, ∀ᶠ k in l, f a k ≤ B a) :
    liminf (fun k => ∏ a ∈ O, f a k) l ≤ ∏ a ∈ O, limsup (f a) l := by
  have hprod0 : ∀ᶠ k in l, 0 ≤ ∏ a ∈ O, f a k := by
    filter_upwards [(Filter.eventually_all_finset O).2 h0] with k hk
    exact Finset.prod_nonneg hk
  have hstep : ∀ η : ℝ, 0 < η →
      liminf (fun k => ∏ a ∈ O, f a k) l ≤ ∏ a ∈ O, (limsup (f a) l + η) := by
    intro η hη
    have hlt : ∀ a ∈ O, ∀ᶠ k in l, f a k ≤ limsup (f a) l + η := fun a ha =>
      (eventually_lt_of_limsup_lt (by linarith)
        (isBoundedUnder_of_eventually_le (hB a ha))).mono fun k hk => hk.le
    have hev : ∀ᶠ k in l, ∏ a ∈ O, f a k ≤ ∏ a ∈ O, (limsup (f a) l + η) := by
      filter_upwards [(Filter.eventually_all_finset O).2 h0,
        (Filter.eventually_all_finset O).2 hlt] with k hk hk'
      exact Finset.prod_le_prod hk hk'
    exact liminf_le_of_frequently_le hev.frequently (isBoundedUnder_of_eventually_ge hprod0)
  have hcont : Tendsto (fun η : ℝ => ∏ a ∈ O, (limsup (f a) l + η)) (𝓝[>] 0)
      (𝓝 (∏ a ∈ O, limsup (f a) l)) := by
    have hc : Continuous fun η : ℝ => ∏ a ∈ O, (limsup (f a) l + η) := by fun_prop
    have := hc.tendsto 0
    simp only [add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hcont (eventually_nhdsWithin_of_forall fun η hη => hstep η hη)
theorem finprod_eq_fintype_prod_of_injective {α β M : Type*} [CommMonoid M] [Fintype α]
    (i : α → β) (hi : Function.Injective i) (e : β → M) (f : α → M) (h1 : ∀ a, e (i a) = f a)
    (h2 : ∀ b, b ∉ range i → e b = 1) : ∏ᶠ b, e b = ∏ a, f a := by
  classical
  have hsub : Function.mulSupport e ⊆ ((Finset.univ.image i : Finset β) : Set β) := by
    intro b hb
    by_contra hbn
    refine hb (h2 b fun ⟨a, ha⟩ => hbn ?_)
    simp [← ha]
  rw [finprod_eq_prod_of_mulSupport_subset e hsub, Finset.prod_image fun a _ a' _ h => hi h]
  exact Finset.prod_congr rfl fun a _ => h1 a
theorem sub_two_mul_sq_le_log_one_add {y : ℝ} (hy : |y| ≤ 1 / 2) :
    y - 2 * y ^ 2 ≤ Real.log (1 + y) := by
  have hlt : |(-y)| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hlt 1
  simp only [Finset.range_one, Finset.sum_singleton, zero_add, pow_one, Nat.cast_zero, div_one,
    sub_neg_eq_add, abs_neg] at h
  have h2 : |y| ^ (1 + 1) / (1 - |y|) ≤ 2 * y ^ 2 := by
    rw [div_le_iff₀ (by linarith)]
    have : |y| ^ (1 + 1) = y ^ 2 := by simp
    rw [this]
    nlinarith [sq_nonneg y]
  have h3 := (abs_le.mp (h.trans h2)).1
  linarith
theorem abs_log_le_one_of_mem_Icc {t : ℝ} (h1 : 1 / 2 ≤ t) (h2 : t ≤ 3 / 2) :
    |Real.log t| ≤ 1 := by
  have ht : 0 < t := by linarith
  have hu := Real.log_le_sub_one_of_pos ht
  have hl := Real.one_sub_inv_le_log_of_pos ht
  have hinv : t⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ ht (by norm_num)]
    linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩
section CellAlgebra
variable {D : GridSetup} {S : Set InfiniteLattice.AmbientSpace}
theorem measurable_of_mem_cellObservables {F : D.GaugeField → ℂ}
    (hF : F ∈ ReflectionGrid.cellObservables (D := D) S) : Measurable F := by
  obtain ⟨f, hf, -, rfl⟩ := hF
  refine hf.comp (measurable_pi_iff.mpr fun b => ?_)
  have h : Continuous fun U : D.GaugeField => U b.1 :=
    (continuous_apply b.1).comp continuous_subtype_val
  exact h.measurable
theorem const_one_mem_cellObservables :
    (fun _ => 1 : D.GaugeField → ℂ) ∈ ReflectionGrid.cellObservables (D := D) S := by apply _root_.YangMills.Construction.ChessboardTori.ChessboardEstimateAndSubadditivity.one_mem_cellObservables <;> assumption
theorem mul_mem_cellObservables {F F' : D.GaugeField → ℂ}
    (hF : F ∈ ReflectionGrid.cellObservables (D := D) S)
    (hF' : F' ∈ ReflectionGrid.cellObservables (D := D) S) :
    (fun U => F U * F' U) ∈ ReflectionGrid.cellObservables (D := D) S := by
  obtain ⟨f, hf, ⟨C, hC⟩, rfl⟩ := hF
  obtain ⟨f', hf', ⟨C', hC'⟩, rfl⟩ := hF'
  refine ⟨fun u => f u * f' u, hf.mul hf', ⟨C * C', fun u => ?_⟩, rfl⟩
  rw [norm_mul]
  exact mul_le_mul (hC u) (hC' u) (norm_nonneg _) ((norm_nonneg _).trans (hC u))
theorem prod_mem_cellObservables {ι : Type*} (O : Finset ι) (F : ι → D.GaugeField → ℂ)
    (hF : ∀ i ∈ O, F i ∈ ReflectionGrid.cellObservables (D := D) S) :
    (fun U => ∏ i ∈ O, F i U) ∈ ReflectionGrid.cellObservables (D := D) S := by
  classical
  induction O using Finset.induction_on with
  | empty => simpa using const_one_mem_cellObservables
  | insert i O hi ih =>
    simp only [Finset.prod_insert hi]
    exact mul_mem_cellObservables (hF i (Finset.mem_insert_self _ _))
      (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))
theorem exists_bound_log_one_add_mem {F : D.GaugeField → ℂ}
    (hF : F ∈ ReflectionGrid.cellObservables (D := D) S) :
    ∃ C : ℝ, 0 < C ∧ (∀ U, ‖F U‖ ≤ C) ∧ ∀ (c : ℂ) (ε : ℝ), ‖c‖ = 1 → 0 < ε → ε * C ≤ 1 / 2 →
      (fun U => ((Real.log (1 + ε * (c * F U).re) : ℝ) : ℂ)) ∈
        ReflectionGrid.cellObservables (D := D) S := by
  obtain ⟨f, hf, ⟨C₀, hC₀⟩, rfl⟩ := hF
  refine ⟨max C₀ 1, lt_max_of_lt_right one_pos,
    fun U => (hC₀ _).trans (le_max_left _ _), fun c ε hc hε hεC => ?_⟩
  have hbound : ∀ u, |ε * (c * f u).re| ≤ 1 / 2 := fun u => by
    have h1 : |(c * f u).re| ≤ max C₀ 1 :=
      (Complex.abs_re_le_norm _).trans (by
        rw [norm_mul, hc, one_mul]
        exact (hC₀ u).trans (le_max_left _ _))
    rw [abs_mul, abs_of_pos hε]
    exact (mul_le_mul_of_nonneg_left h1 hε.le).trans hεC
  refine ⟨fun u => ((Real.log (1 + ε * (c * f u).re) : ℝ) : ℂ), ?_, ⟨1, fun u => ?_⟩, rfl⟩
  · have hm : Measurable fun u => (c * f u).re :=
      Complex.measurable_re.comp (hf.const_mul c)
    exact Complex.measurable_ofReal.comp
      (Real.measurable_log.comp ((hm.const_mul ε).const_add 1))
  · obtain ⟨h1, h2⟩ := abs_le.mp (hbound u)
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_log_le_one_of_mem_Icc (by linarith) (by linarith)
end CellAlgebra
section Torus
variable {D : GridSetup}
theorem cellSide_pos (g : ReflectionGrid D) : 0 < g.cellSide :=
  zpow_pos (by linarith [D.one_lt_factor]) _
theorem two_mul_cellSide_le_of_coarsening {g g' : ReflectionGrid D} (hco : g'.IsCoarsening g)
    (h2 : 2 * g'.cellSide ≤ PeriodicLattice.torusSide D.L D.m) :
    2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m := by
  obtain ⟨⟨k₀, hk⟩, -⟩ := hco
  have hL : (1 : ℝ) ≤ (D.L : ℝ) ^ k₀ := one_le_pow₀ D.one_lt_factor.le
  have hs := cellSide_pos g
  nlinarith
theorem chessboardNormOfCell_nonneg (g : ReflectionGrid D) (S : Set InfiniteLattice.AmbientSpace)
    (F : D.GaugeField → ℂ) : 0 ≤ g.chessboardNormOfCell S F :=
  Real.rpow_nonneg (norm_nonneg _) _
theorem chessboardNormOfCell_le_of_bound (hC : chessboardEstimate_allSides)
    (hG : ReflectionGridProperties) (g : ReflectionGrid D) (hg : g.HasAdmissibleSide)
    (h2 : 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m)
    {S : Set InfiniteLattice.AmbientSpace} (hS : S ∈ g.cellSet) {F : D.GaugeField → ℂ}
    (hF : F ∈ ReflectionGrid.cellObservables (D := D) S)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ U, ‖F U‖ ≤ B) : g.chessboardNormOfCell S F ≤ B := by
  obtain ⟨-, hii, -⟩ := hC D g hg h2
  obtain ⟨-, -, -, -, -, -, htor, -, -⟩ := hG D g hg
  obtain ⟨-, -, -, -, -, hread, -⟩ := htor h2
  have hmem := (hread S hS F hF).1
  have hcell : D.proj '' S ∈ g.torusCellSet := ⟨S, hS, rfl⟩
  exact ((hii _ hcell).1 _ hmem).2.2.1.trans (Real.iSup_le (fun U => hB _) hB0)
theorem chessboardNorm_one_add_re_le (hC : chessboardEstimate_allSides)
    (hG : ReflectionGridProperties) {g g' : ReflectionGrid D} (hg : g.HasAdmissibleSide)
    (hg' : g'.HasAdmissibleSide) (hco : g'.IsCoarsening g)
    (h2 : 2 * g'.cellSide ≤ PeriodicLattice.torusSide D.L D.m)
    {S' : Set InfiniteLattice.AmbientSpace}
    (hS' : S' ∈ g'.cellSet) (O : Finset g.cellSet) (hsub : ∀ S ∈ O, S.1 ⊆ S')
    (F : g.cellSet → D.GaugeField → ℂ)
    (hF : ∀ S, F S ∈ ReflectionGrid.cellObservables (D := D) S.1)
    {c : ℂ} (hc : ‖c‖ = 1) {ε : ℝ} (hε : 0 < ε) :
    g'.chessboardNormOfCell S'
        (fun U => ((1 + ε * (c * ∏ S ∈ O, F S U).re : ℝ) : ℂ)) ≤
      1 + ε * ∏ S ∈ O, g.chessboardNormOfCell S.1 (F S) := by
  have h2g := two_mul_cellSide_le_of_coarsening hco h2
  obtain ⟨-, -, -, -, -, -, htor', -, -⟩ := hG D g' hg'
  obtain ⟨hcells', -, -, -, -, -, -⟩ := htor' h2
  obtain ⟨-, -, -, -, -, -, htor, -, -⟩ := hG D g hg
  obtain ⟨-, -, -, -, -, hread, -⟩ := htor h2g
  obtain ⟨-, hii', -⟩ := hC D g' hg' h2
  obtain ⟨-, hii, hiii⟩ := hC D g hg h2g
  obtain ⟨kS, rfl⟩ := hS'
  have hQ : D.proj '' g'.cell kS ∈ g'.torusCellSet := ⟨_, ⟨kS, rfl⟩, rfl⟩
  have hinj : InjOn D.proj (g'.cell kS) := hcells'.2.1 kS
  let i : O → {C : Set D.Torus // C ∈ g.torusCellSet ∧ C ⊆ D.proj '' g'.cell kS} :=
    fun S => ⟨D.proj '' S.1.1, ⟨S.1.1, S.1.2, rfl⟩, image_mono (hsub S.1 S.2)⟩
  have hi : Function.Injective i := by
    intro S T hST
    have h : D.proj '' S.1.1 = D.proj '' T.1.1 := congrArg Subtype.val hST
    have h' : S.1.1 = T.1.1 := (hinj.image_eq_image_iff (hsub _ S.2) (hsub _ T.2)).mp h
    exact Subtype.ext (Subtype.ext h')
  let f : O → (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ :=
    fun S => D.liftedObservable (F S.1)
  let F' : {C : Set D.Torus // C ∈ g.torusCellSet ∧ C ⊆ D.proj '' g'.cell kS} →
      (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ := Function.extend i f fun _ _ => 1
  have hF'i : ∀ S, F' (i S) = f S := fun S => hi.extend_apply _ _ S
  have hF'n : ∀ C, C ∉ range i → F' C = fun _ => 1 := fun C hC' =>
    Function.extend_apply' _ _ _ hC'
  have hF'mem : ∀ C, F' C ∈ g.torusCellObservables C.1 := by
    intro C
    by_cases h : C ∈ range i
    · obtain ⟨S, rfl⟩ := h
      rw [hF'i]
      exact (hread S.1.1 S.1.2 _ (hF S.1)).1
    · rw [hF'n C h]
      exact (hii C.1 C.2.1).2.1
  obtain ⟨hFlmem, hFlle⟩ := hiii g' hco h2 _ hQ F' hF'mem
  have hprod : (fun U => ∏ᶠ C, F' C U) =
      D.liftedObservable (fun U => ∏ S ∈ O, F S U) := by
    funext U
    rw [finprod_eq_fintype_prod_of_injective i hi (fun C => F' C U) (fun S => f S U)
      (fun S => by simp only [hF'i]) (fun C hC' => by simp only [hF'n C hC'])]
    exact O.prod_coe_sort fun S => F S (D.liftField U)
  have hfun : ∏ᶠ C, g.cellChessboardSeminorm C.1 (F' C) =
      ∏ S ∈ O, g.chessboardNormOfCell S.1 (F S) := by
    rw [finprod_eq_fintype_prod_of_injective i hi
      (fun C => g.cellChessboardSeminorm C.1 (F' C))
      (fun S => g.chessboardNormOfCell S.1.1 (F S.1))
      (fun S => by simp only [hF'i]; rfl)
      (fun C hC' => by simp only [hF'n C hC']; exact (hii C.1 C.2.1).2.2)]
    exact O.prod_coe_sort fun S => g.chessboardNormOfCell S.1 (F S)
  rw [hprod] at hFlmem hFlle
  rw [hfun] at hFlle
  set Fl : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ :=
    D.liftedObservable (fun U => ∏ S ∈ O, F S U) with hFl
  set Q : Set D.Torus := D.proj '' g'.cell kS with hQdef
  have hreading : D.liftedObservable (fun U => ((1 + ε * (c * ∏ S ∈ O, F S U).re : ℝ) : ℂ)) =
      (fun _ => 1) + (((ε / 2 : ℝ) * c : ℂ) • Fl +
        ((ε / 2 : ℝ) * conj c : ℂ) • conjFun Fl) := by
    funext U
    have hz : Fl U = ∏ S ∈ O, F S (D.liftField U) := rfl
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, conjFun, hz]
    change ((1 + ε * (c * ∏ S ∈ O, F S (D.liftField U)).re : ℝ) : ℂ) = _
    generalize (∏ S ∈ O, F S (D.liftField U)) = w
    have hre : (((c * w).re : ℝ) : ℂ) * 2 = c * w + conj c * conj w := by
      rw [← map_mul, Complex.add_conj]
      push_cast
      ring
    push_cast
    linear_combination ((ε : ℂ) / 2) * hre
  have hzn : ‖((ε / 2 : ℝ) * c : ℂ)‖ = ε / 2 := by
    rw [norm_mul, hc, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hzn' : ‖((ε / 2 : ℝ) * conj c : ℂ)‖ = ε / 2 := by
    rw [norm_mul, Complex.norm_conj, hc, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
  obtain ⟨hone, hone1⟩ := (hii' Q hQ).2
  obtain ⟨-, hsm, -, hconj, hconj1, -⟩ := (hii' Q hQ).1 Fl hFlmem
  obtain ⟨hsm1, hsm1e⟩ := hsm ((ε / 2 : ℝ) * c : ℂ)
  obtain ⟨-, hsm', -, -, -, -⟩ := (hii' Q hQ).1 _ hconj
  obtain ⟨hsm2, hsm2e⟩ := hsm' ((ε / 2 : ℝ) * conj c : ℂ)
  obtain ⟨hadd, -⟩ := (hii' Q hQ).1 _ hsm1
  obtain ⟨hsum, hsumle⟩ := hadd _ hsm2
  obtain ⟨hadd1, -⟩ := (hii' Q hQ).1 _ hone
  obtain ⟨-, htotle⟩ := hadd1 _ hsum
  have hmain : g'.cellChessboardSeminorm Q
      ((fun _ => 1) + (((ε / 2 : ℝ) * c : ℂ) • Fl +
        ((ε / 2 : ℝ) * conj c : ℂ) • conjFun Fl)) ≤
      1 + ε * g'.cellChessboardSeminorm Q Fl := by
    refine htotle.trans ?_
    rw [hone1]
    have : g'.cellChessboardSeminorm Q (((ε / 2 : ℝ) * c : ℂ) • Fl +
        ((ε / 2 : ℝ) * conj c : ℂ) • conjFun Fl) ≤
        ε * g'.cellChessboardSeminorm Q Fl := by
      refine hsumle.trans ?_
      rw [hsm1e, hsm2e, hconj1, hzn, hzn']
      linarith
    linarith
  change g'.cellChessboardSeminorm Q _ ≤ _
  rw [hreading]
  refine hmain.trans ?_
  have := mul_le_mul_of_nonneg_left hFlle hε.le
  linarith
end Torus
theorem integral_log_one_add_re_ge {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    [IsProbabilityMeasure ν]
    {G : Ω → ℂ} (hm : Measurable G) {C : ℝ} (hC : ∀ U, ‖G U‖ ≤ C) {c : ℂ} (hc : ‖c‖ = 1)
    {ε : ℝ} (hε : 0 < ε) (hεC : ε * C ≤ 1 / 2)
    (hcz : c * ∫ U, G U ∂ν = (‖∫ U, G U ∂ν‖ : ℝ)) :
    ε * ‖∫ U, G U ∂ν‖ - 2 * ε ^ 2 * C ^ 2 ≤ ∫ U, Real.log (1 + ε * (c * G U).re) ∂ν := by
  have hint : Integrable G ν :=
    Integrable.of_bound hm.aestronglyMeasurable C (Eventually.of_forall hC)
  have hintc : Integrable (fun U => c * G U) ν := hint.const_mul c
  have hu : ∫ U, (c * G U).re ∂ν = ‖∫ U, G U ∂ν‖ := by
    have h := Complex.reCLM.integral_comp_comm hintc
    simp only [Complex.reCLM_apply] at h
    rw [h, integral_const_mul, hcz, Complex.ofReal_re]
  have hure : Integrable (fun U => (c * G U).re) ν := Complex.reCLM.integrable_comp hintc
  have hy : ∀ U, |ε * (c * G U).re| ≤ 1 / 2 := fun U => by
    have h1 : |(c * G U).re| ≤ C := (Complex.abs_re_le_norm _).trans (by
      rw [norm_mul, hc, one_mul]
      exact hC U)
    rw [abs_mul, abs_of_pos hε]
    exact (mul_le_mul_of_nonneg_left h1 hε.le).trans hεC
  have hlogm : Measurable fun U => Real.log (1 + ε * (c * G U).re) :=
    Real.measurable_log.comp
      (((Complex.measurable_re.comp (hm.const_mul c)).const_mul ε).const_add 1)
  have hlogi : Integrable (fun U => Real.log (1 + ε * (c * G U).re)) ν := by
    refine Integrable.of_bound hlogm.aestronglyMeasurable 1 (Eventually.of_forall fun U => ?_)
    obtain ⟨h1, h2⟩ := abs_le.mp (hy U)
    rw [Real.norm_eq_abs]
    exact abs_log_le_one_of_mem_Icc (by linarith) (by linarith)
  have hlin : Integrable (fun U => ε * (c * G U).re - 2 * ε ^ 2 * C ^ 2) ν :=
    (hure.const_mul ε).sub (integrable_const _)
  have hval : ∫ U, (ε * (c * G U).re - 2 * ε ^ 2 * C ^ 2) ∂ν =
      ε * ‖∫ U, G U ∂ν‖ - 2 * ε ^ 2 * C ^ 2 := by
    rw [integral_sub (hure.const_mul ε) (integrable_const _), integral_const_mul, hu,
      integral_const]
    simp
  rw [← hval]
  refine integral_mono hlin hlogi fun U => ?_
  have h1 := sub_two_mul_sq_le_log_one_add (hy U)
  have h2 : (ε * (c * G U).re) ^ 2 ≤ ε ^ 2 * C ^ 2 := by
    have h3 : |(c * G U).re| ≤ C := (Complex.abs_re_le_norm _).trans (by
      rw [norm_mul, hc, one_mul]
      exact hC U)
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left (sq_le_sq' (by linarith [(abs_le.mp h3).1])
      (abs_le.mp h3).2) (sq_nonneg ε)
  show ε * (c * G U).re - 2 * ε ^ 2 * C ^ 2 ≤ Real.log (1 + ε * (c * G U).re)
  linarith
end ChessboardDomination
theorem ChessboardDomination.holds
    (hC : chessboardEstimate_allSides)
    (hG : ReflectionGridProperties)
    (hJ : JensenBoundFromPeriods.Statement) :
    ChessboardDomination.Statement := by
  intro D ν hν g hg m hm F hFalg hF
  set O := hF.toFinset with hO
  obtain ⟨-, -, -, -, -, -, -, hcoarse, hfin⟩ := hG D g hg
  obtain ⟨g', hg', hco, S', hS', hsub⟩ := hfin (Subtype.val '' (O : Set g.cellSet))
    (O.finite_toSet.image _) (by rintro _ ⟨S, -, rfl⟩; exact S.2)
  obtain ⟨k₀, hk₀⟩ := hco.1
  have hsub' : ∀ S ∈ O, S.1 ⊆ S' := fun S hS => hsub _ ⟨S, hS, rfl⟩
  have hin : ∀ S ∈ O, F S ∈ ReflectionGrid.cellObservables (D := D) S' := fun S hS =>
    ((hcoarse g' k₀ hco hk₀).1.1 S' hS').2.2 S.1 S.2 (hsub' S hS) (hFalg S)
  have hFF := ChessboardDomination.prod_mem_cellObservables O F hin
  obtain ⟨C, hCpos, hCb, hlog⟩ := ChessboardDomination.exists_bound_log_one_add_mem hFF
  obtain ⟨p, hp⟩ := (hJ D).1 ν hν
  have : IsProbabilityMeasure ν := hp.1
  have hGibbs : InfiniteLattice.IsGibbs D.β ν :=
    (show InfiniteLattice.IsPeriodicGibbs D.β ν from hν).1
  have hBd : ∀ S, ∃ B : ℝ, 0 ≤ B ∧ ∀ U, ‖F S U‖ ≤ B := fun S => by
    obtain ⟨B, hB, hB', -⟩ := ChessboardDomination.exists_bound_log_one_add_mem (hFalg S)
    exact ⟨B, hB.le, hB'⟩
  choose Bd hBd0 hBdb using hBd
  have hlarge : ∀ᶠ k in atTop, 2 * g'.cellSide ≤ PeriodicLattice.torusSide D.L (m k) :=
    hm.eventually_ge_atTop _
  have h0 : ∀ S ∈ O, ∀ᶠ k in atTop,
      0 ≤ (g.withExponent (m k)).chessboardNormOfCell S.1 (F S) := fun S _ =>
    Eventually.of_forall fun k => ChessboardDomination.chessboardNormOfCell_nonneg _ _ _
  have hB : ∀ S ∈ O, ∀ᶠ k in atTop,
      (g.withExponent (m k)).chessboardNormOfCell S.1 (F S) ≤ Bd S := fun S _ => by
    filter_upwards [hlarge] with k hk
    exact ChessboardDomination.chessboardNormOfCell_le_of_bound hC hG (g.withExponent (m k)) hg
      (ChessboardDomination.two_mul_cellSide_le_of_coarsening (D := D.withExponent (m k))
        (g := g.withExponent (m k)) (g' := g'.withExponent (m k)) hco hk)
      S.2 (hFalg S) (hBd0 S) (hBdb S)
  refine ⟨?_, ChessboardDomination.liminf_finset_prod_le_prod_limsup O _ Bd h0 hB⟩
  have hq0 : ∀ k, 0 ≤ ∏ S ∈ O, (g.withExponent (m k)).chessboardNormOfCell S.1 (F S) :=
    fun k => Finset.prod_nonneg fun S _ =>
      ChessboardDomination.chessboardNormOfCell_nonneg _ _ _
  have hub : ∀ᶠ k in atTop,
      ∏ S ∈ O, (g.withExponent (m k)).chessboardNormOfCell S.1 (F S) ≤ ∏ S ∈ O, Bd S := by
    filter_upwards [(Filter.eventually_all_finset O).2 hB] with k hk
    exact Finset.prod_le_prod
      (fun S _ => ChessboardDomination.chessboardNormOfCell_nonneg _ _ _) hk
  set z : ℂ := ∫ U, (∏ S ∈ O, F S U) ∂ν with hz
  set c : ℂ := Complex.exp (((-Complex.arg z : ℝ) : ℂ) * Complex.I) with hcdef
  have hc : ‖c‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hcz : c * z = (‖z‖ : ℝ) := by
    have h := Complex.norm_mul_exp_arg_mul_I z
    have h1 : c * Complex.exp ((Complex.arg z : ℂ) * Complex.I) = 1 := by
      rw [hcdef, ← Complex.exp_add]
      push_cast
      simp
    calc c * z = c * ((‖z‖ : ℂ) * Complex.exp ((Complex.arg z : ℂ) * Complex.I)) := by rw [h]
      _ = (‖z‖ : ℂ) * (c * Complex.exp ((Complex.arg z : ℂ) * Complex.I)) := by ring
      _ = (‖z‖ : ℝ) := by rw [h1, mul_one]
  set K₀ : ℝ := cubeComparisonConstant * (2 * (p : ℝ)) ^ 4 * D.β *
    (g'.cellSide / D.mesh) ^ 3 with hK₀
  have hstep : ∀ ε : ℝ, 0 < ε → ε * C ≤ 1 / 2 → ∀ᶠ k in atTop,
      ε * ‖z‖ - 2 * ε ^ 2 * C ^ 2 ≤
        ε * (∏ S ∈ O, (g.withExponent (m k)).chessboardNormOfCell S.1 (F S)) +
          K₀ * (g'.cellSide / PeriodicLattice.torusSide D.L (m k)) := by
    intro ε hε hεC
    have hlow := ChessboardDomination.integral_log_one_add_re_ge ν
      (ChessboardDomination.measurable_of_mem_cellObservables hFF) hCb hc hε hεC hcz
    filter_upwards [hlarge] with k hk
    have hJk : ∫ U, Real.log (1 + ε * (c * ∏ S ∈ O, F S U).re) ∂ν ≤
        Real.log ((g'.withExponent (m k)).chessboardNormOfCell S'
          fun U => (Real.exp (Real.log (1 + ε * (c * ∏ S ∈ O, F S U).re)) : ℂ)) +
          cubeComparisonConstant * (2 * (p : ℝ)) ^ 4 * D.β * (g'.cellSide / D.mesh) ^ 3 *
            (g'.cellSide / PeriodicLattice.torusSide D.L (m k)) :=
      (hJ (D.withExponent (m k))).2 ν p hGibbs hp (g'.withExponent (m k)) hg' S' hS' _
        (hlog c ε hc hε hεC) hk
    have hexp : (fun U => ((Real.exp (Real.log (1 + ε * (c * ∏ S ∈ O, F S U).re)) : ℝ) : ℂ)) =
        fun U => ((1 + ε * (c * ∏ S ∈ O, F S U).re : ℝ) : ℂ) := by
      funext U
      have h1 : |(c * ∏ S ∈ O, F S U).re| ≤ C := (Complex.abs_re_le_norm _).trans (by
        rw [norm_mul, hc, one_mul]
        exact hCb U)
      have h2 : |ε * (c * ∏ S ∈ O, F S U).re| ≤ 1 / 2 := by
        rw [abs_mul, abs_of_pos hε]
        exact (mul_le_mul_of_nonneg_left h1 hε.le).trans hεC
      rw [Real.exp_log (by linarith [(abs_le.mp h2).1])]
    have hch := ChessboardDomination.chessboardNorm_one_add_re_le (D := D.withExponent (m k))
      (g := g.withExponent (m k)) (g' := g'.withExponent (m k)) hC hG hg hg' hco hk hS' O hsub'
      F hFalg hc hε
    have hch' : ((g'.withExponent (m k)).chessboardNormOfCell S'
        fun U => (Real.exp (Real.log (1 + ε * (c * ∏ S ∈ O, F S U).re)) : ℂ)) ≤
        1 + ε * ∏ S ∈ O, (g.withExponent (m k)).chessboardNormOfCell S.1 (F S) :=
      (congrArg ((g'.withExponent (m k)).chessboardNormOfCell S') hexp).le.trans hch
    have hlogle : Real.log ((g'.withExponent (m k)).chessboardNormOfCell S'
        fun U => (Real.exp (Real.log (1 + ε * (c * ∏ S ∈ O, F S U).re)) : ℂ)) ≤
        ε * ∏ S ∈ O, (g.withExponent (m k)).chessboardNormOfCell S.1 (F S) := by
      rcases (ChessboardDomination.chessboardNormOfCell_nonneg (g'.withExponent (m k)) S'
        fun U => (Real.exp (Real.log (1 + ε * (c * ∏ S ∈ O, F S U).re)) : ℂ)).eq_or_lt
        with h | h
      · rw [← h, Real.log_zero]
        exact mul_nonneg hε.le (hq0 k)
      · have := Real.log_le_sub_one_of_pos h
        linarith
    linarith
  have hTz : Tendsto (fun k => K₀ * (g'.cellSide / PeriodicLattice.torusSide D.L (m k))) atTop
      (𝓝 0) := by
    have h := (tendsto_const_nhds (x := g'.cellSide)).div_atTop hm
    simpa using h.const_mul K₀
  refine ChessboardDomination.le_liminf_of_forall_sub_eventually hub fun η hη => ?_
  obtain ⟨ε, hε, hεC, hεη⟩ : ∃ ε : ℝ, 0 < ε ∧ ε * C ≤ 1 / 2 ∧ 2 * ε * C ^ 2 ≤ η / 2 := by
    refine ⟨min (1 / (2 * C)) (η / (4 * C ^ 2)), by positivity, ?_, ?_⟩
    · calc min (1 / (2 * C)) (η / (4 * C ^ 2)) * C ≤ 1 / (2 * C) * C :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) hCpos.le
        _ = 1 / 2 := by field_simp
    · calc 2 * min (1 / (2 * C)) (η / (4 * C ^ 2)) * C ^ 2 ≤ 2 * (η / (4 * C ^ 2)) * C ^ 2 := by
            gcongr
            exact min_le_right _ _
        _ = η / 2 := by field_simp; ring
  have hTsmall : ∀ᶠ k in atTop,
      K₀ * (g'.cellSide / PeriodicLattice.torusSide D.L (m k)) < ε * η / 2 :=
    hTz.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hstep ε hε hεC, hTsmall] with k hk hk'
  have h3 : 2 * ε ^ 2 * C ^ 2 ≤ ε * (η / 2) := by
    have := mul_le_mul_of_nonneg_left hεη hε.le
    nlinarith
  have h4 : ε * (‖D.integralOf ν fun U => ∏ S ∈ O, F S U‖ - η) ≤
      ε * ∏ S ∈ O, (g.withExponent (m k)).chessboardNormOfCell S.1 (F S) := by
    have : D.integralOf ν (fun U => ∏ S ∈ O, F S U) = z := rfl
    rw [this]
    nlinarith
  exact le_of_mul_le_mul_left h4 hε
end YangMills.Construction.MirrorGridsAllSides
end
