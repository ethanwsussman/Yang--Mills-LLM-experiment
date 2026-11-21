import YangMills.Construction.TorusOrFourSpace.FormsOfACutOffOnThePeriodBoxProof
import YangMills.Construction.TorusOrFourSpace.CoefficientsOfTestFunctionsOnThePeriodBoxProof
import YangMills.Construction.TorusOrFourSpace.FourierSeriesOfATestFunctionConverges
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped ComplexConjugate Topology
noncomputable section
namespace YangMills.Construction.PeriodicSpace.FourierSeriesConvergence
variable {n : ℕ}
def planeWave (P : ℝ) (k : Fin n → ℤ) (u : Fin n → ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((∑ j, (k j : ℝ) * u j : ℝ) : ℂ) / (P : ℂ))
def toUnitTorus (x : Fin n → ℝ) : UnitAddTorus (Fin n) := fun i => (x i : UnitAddCircle)
def torusRep (z : UnitAddTorus (Fin n)) : Fin n → ℝ :=
  fun i => (AddCircle.equivIoc (1 : ℝ) (-1 / 2) (z i) : ℝ)
theorem continuous_toUnitTorus : Continuous (toUnitTorus (n := n)) :=
  continuous_pi fun i => (AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_apply i)
theorem torusRep_toUnitTorus (x : Fin n → ℝ)
    (hx : ∀ i, x i ∈ Ioc (-1 / 2 : ℝ) (-1 / 2 + 1)) : torusRep (toUnitTorus x) = x :=
  funext fun i => AddCircle.equivIoc_coe_of_mem (p := (1 : ℝ)) (a := -1 / 2) (hx i)
theorem toUnitTorus_torusRep (z : UnitAddTorus (Fin n)) : toUnitTorus (torusRep z) = z :=
  funext fun _ => AddCircle.coe_equivIoc (p := (1 : ℝ)) (a := -1 / 2)
theorem mFourier_toUnitTorus {P : ℝ} (hP : P ≠ 0) (k : Fin n → ℤ) (x : Fin n → ℝ) :
    UnitAddTorus.mFourier k (toUnitTorus x) = planeWave P k (P • x) := by
  have hP' : (P : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hP
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, toUnitTorus, fourier_coe_apply, planeWave,
    Pi.smul_apply, smul_eq_mul]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp
theorem continuous_comp_torusRep (φ : (Fin n → ℝ) → ℂ) (hφ : Continuous φ)
    (C : Set (Fin n → ℝ)) (hC : IsCompact C)
    (hCb : ∀ x ∈ C, ∀ i, x i ∈ Ioo (-1 / 2 : ℝ) (1 / 2)) (h0 : ∀ x, x ∉ C → φ x = 0) :
    Continuous fun z : UnitAddTorus (Fin n) => φ (torusRep z) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : ∀ i, z i ≠ ((-1 / 2 : ℝ) : UnitAddCircle)
  · refine ContinuousAt.comp (g := φ) hφ.continuousAt ?_
    refine continuousAt_pi.2 fun i => ?_
    exact continuous_subtype_val.continuousAt.comp
      (ContinuousAt.comp (AddCircle.continuousAt_equivIoc (1 : ℝ) (-1 / 2) (hz i))
        (continuous_apply i).continuousAt)
  · simp only [not_forall, not_not] at hz
    obtain ⟨i, hi⟩ := hz
    have hclosed : IsClosed (toUnitTorus '' C) := (hC.image continuous_toUnitTorus).isClosed
    have hzn : z ∉ toUnitTorus '' C := by
      rintro ⟨x, hx, rfl⟩
      have hxi := hCb x hx i
      have hmem : x i ∈ Ico (-1 / 2 : ℝ) (-1 / 2 + 1) :=
        ⟨hxi.1.le, by have := hxi.2; linarith⟩
      have hmem' : (-1 / 2 : ℝ) ∈ Ico (-1 / 2 : ℝ) (-1 / 2 + 1) := ⟨le_rfl, by norm_num⟩
      have := (AddCircle.coe_eq_coe_iff_of_mem_Ico hmem hmem').1 hi
      have h1 := hxi.1
      linarith
    have hev : (fun z : UnitAddTorus (Fin n) => φ (torusRep z)) =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [hclosed.isOpen_compl.mem_nhds hzn] with w hw
      refine h0 _ fun hmem => hw ⟨_, hmem, toUnitTorus_torusRep w⟩
    exact continuousAt_const.congr hev.symm
theorem hasSum_planeWave_of_summable {P : ℝ} (hP : 0 < P) (h : (Fin n → ℝ) → ℂ) (hc : Continuous h)
    (K : Set (Fin n → ℝ)) (hK : IsCompact K)
    (hKb : ∀ u ∈ K, ∀ j, u j ∈ Ioo (-P / 2) (P / 2)) (h0 : ∀ u, u ∉ K → h u = 0)
    (c : (Fin n → ℤ) → ℂ)
    (hcoef : ∀ k, c k = ((P : ℂ) ^ n)⁻¹ *
      ∫ u in {u : Fin n → ℝ | ∀ j, u j ∈ Ioo (-P / 2) (P / 2)}, h u * conj (planeWave P k u))
    (hs : Summable c) (u : Fin n → ℝ) (hu : ∀ j, u j ∈ Ioo (-P / 2) (P / 2)) :
    HasSum (fun k => c k * planeWave P k u) (h u) := by
  have hP0 : P ≠ 0 := hP.ne'
  set φ : (Fin n → ℝ) → ℂ := fun x => h (P • x) with hφdef
  have hφ : Continuous φ := hc.comp (continuous_const_smul P)
  set C : Set (Fin n → ℝ) := (fun w => P⁻¹ • w) '' K with hCdef
  have hC : IsCompact C := hK.image (continuous_const_smul P⁻¹)
  have hbox : ∀ x : Fin n → ℝ, (∀ j, (P • x) j ∈ Ioo (-P / 2) (P / 2)) →
      ∀ i, x i ∈ Ioo (-1 / 2 : ℝ) (1 / 2) := by
    intro x hx i
    have h1 := (hx i).1
    have h2 := (hx i).2
    simp only [Pi.smul_apply, smul_eq_mul] at h1 h2
    constructor
    · by_contra hcon
      have : x i ≤ -1 / 2 := not_lt.1 hcon
      nlinarith
    · by_contra hcon
      have : 1 / 2 ≤ x i := not_lt.1 hcon
      nlinarith
  have hCb : ∀ x ∈ C, ∀ i, x i ∈ Ioo (-1 / 2 : ℝ) (1 / 2) := by
    rintro x ⟨w, hw, rfl⟩
    refine hbox _ ?_
    rw [smul_smul, mul_inv_cancel₀ hP0, one_smul]
    exact hKb w hw
  have hφ0 : ∀ x, x ∉ C → φ x = 0 := by
    intro x hx
    refine h0 _ fun hmem => hx ⟨P • x, hmem, ?_⟩
    change P⁻¹ • P • x = x
    rw [smul_smul, inv_mul_cancel₀ hP0, one_smul]
  let f : C(UnitAddTorus (Fin n), ℂ) :=
    ⟨fun z => φ (torusRep z), continuous_comp_torusRep φ hφ C hC hCb hφ0⟩
  have hSmeas : MeasurableSet {x : Fin n → ℝ | ∀ i, x i ∈ Ioc (-1 / 2 : ℝ) (-1 / 2 + 1)} := by
    have := MeasurableSet.univ_pi (fun _ : Fin n => measurableSet_Ioc (a := (-1 / 2 : ℝ))
      (b := -1 / 2 + 1))
    simpa [Set.pi] using this
  have hcoeff : ∀ k, UnitAddTorus.mFourierCoeff f k = c k := by
    intro k
    rw [UnitAddTorus.mFourierCoeff_eq_integral _ k (fun _ => (-1 / 2 : ℝ)), hcoef k]
    set G : (Fin n → ℝ) → ℂ := fun v => h v * conj (planeWave P k v) with hG
    have step1 : ∫ x in {x : Fin n → ℝ | ∀ i, x i ∈ Ioc (-1 / 2 : ℝ) (-1 / 2 + 1)},
        UnitAddTorus.mFourier (-k) (fun i => (x i : UnitAddCircle)) •
          f (fun i => (x i : UnitAddCircle)) =
        ∫ x in {x : Fin n → ℝ | ∀ i, x i ∈ Ioc (-1 / 2 : ℝ) (-1 / 2 + 1)}, G (P • x) := by
      refine setIntegral_congr_fun hSmeas fun x hx => ?_
      change UnitAddTorus.mFourier (-k) (toUnitTorus x) • φ (torusRep (toUnitTorus x)) = G (P • x)
      rw [torusRep_toUnitTorus x hx, UnitAddTorus.mFourier_neg, mFourier_toUnitTorus hP0,
        smul_eq_mul, hG, mul_comm]
    rw [step1]
    have step2 : ∫ x in {x : Fin n → ℝ | ∀ i, x i ∈ Ioc (-1 / 2 : ℝ) (-1 / 2 + 1)}, G (P • x) =
        ∫ x, G (P • x) := by
      refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
      have hxC : x ∉ C := by
        intro hmem
        refine hx fun i => ?_
        have := hCb x hmem i
        exact ⟨this.1, by have := this.2; linarith⟩
      change h (P • x) * _ = 0
      rw [show h (P • x) = 0 from hφ0 x hxC, zero_mul]
    rw [step2, Measure.integral_comp_smul_of_nonneg volume G P (hR := hP.le),
      Module.finrank_fin_fun]
    have step4 : ∫ v in {u : Fin n → ℝ | ∀ j, u j ∈ Ioo (-P / 2) (P / 2)}, G v = ∫ v, G v := by
      refine setIntegral_eq_integral_of_forall_compl_eq_zero fun v hv => ?_
      have hvK : v ∉ K := fun hmem => hv (hKb v hmem)
      change h v * _ = 0
      rw [h0 v hvK, zero_mul]
    rw [step4, Complex.real_smul]
    push_cast
    rfl
  have hsumm : Summable (UnitAddTorus.mFourierCoeff f) := by
    rw [show UnitAddTorus.mFourierCoeff f = c from funext hcoeff]
    exact hs
  have hx : ∀ i, (P⁻¹ • u) i ∈ Ioc (-1 / 2 : ℝ) (-1 / 2 + 1) := by
    have hx' : ∀ i, (P⁻¹ • u) i ∈ Ioo (-1 / 2 : ℝ) (1 / 2) := by
      refine hbox _ ?_
      rw [smul_smul, mul_inv_cancel₀ hP0, one_smul]
      exact hu
    intro i
    exact ⟨(hx' i).1, by have := (hx' i).2; linarith⟩
  have hPu : P • P⁻¹ • u = u := by rw [smul_smul, mul_inv_cancel₀ hP0, one_smul]
  have hsum := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hsumm (toUnitTorus (P⁻¹ • u))
  have hval : f (toUnitTorus (P⁻¹ • u)) = h u := by
    change φ (torusRep (toUnitTorus (P⁻¹ • u))) = h u
    rw [torusRep_toUnitTorus _ hx]
    change h (P • P⁻¹ • u) = h u
    rw [hPu]
  rw [hval] at hsum
  have hfun : (fun k => UnitAddTorus.mFourierCoeff f k •
      UnitAddTorus.mFourier k (toUnitTorus (P⁻¹ • u))) = fun k => c k * planeWave P k u := by
    funext k
    rw [hcoeff k, mFourier_toUnitTorus hP0, hPu, smul_eq_mul]
  rw [hfun] at hsum
  exact hsum
theorem norm_finsetSum_sub_le_tsum_compl {ι : Type*} {f : ι → ℂ} {a : ℂ} (hf : HasSum f a)
    (hb : Summable fun i => ‖f i‖) (s : Finset ι) :
    ‖(∑ i ∈ s, f i) - a‖ ≤ ∑' i : {x // x ∉ s}, ‖f i‖ := by
  have hsplit := hf.summable.sum_add_tsum_subtype_compl s
  rw [hf.tsum_eq] at hsplit
  have heq : (∑ i ∈ s, f i) - a = -∑' i : {x // x ∉ s}, f i := by
    rw [← hsplit]
    ring
  rw [heq, norm_neg]
  exact norm_tsum_le_tsum_norm (hb.subtype _)
open Kind.Tuple (partialDeriv proj)
open PeriodCell
variable {p : ℕ+}
theorem forall_fin_four_mul (Q : Fin (4 * (p : ℕ)) → Prop)
    (h : ∀ (i : Fin (p : ℕ)) (μ : Fin 4) (hj : 4 * (i : ℕ) + (μ : ℕ) < 4 * (p : ℕ)),
      Q ⟨4 * (i : ℕ) + (μ : ℕ), hj⟩)
    (j : Fin (4 * (p : ℕ))) : Q j := by
  have hj := j.2
  have hi : (j : ℕ) / 4 < (p : ℕ) := by omega
  have hμ : (j : ℕ) % 4 < 4 := by omega
  have hlt : 4 * ((j : ℕ) / 4) + (j : ℕ) % 4 < 4 * (p : ℕ) := by omega
  have key := h ⟨(j : ℕ) / 4, hi⟩ ⟨(j : ℕ) % 4, hμ⟩ hlt
  have hjeq : (⟨4 * ((j : ℕ) / 4) + (j : ℕ) % 4, hlt⟩ : Fin (4 * (p : ℕ))) = j := by
    apply Fin.ext
    change 4 * ((j : ℕ) / 4) + (j : ℕ) % 4 = (j : ℕ)
    omega
  rw [← hjeq]
  exact key
theorem proj_euclidean_injective (D : Params) :
    Function.Injective (proj D Kind.euclidean (p := p)) := by
  intro x y hxy
  funext j
  refine forall_fin_four_mul (fun j => x j = y j) (fun i μ _ => ?_) j
  have h1 : x.block i = y.block i := congrFun hxy i
  exact congrFun h1 μ
theorem proj_mem_cellPow_iff (D : Params) (P : ℝ) (u : Coords p) :
    proj D Kind.euclidean u ∈ cellPow D p P ↔ u ∈ coordCube p P := by
  constructor
  · intro h j
    exact forall_fin_four_mul (fun j => u j ∈ Ioo (-P / 2) (P / 2)) (fun i μ _ => h i μ) j
  · intro h i μ
    exact h _
theorem isOpen_coordCube (P : ℝ) : IsOpen (coordCube p P) := by
  have h : coordCube p P = Set.pi univ fun _ => Ioo (-P / 2) (P / 2) := by
    ext u
    simp [coordCube, Set.pi]
  rw [h]
  exact isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo
theorem isCompact_proj_preimage (D : Params)
    (honto : Function.Surjective (proj D Kind.euclidean (p := p)))
    (hopen : ∀ U : Set (Coords p), IsOpen U →
      Kind.Tuple.IsOpenT D Kind.euclidean (proj D Kind.euclidean '' U))
    (S : Set (Kind.euclidean.Tuple D p))
    (hS : Kind.Tuple.IsCompactT D Kind.euclidean S) :
    IsCompact (proj D Kind.euclidean ⁻¹' S) := by
  refine isCompact_of_finite_subcover fun {ι} U hU hcov => ?_
  have hsub : S ⊆ ⋃₀ (Set.range fun i => proj D Kind.euclidean '' U i) := by
    intro y hy
    obtain ⟨x, rfl⟩ := honto y
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hcov hy)
    exact ⟨_, ⟨i, rfl⟩, x, hi, rfl⟩
  obtain ⟨𝒰, h𝒰, hfin, hcov'⟩ := hS _ (by rintro _ ⟨i, rfl⟩; exact hopen _ (hU i)) hsub
  have hex : ∃ t ⊆ (univ : Set ι), t.Finite ∧
      S ⊆ ⋃₀ ((fun i => proj D Kind.euclidean '' U i) '' t) :=
    (Set.exists_subset_image_finite_and (p := fun V => S ⊆ ⋃₀ V)).1
      ⟨𝒰, by rwa [image_univ], hfin, hcov'⟩
  obtain ⟨t, -, htf, hcovt⟩ := hex
  refine ⟨htf.toFinset, fun x hx => ?_⟩
  obtain ⟨_, ⟨i, hi, rfl⟩, w, hw, hwx⟩ := hcovt hx
  rw [proj_euclidean_injective D hwx] at hw
  exact mem_iUnion₂.2 ⟨i, htf.mem_toFinset.2 hi, hw⟩
theorem norm_fourierChar (P : ℝ) (k : IntCoords p) (u : Coords p) :
    ‖fourierChar P k u‖ = 1 := by apply _root_.YangMills.Construction.PeriodicSpace.PeriodCell.Fourier.norm_fourierChar <;> assumption
theorem tendsto_cubeUpTo : Tendsto (IntCoords.cubeUpTo (p := p)) atTop atTop := by apply _root_.YangMills.Construction.PeriodicSpace.PeriodCell.CutoffForms.tendsto_cubeUpTo <;> assumption
theorem hasSum_fourierChar (D : Params) {P : ℝ} (hP : 0 < P)
    (hpts : TupleFacts.AllFacts)
    (H : Kind.euclidean.Tuple D p → ℂ) (hH : H ∈ cellTestFns D p P)
    (hsum : Summable fun k : IntCoords p => ‖fourierCoeff D P H k‖)
    (u : Coords p) (hu : u ∈ coordCube p P) :
    HasSum (fun k : IntCoords p => fourierCoeff D P H k * fourierChar P k u)
      (H (proj D Kind.euclidean u)) := by
  obtain ⟨hfib, -, hmetric, -, -, -, -, hopen, -⟩ := hpts D Kind.euclidean p
  have hcont : Continuous (H ∘ proj D Kind.euclidean (p := p)) := hH.1 0
  have hK := isCompact_proj_preimage D hfib.1 hopen _ hH.2.1
  refine hasSum_planeWave_of_summable hP (H ∘ proj D Kind.euclidean) hcont _ hK ?_ ?_ _
    (fun k => rfl) hsum.of_norm u hu
  · intro v hv
    exact (proj_mem_cellPow_iff D P v).1 (hH.2.2 hv)
  · intro v hv
    by_contra hne
    refine hv fun r hr => ⟨_, hne, ?_⟩
    have h0 := (hmetric.2.1 (proj D Kind.euclidean v)
      (proj D Kind.euclidean v)).2 rfl
    rw [h0]
    exact hr
theorem testFnFourierSeriesConverges_holds (hcoef : PeriodCell.FourierCoeffBounds)
    (hpts : TupleFacts.AllFacts) : TestFnFourierSeriesConverges := by
  intro D p P hP F hF α
  obtain ⟨-, -, hchar, hderiv, -, -, -, -, -, hsummable, -⟩ := hcoef D p P hP
  obtain ⟨-, -, -, -, -, -, -, -, hread, -, -, -, -, -, -, -, -, -, -, hstable, -⟩ :=
    hpts D Kind.euclidean p
  have hcellOpen : Kind.Tuple.IsOpenT D Kind.euclidean (cellPow D p P) := by
    refine (hread _).2 ?_
    have hpre : proj D Kind.euclidean ⁻¹' cellPow D p P = coordCube p P :=
      Set.ext fun u => proj_mem_cellPow_iff D P u
    rw [hpre]
    exact isOpen_coordCube P
  have hH : partialDeriv D Kind.euclidean α F ∈ cellTestFns D p P :=
    ((hstable _ hcellOpen).2 F hF).2.2.1 α
  have hsum := hsummable _ hH
  have hbound : ∀ (t : ℕ+) (u : Coords p), u ∈ coordCube p P →
      ‖(∑ k ∈ IntCoords.cubeUpTo t,
          fourierCoeff D P F k * Coords.iterPartial α (fourierChar P k) u) -
        partialDeriv D Kind.euclidean α F (proj D Kind.euclidean u)‖ ≤
      ∑' k : {x // x ∉ IntCoords.cubeUpTo (p := p) t},
        ‖fourierCoeff D P (partialDeriv D Kind.euclidean α F) k‖ := by
    intro t u hu
    have hrewrite : ∑ k ∈ IntCoords.cubeUpTo t,
        fourierCoeff D P F k * Coords.iterPartial α (fourierChar P k) u =
        ∑ k ∈ IntCoords.cubeUpTo t,
          fourierCoeff D P (partialDeriv D Kind.euclidean α F) k * fourierChar P k u := by
      refine Finset.sum_congr rfl fun k _ => ?_
      have hck : Coords.iterPartial α (fourierChar P k) u =
          fourierMultiplier P k α * fourierChar P k u := congrFun (hchar α k) u
      rw [hck, hderiv F hF α k]
      ring
    rw [hrewrite]
    have hnorm : ∀ k : IntCoords p,
        ‖fourierCoeff D P (partialDeriv D Kind.euclidean α F) k * fourierChar P k u‖ =
          ‖fourierCoeff D P (partialDeriv D Kind.euclidean α F) k‖ := fun k => by
      rw [norm_mul, norm_fourierChar, mul_one]
    have hle := norm_finsetSum_sub_le_tsum_compl (hasSum_fourierChar D hP hpts _ hH hsum u hu)
      (by simpa only [hnorm] using hsum) (IntCoords.cubeUpTo t)
    simpa only [hnorm] using hle
  have htail : Tendsto (fun t : ℕ+ => ∑' k : {x // x ∉ IntCoords.cubeUpTo (p := p) t},
      ‖fourierCoeff D P (partialDeriv D Kind.euclidean α F) k‖) atTop (𝓝 0) :=
    (tendsto_tsum_compl_atTop_zero
      fun k => ‖fourierCoeff D P (partialDeriv D Kind.euclidean α F) k‖).comp tendsto_cubeUpTo
  have htail' := ENNReal.tendsto_ofReal htail
  rw [ENNReal.ofReal_zero] at htail'
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail'
    (fun _ => zero_le)
    fun t => iSup₂_le fun u hu => ENNReal.ofReal_le_ofReal (hbound t u hu)
end YangMills.Construction.PeriodicSpace.FourierSeriesConvergence
