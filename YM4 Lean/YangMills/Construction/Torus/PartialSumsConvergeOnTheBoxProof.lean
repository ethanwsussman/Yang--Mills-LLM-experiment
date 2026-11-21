import YangMills.Construction.Torus.CoefficientsOfATestFunctionOnTheBoxProof
import YangMills.Construction.Torus.CoveringMapOpenAndCompactSetsAndDerivativesOfTuples
import YangMills.Construction.Torus.FormOfACutOffAtTensorsProof
import YangMills.Construction.Torus.PartialSumsConvergeOnTheBox
import YangMills.Construction.TorusOrFourSpace.FourierSeriesOfATestFunctionConvergesProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped ComplexConjugate Topology
noncomputable section
namespace YangMills.Construction
open Torus Torus.FourierBox AmbientPoints
namespace FourierPartialSums
section Modes
variable {D : ℕ}
def modeFrequency (P : ℝ) (k : Fin D → ℤ) (j : Fin D) : ℂ :=
  2 * Real.pi * Complex.I * (k j : ℂ) / (P : ℂ)
def modeWeight (P : ℝ) (k : Fin D → ℤ) (α : PowerSeries.MultiIndex D) : ℂ :=
  ∏ j, modeFrequency P k j ^ α j
theorem fourierMode_add_smul_single (P : ℝ) (k : Fin D → ℤ) (j : Fin D) (u : Fin D → ℝ) (t : ℝ) :
    fourierMode P k (u + t • Pi.single j 1) =
      Complex.exp (2 * Real.pi * Complex.I * (intDot k u : ℂ) / (P : ℂ) +
        (t : ℂ) * modeFrequency P k j) := by
  have hs : intDot k (u + t • Pi.single j 1) =
      intDot k u + t * (k j : ℝ) := by
    unfold intDot
    have : ∀ i, (k i : ℝ) * (u + t • (Pi.single j 1 : Fin D → ℝ)) i =
        (k i : ℝ) * u i + (if i = j then t * (k j : ℝ) else 0) := by
      intro i
      by_cases h : i = j
      · subst h
        simp
        ring
      · simp [h]
    simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [fourierMode, hs, modeFrequency]
  congr 1
  push_cast
  ring
theorem partialDeriv_const_mul_fourierMode (P : ℝ) (k : Fin D → ℤ) (j : Fin D) (c : ℂ) :
    partialDeriv j (fun u => c * fourierMode P k u) =
      fun u => c * modeFrequency P k j * fourierMode P k u := by
  funext u
  set A : ℂ := 2 * Real.pi * Complex.I * (intDot k u : ℂ) / (P : ℂ) with hA
  set f : ℂ := modeFrequency P k j with hf
  have hz : HasDerivAt (fun z : ℂ => c * Complex.exp (A + z * f))
      (c * (Complex.exp (A + ((0 : ℝ) : ℂ) * f) * f)) ((0 : ℝ) : ℂ) := by
    have h1 : HasDerivAt (fun z : ℂ => A + z * f) f ((0 : ℝ) : ℂ) := by
      simpa using ((hasDerivAt_id ((0 : ℝ) : ℂ)).mul_const f).const_add A
    exact (h1.cexp).const_mul c
  have hr : HasDerivAt (fun t : ℝ => c * Complex.exp (A + (t : ℂ) * f))
      (c * (Complex.exp (A + ((0 : ℝ) : ℂ) * f) * f)) 0 := hz.comp_ofReal
  have hline : HasLineDerivAt ℝ (fun u => c * fourierMode P k u)
      (c * (Complex.exp (A + ((0 : ℝ) : ℂ) * f) * f)) u (Pi.single j 1) := by
    unfold HasLineDerivAt
    refine hr.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    change c * fourierMode P k (u + t • Pi.single j 1) = _
    rw [fourierMode_add_smul_single]
  have hval : Complex.exp (A + ((0 : ℝ) : ℂ) * f) = fourierMode P k u := by
    simp [hA, fourierMode]
  change lineDeriv ℝ (fun u => c * fourierMode P k u) u (Pi.single j 1) = _
  rw [hline.lineDeriv, hval]
  ring
theorem iterate_partialDeriv_fourierMode (P : ℝ) (k : Fin D → ℤ) (j : Fin D) (n : ℕ) (c : ℂ) :
    (partialDeriv j)^[n] (fun u => c * fourierMode P k u) =
      fun u => c * modeFrequency P k j ^ n * fourierMode P k u := by
  induction n generalizing c with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, partialDeriv_const_mul_fourierMode, ih]
    funext u
    ring
theorem foldr_partialDeriv_fourierMode (P : ℝ) (k : Fin D → ℤ) (α : PowerSeries.MultiIndex D)
    (l : List (Fin D)) :
    l.foldr (fun j H => (partialDeriv j)^[α j] H) (fourierMode P k) =
      fun u => (l.map fun j => modeFrequency P k j ^ α j).prod * fourierMode P k u := by
  induction l with
  | nil => simp
  | cons j l ih =>
    rw [List.foldr_cons, ih, iterate_partialDeriv_fourierMode]
    funext u
    simp only [List.map_cons, List.prod_cons]
    ring
theorem iteratedPartial_fourierMode (P : ℝ) (k : Fin D → ℤ) (α : PowerSeries.MultiIndex D)
    (u : Fin D → ℝ) :
    iteratedPartial α (fourierMode P k) u = modeWeight P k α * fourierMode P k u := by
  unfold iteratedPartial
  rw [foldr_partialDeriv_fourierMode, modeWeight, Fin.prod_univ_def]
theorem norm_fourierMode {P : ℝ} (k : Fin D → ℤ) (u : Fin D → ℝ) : ‖fourierMode P k u‖ = 1 := by apply _root_.YangMills.Construction.Torus.FourierBox.Estimates.norm_fourierMode <;> assumption
theorem tendsto_modesWithin :
    Tendsto (fun t : ℕ+ => (modesWithin (t : ℕ) : Finset (Fin D → ℤ))) atTop atTop := by apply _root_.YangMills.Construction.AmbientPoints.CutoffSeriesAtTensorsProof.tendsto_modesWithin <;> assumption
end Modes
section Series
variable {n : ℕ}
def toUnitAddTorus (x : Fin n → ℝ) : UnitAddTorus (Fin n) := fun i => (x i : UnitAddCircle)
def torusRep (z : UnitAddTorus (Fin n)) : Fin n → ℝ :=
  fun i => (AddCircle.equivIoc (1 : ℝ) (-1 / 2) (z i) : ℝ)
theorem continuous_toUnitAddTorus : Continuous (toUnitAddTorus (n := n)) := by apply _root_.YangMills.Construction.PeriodicSpace.FourierSeriesConvergence.continuous_toUnitTorus <;> assumption
theorem torusRep_toUnitAddTorus (x : Fin n → ℝ)
    (hx : ∀ i, x i ∈ Ioc (-1 / 2 : ℝ) (-1 / 2 + 1)) : torusRep (toUnitAddTorus x) = x :=
  funext fun i => AddCircle.equivIoc_coe_of_mem (p := (1 : ℝ)) (a := -1 / 2) (hx i)
theorem toUnitAddTorus_torusRep (z : UnitAddTorus (Fin n)) : toUnitAddTorus (torusRep z) = z :=
  funext fun _ => AddCircle.coe_equivIoc (p := (1 : ℝ)) (a := -1 / 2)
theorem mFourier_toUnitAddTorus {P : ℝ} (hP : P ≠ 0) (k : Fin n → ℤ) (x : Fin n → ℝ) :
    UnitAddTorus.mFourier k (toUnitAddTorus x) = fourierMode P k (P • x) := by
  have hP' : (P : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hP
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, toUnitAddTorus, fourier_coe_apply,
    fourierMode, intDot, Pi.smul_apply, smul_eq_mul]
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
    have hclosed : IsClosed (toUnitAddTorus '' C) :=
      (hC.image continuous_toUnitAddTorus).isClosed
    have hzn : z ∉ toUnitAddTorus '' C := by
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
      refine h0 _ fun hmem => hw ⟨_, hmem, toUnitAddTorus_torusRep w⟩
    exact continuousAt_const.congr hev.symm
theorem hasSum_fourierMode_of_summable {P : ℝ} (hP : 0 < P) (h : (Fin n → ℝ) → ℂ)
    (hc : Continuous h) (K : Set (Fin n → ℝ)) (hK : IsCompact K)
    (hKb : ∀ u ∈ K, ∀ j, u j ∈ Ioo (-P / 2) (P / 2)) (h0 : ∀ u, u ∉ K → h u = 0)
    (c : (Fin n → ℤ) → ℂ)
    (hcoef : ∀ k, c k = ((P : ℂ) ^ n)⁻¹ *
      ∫ u in fundamentalCube n P, h u * conj (fourierMode P k u))
    (hs : Summable c) (u : Fin n → ℝ) (hu : ∀ j, u j ∈ Ioo (-P / 2) (P / 2)) :
    HasSum (fun k => c k * fourierMode P k u) (h u) := by
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
    set G : (Fin n → ℝ) → ℂ := fun v => h v * conj (fourierMode P k v) with hG
    have step1 : ∫ x in {x : Fin n → ℝ | ∀ i, x i ∈ Ioc (-1 / 2 : ℝ) (-1 / 2 + 1)},
        UnitAddTorus.mFourier (-k) (fun i => (x i : UnitAddCircle)) •
          f (fun i => (x i : UnitAddCircle)) =
        ∫ x in {x : Fin n → ℝ | ∀ i, x i ∈ Ioc (-1 / 2 : ℝ) (-1 / 2 + 1)}, G (P • x) := by
      refine setIntegral_congr_fun hSmeas fun x hx => ?_
      change UnitAddTorus.mFourier (-k) (toUnitAddTorus x) •
        φ (torusRep (toUnitAddTorus x)) = G (P • x)
      rw [torusRep_toUnitAddTorus x hx, UnitAddTorus.mFourier_neg,
        mFourier_toUnitAddTorus hP0, smul_eq_mul, hG, mul_comm]
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
    have step4 : ∫ v in fundamentalCube n P, G v = ∫ v, G v := by
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
  have hsum :=
    UnitAddTorus.hasSum_mFourier_series_apply_of_summable hsumm (toUnitAddTorus (P⁻¹ • u))
  have hval : f (toUnitAddTorus (P⁻¹ • u)) = h u := by
    change φ (torusRep (toUnitAddTorus (P⁻¹ • u))) = h u
    rw [torusRep_toUnitAddTorus _ hx]
    change h (P • P⁻¹ • u) = h u
    rw [hPu]
  rw [hval] at hsum
  have hfun : (fun k => UnitAddTorus.mFourierCoeff f k •
      UnitAddTorus.mFourier k (toUnitAddTorus (P⁻¹ • u))) = fun k => c k * fourierMode P k u := by
    funext k
    rw [hcoeff k, mFourier_toUnitAddTorus hP0, hPu, smul_eq_mul]
  rw [hfun] at hsum
  exact hsum
theorem norm_finsetSum_sub_le {ι : Type*} {f : ι → ℂ} {a : ℂ} (hf : HasSum f a)
    (hb : Summable fun i => ‖f i‖) (s : Finset ι) :
    ‖(∑ i ∈ s, f i) - a‖ ≤ ∑' i : {x // x ∉ s}, ‖f i‖ := by apply _root_.YangMills.Construction.PeriodicSpace.FourierSeriesConvergence.norm_finsetSum_sub_le_tsum_compl <;> assumption
end Series
section Box
variable {s : Conventions.StandingParameters} {p : ℕ}
theorem fourierCoeff_multiDeriv {P : ℝ}
    (hone : ∀ G ∈ testFns (fundamentalBoxPow s p P), ∀ (j : Fin (4 * p)) (k : Fin (4 * p) → ℤ),
      FourierBox.fourierCoeff P (multiDeriv (Pi.single j 1) G) k =
        modeFrequency P k j * FourierBox.fourierCoeff P G k)
    (hstable : ∀ G ∈ testFns (fundamentalBoxPow s p P), ∀ α : PowerSeries.MultiIndex (4 * p),
      multiDeriv α G ∈ testFns (fundamentalBoxPow s p P))
    (hcomp : ∀ G ∈ testFns (fundamentalBoxPow s p P), ∀ α β : PowerSeries.MultiIndex (4 * p),
      multiDeriv β (multiDeriv α G) = multiDeriv (α + β) G)
    (F : Tuple s .euclidean p → ℂ) (hF : F ∈ testFns (fundamentalBoxPow s p P))
    (k : Fin (4 * p) → ℤ) (m : ℕ) :
    ∀ α : PowerSeries.MultiIndex (4 * p), α.order = m →
      FourierBox.fourierCoeff P (multiDeriv α F) k =
        modeWeight P k α * FourierBox.fourierCoeff P F k := by
  induction m with
  | zero =>
    intro α hα
    have h0 : α = 0 := by
      funext j
      have hs : ∑ i, α i = 0 := hα
      exact (Finset.sum_eq_zero_iff.mp hs) j (Finset.mem_univ j)
    subst h0
    simp [multiDeriv_zero, modeWeight]
  | succ m ih =>
    intro α hα
    have hex : ∃ j, α j ≠ 0 := by
      by_contra hcon
      have hall : ∀ j, α j = 0 := fun j => by
        by_contra hj
        exact hcon ⟨j, hj⟩
      have hs : ∑ i, α i = m + 1 := hα
      simp [hall] at hs
    obtain ⟨j, hj⟩ := hex
    set α' : PowerSeries.MultiIndex (4 * p) := Function.update α j (α j - 1) with hα'
    have hsum : α = α' + Pi.single j 1 := by
      funext i
      by_cases hi : i = j
      · subst hi
        simp only [hα', Pi.add_apply, Function.update_self, Pi.single_eq_same]
        omega
      · simp [hα', hi]
    have hsize : α'.order = m := by
      have h1 : α.order = α'.order + 1 := by
        have : ∑ i, α i = ∑ i, α' i +
            ∑ i, (Pi.single j 1 : PowerSeries.MultiIndex (4 * p)) i := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => congrFun hsum i
        simpa [PowerSeries.MultiIndex.order] using this
      omega
    have hw : modeWeight P k α = modeFrequency P k j * modeWeight P k α' := by
      have hfac : ∀ i, modeFrequency P k i ^ α i =
          (if i = j then modeFrequency P k j else 1) * modeFrequency P k i ^ α' i := by
        intro i
        by_cases hi : i = j
        · subst hi
          have : α i = α' i + 1 := by
            have := congrFun hsum i
            simpa using this
          rw [this, if_pos rfl, pow_succ]
          ring
        · have : α i = α' i := by
            have := congrFun hsum i
            simpa [Pi.single_apply, hi] using this
          rw [this, if_neg hi, one_mul]
      rw [modeWeight, modeWeight, Finset.prod_congr rfl fun i _ => hfac i,
        Finset.prod_mul_distrib]
      simp
    rw [hsum, ← hcomp F hF α' (Pi.single j 1), hone _ (hstable F hF α') j k, ih α' hsize,
      ← hsum, hw]
    ring
end Box
theorem statement_holds (hcoef : FourierCoeffBounds)
    (htop : TupleTopology.Holds)
    (hrest : TestFnOperations) : Statement := by
  intro s p hp P hP F hF α
  obtain ⟨-, hco, -, -⟩ := hcoef s p P hp hP
  obtain ⟨hcm, hopen, -, -, hder⟩ := (htop s .euclidean).1 p hp
  have hΩ : IsOpen (fundamentalBoxPow s p P) := isOpen_fundamentalBoxPow s p P
  obtain ⟨-, -, hparts, -⟩ := (hrest s .euclidean p hp).2.1 _ hΩ
  have hstable : ∀ G ∈ testFns (fundamentalBoxPow s p P), ∀ β : PowerSeries.MultiIndex (4 * p),
      multiDeriv β G ∈ testFns (fundamentalBoxPow s p P) :=
    fun G hG β => ((hparts G hG).2.2.1 β).1
  have hcomp : ∀ G ∈ testFns (fundamentalBoxPow s p P),
      ∀ β γ : PowerSeries.MultiIndex (4 * p),
      multiDeriv γ (multiDeriv β G) = multiDeriv (β + γ) G :=
    fun G hG β γ => (((hder ⊤ G hG.1).1 β le_top).2.2.2 rfl).2 γ
  have hone : ∀ G ∈ testFns (fundamentalBoxPow s p P), ∀ (j : Fin (4 * p))
      (k : Fin (4 * p) → ℤ),
      FourierBox.fourierCoeff P (multiDeriv (Pi.single j 1) G) k =
        modeFrequency P k j * FourierBox.fourierCoeff P G k :=
    fun G hG j k => (hco G hG).2.1 j k
  set H : Tuple s .euclidean p → ℂ := multiDeriv α F with hHdef
  have hH : H ∈ testFns (fundamentalBoxPow s p P) := hstable F hF α
  have hsum : Summable fun k : Fin (4 * p) → ℤ => ‖FourierBox.fourierCoeff P H k‖ := by
    have := (hco H hH).2.2.2 0 le_rfl
    simpa using this
  have hweight : ∀ k, FourierBox.fourierCoeff P H k =
      modeWeight P k α * FourierBox.fourierCoeff P F k :=
    fun k => fourierCoeff_multiDeriv hone hstable hcomp F hF k _ α rfl
  have hinj : Function.Injective (tupleProj s .euclidean p) := by
    intro x x' hx
    have : x - x' = 0 := (hcm.2.1 x x').1 hx
    exact sub_eq_zero.mp this
  have hcontπ : Continuous (tupleProj s .euclidean p) := by
    have h := (hopen.2.2.2.2.2 (Tuple s .euclidean p) id).1 continuous_id
    simpa using h
  have hopenπ : IsOpenMap (tupleProj s .euclidean p) := by
    intro U hU
    refine (hopen.2.2.2.2.1 _).2 ?_
    rwa [Set.preimage_image_eq _ hinj]
  have hhomeo : IsHomeomorph (tupleProj s .euclidean p) :=
    ⟨hcontπ, hopenπ, hinj, hcm.1⟩
  have hK : IsCompact (tupleProj s .euclidean p ⁻¹' closedSupport H) := by
    have := (hhomeo.homeomorph _).isCompact_preimage.2 hH.2.1
    exact this
  have hcontH : Continuous (H ∘ tupleProj s .euclidean p) := by
    have h := hH.1.2 0 zero_le
    exact continuousOn_univ.1 h
  have hseries : ∀ u ∈ fundamentalCube (4 * p) P,
      HasSum (fun k => FourierBox.fourierCoeff P H k * fourierMode P k u)
        (H (tupleProj s .euclidean p u)) := by
    intro u hu
    refine hasSum_fourierMode_of_summable hP (H ∘ tupleProj s .euclidean p) hcontH _ hK ?_ ?_ _
      (fun k => rfl) hsum.of_norm u hu
    · intro v hv
      exact (tupleProj_mem_fundamentalBoxPow_iff s p P v).1 (hH.2.2 hv)
    · intro v hv
      by_contra hne
      exact hv (subset_closure hne)
  have hbound : ∀ (t : ℕ+) (u : Fin (4 * p) → ℝ), u ∈ fundamentalCube (4 * p) P →
      ‖(∑ k ∈ modesWithin (t : ℕ),
          FourierBox.fourierCoeff P F k * iteratedPartial α (fourierMode P k) u) -
        H (tupleProj s .euclidean p u)‖ ≤
      ∑' k : {x // x ∉ (modesWithin (t : ℕ) : Finset (Fin (4 * p) → ℤ))},
        ‖FourierBox.fourierCoeff P H k‖ := by
    intro t u hu
    have hrewrite : ∑ k ∈ modesWithin (t : ℕ),
        FourierBox.fourierCoeff P F k * iteratedPartial α (fourierMode P k) u =
        ∑ k ∈ modesWithin (t : ℕ), FourierBox.fourierCoeff P H k * fourierMode P k u := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [iteratedPartial_fourierMode, hweight k]
      ring
    rw [hrewrite]
    have hnorm : ∀ k : Fin (4 * p) → ℤ,
        ‖FourierBox.fourierCoeff P H k * fourierMode P k u‖ =
          ‖FourierBox.fourierCoeff P H k‖ := fun k => by
      rw [norm_mul, norm_fourierMode, mul_one]
    have hle := norm_finsetSum_sub_le (hseries u hu) (by simpa only [hnorm] using hsum)
      (modesWithin (t : ℕ))
    simpa only [hnorm] using hle
  have htail : Tendsto (fun t : ℕ+ =>
      ∑' k : {x // x ∉ (modesWithin (t : ℕ) : Finset (Fin (4 * p) → ℤ))},
        ‖FourierBox.fourierCoeff P H k‖) atTop (𝓝 0) :=
    (tendsto_tsum_compl_atTop_zero fun k => ‖FourierBox.fourierCoeff P H k‖).comp
      tendsto_modesWithin
  have htail' := ENNReal.tendsto_ofReal htail
  rw [ENNReal.ofReal_zero] at htail'
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail'
    (fun _ => zero_le)
    fun t => iSup₂_le fun u hu => ENNReal.ofReal_le_ofReal (hbound t u hu)
end FourierPartialSums
end YangMills.Construction
