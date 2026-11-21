import YangMills.Construction.Coordinates.PowerSeriesHolomorphy
import YangMills.Construction.Matrices.CalculusOfHolomorphicMaps
import YangMills.Construction.Matrices.ExpChartHolomorphy
import YangMills.Construction.Towers.MapsReadBackFromTheChartAtOneProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter
open YangMills.Construction.Matrices YangMills.Construction.Coordinates YangMills.Construction.PowerSeries.RealSeries YangMills.Construction.Matrices.GroupLieProduct YangMills.Construction.Matrices.GroupLieProduct.Subspaces YangMills.Construction.Matrices.GroupLieProduct.Subspaces.AnalyticCalculus YangMills.Construction.Matrices.PowerExpCharts YangMills.Construction.IdentityExpChart
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
namespace YangMills.Construction.IdentityExpChart.CoordinatesInChart
section Coordinates
variable {N l l' : ℕ}
theorem isRelativelyOpen_realEmbed_image {D : Set (Fin N → ℝ)} (hD : IsOpen D) :
    ComplexMatrix2.IsRelativelyOpen (ComplexCoordinates.realLocus N) (realEmbed '' D) := by apply _root_.YangMills.Construction.Tower.IdentityChartPullback.isRelativelyOpen_realEmbed_image <;> assumption
theorem isRealAnalyticIn_linearMap {D : Set (ComplexCoordinates N)}
    {f : ComplexCoordinates N → ComplexCoordinates l}
    (A : ComplexCoordinates l →ₗ[ℂ] ComplexCoordinates l')
    (hf : ComplexCoordinates.IsRealAnalyticIn D f) :
    ComplexCoordinates.IsRealAnalyticIn D (fun z => A (f z)) := by
  refine ⟨hf.1, fun a ha => ?_⟩
  obtain ⟨c, hc⟩ := hf.2 a ha
  refine ⟨fun m => A (c m), hc.mono fun z hz => ?_⟩
  have := hz.map A.toContinuousLinearMap A.toContinuousLinearMap.continuous
  simpa [Function.comp_def, map_smul] using this
theorem isRealAnalyticIn_finsetSum {ι : Type} [Fintype ι] {D : Set (ComplexCoordinates N)}
    {f : ι → ComplexCoordinates N → ComplexCoordinates l}
    (hD : ComplexMatrix2.IsRelativelyOpen (ComplexCoordinates.realLocus N) D)
    (hf : ∀ i, ComplexCoordinates.IsRealAnalyticIn D (f i)) :
    ComplexCoordinates.IsRealAnalyticIn D (fun z => ∑ i, f i z) := by
  refine ⟨hD, fun a ha => ?_⟩
  choose c hc using fun i => (hf i).2 a ha
  refine ⟨fun m => ∑ i, c i m, ?_⟩
  filter_upwards [eventually_all.2 hc] with z hz
  have := hasSum_sum (s := Finset.univ) fun i _ => hz i
  simpa [Finset.smul_sum] using this
theorem isRealAnalyticIn_congr {D : Set (ComplexCoordinates N)}
    {f g : ComplexCoordinates N → ComplexCoordinates l}
    (hf : ComplexCoordinates.IsRealAnalyticIn D f) (hfg : EqOn f g D) :
    ComplexCoordinates.IsRealAnalyticIn D g := by
  refine ⟨hf.1, fun a ha => ?_⟩
  obtain ⟨c, hc⟩ := hf.2 a ha
  refine ⟨c, ?_⟩
  obtain ⟨U, hU, hDU⟩ := hf.1
  have hmem : D ∈ 𝓝[ComplexCoordinates.realLocus N] a := by
    rw [hDU] at ha ⊢
    rw [inter_comm]
    exact inter_mem_nhdsWithin _ (hU.mem_nhds ha.1)
  filter_upwards [hc, hmem] with z hz hzD
  rw [← hfg hzD]
  exact hz
theorem isHolomorphicIn_linearMap {S : Set (ComplexCoordinates N)} (hS : IsOpen S)
    (A : ComplexCoordinates N →ₗ[ℂ] ComplexCoordinates l) :
    ComplexCoordinates.IsHolomorphicIn S A := by
  refine ⟨hS, A.toContinuousLinearMap.continuous.continuousOn, fun a _ j => ?_⟩
  refine Eventually.of_forall fun ζ => ?_
  have h1 : DifferentiableAt ℂ (fun ζ : ℂ => a + ζ • ComplexCoordinates.stdBasisVector j) ζ := by
    fun_prop
  exact A.toContinuousLinearMap.differentiableAt.comp ζ h1
def complexExtension (R : (Fin N → ℝ) →ₗ[ℝ] (Fin l → ℝ)) :
    ComplexCoordinates N →ₗ[ℂ] ComplexCoordinates l where
  toFun z i := ∑ j, (R (Pi.single j 1) i : ℂ) * z j
  map_add' z w := by
    funext i
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c z := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
theorem complexExtension_realEmbed (R : (Fin N → ℝ) →ₗ[ℝ] (Fin l → ℝ)) (u : Fin N → ℝ) :
    complexExtension R (realEmbed u) = realEmbed (R u) := by
  funext i
  have hu : u = ∑ j, u j • (Pi.single j 1 : Fin N → ℝ) := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  have hR : R u i = ∑ j, u j * R (Pi.single j 1) i := by
    conv_lhs => rw [hu]
    simp [map_sum, Finset.sum_apply]
  simp only [complexExtension, LinearMap.coe_mk, AddHom.coe_mk, realEmbed, hR]
  push_cast
  exact Finset.sum_congr rfl fun j _ => by ring
end Coordinates
section Via
variable {V T T' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {l l' : ℕ}
theorem realAnalyticVia_congr {e : T → ComplexCoordinates l} {e' : T' → ComplexCoordinates l}
    {D : Set V} {g : V → T} {g' : V → T'} (hg₀ : IsRealAnalyticVia e D g)
    (hg : ∀ Y ∈ D, e' (g' Y) = e (g Y)) : IsRealAnalyticVia e' D g' := by
  refine ⟨hg₀.1, fun N x => isRealAnalyticIn_congr (hg₀.2 N x) ?_⟩
  rintro _ ⟨_, ⟨Y, hY, rfl⟩, rfl⟩
  have hre : (fun i => (realEmbed (x Y) i).re) = x Y := by
    funext i
    simp [realEmbed]
  simp only [hre, LinearEquiv.symm_apply_apply]
  exact (hg Y hY).symm
theorem realAnalyticVia_linearMap {e : T → ComplexCoordinates l} {D : Set V} {g : V → T}
    (A : ComplexCoordinates l →ₗ[ℂ] ComplexCoordinates l') (hg : IsRealAnalyticVia e D g) :
    IsRealAnalyticVia (fun t => A (e t)) D g :=
  ⟨hg.1, fun N x => isRealAnalyticIn_linearMap A (hg.2 N x)⟩
theorem realAnalyticVia_sum {ι : Type} [Fintype ι] [Nonempty ι]
    {e : ι → T → ComplexCoordinates l} {D : Set V} {g : V → T}
    (hg : ∀ i, IsRealAnalyticVia (e i) D g) :
    IsRealAnalyticVia (fun t => ∑ i, e i t) D g := by
  refine ⟨(hg (Classical.arbitrary ι)).1, fun N x => ?_⟩
  exact isRealAnalyticIn_finsetSum ((hg (Classical.arbitrary ι)).2 N x).1 fun i => (hg i).2 N x
end Via
section Pauli
def toMatrixLinear : ComplexMatrix2.LieElement →ₗ[ℝ] ComplexMatrix2 where
  toFun := ComplexMatrix2.LieElement.toMatrix
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem toMatrixLinear_apply (Y : ComplexMatrix2.LieElement) : toMatrixLinear Y = Y.toMatrix := rfl
theorem lieElement_ext {Y Y' : ComplexMatrix2.LieElement} (h : Y.toMatrix = Y'.toMatrix) : Y = Y' :=
  Subtype.ext h
def pauliPairing (a : Fin 3) : ComplexMatrix2 →ₗ[ℂ] ℂ where
  toFun M := (1 / 2 : ℂ) * Matrix.trace (M * pauliFamily a)
  map_add' M M' := by simp [add_mul, Matrix.trace_add, mul_add]
  map_smul' c M := by
    simp [Matrix.trace_smul]
    ring
def pauliCoeff (a : Fin 3) : ComplexMatrix2.LieElement →ₗ[ℝ] ℝ :=
  Complex.reLm ∘ₗ (pauliPairing a).restrictScalars ℝ ∘ₗ toMatrixLinear
theorem pauliCoeff_apply (a : Fin 3) (Y : ComplexMatrix2.LieElement) :
    pauliCoeff a Y = (pauliPairing a Y.toMatrix).re := rfl
theorem pauliPairing_zero (M : ComplexMatrix2) :
    pauliPairing 0 M = (1 / 2 : ℂ) * (M 0 1 + M 1 0) := by
  simp [pauliPairing, pauliFamily, OneLoop.pauliX, Matrix.trace_fin_two, Matrix.mul_apply,
    Fin.sum_univ_two]
theorem pauliPairing_one (M : ComplexMatrix2) :
    pauliPairing 1 M = (1 / 2 : ℂ) * (Complex.I * (M 0 1 - M 1 0)) := by
  simp [pauliPairing, pauliFamily, OneLoop.pauliY, Matrix.trace_fin_two, Matrix.mul_apply,
    Fin.sum_univ_two]
  ring
theorem pauliPairing_two (M : ComplexMatrix2) :
    pauliPairing 2 M = (1 / 2 : ℂ) * (M 0 0 - M 1 1) := by
  simp [pauliPairing, pauliFamily, OneLoop.pauliZ, Matrix.trace_fin_two, Matrix.mul_apply,
    Fin.sum_univ_two]
  ring
theorem pauliPairing_eq_ofReal (a : Fin 3) (Y : ComplexMatrix2.LieElement) :
    pauliPairing a Y.toMatrix = (pauliCoeff a Y : ℂ) := by
  have h := ComplexMatrix2.LieElement.star_fullTrace_mul Y (pauliLie a)
  have hm : (pauliLie a).toMatrix = pauliFamily a := rfl
  rw [hm] at h
  apply Complex.ext
  · simp [pauliCoeff_apply]
  · have him : (ComplexMatrix2.fullTrace (Y.toMatrix * pauliFamily a)).im = 0 :=
      Complex.conj_eq_iff_im.1 h
    simp only [pauliPairing, LinearMap.coe_mk, AddHom.coe_mk, Complex.ofReal_im]
    simp only [ComplexMatrix2.fullTrace] at him
    simp [Complex.mul_im, him]
theorem toMatrix_eq_sum_pauli (Y : ComplexMatrix2.LieElement) :
    Y.toMatrix = ∑ a, (pauliCoeff a Y : ℂ) • pauliFamily a := by
  have h0 := pauliPairing_eq_ofReal 0 Y
  have h1 := pauliPairing_eq_ofReal 1 Y
  have h2 := pauliPairing_eq_ofReal 2 Y
  rw [pauliPairing_zero] at h0
  rw [pauliPairing_one] at h1
  rw [pauliPairing_two] at h2
  have ht : Y.toMatrix 0 0 + Y.toMatrix 1 1 = 0 := by
    have h' : Matrix.trace Y.toMatrix = 0 := Y.2.2
    simpa [Matrix.trace_fin_two] using h'
  have hI := Complex.I_sq
  simp only [Fin.sum_univ_three, ← h0, ← h1, ← h2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliFamily, OneLoop.pauliX, OneLoop.pauliY, OneLoop.pauliZ]
  · linear_combination (1 / 2 : ℂ) * ht
  · linear_combination (1 / 2 : ℂ) * (Y.toMatrix 0 1 - Y.toMatrix 1 0) * hI
  · linear_combination (-1 / 2 : ℂ) * (Y.toMatrix 0 1 - Y.toMatrix 1 0) * hI
  · linear_combination (1 / 2 : ℂ) * ht
theorem pauliCoeff_pauliLie (a c : Fin 3) :
    pauliCoeff a (pauliLie c) = if a = c then 1 else 0 := by
  have hm : (pauliLie c).toMatrix = pauliFamily c := rfl
  rw [pauliCoeff_apply, hm]
  fin_cases a <;> fin_cases c <;>
    simp [pauliPairing_zero, pauliPairing_one, pauliPairing_two, pauliFamily, OneLoop.pauliX,
      OneLoop.pauliY, OneLoop.pauliZ] <;> norm_num
variable {σ : Type} [Fintype σ]
theorem toMatrix_ofCoeffs (y : σ → Fin 3 → ℝ) (s : σ) :
    (ofCoeffs y s).toMatrix = ∑ a, (y s a : ℂ) • pauliFamily a := by
  rw [← toMatrixLinear_apply, ofCoeffs, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, toMatrixLinear_apply, Complex.coe_smul]
  rfl
theorem pauliCoeff_ofCoeffs (y : σ → Fin 3 → ℝ) (s : σ) (a : Fin 3) :
    pauliCoeff a (ofCoeffs y s) = y s a := by
  simp [ofCoeffs, map_sum, pauliCoeff_pauliLie]
theorem ofCoeffs_pauliCoeff (Y : σ → ComplexMatrix2.LieElement) :
    ofCoeffs (fun s a => pauliCoeff a (Y s)) = Y := by
  funext s
  apply lieElement_ext
  rw [toMatrix_ofCoeffs, ← toMatrix_eq_sum_pauli]
def familyCoeffEquiv {N : ℕ} (κ : σ × Fin 3 ≃ Fin N) :
    (σ → ComplexMatrix2.LieElement) ≃ₗ[ℝ] (Fin N → ℝ) where
  toFun Y i := pauliCoeff (κ.symm i).2 (Y (κ.symm i).1)
  invFun u := ofCoeffs fun s a => u (κ (s, a))
  map_add' Y Y' := by
    funext i
    simp
  map_smul' r Y := by
    funext i
    simp
  left_inv Y := by
    simp [ofCoeffs_pauliCoeff]
  right_inv u := by
    funext i
    simp [pauliCoeff_ofCoeffs]
theorem sum_pauliCoeff_sq (Y : ComplexMatrix2.LieElement) :
    ∑ a, pauliCoeff a Y ^ 2 = ComplexMatrix2.operatorNorm Y.toMatrix ^ 2 := by
  have hI := Complex.I_sq
  have hMM : Y.toMatrix * Y.toMatrix =
      ((∑ a, pauliCoeff a Y ^ 2 : ℝ) : ℂ) • (1 : ComplexMatrix2) := by
    conv_lhs => rw [toMatrix_eq_sum_pauli Y]
    simp only [Fin.sum_univ_three]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, pauliFamily, OneLoop.pauliX, OneLoop.pauliY,
        OneLoop.pauliZ]
    · linear_combination (-(pauliCoeff 1 Y : ℂ) ^ 2) * hI
    · ring
    · ring
    · linear_combination (-(pauliCoeff 1 Y : ℂ) ^ 2) * hI
  have hs : star Y.toMatrix = Y.toMatrix := Y.2.1.symm
  have hn := CStarRing.norm_star_mul_self (x := Y.toMatrix)
  rw [hs, hMM, norm_smul, CStarRing.norm_one, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg fun a _ => sq_nonneg _)] at hn
  rw [hn, sq]
end Pauli
section Chart
variable (σ : Type) [Fintype σ]
def indexEnum : IndexEnum σ :=
  Fintype.equivFinOfCardEq (by simp [Nat.mul_comm])
def chartIndexEquiv : σ × Fin 3 ≃ Fin (0 + 3 * Fintype.card σ) :=
  (indexEnum σ).trans (finCongr (Nat.zero_add _).symm)
def pauliCoords : (σ → ComplexMatrix2.LieElement) ≃ₗ[ℝ] (Fin (0 + 3 * Fintype.card σ) → ℝ) :=
  familyCoeffEquiv (chartIndexEquiv σ)
def basisOfEmpty : Module.Basis (Fin 0) ℝ (hermitianTracelessFunctions Empty) :=
  Module.Basis.empty _
def onePoint : σ ⊕ Empty → ComplexMatrix2 := asGroupFactors (oneFamily σ)
def productChart (z : ComplexCoordinates (0 + 3 * Fintype.card σ)) : σ ⊕ Empty → ComplexMatrix2 :=
  basisExpChart (basisOfEmpty) (indexEnum σ) (onePoint σ) z
variable {σ}
theorem asGroupFactors_injective :
    Function.Injective (asGroupFactors : (σ → ComplexMatrix2) → σ ⊕ Empty → ComplexMatrix2) := by
  intro X X' h
  funext s
  exact congrFun h (.inl s)
theorem groupComponent_asGroupFactors (X : σ → ComplexMatrix2) :
    groupComponent (asGroupFactors X) = X := rfl
theorem realEmbed_injective {N : ℕ} :
    Function.Injective (realEmbed : (Fin N → ℝ) → ComplexCoordinates N) := by
  intro u v h
  funext i
  exact Complex.ofReal_injective (congrFun h i)
theorem re_realEmbed {N : ℕ} (u : Fin N → ℝ) :
    (fun i => (realEmbed u i).re) = u := by
  funext i
  simp [realEmbed]
theorem realEmbed_mem_realLocus {N : ℕ} (u : Fin N → ℝ) :
    realEmbed u ∈ ComplexCoordinates.realLocus N := by
  intro j
  simp [realEmbed]
theorem realEmbed_re {N : ℕ} {z : ComplexCoordinates N} (hz : z ∈ ComplexCoordinates.realLocus N) :
    realEmbed (fun i => (z i).re) = z := by
  funext i
  apply Complex.ext
  · simp [realEmbed]
  · simpa [realEmbed] using (hz i).symm
theorem natAdd_indexEnum (p : σ × Fin 3) : Fin.natAdd 0 (indexEnum σ p) = chartIndexEquiv σ p := by
  apply Fin.ext
  simp [chartIndexEquiv]
theorem productChart_realEmbed (u : Fin (0 + 3 * Fintype.card σ) → ℝ) :
    productChart σ (realEmbed u) = asGroupFactors (expFamily ((pauliCoords σ).symm u)) := by
  funext q
  rcases q with s | k
  · have hsym : (pauliCoords σ).symm u = ofCoeffs fun s a => u (chartIndexEquiv σ (s, a)) := rfl
    have hcomb : pauliSum (angularPart (indexEnum σ) (realEmbed u)) s =
        (((pauliCoords σ).symm u) s).toMatrix := by
      rw [hsym, toMatrix_ofCoeffs]
      simp only [pauliSum, angularPart, natAdd_indexEnum, realEmbed]
    simp only [productChart, basisExpChart, ofParts, Sum.elim_inl]
    rw [hcomb]
    simp [groupComponent, onePoint, asGroupFactors, oneFamily, expFamily]
  · exact k.elim
theorem pauliCoords_chartIndex (Y : σ → ComplexMatrix2.LieElement) (s : σ) (a : Fin 3) :
    pauliCoords σ Y (chartIndexEquiv σ (s, a)) = pauliCoeff a (Y s) := by
  simp [pauliCoords, familyCoeffEquiv]
theorem mem_lieBall_iff [Nonempty σ] {ε : ℝ} {Y : σ → ComplexMatrix2.LieElement} :
    Y ∈ lieBall σ ε ↔ ∀ s, ComplexMatrix2.operatorNorm (Y s).toMatrix < ε := by
  have hb : BddAbove (range fun s => ComplexMatrix2.operatorNorm (toMatrices Y s)) :=
    (finite_range _).bddAbove
  constructor
  · intro h s
    exact (le_ciSup hb s).trans_lt h
  · intro h
    obtain ⟨s, hs⟩ :=
      exists_eq_ciSup_of_finite (f := fun s => ComplexMatrix2.operatorNorm (toMatrices Y s))
    change (⨆ s, ComplexMatrix2.operatorNorm (toMatrices Y s)) < ε
    rw [← hs]
    exact h s
theorem continuous_toMatrix : Continuous fun Y : ComplexMatrix2.LieElement => Y.toMatrix :=
  toMatrixLinear.continuous_of_finiteDimensional
theorem continuous_expFamily : Continuous (expFamily (σ := σ)) := by
  refine continuous_pi fun s => ?_
  have h0 : Continuous fun Y : σ → ComplexMatrix2.LieElement => (Y s).toMatrix :=
    continuous_toMatrix.comp (continuous_apply s)
  have h1 : Continuous fun Y : σ → ComplexMatrix2.LieElement => Complex.I • (Y s).toMatrix :=
    (continuous_const_smul Complex.I).comp h0
  let +nondep : NormedAlgebra ℚ ComplexMatrix2 := .restrictScalars ℚ ℂ ComplexMatrix2
  exact (NormedSpace.exp_continuous).comp h1
theorem isOpen_lieBall [Nonempty σ] {ε : ℝ} : IsOpen (lieBall σ ε) := by
  have hEq : lieBall σ ε =
      ⋂ s, {Y | ComplexMatrix2.operatorNorm ((Y : σ → ComplexMatrix2.LieElement) s).toMatrix < ε} := by
    ext Y
    simp [mem_lieBall_iff]
  rw [hEq]
  refine isOpen_iInter_of_finite fun s => ?_
  exact isOpen_lt (continuous_norm.comp (continuous_toMatrix.comp (continuous_apply s)))
    continuous_const
theorem isOpen_pullbackDomain [Nonempty σ] (hE : specialUnitaryPower.IsOpenSubset (expImage σ))
    {O : Set (σ → ComplexMatrix2)} (hO : specialUnitaryPower.IsOpenSubset O) :
    IsOpen (pullbackDomain O) := by
  obtain ⟨U, hU, rfl⟩ := hO
  have hsub : expImage σ ⊆ specialUnitaryPower σ := by
    obtain ⟨U', _, hU'⟩ := hE
    rw [hU']
    exact inter_subset_right
  have hEq : pullbackDomain (U ∩ specialUnitaryPower σ) = lieBall σ (1 / 2) ∩ expFamily ⁻¹' U := by
    ext Y
    constructor
    · rintro ⟨h1, h2, _⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2, hsub ⟨Y, h1, rfl⟩⟩
  rw [hEq]
  exact isOpen_lieBall.inter (hU.preimage continuous_expFamily)
def coordImage (D : Set (σ → ComplexMatrix2.LieElement)) :
    Set (ComplexCoordinates (0 + 3 * Fintype.card σ)) :=
  realEmbed '' (pauliCoords σ '' D)
theorem continuous_linearEquiv_symm {N : ℕ} (x : (σ → ComplexMatrix2.LieElement) ≃ₗ[ℝ] (Fin N → ℝ)) :
    Continuous x.symm := x.symm.toLinearMap.continuous_of_finiteDimensional
theorem isOpen_linearEquiv_image {N : ℕ} (x : (σ → ComplexMatrix2.LieElement) ≃ₗ[ℝ] (Fin N → ℝ))
    {D : Set (σ → ComplexMatrix2.LieElement)} (hD : IsOpen D) : IsOpen (x '' D) := by
  have hEq : x '' D = x.symm ⁻¹' D := x.toEquiv.image_eq_preimage_symm D
  rw [hEq]
  exact hD.preimage (continuous_linearEquiv_symm x)
theorem coordImage_subset [Nonempty σ] {D : Set (σ → ComplexMatrix2.LieElement)}
    (hD : D ⊆ lieBall σ (1 / 2)) :
    coordImage D ⊆ basisExpChartSource 0 (indexEnum σ) := by
  rintro _ ⟨_, ⟨Y, hY, rfl⟩, rfl⟩
  refine ⟨realEmbed_mem_realLocus _, fun ρ => ?_⟩
  have hc : ∀ a, (angularPart (indexEnum σ) (realEmbed (pauliCoords σ Y)) ρ a).re =
      pauliCoeff a (Y ρ) := by
    intro a
    simp [angularPart, natAdd_indexEnum, realEmbed, pauliCoords_chartIndex]
  simp only [hc, sum_pauliCoeff_sq]
  have h1 := mem_lieBall_iff.1 (hD hY) ρ
  have h2 : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  exact pow_lt_pow_left₀ (h1.trans h2) (norm_nonneg _) (by norm_num)
theorem isRelativelyOpen_coordImage [Nonempty σ] {D : Set (σ → ComplexMatrix2.LieElement)}
    (hDo : IsOpen D) (hD : D ⊆ lieBall σ (1 / 2)) :
    ComplexMatrix2.IsRelativelyOpen (basisExpChartSource 0 (indexEnum σ)) (coordImage D) := by
  obtain ⟨U, hU, hUD⟩ :=
    isRelativelyOpen_realEmbed_image (isOpen_linearEquiv_image (pauliCoords σ) hDo)
  refine ⟨U, hU, ?_⟩
  apply Subset.antisymm
  · intro z hz
    exact ⟨(hUD.le hz).1, coordImage_subset hD hz⟩
  · rintro z ⟨hzU, hz⟩
    exact hUD.ge ⟨hzU, hz.1⟩
theorem productChart_image_coordImage {O : Set (σ → ComplexMatrix2)} (hOE : O ⊆ expImage σ) :
    productChart σ '' coordImage (pullbackDomain O) = asGroupFactors '' O := by
  ext q
  constructor
  · rintro ⟨_, ⟨_, ⟨Y, hY, rfl⟩, rfl⟩, rfl⟩
    rw [productChart_realEmbed, LinearEquiv.symm_apply_apply]
    exact ⟨_, hY.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨Y, hY, rfl⟩ := hOE hx
    refine ⟨_, ⟨_, ⟨Y, ⟨hY, hx⟩, rfl⟩, rfl⟩, ?_⟩
    rw [productChart_realEmbed, LinearEquiv.symm_apply_apply]
end Chart
section Comparison
variable {σ T : Type} [Fintype σ] {l : ℕ}
theorem realAnalyticVia_of_extensions
    (hH : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {e : T → ComplexCoordinates l} {D : Set (σ → ComplexMatrix2.LieElement)}
    {g : (σ → ComplexMatrix2.LieElement) → T}
    {G : ComplexCoordinates (0 + 3 * Fintype.card σ) → ComplexCoordinates l} (hD : IsOpen D)
    (hT : HasLocalHolomorphicExtensions (coordImage D) G)
    (hG : ∀ Y ∈ D, G (realEmbed (pauliCoords σ Y)) = e (g Y)) :
    IsRealAnalyticVia e D g := by
  refine ⟨hD, fun N x => ⟨isRelativelyOpen_realEmbed_image (isOpen_linearEquiv_image x hD), ?_⟩⟩
  rintro _ ⟨_, ⟨Y, hY, rfl⟩, rfl⟩
  obtain ⟨𝒩, h𝒩, hζ, hsub, h, hh, heq⟩ :=
    hT (realEmbed (pauliCoords σ Y)) ⟨_, ⟨Y, hY, rfl⟩, rfl⟩
  let R : (Fin N → ℝ) →ₗ[ℝ] (Fin (0 + 3 * Fintype.card σ) → ℝ) :=
    (pauliCoords σ).toLinearMap ∘ₗ x.symm.toLinearMap
  have hLc : Continuous (complexExtension R) := (complexExtension R).continuous_of_finiteDimensional
  have hopen : IsOpen (complexExtension R ⁻¹' 𝒩) := h𝒩.preimage hLc
  have hcomp : ComplexCoordinates.IsHolomorphicIn (complexExtension R ⁻¹' 𝒩) (h ∘ complexExtension R) :=
    ((hH.1 _ 𝒩 h𝒩).1 _ h hh).2.2.2.1 _ _ _ (isHolomorphicIn_linearMap hopen (complexExtension R))
      fun z hz => hz
  have hra := ((hH.1 _ _ hopen).1 _ _ hcomp).2.2.2.2
  have hLx : ∀ Y' : σ → ComplexMatrix2.LieElement, complexExtension R (realEmbed (x Y')) =
      realEmbed (pauliCoords σ Y') := by
    intro Y'
    rw [complexExtension_realEmbed]
    simp [R]
  have ha : realEmbed (x Y) ∈ complexExtension R ⁻¹' 𝒩 := by
    change complexExtension R _ ∈ 𝒩
    rw [hLx]
    exact hζ
  obtain ⟨c, hc⟩ := hra.2 _ ⟨ha, realEmbed_mem_realLocus _⟩
  refine ⟨c, ?_⟩
  filter_upwards [hc, nhdsWithin_le_nhds (hopen.mem_nhds ha), self_mem_nhdsWithin] with z hz hz𝒩 hzr
  set Y' := x.symm fun i => (z i).re with hY'
  have hzY : z = realEmbed (x Y') := by
    rw [hY', LinearEquiv.apply_symm_apply, realEmbed_re hzr]
  have hL : complexExtension R z = realEmbed (pauliCoords σ Y') := by
    rw [hzY, hLx]
  have hm : realEmbed (pauliCoords σ Y') ∈ 𝒩 := by
    rw [← hL]
    exact hz𝒩
  have hY'D : Y' ∈ D := by
    obtain ⟨_, ⟨Y'', hY'', rfl⟩, hYY⟩ := hsub ⟨hm, realEmbed_mem_realLocus _⟩
    have hinj := (pauliCoords σ).injective (realEmbed_injective hYY)
    rwa [← hinj]
  have hval : h (complexExtension R z) = e (g Y') := by
    rw [hL, heq ⟨hm, realEmbed_mem_realLocus _⟩, hG Y' hY'D]
  have hgoal := hz
  simp only [Function.comp_apply] at hgoal
  rw [hval] at hgoal
  exact hgoal
theorem productChart_properties (hK : AnalyticCalculusStatement) (σ τ : Type) [Fintype σ]
    [Fintype τ] :
    BasisExpChartIsChart (basisOfEmpty) (indexEnum σ) (onePoint σ) ∧
      AnalyticInChartOfAnalytic (hermitianTracelessFunctions Empty) τ
        (basisOfEmpty) (indexEnum σ) (onePoint σ) ∧
      AnalyticOfAnalyticInChart (basisOfEmpty) (indexEnum σ) (onePoint σ) := by
  have hE : hermitianTracelessFunctions Empty ≤ hermitianTracelessFunctions Empty := le_rfl
  refine ((hK Empty σ Empty τ).2.2.2 _ _ hE hE).2.2.2 0 _ _ _ ?_
  refine ⟨?_, ?_⟩
  · intro k
    exact k.elim
  · intro s
    exact one_mem (ComplexMatrix2.specialUnitary)
theorem realAnalytic_iff_via_expFamily
    (hH : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hK : AnalyticCalculusStatement) [Nonempty σ]
    (hE : specialUnitaryPower.IsOpenSubset (expImage σ)) {O : Set (σ → ComplexMatrix2)}
    (hO : specialUnitaryPower.IsOpenSubset O) (hOE : O ⊆ expImage σ) (e : T → ComplexCoordinates l)
    (f : (σ → ComplexMatrix2) → T) :
    IsSubspaceAnalyticToCoords (hermitianTracelessFunctions Empty) (asGroupFactors '' O)
        (fun q => e (f (groupComponent q))) ↔
      IsRealAnalyticVia e (pullbackDomain O) (f ∘ expFamily) := by
  have hD := isOpen_pullbackDomain hE hO
  have hsm : pullbackDomain O ⊆ lieBall σ (1 / 2) := fun Y hY => hY.1
  have hTo := isRelativelyOpen_coordImage hD hsm
  obtain ⟨-, hread, hback⟩ := productChart_properties hK σ σ
  have himg : basisExpChart (basisOfEmpty) (indexEnum σ) (onePoint σ) ''
      coordImage (pullbackDomain O) = asGroupFactors '' O := productChart_image_coordImage hOE
  constructor
  · intro h
    have hr := (hread _ hTo).1 l (fun q => e (f (groupComponent q))) (by rw [himg]; exact h)
    refine realAnalyticVia_of_extensions hH hD hr.1 fun Y _ => ?_
    change e (f (groupComponent (productChart σ (realEmbed _)))) = _
    rw [productChart_realEmbed, LinearEquiv.symm_apply_apply]
    rfl
  · intro h
    have hra := h.2 _ (pauliCoords σ)
    have h2 : ComplexCoordinates.IsRealAnalyticIn (coordImage (pullbackDomain O))
        ((fun q => e (f (groupComponent q))) ∘
          basisExpChart (basisOfEmpty) (indexEnum σ) (onePoint σ)) := by
      refine isRealAnalyticIn_congr hra ?_
      rintro _ ⟨_, ⟨Y, hY, rfl⟩, rfl⟩
      change _ = e (f (groupComponent (productChart σ (realEmbed _))))
      rw [productChart_realEmbed]
      beta_reduce
      rw [re_realEmbed, LinearEquiv.symm_apply_apply]
      rfl
    have h3 := hback _ hTo l _ h2
    rwa [himg] at h3
end Comparison
section Holomorphic
variable {ι κ E E' : Type} [Fintype ι] [Fintype κ] {m m' : ℕ}
theorem isHolomorphicIn_comp (hH : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {N N' N'' : ℕ} {U : Set (ComplexCoordinates N)} {U' : Set (ComplexCoordinates N'')}
    {h : ComplexCoordinates N → ComplexCoordinates N'} {g : ComplexCoordinates N'' → ComplexCoordinates N}
    (hh : ComplexCoordinates.IsHolomorphicIn U h) (hg : ComplexCoordinates.IsHolomorphicIn U' g)
    (hm : MapsTo g U' U) : ComplexCoordinates.IsHolomorphicIn U' (h ∘ g) :=
  ((hH.1 _ U hh.1).1 _ h hh).2.2.2.1 _ _ _ hg hm
theorem isHolomorphicToCoords_postcomp
    (hH : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {e : E ≃ ComplexCoordinates m}
    (e' : E' ≃ ComplexCoordinates m')
    {W : Set (ι ⊕ κ → ComplexMatrix2)} {Φ : (ι ⊕ κ → ComplexMatrix2) → E}
    {U : Set (ComplexCoordinates m)}
    {h : ComplexCoordinates m → ComplexCoordinates m'} (hU : ComplexCoordinates.IsHolomorphicIn U h)
    (hm : ∀ q ∈ W, e (Φ q) ∈ U) (hΦ : IsHolomorphicToCoords b e W Φ) :
    IsHolomorphicToCoords b e' W fun q => e'.symm (h (e (Φ q))) := by
  refine ⟨hΦ.1, ?_, fun p hp => ?_⟩
  · have hc : ContinuousOn (h ∘ (e ∘ Φ)) W := hU.2.1.comp hΦ.2.1 hm
    exact hc.congr fun q _ => by simp
  · obtain ⟨O, h0, hOW, hOT⟩ := hΦ.2.2 p hp
    refine ⟨O, h0, hOW, hOT.1, fun ν => ?_⟩
    have h2 := isHolomorphicIn_comp hH hU (hOT.2 ν) fun w hw => hm _ (hOW _ hw)
    convert h2 using 1
    funext w
    simp
theorem isRelativelyOpen_inter_preimage {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {P W : Set X} {F : X → Y} {U : Set Y} (hW : ComplexMatrix2.IsRelativelyOpen P W)
    (hc : ContinuousOn F W) (hU : IsOpen U) : ComplexMatrix2.IsRelativelyOpen P (W ∩ F ⁻¹' U) := by
  obtain ⟨B, hB, hBe⟩ := continuousOn_iff'.1 hc U hU
  obtain ⟨A, hA, rfl⟩ := hW
  refine ⟨A ∩ B, hA.inter hB, ?_⟩
  ext q
  have hq := Set.ext_iff.1 hBe q
  simp only [mem_inter_iff, mem_preimage] at hq ⊢
  tauto
def matrixLinearEquiv : ComplexMatrix2 ≃ₗ[ℂ] ComplexCoordinates 4 :=
  { ComplexCoordinates.matrixEquiv with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
theorem matrixLinearEquiv_apply (M : ComplexMatrix2) :
    matrixLinearEquiv M = ComplexCoordinates.matrixEquiv M := rfl
theorem matrixLinearEquiv_symm_apply (z : ComplexCoordinates 4) :
    matrixLinearEquiv.symm z = ComplexCoordinates.matrixEquiv.symm z := rfl
def inMatrixCoords (A : ComplexMatrix2 →ₗ[ℂ] ComplexMatrix2) :
    ComplexCoordinates 4 →ₗ[ℂ] ComplexCoordinates 4 :=
  matrixLinearEquiv.toLinearMap ∘ₗ A ∘ₗ matrixLinearEquiv.symm.toLinearMap
theorem inMatrixCoords_apply (A : ComplexMatrix2 →ₗ[ℂ] ComplexMatrix2) (M : ComplexMatrix2) :
    inMatrixCoords A (ComplexCoordinates.matrixEquiv M) =
      ComplexCoordinates.matrixEquiv (A M) := by
  simp [inMatrixCoords, matrixLinearEquiv_apply, matrixLinearEquiv_symm_apply]
def tracelessProj : ComplexMatrix2 →ₗ[ℂ] ComplexMatrix2 :=
  LinearMap.id - (LinearMap.toSpanSingleton ℂ ComplexMatrix2 1) ∘ₗ
    ((1 / 2 : ℂ) • Matrix.traceLinearMap (Fin 2) ℂ ℂ)
theorem tracelessProj_apply (M : ComplexMatrix2) :
    tracelessProj M = M - ((1 / 2 : ℂ) * Matrix.trace M) • (1 : ComplexMatrix2) := by
  simp [tracelessProj]
theorem trace_tracelessProj (M : ComplexMatrix2) : Matrix.trace (tracelessProj M) = 0 := by
  rw [tracelessProj_apply, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one]
  simp
  ring
def logInCoords (z : ComplexCoordinates 4) : ComplexCoordinates 4 :=
  ComplexCoordinates.matrixEquiv (ComplexMatrix2.logSeries (ComplexCoordinates.matrixEquiv.symm z))
def expInCoords (z : ComplexCoordinates 4) : ComplexCoordinates 4 :=
  ComplexCoordinates.matrixEquiv (ComplexMatrix2.matExp (ComplexCoordinates.matrixEquiv.symm z))
def detFixSource (g : ComplexMatrix2) : Set (ComplexCoordinates 4) :=
  inMatrixCoords (LinearMap.mulRight ℂ g⁻¹) ⁻¹'
    (ComplexCoordinates.matrixEquiv '' ComplexMatrix2.logBall)
def detFix (g : ComplexMatrix2) : ComplexCoordinates 4 → ComplexCoordinates 4 :=
  inMatrixCoords (LinearMap.mulRight ℂ g) ∘ expInCoords ∘ inMatrixCoords tracelessProj ∘
    logInCoords ∘ inMatrixCoords (LinearMap.mulRight ℂ g⁻¹)
theorem detFix_apply (g M : ComplexMatrix2) :
    detFix g (ComplexCoordinates.matrixEquiv M) =
      ComplexCoordinates.matrixEquiv
        (ComplexMatrix2.matExp (tracelessProj (ComplexMatrix2.logSeries (M * g⁻¹))) * g) := by
  simp [detFix, inMatrixCoords_apply, logInCoords, expInCoords]
theorem isHolomorphicIn_logInCoords (hH : ComplexCoordinates.PowerSeriesHolomorphy.Properties) :
    ComplexCoordinates.IsHolomorphicIn (ComplexCoordinates.matrixEquiv '' ComplexMatrix2.logBall)
      logInCoords := hH.2.2.2.2.2
theorem isHolomorphicIn_expInCoords (hH : ComplexCoordinates.PowerSeriesHolomorphy.Properties) :
    ComplexCoordinates.IsHolomorphicIn univ expInCoords := by
  have h := hH.2.2.2.2.1
  have himg : ComplexCoordinates.matrixEquiv '' (univ : Set ComplexMatrix2) = univ :=
    ComplexCoordinates.matrixEquiv.surjective.range_eq ▸ image_univ
  unfold ComplexCoordinates.IsHolomorphicVia at h
  rw [himg] at h
  exact h
theorem isOpen_detFixSource (hH : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (g : ComplexMatrix2) : IsOpen (detFixSource g) :=
  (isHolomorphicIn_logInCoords hH).1.preimage
    (inMatrixCoords (LinearMap.mulRight ℂ g⁻¹)).continuous_of_finiteDimensional
theorem isHolomorphicIn_detFix (hH : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (g : ComplexMatrix2) : ComplexCoordinates.IsHolomorphicIn (detFixSource g) (detFix g) := by
  have h1 := isHolomorphicIn_linearMap (isOpen_detFixSource hH g)
    (inMatrixCoords (LinearMap.mulRight ℂ g⁻¹))
  have h2 := isHolomorphicIn_comp hH (isHolomorphicIn_logInCoords hH) h1 fun z hz => hz
  have h3 := isHolomorphicIn_comp hH
    (isHolomorphicIn_linearMap isOpen_univ (inMatrixCoords tracelessProj)) h2 (mapsTo_univ _ _)
  have h4 := isHolomorphicIn_comp hH (isHolomorphicIn_expInCoords hH) h3 (mapsTo_univ _ _)
  exact isHolomorphicIn_comp hH
    (isHolomorphicIn_linearMap isOpen_univ (inMatrixCoords (LinearMap.mulRight ℂ g)))
    h4 (mapsTo_univ _ _)
end Holomorphic
section Unimodular
variable {σ τ : Type} [Fintype σ] [Fintype τ]
theorem specialUnitary_inv {g : ComplexMatrix2} (hg : g ∈ ComplexMatrix2.specialUnitary) :
    g⁻¹ ∈ ComplexMatrix2.specialUnitary ∧ g * g⁻¹ = 1 ∧ g⁻¹ * g = 1 := by
  obtain ⟨hu, hd⟩ := Matrix.mem_specialUnitaryGroup_iff.1 hg
  have h1 : g * star g = 1 := Matrix.mem_unitaryGroup_iff.1 hu
  have h2 : star g * g = 1 := Matrix.mem_unitaryGroup_iff'.1 hu
  have hinv : g⁻¹ = star g := Matrix.inv_eq_right_inv h1
  rw [hinv]
  refine ⟨Matrix.mem_specialUnitaryGroup_iff.2 ⟨?_, ?_⟩, h1, h2⟩
  · rw [Matrix.mem_unitaryGroup_iff, star_star]
    exact h2
  · rw [Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, hd, star_one]
theorem detFix_value_eq (hL : ComplexMatrix2.ExpLogEstimates) {g X : ComplexMatrix2}
    (hg : g ∈ ComplexMatrix2.specialUnitary) (hX : X ∈ ComplexMatrix2.specialUnitary)
    (hd : X * g⁻¹ ∈ ComplexMatrix2.logBall) :
    ComplexMatrix2.matExp (tracelessProj (ComplexMatrix2.logSeries (X * g⁻¹))) * g = X := by
  obtain ⟨hgi, -, hgg⟩ := specialUnitary_inv hg
  have hA : X * g⁻¹ ∈ ComplexMatrix2.specialUnitary := mul_mem hX hgi
  obtain ⟨hu, hdet⟩ := Matrix.mem_specialUnitaryGroup_iff.1 hA
  obtain ⟨H, -, hlog, -, hexp, -, hrest⟩ := hL.2.2.2.2.2.2.2.1 _ hu hd
  have htr : Matrix.trace H = 0 := (hrest hdet).1
  have hP : tracelessProj (ComplexMatrix2.logSeries (X * g⁻¹)) =
      ComplexMatrix2.logSeries (X * g⁻¹) := by
    rw [tracelessProj_apply, hlog, Matrix.trace_smul, htr]
    simp
  rw [hP, hlog, hexp, mul_assoc, hgg, mul_one]
theorem det_detFix_value (hL : ComplexMatrix2.ExpLogEstimates) {g : ComplexMatrix2}
    (hg : g ∈ ComplexMatrix2.specialUnitary) (M : ComplexMatrix2) :
    (ComplexMatrix2.matExp (tracelessProj M) * g).det = 1 := by
  have hd := (Matrix.mem_specialUnitaryGroup_iff.1 hg).2
  rw [Matrix.det_mul, hL.2.2.2.2.2.1, hd, mul_one]
  simp [ComplexMatrix2.fullTrace, trace_tracelessProj]
theorem exists_unimodular_extension (hH : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hC : GroupLieProduct.HolomorphicCalculus.Properties) (hL : ComplexMatrix2.ExpLogEstimates)
    {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {O : Set (σ → ComplexMatrix2)}
    {F : (σ → ComplexMatrix2) → ComplexMatrix2}
    (hFG : ∀ x ∈ O, F x ∈ ComplexMatrix2.specialUnitary)
    (hF : IsLocallyHolomorphicRestriction (HolomorphicMatrix b) id O F) {p : σ → ComplexMatrix2}
    (hp : p ∈ O) :
    ∃ (W : Set (σ ⊕ Empty → ComplexMatrix2)) (Φ : (σ ⊕ Empty → ComplexMatrix2) → ComplexMatrix2),
      asGroupFactors p ∈ W ∧
      IsHolomorphicToCoords b ComplexCoordinates.matrixEquiv W Φ ∧
      MapsTo Φ W ComplexMatrix2.unitDeterminant ∧
      ∀ x ∈ O, asGroupFactors x ∈ W → Φ (asGroupFactors x) = F x := by
  obtain ⟨W, Φ, hpW, hΦ, hv⟩ := hF p hp
  have hΦ' : IsHolomorphicToCoords b ComplexCoordinates.matrixEquiv W Φ := hΦ
  have hg := hFG p hp
  set g := F p with hgdef
  have hopen := isRelativelyOpen_inter_preimage hΦ'.1 hΦ'.2.1 (isOpen_detFixSource hH g)
  have hres := (hC.2.2.2.2.2.2.2.1 σ Empty) b W _ _ _ _ _ hΦ' hopen inter_subset_left
  have hpost := isHolomorphicToCoords_postcomp hH ComplexCoordinates.matrixEquiv
    (isHolomorphicIn_detFix hH g) (fun q hq => hq.2) hres
  have hform : ∀ q, ComplexCoordinates.matrixEquiv.symm
      (detFix g (ComplexCoordinates.matrixEquiv (Φ q))) =
      ComplexMatrix2.matExp (tracelessProj (ComplexMatrix2.logSeries (Φ q * g⁻¹))) * g := by
    intro q
    rw [detFix_apply, Equiv.symm_apply_apply]
  have hdom : ∀ M, ComplexCoordinates.matrixEquiv M ∈ detFixSource g ↔
      M * g⁻¹ ∈ ComplexMatrix2.logBall := by
    intro M
    change inMatrixCoords (LinearMap.mulRight ℂ g⁻¹) (ComplexCoordinates.matrixEquiv M) ∈
      ComplexCoordinates.matrixEquiv '' ComplexMatrix2.logBall ↔ _
    rw [inMatrixCoords_apply]
    exact ComplexCoordinates.matrixEquiv.injective.mem_set_image
  refine ⟨W ∩ (ComplexCoordinates.matrixEquiv ∘ Φ) ⁻¹' detFixSource g,
    fun q => ComplexCoordinates.matrixEquiv.symm
      (detFix g (ComplexCoordinates.matrixEquiv (Φ q))), ⟨hpW, ?_⟩, hpost, fun q _ => ?_,
    fun x hx hxW => ?_⟩
  · change ComplexCoordinates.matrixEquiv (Φ (asGroupFactors p)) ∈ detFixSource g
    rw [hdom, hv p hp hpW]
    simp only [id]
    rw [← hgdef, (specialUnitary_inv hg).2.1]
    simp [ComplexMatrix2.logBall]
  · change (ComplexCoordinates.matrixEquiv.symm
      (detFix g (ComplexCoordinates.matrixEquiv (Φ q)))).det = 1
    rw [hform]
    exact det_detFix_value hL hg _
  · have hxv : Φ (asGroupFactors x) = F x := hv x hx hxW.1
    beta_reduce
    rw [hform, hxv]
    have hmem : ComplexCoordinates.matrixEquiv (Φ (asGroupFactors x)) ∈ detFixSource g := hxW.2
    rw [hdom, hxv] at hmem
    exact detFix_value_eq hL hg (hFG x hx) hmem
theorem restriction_toProduct_of_components [Nonempty τ]
    (hH : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hC : GroupLieProduct.HolomorphicCalculus.Properties)
    (hX : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (hL : ComplexMatrix2.ExpLogEstimates) {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
    {O : Set (σ → ComplexMatrix2)} {f : (σ → ComplexMatrix2) → τ → ComplexMatrix2}
    (hf : MapsTo f O (specialUnitaryPower τ))
    (hm : ∀ t, IsLocallyHolomorphicRestriction (HolomorphicMatrix b) id O fun x => f x t) :
    IsLocallyHolomorphicRestriction (IsHolomorphicToProduct b) asGroupFactors O f := by
  intro p hp
  choose W Φ hpW hΦ hdet hval using fun t =>
    exists_unimodular_extension hH hC hL (fun x hx => hf hx t) (hm t) hp
  have hopen : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct σ Empty) (⋂ t, W t) := by
    choose U hU hUW using fun t => (hΦ t).1
    refine ⟨⋂ t, U t, isOpen_iInter_of_finite hU, ?_⟩
    ext q
    simp only [mem_iInter, mem_inter_iff]
    constructor
    · intro h
      refine ⟨fun t => ?_, ?_⟩
      · have ht := h t
        rw [hUW t] at ht
        exact ht.1
      · have ht := h (Classical.arbitrary τ)
        rw [hUW _] at ht
        exact ht.2
    · rintro ⟨h1, h2⟩ t
      rw [hUW t]
      exact ⟨h1 t, h2⟩
  refine ⟨⋂ t, W t, fun q => Sum.elim (fun t => Φ t q) Empty.elim, mem_iInter.2 hpW, ?_, ?_⟩
  · refine ⟨hopen, fun t => ?_, fun k => k.elim⟩
    have hres := (hC.2.2.2.2.2.2.2.1 σ Empty) b (W t) _ _ _ _ _ (hΦ t) hopen (iInter_subset _ t)
    refine ((hX.2.2.2.1 σ Empty).2.1 b _ _ hopen fun q hq => ?_).2 hres
    exact hdet t (mem_iInter.1 hq t)
  · intro x hx hxW
    funext i
    rcases i with t | k
    · exact hval t x hx (mem_iInter.1 hxW t)
    · exact k.elim
end Unimodular
section Targets
variable {σ τ : Type} [Fintype σ] [Fintype τ] [Nonempty σ] [Nonempty τ]
theorem isOpenInSubspaceTimesGroup_image (hK : AnalyticCalculusStatement)
    (hE : specialUnitaryPower.IsOpenSubset (expImage σ)) {O : Set (σ → ComplexMatrix2)}
    (hO : specialUnitaryPower.IsOpenSubset O) (hOE : O ⊆ expImage σ) :
    IsOpenInSubspaceTimesGroup (R := σ) (hermitianTracelessFunctions Empty) (asGroupFactors '' O) := by
  have hD := isOpen_pullbackDomain hE hO
  have hTo := isRelativelyOpen_coordImage hD (fun Y hY => hY.1)
  refine ⟨le_rfl, ?_⟩
  have h := (productChart_properties hK σ σ).1.2.2.2.2 _ hTo
  have himg : basisExpChart (basisOfEmpty) (indexEnum σ) (onePoint σ) ''
      coordImage (pullbackDomain O) = asGroupFactors '' O := productChart_image_coordImage hOE
  rwa [himg] at h
theorem power_inChart (hK : AnalyticCalculusStatement)
    (hE : specialUnitaryPower.IsOpenSubset (expImage σ)) {O : Set (σ → ComplexMatrix2)}
    (hO : specialUnitaryPower.IsOpenSubset O) (hOE : O ⊆ expImage σ)
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) :
    (∀ f : (σ → ComplexMatrix2) → ℂ,
      IsSubspaceAnalyticToCoords (hermitianTracelessFunctions Empty) (asGroupFactors '' O)
          (fun q => scalarEquiv (f (groupComponent q))) ↔
        IsLocallyHolomorphicRestriction (HolomorphicScalar b) id O f) ∧
    (∀ f : (σ → ComplexMatrix2) → ComplexMatrix2,
      IsSubspaceAnalyticToCoords (hermitianTracelessFunctions Empty) (asGroupFactors '' O)
          (fun q => ComplexCoordinates.matrixEquiv (f (groupComponent q))) ↔
        IsLocallyHolomorphicRestriction (HolomorphicMatrix b) id O f) ∧
    ∀ f : (σ → ComplexMatrix2) → τ → ComplexMatrix2, MapsTo f O (specialUnitaryPower τ) →
      (IsSubspaceAnalyticToProduct (hermitianTracelessFunctions Empty)
          (hermitianTracelessFunctions Empty) (asGroupFactors '' O)
          (fun q => asGroupFactors (f (groupComponent q))) ↔
        IsLocallyHolomorphicRestriction (IsHolomorphicToProduct b) asGroupFactors O f) := by
  have h := ((hK Empty σ Empty τ).2.2.1 (asGroupFactors '' O)
    (isOpenInSubspaceTimesGroup_image hK hE hO hOE)).2 b
  rw [preimage_image_eq _ asGroupFactors_injective] at h
  exact h
theorem matrix_restriction_iff (hH : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hK : AnalyticCalculusStatement)
    (hE : specialUnitaryPower.IsOpenSubset (expImage σ)) {O : Set (σ → ComplexMatrix2)}
    (hO : specialUnitaryPower.IsOpenSubset O) (hOE : O ⊆ expImage σ)
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (f : (σ → ComplexMatrix2) → ComplexMatrix2) :
    IsLocallyHolomorphicRestriction (HolomorphicMatrix b) id O f ↔
      IsRealAnalyticVia ComplexCoordinates.matrixEquiv (pullbackDomain O) (f ∘ expFamily) :=
  ((power_inChart (τ := σ) hK hE hO hOE b).2.1 f).symm.trans
    (realAnalytic_iff_via_expFamily hH hK hE hO hOE ComplexCoordinates.matrixEquiv f)
theorem scalar_restriction_iff (hH : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hK : AnalyticCalculusStatement)
    (hE : specialUnitaryPower.IsOpenSubset (expImage σ)) {O : Set (σ → ComplexMatrix2)}
    (hO : specialUnitaryPower.IsOpenSubset O) (hOE : O ⊆ expImage σ)
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (f : (σ → ComplexMatrix2) → ℝ) :
    IsLocallyHolomorphicRestriction (HolomorphicScalar b) Complex.ofReal O f ↔
      IsRealAnalyticToRealSpace (pullbackDomain O) (f ∘ expFamily) := by
  have h1 : IsLocallyHolomorphicRestriction (HolomorphicScalar b) Complex.ofReal O f ↔
      IsRealAnalyticVia (fun r : ℝ => scalarEquiv (r : ℂ)) (pullbackDomain O) (f ∘ expFamily) :=
    ((power_inChart (τ := σ) hK hE hO hOE b).1 fun x => (f x : ℂ)).symm.trans
      (realAnalytic_iff_via_expFamily hH hK hE hO hOE (fun r : ℝ => scalarEquiv (r : ℂ)) f)
  rw [h1]
  constructor
  · intro h M y
    let A : ComplexCoordinates 1 →ₗ[ℂ] ComplexCoordinates M :=
      (LinearMap.toSpanSingleton ℂ _ (realEmbed (y 1))) ∘ₗ LinearMap.proj 0
    refine realAnalyticVia_congr (realAnalyticVia_linearMap A h) fun Y _ => ?_
    have hy : y ((f ∘ expFamily) Y) = (f ∘ expFamily) Y • y 1 := by
      rw [← map_smul]
      simp
    rw [hy]
    funext i
    simp [A, realEmbed, scalarEquiv]
  · intro h
    refine realAnalyticVia_congr (h 1 (LinearEquiv.funUnique (Fin 1) ℝ ℝ).symm) fun Y _ => ?_
    funext i
    simp [realEmbed, scalarEquiv]
theorem matrixPiEquiv_asGroupFactors {k : ℕ} (ν : τ ≃ Fin k) (X : τ → ComplexMatrix2) :
    matrixPiEquiv ((Equiv.sumEmpty τ Empty).trans ν) (asGroupFactors X) = matrixPiEquiv ν X := by
  rfl
theorem productEquiv_apply_sigma {k : ℕ} (s : Fin k → ComplexCoordinates.Component)
    (x : ComplexCoordinates.ComponentProduct s) (i : Fin k) (j : Fin (s i).dim) :
    ComplexCoordinates.productEquiv s x (finSigmaFinEquiv ⟨i, j⟩) = (s i).equiv (x i) j := by
  change Sigma.uncurry (fun i => (s i).equiv (x i))
    (finSigmaFinEquiv.symm (finSigmaFinEquiv ⟨i, j⟩)) = _
  rw [Equiv.symm_apply_apply]
  rfl
theorem matrixPiEquiv_component {k : ℕ} (ν : τ ≃ Fin k) (X : τ → ComplexMatrix2) (t : τ)
    (j : Fin 4) :
    matrixPiEquiv ν X (finSigmaFinEquiv
        (⟨ν t, j⟩ : (i : Fin k) × Fin ((fun _ : Fin k => ComplexCoordinates.Component.matrix) i).dim)) =
      ComplexCoordinates.matrixEquiv (X t) j := by
  refine (productEquiv_apply_sigma (fun _ : Fin k => ComplexCoordinates.Component.matrix)
    (fun i => X (ν.symm i)) (ν t) j).trans ?_
  change ComplexCoordinates.matrixEquiv (X (ν.symm (ν t))) j = _
  rw [Equiv.symm_apply_apply]
theorem realAnalyticVia_of_productRestriction
    (hH : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hK : AnalyticCalculusStatement)
    (hE : specialUnitaryPower.IsOpenSubset (expImage σ)) {O : Set (σ → ComplexMatrix2)}
    (hO : specialUnitaryPower.IsOpenSubset O) (hOE : O ⊆ expImage σ)
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) {f : (σ → ComplexMatrix2) → τ → ComplexMatrix2}
    (hf : MapsTo f O (specialUnitaryPower τ))
    (h : IsLocallyHolomorphicRestriction (IsHolomorphicToProduct b) asGroupFactors O f) (k : ℕ)
    (ν : τ ≃ Fin k) :
    IsRealAnalyticVia (matrixPiEquiv ν) (pullbackDomain O) (f ∘ expFamily) := by
  have hD := isOpen_pullbackDomain hE hO
  have hTo := isRelativelyOpen_coordImage hD (fun Y hY => hY.1)
  have himg : basisExpChart (basisOfEmpty) (indexEnum σ) (onePoint σ) ''
      coordImage (pullbackDomain O) = asGroupFactors '' O := productChart_image_coordImage hOE
  have hP := ((power_inChart (τ := τ) hK hE hO hOE b).2.2 f hf).2 h
  have hr := ((productChart_properties hK σ τ).2.1 _ hTo).2 k ((Equiv.sumEmpty τ Empty).trans ν)
    (fun q => asGroupFactors (f (groupComponent q))) (by rw [himg]; exact hP)
  refine realAnalyticVia_of_extensions hH hD hr.1 fun Y _ => ?_
  change matrixPiEquiv _
    (asGroupFactors (f (groupComponent (productChart σ (realEmbed _))))) = _
  rw [productChart_realEmbed, LinearEquiv.symm_apply_apply, matrixPiEquiv_asGroupFactors]
  rfl
def componentCoords {k : ℕ} (ν : τ ≃ Fin k) (t : τ) :
    ComplexCoordinates (ComplexCoordinates.productDim
      fun _ : Fin k => ComplexCoordinates.Component.matrix) →ₗ[ℂ] ComplexCoordinates 4 where
  toFun z j := z (finSigmaFinEquiv
    (⟨ν t, j⟩ : (i : Fin k) × Fin ((fun _ : Fin k => ComplexCoordinates.Component.matrix) i).dim))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem productRestriction_of_realAnalyticVia
    (hH : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hK : AnalyticCalculusStatement) (hC : GroupLieProduct.HolomorphicCalculus.Properties)
    (hX : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (hL : ComplexMatrix2.ExpLogEstimates)
    (hE : specialUnitaryPower.IsOpenSubset (expImage σ)) {O : Set (σ → ComplexMatrix2)}
    (hO : specialUnitaryPower.IsOpenSubset O) (hOE : O ⊆ expImage σ)
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) {f : (σ → ComplexMatrix2) → τ → ComplexMatrix2}
    (hf : MapsTo f O (specialUnitaryPower τ))
    (h : ∀ (k : ℕ) (ν : τ ≃ Fin k),
      IsRealAnalyticVia (matrixPiEquiv ν) (pullbackDomain O) (f ∘ expFamily)) :
    IsLocallyHolomorphicRestriction (IsHolomorphicToProduct b) asGroupFactors O f := by
  refine restriction_toProduct_of_components hH hC hX hL hf fun t => ?_
  refine (matrix_restriction_iff hH hK hE hO hOE b _).2 ?_
  let ν := Fintype.equivFin τ
  refine realAnalyticVia_congr (realAnalyticVia_linearMap (componentCoords ν t) (h _ ν))
    fun Y _ => ?_
  funext j
  exact (matrixPiEquiv_component ν _ t j).symm
end Targets
section Logarithm
variable {σ τ : Type} [Fintype σ] [Fintype τ] [Nonempty σ] [Nonempty τ]
theorem mem_logBall_of_mem_expImage (hL : ComplexMatrix2.ExpLogEstimates) {X : τ → ComplexMatrix2}
    (hX : X ∈ expImage τ) (t : τ) : X t ∈ ComplexMatrix2.logBall := by
  obtain ⟨Y, hY, rfl⟩ := hX
  have h1 := mem_lieBall_iff.1 hY t
  have h2 : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hn : ComplexMatrix2.operatorNorm (Complex.I • (Y t).toMatrix) < Real.log 2 := by
    simp only [ComplexMatrix2.operatorNorm, norm_smul, Complex.norm_I, one_mul]
    exact h1.trans h2
  exact (hL.2.2.2.2.1 _ hn).1
theorem log_component_restriction (hH : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hC : GroupLieProduct.HolomorphicCalculus.Properties)
    (hX : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (hL : ComplexMatrix2.ExpLogEstimates) {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
    {O : Set (σ → ComplexMatrix2)} {f : (σ → ComplexMatrix2) → τ → ComplexMatrix2}
    (hfE : MapsTo f O (expImage τ))
    (h : IsLocallyHolomorphicRestriction (IsHolomorphicToProduct b) asGroupFactors O f) (t : τ) :
    IsLocallyHolomorphicRestriction (HolomorphicMatrix b) id O
      fun x => ComplexMatrix2.logSeries (f x t) := by
  intro p hp
  obtain ⟨W, Ψ, hpW, hΨ, hv⟩ := h p hp
  have hg : IsHolomorphicToUnimodular b W fun q => Ψ q (.inl t) := hΨ.2.1 t
  have hm : IsHolomorphicToCoords b ComplexCoordinates.matrixEquiv W
      fun q => Ψ q (.inl t) := ((hX.2.2.2.1 σ Empty).2.1 b W _ hΨ.1 hg.2.1).1 hg
  have hopen := isRelativelyOpen_inter_preimage hm.1 hm.2.1 (isHolomorphicIn_logInCoords hH).1
  have hres := (hC.2.2.2.2.2.2.2.1 σ Empty) b W _ _ _ _ _ hm hopen inter_subset_left
  have hpost := isHolomorphicToCoords_postcomp hH ComplexCoordinates.matrixEquiv
    (isHolomorphicIn_logInCoords hH) (fun q hq => hq.2) hres
  have hval : ∀ x ∈ O, asGroupFactors x ∈ W → Ψ (asGroupFactors x) (.inl t) = f x t := by
    intro x hx hxW
    rw [hv x hx hxW]
    rfl
  refine ⟨W ∩ (ComplexCoordinates.matrixEquiv ∘ fun q => Ψ q (.inl t)) ⁻¹'
      (ComplexCoordinates.matrixEquiv '' ComplexMatrix2.logBall),
    fun q => ComplexCoordinates.matrixEquiv.symm (logInCoords
      (ComplexCoordinates.matrixEquiv (Ψ q (.inl t)))), ⟨hpW, ?_⟩, hpost, fun x hx hxW => ?_⟩
  · refine ⟨_, mem_logBall_of_mem_expImage hL (hfE hp) t, ?_⟩
    change _ = ComplexCoordinates.matrixEquiv (Ψ (asGroupFactors p) (.inl t))
    rw [hval p hp hpW]
  · simp only [logInCoords, Equiv.symm_apply_apply, id]
    rw [hval x hx hxW.1]
def componentChart {M : ℕ} (v : Fin 3 → ComplexCoordinates M) :
    ComplexCoordinates 4 →ₗ[ℂ] ComplexCoordinates M :=
  ∑ a, (LinearMap.toSpanSingleton ℂ _ (v a)) ∘ₗ
    ((1 / Complex.I) • (pauliPairing a ∘ₗ matrixLinearEquiv.symm.toLinearMap))
theorem componentChart_apply {M : ℕ} (v : Fin 3 → ComplexCoordinates M) (X : ComplexMatrix2) :
    componentChart v (ComplexCoordinates.matrixEquiv X) =
      ∑ a, ((1 / Complex.I) * pauliPairing a X) • v a := by
  simp [componentChart, LinearMap.sum_apply, matrixLinearEquiv_symm_apply]
theorem family_eq_sum_coeffDirection (Y : τ → ComplexMatrix2.LieElement) :
    Y = ∑ t, ∑ a, pauliCoeff a (Y t) • coeffDirection t a := by
  classical
  funext s
  apply lieElement_ext
  rw [toMatrix_eq_sum_pauli (Y s), ← toMatrixLinear_apply, Finset.sum_apply, map_sum]
  rw [Finset.sum_eq_single s]
  · rw [Finset.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Pi.smul_apply, coeffDirection, Pi.single_eq_same, map_smul]
    rw [Complex.coe_smul]
    rfl
  · intro t _ hts
    simp [coeffDirection, Pi.single_eq_of_ne hts.symm]
  · simp
theorem realEmbed_linearEquiv_expand {M : ℕ}
    (y : (τ → ComplexMatrix2.LieElement) ≃ₗ[ℝ] (Fin M → ℝ)) (Y : τ → ComplexMatrix2.LieElement) :
    realEmbed (y Y) = ∑ t, ∑ a, (pauliCoeff a (Y t) : ℂ) • realEmbed (y (coeffDirection t a)) := by
  conv_lhs => rw [family_eq_sum_coeffDirection Y]
  funext i
  simp [realEmbed, map_sum, Finset.sum_apply]
theorem logChart_realAnalytic_of_restriction
    (hH : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hK : AnalyticCalculusStatement) (hC : GroupLieProduct.HolomorphicCalculus.Properties)
    (hX : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (hL : ComplexMatrix2.ExpLogEstimates) (hσ : ExpChartAtOne σ) (hτ : ExpChartAtOne τ)
    {O : Set (σ → ComplexMatrix2)} (hO : specialUnitaryPower.IsOpenSubset O) (hOE : O ⊆ expImage σ)
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) {f : (σ → ComplexMatrix2) → τ → ComplexMatrix2}
    (hfE : MapsTo f O (expImage τ))
    (h : IsLocallyHolomorphicRestriction (IsHolomorphicToProduct b) asGroupFactors O f) :
    IsRealAnalyticToRealSpace (pullbackDomain O) (logChart ∘ f ∘ expFamily) := by
  intro M y
  have hE := hσ.2.1
  have hT : ∀ t, IsRealAnalyticVia
      (fun X : τ → ComplexMatrix2 => componentChart
        (fun a => realEmbed (y (coeffDirection t a)))
        (ComplexCoordinates.matrixEquiv (ComplexMatrix2.logSeries (X t))))
      (pullbackDomain O) (f ∘ expFamily) := by
    intro t
    have h1 := (matrix_restriction_iff hH hK hE hO hOE b _).1
      (log_component_restriction hH hC hX hL hfE h t)
    exact realAnalyticVia_congr (realAnalyticVia_linearMap (componentChart
      (fun a => realEmbed (y (coeffDirection t a)))) h1) fun Y _ => rfl
  refine realAnalyticVia_congr (realAnalyticVia_sum hT) fun Y hY => ?_
  have hmem : f (expFamily Y) ∈ expImage τ := hfE hY.2
  have hmat := hτ.2.2.2.1 _ hmem
  simp only [Function.comp_apply, componentChart_apply]
  rw [realEmbed_linearEquiv_expand]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun a _ => ?_
  congr 1
  rw [← pauliPairing_eq_ofReal]
  have ht := congrFun hmat t
  simp only [toMatrices, logFamily] at ht
  rw [ht, map_smul, smul_eq_mul]
def componentMatrix (t : τ) :
    ComplexCoordinates (0 + 3 * Fintype.card τ) →ₗ[ℂ] ComplexCoordinates 4 :=
  matrixLinearEquiv.toLinearMap ∘ₗ
    ∑ a, (LinearMap.toSpanSingleton ℂ _ (Complex.I • pauliFamily a)) ∘ₗ
      LinearMap.proj (chartIndexEquiv τ (t, a))
theorem componentMatrix_apply (t : τ) (Y : τ → ComplexMatrix2.LieElement) :
    componentMatrix t (realEmbed (pauliCoords τ Y)) =
      ComplexCoordinates.matrixEquiv (Complex.I • (Y t).toMatrix) := by
  rw [toMatrix_eq_sum_pauli (Y t), Finset.smul_sum]
  simp only [componentMatrix, LinearMap.comp_apply, LinearMap.sum_apply, LinearEquiv.coe_coe]
  rw [matrixLinearEquiv_apply]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [LinearMap.proj_apply, LinearMap.toSpanSingleton_apply, realEmbed,
    pauliCoords_chartIndex]
  exact smul_comm _ _ _
theorem restriction_of_logChart_realAnalytic
    (hH : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hK : AnalyticCalculusStatement) (hC : GroupLieProduct.HolomorphicCalculus.Properties)
    (hX : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (hL : ComplexMatrix2.ExpLogEstimates) (hσ : ExpChartAtOne σ) (hτ : ExpChartAtOne τ)
    {O : Set (σ → ComplexMatrix2)} (hO : specialUnitaryPower.IsOpenSubset O) (hOE : O ⊆ expImage σ)
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) {f : (σ → ComplexMatrix2) → τ → ComplexMatrix2}
    (hf : MapsTo f O (specialUnitaryPower τ)) (hfE : MapsTo f O (expImage τ))
    (h : IsRealAnalyticToRealSpace (pullbackDomain O) (logChart ∘ f ∘ expFamily)) :
    IsLocallyHolomorphicRestriction (IsHolomorphicToProduct b) asGroupFactors O f := by
  have hE := hσ.2.1
  have hsub : expImage σ ⊆ specialUnitaryPower σ := by
    obtain ⟨U', _, hU'⟩ := hE
    rw [hU']
    exact inter_subset_right
  have hb := (realAnalytic_iff_via_expFamily hH hK hE hO hOE
    (fun w => realEmbed (pauliCoords τ w)) (logChart ∘ f)).2 (h _ (pauliCoords τ))
  refine restriction_toProduct_of_components hH hC hX hL hf fun t p hp => ?_
  obtain ⟨𝒳, hp𝒳, -, -, Φ, hΦ, heq⟩ := hb.2 (asGroupFactors p) ⟨p, hp, rfl⟩
  have hEt : ComplexCoordinates.IsHolomorphicIn univ (expInCoords ∘ componentMatrix t) :=
    isHolomorphicIn_comp hH (isHolomorphicIn_expInCoords hH) (isHolomorphicIn_linearMap isOpen_univ _)
      (mapsTo_univ _ _)
  refine ⟨𝒳, fun q => ComplexCoordinates.matrixEquiv.symm
      (expInCoords (componentMatrix t (Φ q))), hp𝒳, ?_, fun x hx hx𝒳 => ?_⟩
  · exact isHolomorphicToCoords_postcomp hH ComplexCoordinates.matrixEquiv (e := Equiv.refl _)
      (h := expInCoords ∘ componentMatrix t) hEt (fun _ _ => mem_univ _) (hΦ b)
  · have hreal : asGroupFactors x ∈ subspaceTimesGroup (hermitianTracelessFunctions Empty) σ := by
      refine ⟨fun k => k.elim, ?_⟩
      exact hsub (hOE hx)
    have hval := heq ⟨hx𝒳, hreal⟩
    obtain ⟨Y', hY', hYe⟩ := hfE hx
    have hinv : logChart (f x) = Y' := by
      rw [← hYe]
      exact hτ.2.2.1 _ hY'
    simp only [Function.comp_apply, groupComponent_asGroupFactors, hinv] at hval
    simp only [id]
    rw [hval, componentMatrix_apply]
    simp only [expInCoords, Equiv.symm_apply_apply]
    rw [← hYe]
    rfl
end Logarithm
theorem analyticReadInExpChart (h₁ : ChartAndBallImages.Statement)
    (hK : AnalyticCalculusStatement)
    (hH : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hX : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (hC : GroupLieProduct.HolomorphicCalculus.Properties)
    (hL : ComplexMatrix2.ExpLogEstimates) : AnalyticReadInExpChartStatement := by
  intro σ τ _ _ _ _ b O hO hOE
  have hσ := (h₁ σ).1
  have hτ := (h₁ τ).1
  refine ⟨fun f => scalar_restriction_iff hH hK hσ.2.1 hO hOE b f,
    fun f => matrix_restriction_iff hH hK hσ.2.1 hO hOE b f, fun f hf => ⟨?_, fun hfE => ?_⟩⟩
  · exact ⟨fun h k ν => realAnalyticVia_of_productRestriction hH hK hσ.2.1 hO hOE b hf h k ν,
      productRestriction_of_realAnalyticVia hH hK hC hX hL hσ.2.1 hO hOE b hf⟩
  · exact ⟨logChart_realAnalytic_of_restriction hH hK hC hX hL hσ hτ hO hOE b hfE,
      restriction_of_logChart_realAnalytic hH hK hC hX hL hσ hτ hO hOE b hf hfE⟩
end YangMills.Construction.IdentityExpChart.CoordinatesInChart
