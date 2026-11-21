import YangMills.Construction.Averaging.MeanInTheComplexGroup
import YangMills.Construction.Matrices.NormExpLogBasics
import YangMills.Construction.Matrices.NormExpLogConjugationLemmas
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.PeriodicLattice YangMills.Construction.Matrices YangMills.Construction.Coordinates
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
namespace YangMills.Construction.Averaging.ComplexLogMean
variable {n : ℕ}
theorem isUnit_of_mem_complexGaugeGroup {X : ComplexMatrix2} (h : X ∈ complexGaugeGroup) :
    IsUnit X := by
  have hdet : X.det = 1 := h
  exact (Matrix.isUnit_iff_isUnit_det X).2 (by rw [hdet]; exact isUnit_one)
theorem mem_complexGaugeGroup_of_mem_compactGaugeGroup {X : ComplexMatrix2}
    (h : X ∈ compactGaugeGroup) : X ∈ complexGaugeGroup :=
  (Matrix.mem_specialUnitaryGroup_iff.1 h).2
theorem mul_inv_self_of_isUnit {X : ComplexMatrix2} (h : IsUnit X) : X * X⁻¹ = 1 :=
  Matrix.mul_nonsing_inv X ((Matrix.isUnit_iff_isUnit_det X).1 h)
theorem isUnitFamily_of_mem (hn : 1 ≤ n) {V : Fin n → ComplexMatrix2}
    (hV : V ∈ smallComplexFamilies n) : ComplexMatrix2.IsUnitFamily V :=
  ⟨hn, fun i => isUnit_of_mem_complexGaugeGroup (hV.1 i)⟩
theorem unitFamilyDiameter_le {V : Fin n → ComplexMatrix2} (hV : V ∈ smallComplexFamilies n) :
    ComplexMatrix2.unitFamilyDiameter V ≤ 1 / 40 := by
  have h : ComplexMatrix2.familyDiameter V < centreOfMassDiameter := hV.2
  have hb : centreOfMassDiameter = 1 / 40 := rfl
  rw [hb] at h
  exact h.le
theorem isNearComplexLogMean_average (h : SmallDiameterMean.AverageStatement) (hn : 1 ≤ n)
    {V : Fin n → ComplexMatrix2} (hV : V ∈ smallComplexFamilies n) :
    IsNearComplexLogMean V (SmallDiameterMean.average V) := by
  obtain ⟨h₁, -⟩ := h
  obtain ⟨-, -, -, -, -, -, hS, h4, hL, -, -, hC, -, -⟩ :=
    h₁ n V (isUnitFamily_of_mem hn hV) (unitFamilyDiameter_le hV)
  have hr : ∀ i, ComplexMatrix2.operatorNorm (V i * (SmallDiameterMean.average V)⁻¹ - 1) ≤
      1 / 10 :=
    fun i => (hS i).trans h4
  refine ⟨⟨(hC hV.1).2, fun i => (hr i).trans_lt (by norm_num), hL⟩, ⟨0, hn⟩, ?_⟩
  exact hr _
theorem eq_average_of_isNearComplexLogMean (h : SmallDiameterMean.AverageStatement)
    (hn : 1 ≤ n) {V : Fin n → ComplexMatrix2} (hV : V ∈ smallComplexFamilies n)
    {W : ComplexMatrix2} (hW : IsNearComplexLogMean V W) :
    W = SmallDiameterMean.average V := by
  obtain ⟨h₁, -⟩ := h
  obtain ⟨-, -, -, -, -, -, -, -, -, hU, -, -, -, -⟩ :=
    h₁ n V (isUnitFamily_of_mem hn hV) (unitFamilyDiameter_le hV)
  obtain ⟨⟨hG, hlt, hL⟩, k, hk⟩ := hW
  exact hU W (isUnit_of_mem_complexGaugeGroup hG) hlt hL ⟨k, hk⟩
theorem complexLogMean_eq_average (h : SmallDiameterMean.AverageStatement) (hn : 1 ≤ n)
    {V : Fin n → ComplexMatrix2} (hV : V ∈ smallComplexFamilies n) :
    complexLogMean V = SmallDiameterMean.average V := by
  have hs : IsNearComplexLogMean V (Classical.epsilon (IsNearComplexLogMean V)) :=
    Classical.epsilon_spec ⟨_, isNearComplexLogMean_average h hn hV⟩
  exact eq_average_of_isNearComplexLogMean h hn hV hs
theorem familyDiameter_comp_perm (π : Equiv.Perm (Fin n)) (V : Fin n → ComplexMatrix2) :
    ComplexMatrix2.familyDiameter (V ∘ π) = ComplexMatrix2.familyDiameter V := by
  unfold ComplexMatrix2.familyDiameter
  exact (Equiv.prodCongr π π).surjective.iSup_comp
    fun p : Fin n × Fin n => ComplexMatrix2.operatorNorm (V p.1 * (V p.2)⁻¹ - 1)
theorem comp_perm_mem (π : Equiv.Perm (Fin n)) {V : Fin n → ComplexMatrix2}
    (hV : V ∈ smallComplexFamilies n) : V ∘ π ∈ smallComplexFamilies n := by
  refine ⟨fun i => hV.1 (π i), ?_⟩
  rw [familyDiameter_comp_perm]
  exact hV.2
theorem const_mem {W : ComplexMatrix2} (hW : W ∈ complexGaugeGroup) :
    (fun _ : Fin n => W) ∈ smallComplexFamilies n := by
  refine ⟨fun _ => hW, ?_⟩
  have hWW : W * W⁻¹ = 1 := mul_inv_self_of_isUnit (isUnit_of_mem_complexGaugeGroup hW)
  have hd : ComplexMatrix2.familyDiameter (fun _ : Fin n => W) = 0 := by
    unfold ComplexMatrix2.familyDiameter
    simp only [hWW, sub_self, norm_zero]
    exact Real.iSup_const_zero
  rw [hd]
  norm_num [centreOfMassDiameter]
theorem smallComplexFamilies_eq_inter :
    smallComplexFamilies n = SmallDiameterMean.narrowFamilies n ∩
      EntrywiseHolomorphy.unimodularPow n := by
  ext V
  constructor
  · intro hV
    have hb : ComplexMatrix2.unitFamilyDiameter V < 1 / 40 := hV.2
    exact ⟨⟨fun i => isUnit_of_mem_complexGaugeGroup (hV.1 i), hb⟩, hV.1⟩
  · rintro ⟨⟨-, hd⟩, hc⟩
    exact ⟨hc, hd⟩
theorem isHolomorphicIn_congr {N N' : ℕ} {O : Set (ComplexCoordinates N)}
    {f g : ComplexCoordinates N → ComplexCoordinates N'}
    (hf : ComplexCoordinates.IsHolomorphicIn O f)
    (h : ∀ z ∈ O, f z = g z) : ComplexCoordinates.IsHolomorphicIn O g := by
  obtain ⟨hO, hc, hd⟩ := hf
  refine ⟨hO, hc.congr fun z hz => (h z hz).symm, fun a ha j => ?_⟩
  have hcont : Continuous fun ζ : ℂ => a + ζ • ComplexCoordinates.stdBasisVector j := by
    fun_prop
  have hmem : ∀ᶠ ζ in 𝓝 (0 : ℂ), a + ζ • ComplexCoordinates.stdBasisVector j ∈ O :=
    hcont.continuousAt.eventually_mem (by simpa using hO.mem_nhds ha)
  filter_upwards [hd a ha j, hmem.eventually_nhds] with ζ hζ hnear
  exact hζ.congr_of_eventuallyEq (hnear.mono fun ζ' hζ' => (h _ hζ').symm)
theorem isHolomorphicOnSL2Power_congr (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    {U : Set (Fin n → ComplexMatrix2)} {Φ Ψ : (Fin n → ComplexMatrix2) → ComplexMatrix2}
    (hΦ : ComplexCoordinates.IsHolomorphicOnSL2Power b U Φ) (h : ∀ X ∈ U, Φ X = Ψ X) :
    ComplexCoordinates.IsHolomorphicOnSL2Power b U Ψ := by
  obtain ⟨hn, hO, hm, hc, hX⟩ := hΦ
  refine ⟨hn, hO, fun X hXU => h X hXU ▸ hm hXU, hc.congr fun X hXU => (h X hXU).symm,
    fun X hXU => ?_⟩
  obtain ⟨W, h0, hW, hholo⟩ := hX X hXU
  have hq : ∀ w ∈ W, ComplexCoordinates.expChartQuotient Φ X
      (ComplexCoordinates.tracelessTuple b w) =
      ComplexCoordinates.expChartQuotient Ψ X (ComplexCoordinates.tracelessTuple b w) := by
    intro w hw
    unfold ComplexCoordinates.expChartQuotient
    rw [h _ (hW w hw).1, h X hXU]
  refine ⟨W, h0, fun w hw => ⟨(hW w hw).1, hq w hw ▸ (hW w hw).2⟩,
    isHolomorphicIn_congr hholo fun w hw => ?_⟩
  simp only [hq w hw]
theorem isHolomorphicBetween_congr {ι κ : Type} [Fintype ι] [Fintype κ]
    {s : ι → ComplexMatrix2.FactorKind} {t : κ → ComplexMatrix2.FactorKind}
    {D : Set (ι → ComplexMatrix2)} {f g : (ι → ComplexMatrix2) → κ → ComplexMatrix2}
    (hf : ComplexMatrix2.IsHolomorphicBetween s t D f) (h : ∀ x ∈ D, f x = g x) :
    ComplexMatrix2.IsHolomorphicBetween s t D g := by
  obtain ⟨hO, hm, hx⟩ := hf
  refine ⟨hO, fun x hxD => h x hxD ▸ hm hxD, fun x hxD => ?_⟩
  obtain ⟨F, hF, hev⟩ := hx x hxD
  refine ⟨F, hF, ?_⟩
  filter_upwards [hev, self_mem_nhdsWithin] with y hy hyD
  rw [← h y hyD, hy]
theorem mem_unitaryGroup_of_mem_compactGaugeGroup {W : ComplexMatrix2}
    (h : W ∈ compactGaugeGroup) : W ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  (Matrix.mem_specialUnitaryGroup_iff.1 h).1
theorem inv_mem_unitaryGroup {W : ComplexMatrix2} (h : W ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    W⁻¹ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by apply _root_.YangMills.Construction.Matrices.ComplexMatrix2.NormExpLogConj.unitary_inv_mem <;> assumption
theorem conj_ratio_eq {W W' : ComplexMatrix2} (hW' : IsUnit W') (A B : ComplexMatrix2) :
    W * A * W' * (W * B * W')⁻¹ = W * (A * B⁻¹) * W⁻¹ := by
  have h : W' * W'⁻¹ = 1 := mul_inv_self_of_isUnit hW'
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  calc W * A * W' * (W'⁻¹ * (B⁻¹ * W⁻¹)) = W * A * (W' * W'⁻¹) * (B⁻¹ * W⁻¹) := by
        simp only [mul_assoc]
    _ = W * (A * B⁻¹) * W⁻¹ := by
        rw [h]
        simp only [mul_assoc, mul_one]
theorem familyDiameter_conj (hE : ComplexMatrix2.NormExpLogBasics)
    {V : Fin n → ComplexMatrix2} {W W' : ComplexMatrix2} (hW : W ∈ compactGaugeGroup)
    (hW' : W' ∈ compactGaugeGroup) :
    ComplexMatrix2.familyDiameter (fun i => W * V i * W') =
      ComplexMatrix2.familyDiameter V := by
  obtain ⟨⟨-, -, -, hnorm, -⟩, -⟩ := hE
  have hWu := mem_unitaryGroup_of_mem_compactGaugeGroup hW
  have hWW : W * W⁻¹ = 1 :=
    mul_inv_self_of_isUnit
      (isUnit_of_mem_complexGaugeGroup (mem_complexGaugeGroup_of_mem_compactGaugeGroup hW))
  have hu' : IsUnit W' :=
    isUnit_of_mem_complexGaugeGroup (mem_complexGaugeGroup_of_mem_compactGaugeGroup hW')
  unfold ComplexMatrix2.familyDiameter
  refine iSup_congr fun p => ?_
  have hs : W * (V p.1 * (V p.2)⁻¹) * W⁻¹ - 1 = W * (V p.1 * (V p.2)⁻¹ - 1) * W⁻¹ := by
    rw [mul_sub, sub_mul, mul_one, hWW]
  rw [conj_ratio_eq hu', hs]
  exact hnorm _ _ _ hWu (inv_mem_unitaryGroup hWu)
theorem complexLogMean_conj (hM : SmallDiameterMean.AverageStatement)
    (hE : ComplexMatrix2.NormExpLogBasics) (hn : 1 ≤ n) {V : Fin n → ComplexMatrix2}
    (hV : V ∈ smallComplexFamilies n) {W W' : ComplexMatrix2} (hW : W ∈ compactGaugeGroup)
    (hW' : W' ∈ compactGaugeGroup) :
    complexLogMean (fun i => W * V i * W') = W * complexLogMean V * W' := by
  have hWc : W.det = 1 := mem_complexGaugeGroup_of_mem_compactGaugeGroup hW
  have hWc' : W'.det = 1 := mem_complexGaugeGroup_of_mem_compactGaugeGroup hW'
  have hWu := mem_unitaryGroup_of_mem_compactGaugeGroup hW
  have hu' : IsUnit W' :=
    isUnit_of_mem_complexGaugeGroup (mem_complexGaugeGroup_of_mem_compactGaugeGroup hW')
  have hV' : (fun i => W * V i * W') ∈ smallComplexFamilies n := by
    refine ⟨fun i => ?_, ?_⟩
    · have hdet : (V i).det = 1 := hV.1 i
      change (W * V i * W').det = 1
      rw [Matrix.det_mul, Matrix.det_mul, hWc, hWc', hdet]
      norm_num
    · rw [familyDiameter_conj hE hW hW']
      exact hV.2
  obtain ⟨⟨hG, hlt, hL⟩, k, hk⟩ := isNearComplexLogMean_average hM hn hV
  obtain ⟨-, -, hconj, -⟩ := hE
  have hnear : IsNearComplexLogMean (fun i => W * V i * W')
      (W * SmallDiameterMean.average V * W') := by
    have hq : ∀ i, W * V i * W' * (W * SmallDiameterMean.average V * W')⁻¹ =
        W * (V i * (SmallDiameterMean.average V)⁻¹) * W⁻¹ :=
      fun i => conj_ratio_eq hu' _ _
    refine ⟨⟨?_, fun i => ?_, ?_⟩, k, ?_⟩
    · have hdet : (SmallDiameterMean.average V).det = 1 := hG
      change (W * SmallDiameterMean.average V * W').det = 1
      rw [Matrix.det_mul, Matrix.det_mul, hWc, hWc', hdet]
      norm_num
    · rw [hq i, (hconj _ W (hlt i) hWu).1]
      exact hlt i
    · simp only [hq]
      rw [Finset.sum_congr rfl fun i _ => (hconj _ W (hlt i) hWu).2, ← Finset.sum_mul,
        ← Finset.mul_sum, hL]
      simp
    · rw [hq k, (hconj _ W (hlt k) hWu).1]
      exact hk
  rw [complexLogMean_eq_average hM hn hV, complexLogMean_eq_average hM hn hV',
    ← eq_average_of_isNearComplexLogMean hM hn hV' hnear]
theorem complexLogMeanProperties_of (hM : SmallDiameterMean.AverageStatement)
    (hH : EntrywiseHolomorphy.RestrictionStatement) (hE : ComplexMatrix2.NormExpLogBasics)
    (hn : 1 ≤ n) : ComplexLogMeanProperties n := by
  have hM' := hM
  obtain ⟨h₁, hConst, hHolo, hFinal⟩ := hM'
  have hMem : ∀ V : Fin n → ComplexMatrix2, (∀ i, V i ∈ compactGaugeGroup) →
      ComplexMatrix2.familyDiameter V < centreOfMassDiameter → V ∈ smallComplexFamilies n :=
    fun V hG hd => ⟨fun i => mem_complexGaugeGroup_of_mem_compactGaugeGroup (hG i), hd⟩
  have hOnly : ∀ V : Fin n → ComplexMatrix2, (∀ i, V i ∈ compactGaugeGroup) →
      ComplexMatrix2.familyDiameter V < centreOfMassDiameter →
        ∀ W, ComplexMatrix2.IsLogMean compactGaugeGroup V W ↔ W = complexLogMean V := by
    intro V hG hd W
    have hV := hMem V hG hd
    obtain ⟨hiff, -⟩ := hFinal n V ⟨hn, hG⟩ (unitFamilyDiameter_le hV)
    rw [complexLogMean_eq_average hM hn hV]
    exact ⟨fun h => (hiff W).1 ⟨⟨hn, hG⟩, h⟩, fun h => ((hiff W).2 h).2⟩
  obtain ⟨hOpen, -, hEntries⟩ := hHolo n hn
  have hValues : ∀ X ∈ SmallDiameterMean.narrowFamilies n ∩
      EntrywiseHolomorphy.unimodularPow n,
      SmallDiameterMean.average X ∈ ComplexMatrix2.unitDeterminant := by
    intro X hX
    have hXs : X ∈ smallComplexFamilies n := by
      rw [smallComplexFamilies_eq_inter]
      exact hX
    exact (isNearComplexLogMean_average hM hn hXs).1.1
  obtain ⟨⟨hOpenIn, hDiff, hEnt⟩, -⟩ :=
    hH n hn (SmallDiameterMean.narrowFamilies n) hOpen SmallDiameterMean.average hEntries hValues
  rw [← smallComplexFamilies_eq_inter] at hOpenIn hDiff hEnt
  refine
    { existsUnique := fun V hV => ⟨SmallDiameterMean.average V,
        isNearComplexLogMean_average hM hn hV,
        fun W hW => eq_average_of_isNearComplexLogMean hM hn hV hW⟩
      spread := fun V hV i => ?_
      numbering := fun V hV π => ?_
      constantFamily := fun W hW => ?_
      isOpen := hOpenIn
      holomorphic := fun b => isHolomorphicOnSL2Power_congr b (hDiff b)
        fun X hX => (complexLogMean_eq_average hM hn hX).symm
      holomorphicInEntries := isHolomorphicBetween_congr hEnt
        fun X hX => by rw [complexLogMean_eq_average hM hn hX]
      memRealGroup := fun V hG hd => ?_
      onlyMean := hOnly
      exactlyOneMean := fun V hG hd =>
        ⟨complexLogMean V, (hOnly V hG hd _).2 rfl, fun W hW => (hOnly V hG hd W).1 hW⟩
      meanEqualsAverage := fun V hG hd => (hOnly V hG hd _).1 <|
        Classical.epsilon_spec ⟨complexLogMean V, (hOnly V hG hd _).2 rfl⟩
      covariant := fun V hV W hW W' hW' => complexLogMean_conj hM hE hn hV hW hW' }
  · obtain ⟨-, -, -, -, -, -, hS, -⟩ :=
      h₁ n V (isUnitFamily_of_mem hn hV) (unitFamilyDiameter_le hV)
    rw [complexLogMean_eq_average hM hn hV]
    exact hS i
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, hP, -⟩ :=
      h₁ n V (isUnitFamily_of_mem hn hV) (unitFamilyDiameter_le hV)
    rw [complexLogMean_eq_average hM hn hV,
      complexLogMean_eq_average hM hn (comp_perm_mem π hV)]
    exact hP π
  · rw [complexLogMean_eq_average hM hn (const_mem hW)]
    exact hConst n hn W (isUnit_of_mem_complexGaugeGroup hW)
  · have hV := hMem V hG hd
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hSU, -⟩ :=
      h₁ n V (isUnitFamily_of_mem hn hV) (unitFamilyDiameter_le hV)
    rw [complexLogMean_eq_average hM hn hV]
    exact (hSU hG).2
theorem averagingRadiusCap_mem (s : Conventions.StandingParameters) :
    averagingRadiusCap s.L ∈ Ioc (0 : ℝ) 1 := by
  have hL : (13 : ℝ) ≤ s.L := by exact_mod_cast s.isAdmissible.2
  have hp : (0 : ℝ) < 200 * (s.L : ℝ) ^ 2 := by positivity
  unfold averagingRadiusCap
  exact ⟨one_div_pos.2 hp, (div_le_one hp).2 (by nlinarith)⟩
theorem contourHolonomies_small (hR : SmallRadius.EverySmallRadiusSuffices)
    (s : Conventions.StandingParameters) :
    ContourHolonomiesAreSmall s.L s.m s.K (averagingRadiusCap s.L) := by
  intro ω hω k hk c U hU y hy x hx
  have hc := hR s ω hω k hk c
  have hle : ComplexMatrix2.familyDiameter (contourHolonomies U y x) ≤ 1 / 50 := by
    refine Real.iSup_le (fun p => ?_) (by norm_num)
    obtain ⟨h₁, h₂, h₃, h₄⟩ := hc.holonomy_ratio_le U hU y hy x hx
      (orderedContour y x p.2) ⟨p.2, rfl⟩ (orderedContour y x p.1) ⟨p.1, rfl⟩
    exact h₁.trans (h₂.trans (h₃.trans h₄))
  refine hle.trans_lt ?_
  norm_num [centreOfMassDiameter]
theorem complexLogMeanOfSmallFamilies_holds (hM : SmallDiameterMean.AverageStatement)
    (hH : EntrywiseHolomorphy.RestrictionStatement) (hE : ComplexMatrix2.NormExpLogBasics)
    (hR : SmallRadius.EverySmallRadiusSuffices) : ComplexLogMeanOfSmallFamilies :=
  ⟨by norm_num [centreOfMassDiameter],
    by norm_num [centreOfMassDiameter, complexMeanTolerance],
    by norm_num [complexMeanTolerance], fun _ hn => complexLogMeanProperties_of hM hH hE hn,
    fun s => ⟨averagingRadiusCap_mem s, contourHolonomies_small hR s⟩⟩
end YangMills.Construction.Averaging.ComplexLogMean
end
