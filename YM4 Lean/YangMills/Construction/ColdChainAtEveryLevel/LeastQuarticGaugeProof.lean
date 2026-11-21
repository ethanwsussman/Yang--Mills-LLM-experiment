import YangMills.Construction.ColdChainAtEveryLevel.PlaquettesNearAPoint
import YangMills.Construction.ColdChainAtEveryLevel.UnitPartsOfQuaternions
import YangMills.Construction.HoleBesideASecondHole.TreeGaugeOfAField
import YangMills.Construction.ColdChainAtEveryLevel.CurlOfAGapOnAPatchProof
import YangMills.Construction.ColdChainAtEveryLevel.DensityUnderAChangeOfFramingProof
import YangMills.Construction.ColdChainAtEveryLevel.RatesOfTheTerms
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages LatticeFractionalIntegration
namespace LeastQuarticGauge
section Group
theorem norm_coe_unit (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
def distOne (g : UnitQuaternion) : ℝ := ‖(g : ℍ[ℝ]) - 1‖
theorem distOne_nonneg (g : UnitQuaternion) : 0 ≤ distOne g := norm_nonneg _
theorem distOne_one : distOne 1 = 0 := by simp [distOne]
theorem distOne_mul_le (g h : UnitQuaternion) : distOne (g * h) ≤ distOne g + distOne h := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_mul_sub_one_le <;> assumption
theorem distOne_inv (g : UnitQuaternion) : distOne g⁻¹ = distOne g := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_inv_sub_one <;> assumption
theorem distOne_conj (a g : UnitQuaternion) : distOne (a * g * a⁻¹) = distOne g := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_conj_sub_one <;> assumption
theorem latticePlaquette_gaugeTransform (γ : Lattice4 → UnitQuaternion)
    (X : Lattice4 → Fin 4 → UnitQuaternion) (y : Lattice4) (μ ν : Fin 4) :
    latticePlaquette (latticeGaugeTransform γ X) y μ ν = γ y * latticePlaquette X y μ ν * (γ y)⁻¹ := by
  simp only [latticePlaquette, latticeGaugeTransform, mul_inv_rev, inv_inv]
  have e : y + basisVector μ + basisVector ν = y + basisVector ν + basisVector μ := by abel
  rw [e]
  group
end Group
section Growth
structure LayerStep (P' P'' : Finset Lattice4) (i : Fin 4) : Prop where
  subset : P' ⊆ P''
  newShift : ∀ x ∈ P'', x ∉ P' → x + basisVector i ∈ P'
  oldShift : ∀ y ∈ P', ∀ j, y + basisVector j ∈ P'' → y + basisVector j ∈ P'
  newSideShift : ∀ x ∈ P'', x ∉ P' → ∀ j, j ≠ i → x + basisVector j ∈ P'' →
    x + basisVector j + basisVector i ∈ P'
def quarticSum (P : Finset Lattice4) (Y : Lattice4 → Fin 4 → UnitQuaternion) : ℝ :=
  ∑ b ∈ bondsOf P, distOne (Y b.1 b.2) ^ 4
def plaquetteEnergy (P : Finset Lattice4) (Y : Lattice4 → Fin 4 → UnitQuaternion) : ℝ :=
  ∑ p ∈ orientedPlaquettesOf P, distOne (latticePlaquette Y p.1 p.2.1 p.2.2) ^ 2
theorem mem_bondsOf {P : Finset Lattice4} {b : Lattice4 × Fin 4} :
    b ∈ bondsOf P ↔ b.1 ∈ P ∧ b.1 + basisVector b.2 ∈ P := by
  simp [bondsOf]
theorem mem_orientedPlaquettesOf {P : Finset Lattice4} {p : Lattice4 × Fin 4 × Fin 4} :
    p ∈ orientedPlaquettesOf P ↔ p.1 ∈ P ∧ p.2.1 ≠ p.2.2 ∧ p.1 + basisVector p.2.1 ∈ P ∧
      p.1 + basisVector p.2.2 ∈ P ∧ p.1 + basisVector p.2.1 + basisVector p.2.2 ∈ P := by
  simp [orientedPlaquettesOf]
theorem plaquetteEnergy_gaugeTransform (P : Finset Lattice4) (γ : Lattice4 → UnitQuaternion)
    (X : Lattice4 → Fin 4 → UnitQuaternion) :
    plaquetteEnergy P (latticeGaugeTransform γ X) = plaquetteEnergy P X := by
  unfold plaquetteEnergy
  apply Finset.sum_congr rfl
  intro p _
  rw [latticePlaquette_gaugeTransform, distOne_conj]
theorem plaquetteEnergy_mono {P' P'' : Finset Lattice4} (h : P' ⊆ P'')
    (Y : Lattice4 → Fin 4 → UnitQuaternion) : plaquetteEnergy P' Y ≤ plaquetteEnergy P'' Y := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    rw [mem_orientedPlaquettesOf] at hp ⊢
    exact ⟨h hp.1, hp.2.1, h hp.2.2.1, h hp.2.2.2.1, h hp.2.2.2.2⟩
  · exact fun p _ _ => by positivity
theorem sum_pow_four_le_sq_sum (A : Finset (Lattice4 × Fin 4 × Fin 4))
    (f : Lattice4 × Fin 4 × Fin 4 → ℝ) (hf : ∀ p, 0 ≤ f p) :
    ∑ p ∈ A, f p ^ 4 ≤ (∑ p ∈ A, f p ^ 2) ^ 2 := by
  have h := Finset.sum_sq_le_sq_sum_of_nonneg (s := A) (f := fun p => f p ^ 2)
    (fun p _ => by positivity)
  refine le_trans (le_of_eq ?_) h
  apply Finset.sum_congr rfl
  intro p _
  ring
end Growth
section Extension
theorem sum_comp_le_of_injOn {α β : Type} [DecidableEq β] (T : Finset α) (φ : α → β) (B : Finset β)
    (f : β → ℝ) (hf : ∀ u, 0 ≤ f u) (hinj : Set.InjOn φ T) (hin : ∀ a ∈ T, f (φ a) ≠ 0 → φ a ∈ B) :
    ∑ a ∈ T, f (φ a) ≤ ∑ u ∈ B, f u := by
  rw [← Finset.sum_image (f := f) (g := φ) (s := T) hinj, ← Finset.sum_filter_ne_zero]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro u hu
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hu
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 h1
    exact hin a ha h2
  · exact fun u _ _ => hf u
theorem add_three_pow_four_le (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (a + b + c) ^ 4 ≤ 27 * (a ^ 4 + b ^ 4 + c ^ 4) := by
  have h2 : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
  have h3 : (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≤ 3 * (a ^ 4 + b ^ 4 + c ^ 4) := by
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (a ^ 2 - c ^ 2)]
  have h4 : (a + b + c) ^ 4 = ((a + b + c) ^ 2) ^ 2 := by ring
  rw [h4]
  calc ((a + b + c) ^ 2) ^ 2 ≤ (3 * (a ^ 2 + b ^ 2 + c ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (sq_nonneg _) h2 2
    _ = 9 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 := by ring
    _ ≤ _ := by linarith
def layerGauge (P' : Finset Lattice4) (i : Fin 4) (γ : Lattice4 → UnitQuaternion)
    (X : Lattice4 → Fin 4 → UnitQuaternion) : Lattice4 → UnitQuaternion := by
  classical exact fun x => if x ∈ P' then γ x else γ (x + basisVector i) * (X x i)⁻¹
theorem exists_layer_gauge {P' P'' : Finset Lattice4} {i : Fin 4} (hG : LayerStep P' P'' i)
    (γ : Lattice4 → UnitQuaternion) (X : Lattice4 → Fin 4 → UnitQuaternion) :
    ∃ γ'' : Lattice4 → UnitQuaternion, quarticSum P'' (latticeGaugeTransform γ'' X) ≤
      136 * quarticSum P' (latticeGaugeTransform γ X) + 27 * plaquetteEnergy P'' X ^ 2 := by
  classical
  refine ⟨layerGauge P' i γ X, ?_⟩
  set γ'' := layerGauge P' i γ X with hγ''
  set Y := latticeGaugeTransform γ'' X with hY
  set Y' := latticeGaugeTransform γ X with hY'
  have hold : ∀ x, x ∈ P' → γ'' x = γ x := fun x hx => if_pos hx
  have hnew : ∀ x, x ∉ P' → γ'' x = γ (x + basisVector i) * (X x i)⁻¹ := fun x hx => if_neg hx
  have hYY' : ∀ b ∈ bondsOf P', Y b.1 b.2 = Y' b.1 b.2 := by
    intro b hb
    obtain ⟨h1, h2⟩ := mem_bondsOf.1 hb
    simp only [hY, hY', latticeGaugeTransform]
    rw [hold _ h1, hold _ h2]
  have hone : ∀ x ∈ P'', x ∉ P' → Y x i = 1 := by
    intro x hx hx'
    simp only [hY, latticeGaugeTransform]
    rw [hnew x hx', hold _ (hG.newShift x hx hx')]
    group
  have hsubB : bondsOf P' ⊆ bondsOf P'' := by
    intro b hb
    obtain ⟨h1, h2⟩ := mem_bondsOf.1 hb
    exact mem_bondsOf.2 ⟨hG.subset h1, hG.subset h2⟩
  set NB := bondsOf P'' \ bondsOf P' with hNB
  have hNBnew : ∀ b ∈ NB, b.1 ∉ P' := by
    intro b hb h1
    obtain ⟨h2, h3⟩ := Finset.mem_sdiff.1 hb
    exact h3 (mem_bondsOf.2 ⟨h1, hG.oldShift _ h1 _ (mem_bondsOf.1 h2).2⟩)
  set pa : Lattice4 × Fin 4 → Lattice4 × Fin 4 × Fin 4 := fun b => (b.1, b.2, i) with hpa
  set pb : Lattice4 × Fin 4 → Lattice4 × Fin 4 := fun b => (b.1 + basisVector i, b.2) with hpb
  set pc : Lattice4 × Fin 4 → Lattice4 × Fin 4 := fun b => (b.1 + basisVector b.2, i) with hpc
  set fa : Lattice4 × Fin 4 × Fin 4 → ℝ := fun p => distOne (latticePlaquette Y p.1 p.2.1 p.2.2) with hfa
  set fb : Lattice4 × Fin 4 → ℝ := fun b => distOne (Y b.1 b.2) with hfb
  have hterm : ∀ b ∈ NB, b.2 ≠ i → fb b ≤ fa (pa b) + fb (pb b) + fb (pc b) := by
    intro b hb hbi
    obtain ⟨x, j⟩ := b
    have hx'' : x ∈ P'' := (mem_bondsOf.1 (Finset.mem_sdiff.1 hb).1).1
    have hxn := hNBnew (x, j) hb
    have e1 := hone x hx'' hxn
    have hform : Y x j = latticePlaquette Y x j i * Y (x + basisVector i) j *
        (Y (x + basisVector j) i)⁻¹ := by
      simp only [latticePlaquette, e1]
      group
    simp only [hfb, hfa, hpa, hpb, hpc]
    rw [hform]
    refine (distOne_mul_le _ _).trans ?_
    rw [distOne_inv]
    have := distOne_mul_le (latticePlaquette Y x j i) (Y (x + basisVector i) j)
    linarith
  have hzero : ∀ b ∈ NB, b.2 = i → fb b = 0 := by
    intro b hb hbi
    have hx'' : b.1 ∈ P'' := (mem_bondsOf.1 (Finset.mem_sdiff.1 hb).1).1
    simp only [hfb]
    rw [hbi, hone b.1 hx'' (hNBnew b hb), distOne_one]
  have hfb0 : ∀ b, 0 ≤ fb b := fun b => distOne_nonneg _
  have hfa0 : ∀ p, 0 ≤ fa p := fun p => distOne_nonneg _
  set NB' := NB.filter fun b => b.2 ≠ i with hNB'
  have hNBsum : ∑ b ∈ NB, fb b ^ 4 ≤
      27 * (∑ b ∈ NB', fa (pa b) ^ 4 + ∑ b ∈ NB', fb (pb b) ^ 4 + ∑ b ∈ NB', fb (pc b) ^ 4) := by
    have e : ∑ b ∈ NB, fb b ^ 4 = ∑ b ∈ NB', fb b ^ 4 := by
      symm
      apply Finset.sum_filter_of_ne
      intro b hb hne hbi
      apply hne
      rw [hzero b hb (not_not.1 (by simpa using hbi))]
      norm_num
    rw [e, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro b hb
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hb
    exact (pow_le_pow_left₀ (hfb0 b) (hterm b h1 h2) 4).trans
      (add_three_pow_four_le _ _ _ (hfa0 _) (hfb0 _) (hfb0 _))
  have hfacts : ∀ b ∈ NB', b.1 ∈ P'' ∧ b.1 ∉ P' ∧ b.2 ≠ i ∧ b.1 + basisVector b.2 ∈ P'' ∧
      b.1 + basisVector i ∈ P' ∧ b.1 + basisVector b.2 + basisVector i ∈ P' := by
    intro b hb
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hb
    obtain ⟨h3, h4⟩ := mem_bondsOf.1 (Finset.mem_sdiff.1 h1).1
    have h5 := hNBnew b h1
    exact ⟨h3, h5, h2, h4, hG.newShift _ h3 h5, hG.newSideShift _ h3 h5 _ h2 h4⟩
  have hA : ∑ b ∈ NB', fa (pa b) ^ 4 ≤ plaquetteEnergy P'' X ^ 2 := by
    rw [← plaquetteEnergy_gaugeTransform P'' γ'' X]
    refine le_trans ?_ (sum_pow_four_le_sq_sum _ fa hfa0)
    have hinj : Set.InjOn pa NB' := by
      intro a _ b _ h
      simp only [hpa, Prod.mk.injEq] at h
      exact Prod.ext h.1 h.2.1
    apply sum_comp_le_of_injOn NB' pa _ (fun p => fa p ^ 4) (fun p => by have := hfa0 p; positivity) hinj
    intro b hb _
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hfacts b hb
    exact mem_orientedPlaquettesOf.2 ⟨h1, h3, h4, hG.subset h5, hG.subset h6⟩
  have hquart : ∑ u ∈ bondsOf P', fb u ^ 4 = quarticSum P' Y' := by
    apply Finset.sum_congr rfl
    intro u hu
    simp only [hfb]
    rw [hYY' u hu]
  have hB : ∑ b ∈ NB', fb (pb b) ^ 4 ≤ quarticSum P' Y' := by
    rw [← hquart]
    have hinj : Set.InjOn pb NB' := by
      intro a _ b _ h
      simp only [hpb, Prod.mk.injEq, add_left_inj] at h
      exact Prod.ext h.1 h.2
    apply sum_comp_le_of_injOn NB' pb _ (fun u => fb u ^ 4) (fun u => by have := hfb0 u; positivity) hinj
    intro b hb _
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hfacts b hb
    refine mem_bondsOf.2 ⟨h5, ?_⟩
    simp only [hpb]
    have : b.1 + basisVector i + basisVector b.2 = b.1 + basisVector b.2 + basisVector i := by abel
    rw [this]
    exact h6
  have hC : ∑ b ∈ NB', fb (pc b) ^ 4 ≤ 4 * quarticSum P' Y' := by
    have hfib : ∑ j : Fin 4, ∑ b ∈ NB'.filter (fun b => b.2 = j), fb (pc b) ^ 4 =
        ∑ b ∈ NB', fb (pc b) ^ 4 :=
      Finset.sum_fiberwise_of_maps_to (fun b _ => Finset.mem_univ b.2) _
    rw [← hfib]
    have hone' : ∀ j : Fin 4, ∑ b ∈ NB'.filter (fun b => b.2 = j), fb (pc b) ^ 4 ≤
        quarticSum P' Y' := by
      intro j
      rw [← hquart]
      have hinj : Set.InjOn pc (NB'.filter fun b => b.2 = j) := by
        intro a ha b hb h
        have h1 := (Finset.mem_filter.1 (Finset.mem_coe.1 ha)).2
        have h2 := (Finset.mem_filter.1 (Finset.mem_coe.1 hb)).2
        simp only [hpc, Prod.mk.injEq, and_true] at h
        rw [h1, h2] at h
        exact Prod.ext (add_right_cancel h) (h1.trans h2.symm)
      apply sum_comp_le_of_injOn _ pc _ (fun u => fb u ^ 4) (fun u => by have := hfb0 u; positivity) hinj
      intro b hb hne
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hfacts b (Finset.mem_filter.1 hb).1
      by_cases hz : b.1 + basisVector b.2 ∈ P'
      · exact mem_bondsOf.2 ⟨hz, h6⟩
      · exfalso
        apply hne
        simp only [hfb, hpc]
        rw [hone _ h4 hz, distOne_one]
        norm_num
    calc _ ≤ ∑ _j : Fin 4, quarticSum P' Y' := Finset.sum_le_sum fun j _ => hone' j
      _ = _ := by simp
  have htotal : quarticSum P'' Y = ∑ u ∈ bondsOf P', fb u ^ 4 + ∑ b ∈ NB, fb b ^ 4 := by
    have := Finset.sum_sdiff (f := fun b => fb b ^ 4) hsubB
    simp only [quarticSum, hfb]
    rw [← this]
    simp only [hNB]
    ring
  rw [htotal, hquart]
  linarith
end Extension
section Calculus
theorem quaternion_re_mul_comm (a b : ℍ[ℝ]) : (a * b).re = (b * a).re := by apply _root_.YangMills.Construction.BlockAverages.GaugedChains.quaternion_re_mul_comm <;> assumption
theorem norm_sq_eq_components (q : ℍ[ℝ]) :
    ‖q‖ ^ 2 = q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 := by
  rw [sq ‖q‖, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
theorem distOne_sq (g : UnitQuaternion) : distOne g ^ 2 = 2 - 2 * (g : ℍ[ℝ]).re := by apply _root_.YangMills.Construction.GaugeFixing.norm_coe_sub_one_sq <;> assumption
theorem norm_im_sq_unit (g : UnitQuaternion) :
    ‖(g : ℍ[ℝ]).im‖ ^ 2 = distOne g ^ 2 * (1 - distOne g ^ 2 / 4) := by
  have h := norm_sq_eq_components (g : ℍ[ℝ])
  rw [norm_coe_unit] at h
  have h2 := distOne_sq g
  rw [norm_sq_eq_components, h2]
  simp only [Quaternion.re_im, Quaternion.imI_im, Quaternion.imJ_im, Quaternion.imK_im]
  nlinarith
theorem norm_im_le_distOne (g : UnitQuaternion) : ‖(g : ℍ[ℝ]).im‖ ≤ distOne g := by apply _root_.YangMills.Construction.PlaquetteExpansion.norm_coe_im_le <;> assumption
theorem abs_re_le_norm (q : ℍ[ℝ]) : |q.re| ≤ ‖q‖ := by apply _root_.YangMills.Construction.BlockAverages.VariationRates.quaternion_abs_re_le_norm <;> assumption
theorem expUnit_zero : expUnit 0 = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
theorem coe_expUnit (w : imaginaryQuaternions) :
    ((expUnit w : UnitQuaternion) : ℍ[ℝ]) = NormedSpace.exp (w : ℍ[ℝ]) := rfl
theorem expUnit_inv (w : imaginaryQuaternions) : (expUnit w)⁻¹ = expUnit (-w) := by
  rw [inv_eq_iff_mul_eq_one]
  apply Subtype.ext
  simp only [Submonoid.coe_mul, coe_expUnit, Submodule.coe_neg, OneMemClass.coe_one]
  have hneg : NormedSpace.exp (-(w : ℍ[ℝ])) = (NormedSpace.exp (w : ℍ[ℝ]))⁻¹ :=
    NormedSpace.exp_neg_of_mem_ball (𝕂 := ℝ)
      ((NormedSpace.expSeries_radius_eq_top ℝ ℍ[ℝ]).symm ▸ edist_lt_top _ _)
  rw [hneg]
  apply mul_inv_cancel₀
  intro h0
  have := norm_coe_unit (expUnit w)
  rw [coe_expUnit, h0, norm_zero] at this
  norm_num at this
def reCLM : ℍ[ℝ] →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun q => q.re
      map_add' := by simp
      map_smul' := by simp }
theorem hasDerivAt_re_conjugate_flow (a b Y : ℍ[ℝ]) :
    HasDerivAt (fun τ : ℝ => (NormedSpace.exp (τ • a) * Y * NormedSpace.exp (τ • (-b))).re)
      ((a * Y - Y * b).re) 0 := by
  have h1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) a 0
  have h2 := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-b) 0
  have h3 := (h1.mul_const Y).mul h2
  have h4 := reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h3
  simp only [zero_smul, NormedSpace.exp_zero, one_mul, mul_one] at h4
  have e : reCLM (a * Y + Y * -b) = (a * Y - Y * b).re := by
    change (a * Y + Y * -b).re = _
    rw [mul_neg, sub_eq_add_neg]
  rw [e] at h4
  exact h4
theorem hasDerivAt_distOne_pow_four (a b : imaginaryQuaternions) (Y : UnitQuaternion) :
    HasDerivAt (fun τ : ℝ => distOne (expUnit (τ • a) * Y * (expUnit (τ • b))⁻¹) ^ 4)
      (-4 * (distOne Y ^ 2 * ((((a : ℍ[ℝ]) - b) * Y).re))) 0 := by
  have e : ∀ τ : ℝ, distOne (expUnit (τ • a) * Y * (expUnit (τ • b))⁻¹) ^ 4 =
      (2 - 2 * (NormedSpace.exp (τ • (a : ℍ[ℝ])) * (Y : ℍ[ℝ]) *
        NormedSpace.exp (τ • (-(b : ℍ[ℝ])))).re) ^ 2 := by
    intro τ
    have h := distOne_sq (expUnit (τ • a) * Y * (expUnit (τ • b))⁻¹)
    rw [show distOne (expUnit (τ • a) * Y * (expUnit (τ • b))⁻¹) ^ 4 =
      (distOne (expUnit (τ • a) * Y * (expUnit (τ • b))⁻¹) ^ 2) ^ 2 by ring, h, expUnit_inv]
    simp only [Submonoid.coe_mul, coe_expUnit, Submodule.coe_smul, Submodule.coe_neg, smul_neg]
  simp_rw [e, sq]
  have h := hasDerivAt_re_conjugate_flow (a : ℍ[ℝ]) (b : ℍ[ℝ]) (Y : ℍ[ℝ])
  have hu := (h.const_mul 2).const_sub 2
  have hsq := hu.fun_mul hu
  refine hsq.congr_deriv ?_
  have e2 : ((a : ℍ[ℝ]) * Y - Y * b).re = (((a : ℍ[ℝ]) - b) * Y).re := by
    simp only [Quaternion.re_sub, sub_mul]
    rw [quaternion_re_mul_comm (Y : ℍ[ℝ]) (b : ℍ[ℝ])]
  have e3 : (NormedSpace.exp ((0 : ℝ) • (a : ℍ[ℝ])) * (Y : ℍ[ℝ]) *
      NormedSpace.exp ((0 : ℝ) • (-(b : ℍ[ℝ])))).re = (Y : ℍ[ℝ]).re := by
    simp
  have hd := distOne_sq Y
  rw [sq] at hd
  rw [e3, e2, hd]
  ring
theorem first_variation_eq_zero (P : Finset Lattice4) (Y : Lattice4 → Fin 4 → UnitQuaternion)
    (hmin : ∀ γ : Lattice4 → UnitQuaternion, quarticSum P Y ≤ quarticSum P (latticeGaugeTransform γ Y))
    (ξ : Lattice4 → imaginaryQuaternions) :
    ∑ b ∈ bondsOf P, distOne (Y b.1 b.2) ^ 2 *
      ((((ξ b.1 : ℍ[ℝ]) - ξ (b.1 + basisVector b.2)) * Y b.1 b.2).re) = 0 := by
  set Ψ : ℝ → ℝ := fun τ => quarticSum P (latticeGaugeTransform (fun x => expUnit (τ • ξ x)) Y) with hΨ
  have hder : HasDerivAt Ψ (∑ b ∈ bondsOf P, -4 * (distOne (Y b.1 b.2) ^ 2 *
      ((((ξ b.1 : ℍ[ℝ]) - ξ (b.1 + basisVector b.2)) * Y b.1 b.2).re))) 0 := by
    simp only [hΨ, quarticSum, latticeGaugeTransform]
    exact HasDerivAt.fun_sum fun b _ => hasDerivAt_distOne_pow_four _ _ _
  have h0 : Ψ 0 = quarticSum P Y := by
    simp only [hΨ, quarticSum, latticeGaugeTransform, zero_smul, expUnit_zero]
    simp
  have hloc : IsLocalMin Ψ 0 := by
    apply Filter.Eventually.of_forall
    intro τ
    rw [h0]
    exact hmin _
  have hz := hloc.hasDerivAt_eq_zero hder
  rw [← Finset.mul_sum] at hz
  linarith
end Calculus
section Curl
theorem norm_im_le_norm (q : ℍ[ℝ]) : ‖q.im‖ ≤ ‖q‖ := by apply _root_.YangMills.Construction.BlockAverages.GaugeChangeDensity.norm_im_le_norm <;> assumption
theorem coe_inv_unit (g : UnitQuaternion) : ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = star (g : ℍ[ℝ]) := rfl
theorem coe_mul_sub_one (g h : UnitQuaternion) : ((g * h : UnitQuaternion) : ℍ[ℝ]) - 1 =
    ((g : ℍ[ℝ]) - 1) + ((h : ℍ[ℝ]) - 1) + ((g : ℍ[ℝ]) - 1) * ((h : ℍ[ℝ]) - 1) := by
  simp only [Submonoid.coe_mul, mul_sub, sub_mul, one_mul, mul_one]
  abel
def imaginaryField (Y : Lattice4 → Fin 4 → UnitQuaternion) : Lattice4 → Fin 4 → ℍ[ℝ] :=
  fun y i => ((Y y i : UnitQuaternion) : ℍ[ℝ]).im
theorem norm_curl_le (Y : Lattice4 → Fin 4 → UnitQuaternion) (y : Lattice4) (μ ν : Fin 4) :
    ‖plaquetteCurl (imaginaryField Y) y μ ν‖ ≤ distOne (latticePlaquette Y y μ ν) +
      (distOne (Y y μ) + distOne (Y (y + basisVector μ) ν) + distOne (Y (y + basisVector ν) μ) +
        distOne (Y y ν)) ^ 2 := by
  set g1 := Y y μ
  set g2 := Y (y + basisVector μ) ν
  set g3 := Y (y + basisVector ν) μ
  set g4 := Y y ν
  set d1 := distOne g1
  set d2 := distOne g2
  set d3 := distOne g3
  set d4 := distOne g4
  have hd1 : 0 ≤ d1 := distOne_nonneg _
  have hd2 : 0 ≤ d2 := distOne_nonneg _
  have hd3 : 0 ≤ d3 := distOne_nonneg _
  have hd4 : 0 ≤ d4 := distOne_nonneg _
  set A := g1 * g2 with hA
  set B := A * g3⁻¹ with hB
  have hP : latticePlaquette Y y μ ν = B * g4⁻¹ := rfl
  set a1 : ℍ[ℝ] := (g1 : ℍ[ℝ]) - 1
  set a2 : ℍ[ℝ] := (g2 : ℍ[ℝ]) - 1
  set a3 : ℍ[ℝ] := ((g3⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1
  set a4 : ℍ[ℝ] := ((g4⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1
  set eA : ℍ[ℝ] := (A : ℍ[ℝ]) - 1
  set eB : ℍ[ℝ] := (B : ℍ[ℝ]) - 1
  have h1 : eA = a1 + a2 + a1 * a2 := coe_mul_sub_one g1 g2
  have h2 : eB = eA + a3 + eA * a3 := coe_mul_sub_one A g3⁻¹
  have h3 : ((latticePlaquette Y y μ ν : UnitQuaternion) : ℍ[ℝ]) - 1 = eB + a4 + eB * a4 := by
    rw [hP]
    exact coe_mul_sub_one B g4⁻¹
  set E : ℍ[ℝ] := a1 * a2 + eA * a3 + eB * a4 with hE
  have hsum : ((latticePlaquette Y y μ ν : UnitQuaternion) : ℍ[ℝ]) - 1 = a1 + a2 + a3 + a4 + E := by
    rw [h3]
    calc eB + a4 + eB * a4 = (eA + a3 + eA * a3) + a4 + eB * a4 := by rw [← h2]
      _ = ((a1 + a2 + a1 * a2) + a3 + eA * a3) + a4 + eB * a4 := by rw [← h1]
      _ = _ := by
          rw [hE]
          abel
  have him : plaquetteCurl (imaginaryField Y) y μ ν =
      (((latticePlaquette Y y μ ν : UnitQuaternion) : ℍ[ℝ]) - 1).im - E.im := by
    rw [hsum]
    simp only [plaquetteCurl, imaginaryField, Quaternion.im_add]
    have e1 : a1.im = ((g1 : ℍ[ℝ])).im := by simp [a1]
    have e2 : a2.im = ((g2 : ℍ[ℝ])).im := by simp [a2]
    have e3 : a3.im = - ((g3 : ℍ[ℝ])).im := by simp [a3, coe_inv_unit]
    have e4 : a4.im = - ((g4 : ℍ[ℝ])).im := by simp [a4, coe_inv_unit]
    rw [e1, e2, e3, e4]
    abel
  have n1 : ‖a1‖ = d1 := rfl
  have n2 : ‖a2‖ = d2 := rfl
  have n3 : ‖a3‖ = d3 := distOne_inv g3
  have n4 : ‖a4‖ = d4 := distOne_inv g4
  have nA : ‖eA‖ ≤ d1 + d2 := distOne_mul_le g1 g2
  have nB : ‖eB‖ ≤ d1 + d2 + d3 := by
    have h := distOne_mul_le A g3⁻¹
    rw [distOne_inv] at h
    have hA2 : distOne A ≤ d1 + d2 := nA
    have : ‖eB‖ = distOne (A * g3⁻¹) := rfl
    linarith
  have nE : ‖E‖ ≤ (d1 + d2 + d3 + d4) ^ 2 := by
    calc ‖E‖ ≤ ‖a1 * a2‖ + ‖eA * a3‖ + ‖eB * a4‖ := norm_add₃_le
      _ = ‖a1‖ * ‖a2‖ + ‖eA‖ * ‖a3‖ + ‖eB‖ * ‖a4‖ := by simp only [norm_mul]
      _ ≤ d1 * d2 + (d1 + d2) * d3 + (d1 + d2 + d3) * d4 := by
          rw [n1, n2, n3, n4]
          gcongr
      _ ≤ _ := by nlinarith [mul_nonneg hd1 hd2, mul_nonneg hd1 hd3, mul_nonneg hd1 hd4,
            mul_nonneg hd2 hd3, mul_nonneg hd2 hd4, mul_nonneg hd3 hd4, sq_nonneg d1, sq_nonneg d2,
            sq_nonneg d3, sq_nonneg d4]
  rw [him]
  refine (norm_sub_le _ _).trans ?_
  exact add_le_add (norm_im_le_norm _) ((norm_im_le_norm _).trans nE)
theorem add_four_pow_four_le (a b c d : ℝ) :
    (a + b + c + d) ^ 4 ≤ 64 * (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) := by apply _root_.YangMills.Construction.PatchCurls.add_add_add_pow_four_le <;> assumption
theorem sum_plaquette_bond_le (P : Finset Lattice4) (Y : Lattice4 → Fin 4 → UnitQuaternion)
    (φ : Lattice4 × Fin 4 × Fin 4 → Lattice4 × Fin 4) (sel : Lattice4 × Fin 4 × Fin 4 → Fin 4)
    (hinj : ∀ a b, sel a = sel b → φ a = φ b → a ∈ orientedPlaquettesOf P →
      b ∈ orientedPlaquettesOf P → a = b)
    (hin : ∀ p ∈ orientedPlaquettesOf P, φ p ∈ bondsOf P) :
    ∑ p ∈ orientedPlaquettesOf P, distOne (Y (φ p).1 (φ p).2) ^ 4 ≤ 4 * quarticSum P Y := by
  classical
  have hfib : ∑ j : Fin 4, ∑ p ∈ (orientedPlaquettesOf P).filter (fun p => sel p = j),
      distOne (Y (φ p).1 (φ p).2) ^ 4 =
        ∑ p ∈ orientedPlaquettesOf P, distOne (Y (φ p).1 (φ p).2) ^ 4 :=
    Finset.sum_fiberwise_of_maps_to (fun p _ => Finset.mem_univ (sel p)) _
  rw [← hfib]
  have hone : ∀ j : Fin 4, ∑ p ∈ (orientedPlaquettesOf P).filter (fun p => sel p = j),
      distOne (Y (φ p).1 (φ p).2) ^ 4 ≤ quarticSum P Y := by
    intro j
    apply sum_comp_le_of_injOn _ φ _ (fun u => distOne (Y u.1 u.2) ^ 4)
      (fun u => by have := distOne_nonneg (Y u.1 u.2); positivity)
    · intro a ha b hb h
      have h1 := Finset.mem_filter.1 (Finset.mem_coe.1 ha)
      have h2 := Finset.mem_filter.1 (Finset.mem_coe.1 hb)
      exact hinj a b (h1.2.trans h2.2.symm) h h1.1 h2.1
    · intro p hp _
      exact hin p (Finset.mem_filter.1 hp).1
  calc _ ≤ ∑ _j : Fin 4, quarticSum P Y := Finset.sum_le_sum fun j _ => hone j
    _ = _ := by simp
theorem sum_norm_curl_sq_le (P : Finset Lattice4) (Y : Lattice4 → Fin 4 → UnitQuaternion) :
    ∑ p ∈ orientedPlaquettesOf P, ‖plaquetteCurl (imaginaryField Y) p.1 p.2.1 p.2.2‖ ^ 2 ≤
      2 * plaquetteEnergy P Y + 2048 * quarticSum P Y := by
  have hpt : ∀ p ∈ orientedPlaquettesOf P, ‖plaquetteCurl (imaginaryField Y) p.1 p.2.1 p.2.2‖ ^ 2 ≤
      2 * distOne (latticePlaquette Y p.1 p.2.1 p.2.2) ^ 2 +
      128 * (distOne (Y p.1 p.2.1) ^ 4 + distOne (Y (p.1 + basisVector p.2.1) p.2.2) ^ 4 +
        distOne (Y (p.1 + basisVector p.2.2) p.2.1) ^ 4 + distOne (Y p.1 p.2.2) ^ 4) := by
    intro p _
    have h := norm_curl_le Y p.1 p.2.1 p.2.2
    have h0 := norm_nonneg (plaquetteCurl (imaginaryField Y) p.1 p.2.1 p.2.2)
    set a := distOne (latticePlaquette Y p.1 p.2.1 p.2.2)
    set s := distOne (Y p.1 p.2.1) + distOne (Y (p.1 + basisVector p.2.1) p.2.2) +
      distOne (Y (p.1 + basisVector p.2.2) p.2.1) + distOne (Y p.1 p.2.2) with hs
    have h4 := add_four_pow_four_le (distOne (Y p.1 p.2.1))
      (distOne (Y (p.1 + basisVector p.2.1) p.2.2))
      (distOne (Y (p.1 + basisVector p.2.2) p.2.1)) (distOne (Y p.1 p.2.2))
    have h5 : ‖plaquetteCurl (imaginaryField Y) p.1 p.2.1 p.2.2‖ ^ 2 ≤ (a + s ^ 2) ^ 2 :=
      pow_le_pow_left₀ h0 h 2
    have h6 : (a + s ^ 2) ^ 2 ≤ 2 * a ^ 2 + 2 * s ^ 4 := by
      nlinarith [sq_nonneg (a - s ^ 2)]
    linarith
  have hb1 := sum_plaquette_bond_le P Y (fun p => (p.1, p.2.1)) (fun p => p.2.2)
    (by
      intro a b h1 h2 _ _
      simp only [Prod.mk.injEq] at h2
      exact Prod.ext h2.1 (Prod.ext h2.2 h1))
    (by
      intro p hp
      obtain ⟨h1, -, h3, -, -⟩ := mem_orientedPlaquettesOf.1 hp
      exact mem_bondsOf.2 ⟨h1, h3⟩)
  have hb2 := sum_plaquette_bond_le P Y (fun p => (p.1 + basisVector p.2.1, p.2.2)) (fun p => p.2.1)
    (by
      intro a b h1 h2 _ _
      simp only [Prod.mk.injEq] at h2
      rw [h1] at h2
      exact Prod.ext (add_right_cancel h2.1) (Prod.ext h1 h2.2))
    (by
      intro p hp
      obtain ⟨-, -, h3, -, h5⟩ := mem_orientedPlaquettesOf.1 hp
      exact mem_bondsOf.2 ⟨h3, h5⟩)
  have hb3 := sum_plaquette_bond_le P Y (fun p => (p.1 + basisVector p.2.2, p.2.1)) (fun p => p.2.2)
    (by
      intro a b h1 h2 _ _
      simp only [Prod.mk.injEq] at h2
      rw [h1] at h2
      exact Prod.ext (add_right_cancel h2.1) (Prod.ext h2.2 h1))
    (by
      intro p hp
      obtain ⟨-, -, -, h4, h5⟩ := mem_orientedPlaquettesOf.1 hp
      refine mem_bondsOf.2 ⟨h4, ?_⟩
      have : p.1 + basisVector p.2.2 + basisVector p.2.1 =
          p.1 + basisVector p.2.1 + basisVector p.2.2 := by abel
      simp only [this]
      exact h5)
  have hb4 := sum_plaquette_bond_le P Y (fun p => (p.1, p.2.2)) (fun p => p.2.1)
    (by
      intro a b h1 h2 _ _
      simp only [Prod.mk.injEq] at h2
      exact Prod.ext h2.1 (Prod.ext h1 h2.2))
    (by
      intro p hp
      obtain ⟨h1, -, -, h4, -⟩ := mem_orientedPlaquettesOf.1 hp
      exact mem_bondsOf.2 ⟨h1, h4⟩)
  simp only at hb1 hb2 hb3 hb4
  calc _ ≤ ∑ p ∈ orientedPlaquettesOf P, (2 * distOne (latticePlaquette Y p.1 p.2.1 p.2.2) ^ 2 +
        128 * (distOne (Y p.1 p.2.1) ^ 4 + distOne (Y (p.1 + basisVector p.2.1) p.2.2) ^ 4 +
        distOne (Y (p.1 + basisVector p.2.2) p.2.1) ^ 4 + distOne (Y p.1 p.2.2) ^ 4)) :=
        Finset.sum_le_sum hpt
    _ = 2 * plaquetteEnergy P Y + 128 * (∑ p ∈ orientedPlaquettesOf P, distOne (Y p.1 p.2.1) ^ 4 +
        ∑ p ∈ orientedPlaquettesOf P, distOne (Y (p.1 + basisVector p.2.1) p.2.2) ^ 4 +
        ∑ p ∈ orientedPlaquettesOf P, distOne (Y (p.1 + basisVector p.2.2) p.2.1) ^ 4 +
        ∑ p ∈ orientedPlaquettesOf P, distOne (Y p.1 p.2.2) ^ 4) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib,
          Finset.sum_add_distrib, Finset.sum_add_distrib]
        rfl
    _ ≤ _ := by linarith
end Curl
section APriori
theorem exists_lattice_l4_bound (hH : hardyLittlewoodSobolevStatement) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D E : Finset Lattice4) (g : Lattice4 → ℝ), (∀ y, 0 ≤ g y) →
      ∑ x ∈ E, (∑ y ∈ D, cubicKernel (x - y) * g y) ^ 4 ≤ C * (∑ y ∈ D, g y ^ 2) ^ 2 := by
  obtain ⟨C0, hC0, h0⟩ := hH 2 4 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C0 ^ 4, by positivity, ?_⟩
  intro D E g hg
  have h := h0 D E g
  have hc : ∀ v, 0 ≤ cubicKernel v := fun v => by unfold cubicKernel; positivity
  have hI : ∀ x, 0 ≤ ∑ y ∈ D, cubicKernel (x - y) * g y := fun x =>
    Finset.sum_nonneg fun y _ => mul_nonneg (hc _) (hg y)
  have e1 : ∑ x ∈ E, |∑ y ∈ D, cubicKernel (x - y) * g y| ^ (4 : ℝ) =
      ∑ x ∈ E, (∑ y ∈ D, cubicKernel (x - y) * g y) ^ 4 := by
    apply Finset.sum_congr rfl
    intro x _
    rw [abs_of_nonneg (hI x)]
    exact_mod_cast Real.rpow_natCast _ 4
  have e2 : ∑ y ∈ D, |g y| ^ (2 : ℝ) = ∑ y ∈ D, g y ^ 2 := by
    apply Finset.sum_congr rfl
    intro y _
    rw [abs_of_nonneg (hg y)]
    exact_mod_cast Real.rpow_natCast _ 2
  rw [e1, e2] at h
  set t := ∑ x ∈ E, (∑ y ∈ D, cubicKernel (x - y) * g y) ^ 4 with ht
  set S := ∑ y ∈ D, g y ^ 2 with hS
  have ht0 : 0 ≤ t := Finset.sum_nonneg fun x _ => by positivity
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun y _ => sq_nonneg _
  have h1 : t = (t ^ (1 / 4 : ℝ)) ^ 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht0]
    norm_num
  have h2 : (S ^ (1 / 2 : ℝ)) ^ 4 = S ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hS0, ← Real.rpow_natCast]
    norm_num
  rw [h1]
  calc _ ≤ (C0 * S ^ (1 / 2 : ℝ)) ^ 4 := pow_le_pow_left₀ (by positivity) h 4
    _ = _ := by rw [mul_pow, h2]
theorem re_mul_eq_re_mul_im (q Y : ℍ[ℝ]) (hq : q.re = 0) : (q * Y).re = (q * Y.im).re := by
  simp [Quaternion.re_mul, hq]
theorem re_mul_self_of_re_eq_zero (q : ℍ[ℝ]) (hq : q.re = 0) : (q * q).re = -‖q‖ ^ 2 := by
  rw [norm_sq_eq_components, hq]
  simp only [Quaternion.re_mul, hq]
  ring
theorem cube_mul_le_young (d h : ℝ) : d ^ 3 * h ≤ (1 / 4) * d ^ 4 + (27 / 4) * h ^ 4 := by
  nlinarith [mul_nonneg (sq_nonneg (d - 3 * h)) (by nlinarith [sq_nonneg (d + h), sq_nonneg h] :
    (0 : ℝ) ≤ d ^ 2 + 2 * d * h + 3 * h ^ 2)]
theorem sum_kernel_curl_pow_four_le (C C4 : ℝ) (hC : 0 < C) (hC4 : 0 < C4)
    (h4 : ∀ (D E : Finset Lattice4) (g : Lattice4 → ℝ), (∀ y, 0 ≤ g y) →
      ∑ x ∈ E, (∑ y ∈ D, cubicKernel (x - y) * g y) ^ 4 ≤ C4 * (∑ y ∈ D, g y ^ 2) ^ 2)
    (P : Finset Lattice4) (H : Lattice4 × Fin 4 → Lattice4 × Fin 4 × Fin 4 → ℝ)
    (hH : ∀ b p, |H b p| ≤ C * cubicKernel (b.1 - p.1))
    (u : Lattice4 × Fin 4 × Fin 4 → ℍ[ℝ]) :
    ∑ b ∈ bondsOf P, ‖∑ p ∈ orientedPlaquettesOf P, H b p • u p‖ ^ 4 ≤
      4 * C ^ 4 * C4 * (16 * ∑ p ∈ orientedPlaquettesOf P, ‖u p‖ ^ 2) ^ 2 := by
  classical
  set PQ := orientedPlaquettesOf P with hPQ
  set D : Lattice4 → ℝ := fun y => ∑ p ∈ PQ.filter (fun p => p.1 = y), ‖u p‖ with hD
  have hD0 : ∀ y, 0 ≤ D y := fun y => Finset.sum_nonneg fun p _ => norm_nonneg _
  have hc : ∀ v, 0 ≤ cubicKernel v := fun v => by unfold cubicKernel; positivity
  set I : Lattice4 → ℝ := fun x => ∑ y ∈ P, cubicKernel (x - y) * D y with hI
  have hI0 : ∀ x, 0 ≤ I x := fun x => Finset.sum_nonneg fun y _ => mul_nonneg (hc _) (hD0 y)
  have hmaps : ∀ p ∈ PQ, p.1 ∈ P := fun p hp => (mem_orientedPlaquettesOf.1 hp).1
  have hpt : ∀ b, ‖∑ p ∈ PQ, H b p • u p‖ ≤ C * I b.1 := by
    intro b
    calc _ ≤ ∑ p ∈ PQ, ‖H b p • u p‖ := norm_sum_le _ _
      _ ≤ ∑ p ∈ PQ, C * (cubicKernel (b.1 - p.1) * ‖u p‖) := by
          apply Finset.sum_le_sum
          intro p _
          rw [norm_smul, Real.norm_eq_abs, ← mul_assoc]
          exact mul_le_mul_of_nonneg_right (hH b p) (norm_nonneg _)
      _ = C * ∑ y ∈ P, ∑ p ∈ PQ.filter (fun p => p.1 = y), cubicKernel (b.1 - p.1) * ‖u p‖ := by
          rw [← Finset.mul_sum, Finset.sum_fiberwise_of_maps_to hmaps]
      _ = _ := by
          congr 1
          apply Finset.sum_congr rfl
          intro y _
          simp only [hD]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p hp
          rw [(Finset.mem_filter.1 hp).2]
  have hb : ∑ b ∈ bondsOf P, (I b.1) ^ 4 ≤ 4 * ∑ x ∈ P, I x ^ 4 := by
    have hfib : ∑ j : Fin 4, ∑ b ∈ (bondsOf P).filter (fun b => b.2 = j), (I b.1) ^ 4 =
        ∑ b ∈ bondsOf P, (I b.1) ^ 4 :=
      Finset.sum_fiberwise_of_maps_to (fun b _ => Finset.mem_univ b.2) _
    rw [← hfib]
    have hone : ∀ j : Fin 4, ∑ b ∈ (bondsOf P).filter (fun b => b.2 = j), (I b.1) ^ 4 ≤
        ∑ x ∈ P, I x ^ 4 := by
      intro j
      apply sum_comp_le_of_injOn _ Prod.fst _ (fun x => I x ^ 4) (fun x => by have := hI0 x; positivity)
      · intro a ha b hb h
        have h1 := (Finset.mem_filter.1 (Finset.mem_coe.1 ha)).2
        have h2 := (Finset.mem_filter.1 (Finset.mem_coe.1 hb)).2
        exact Prod.ext h (h1.trans h2.symm)
      · intro b hb _
        exact (mem_bondsOf.1 (Finset.mem_filter.1 hb).1).1
    calc _ ≤ ∑ _j : Fin 4, ∑ x ∈ P, I x ^ 4 := Finset.sum_le_sum fun j _ => hone j
      _ = _ := by simp
  have hDsq : ∑ y ∈ P, D y ^ 2 ≤ 16 * ∑ p ∈ PQ, ‖u p‖ ^ 2 := by
    have hcard : ∀ y, ((PQ.filter (fun p => p.1 = y)).card : ℝ) ≤ 16 := by
      intro y
      have hle : (PQ.filter (fun p => p.1 = y)).card ≤
          (Finset.univ : Finset (Fin 4 × Fin 4)).card := by
        apply Finset.card_le_card_of_injOn (fun p => p.2)
          (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
        intro a ha b hb h
        have h1 := (Finset.mem_filter.1 (Finset.mem_coe.1 ha)).2
        have h2 := (Finset.mem_filter.1 (Finset.mem_coe.1 hb)).2
        exact Prod.ext (h1.trans h2.symm) h
      simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at hle
      exact_mod_cast hle
    calc _ ≤ ∑ y ∈ P, 16 * ∑ p ∈ PQ.filter (fun p => p.1 = y), ‖u p‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro y _
          have h1 := sq_sum_le_card_mul_sum_sq (s := PQ.filter (fun p => p.1 = y))
            (f := fun p => ‖u p‖)
          refine h1.trans ?_
          exact mul_le_mul_of_nonneg_right (hcard y) (Finset.sum_nonneg fun p _ => sq_nonneg _)
      _ = _ := by
          rw [← Finset.mul_sum, Finset.sum_fiberwise_of_maps_to hmaps]
  calc _ ≤ ∑ b ∈ bondsOf P, C ^ 4 * (I b.1) ^ 4 := by
        apply Finset.sum_le_sum
        intro b _
        rw [← mul_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hpt b) 4
    _ = C ^ 4 * ∑ b ∈ bondsOf P, (I b.1) ^ 4 := by rw [Finset.mul_sum]
    _ ≤ C ^ 4 * (4 * ∑ x ∈ P, I x ^ 4) := by gcongr
    _ ≤ C ^ 4 * (4 * (C4 * (∑ y ∈ P, D y ^ 2) ^ 2)) := by
        gcongr
        exact h4 P P D hD0
    _ ≤ C ^ 4 * (4 * (C4 * (16 * ∑ p ∈ PQ, ‖u p‖ ^ 2) ^ 2)) := by gcongr
    _ = _ := by ring
end APriori
section Main
theorem a_priori_bound (hHom : randomStaircaseHomotopyStatement)
    (hFrac : hardyLittlewoodSobolevStatement) :
    ∃ K c₁ : ℝ, 0 < K ∧ 0 < c₁ ∧ c₁ ≤ 1 ∧ ∀ (l : ℕ) (c : Lattice4) (P : Finset Lattice4), 1 ≤ l →
      IsFilledToward l c P → ∀ Y : Lattice4 → Fin 4 → UnitQuaternion,
        (∀ γ : Lattice4 → UnitQuaternion, quarticSum P Y ≤ quarticSum P (latticeGaugeTransform γ Y)) →
        quarticSum P Y ≤ c₁ → quarticSum P Y ≤ K * plaquetteEnergy P Y ^ 2 := by
  classical
  obtain ⟨C, hC, hHf⟩ := hHom
  obtain ⟨C4, hC4, h4⟩ := exists_lattice_l4_bound hFrac
  set K0 : ℝ := (27 / 2) * (4 * C ^ 4 * C4) * 256 with hK0
  have hK0pos : 0 < K0 := by positivity
  refine ⟨16 * K0, min 1 (1 / (4 * K0 * 2048 ^ 2)), by positivity, by positivity, min_le_left _ _, ?_⟩
  intro l c P hl hfill Y hmin hsmall
  obtain ⟨H, G, hH, -, hE⟩ := hHf l c P hl hfill
  obtain ⟨e1, e2, -⟩ := hE ℍ[ℝ]
  set w := imaginaryField Y with hw
  set pm := randomPathMean l c w with hpm
  have hwim : ∀ x i, w x i ∈ imaginaryQuaternions := fun x i => (Quaternion.re_im _ : _ = _)
  have him : ∀ x ∈ P, pm x ∈ imaginaryQuaternions := by
    intro x hx
    rw [hpm, e1 w x hx]
    exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (hwim _ _)
  set ξ : Lattice4 → imaginaryQuaternions := fun x => if h : x ∈ P then ⟨pm x, him x h⟩ else 0 with hξ
  have hst := first_variation_eq_zero P Y hmin ξ
  set Ψ := quarticSum P Y with hΨ
  set E := plaquetteEnergy P Y with hE'
  have hE0 : 0 ≤ E := Finset.sum_nonneg fun p _ => sq_nonneg _
  have hΨ0 : 0 ≤ Ψ := Finset.sum_nonneg fun b _ => by have := distOne_nonneg (Y b.1 b.2); positivity
  have hsm1 : Ψ ≤ 1 := hsmall.trans (min_le_left _ _)
  have hsm2 : Ψ ≤ 1 / (4 * K0 * 2048 ^ 2) := hsmall.trans (min_le_right _ _)
  set hb : Lattice4 × Fin 4 → ℍ[ℝ] :=
    fun b => ∑ p ∈ orientedPlaquettesOf P, H b p • plaquetteCurl w p.1 p.2.1 p.2.2 with hhb
  have hdle : ∀ b ∈ bondsOf P, distOne (Y b.1 b.2) ≤ 1 := by
    intro b hb'
    have h1 : distOne (Y b.1 b.2) ^ 4 ≤ Ψ :=
      Finset.single_le_sum (f := fun b : Lattice4 × Fin 4 => distOne (Y b.1 b.2) ^ 4)
        (fun b _ => by have := distOne_nonneg (Y b.1 b.2); positivity) hb'
    by_contra hc
    have h2 : 1 < distOne (Y b.1 b.2) := not_le.1 hc
    have h3 : 1 < distOne (Y b.1 b.2) ^ 4 := one_lt_pow₀ h2 (by norm_num)
    linarith
  have hterm : ∀ b ∈ bondsOf P, distOne (Y b.1 b.2) ^ 2 *
      ((((ξ b.1 : ℍ[ℝ]) - ξ (b.1 + basisVector b.2)) * Y b.1 b.2).re) =
      distOne (Y b.1 b.2) ^ 2 * (-‖w b.1 b.2‖ ^ 2 - (hb b * w b.1 b.2).re) := by
    intro b hb'
    obtain ⟨h1, h2⟩ := mem_bondsOf.1 hb'
    have hx1 : (ξ b.1 : ℍ[ℝ]) = pm b.1 := by simp [hξ, h1]
    have hx2 : (ξ (b.1 + basisVector b.2) : ℍ[ℝ]) = pm (b.1 + basisVector b.2) := by simp [hξ, h2]
    have hk := e2 w b.1 b.2 h1 h2
    have hq : (ξ b.1 : ℍ[ℝ]) - ξ (b.1 + basisVector b.2) = w b.1 b.2 - hb b := by
      rw [hx1, hx2]
      simp only [hhb]
      rw [← hk]
      abel
    have hqre : ((ξ b.1 : ℍ[ℝ]) - ξ (b.1 + basisVector b.2)).re = 0 := by
      have a1 : ((ξ b.1 : imaginaryQuaternions) : ℍ[ℝ]).re = 0 := (ξ b.1).2
      have a2 : ((ξ (b.1 + basisVector b.2) : imaginaryQuaternions) : ℍ[ℝ]).re = 0 :=
        (ξ (b.1 + basisVector b.2)).2
      simp [a1, a2]
    have hwre : (w b.1 b.2).re = 0 := hwim _ _
    congr 1
    rw [re_mul_eq_re_mul_im _ _ hqre, hq, sub_mul, Quaternion.re_sub]
    have : ((Y b.1 b.2 : UnitQuaternion) : ℍ[ℝ]).im = w b.1 b.2 := rfl
    rw [this, re_mul_self_of_re_eq_zero _ hwre]
  rw [Finset.sum_congr rfl hterm] at hst
  have hmain : (3 / 4) * Ψ ≤ (1 / 4) * Ψ + (27 / 4) * ∑ b ∈ bondsOf P, ‖hb b‖ ^ 4 := by
    have hpt : ∀ b ∈ bondsOf P, (3 / 4) * distOne (Y b.1 b.2) ^ 4 ≤
        -(distOne (Y b.1 b.2) ^ 2 * (-‖w b.1 b.2‖ ^ 2 - (hb b * w b.1 b.2).re)) +
          ((1 / 4) * distOne (Y b.1 b.2) ^ 4 + (27 / 4) * ‖hb b‖ ^ 4) := by
      intro b hb'
      set d := distOne (Y b.1 b.2) with hd
      have hd0 : 0 ≤ d := distOne_nonneg _
      have hd1 : d ≤ 1 := hdle b hb'
      have hw2 : ‖w b.1 b.2‖ ^ 2 = d ^ 2 * (1 - d ^ 2 / 4) := norm_im_sq_unit _
      have hwd : ‖w b.1 b.2‖ ≤ d := norm_im_le_distOne _
      have hre : -(hb b * w b.1 b.2).re ≤ ‖hb b‖ * d := by
        have := (abs_le.1 (abs_re_le_norm (hb b * w b.1 b.2))).1
        rw [norm_mul] at this
        have h2 : ‖hb b‖ * ‖w b.1 b.2‖ ≤ ‖hb b‖ * d :=
          mul_le_mul_of_nonneg_left hwd (norm_nonneg _)
        linarith
      have hy := cube_mul_le_young d ‖hb b‖
      have hd2 : d ^ 2 ≤ 1 := by nlinarith
      have hmul : d ^ 2 * (-(hb b * w b.1 b.2).re) ≤ d ^ 2 * (‖hb b‖ * d) :=
        mul_le_mul_of_nonneg_left hre (sq_nonneg d)
      have hT : (3 / 4) * d ^ 4 ≤ d ^ 2 * ‖w b.1 b.2‖ ^ 2 := by
        rw [hw2]
        nlinarith [pow_nonneg hd0 4, mul_nonneg (sq_nonneg d) (sq_nonneg d),
          mul_nonneg (mul_nonneg (sq_nonneg d) (sq_nonneg d)) (sub_nonneg.2 hd2)]
      nlinarith
    have hs := Finset.sum_le_sum hpt
    rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, hst, neg_zero, zero_add,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum] at hs
    exact hs
  have hk := sum_kernel_curl_pow_four_le C C4 hC hC4 h4 P H hH
    (fun p => plaquetteCurl w p.1 p.2.1 p.2.2)
  have hcu := sum_norm_curl_sq_le P Y
  set Cu := ∑ p ∈ orientedPlaquettesOf P, ‖plaquetteCurl w p.1 p.2.1 p.2.2‖ ^ 2 with hCu
  have hCu0 : 0 ≤ Cu := Finset.sum_nonneg fun p _ => sq_nonneg _
  have hΨK : Ψ ≤ K0 * (2 * E + 2048 * Ψ) ^ 2 := by
    have h1 : (1 / 2) * Ψ ≤ (27 / 4) * (4 * C ^ 4 * C4 * (16 * Cu) ^ 2) := by
      have : ∑ b ∈ bondsOf P, ‖hb b‖ ^ 4 ≤ 4 * C ^ 4 * C4 * (16 * Cu) ^ 2 := hk
      linarith
    have h2 : Cu ^ 2 ≤ (2 * E + 2048 * Ψ) ^ 2 := pow_le_pow_left₀ hCu0 hcu 2
    have h3 : (0 : ℝ) ≤ 4 * C ^ 4 * C4 := by positivity
    rw [hK0]
    nlinarith
  have hsq : (2 * E + 2048 * Ψ) ^ 2 ≤ 8 * E ^ 2 + 2 * 2048 ^ 2 * Ψ ^ 2 := by
    nlinarith [sq_nonneg (2 * E - 2048 * Ψ)]
  have hhalf : K0 * (2 * 2048 ^ 2 * Ψ ^ 2) ≤ (1 / 2) * Ψ := by
    have h1 : K0 * (4 * 2048 ^ 2) * Ψ ≤ 1 := by
      have hpos : (0 : ℝ) < 4 * K0 * 2048 ^ 2 := by positivity
      rw [le_div_iff₀ hpos] at hsm2
      nlinarith
    nlinarith
  nlinarith
end Main
section Reach
theorem latticeGaugeTransform_comp (γ γ' : Lattice4 → UnitQuaternion)
    (X : Lattice4 → Fin 4 → UnitQuaternion) :
    latticeGaugeTransform γ (latticeGaugeTransform γ' X) =
      latticeGaugeTransform (fun x => γ x * γ' x) X := by
  funext y i
  simp only [latticeGaugeTransform, mul_inv_rev]
  group
instance compactSpace_unitQuaternion : CompactSpace UnitQuaternion := by
  have h : IsCompact ((unitary ℍ[ℝ] : Submonoid ℍ[ℝ]) : Set ℍ[ℝ]) := by
    apply Metric.isCompact_of_isClosed_isBounded isClosed_unitary
    refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨1, ?_⟩
    intro q hq
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact (norm_coe_unit ⟨q, hq⟩).le
  exact isCompact_iff_compactSpace.1 h
theorem continuous_distOne : Continuous distOne := by
  unfold distOne
  exact (continuous_subtype_val.sub continuous_const).norm
theorem continuous_quarticSum_gauge (P : Finset Lattice4) (X : Lattice4 → Fin 4 → UnitQuaternion) :
    Continuous fun γ : Lattice4 → UnitQuaternion => quarticSum P (latticeGaugeTransform γ X) := by
  unfold quarticSum
  refine continuous_finsetSum _ fun b _ => ?_
  refine (continuous_distOne.comp ?_).pow 4
  simp only [latticeGaugeTransform]
  exact ((continuous_apply _).mul continuous_const).mul (continuous_apply _).inv
theorem exists_minimizing_gauge (P : Finset Lattice4) (X : Lattice4 → Fin 4 → UnitQuaternion) :
    ∃ γ : Lattice4 → UnitQuaternion, ∀ γ',
      quarticSum P (latticeGaugeTransform γ X) ≤ quarticSum P (latticeGaugeTransform γ' X) := by
  obtain ⟨γ, -, hγ⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty (α := Lattice4 → UnitQuaternion))
    (continuous_quarticSum_gauge P X).continuousOn
  exact ⟨γ, fun γ' => hγ (Set.mem_univ γ')⟩
inductive LayerReachable : Finset Lattice4 → Prop
  | single (x : Lattice4) : LayerReachable {x}
  | grow (P' P'' : Finset Lattice4) (i : Fin 4) : LayerReachable P' → LayerStep P' P'' i →
      (∃ l c, 1 ≤ l ∧ IsFilledToward l c P'') → LayerReachable P''
theorem LayerReachable.exists_gauge_bound (K c₁ : ℝ) (hK : 0 < K)
    (hap : ∀ (l : ℕ) (c : Lattice4) (P : Finset Lattice4), 1 ≤ l → IsFilledToward l c P →
      ∀ Y : Lattice4 → Fin 4 → UnitQuaternion,
        (∀ γ : Lattice4 → UnitQuaternion, quarticSum P Y ≤ quarticSum P (latticeGaugeTransform γ Y)) →
        quarticSum P Y ≤ c₁ → quarticSum P Y ≤ K * plaquetteEnergy P Y ^ 2)
    (X : Lattice4 → Fin 4 → UnitQuaternion) (B : ℝ) (hB : 0 ≤ B) (hsmall : (136 * K + 27) * B ^ 2 ≤ c₁)
    {P : Finset Lattice4} (hP : LayerReachable P) (hE : plaquetteEnergy P X ≤ B) :
    ∃ γ : Lattice4 → UnitQuaternion, quarticSum P (latticeGaugeTransform γ X) ≤ K * plaquetteEnergy P X ^ 2 := by
  induction hP with
  | single x =>
    refine ⟨fun _ => 1, ?_⟩
    have hempty : bondsOf ({x} : Finset Lattice4) = ∅ := by
      ext b
      simp only [mem_bondsOf, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
      rintro rfl h
      have := congrFun (add_eq_left.1 h) b.2
      simp [basisVector] at this
    have h0 : quarticSum {x} (latticeGaugeTransform (fun _ => 1) X) = 0 := by
      simp [quarticSum, hempty]
    rw [h0]
    positivity
  | grow P' P'' i hR hG hfill ih =>
    have hE' : plaquetteEnergy P' X ≤ B := (plaquetteEnergy_mono hG.subset X).trans hE
    obtain ⟨γ', h1⟩ := ih hE'
    obtain ⟨γ'', h2⟩ := exists_layer_gauge hG γ' X
    obtain ⟨γ, hγ⟩ := exists_minimizing_gauge P'' X
    obtain ⟨l, c, hl, hfl⟩ := hfill
    set Y := latticeGaugeTransform γ X with hY
    have hE0 : 0 ≤ plaquetteEnergy P'' X := Finset.sum_nonneg fun p _ => sq_nonneg _
    have hE'0 : 0 ≤ plaquetteEnergy P' X := Finset.sum_nonneg fun p _ => sq_nonneg _
    have hmono : plaquetteEnergy P' X ≤ plaquetteEnergy P'' X := plaquetteEnergy_mono hG.subset X
    have hsq : plaquetteEnergy P' X ^ 2 ≤ plaquetteEnergy P'' X ^ 2 := pow_le_pow_left₀ hE'0 hmono 2
    have hB2 : plaquetteEnergy P'' X ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hE0 hE 2
    have hless : quarticSum P'' Y ≤ c₁ := by
      calc quarticSum P'' Y ≤ quarticSum P'' (latticeGaugeTransform γ'' X) := hγ γ''
        _ ≤ 136 * quarticSum P' (latticeGaugeTransform γ' X) + 27 * plaquetteEnergy P'' X ^ 2 := h2
        _ ≤ 136 * (K * plaquetteEnergy P' X ^ 2) + 27 * plaquetteEnergy P'' X ^ 2 := by gcongr
        _ ≤ 136 * (K * plaquetteEnergy P'' X ^ 2) + 27 * plaquetteEnergy P'' X ^ 2 := by gcongr
        _ = (136 * K + 27) * plaquetteEnergy P'' X ^ 2 := by ring
        _ ≤ (136 * K + 27) * B ^ 2 := by gcongr
        _ ≤ c₁ := hsmall
    have hminY : ∀ γ₂ : Lattice4 → UnitQuaternion,
        quarticSum P'' Y ≤ quarticSum P'' (latticeGaugeTransform γ₂ Y) := by
      intro γ₂
      rw [hY, latticeGaugeTransform_comp]
      exact hγ _
    refine ⟨γ, ?_⟩
    have := hap l c P'' hl hfl Y hminY hless
    rwa [hY, plaquetteEnergy_gaugeTransform] at this
variable (T : ℤ)
def boxBelow (lo : Lattice4) : Finset Lattice4 := Fintype.piFinset fun i => Finset.Icc (lo i) T
theorem mem_boxBelow {lo x : Lattice4} : x ∈ boxBelow T lo ↔ ∀ i, lo i ≤ x i ∧ x i ≤ T := by
  simp [boxBelow, Fintype.mem_piFinset]
theorem basisVector_self (i : Fin 4) : basisVector i i = 1 := by simp [basisVector]
theorem basisVector_of_ne {i j : Fin 4} (h : j ≠ i) : basisVector i j = 0 := by simp [basisVector, h]
theorem boxBelow_layerStep (lo : Lattice4) (i : Fin 4) (h : lo i + 1 ≤ T) :
    LayerStep (boxBelow T (lo + basisVector i)) (boxBelow T lo) i := by
  have key : ∀ x, x ∈ boxBelow T lo → x ∉ boxBelow T (lo + basisVector i) → x i = lo i := by
    intro x hx hx'
    by_contra hne
    apply hx'
    rw [mem_boxBelow] at hx ⊢
    intro k
    have := hx k
    by_cases hk : k = i
    · subst hk
      simp only [Pi.add_apply, basisVector_self]
      constructor <;> omega
    · simp only [Pi.add_apply, basisVector_of_ne hk, add_zero]
      exact this
  have hu : ∀ j k : Fin 4, 0 ≤ basisVector j k := by
    intro j k
    simp only [basisVector, Pi.single_apply]
    split_ifs <;> norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [mem_boxBelow] at hx ⊢
    intro j
    have := hx j
    have h2 := hu i j
    simp only [Pi.add_apply] at this
    constructor <;> omega
  · intro x hx hx'
    have hxi := key x hx hx'
    rw [mem_boxBelow] at hx ⊢
    intro k
    have hk := hx k
    by_cases hki : k = i
    · subst hki
      simp only [Pi.add_apply, basisVector_self]
      constructor <;> omega
    · simp only [Pi.add_apply, basisVector_of_ne hki, add_zero]
      exact hk
  · intro y hy j hj
    rw [mem_boxBelow] at hy hj ⊢
    intro k
    have h1 := hy k
    have h2 := hj k
    have h3 := hu j k
    simp only [Pi.add_apply] at h1 h2 ⊢
    constructor <;> omega
  · intro x hx hx' j hji hj
    have hxi := key x hx hx'
    rw [mem_boxBelow] at hx hj ⊢
    intro k
    have h1 := hj k
    have h2 := hx k
    by_cases hki : k = i
    · subst hki
      simp only [Pi.add_apply, basisVector_self, basisVector_of_ne (Ne.symm hji)] at h1 ⊢
      constructor <;> omega
    · simp only [Pi.add_apply, basisVector_of_ne hki, add_zero] at h1 ⊢
      have h3 := hu j k
      constructor <;> omega
theorem boxBelow_isFilledToward (lo : Lattice4) (m : ℕ) (hm : 1 ≤ m)
    (hlo : ∀ i, lo i = T - m ∨ lo i = T - m + 1) :
    IsFilledToward m (fun _ => T - m + 1) (boxBelow T lo) := by
  have hq : ∀ q ∈ cornerCube m (fun _ => T - m + 1), ∀ i, T - m + 1 ≤ q i ∧ q i ≤ T := by
    intro q hq i
    have := (Fintype.mem_piFinset.1 hq) i
    rw [Finset.mem_Ico] at this
    dsimp only at this
    constructor <;> omega
  refine ⟨?_, ?_, ?_⟩
  · intro q hq'
    rw [mem_boxBelow]
    intro i
    have := hq q hq' i
    have h2 := hlo i
    constructor <;> omega
  · intro x hx i
    rw [mem_boxBelow] at hx
    have h1 := hx i
    have h2 := hlo i
    rw [abs_le]
    dsimp only
    constructor <;> omega
  · intro x hx q hq' y hy
    rw [mem_boxBelow] at hx ⊢
    intro i
    have h1 := hx i
    have h2 := hq q hq' i
    have h3 := hy i
    have h4 := hlo i
    rcases le_total (x i) (q i) with h | h
    · rw [min_eq_left h, max_eq_right h] at h3
      constructor <;> omega
    · rw [min_eq_right h, max_eq_left h] at h3
      constructor <;> omega
def loweredCorner (m : ℕ) (U : Finset (Fin 4)) : Lattice4 := by
  classical exact fun i => if i ∈ U then T - m else T - m + 1
theorem layerReachable_cube (m : ℕ) (hm : 1 ≤ m) :
    LayerReachable (boxBelow T fun _ => T - m + 1) := by
  classical
  induction m, hm using Nat.le_induction with
  | base =>
    have : boxBelow T (fun _ => T - ((1 : ℕ) : ℤ) + 1) = {fun _ => T} := by
      ext x
      rw [mem_boxBelow, Finset.mem_singleton]
      constructor
      · intro h
        funext i
        have := h i
        push_cast at this
        omega
      · rintro rfl i
        push_cast
        omega
    rw [this]
    exact LayerReachable.single _
  | succ m hm ih =>
    have hU : ∀ U : Finset (Fin 4), LayerReachable (boxBelow T (loweredCorner T m U)) := by
      intro U
      induction U using Finset.induction_on with
      | empty =>
        have : loweredCorner T m ∅ = fun _ => T - m + 1 := by
          funext i
          simp [loweredCorner]
        rw [this]
        exact ih
      | insert i U hi ihU =>
        have e : loweredCorner T m U = loweredCorner T m (insert i U) + basisVector i := by
          funext k
          simp only [loweredCorner, Pi.add_apply, Finset.mem_insert]
          by_cases hki : k = i
          · subst hki
            simp [hi, basisVector_self]
          · simp [hki, basisVector_of_ne hki]
        have hlow : loweredCorner T m (insert i U) i + 1 ≤ T := by
          simp only [loweredCorner, Finset.mem_insert, true_or, if_true]
          have : (1 : ℤ) ≤ m := by exact_mod_cast hm
          omega
        have hG := boxBelow_layerStep T (loweredCorner T m (insert i U)) i hlow
        rw [← e] at hG
        refine LayerReachable.grow _ _ i ihU hG ⟨m, fun _ => T - m + 1, hm, ?_⟩
        apply boxBelow_isFilledToward T _ m hm
        intro k
        simp only [loweredCorner]
        split_ifs
        · left
          rfl
        · right
          rfl
    have e : loweredCorner T m Finset.univ = fun _ => T - ((m + 1 : ℕ) : ℤ) + 1 := by
      funext i
      simp only [loweredCorner, Finset.mem_univ, if_true]
      push_cast
      ring
    have := hU Finset.univ
    rwa [e] at this
end Reach
section Region
open Classical
def upperRegion (N : ℕ) (A : Finset Lattice4) (κ : Fin 4 → ℕ) : Finset Lattice4 :=
  (boxBelow (21 * (N : ℤ) - 1) fun _ => -(10 * (N : ℤ))).filter fun x =>
    ∃ a ∈ A, ∀ i, min (a i + κ i) (12 * (N : ℤ)) ≤ x i
theorem mem_upperRegion {N : ℕ} {A : Finset Lattice4} {κ : Fin 4 → ℕ} {x : Lattice4} :
    x ∈ upperRegion N A κ ↔ (∀ i, -(10 * (N : ℤ)) ≤ x i ∧ x i ≤ 21 * (N : ℤ) - 1) ∧
      ∃ a ∈ A, ∀ i, min (a i + κ i) (12 * (N : ℤ)) ≤ x i := by
  rw [upperRegion, Finset.mem_filter, mem_boxBelow]
def raiseAt (κ : Fin 4 → ℕ) (i : Fin 4) : Fin 4 → ℕ := fun k => κ k + if k = i then 1 else 0
theorem upperRegion_layerStep (N : ℕ) (hN : 1 ≤ N) (A : Finset Lattice4) (κ : Fin 4 → ℕ) (i : Fin 4) :
    LayerStep (upperRegion N A (raiseAt κ i)) (upperRegion N A κ) i := by
  have hu : ∀ j k : Fin 4, 0 ≤ basisVector j k := by
    intro j k
    simp only [basisVector, Pi.single_apply]
    split_ifs <;> norm_num
  have hlow : ∀ x, x ∈ upperRegion N A κ → x ∉ upperRegion N A (raiseAt κ i) →
      x i < 12 * (N : ℤ) := by
    intro x hx hx'
    by_contra hc
    apply hx'
    obtain ⟨h1, a, ha, h2⟩ := mem_upperRegion.1 hx
    refine mem_upperRegion.2 ⟨h1, a, ha, fun k => ?_⟩
    by_cases hk : k = i
    · subst hk
      exact (min_le_right _ _).trans (not_lt.1 hc)
    · simpa [raiseAt, hk] using h2 k
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨h1, a, ha, h2⟩ := mem_upperRegion.1 hx
    refine mem_upperRegion.2 ⟨h1, a, ha, fun k => ?_⟩
    refine le_trans ?_ (h2 k)
    apply min_le_min_right
    simp only [raiseAt]
    push_cast
    split_ifs <;> simp
  · intro x hx hx'
    have hxi := hlow x hx hx'
    obtain ⟨h1, a, ha, h2⟩ := mem_upperRegion.1 hx
    refine mem_upperRegion.2 ⟨fun k => ?_, a, ha, fun k => ?_⟩
    · have := h1 k
      have h3 := hu i k
      by_cases hk : k = i
      · subst hk
        simp only [Pi.add_apply, basisVector_self]
        constructor <;> omega
      · simp only [Pi.add_apply, basisVector_of_ne hk, add_zero]
        exact this
    · have := h2 k
      by_cases hk : k = i
      · subst hk
        simp only [Pi.add_apply, basisVector_self, raiseAt, if_true]
        push_cast
        rcases le_total ((a k) + (κ k)) (12 * (N : ℤ)) with h | h
        · rw [min_eq_left h] at this
          exact (min_le_left _ _).trans (by omega)
        · rw [min_eq_right h] at this
          omega
      · simpa [raiseAt, hk, basisVector_of_ne hk] using this
  · intro y hy j hj
    obtain ⟨h1, a, ha, h2⟩ := mem_upperRegion.1 hy
    obtain ⟨h3, -⟩ := mem_upperRegion.1 hj
    refine mem_upperRegion.2 ⟨h3, a, ha, fun k => ?_⟩
    have := h2 k
    have h4 := hu j k
    simp only [Pi.add_apply]
    omega
  · intro x hx hx' j hji hj
    have hxi := hlow x hx hx'
    obtain ⟨h1, a, ha, h2⟩ := mem_upperRegion.1 hx
    obtain ⟨h3, -⟩ := mem_upperRegion.1 hj
    refine mem_upperRegion.2 ⟨fun k => ?_, a, ha, fun k => ?_⟩
    · have e1 := h3 k
      have e2 := h1 k
      by_cases hk : k = i
      · subst hk
        simp only [Pi.add_apply, basisVector_self, basisVector_of_ne (Ne.symm hji)]
        constructor <;> omega
      · simp only [Pi.add_apply, basisVector_of_ne hk, add_zero] at e1 ⊢
        exact e1
    · have e2 := h2 k
      have e3 := hu j k
      by_cases hk : k = i
      · subst hk
        simp only [Pi.add_apply, basisVector_self, basisVector_of_ne (Ne.symm hji), raiseAt, if_true]
        push_cast
        rcases le_total ((a k) + (κ k)) (12 * (N : ℤ)) with h | h
        · rw [min_eq_left h] at e2
          exact (min_le_left _ _).trans (by omega)
        · rw [min_eq_right h] at e2
          have := min_le_right (a k + ((κ k : ℤ) + 1)) (12 * (N : ℤ))
          omega
      · simp only [Pi.add_apply, basisVector_of_ne hk, add_zero, raiseAt, if_neg hk]
        omega
theorem upperRegion_isFilledToward (N : ℕ) (hN : 1 ≤ N) (A : Finset Lattice4) (hA : A.Nonempty)
    (hb : ∀ a ∈ A, ∀ i, -(10 * (N : ℤ)) ≤ a i ∧ a i ≤ 12 * (N : ℤ)) (κ : Fin 4 → ℕ) :
    IsFilledToward (9 * N) (fun _ => 12 * (N : ℤ)) (upperRegion N A κ) := by
  have hq : ∀ q ∈ cornerCube (9 * N) (fun _ => 12 * (N : ℤ)), ∀ i,
      12 * (N : ℤ) ≤ q i ∧ q i ≤ 21 * (N : ℤ) - 1 := by
    intro q hq i
    have := (Fintype.mem_piFinset.1 hq) i
    rw [Finset.mem_Ico] at this
    dsimp only at this
    push_cast at this
    constructor <;> omega
  refine ⟨?_, ?_, ?_⟩
  · intro q hq'
    obtain ⟨a, ha⟩ := hA
    refine mem_upperRegion.2 ⟨fun i => ?_, a, ha, fun i => ?_⟩
    · have := hq q hq' i
      constructor <;> omega
    · exact (min_le_right _ _).trans (hq q hq' i).1
  · intro x hx i
    obtain ⟨h1, -⟩ := mem_upperRegion.1 hx
    have := h1 i
    rw [abs_le]
    dsimp only
    push_cast
    constructor <;> omega
  · intro x hx q hq' y hy
    obtain ⟨h1, a, ha, h2⟩ := mem_upperRegion.1 hx
    refine mem_upperRegion.2 ⟨fun i => ?_, a, ha, fun i => ?_⟩
    · have e1 := h1 i
      have e2 := hq q hq' i
      have e3 := hy i
      rcases le_total (x i) (q i) with h | h
      · rw [min_eq_left h, max_eq_right h] at e3
        constructor <;> omega
      · rw [min_eq_right h, max_eq_left h] at e3
        constructor <;> omega
    · have e1 := h2 i
      have e2 := hq q hq' i
      have e3 := hy i
      have e4 := min_le_right (a i + (κ i : ℤ)) (12 * (N : ℤ))
      rcases le_total (x i) (q i) with h | h
      · rw [min_eq_left h] at e3
        omega
      · rw [min_eq_right h] at e3
        omega
theorem upperRegion_top (N : ℕ) (hN : 1 ≤ N) (A : Finset Lattice4) (hA : A.Nonempty)
    (hb : ∀ a ∈ A, ∀ i, -(10 * (N : ℤ)) ≤ a i ∧ a i ≤ 12 * (N : ℤ)) :
    upperRegion N A (fun _ => 22 * N) =
      boxBelow (21 * (N : ℤ) - 1) fun _ => 21 * (N : ℤ) - 1 - ((9 * N : ℕ) : ℤ) + 1 := by
  ext x
  rw [mem_upperRegion, mem_boxBelow]
  constructor
  · rintro ⟨h1, a, ha, h2⟩ i
    have e1 := h2 i
    have e2 := (hb a ha i).1
    have e3 : min (a i + ((22 * N : ℕ) : ℤ)) (12 * (N : ℤ)) = 12 * (N : ℤ) := by
      apply min_eq_right
      push_cast
      omega
    rw [e3] at e1
    push_cast
    have := (h1 i).2
    constructor <;> omega
  · intro h
    obtain ⟨a, ha⟩ := hA
    refine ⟨fun i => ?_, a, ha, fun i => ?_⟩
    · have := h i
      push_cast at this
      constructor <;> omega
    · have := h i
      push_cast at this
      exact (min_le_right _ _).trans (by omega)
theorem upperRegion_layerReachable (N : ℕ) (hN : 1 ≤ N) (A : Finset Lattice4) (hA : A.Nonempty)
    (hb : ∀ a ∈ A, ∀ i, -(10 * (N : ℤ)) ≤ a i ∧ a i ≤ 12 * (N : ℤ)) :
    ∀ (n : ℕ) (κ : Fin 4 → ℕ), (∀ i, κ i ≤ 22 * N) → ∑ i, (22 * N - κ i) = n →
      LayerReachable (upperRegion N A κ) := by
  intro n
  induction n with
  | zero =>
    intro κ hκ hs
    have hall : κ = fun _ => 22 * N := by
      funext i
      have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)).1 hs i (Finset.mem_univ i)
      have := hκ i
      omega
    rw [hall, upperRegion_top N hN A hA hb]
    exact layerReachable_cube _ (9 * N) (by omega)
  | succ n ih =>
    intro κ hκ hs
    obtain ⟨i, hi⟩ : ∃ i, κ i < 22 * N := by
      by_contra hc
      push Not at hc
      have : ∑ i, (22 * N - κ i) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        have := hc i
        omega
      omega
    have hraised : ∀ k, raiseAt κ i k ≤ 22 * N := by
      intro k
      simp only [raiseAt]
      split_ifs with h
      · subst h
        omega
      · simpa using hκ k
    have hsum : ∑ k, (22 * N - raiseAt κ i k) = n := by
      have e : ∀ k, 22 * N - κ k = (22 * N - raiseAt κ i k) + if k = i then 1 else 0 := by
        intro k
        simp only [raiseAt]
        split_ifs with h
        · subst h
          omega
        · simp
      have h2 : ∑ k, (22 * N - κ k) = ∑ k, (22 * N - raiseAt κ i k) + 1 := by
        rw [Finset.sum_congr rfl fun k _ => e k, Finset.sum_add_distrib]
        simp
      omega
    exact LayerReachable.grow _ _ i (ih _ hraised hsum) (upperRegion_layerStep N hN A κ i)
      ⟨9 * N, _, by omega, upperRegion_isFilledToward N hN A hA hb κ⟩
end Region
theorem quarticGaugeStatement_holds (hHom : randomStaircaseHomotopyStatement)
    (hFrac : hardyLittlewoodSobolevStatement) : quarticGaugeStatement := by
  obtain ⟨K, c₁, hK, hc₁, -, hap⟩ := a_priori_bound hHom hFrac
  have hden : 0 < 136 * K + 27 := by positivity
  refine ⟨K + 1, min 1 (c₁ / (136 * K + 27)), by positivity, by positivity, ?_⟩
  intro N A P X ε hN hA hb hP hε0 hε hE
  have hε1 : ε ≤ 1 := hε.trans (min_le_left _ _)
  have hε2 : ε ≤ c₁ / (136 * K + 27) := hε.trans (min_le_right _ _)
  have hset : P = upperRegion N A (fun _ => 0) := by
    ext x
    rw [hP, mem_upperRegion]
    constructor
    · rintro ⟨h1, a, ha, h2⟩
      refine ⟨fun i => ⟨?_, h1 i⟩, a, ha, fun i => ?_⟩
      · have := (hb a ha i).1
        have := h2 i
        omega
      · exact (min_le_left _ _).trans (by simpa using h2 i)
    · rintro ⟨h1, a, ha, h2⟩
      refine ⟨fun i => (h1 i).2, a, ha, fun i => ?_⟩
      have e := h2 i
      rw [min_eq_left (by simpa using (hb a ha i).2)] at e
      simpa using e
  have hreach : LayerReachable P := by
    rw [hset]
    exact upperRegion_layerReachable N hN A hA hb _ _ (fun _ => Nat.zero_le _) rfl
  have hsmall : (136 * K + 27) * (ε ^ 2) ^ 2 ≤ c₁ := by
    rw [le_div_iff₀ hden] at hε2
    have h4 : (ε ^ 2) ^ 2 ≤ ε := by
      have : ε ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg ε]
    nlinarith
  obtain ⟨γ, hγ⟩ := LayerReachable.exists_gauge_bound K c₁ hK hap X (ε ^ 2) (sq_nonneg ε) hsmall hreach hE
  refine ⟨γ, ?_⟩
  have hE0 : 0 ≤ plaquetteEnergy P X := Finset.sum_nonneg fun p _ => sq_nonneg _
  have hE2 : plaquetteEnergy P X ^ 2 ≤ (ε ^ 2) ^ 2 := pow_le_pow_left₀ hE0 hE 2
  change quarticSum P (latticeGaugeTransform γ X) ≤ _
  refine hγ.trans ?_
  have h3 : K ≤ (K + 1) ^ 4 := by
    have h1 : 1 ≤ K + 1 := by linarith
    have : K + 1 ≤ (K + 1) ^ 4 := le_self_pow₀ h1 (by norm_num)
    linarith
  calc K * plaquetteEnergy P X ^ 2 ≤ K * (ε ^ 2) ^ 2 := by gcongr
    _ ≤ (K + 1) ^ 4 * (ε ^ 2) ^ 2 := by gcongr
    _ = _ := by ring
end LeastQuarticGauge
end YangMills.Construction
end
