import YangMills.Construction.ClusterExpansionOfAStep.DerivativesOfTheWilsonEnergy
import YangMills.Construction.ColdStepAtMirrorFrames.BareActionIsCriticalAtAnAbelianFieldProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.WilsonDerivativeBounds
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields YangMills.Construction.WilsonDerivatives
def reContinuousLinear : ℍ[ℝ] →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun q => q.re, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => by simp }
theorem contDiff_exp_quaternion : ContDiff ℝ ⊤ (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) := by apply _root_.YangMills.SharedProofs.p23558 <;> assumption
abbrev EdgePair : Type := (Fin 4 → ℍ[ℝ]) × (Fin 4 → ℍ[ℝ])
def plaquetteForm (z : EdgePair) : ℝ :=
  1 - reContinuousLinear (NormedSpace.exp (z.2 0) * z.1 0 * (NormedSpace.exp (z.2 1) * z.1 1) *
    star (NormedSpace.exp (z.2 2) * z.1 2) * star (NormedSpace.exp (z.2 3) * z.1 3))
def starContinuousLinear : ℍ[ℝ] →L[ℝ] ℍ[ℝ] :=
  LinearMap.toContinuousLinearMap
    { toFun := star, map_add' := star_add, map_smul' := fun c q => by ext <;> simp }
theorem contDiff_conj : ContDiff ℝ ⊤ (star : ℍ[ℝ] → ℍ[ℝ]) := starContinuousLinear.contDiff
theorem contDiff_plaquetteForm : ContDiff ℝ ⊤ plaquetteForm := by
  unfold plaquetteForm
  have hC (i : Fin 4) : ContDiff ℝ ⊤ fun z : EdgePair => z.1 i := by fun_prop
  have hV (i : Fin 4) : ContDiff ℝ ⊤ fun z : EdgePair => NormedSpace.exp (z.2 i) :=
    contDiff_exp_quaternion.comp (by fun_prop)
  have e (i : Fin 4) : ContDiff ℝ ⊤ fun z : EdgePair => NormedSpace.exp (z.2 i) * z.1 i :=
    (hV i).mul (hC i)
  exact contDiff_const.sub (reContinuousLinear.contDiff.comp
    ((((e 0).mul (e 1)).mul (contDiff_conj.comp (e 2))).mul (contDiff_conj.comp (e 3))))
variable {n k : ℕ}
def bondDisplacement (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (b : TorusBond n) :
    (Fin k → ℝ) →L[ℝ] ℍ[ℝ] :=
  ∑ l, if c l = b then (ContinuousLinearMap.proj l : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (X l : ℍ[ℝ]) else 0
theorem coe_sum_perturbation (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (b : TorusBond n)
    (σ : Fin k → ℝ) :
    (((∑ l, if c l = b then σ l • X l else 0 : imaginaryQuaternions)) : ℍ[ℝ]) = bondDisplacement c X b σ := by
  rw [bondDisplacement, _root_.sum_apply, AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp
theorem bondDisplacement_single (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (b : TorusBond n)
    (l₀ : Fin k) :
    bondDisplacement c X b (Pi.single l₀ 1) = if c l₀ = b then (X l₀ : ℍ[ℝ]) else 0 := by
  rw [bondDisplacement, _root_.sum_apply, Finset.sum_eq_single l₀]
  · split_ifs <;> simp
  · intro l _ hl
    split_ifs <;> simp [hl]
  · simp
def cornerBonds (x : TorusSite n) (μ ν : Fin 4) : Fin 4 → TorusBond n :=
  ![(x, μ), (x + TorusFields.unitStep n μ, ν), (x + TorusFields.unitStep n ν, μ), (x, ν)]
def cornerDisplacement (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (x : TorusSite n)
    (μ ν : Fin 4) : (Fin k → ℝ) →L[ℝ] (Fin 4 → ℍ[ℝ]) :=
  ContinuousLinearMap.pi fun i => bondDisplacement c X (cornerBonds x μ ν i)
def cornerValues (W : TorusField n) (x : TorusSite n) (μ ν : Fin 4) : Fin 4 → ℍ[ℝ] :=
  fun i => ((W (cornerBonds x μ ν i).1 (cornerBonds x μ ν i).2 : UnitQuaternion) : ℍ[ℝ])
theorem coe_perturb (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (σ : Fin k → ℝ)
    (W : TorusField n) (b : TorusBond n) :
    ((perturb c X σ W b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) =
      NormedSpace.exp (bondDisplacement c X b σ) * ((W b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) := by
  have : (perturb c X σ W b.1 b.2 : UnitQuaternion) =
      expUnit (∑ l, if c l = (b.1, b.2) then σ l • X l else 0) * W b.1 b.2 :=
    rfl
  rw [this, Submonoid.coe_mul]
  congr 1
  show NormedSpace.exp _ = _
  rw [coe_sum_perturbation]
theorem coe_inv_unit (g : UnitQuaternion) : ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = star (g : ℍ[ℝ]) := by
  rw [← Unitary.star_eq_inv, Unitary.coe_star]
theorem plaquetteEnergy_perturb (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (σ : Fin k → ℝ)
    (W : TorusField n) (x : TorusSite n) (μ ν : Fin 4) :
    plaquetteEnergy (perturb c X σ W) x μ ν =
      plaquetteForm (cornerValues W x μ ν, cornerDisplacement c X x μ ν σ) := by
  unfold plaquetteEnergy plaquetteForm holonomy
  have h1 := coe_perturb c X σ W (x, μ)
  have h2 := coe_perturb c X σ W (x + TorusFields.unitStep n μ, ν)
  have h3 := coe_perturb c X σ W (x + TorusFields.unitStep n ν, μ)
  have h4 := coe_perturb c X σ W (x, ν)
  simp only [Submonoid.coe_mul, coe_inv_unit] at *
  rw [h1, h2, h3, h4]
  rfl
theorem exists_bound_iteratedFDeriv_plaquetteForm : ∃ M : ℝ, 0 ≤ M ∧ ∀ (m : ℕ), m ≤ 3 →
    ∀ C : Fin 4 → ℍ[ℝ], (∀ i, C i ∈ unitary ℍ[ℝ]) → ‖iteratedFDeriv ℝ m plaquetteForm (C, 0)‖ ≤ M := by
  have hK : IsCompact (Set.pi Set.univ fun _ : Fin 4 => (unitary ℍ[ℝ] : Set ℍ[ℝ])) :=
    isCompact_univ_pi fun _ => isCompact_unitary_quaternion
  have hb (m : ℕ) : ∃ M : ℝ, ∀ C ∈ Set.pi Set.univ fun _ : Fin 4 => (unitary ℍ[ℝ] : Set ℍ[ℝ]),
      ‖iteratedFDeriv ℝ m plaquetteForm (C, (0 : Fin 4 → ℍ[ℝ]))‖ ≤ M := by
    have hc : Continuous fun C : Fin 4 → ℍ[ℝ] =>
        iteratedFDeriv ℝ m plaquetteForm (C, (0 : Fin 4 → ℍ[ℝ])) :=
      (contDiff_plaquetteForm.continuous_iteratedFDeriv (m := m) (by exact_mod_cast le_top)).comp
        (by fun_prop)
    exact hK.exists_bound_of_continuousOn hc.continuousOn
  choose M hM using hb
  refine ⟨|M 0| + |M 1| + |M 2| + |M 3|, by positivity, fun m hm C hC => ?_⟩
  have hCm : C ∈ Set.pi Set.univ fun _ : Fin 4 => (unitary ℍ[ℝ] : Set ℍ[ℝ]) := fun i _ => hC i
  have h0 := le_abs_self (M m)
  have := hM m C hCm
  interval_cases m <;> linarith [abs_nonneg (M 0), abs_nonneg (M 1), abs_nonneg (M 2), abs_nonneg (M 3)]
theorem contDiff_plaquetteEnergy_perturb (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (W : TorusField n) (x : TorusSite n) (μ ν : Fin 4) :
    ContDiff ℝ ⊤ fun σ : Fin k → ℝ => plaquetteEnergy (perturb c X σ W) x μ ν := by
  simp only [plaquetteEnergy_perturb]
  exact contDiff_plaquetteForm.comp (contDiff_const.prodMk (cornerDisplacement c X x μ ν).contDiff)
theorem iteratedFDeriv_plaquetteEnergy_perturb (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (W : TorusField n) (x : TorusSite n) (μ ν : Fin 4) (m : Fin k → Fin k → ℝ) :
    iteratedFDeriv ℝ k (fun σ : Fin k → ℝ => plaquetteEnergy (perturb c X σ W) x μ ν) 0 m =
      iteratedFDeriv ℝ k plaquetteForm (cornerValues W x μ ν, 0) fun l =>
        (0, cornerDisplacement c X x μ ν (m l)) := by
  let B : (Fin k → ℝ) →L[ℝ] EdgePair :=
    (ContinuousLinearMap.inr ℝ (Fin 4 → ℍ[ℝ]) (Fin 4 → ℍ[ℝ])).comp (cornerDisplacement c X x μ ν)
  have hf : (fun σ : Fin k → ℝ => plaquetteEnergy (perturb c X σ W) x μ ν) =
      (fun z : EdgePair => plaquetteForm (z + (cornerValues W x μ ν, 0))) ∘ B := by
    funext σ
    simp [plaquetteEnergy_perturb, B]
  have hs : ContDiff ℝ ⊤ fun z : EdgePair => plaquetteForm (z + (cornerValues W x μ ν, 0)) :=
    contDiff_plaquetteForm.comp (contDiff_id.add contDiff_const)
  rw [hf, B.iteratedFDeriv_comp_right hs 0 (by exact_mod_cast le_top)]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_comp_add_right]
  simp [B]
open Classical in
theorem card_plaquettes_through_bond_le [NeZero n] (b : TorusBond n) :
    ((plaquettesIn (Finset.univ : Finset (TorusSite n))).filter fun p =>
      ∃ i, cornerBonds p.1 p.2.1 p.2.2 i = b).card ≤ 48 := by
  let T : Fin 3 × Fin 4 × Fin 4 → TorusPlaquette n := fun e =>
    (if e.1 = 0 then b.1 else if e.1 = 1 then b.1 - TorusFields.unitStep n e.2.1
      else b.1 - TorusFields.unitStep n e.2.2,
      e.2.1, e.2.2)
  have hsub : ((plaquettesIn (Finset.univ : Finset (TorusSite n))).filter fun p =>
      ∃ i, cornerBonds p.1 p.2.1 p.2.2 i = b) ⊆ Finset.univ.image T := by
    intro p hp
    obtain ⟨x, μ, ν⟩ := p
    obtain ⟨i, hi⟩ := (Finset.mem_filter.mp hp).2
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    fin_cases i
    · refine ⟨(0, μ, ν), ?_⟩
      have : (x, μ) = b := hi
      simp [T, ← this]
    · refine ⟨(1, μ, ν), ?_⟩
      have : (x + TorusFields.unitStep n μ, ν) = b := hi
      simp [T, ← this]
    · refine ⟨(2, μ, ν), ?_⟩
      have : (x + TorusFields.unitStep n ν, μ) = b := hi
      simp [T, ← this]
    · refine ⟨(0, μ, ν), ?_⟩
      have : (x, ν) = b := hi
      simp [T, ← this]
  calc _ ≤ (Finset.univ.image T).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin 3 × Fin 4 × Fin 4)).card := Finset.card_image_le
    _ = 48 := by simp
theorem wilsonAction_perturb_eq_sum [NeZero n] (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (W : TorusField n) :
    (fun σ : Fin k → ℝ => wilsonAction Finset.univ (perturb c X σ W)) =
      ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)),
        fun σ : Fin k → ℝ => plaquetteEnergy (perturb c X σ W) p.1 p.2.1 p.2.2 := by
  funext σ
  simp [TorusFields.wilsonAction, Finset.sum_apply]
theorem norm_cornerDisplacement_single_le (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (hX : AreUnitVectors X) (x : TorusSite n) (μ ν : Fin 4) (l : Fin k) :
    ‖((0, cornerDisplacement c X x μ ν (Pi.single l 1)) : EdgePair)‖ ≤ 1 := by
  rw [Prod.norm_def]
  refine max_le (by simp) ?_
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
  show ‖bondDisplacement c X (cornerBonds x μ ν i) (Pi.single l 1)‖ ≤ 1
  rw [bondDisplacement_single]
  split_ifs
  · exact (hX l).le
  · simp
theorem boundedDerivativesOfWilsonAction_holds : BoundedDerivativesOfWilsonAction := by
  classical
  obtain ⟨M, hM0, hM⟩ := exists_bound_iteratedFDeriv_plaquetteForm
  refine ⟨48 * M + 1, by positivity, fun n _ W => ⟨?_, ?_⟩⟩
  · intro k c X
    simp only [TorusFields.wilsonAction]
    exact (ContDiff.sum fun (p : TorusPlaquette n) _ =>
      (contDiff_plaquetteEnergy_perturb c X W p.1 p.2.1 p.2.2).of_le le_top).contDiffAt
  · intro k c X hk1 hk3 hX
    have hunit : ∀ (x : TorusSite n) (μ ν : Fin 4) (i : Fin 4), cornerValues W x μ ν i ∈ unitary ℍ[ℝ] :=
      fun x μ ν i => (W (cornerBonds x μ ν i).1 (cornerBonds x μ ν i).2).2
    let l₀ : Fin k := ⟨0, hk1⟩
    unfold mixedDeriv
    rw [wilsonAction_perturb_eq_sum, iteratedFDeriv_sum_apply
      (fun (p : TorusPlaquette n) _ =>
        ((contDiff_plaquetteEnergy_perturb c X W p.1 p.2.1 p.2.2).of_le le_top).contDiffAt),
      _root_.sum_apply]
    have hterm : ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)),
        ‖iteratedFDeriv ℝ k (fun σ : Fin k → ℝ => plaquetteEnergy (perturb c X σ W) p.1 p.2.1 p.2.2) 0
          (fun l => Pi.single l 1)‖ ≤ if ∃ i, cornerBonds p.1 p.2.1 p.2.2 i = c l₀ then M else 0 := by
      intro p _
      rw [iteratedFDeriv_plaquetteEnergy_perturb]
      split_ifs with hp
      · refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
        have h1 := hM k hk3 (cornerValues W p.1 p.2.1 p.2.2) (hunit _ _ _)
        have h2 : ∏ l : Fin k, ‖((0, cornerDisplacement c X p.1 p.2.1 p.2.2 (Pi.single l 1)) : EdgePair)‖ ≤ 1 :=
          Finset.prod_le_one (fun _ _ => norm_nonneg _) fun l _ =>
            norm_cornerDisplacement_single_le c X hX _ _ _ l
        calc _ ≤ M * 1 := mul_le_mul h1 h2 (Finset.prod_nonneg fun _ _ => norm_nonneg _) hM0
          _ = M := mul_one M
      · have hz : ((0, cornerDisplacement c X p.1 p.2.1 p.2.2 (Pi.single l₀ 1)) : EdgePair) = 0 := by
          ext1
          · rfl
          · funext i
            show bondDisplacement c X (cornerBonds p.1 p.2.1 p.2.2 i) (Pi.single l₀ 1) = 0
            rw [bondDisplacement_single, if_neg fun h => hp ⟨i, h.symm⟩]
        rw [ContinuousMultilinearMap.map_coord_zero _ l₀ hz]
        simp
    have hsum := norm_sum_le_of_le _ hterm
    rw [Real.norm_eq_abs] at hsum
    refine hsum.trans ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hc := card_plaquettes_through_bond_le (c l₀)
    have : (((plaquettesIn (Finset.univ : Finset (TorusSite n))).filter fun p =>
        ∃ i, cornerBonds p.1 p.2.1 p.2.2 i = c l₀).card : ℝ) ≤ 48 := by exact_mod_cast hc
    nlinarith
end YangMills.Construction.WilsonDerivativeBounds
end
