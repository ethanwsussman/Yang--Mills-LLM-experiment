import YangMills.Construction.ClusterExpansionOfAStep.NumberOfFourDensitiesProof
import YangMills.Construction.ColdChainAtEveryLevel.LeastQuarticGaugeProof
import YangMills.Construction.LawInAState.DecayOverATorusProof
import YangMills.Construction.OneLoopLaw.FourierSeriesOfASymbolProof
import YangMills.Construction.ResponseInTheExpansion.ResponseIntegralIsCarriedProof
import YangMills.Construction.RunningCouplingSlope.CompositionKeepsTheCoefficientProof
import YangMills.Construction.WindowOfTheParameters.CoefficientAsAMixedMoment
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SlopeCoefficient
open scoped Topology Quaternion
open BlockAverages hiding unitStep gaugeTransform
open TorusFields TorusLumps
variable {n : ℕ}
private theorem fderiv_fderiv_comp_clm {k m : ℕ} {φ : (Fin k → ℝ) → ℝ} (hφ : ContDiffAt ℝ 2 φ 0)
    (L : (Fin m → ℝ) →L[ℝ] (Fin k → ℝ)) (v w : Fin m → ℝ) :
    fderiv ℝ (fderiv ℝ (φ ∘ L)) 0 v w = fderiv ℝ (fderiv ℝ φ) 0 (L v) (L w) := by
  have hd : ∀ᶠ y in 𝓝 (0 : Fin k → ℝ), DifferentiableAt ℝ φ y := by
    have h1 : ∀ᶠ y in 𝓝 (0 : Fin k → ℝ), ContDiffAt ℝ 2 φ y := hφ.eventually (by simp)
    exact h1.mono fun y hy => hy.differentiableAt (by norm_num)
  have hL : Filter.Tendsto L (𝓝 0) (𝓝 0) := by
    simpa using L.continuous.tendsto 0
  have heq : fderiv ℝ (φ ∘ L) =ᶠ[𝓝 0] fun z => (fderiv ℝ φ (L z)).comp L := by
    filter_upwards [hL.eventually hd] with z hz
    rw [fderiv_comp z hz L.differentiableAt, L.fderiv]
  have hD : DifferentiableAt ℝ (fderiv ℝ φ) 0 :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h1 : HasFDerivAt (fun z => fderiv ℝ φ (L z)) ((fderiv ℝ (fderiv ℝ φ) 0).comp L) 0 := by
    have h0 : HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) 0) (L 0) := by
      simpa using hD.hasFDerivAt
    exact h0.comp 0 L.hasFDerivAt
  have h2 := h1.clm_comp (hasFDerivAt_const L (0 : Fin m → ℝ))
  rw [heq.fderiv_eq, h2.fderiv]
  simp
private theorem mixedDeriv_eq_fderiv_fderiv (G : TorusField n → ℝ) (W : TorusField n) (c : Fin 2 → TorusBond n)
    (X : Fin 2 → imaginaryQuaternions) :
    mixedDeriv G W c X =
      fderiv ℝ (fderiv ℝ fun σ => G (perturb c X σ W)) 0 (Pi.single 0 1) (Pi.single 1 1) := by
  unfold mixedDeriv
  rw [iteratedFDeriv_two_apply]
private def coordPlane {k : ℕ} (i j : Fin k) : (Fin 2 → ℝ) →L[ℝ] (Fin k → ℝ) :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).smulRight (Pi.single i 1) +
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).smulRight (Pi.single j 1)
private theorem coordPlane_apply {k : ℕ} (i j : Fin k) (σ : Fin 2 → ℝ) (l : Fin k) :
    coordPlane i j σ l = σ 0 * (if l = i then 1 else 0) + σ 1 * (if l = j then 1 else 0) := by
  simp [coordPlane, Pi.single_apply]
private theorem perturb_coordPlane {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (i j : Fin k) (σ : Fin 2 → ℝ) (W : TorusField n) :
    perturb c X (coordPlane i j σ) W = perturb ![c i, c j] ![X i, X j] σ W := by
  funext x b
  unfold perturb
  congr 2
  have h : ∀ l, (if c l = (x, b) then coordPlane i j σ l • X l else 0) =
      (if l = i then (if c i = (x, b) then σ 0 • X i else 0) else 0) +
        (if l = j then (if c j = (x, b) then σ 1 • X j else 0) else 0) := by
    intro l
    rw [coordPlane_apply]
    by_cases h1 : l = i <;> by_cases h2 : l = j
    · subst h1; subst h2
      by_cases h3 : c l = (x, b) <;> simp [h3, add_smul]
    · subst h1
      by_cases h3 : c l = (x, b) <;> simp [h3, h2]
    · subst h2
      by_cases h3 : c l = (x, b) <;> simp [h3, h1]
    · simp [h1, h2]
  rw [Finset.sum_congr rfl fun l _ => h l, Finset.sum_add_distrib, Fin.sum_univ_two]
  simp
  congr
private theorem coordPlane_single_zero {k : ℕ} (i j : Fin k) :
    coordPlane i j (Pi.single 0 1) = Pi.single i 1 := by
  funext l
  rw [coordPlane_apply]
  simp [Pi.single_apply]
private theorem coordPlane_single_one {k : ℕ} (i j : Fin k) :
    coordPlane i j (Pi.single 1 1) = Pi.single j 1 := by
  funext l
  rw [coordPlane_apply]
  simp [Pi.single_apply]
private theorem mixedDeriv_pair_eq {k : ℕ} (G : TorusField n → ℝ) (W : TorusField n) (c : Fin k → TorusBond n)
    (X : Fin k → imaginaryQuaternions)
    (hφ : ContDiffAt ℝ 2 (fun σ : Fin k → ℝ => G (perturb c X σ W)) 0) (i j : Fin k) :
    mixedDeriv G W ![c i, c j] ![X i, X j] =
      fderiv ℝ (fderiv ℝ fun σ : Fin k → ℝ => G (perturb c X σ W)) 0 (Pi.single i 1) (Pi.single j 1) := by
  rw [mixedDeriv_eq_fderiv_fderiv]
  have h : (fun σ : Fin 2 → ℝ => G (perturb ![c i, c j] ![X i, X j] σ W)) =
      (fun σ : Fin k → ℝ => G (perturb c X σ W)) ∘ coordPlane i j := by
    funext σ
    simp only [Function.comp, perturb_coordPlane]
  rw [h, fderiv_fderiv_comp_clm hφ, coordPlane_single_zero, coordPlane_single_one]
private theorem perturb_trivialField_apply {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (σ : Fin k → ℝ) (x : TorusSite n) (i : Fin 4) :
    perturb c X σ (trivialField n) x i = expUnit (∑ l, if c l = (x, i) then σ l • X l else 0) := by
  simp [perturb, trivialField]
private theorem continuous_expUnit : Continuous expUnit := by apply _root_.YangMills.Construction.TorusFields.continuous_expUnit <;> assumption
private theorem expUnit_zero : expUnit (0 : imaginaryQuaternions) = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
private theorem expUnit_smul_mul (X : imaginaryQuaternions) (a b : ℝ) :
    expUnit (a • X) * expUnit (b • X) = expUnit ((a + b) • X) := by apply _root_.YangMills.Construction.TorusFrame.expUnit_smul_mul <;> assumption
private theorem expUnit_smul_inv (X : imaginaryQuaternions) (a : ℝ) :
    (expUnit (a • X))⁻¹ = expUnit ((-a) • X) := by apply _root_.YangMills.SharedProofs.p4359 <;> assumption
private theorem expUnit_inv (w : imaginaryQuaternions) : (expUnit w)⁻¹ = expUnit (-w) := by apply _root_.YangMills.Construction.LeastQuarticGauge.expUnit_inv <;> assumption
private theorem tendsto_perturb_trivial {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) :
    Filter.Tendsto (fun σ : Fin k → ℝ => perturb c X σ (trivialField n)) (𝓝 0) (𝓝 (trivialField n)) := by apply _root_.YangMills.Construction.RunningCouplingSlope.StepGaugeTotals.tendsto_perturb_trivialField <;> assumption
private def wardBondList (c : TorusBond n) (y : TorusSite n) : Fin 9 → TorusBond n :=
  ![c, (y, 0), (y, 1), (y, 2), (y, 3), (y - unitStep n 0, 0), (y - unitStep n 1, 1), (y - unitStep n 2, 2),
    (y - unitStep n 3, 3)]
private def siteGradient : Fin 9 → ℝ := ![0, 1, 1, 1, 1, -1, -1, -1, -1]
private theorem ite_add_ite_eq_sub (P A B : Prop) [Decidable P] [Decidable A] [Decidable B] :
    (if P then (0 : ℝ) else 0) + ((if A then 1 else 0) + if B then -1 else 0) =
      (if A then 1 else 0) - if B then 1 else 0 := by
  by_cases hP : P <;> by_cases hA : A <;> by_cases hB : B <;> simp [hP, hA, hB]
private theorem sum_siteGradient (c : TorusBond n) (y x : TorusSite n) (i : Fin 4) :
    (∑ l, if wardBondList c y l = (x, i) then siteGradient l else 0) =
      (if x = y then 1 else 0) - (if x + unitStep n i = y then 1 else 0) := by
  have h1 : (y = x) = (x = y) := propext eq_comm
  have h2 : ∀ j, (y - unitStep n j = x) = (x + unitStep n j = y) := fun j =>
    propext ⟨fun h => by rw [← h]; abel, fun h => by rw [← h]; abel⟩
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  fin_cases i <;> simp [wardBondList, siteGradient, Prod.mk.injEq, h1, h2, Fin.ext_iff] <;>
    exact ite_add_ite_eq_sub _ _ _
private def gaugeAtSite (X : imaginaryQuaternions) (y : TorusSite n) (s : ℝ) : TorusSite n → UnitQuaternion :=
  fun z => expUnit ((if z = y then s else 0) • X)
private def wardPlane : (Fin 2 → ℝ) →L[ℝ] (Fin 9 → ℝ) :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).smulRight (Pi.single 0 1) +
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).smulRight siteGradient
private def bondLine : (Fin 2 → ℝ) →L[ℝ] (Fin 9 → ℝ) :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).smulRight (Pi.single 0 1)
private theorem sum_ite_smul_eq {k : ℕ} (c : Fin k → TorusBond n) (X : imaginaryQuaternions) (v : Fin k → ℝ)
    (b : TorusBond n) :
    (∑ l, if c l = b then v l • X else 0) = (∑ l, if c l = b then v l else 0) • X := by
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp
private theorem gaugeTransform_eq_perturb (X : imaginaryQuaternions) (c : TorusBond n) (y : TorusSite n)
    (σ : Fin 2 → ℝ) :
    gaugeTransform (gaugeAtSite X y (σ 1))
        (perturb (wardBondList c y) (fun _ => X) (bondLine σ) (trivialField n)) =
      perturb (wardBondList c y) (fun _ => X) (wardPlane σ) (trivialField n) := by
  funext x i
  simp only [gaugeTransform, perturb_trivialField_apply, gaugeAtSite, sum_ite_smul_eq]
  rw [expUnit_smul_inv, expUnit_smul_mul, expUnit_smul_mul]
  congr 2
  have h : ∀ l, wardPlane σ l = bondLine σ l + σ 1 * siteGradient l := by
    intro l
    simp [wardPlane, bondLine]
  have h' : (∑ l, if wardBondList c y l = (x, i) then wardPlane σ l else 0) =
      (∑ l, if wardBondList c y l = (x, i) then bondLine σ l else 0) +
        σ 1 * ∑ l, if wardBondList c y l = (x, i) then siteGradient l else 0 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [h]
    split_ifs <;> simp
  rw [h', sum_siteGradient]
  split_ifs <;> ring
private theorem tendsto_gaugeAtSite (X : imaginaryQuaternions) (y : TorusSite n) :
    Filter.Tendsto (fun σ : Fin 2 → ℝ => gaugeAtSite X y (σ 1)) (𝓝 0) (𝓝 1) := by
  have hc : Continuous fun σ : Fin 2 → ℝ => gaugeAtSite X y (σ 1) := by
    refine continuous_pi fun z => ?_
    simp only [gaugeAtSite]
    refine continuous_expUnit.comp ?_
    by_cases h : z = y
    · simp only [h, if_true]
      exact (continuous_apply 1).smul continuous_const
    · simp only [h, if_false]
      exact continuous_const
  have h0 : gaugeAtSite X y ((0 : Fin 2 → ℝ) 1) = (1 : TorusSite n → UnitQuaternion) := by
    funext z
    simp [gaugeAtSite, expUnit_zero]
  have h := hc.tendsto 0
  rw [h0] at h
  exact h
private theorem ward_identity_torus {H : GaugeTotal} (hT : IsGaugeTotalAt H n) (X : imaginaryQuaternions)
    (c : TorusBond n) (y : TorusSite n) :
    ∑ j : Fin 4, (hessianAtTrivial H n c (y, j) X X - hessianAtTrivial H n c (y - unitStep n j, j) X X) = 0 := by
  set φ : (Fin 9 → ℝ) → ℝ := fun σ => H n (perturb (wardBondList c y) (fun _ => X) σ (trivialField n))
    with hφdef
  have hφ : ContDiffAt ℝ 2 φ 0 := hT.contDiffAt_perturb 9 (wardBondList c y) fun _ => X
  have hev : φ ∘ wardPlane =ᶠ[𝓝 0] φ ∘ bondLine := by
    have ht : Filter.Tendsto (fun σ : Fin 2 → ℝ =>
        ((gaugeAtSite X y (σ 1), perturb (wardBondList c y) (fun _ => X) (bondLine σ) (trivialField n)) :
          (TorusSite n → UnitQuaternion) × TorusField n)) (𝓝 0) (𝓝 (1, trivialField n)) := by
      refine (tendsto_gaugeAtSite X y).prodMk_nhds ?_
      have hb : Filter.Tendsto bondLine (𝓝 0) (𝓝 0) := by
        simpa using bondLine.continuous.tendsto 0
      exact (tendsto_perturb_trivial (wardBondList c y) fun _ => X).comp hb
    filter_upwards [ht.eventually hT.gauge_invariant_near] with σ hσ
    simp only [Function.comp, hφdef]
    rw [← gaugeTransform_eq_perturb]
    exact hσ
  have h0 : fderiv ℝ (fderiv ℝ φ) 0 (Pi.single 0 1) siteGradient = 0 := by
    have e1 : fderiv ℝ (fderiv ℝ (φ ∘ wardPlane)) 0 = fderiv ℝ (fderiv ℝ (φ ∘ bondLine)) 0 :=
      (hev.fderiv).fderiv_eq
    have e2 := fderiv_fderiv_comp_clm hφ wardPlane (Pi.single 0 1) (Pi.single 1 1)
    have e3 := fderiv_fderiv_comp_clm hφ bondLine (Pi.single 0 1) (Pi.single 1 1)
    rw [e1, e3] at e2
    have w0 : wardPlane (Pi.single 0 1) = Pi.single 0 1 := by
      simp [wardPlane]
    have w1 : wardPlane (Pi.single 1 1) = siteGradient := by
      simp [wardPlane]
    have b0 : bondLine (Pi.single 0 1) = Pi.single 0 1 := by
      simp [bondLine]
    have b1 : bondLine (Pi.single 1 1) = 0 := by
      simp [bondLine]
    rw [w0, w1, b0, b1] at e2
    simpa using e2.symm
  have hdir : siteGradient = ∑ l, siteGradient l • (Pi.single l (1 : ℝ) : Fin 9 → ℝ) := by
    funext l
    simp [Finset.sum_apply, Pi.single_apply]
  have hsec : ∀ l, fderiv ℝ (fderiv ℝ φ) 0 (Pi.single 0 1) (Pi.single l 1) =
      hessianAtTrivial H n c (wardBondList c y l) X X := by
    intro l
    exact (mixedDeriv_pair_eq (H n) (trivialField n) (wardBondList c y) (fun _ => X) hφ 0 l).symm
  rw [hdir, map_sum] at h0
  simp only [map_smul, hsec, Fin.sum_univ_succ, Fin.sum_univ_zero] at h0
  simp only [Fin.sum_univ_four]
  simp [wardBondList, siteGradient] at h0
  linarith
private def bondImage (g : TorusIsometry) (b : TorusBond n) : TorusBond n :=
  if g.axisSign (g.axisPerm.symm b.2) = 1 then (g.mapSite b.1, g.axisPerm.symm b.2)
  else (g.mapSite b.1 - unitStep n (g.axisPerm.symm b.2), g.axisPerm.symm b.2)
private def axisSignAt (g : TorusIsometry) (k : Fin 4) : ℝ := (g.axisSign (g.axisPerm.symm k) : ℝ)
private theorem mapSite_injective (g : TorusIsometry) : Function.Injective (g.mapSite (n := n)) := by apply _root_.YangMills.SharedProofs.p54677 <;> assumption
private theorem bondImage_injective (g : TorusIsometry) : Function.Injective (bondImage (n := n) g) := by
  have hsnd : ∀ b : TorusBond n, (bondImage g b).2 = g.axisPerm.symm b.2 := by
    intro b
    unfold bondImage
    split_ifs <;> rfl
  rintro ⟨x, k⟩ ⟨x', k'⟩ h
  have hk : k = k' := g.axisPerm.symm.injective (by
    have := congrArg Prod.snd h
    rwa [hsnd, hsnd] at this)
  subst hk
  have hx : x = x' := by
    apply mapSite_injective g
    by_cases hs : g.axisSign (g.axisPerm.symm k) = 1
    · simpa [bondImage, hs] using h
    · simpa [bondImage, hs] using h
  rw [hx]
private theorem transports_perturb {k : ℕ} (g : TorusIsometry) (c : Fin k → TorusBond n)
    (X : Fin k → imaginaryQuaternions) (σ : Fin k → ℝ) :
    g.Transports (perturb c X σ (trivialField n))
      (perturb (fun l => bondImage g (c l)) (fun l => axisSignAt g (c l).2 • X l) σ (trivialField n)) := by
  intro x b
  by_cases hs : g.axisSign (g.axisPerm.symm b) = 1
  · rw [if_pos hs, perturb_trivialField_apply, perturb_trivialField_apply]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    have e : (g.mapSite x, g.axisPerm.symm b) = bondImage g (x, b) := by simp [bondImage, hs]
    rw [e]
    by_cases h : c l = (x, b)
    · simp [h, axisSignAt, hs]
    · have h' : bondImage g (c l) ≠ bondImage g (x, b) := fun h' => h (bondImage_injective g h')
      simp [h, h']
  · have hs' : g.axisSign (g.axisPerm.symm b) = -1 := (g.axisSign_unit _).resolve_left hs
    rw [if_neg hs, perturb_trivialField_apply, perturb_trivialField_apply, expUnit_inv]
    congr 1
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    have e : (g.mapSite x - unitStep n (g.axisPerm.symm b), g.axisPerm.symm b) = bondImage g (x, b) := by
      simp [bondImage, hs]
    rw [e]
    by_cases h : c l = (x, b)
    · simp [h, axisSignAt, hs']
      apply Subtype.ext
      simp
    · have h' : bondImage g (c l) ≠ bondImage g (x, b) := fun h' => h (bondImage_injective g h')
      simp [h, h']
private theorem hessian_bondImage {H : GaugeTotal} (hT : IsGaugeTotalAt H n) (g : TorusIsometry)
    (c c' : TorusBond n) (X X' : imaginaryQuaternions) :
    hessianAtTrivial H n (bondImage g c) (bondImage g c') (axisSignAt g c.2 • X) (axisSignAt g c'.2 • X') =
      hessianAtTrivial H n c c' X X' := by
  unfold hessianAtTrivial
  rw [mixedDeriv_eq_fderiv_fderiv, mixedDeriv_eq_fderiv_fderiv]
  have hev : (fun σ : Fin 2 → ℝ => H n (perturb ![bondImage g c, bondImage g c']
      ![axisSignAt g c.2 • X, axisSignAt g c'.2 • X'] σ (trivialField n))) =ᶠ[𝓝 0]
      fun σ => H n (perturb ![c, c'] ![X, X'] σ (trivialField n)) := by
    filter_upwards [(tendsto_perturb_trivial ![c, c'] ![X, X']).eventually (hT.isometry_invariant g)]
      with σ hσ
    apply hσ
    have h := transports_perturb g ![c, c'] ![X, X'] σ
    have e1 : (fun l => bondImage g (![c, c'] l)) = ![bondImage g c, bondImage g c'] := by
      funext l
      fin_cases l <;> rfl
    have e2 : (fun l => axisSignAt g (![c, c'] l).2 • ![X, X'] l) =
        ![axisSignAt g c.2 • X, axisSignAt g c'.2 • X'] := by
      funext l
      fin_cases l <;> rfl
    rwa [e1, e2] at h
  rw [hev.fderiv.fderiv_eq]
private def latticeSiteImage (g : TorusIsometry) (z : Fin 4 → ℤ) : Fin 4 → ℤ :=
  fun i => g.axisSign i * z (g.axisPerm i) + g.offset i
private def latticeBondImage (g : TorusIsometry) (c : LatticeBond) : LatticeBond :=
  if g.axisSign (g.axisPerm.symm c.2) = 1 then (latticeSiteImage g c.1, g.axisPerm.symm c.2)
  else (latticeSiteImage g c.1 - Pi.single (g.axisPerm.symm c.2) 1, g.axisPerm.symm c.2)
private theorem siteOfInt_sub (a b : Fin 4 → ℤ) :
    (siteOfInt (a - b) : TorusSite n) = siteOfInt a - siteOfInt b := by apply _root_.YangMills.Construction.SlopeCoefficient.Pullback.siteOfInt_sub <;> assumption
private theorem siteOfInt_single (j : Fin 4) : (siteOfInt (Pi.single j 1) : TorusSite n) = unitStep n j := by apply _root_.YangMills.Construction.FrameTorusAction.siteOfInt_single <;> assumption
private theorem mapSite_siteOfInt (g : TorusIsometry) (z : Fin 4 → ℤ) :
    g.mapSite (siteOfInt z : TorusSite n) = siteOfInt (latticeSiteImage g z) := by
  funext i
  simp [TorusIsometry.mapSite, siteOfInt, latticeSiteImage]
private theorem bondFrom_zero (c : LatticeBond) : bondFrom (0 : TorusSite n) c = (siteOfInt c.1, c.2) := by
  simp [bondFrom]
private theorem bondImage_bondFrom (g : TorusIsometry) (c : LatticeBond) :
    bondImage g (bondFrom (0 : TorusSite n) c) = bondFrom 0 (latticeBondImage g c) := by
  rw [bondFrom_zero, bondFrom_zero]
  unfold bondImage latticeBondImage
  by_cases hs : g.axisSign (g.axisPerm.symm c.2) = 1
  · simp [hs, mapSite_siteOfInt]
  · simp [hs, mapSite_siteOfInt, siteOfInt_sub, siteOfInt_single]
private theorem norm_quaternionI : ‖quaternionI‖ = 1 := by apply _root_.YangMills.SharedProofs.p9532 <;> assumption
private theorem inner_quaternionI_self :
    inner ℝ ((quaternionI : imaginaryQuaternions) : ℍ[ℝ]) ((quaternionI : imaginaryQuaternions) : ℍ[ℝ]) = 1 := by apply _root_.YangMills.Construction.RunningCouplingSlope.LocalDensityCoefficient.inner_quaternionI_self <;> assumption
section LimitKernel
variable {l : Filter ℕ} [l.NeBot] {H : GaugeTotal} {K : LatticeBond → LatticeBond → ℝ}
omit [l.NeBot] in
private theorem tendsto_hessian_kernel (hK : IsLocalGaugeTotal l H K) (c c' : LatticeBond) :
    Filter.Tendsto (fun n => hessianAtTrivial H n (bondFrom 0 c) (bondFrom 0 c') quaternionI quaternionI) l
      (𝓝 (K c c')) := by
  have h := hK.tendsto_kernel c c' quaternionI quaternionI
  rw [inner_quaternionI_self, one_mul] at h
  exact h
private theorem kernel_isometry (hK : IsLocalGaugeTotal l H K) (g : TorusIsometry) (c c' : LatticeBond) :
    axisSignAt g c.2 * axisSignAt g c'.2 * K (latticeBondImage g c) (latticeBondImage g c') = K c c' := by
  have h1 := hK.tendsto_kernel (latticeBondImage g c) (latticeBondImage g c') (axisSignAt g c.2 • quaternionI)
    (axisSignAt g c'.2 • quaternionI)
  have h2 := tendsto_hessian_kernel hK c c'
  have hev : (fun n => hessianAtTrivial H n (bondFrom 0 (latticeBondImage g c))
      (bondFrom 0 (latticeBondImage g c'))
      (axisSignAt g c.2 • quaternionI) (axisSignAt g c'.2 • quaternionI)) =ᶠ[l]
      fun n => hessianAtTrivial H n (bondFrom 0 c) (bondFrom 0 c') quaternionI quaternionI := by
    filter_upwards [hK.eventually_isGaugeTotalAt] with n hn
    rw [← bondImage_bondFrom, ← bondImage_bondFrom]
    exact hessian_bondImage hn g _ _ _ _
  have h3 := tendsto_nhds_unique (h1.congr' hev) h2
  rw [← h3]
  simp only [Submodule.coe_smul, real_inner_smul_left, real_inner_smul_right, inner_quaternionI_self]
  ring
private def translation (a : Fin 4 → ℤ) : TorusIsometry := ⟨1, fun _ => 1, a, fun _ => Or.inl rfl⟩
private theorem kernel_translate (hK : IsLocalGaugeTotal l H K) (a : Fin 4 → ℤ) (c c' : LatticeBond) :
    K (c.1 + a, c.2) (c'.1 + a, c'.2) = K c c' := by
  have h := kernel_isometry hK (translation a) c c'
  have e : ∀ b : LatticeBond, latticeBondImage (translation a) b = (b.1 + a, b.2) := by
    intro b
    have hb : latticeSiteImage (translation a) b.1 = b.1 + a := by
      funext i
      simp [latticeSiteImage, translation]
    have hs : (translation a).axisSign ((translation a).axisPerm.symm b.2) = 1 := rfl
    unfold latticeBondImage
    rw [if_pos hs, hb]
    rfl
  rw [e, e] at h
  simpa [axisSignAt, translation] using h
private theorem kernel_eq_offset (hK : IsLocalGaugeTotal l H K) (c c' : LatticeBond) :
    K c c' = K (0, c.2) (c'.1 - c.1, c'.2) := by
  have h := kernel_translate hK (-c.1) c c'
  rw [add_neg_cancel, ← sub_eq_add_neg] at h
  exact h.symm
private theorem ward_identity_kernel (hK : IsLocalGaugeTotal l H K) (y : Fin 4 → ℤ) :
    ∑ j : Fin 4, (K (0, 1) (y, j) - K (0, 1) (y - Pi.single j 1, j)) = 0 := by
  have hlim : Filter.Tendsto (fun n => ∑ j : Fin 4,
      (hessianAtTrivial H n (bondFrom 0 (0, 1)) (bondFrom 0 (y, j)) quaternionI quaternionI -
        hessianAtTrivial H n (bondFrom 0 (0, 1)) (bondFrom 0 (y - Pi.single j 1, j)) quaternionI quaternionI)) l
      (𝓝 (∑ j : Fin 4, (K (0, 1) (y, j) - K (0, 1) (y - Pi.single j 1, j)))) :=
    tendsto_finsetSum _ fun j _ => (tendsto_hessian_kernel hK _ _).sub (tendsto_hessian_kernel hK _ _)
  have hz : (fun n => ∑ j : Fin 4,
      (hessianAtTrivial H n (bondFrom 0 (0, 1)) (bondFrom 0 (y, j)) quaternionI quaternionI -
        hessianAtTrivial H n (bondFrom 0 (0, 1)) (bondFrom 0 (y - Pi.single j 1, j)) quaternionI quaternionI))
      =ᶠ[l] fun _ => (0 : ℝ) := by
    filter_upwards [hK.eventually_isGaugeTotalAt] with n hn
    simp only [bondFrom_zero, siteOfInt_sub, siteOfInt_single]
    exact ward_identity_torus hn quaternionI _ _
  exact tendsto_nhds_unique (hlim.congr' hz) tendsto_const_nhds
private theorem supDist_siteOfInt (a b : Fin 4 → ℤ) (hn : 2 * offsetNorm (a - b) < n) :
    supDist (siteOfInt a : TorusSite n) (siteOfInt b) = offsetNorm (a - b) := by apply _root_.YangMills.Construction.TorusLumps.SumOfFourCurvature.supDist_siteOfInt <;> assumption
private theorem kernel_exp_decay (hl : l ≤ Filter.atTop) (hK : IsLocalGaugeTotal l H K) :
    ∃ M θ : ℝ, 0 < θ ∧ ∀ c c' : LatticeBond,
      |K c c'| ≤ M * Real.exp (-(θ * offsetNorm (c.1 - c'.1))) := by
  obtain ⟨M, θ, hθ, hd⟩ := hK.exp_decay
  refine ⟨M, θ, hθ, fun c c' => ?_⟩
  refine le_of_tendsto (tendsto_hessian_kernel hK c c').abs ?_
  filter_upwards [hd, hl (Filter.eventually_gt_atTop (2 * offsetNorm (c.1 - c'.1)))] with n hn hb
  have h := hn (bondFrom 0 c) (bondFrom 0 c') quaternionI quaternionI norm_quaternionI norm_quaternionI
  rw [bondFrom_zero, bondFrom_zero] at h
  simp only [supDist_siteOfInt _ _ hb] at h
  simpa [bondFrom_zero] using h
private def reflectFirst : TorusIsometry :=
  ⟨1, fun i => if i = 0 then -1 else 1, 0, by
    intro i
    by_cases h : i = 0 <;> simp [h]⟩
private def reflectOffset (u : Fin 4 → ℤ) : Fin 4 → ℤ := latticeSiteImage reflectFirst u - Pi.single 0 1
private theorem reflectOffset_apply (u : Fin 4 → ℤ) (i : Fin 4) :
    reflectOffset u i = if i = 0 then -u 0 - 1 else u i := by
  by_cases h : i = 0
  · subst h
    simp [reflectOffset, latticeSiteImage, reflectFirst]
  · simp [reflectOffset, latticeSiteImage, reflectFirst, h]
private theorem reflectOffset_involutive : Function.Involutive reflectOffset := by
  intro u
  funext i
  by_cases h : i = 0
  · subst h
    simp [reflectOffset_apply]
  · simp [reflectOffset_apply, h]
private theorem kernel_reflect (hK : IsLocalGaugeTotal l H K) (u : Fin 4 → ℤ) :
    K (0, 1) (reflectOffset u, 0) = -K (0, 1) (u, 0) := by
  have h := kernel_isometry hK reflectFirst ((0 : Fin 4 → ℤ), (1 : Fin 4)) (u, (0 : Fin 4))
  have t1 : reflectFirst.axisSign (reflectFirst.axisPerm.symm 1) = 1 := by
    show reflectFirst.axisSign 1 = 1
    simp [reflectFirst]
  have t0 : reflectFirst.axisSign (reflectFirst.axisPerm.symm 0) = -1 := by
    show reflectFirst.axisSign 0 = -1
    simp [reflectFirst]
  have e1 : latticeBondImage reflectFirst ((0 : Fin 4 → ℤ), (1 : Fin 4)) = (0, 1) := by
    have hs : latticeSiteImage reflectFirst 0 = 0 := by
      funext i
      simp [latticeSiteImage, reflectFirst]
    unfold latticeBondImage
    rw [if_pos t1]
    show (latticeSiteImage reflectFirst 0, (1 : Fin 4)) = (0, 1)
    rw [hs]
  have e2 : latticeBondImage reflectFirst (u, (0 : Fin 4)) = (reflectOffset u, 0) := by
    unfold latticeBondImage
    rw [if_neg (by rw [show (u, (0 : Fin 4)).2 = (0 : Fin 4) from rfl, t0]; norm_num)]
    rfl
  have s1 : axisSignAt reflectFirst 1 = 1 := by
    unfold axisSignAt
    rw [t1]
    simp
  have s0 : axisSignAt reflectFirst 0 = -1 := by
    unfold axisSignAt
    rw [t0]
    simp
  rw [e1, e2] at h
  simp only [s1, s0] at h
  linarith
private def permuteAxes (p : Equiv.Perm (Fin 4)) : TorusIsometry := ⟨p, fun _ => 1, 0, fun _ => Or.inl rfl⟩
private theorem kernel_permuteAxes (hK : IsLocalGaugeTotal l H K) (p : Equiv.Perm (Fin 4)) (u : Fin 4 → ℤ) :
    K (0, p.symm 1) (u ∘ p, p.symm 0) = K (0, 1) (u, 0) := by
  have h := kernel_isometry hK (permuteAxes p) ((0 : Fin 4 → ℤ), (1 : Fin 4)) (u, (0 : Fin 4))
  have hs : ∀ z : Fin 4 → ℤ, latticeSiteImage (permuteAxes p) z = z ∘ p := by
    intro z
    funext i
    simp [latticeSiteImage, permuteAxes]
  have e : ∀ b : LatticeBond, latticeBondImage (permuteAxes p) b = (b.1 ∘ p, p.symm b.2) := by
    intro b
    simp [latticeBondImage, permuteAxes, ← hs]
  rw [e, e] at h
  simpa [axisSignAt, permuteAxes] using h
end LimitKernel
private theorem hasSum_of_forall_eq {f g : (Fin 4 → ℤ) → ℝ} {a : ℝ} (h : ∀ y, f y = g y) (hg : HasSum g a) :
    HasSum f a := by
  rw [funext h]
  exact hg
private theorem summable_exp_neg_abs {r : ℝ} (hr : 0 < r) :
    Summable fun z : ℤ => Real.exp (-(r * |(z : ℝ)|)) := by apply _root_.YangMills.SharedProofs.p3695 <;> assumption
private theorem summable_prod_pi {f : ℤ → ℝ} (h0 : ∀ z, 0 ≤ f z) (hf : Summable f) (m : ℕ) :
    Summable fun u : Fin m → ℤ => ∏ i, f (u i) := by apply _root_.YangMills.Construction.OneLoopLaw.SymbolFourierSeries.summable_pi_prod_of_nonneg <;> assumption
private theorem abs_coord_le_offsetNorm (u : Fin 4 → ℤ) (i : Fin 4) : |(u i : ℝ)| ≤ offsetNorm u := by apply _root_.YangMills.Construction.RunningCouplingSlope.LocalDensityCoefficient.abs_coord_le_offsetNorm <;> assumption
private theorem summable_mul_of_exp_decay {a q : (Fin 4 → ℤ) → ℝ} {M θ C : ℝ} (hθ : 0 < θ)
    (ha : ∀ u, |a u| ≤ M * Real.exp (-(θ * offsetNorm u)))
    (hq : ∀ u, |q u| ≤ C * (1 + (offsetNorm u : ℝ)) ^ 3) : Summable fun u => a u * q u := by
  have hr : 0 < θ / 8 := by positivity
  have hs := summable_prod_pi (f := fun z : ℤ => Real.exp (-(θ / 8 * |(z : ℝ)|)))
    (fun _ => (Real.exp_pos _).le) (summable_exp_neg_abs hr) 4
  have hD : 0 < 1 + 6 / θ := by positivity
  have hM : 0 ≤ M := by
    have h1 := (abs_nonneg _).trans (ha 0)
    exact nonneg_of_mul_nonneg_left h1 (Real.exp_pos _)
  have hC : 0 ≤ C := by
    have h1 := (abs_nonneg _).trans (hq 0)
    exact nonneg_of_mul_nonneg_left h1 (by positivity)
  refine Summable.of_norm_bounded (g := fun u : Fin 4 → ℤ => (M * C * (1 + 6 / θ) ^ 3) *
    ∏ i, Real.exp (-(θ / 8 * |(u i : ℝ)|))) (hs.mul_left _) fun u => ?_
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = offsetNorm u := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := by rw [hsdef]; exact Nat.cast_nonneg _
  have h1 : 1 + s ≤ (1 + 6 / θ) * Real.exp (θ * s / 6) := by
    have e1 : 1 + θ * s / 6 ≤ Real.exp (θ * s / 6) := by
      linarith [Real.add_one_le_exp (θ * s / 6)]
    have e2 : 1 + s ≤ (1 + 6 / θ) * (1 + θ * s / 6) := by
      have e3 : (1 + 6 / θ) * (1 + θ * s / 6) = 1 + θ * s / 6 + 6 / θ + s := by
        field_simp
        ring
      have e4 : 0 ≤ θ * s / 6 := by positivity
      have e5 : 0 ≤ 6 / θ := by positivity
      linarith
    exact e2.trans (mul_le_mul_of_nonneg_left e1 hD.le)
  have h2 : (1 + s) ^ 3 ≤ (1 + 6 / θ) ^ 3 * Real.exp (θ * s / 2) := by
    calc (1 + s) ^ 3 ≤ ((1 + 6 / θ) * Real.exp (θ * s / 6)) ^ 3 := pow_le_pow_left₀ (by positivity) h1 3
      _ = (1 + 6 / θ) ^ 3 * Real.exp (θ * s / 2) := by
        rw [mul_pow, ← Real.exp_nat_mul]
        congr 2
        push_cast
        ring
  have h3 : Real.exp (-(θ * s)) * Real.exp (θ * s / 2) = Real.exp (-(θ * s / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h4 : Real.exp (-(θ * s / 2)) ≤ ∏ i, Real.exp (-(θ / 8 * |(u i : ℝ)|)) := by
    rw [← Real.exp_sum]
    apply Real.exp_le_exp.mpr
    have e1 : ∑ i, |(u i : ℝ)| ≤ 4 * s := by
      calc ∑ i, |(u i : ℝ)| ≤ ∑ _i : Fin 4, s :=
            Finset.sum_le_sum fun i _ => by rw [hsdef]; exact abs_coord_le_offsetNorm u i
        _ = 4 * s := by simp
    rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
    nlinarith
  rw [Real.norm_eq_abs, abs_mul]
  have hau := ha u
  have hqu := hq u
  rw [← hsdef] at hau hqu
  calc |a u| * |q u| ≤ (M * Real.exp (-(θ * s))) * (C * (1 + s) ^ 3) :=
        mul_le_mul hau hqu (abs_nonneg _) (by positivity)
    _ ≤ (M * Real.exp (-(θ * s))) * (C * ((1 + 6 / θ) ^ 3 * Real.exp (θ * s / 2))) := by gcongr
    _ = M * C * (1 + 6 / θ) ^ 3 * (Real.exp (-(θ * s)) * Real.exp (θ * s / 2)) := by ring
    _ = M * C * (1 + 6 / θ) ^ 3 * Real.exp (-(θ * s / 2)) := by rw [h3]
    _ ≤ M * C * (1 + 6 / θ) ^ 3 * ∏ i, Real.exp (-(θ / 8 * |(u i : ℝ)|)) := by gcongr
private def cubicWeight (y : Fin 4 → ℤ) : ℝ := (y 0 : ℝ) ^ 2 * (y 1 : ℝ)
private theorem abs_mul_mul_le_cube {p q r s : ℝ} (hs : 0 ≤ s) (hp : |p| ≤ 1 + s) (hq : |q| ≤ 1 + s)
    (hr : |r| ≤ 1 + s) : |p * q * r| ≤ 1 * (1 + s) ^ 3 := by
  rw [abs_mul, abs_mul, one_mul, pow_succ, pow_two]
  have h0 : 0 ≤ 1 + s := by linarith
  exact mul_le_mul (mul_le_mul hp hq (abs_nonneg _) h0) hr (abs_nonneg _) (mul_nonneg h0 h0)
private theorem abs_coord_le_one_add (u : Fin 4 → ℤ) (i : Fin 4) : |(u i : ℝ)| ≤ 1 + offsetNorm u := by
  linarith [abs_coord_le_offsetNorm u i]
private theorem abs_add_coord_le (u e : Fin 4 → ℤ) (he : ∀ i, |(e i : ℝ)| ≤ 1) (i : Fin 4) :
    |((u + e) i : ℝ)| ≤ 1 + offsetNorm u := by
  have h : (((u + e) i : ℤ) : ℝ) = (u i : ℝ) + (e i : ℝ) := by simp
  rw [h]
  have h1 := abs_add_le (u i : ℝ) (e i : ℝ)
  linarith [abs_coord_le_offsetNorm u i, he i]
private theorem abs_single_le_one (j i : Fin 4) : |((Pi.single j (1 : ℤ) : Fin 4 → ℤ) i : ℝ)| ≤ 1 := by
  by_cases h : i = j
  · subst h
    simp
  · simp [h]
private theorem ward_cubic_moment {S : Fin 4 → (Fin 4 → ℤ) → ℝ} {M θ : ℝ} (hθ : 0 < θ)
    (hd : ∀ i u, |S i u| ≤ M * Real.exp (-(θ * offsetNorm u)))
    (hw : ∀ y : Fin 4 → ℤ, ∑ j : Fin 4, (S j y - S j (y - Pi.single j 1)) = 0) :
    Summable (fun y => S 0 y * (y 1 : ℝ) * (y 0 : ℝ)) ∧ Summable (fun y => S 0 y * (y 1 : ℝ)) ∧
      Summable (fun y => S 1 y * (y 0 : ℝ) ^ 2) ∧
      (∑' y, S 1 y * (y 0 : ℝ) ^ 2) =
        -2 * (∑' y, S 0 y * (y 1 : ℝ) * (y 0 : ℝ)) - ∑' y, S 0 y * (y 1 : ℝ) := by
  have hm : Summable (fun y => S 0 y * (y 1 : ℝ) * (y 0 : ℝ)) := by
    have h := summable_mul_of_exp_decay (q := fun y => (y 1 : ℝ) * (y 0 : ℝ) * 1) (C := 1) hθ (hd 0)
      fun u => abs_mul_mul_le_cube (Nat.cast_nonneg _) (abs_coord_le_one_add u 1)
        (abs_coord_le_one_add u 0) (by
        have : (0 : ℝ) ≤ offsetNorm u := Nat.cast_nonneg _
        rw [abs_one]
        linarith)
    exact h.congr fun y => by ring
  have ha : Summable (fun y => S 0 y * (y 1 : ℝ)) := by
    have h := summable_mul_of_exp_decay (q := fun y => (y 1 : ℝ) * 1 * 1) (C := 1) hθ (hd 0)
      fun u => by
        have h0 : (0 : ℝ) ≤ offsetNorm u := Nat.cast_nonneg _
        exact abs_mul_mul_le_cube h0 (abs_coord_le_one_add u 1) (by rw [abs_one]; linarith)
          (by rw [abs_one]; linarith)
    exact h.congr fun y => by ring
  have hq : Summable (fun y => S 1 y * (y 0 : ℝ) ^ 2) := by
    have h := summable_mul_of_exp_decay (q := fun y => (y 0 : ℝ) * (y 0 : ℝ) * 1) (C := 1) hθ (hd 1)
      fun u => by
        have h0 : (0 : ℝ) ≤ offsetNorm u := Nat.cast_nonneg _
        exact abs_mul_mul_le_cube h0 (abs_coord_le_one_add u 0) (abs_coord_le_one_add u 0)
          (by rw [abs_one]; linarith)
    exact h.congr fun y => by ring
  refine ⟨hm, ha, hq, ?_⟩
  have hA : ∀ i, Summable fun y => S i y * cubicWeight y := by
    intro i
    have h := summable_mul_of_exp_decay (q := fun y => (y 0 : ℝ) * (y 0 : ℝ) * (y 1 : ℝ)) (C := 1) hθ (hd i)
      fun u => abs_mul_mul_le_cube (Nat.cast_nonneg _) (abs_coord_le_one_add u 0) (abs_coord_le_one_add u 0)
        (abs_coord_le_one_add u 1)
    exact h.congr fun y => by simp only [cubicWeight]; ring
  have hB : ∀ i : Fin 4, Summable fun y => S i y * cubicWeight (y + Pi.single i 1) := by
    intro i
    have h := summable_mul_of_exp_decay (q := fun y : Fin 4 → ℤ =>
      (((y + Pi.single i 1 : Fin 4 → ℤ) 0 : ℤ) : ℝ) * (((y + Pi.single i 1 : Fin 4 → ℤ) 0 : ℤ) : ℝ) *
        (((y + Pi.single i 1 : Fin 4 → ℤ) 1 : ℤ) : ℝ)) (C := 1) hθ (hd i)
      fun u => abs_mul_mul_le_cube (Nat.cast_nonneg _) (abs_add_coord_le u _ (abs_single_le_one i) 0)
        (abs_add_coord_le u _ (abs_single_le_one i) 0) (abs_add_coord_le u _ (abs_single_le_one i) 1)
    exact h.congr fun y => by simp only [cubicWeight]; ring
  have hC : ∀ i : Fin 4, HasSum (fun y => S i (y - Pi.single i 1) * cubicWeight y)
      (∑' y, S i y * cubicWeight (y + Pi.single i 1)) := by
    intro i
    have h := ((Equiv.subRight (Pi.single i (1 : ℤ) : Fin 4 → ℤ)).hasSum_iff).mpr (hB i).hasSum
    have e : ((fun y => S i y * cubicWeight (y + Pi.single i 1)) ∘
        (Equiv.subRight (Pi.single i (1 : ℤ) : Fin 4 → ℤ))) =
        fun y => S i (y - Pi.single i 1) * cubicWeight y := by
      funext y
      simp
    rwa [e] at h
  have hsum : HasSum (fun y => ∑ i : Fin 4, (S i y * cubicWeight y - S i (y - Pi.single i 1) * cubicWeight y))
      (∑ i : Fin 4, ((∑' y, S i y * cubicWeight y) - ∑' y, S i y * cubicWeight (y + Pi.single i 1))) :=
    hasSum_sum fun i _ => (hA i).hasSum.sub (hC i)
  have hzero : (fun y => ∑ i : Fin 4, (S i y * cubicWeight y - S i (y - Pi.single i 1) * cubicWeight y)) =
      fun _ => 0 := by
    funext y
    calc ∑ i : Fin 4, (S i y * cubicWeight y - S i (y - Pi.single i 1) * cubicWeight y)
        = (∑ j : Fin 4, (S j y - S j (y - Pi.single j 1))) * cubicWeight y := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = 0 := by rw [hw y, zero_mul]
  rw [hzero] at hsum
  have htot := hsum.unique hasSum_zero
  have hD : ∀ i : Fin 4, HasSum (fun y => S i y * cubicWeight y - S i y * cubicWeight (y + Pi.single i 1))
      ((∑' y, S i y * cubicWeight y) - ∑' y, S i y * cubicWeight (y + Pi.single i 1)) :=
    fun i => (hA i).hasSum.sub (hB i).hasSum
  have e0 : ((∑' y, S 0 y * cubicWeight y) - ∑' y, S 0 y * cubicWeight (y + Pi.single 0 1)) =
      -2 * (∑' y, S 0 y * (y 1 : ℝ) * (y 0 : ℝ)) - ∑' y, S 0 y * (y 1 : ℝ) := by
    refine (hD 0).unique (hasSum_of_forall_eq (fun y => ?_) ((hm.hasSum.mul_left (-2)).sub ha.hasSum))
    simp [cubicWeight]
    ring
  have e1 : ((∑' y, S 1 y * cubicWeight y) - ∑' y, S 1 y * cubicWeight (y + Pi.single 1 1)) =
      -∑' y, S 1 y * (y 0 : ℝ) ^ 2 := by
    refine (hD 1).unique (hasSum_of_forall_eq (fun y => ?_) hq.hasSum.neg)
    simp [cubicWeight]
    ring
  have e2 : ((∑' y, S 2 y * cubicWeight y) - ∑' y, S 2 y * cubicWeight (y + Pi.single 2 1)) = 0 := by
    refine (hD 2).unique (hasSum_of_forall_eq (fun y => ?_) hasSum_zero)
    simp [cubicWeight]
  have e3 : ((∑' y, S 3 y * cubicWeight y) - ∑' y, S 3 y * cubicWeight (y + Pi.single 3 1)) = 0 := by
    refine (hD 3).unique (hasSum_of_forall_eq (fun y => ?_) hasSum_zero)
    simp [cubicWeight]
  rw [Fin.sum_univ_four, e0, e1, e2, e3] at htot
  linarith
private theorem exists_perm_to_first_axes {μ ν : Fin 4} (h : μ ≠ ν) :
    ∃ p : Equiv.Perm (Fin 4), p μ = 1 ∧ p ν = 0 := by
  have hν : Equiv.swap μ 1 ν ≠ 1 := by
    intro e
    apply h
    have h1 : Equiv.swap μ 1 ν = Equiv.swap μ 1 μ := by rw [e, Equiv.swap_apply_left]
    exact ((Equiv.swap μ 1).injective h1).symm
  refine ⟨Equiv.swap (Equiv.swap μ 1 ν) 0 * Equiv.swap μ 1, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne hν.symm (by decide)
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
theorem slopeIsMixedMoment : SlopeIsMixedMoment := by
  intro l _ hl H b hb
  obtain ⟨K, hK, hsum⟩ := hb
  obtain ⟨M, θ, hθ, hdec⟩ := kernel_exp_decay hl hK
  have hd : ∀ (i : Fin 4) (u : Fin 4 → ℤ), |K (0, 1) (u, i)| ≤ M * Real.exp (-(θ * offsetNorm u)) := by
    intro i u
    have h : |K (0, 1) (u, i)| ≤ M * Real.exp (-(θ * offsetNorm ((0 : Fin 4 → ℤ) - u))) :=
      hdec (0, 1) (u, i)
    have e : offsetNorm ((0 : Fin 4 → ℤ) - u) = offsetNorm u := by simp [offsetNorm]
    rwa [e] at h
  obtain ⟨hm, ha, hq, hrel⟩ := ward_cubic_moment (S := fun i u => K (0, 1) (u, i)) hθ hd
    fun y => ward_identity_kernel hK y
  have ha0 : ∑' y : Fin 4 → ℤ, K (0, 1) (y, 0) * (y 1 : ℝ) = 0 := by
    have h1 := (reflectOffset_involutive.toPerm.hasSum_iff).mpr ha.hasSum
    have h2 : HasSum (fun y : Fin 4 → ℤ => -(K (0, 1) (y, 0) * (y 1 : ℝ)))
        (∑' y : Fin 4 → ℤ, K (0, 1) (y, 0) * (y 1 : ℝ)) := by
      refine hasSum_of_forall_eq (fun y => ?_) h1
      show _ = K (0, 1) (reflectOffset y, 0) * ((reflectOffset y 1 : ℤ) : ℝ)
      rw [kernel_reflect hK]
      simp [reflectOffset_apply]
    have h3 := ha.hasSum.neg.unique h2
    linarith
  have hb' : HasSum (fun u : Fin 4 → ℤ => K (0, 1) (u, 0) * (u 1 : ℝ) * (u 0 : ℝ)) b := by
    have h1 : HasSum (secondMomentTerm K)
        (-(1 / 2) * ∑' y : Fin 4 → ℤ, K (0, 1) (y, 1) * (y 0 : ℝ) ^ 2) := by
      refine hasSum_of_forall_eq (fun z => ?_) (hq.hasSum.mul_left (-(1 / 2)))
      simp only [secondMomentTerm, secondAxis]
      ring
    have hbv := hsum.unique h1
    rw [hrel, ha0] at hbv
    have e : b = ∑' y : Fin 4 → ℤ, K (0, 1) (y, 0) * (y 1 : ℝ) * (y 0 : ℝ) := by
      rw [hbv]
      ring
    rw [e]
    exact hm.hasSum
  refine ⟨fun μ ν u => K (0, μ) (u, ν), ?_, ?_⟩
  · intro c c' X X'
    have h := hK.tendsto_kernel c c' X X'
    rwa [kernel_eq_offset hK c c'] at h
  · intro μ ν hμν
    obtain ⟨p, h1, h2⟩ := exists_perm_to_first_axes hμν
    have hs1 : p.symm 1 = μ := by rw [← h1]; simp
    have hs0 : p.symm 0 = ν := by rw [← h2]; simp
    let e : (Fin 4 → ℤ) ≃ (Fin 4 → ℤ) :=
      { toFun := fun u => u ∘ p
        invFun := fun v => v ∘ p.symm
        left_inv := fun u => by funext i; simp
        right_inv := fun v => by funext i; simp }
    refine (e.hasSum_iff).mp (hasSum_of_forall_eq (fun u => ?_) hb')
    have hk := kernel_permuteAxes hK p u
    rw [hs1, hs0] at hk
    show K (0, μ) (u ∘ p, ν) * (((u ∘ p) μ : ℤ) : ℝ) * (((u ∘ p) ν : ℤ) : ℝ) = _
    rw [hk]
    simp [h1, h2]
end YangMills.Construction.SlopeCoefficient
end
