import YangMills.Construction.ClusterExpansionOfAStep.OneCouplingAtGivenParametersProof
import YangMills.Construction.ColdStepAtMirrorFrames.SecondOrderOfADensityAtConstantCurvatureProof
import YangMills.Construction.ClusterExpansionOfAStep.FormOfTheShares
import YangMills.Construction.ColdStepAtMirrorFrames.FlatFormFromASmallDifferenceProof
import YangMills.Construction.LawInAState.MarkAtACurvedField
import YangMills.Construction.LawInAState.TheMarkOfAFunctionOfTheField
import YangMills.Construction.ResponseInTheExpansion.ColdResponsesKeepTheGauge
import YangMills.Construction.ResponseInTheExpansion.WeightsNearTheirMeans
import YangMills.Construction.ResponseInTheExpansion.WilsonWeightHasTheExpansionOfTheResponseProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.StateLaws
open TorusFields TorusLumps BlockAverages WeightedResponses ResponseInTheExpansion RenormalizationStepParameters StepSettings StepCosts
  ShareFamilies FlatHessian LumpContours StateLaw AxialLogarithm BoxForm CurvatureKernel AxialForms LatticeSums
variable {n : ℕ}
private theorem mixedDeriv_fin_zero (G : TorusField n → ℝ) (W : TorusField n) (c : Fin 0 → TorusBond n)
    (X : Fin 0 → imaginaryQuaternions) : mixedDeriv G W c X = G W := by apply _root_.YangMills.Construction.TorusLumps.mixedDeriv_of_fin_zero <;> assumption
private def curvedMark (a b : ℝ) (S R T : TorusField n → ℝ) : TorusField n → ℝ := fun W => a * (b * S W + R W) + T W
private theorem curvedMark_contDiffThree {a b : ℝ} {S R T : TorusField n → ℝ} {W : TorusField n}
    (hS : ContDiffThreeAt S W) (hR : ContDiffThreeAt R W) (hT : ContDiffThreeAt T W) :
    ContDiffThreeAt (curvedMark a b S R T) W := by
  intro k c X
  have h1 := hS k c X
  have h2 := hR k c X
  have h3 := hT k c X
  exact (contDiffAt_const.mul ((contDiffAt_const.mul h1).add h2)).add h3
private theorem curvedMark_mixedDeriv {a b : ℝ} {S R T : TorusField n → ℝ} {W : TorusField n} {k : ℕ} (hk : k ≤ 3)
    (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (hS : ContDiffThreeAt S W) (hR : ContDiffThreeAt R W) (hT : ContDiffThreeAt T W) :
    mixedDeriv (curvedMark a b S R T) W c X = a * (b * mixedDeriv S W c X + mixedDeriv R W c X) + mixedDeriv T W c X := by
  have h1 := (hS k c X).of_le (m := k) (by exact_mod_cast hk)
  have h2 := (hR k c X).of_le (m := k) (by exact_mod_cast hk)
  have h3 := (hT k c X).of_le (m := k) (by exact_mod_cast hk)
  have e : (fun σ : Fin k → ℝ => curvedMark a b S R T (TorusFields.perturb c X σ W)) =
      a • (b • (fun σ => S (TorusFields.perturb c X σ W)) + fun σ => R (TorusFields.perturb c X σ W)) +
        fun σ => T (TorusFields.perturb c X σ W) := by
    funext σ
    simp [curvedMark, mul_add]
  have hb1 : ContDiffAt ℝ k (b • (fun σ => S (TorusFields.perturb c X σ W))) 0 := h1.const_smul b
  have hb : ContDiffAt ℝ k (b • (fun σ => S (TorusFields.perturb c X σ W)) + fun σ => R (TorusFields.perturb c X σ W)) 0 :=
    hb1.add h2
  have hA : ContDiffAt ℝ k (a • (b • (fun σ => S (TorusFields.perturb c X σ W)) +
      fun σ => R (TorusFields.perturb c X σ W))) 0 :=
    hb.const_smul a
  unfold mixedDeriv
  rw [e, iteratedFDeriv_add_apply hA h3, iteratedFDeriv_const_smul_apply hb, iteratedFDeriv_add_apply hb1 h2,
    iteratedFDeriv_const_smul_apply h1]
  simp
  ring
private theorem curvatureFamily_mono {ℓ : StepParameters} {C C' : ℝ} {f : LocalDensity} (hf : IsCurvatureFamily ℓ C f)
    (h : C ≤ C') (hw : ∀ m, 0 < ℓ.weight m) : IsCurvatureFamily ℓ C' f where
  smooth := hf.smooth
  gauge := hf.gauge
  translation := hf.translation
  decay := fun n _ hn y W hW k c X h1 h3 hX =>
    (hf.decay n hn y W hW k c X h1 h3 hX).trans (div_le_div_of_nonneg_right h (hw _).le)
  local_density := fun n n' _ _ hn hn' y y' W W' m h1 h2 hW hW' ha k b X hk hb hX =>
    (hf.local_density n n' hn hn' y y' W W' m h1 h2 hW hW' ha k b X hk hb hX).trans
      (div_le_div_of_nonneg_right h (hw _).le)
private theorem curvatureFamily_of_coldBounds {ℓ : StepParameters} {E E₃ C : ℝ} {f : LocalDensity}
    (hf : ColdDensityBounds ℓ E E₃ f) (h : E ≤ C) (h3 : E₃ ≤ C)
    (hw : ∀ m, 0 < ℓ.weight m) : IsCurvatureFamily ℓ C f where
  smooth := hf.smooth
  gauge := hf.gauge
  translation := hf.translation
  decay := fun n _ hn y W hW k c X h1 h2 hX => by
    refine (hf.decay n hn y W hW k c X h1 h2 hX).trans (div_le_div_of_nonneg_right ?_ (hw _).le)
    split_ifs
    · exact h3
    · exact h
  local_density := fun n n' _ _ hn hn' y y' W W' m h1 h2 hW hW' ha k b X hk hb hX =>
    (hf.local_density n n' hn hn' y y' W W' m h1 h2 hW hW' ha k b X hk hb hX).trans
      (div_le_div_of_nonneg_right h (hw _).le)
private theorem stepWeight_pos {ℓ : StepParameters} (m : ℕ) : 0 < ℓ.weight m := by apply _root_.YangMills.Construction.WilsonExpansion.weight_pos <;> assumption
private theorem exp_le_stepWeight (ℓ : StepParameters) (m : ℕ) : Real.exp (ℓ.weightRate * m) ≤ ℓ.weight m := by apply _root_.YangMills.SharedProofs.p47115 <;> assumption
private def planeUnitCurvature (μ ν : Fin 4) : Fin 4 → Fin 4 → ℝ := fun i j =>
  if i = μ ∧ j = ν then 1 else if i = ν ∧ j = μ then -1 else 0
private theorem planeUnitCurvature_antisymm {μ ν : Fin 4} (h : μ < ν) (i j : Fin 4) :
    planeUnitCurvature μ ν i j = - planeUnitCurvature μ ν j i := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondOrderAtConstantCurvature.planeUnitForm_antisymm <;> assumption
private theorem abs_planeUnitCurvature_le (μ ν i j : Fin 4) : |planeUnitCurvature μ ν i j| ≤ 1 := by apply _root_.YangMills.Construction.PlaneFields.abs_planeForm_le_one <;> assumption
private theorem curvaturePairing_planes {μ ν ρ τ : Fin 4} (h : μ < ν) (h' : ρ < τ) :
    curvaturePairing (curvatureAlong FlatHessian.quaternionI (planeUnitCurvature μ ν))
      (curvatureAlong FlatHessian.quaternionI (planeUnitCurvature ρ τ)) = if (μ, ν) = (ρ, τ) then 1 else 0 := by
  have hi : inner ℝ ((FlatHessian.quaternionI : imaginaryQuaternions) : ℍ[ℝ])
      ((FlatHessian.quaternionI : imaginaryQuaternions) : ℍ[ℝ]) = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq]
    have h1 : Quaternion.normSq ((FlatHessian.quaternionI : imaginaryQuaternions) : ℍ[ℝ]) = 1 := by
      rw [Quaternion.normSq_def']
      simp [FlatHessian.quaternionI]
    rw [sq, ← Quaternion.normSq_eq_norm_mul_self, h1]
  have hne : μ ≠ ν := ne_of_lt h
  have term : ∀ i j : Fin 4, (if i < j then inner ℝ
      ((curvatureAlong FlatHessian.quaternionI (planeUnitCurvature μ ν) i j : imaginaryQuaternions) : ℍ[ℝ])
      ((curvatureAlong FlatHessian.quaternionI (planeUnitCurvature ρ τ) i j : imaginaryQuaternions) : ℍ[ℝ])
      else (0 : ℝ)) =
      if i = μ then (if j = ν then (if (μ, ν) = (ρ, τ) then 1 else 0) else 0) else 0 := by
    intro i j
    by_cases h1 : i = μ ∧ j = ν
    · obtain ⟨rfl, rfl⟩ := h1
      simp only [h, if_true, curvatureAlong, Submodule.coe_smul, inner_smul_left, inner_smul_right, hi]
      by_cases h2 : (i, j) = (ρ, τ)
      · obtain ⟨rfl, rfl⟩ : i = ρ ∧ j = τ := Prod.ext_iff.1 h2
        simp [planeUnitCurvature]
      · have h3 : ¬ (i = ρ ∧ j = τ) := fun h => h2 (Prod.ext h.1 h.2)
        have h4 : ¬ (i = τ ∧ j = ρ) := by
          rintro ⟨rfl, rfl⟩
          exact absurd h (not_lt.2 h'.le)
        simp [planeUnitCurvature, h2, h3, h4]
    · have hR : (if i = μ then (if j = ν then (if (μ, ν) = (ρ, τ) then (1 : ℝ) else 0) else 0) else 0) = 0 := by
        by_cases a : i = μ
        · have : j ≠ ν := fun b => h1 ⟨a, b⟩
          simp [a, this]
        · simp [a]
      rw [hR]
      by_cases hij : i < j
      · have h2 : ¬ (i = ν ∧ j = μ) := by
          rintro ⟨rfl, rfl⟩
          exact absurd h (not_lt.2 hij.le)
        simp [hij, curvatureAlong, planeUnitCurvature, h1, h2]
      · simp [hij]
  unfold curvaturePairing
  simp only [term]
  rw [Finset.sum_eq_single μ (fun b _ hb => by simp [hb]) (by simp)]
  simp
private theorem sum_four_swap {ι κ : Type*} (T T' : Finset ι) (s : Finset κ) (Q : κ → κ → ℝ) (A : κ → ι → ℝ) :
    ∑ p ∈ T, ∑ p' ∈ T', ∑ c ∈ s, ∑ c' ∈ s, Q c c' * (A c p * A c' p') =
      ∑ c ∈ s, ∑ c' ∈ s, Q c c' * ((∑ p ∈ T, A c p) * ∑ p' ∈ T', A c' p') := by
  have e : ∀ c c', Q c c' * ((∑ p ∈ T, A c p) * ∑ p' ∈ T', A c' p') =
      ∑ p ∈ T, ∑ p' ∈ T', Q c c' * (A c p * A c' p') := by
    intro c c'
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => e c c']
  calc _ = ∑ p ∈ T, ∑ c ∈ s, ∑ p' ∈ T', ∑ c' ∈ s, Q c c' * (A c p * A c' p') :=
        Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ = ∑ c ∈ s, ∑ p ∈ T, ∑ p' ∈ T', ∑ c' ∈ s, Q c c' * (A c p * A c' p') := Finset.sum_comm
    _ = ∑ c ∈ s, ∑ p ∈ T, ∑ c' ∈ s, ∑ p' ∈ T', Q c c' * (A c p * A c' p') :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun c _ => Finset.sum_comm
private theorem axialFormCoeff_plane_sum [NeZero n] (z : TorusSite n) (c : LatticeBond) {μ ν : Fin 4} (h : μ < ν) :
    ∑ p ∈ (plaquettesIn (Finset.univ : Finset (TorusSite n))).filter (fun p : TorusPlaquette n => p.2 = (μ, ν)),
      axialFormCoeff z c p = constantCurvaturePotential (planeUnitCurvature μ ν) c := by
  have h1 := axialForm_eq_sum_coeff z c (plaquettesIn Finset.univ) (fun p => if p.2 = (μ, ν) then 1 else 0)
    (fun ν' hν j _ => by simp [plaquettesIn, hν])
  rw [Finset.sum_filter]
  have e1 : ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)),
      (if p.2 = (μ, ν) then axialFormCoeff z c p else 0) =
      ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)),
        axialFormCoeff z c p * (if p.2 = (μ, ν) then 1 else 0) :=
    Finset.sum_congr rfl fun p _ => by split_ifs <;> simp
  rw [e1, ← h1]
  unfold BoxForm.constantCurvaturePotential axialForm
  congr 1
  refine Finset.sum_congr rfl fun ν' _ => ?_
  by_cases hν : c.2 < ν'
  · simp only [hν, if_true]
    refine intervalSum_congr _ fun j => ?_
    by_cases a : c.2 = μ ∧ ν' = ν
    · obtain ⟨a1, a2⟩ := a
      simp [planeUnitCurvature, a1, a2]
    · have b : ¬ (c.2 = ν ∧ ν' = μ) := by
        rintro ⟨b1, b2⟩
        rw [b1, b2] at hν
        exact absurd h (not_lt.2 hν.le)
      have a' : ¬ ((c.2, ν') = (μ, ν)) := fun e => a (Prod.ext_iff.1 e)
      simp [planeUnitCurvature, a, b, a']
  · simp [hν]
private theorem curvatureKernel_plane_sum [NeZero n] (U : TorusField n → ℝ) (z : TorusSite n) (m : ℕ) {μ ν ρ τ : Fin 4}
    (h : μ < ν) (h' : ρ < τ) :
    ∑ p ∈ (plaquettesIn (Finset.univ : Finset (TorusSite n))).filter (fun p : TorusPlaquette n => p.2 = (μ, ν)),
      ∑ p' ∈ (plaquettesIn (Finset.univ : Finset (TorusSite n))).filter (fun p' : TorusPlaquette n => p'.2 = (ρ, τ)),
        curvatureKernel U z m p p' =
      ∑ c ∈ bondsWithin m, ∑ c' ∈ bondsWithin m, flatHessian U (bondFrom z c) (bondFrom z c') *
        (constantCurvaturePotential (planeUnitCurvature μ ν) c *
          constantCurvaturePotential (planeUnitCurvature ρ τ) c') := by
  unfold curvatureKernel
  rw [sum_four_swap _ _ (bondsWithin m) (fun c c' => flatHessian U (bondFrom z c) (bondFrom z c'))
    (fun c p => axialFormCoeff z c p)]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
  rw [axialFormCoeff_plane_sum z c h, axialFormCoeff_plane_sum z c' h']
private theorem abs_sum_against_potentials_le {Qf : LatticeBond → LatticeBond → ℝ} {B r : ℝ} {m : ℕ}
    {ω ω' : Fin 4 → Fin 4 → ℝ} (hB : 0 ≤ B)
    (hr : 0 < r) (h1 : ∀ i j, |ω i j| ≤ 1) (h1' : ∀ i j, |ω' i j| ≤ 1)
    (hq : ∀ c ∈ bondsWithin m, ∀ c' ∈ bondsWithin m,
      |Qf c c'| ≤ B * Real.exp (-(r * max (offsetSupNorm c.1 : ℝ) (offsetSupNorm c'.1 : ℝ)))) :
    |∑ c ∈ bondsWithin m, ∑ c' ∈ bondsWithin m,
        Qf c c' * (constantCurvaturePotential ω c * constantCurvaturePotential ω' c')| ≤
      16 * B * bondWeightSum (r / 4) 3 ^ 2 := by
  rw [← Finset.sum_product' (bondsWithin m) (bondsWithin m)
    (fun c c' => Qf c c' * (constantCurvaturePotential ω c * constantCurvaturePotential ω' c'))]
  have abound : ∀ {ζ : Fin 4 → Fin 4 → ℝ}, (∀ i j, |ζ i j| ≤ 1) → ∀ c : LatticeBond,
      |constantCurvaturePotential ζ c| ≤ 4 * (1 + (offsetSupNorm c.1 : ℝ)) ^ 3 := by
    intro ζ hz c
    have h := abs_axialForm_le (D := fun _ μ ν => ζ μ ν) (c := c) (t := 1) (fun ν _ j _ => hz _ _) zero_le_one
    have h2 : (offsetSupNorm c.1 : ℝ) ≤ (1 + (offsetSupNorm c.1 : ℝ)) ^ 3 := by
      nlinarith [Nat.cast_nonneg (α := ℝ) (offsetSupNorm c.1), sq_nonneg (offsetSupNorm c.1 : ℝ),
        pow_nonneg (Nat.cast_nonneg (α := ℝ) (offsetSupNorm c.1)) 3]
    have h3 : |constantCurvaturePotential ζ c| ≤ 4 * (offsetSupNorm c.1 : ℝ) * 1 := h
    linarith
  have hb : ∀ cc ∈ bondsWithin m ×ˢ bondsWithin m,
      |Qf cc.1 cc.2 * (constantCurvaturePotential ω cc.1 * constantCurvaturePotential ω' cc.2)| ≤
      16 * B * bondPairWeight r cc := by
    intro cc hcc
    obtain ⟨i1, i2⟩ := Finset.mem_product.1 hcc
    rw [abs_mul, abs_mul]
    calc _ ≤ B * Real.exp (-(r * max (offsetSupNorm cc.1.1 : ℝ) (offsetSupNorm cc.2.1 : ℝ))) *
          ((4 * (1 + (offsetSupNorm cc.1.1 : ℝ)) ^ 3) * (4 * (1 + (offsetSupNorm cc.2.1 : ℝ)) ^ 3)) := by
          gcongr
          · exact hq _ i1 _ i2
          · exact abound h1 cc.1
          · exact abound h1' cc.2
      _ = _ := by
          unfold bondPairWeight
          ring
  have hsum := sum_bondPairWeight_le hr (bondsWithin m ×ˢ bondsWithin m) 0 le_rfl
    (fun cc _ => le_max_of_le_left (Nat.cast_nonneg _))
  simp only [mul_zero, neg_zero, Real.exp_zero, mul_one] at hsum
  calc _ ≤ ∑ cc ∈ bondsWithin m ×ˢ bondsWithin m,
        |Qf cc.1 cc.2 * (constantCurvaturePotential ω cc.1 * constantCurvaturePotential ω' cc.2)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ cc ∈ bondsWithin m ×ˢ bondsWithin m, 16 * B * bondPairWeight r cc := Finset.sum_le_sum hb
    _ = 16 * B * ∑ cc ∈ bondsWithin m ×ˢ bondsWithin m, bondPairWeight r cc := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)
private theorem offsetSupNorm_max_le_supportDiam [NeZero n] {z : TorusSite n} {c c' : LatticeBond}
    (hc : 2 * offsetSupNorm c.1 < n) (hc' : 2 * offsetSupNorm c'.1 < n) :
    max (offsetSupNorm c.1 : ℝ) (offsetSupNorm c'.1 : ℝ) ≤ supportDiam z ![bondFrom z c, bondFrom z c'] := by
  have t1 : offsetSupNorm c.1 ≤ supportDiam z ![bondFrom z c, bondFrom z c'] := by
    have h1 : _root_.YangMills.Construction.TorusFields.supDist z (bondFrom z c).1 ≤ supportDiam z ![bondFrom z c, bondFrom z c'] := le_max_of_le_left
      (Finset.le_sup (f := fun l : Fin 2 => supDist z ((![bondFrom z c, bondFrom z c'] : Fin 2 → TorusBond n) l).1)
        (Finset.mem_univ 0))
    have h2 : _root_.YangMills.Construction.TorusFields.supDist (z + siteOfInt c.1) z = offsetSupNorm c.1 := _root_.YangMills.Construction.LatticeSums.supDist_add_siteOfInt z hc
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm] at h1
    change _root_.YangMills.Construction.TorusFields.supDist (z + siteOfInt c.1) z ≤ _ at h1
    omega
  have t2 : offsetSupNorm c'.1 ≤ supportDiam z ![bondFrom z c, bondFrom z c'] := by
    have h1 : _root_.YangMills.Construction.TorusFields.supDist z (bondFrom z c').1 ≤ supportDiam z ![bondFrom z c, bondFrom z c'] := le_max_of_le_left
      (Finset.le_sup (f := fun l : Fin 2 => supDist z ((![bondFrom z c, bondFrom z c'] : Fin 2 → TorusBond n) l).1)
        (Finset.mem_univ 1))
    have h2 : _root_.YangMills.Construction.TorusFields.supDist (z + siteOfInt c'.1) z = offsetSupNorm c'.1 := _root_.YangMills.Construction.LatticeSums.supDist_add_siteOfInt z hc'
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm] at h1
    change _root_.YangMills.Construction.TorusFields.supDist (z + siteOfInt c'.1) z ≤ _ at h1
    omega
  exact max_le (by exact_mod_cast t1) (by exact_mod_cast t2)
private theorem curvedMark_isRegularObservable [NeZero n] {ℓ : StepParameters} {Ca Cr Ck a b : ℝ}
    {S R T : TorusField n → ℝ} {z : TorusSite n}
    (hCa : 0 ≤ Ca) (hCr : 0 ≤ Cr) (hCk : 0 ≤ Ck) (ha : |a| ≤ 1) (hb : |b| ≤ 2)
    (hS : ∀ W, IsCold ℓ.threshold W → ContDiffThreeAt S W) (hR : ∀ W, IsCold ℓ.threshold W → ContDiffThreeAt R W)
    (hT : ∀ W, IsCold ℓ.threshold W → ContDiffThreeAt T W)
    (gS : ∀ (g : TorusSite n → UnitQuaternion) W, IsCold ℓ.threshold W → S (TorusFields.gaugeTransform g W) = S W)
    (gR : ∀ (g : TorusSite n → UnitQuaternion) W, IsCold ℓ.threshold W → R (TorusFields.gaugeTransform g W) = R W)
    (gT : ∀ (g : TorusSite n → UnitQuaternion) W, IsCold ℓ.threshold W → T (TorusFields.gaugeTransform g W) = T W)
    (dS : ∀ W, IsCold ℓ.threshold W → ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
      1 ≤ k → k ≤ 3 → AreUnitVectors X → |mixedDeriv S W c X| ≤ Ca / ℓ.weight (supportDiam z c))
    (dR : ∀ W, IsCold ℓ.threshold W → ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
      1 ≤ k → k ≤ 3 → AreUnitVectors X → |mixedDeriv R W c X| ≤ Cr / ℓ.weight (supportDiam z c))
    (dT : ∀ W, IsCold ℓ.threshold W → ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
      1 ≤ k → k ≤ 3 → AreUnitVectors X → |mixedDeriv T W c X| ≤ Ck / ℓ.weight (supportDiam z c)) :
    IsRegularObservable ℓ.threshold (2 * Ca + Cr + Ck) (2 * Ca + Cr + Ck) ℓ.weight z (curvedMark a b S R T) where
  contDiff := fun W hW => curvedMark_contDiffThree (hS W hW) (hR W hW) (hT W hW)
  gauge_invariant := fun g W hW => by
    simp only [curvedMark, gS g W hW, gR g W hW, gT g W hW]
  deriv_bound := fun W hW k c X h1 h3 hX => by
    rw [curvedMark_mixedDeriv h3 c X (hS W hW) (hR W hW) (hT W hW), ite_self]
    have w0 := stepWeight_pos (ℓ := ℓ) (supportDiam z c)
    have e1 := dS W hW k c X h1 h3 hX
    have e2 := dR W hW k c X h1 h3 hX
    have e3 := dT W hW k c X h1 h3 hX
    set q := (ℓ.weight (supportDiam z c))⁻¹ with hq
    rw [div_eq_mul_inv] at e1 e2 e3 ⊢
    have t1 : |b * mixedDeriv S W c X| ≤ 2 * (Ca * q) := by
      rw [abs_mul]
      exact mul_le_mul hb e1 (abs_nonneg _) (by norm_num)
    have t2 : |b * mixedDeriv S W c X + mixedDeriv R W c X| ≤ 2 * (Ca * q) + Cr * q :=
      (abs_add_le _ _).trans (add_le_add t1 e2)
    have t3 : |a * (b * mixedDeriv S W c X + mixedDeriv R W c X)| ≤ 1 * (2 * (Ca * q) + Cr * q) := by
      rw [abs_mul]
      exact mul_le_mul ha t2 (abs_nonneg _) zero_le_one
    refine (abs_add_le _ _).trans ((add_le_add t3 e3).trans (le_of_eq ?_))
    ring
private theorem abs_curvedMark_planes_le [NeZero n] {ℓ : StepParameters} {a b C₁ C₂ B e₁ e₂ : ℝ}
    {S R T : TorusField n → ℝ} {z : TorusSite n} {m : ℕ}
    (hr : 0 < ℓ.weightRate) (hB : 0 ≤ B) (ha : |a| ≤ 1) (hb : |b| ≤ 2) (he₁ : 0 ≤ e₁) (he₂ : 0 ≤ e₂)
    (hS : ContDiffThreeAt S (trivialField n)) (hR : ContDiffThreeAt R (trivialField n))
    (hT : ContDiffThreeAt T (trivialField n))
    (hq : ∀ c ∈ bondsWithin m, ∀ c' ∈ bondsWithin m, |flatHessian T (bondFrom z c) (bondFrom z c')| ≤
      B * Real.exp (-(ℓ.weightRate * max (offsetSupNorm c.1 : ℝ) (offsetSupNorm c'.1 : ℝ))))
    {μ ν ρ τ : Fin 4} (h : μ < ν) (h' : ρ < τ)
    (hx1 : |∑ c ∈ bondsWithin m, ∑ c' ∈ bondsWithin m, flatHessian S (bondFrom z c) (bondFrom z c') *
        (constantCurvaturePotential (planeUnitCurvature μ ν) c *
          constantCurvaturePotential (planeUnitCurvature ρ τ) c') -
        (if (μ, ν) = (ρ, τ) then 1 else 0)| ≤ C₁ * e₁)
    (hx2 : |∑ c ∈ bondsWithin m, ∑ c' ∈ bondsWithin m, flatHessian R (bondFrom z c) (bondFrom z c') *
        (constantCurvaturePotential (planeUnitCurvature μ ν) c *
          constantCurvaturePotential (planeUnitCurvature ρ τ) c')| ≤ C₂ * e₂) :
    |∑ p ∈ (plaquettesIn (Finset.univ : Finset (TorusSite n))).filter (fun p : TorusPlaquette n => p.2 = (μ, ν)),
        ∑ p' ∈ (plaquettesIn (Finset.univ : Finset (TorusSite n))).filter
          (fun p' : TorusPlaquette n => p'.2 = (ρ, τ)),
          curvatureKernel (curvedMark a b S R T) z m p p' - (if (μ, ν) = (ρ, τ) then b * a else 0)| ≤
      2 * (C₁ * e₁) + C₂ * e₂ + 16 * B * bondWeightSum (ℓ.weightRate / 4) 3 ^ 2 := by
  rw [curvatureKernel_plane_sum _ z m h h']
  set w : LatticeBond → LatticeBond → ℝ := fun c c' =>
    constantCurvaturePotential (planeUnitCurvature μ ν) c * constantCurvaturePotential (planeUnitCurvature ρ τ) c'
    with hw
  have hsplit : ∀ c c', flatHessian (curvedMark a b S R T) (bondFrom z c) (bondFrom z c') =
      a * (b * flatHessian S (bondFrom z c) (bondFrom z c') + flatHessian R (bondFrom z c) (bondFrom z c')) +
        flatHessian T (bondFrom z c) (bondFrom z c') := fun c c' => curvedMark_mixedDeriv (by norm_num) _ _ hS hR hT
  set X₁ := ∑ c ∈ bondsWithin m, ∑ c' ∈ bondsWithin m, flatHessian S (bondFrom z c) (bondFrom z c') * w c c' with hX₁
  set X₂ := ∑ c ∈ bondsWithin m, ∑ c' ∈ bondsWithin m, flatHessian R (bondFrom z c) (bondFrom z c') * w c c' with hX₂
  set X₃ := ∑ c ∈ bondsWithin m, ∑ c' ∈ bondsWithin m, flatHessian T (bondFrom z c) (bondFrom z c') * w c c' with hX₃
  have hsum : ∑ c ∈ bondsWithin m, ∑ c' ∈ bondsWithin m,
      flatHessian (curvedMark a b S R T) (bondFrom z c) (bondFrom z c') * w c c' = a * (b * X₁ + X₂) + X₃ := by
    simp only [hX₁, hX₂, hX₃, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
    rw [hsplit]
    ring
  rw [hsum]
  have hx3 : |X₃| ≤ 16 * B * bondWeightSum (ℓ.weightRate / 4) 3 ^ 2 :=
    abs_sum_against_potentials_le hB hr (abs_planeUnitCurvature_le μ ν) (abs_planeUnitCurvature_le ρ τ) hq
  set d : ℝ := if (μ, ν) = (ρ, τ) then 1 else 0 with hd
  have e : a * (b * X₁ + X₂) + X₃ - (if (μ, ν) = (ρ, τ) then b * a else 0) = a * b * (X₁ - d) + a * X₂ + X₃ := by
    by_cases hc : (μ, ν) = (ρ, τ)
    · simp only [hd, hc, if_true]
      ring
    · simp only [hd, hc, if_false]
      ring
  rw [e]
  have hab : |a * b| ≤ 2 := by
    rw [abs_mul]
    calc _ ≤ 1 * 2 := mul_le_mul ha hb (abs_nonneg _) zero_le_one
      _ = 2 := by norm_num
  have t1 : |a * b * (X₁ - d)| ≤ 2 * (C₁ * e₁) := by
    rw [abs_mul]
    exact mul_le_mul hab hx1 (abs_nonneg _) (by norm_num)
  have t2 : |a * X₂| ≤ C₂ * e₂ := by
    rw [abs_mul]
    calc _ ≤ 1 * (C₂ * e₂) := mul_le_mul ha hx2 (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  exact (abs_add_three _ _ _).trans (add_le_add (add_le_add t1 t2) hx3)
private theorem abs_three_terms_le {a b d₁ d₂ d₃ Ca Cr Ck q : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 2) (h1 : |d₁| ≤ Ca * q)
    (h2 : |d₂| ≤ Cr * q) (h3 : |d₃| ≤ Ck * q) : |a * (b * d₁ + d₂) + d₃| ≤ (2 * Ca + Cr + Ck) * q := by
  have t1 : |b * d₁| ≤ 2 * (Ca * q) := by
    rw [abs_mul]
    exact mul_le_mul hb h1 (abs_nonneg _) (by norm_num)
  have t2 : |b * d₁ + d₂| ≤ 2 * (Ca * q) + Cr * q := (abs_add_le _ _).trans (add_le_add t1 h2)
  have t3 : |a * (b * d₁ + d₂)| ≤ 1 * (2 * (Ca * q) + Cr * q) := by
    rw [abs_mul]
    exact mul_le_mul ha t2 (abs_nonneg _) zero_le_one
  refine (abs_add_le _ _).trans ((add_le_add t3 h3).trans (le_of_eq ?_))
  ring
private theorem weightLipschitz_nonneg_aux (L t : ℕ) {m : ℕ} (h : PlaquetteWeight m) : 0 ≤ weightLipschitz L t h := by apply _root_.YangMills.Construction.ResponseInTheExpansion.weightLipschitz_nonneg <;> assumption
private theorem curvatureAlong_antisymm {ζ : Fin 4 → Fin 4 → ℝ} (hz : ∀ i j, ζ i j = - ζ j i) (i j : Fin 4) :
    curvatureAlong FlatHessian.quaternionI ζ i j = - curvatureAlong FlatHessian.quaternionI ζ j i := by
  simp only [curvatureAlong]
  rw [hz i j]
  apply Subtype.ext
  simp
set_option maxHeartbeats 1600000 in
private theorem curvedFieldResponse_core {ℓ : StepParameters} {Kr : ResponseParameters} {Ca : ℝ}
    (hfit : ℓ.Admissible) (hKr : Kr.Admissible ℓ) (hCa : 0 ≤ Ca)
    (hsh : ∀ k, IsCurvatureFamily ℓ Ca (levelShareFamily ℓ.coupling ℓ.side k))
    (hsf : ∀ k, HasCurvatureForm (levelShareFamily ℓ.coupling ℓ.side k) 1)
    (hgauge : ∀ (β : ℝ) (k : ℕ) (al : ℕ → ℝ), IsChainResponseCoeff ℓ Kr β k al → ∀ (n : ℕ) [NeZero n], ℓ.n₀ ≤ n →
      ∀ (z : TorusSite n) (g : TorusSite n → UnitQuaternion) (W : TorusField n), IsCold ℓ.threshold W →
        ∀ h : PlaquetteWeight (fineSide ℓ.side k n),
          coldResponseChain ℓ β (flowCouplings ℓ β) al k n z (TorusFields.gaugeTransform g W) h =
            coldResponseChain ℓ β (flowCouplings ℓ β) al k n z W h)
    (hM : curvatureKernelExpansionStatement) (hF : boxFormStatement)
    (hWt : WeightsCloseToBlockMeans) :
    ∃ C c x₀ : ℝ, 0 < c ∧
    ∀ (β : ℝ) (k : ℕ) (al : ℕ → ℝ) (n : ℕ) [NeZero n],
      (∀ j ≤ k, ℓ.y₁ ≤ flowCouplings ℓ β j) → x₀ ≤ flowCouplings ℓ β k →
      IsChainResponseCoeff ℓ Kr β k al → |al k| ≤ 2 → ℓ.n₀ ≤ n →
      ∀ (z : TorusSite n) (h : PlaquetteWeight (fineSide ℓ.side k n)), weightSup h ≤ 1 →
        weightLipschitz ℓ.side k h ≤ 1 →
      ∃ κ : TorusPlaquette n → TorusPlaquette n → ℝ,
        (∀ p p', κ p p' = κ p' p) ∧
        (∀ p p', |κ p p'| ≤ C * Real.exp (-(c * max (_root_.YangMills.Construction.TorusFields.supDist p.1 z : ℝ) (_root_.YangMills.Construction.TorusFields.supDist p'.1 z : ℝ)))) ∧
        (∀ μ ν ρ τ : Fin 4, μ < ν → ρ < τ →
          |∑ p ∈ (plaquettesIn Finset.univ).filter (fun p : TorusPlaquette n => p.2 = (μ, ν)),
              ∑ p' ∈ (plaquettesIn Finset.univ).filter (fun p' : TorusPlaquette n => p'.2 = (ρ, τ)), κ p p' -
            (if (μ, ν) = (ρ, τ) then al k * blockMean ℓ.side k n z h else 0)| ≤
              C * (weightLipschitz ℓ.side k h + Real.exp (-(c * n)))) ∧
        ∀ (W : TorusField n) (g : TorusSite n → UnitQuaternion) (v : TorusBond n → imaginaryQuaternions) (ρ s t : ℝ),
          IsCold ℓ.threshold W →
          1 ≤ ρ → 4 * ρ + 4 ≤ n → 0 ≤ s → s ≤ 1 → 0 ≤ t → t ≤ 1 →
          (∀ b : TorusBond n, b.1 ∈ supBall z ρ → ‖(v b : Quaternion ℝ)‖ ≤ s ∧
            ‖(v b : Quaternion ℝ) - (minimalLog (ResponseInTheExpansion.gaugeTransform g W b) : Quaternion ℝ)‖ ≤ s ^ 2) →
          (∀ x ∈ supBall z ρ, ∀ μ ν : Fin 4, TorusFields.curvature W x μ ν ≤ t) →
          (∀ p ∈ plaquettesIn (supBall z ρ), ‖(lieFormCurl v p : Quaternion ℝ)‖ ≤ t) →
            |centeredResponse (coldResponseChain ℓ β (flowCouplings ℓ β) al k) n z W h -
                (1 / 2) * ∑ p ∈ plaquettesIn (supBall z ρ), ∑ p' ∈ plaquettesIn (supBall z ρ),
                  κ p p' * ∑ e : Fin 3, imaginaryComponent e (lieFormCurl v p) *
                    imaginaryComponent e (lieFormCurl v p')| ≤
              C * (t ^ 3 + t * s ^ 2 + Real.exp (-(c * ρ))) := by
  have hσ := hfit.σ_pos
  have hrate : 0 < ℓ.weightRate := by
    have := hfit.rt_pos
    unfold StepParameters.weightRate
    positivity
  have hη := hKr.η₃_pos
  have hη1 := hKr.η₃_le
  have hKa := hKr.Ka_nonneg
  have hKc : 0 ≤ Kr.Kc := by linarith [hKr.Kc_ge]
  obtain ⟨Cr, hCrd⟩ : ∃ Cr, Cr = Kr.Ka / Kr.η₃ := ⟨_, rfl⟩
  obtain ⟨Ck, hCkd⟩ : ∃ Ck, Ck = Kr.Kc / Kr.η₃ := ⟨_, rfl⟩
  have hCr : 0 ≤ Cr := by
    rw [hCrd]
    positivity
  have hCk : 0 ≤ Ck := by
    rw [hCkd]
    positivity
  have hKaCr : Kr.Ka ≤ Cr := by
    rw [hCrd]
    exact (le_div_iff₀ hη).2 (by nlinarith)
  have hKcCk : Kr.Kc ≤ Ck := by
    rw [hCkd]
    exact (le_div_iff₀ hη).2 (by nlinarith)
  obtain ⟨Eu, hEud⟩ : ∃ Eu, Eu = 2 * Ca + Cr + Ck := ⟨_, rfl⟩
  have hEu : 0 ≤ Eu := by
    rw [hEud]
    positivity
  obtain ⟨Cm, cm, hcm, hmk⟩ := hM ℓ.threshold Eu Eu ℓ.weightRate hσ hEu hEu hrate
  obtain ⟨C₁, c₁, hc₁, hf₁⟩ := hF ℓ hfit Ca hCa
  obtain ⟨C₂, c₂, hc₂, hf₂⟩ := hF ℓ hfit Cr hCr
  obtain ⟨S2, hS2⟩ : ∃ S2, S2 = bondWeightSum (ℓ.weightRate / 4) 3 ^ 2 := ⟨_, rfl⟩
  have hS20 : 0 ≤ S2 := by
    rw [hS2]
    positivity
  obtain ⟨Cf, hCf⟩ : ∃ Cf, Cf = |Cm| + 2 * |C₁| + |C₂| + 16 * Kr.Kc * S2 := ⟨_, rfl⟩
  obtain ⟨cf, hcf⟩ : ∃ cf, cf = min cm (min (c₁ / 8) (c₂ / 8)) := ⟨_, rfl⟩
  have hcf0 : 0 < cf := by
    rw [hcf]
    exact lt_min hcm (lt_min (by positivity) (by positivity))
  have hCf0 : 0 ≤ Cf := by
    rw [hCf]
    positivity
  refine ⟨Cf, cf, 1, hcf0, ?_⟩
  intro β k al n _ hy₁ hx hnum hal hn z h hsup hlip
  obtain ⟨Ra, Rb, hcl⟩ := hnum.bounds k le_rfl
  have hn16 : 16 ≤ n := by
    have := hfit.n₀_ge
    omega
  have hp1 : flowCouplings ℓ β k ^ (-(1 / 2) : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num)
  have hp0 : 0 ≤ flowCouplings ℓ β k ^ (-(1 / 2) : ℝ) := by
    have : 0 ≤ flowCouplings ℓ β k := by linarith
    positivity
  have hE1 : Kr.Ka * flowCouplings ℓ β k ^ (-(1 / 2) : ℝ) ≤ Kr.Ka := by nlinarith
  have hfam : IsCurvatureFamily ℓ Cr Ra := curvatureFamily_of_coldBounds hcl.site_family (hE1.trans hKaCr)
    (by
      rw [hCrd]
      exact div_le_div_of_nonneg_right hE1 hη.le) stepWeight_pos
  set P := coldResponseChain ℓ β (flowCouplings ℓ β) al k with hP
  set a := blockMean ℓ.side k n z h with ha
  have haabs : |a| ≤ 1 := ((hWt ℓ.side hfit.L_odd k n z).1 h).trans hsup
  set Sh : TorusField n → ℝ := levelShareFamily ℓ.coupling ℓ.side k n z with hSh
  set Rr : TorusField n → ℝ := Ra n z with hRr
  set Tr : TorusField n → ℝ := responseRemainder P n z h with hTr
  set U := curvedMark a (al k) Sh Rr Tr with hU
  have sS : ∀ W, IsCold ℓ.threshold W → ContDiffThreeAt Sh W := fun W hW => (hsh k).smooth n hn z W hW
  have sR : ∀ W, IsCold ℓ.threshold W → ContDiffThreeAt Rr W := fun W hW => hfam.smooth n hn z W hW
  have sT : ∀ W, IsCold ℓ.threshold W → ContDiffThreeAt Tr W := fun W hW => hcl.remainder.smooth n hn z W hW h
  have gT : ∀ (g : TorusSite n → UnitQuaternion) W, IsCold ℓ.threshold W →
      Tr (TorusFields.gaugeTransform g W) = Tr W := by
    intro g W hW
    simp only [hTr, responseRemainder, hP]
    rw [hgauge β k al hnum n hn z g W hW h, hgauge β k al hnum n hn z g W hW (constOneWeight _)]
  have dT : ∀ W, IsCold ℓ.threshold W → ∀ (j : ℕ) (c : Fin j → TorusBond n) (X : Fin j → imaginaryQuaternions),
      1 ≤ j → j ≤ 3 → AreUnitVectors X → |mixedDeriv Tr W c X| ≤ Ck / ℓ.weight (supportDiam z c) := by
    intro W hW j c X h1 h3 hX
    refine (hcl.remainder.decay n hn z W hW h j c X h1 h3 hX).trans
      (div_le_div_of_nonneg_right ?_ (stepWeight_pos _).le)
    have hb : (if j = 3 then Kr.Kc / Kr.η₃ else Kr.Kc) ≤ Ck := by
      split_ifs
      · exact hCkd.symm.le
      · exact hKcCk
    have hb0 : 0 ≤ (if j = 3 then Kr.Kc / Kr.η₃ else Kr.Kc) := by
      split_ifs <;> positivity
    calc _ ≤ (if j = 3 then Kr.Kc / Kr.η₃ else Kr.Kc) * 1 := mul_le_mul_of_nonneg_left hlip hb0
      _ ≤ Ck := by linarith
  have hfun : IsRegularObservable ℓ.threshold Eu Eu ℓ.weight z U := by
    rw [hEud]
    exact curvedMark_isRegularObservable hCa hCr hCk haabs hal sS sR sT
      (fun g W hW => (hsh k).gauge n hn z g W hW)
      (fun g W hW => hfam.gauge n hn z g W hW) gT
      (fun W hW j c X h1 h3 hX => (hsh k).decay n hn z W hW j c X h1 h3 hX)
      (fun W hW j c X h1 h3 hX => hfam.decay n hn z W hW j c X h1 h3 hX) dT
  have hcomp : ∀ (W W' : TorusField n) (m : ℕ), IsCold ℓ.threshold W → IsCold ℓ.threshold W' → 2 * m + 2 < n →
      FieldsAgreeNear W W' z z m → |U W - U W'| ≤ Eu / ℓ.weight m := by
    intro W W' m hW hW' h2 hag
    have e1 := (hsh k).local_density n n hn hn z z W W' m h2 h2 hW hW' hag 0 (fun i => i.elim0) (fun i => i.elim0)
      (Nat.zero_le _) (fun l => l.elim0) (fun l => l.elim0)
    have e2 := hfam.local_density n n hn hn z z W W' m h2 h2 hW hW' hag 0 (fun i => i.elim0) (fun i => i.elim0)
      (Nat.zero_le _) (fun l => l.elim0) (fun l => l.elim0)
    have e3 := hcl.remainder.compare n hn z W W' m h2 hW hW' hag h 0 (fun i => i.elim0) (fun i => i.elim0)
      (Nat.zero_le _) (fun l => l.elim0) (fun l => l.elim0)
    simp only [mixedDeriv_fin_zero, centered, centeredRemainder] at e1 e2 e3
    have d1 : |Sh W - Sh W'| ≤ Ca * (ℓ.weight m)⁻¹ := by
      rw [← div_eq_mul_inv]
      refine le_trans (le_of_eq ?_) e1
      congr 1
      simp only [hSh]
      ring
    have d2 : |Rr W - Rr W'| ≤ Cr * (ℓ.weight m)⁻¹ := by
      rw [← div_eq_mul_inv]
      refine le_trans (le_of_eq ?_) e2
      congr 1
      simp only [hRr]
      ring
    have d3 : |Tr W - Tr W'| ≤ Ck * (ℓ.weight m)⁻¹ := by
      rw [← div_eq_mul_inv]
      have hk : Kr.Kc * weightLipschitz ℓ.side k h ≤ Ck := by
        calc _ ≤ Kr.Kc * 1 := mul_le_mul_of_nonneg_left hlip hKc
          _ ≤ Ck := by linarith
      refine le_trans (le_of_eq ?_) (e3.trans (div_le_div_of_nonneg_right hk (stepWeight_pos _).le))
      congr 1
      simp only [hTr, hP]
      ring
    have e : U W - U W' = a * (al k * (Sh W - Sh W') + (Rr W - Rr W')) + (Tr W - Tr W') := by
      simp only [hU, curvedMark]
      ring
    rw [e, hEud, div_eq_mul_inv]
    exact abs_three_terms_le haabs hal d1 d2 d3
  obtain ⟨hsym, hdec, hexp⟩ := hmk n z ℓ.weight U hn16 (exp_le_stepWeight ℓ) hfun hcomp
  have hflat : IsCold ℓ.threshold (trivialField n) := fun x μ ν _ => by
    simpa [TorusFields.curvature, holonomy, trivialField] using hσ
  have hCmCf : Cm ≤ Cf := by
    rw [hCf]
    have := le_abs_self Cm
    have : 0 ≤ 2 * |C₁| + |C₂| + 16 * Kr.Kc * S2 := by positivity
    linarith [le_abs_self Cm]
  have hcfm : cf ≤ cm := by
    rw [hcf]
    exact min_le_left _ _
  have hcf1 : cf ≤ c₁ / 8 := by
    rw [hcf]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hcf2 : cf ≤ c₂ / 8 := by
    rw [hcf]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hexpmono : ∀ x : ℝ, 0 ≤ x → Real.exp (-(cm * x)) ≤ Real.exp (-(cf * x)) := fun x hx0 =>
    Real.exp_le_exp.mpr (by nlinarith)
  refine ⟨curvatureKernel U z (n / 4), hsym, ?_, ?_, ?_⟩
  · intro p p'
    refine (hdec p p').trans ?_
    have hx0 : 0 ≤ max (_root_.YangMills.Construction.TorusFields.supDist p.1 z : ℝ) (_root_.YangMills.Construction.TorusFields.supDist p'.1 z : ℝ) := le_max_of_le_left (Nat.cast_nonneg _)
    exact mul_le_mul hCmCf (hexpmono _ hx0) (Real.exp_pos _).le hCf0
  · intro μ ν ρ τ h1 h2
    have hm2 : 2 * (n / 4 + 1) + 2 < n := by omega
    have hB : 0 ≤ Kr.Kc * weightLipschitz ℓ.side k h := mul_nonneg hKc (weightLipschitz_nonneg_aux _ _ _)
    have hq : ∀ c ∈ bondsWithin (n / 4), ∀ c' ∈ bondsWithin (n / 4),
        |flatHessian Tr (bondFrom z c) (bondFrom z c')| ≤
          Kr.Kc * weightLipschitz ℓ.side k h *
            Real.exp (-(ℓ.weightRate * max (offsetSupNorm c.1 : ℝ) (offsetSupNorm c'.1 : ℝ))) := by
      intro c hc c' hc'
      have s1 := mem_bondsWithin_iff.1 hc
      have s2 := mem_bondsWithin_iff.1 hc'
      have hd := hcl.remainder.decay n hn z (trivialField n) hflat h 2 ![bondFrom z c, bondFrom z c']
        ![FlatHessian.quaternionI, FlatHessian.quaternionI] (by norm_num) (by norm_num) (fun l => by
          have h3 : Quaternion.normSq ((FlatHessian.quaternionI : imaginaryQuaternions) : ℍ[ℝ]) = 1 := by
            rw [Quaternion.normSq_def']
            simp [FlatHessian.quaternionI]
          have h4 : ‖((FlatHessian.quaternionI : imaginaryQuaternions) : ℍ[ℝ])‖ *
              ‖((FlatHessian.quaternionI : imaginaryQuaternions) : ℍ[ℝ])‖ = 1 := by
            rw [← Quaternion.normSq_eq_norm_mul_self, h3]
          have h5 : ‖((FlatHessian.quaternionI : imaginaryQuaternions) : ℍ[ℝ])‖ = 1 := by
            nlinarith [norm_nonneg ((FlatHessian.quaternionI : imaginaryQuaternions) : ℍ[ℝ])]
          fin_cases l <;> exact h5)
      simp only [show ¬ (2 = 3) by norm_num, if_false] at hd
      refine hd.trans ?_
      rw [div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_left ?_ hB
      rw [Real.exp_neg]
      refine inv_anti₀ (Real.exp_pos _) ((Real.exp_le_exp.mpr ?_).trans (exp_le_stepWeight ℓ _))
      exact mul_le_mul_of_nonneg_left (offsetSupNorm_max_le_supportDiam (by omega) (by omega)) hrate.le
    have hx1 := hf₁ _ (hsh k) (planeUnitCurvature μ ν) (planeUnitCurvature ρ τ) (planeUnitCurvature_antisymm h1)
      (planeUnitCurvature_antisymm h2) (abs_planeUnitCurvature_le _ _) (abs_planeUnitCurvature_le _ _) n z (n / 4) hn hm2
    have hx2 := hf₂ _ hfam (planeUnitCurvature μ ν) (planeUnitCurvature ρ τ) (planeUnitCurvature_antisymm h1)
      (planeUnitCurvature_antisymm h2) (abs_planeUnitCurvature_le _ _) (abs_planeUnitCurvature_le _ _) n z (n / 4) hn hm2
    have v1 : ∑' cc, limitFormTerm (levelShareFamily ℓ.coupling ℓ.side k)
        (curvatureAlong FlatHessian.quaternionI (planeUnitCurvature μ ν))
        (curvatureAlong FlatHessian.quaternionI (planeUnitCurvature ρ τ)) cc = if (μ, ν) = (ρ, τ) then 1 else 0 := by
      rw [((hsf k).2 _ _ (curvatureAlong_antisymm (planeUnitCurvature_antisymm h1))
        (curvatureAlong_antisymm (planeUnitCurvature_antisymm h2))).tsum_eq, one_mul, curvaturePairing_planes h1 h2]
    have v2 : ∑' cc, limitFormTerm Ra (curvatureAlong FlatHessian.quaternionI (planeUnitCurvature μ ν))
        (curvatureAlong FlatHessian.quaternionI (planeUnitCurvature ρ τ)) cc = 0 :=
      hcl.site_family.no_curvature_term _ _ (curvatureAlong_antisymm (planeUnitCurvature_antisymm h1))
        (curvatureAlong_antisymm (planeUnitCurvature_antisymm h2))
    rw [v1] at hx1
    rw [v2, sub_zero] at hx2
    have hpb := abs_curvedMark_planes_le (ℓ := ℓ) (a := a) (b := al k) (S := Sh) (R := Rr) (T := Tr) (z := z)
      (m := n / 4) hrate hB haabs hal (Real.exp_pos _).le (Real.exp_pos _).le (sS _ hflat) (sR _ hflat) (sT _ hflat)
      hq h1 h2 hx1 hx2
    refine hpb.trans ?_
    rw [← hS2]
    have hnr : (n : ℝ) ≤ 8 * ((n / 4 : ℕ) : ℝ) := by
      have : n ≤ 8 * (n / 4) := by omega
      exact_mod_cast this
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have b1 : Real.exp (-(c₁ * ((n / 4 : ℕ) : ℝ))) ≤ Real.exp (-(cf * n)) := Real.exp_le_exp.mpr (by nlinarith)
    have b2 : Real.exp (-(c₂ * ((n / 4 : ℕ) : ℝ))) ≤ Real.exp (-(cf * n)) := Real.exp_le_exp.mpr (by nlinarith)
    set E := Real.exp (-(cf * n)) with hE
    have hE0 : 0 ≤ E := (Real.exp_pos _).le
    have t1 : C₁ * Real.exp (-(c₁ * ((n / 4 : ℕ) : ℝ))) ≤ |C₁| * E :=
      (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le).trans
        (mul_le_mul_of_nonneg_left b1 (abs_nonneg _))
    have t2 : C₂ * Real.exp (-(c₂ * ((n / 4 : ℕ) : ℝ))) ≤ |C₂| * E :=
      (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le).trans
        (mul_le_mul_of_nonneg_left b2 (abs_nonneg _))
    have hl0 := weightLipschitz_nonneg_aux ℓ.side k h
    have hCE : (2 * |C₁| + |C₂|) * E ≤ Cf * E := by
      refine mul_le_mul_of_nonneg_right ?_ hE0
      rw [hCf]
      have : 0 ≤ |Cm| + 16 * Kr.Kc * S2 := by positivity
      linarith
    have hCl : 16 * Kr.Kc * S2 * weightLipschitz ℓ.side k h ≤ Cf * weightLipschitz ℓ.side k h := by
      refine mul_le_mul_of_nonneg_right ?_ hl0
      rw [hCf]
      have : 0 ≤ |Cm| + 2 * |C₁| + |C₂| := by positivity
      linarith
    have e1 : 16 * (Kr.Kc * weightLipschitz ℓ.side k h) * S2 = 16 * Kr.Kc * S2 * weightLipschitz ℓ.side k h := by ring
    have e2 : Cf * (weightLipschitz ℓ.side k h + E) = Cf * weightLipschitz ℓ.side k h + Cf * E := by ring
    have e3 : (2 * |C₁| + |C₂|) * E = 2 * (|C₁| * E) + |C₂| * E := by ring
    rw [e1, e2]
    linarith
  · intro W g v ρ s t hW h1 h2 hs0 hs1 ht0 ht1 hform hcurv hcurl
    have hb : IsSmallOnBall W g v z ρ s t := ⟨hform, hcurv, hcurl⟩
    have hE := hexp W g v ρ s t hW h1 h2 hs0 hs1 ht0 ht1 hb
    have hid : centeredResponse P n z W h = U W - U (trivialField n) := by
      have s1 := hcl.share_site n hn z W hW
      have s0 := hcl.share_site n hn z (trivialField n) hflat
      have shf : ∀ V : TorusField n, Sh V = levelShare ℓ.coupling ℓ.side k Finset.univ z V := fun V => by
        simp only [hSh, levelShareFamily, dif_neg (NeZero.ne n)]
      simp only [centeredResponse, centered, sub_self, ← hP] at s1 s0
      rw [← shf] at s1 s0
      simp only [← hRr] at s1 s0
      simp only [centeredResponse, hU, curvedMark, hTr, responseRemainder, ← ha]
      have s0' : al k * Sh (trivialField n) = 0 := by linarith
      linear_combination a * s1 + a * s0'
    rw [hid]
    refine hE.trans ?_
    have hexp0 : 0 ≤ t ^ 3 + t * s ^ 2 := by positivity
    have hρ0 : 0 ≤ ρ := by linarith
    have h3 : t ^ 3 + t * s ^ 2 + Real.exp (-(cm * ρ)) ≤ t ^ 3 + t * s ^ 2 + Real.exp (-(cf * ρ)) := by
      linarith [hexpmono ρ hρ0]
    have h4 : 0 ≤ t ^ 3 + t * s ^ 2 + Real.exp (-(cm * ρ)) := by positivity
    exact mul_le_mul hCmCf h3 h4 hCf0
theorem curvedFieldResponseStatement_holds (hM : curvatureKernelExpansionStatement) (hF : boxFormStatement)
    (hG : coldResponseGaugeInvariantStatement) (hWs : WilsonSharesFormCurvatureFamily)
    (hSh : LevelSharesFormCurvatureFamily) (hFo : LevelSharesHaveUnitCurvatureForm)
    (hWt : WeightsCloseToBlockMeans) :
    curvedFieldResponseStatement := by
  intro a ha
  refine ⟨0, fun _ => 1, 0, fun _ => one_pos, fun L hL hL' T e1 e2 hD hCS hOn hrt hCd => ?_⟩
  refine ⟨T.floorMin, fun y hy₀ hR hWil => ?_⟩
  have hfit : (T.stepParameters y).Admissible := hD.fits y hy₀
  intro Kr hKr
  obtain ⟨Cw, hCw, hfam0, hform0⟩ := hWs (T.stepParameters y) hfit
  obtain ⟨Cb, hCb⟩ : ∃ Cb, Cb = weightGrowthSup T.rt T.n₁ * maxOfFirstFour T.N := ⟨_, rfl⟩
  have hmax0 : 0 ≤ max Cb Cw := hCw.trans (le_max_right _ _)
  have hsh : ∀ k, IsCurvatureFamily (T.stepParameters y) (max Cb Cw)
      (levelShareFamily (T.stepParameters y).coupling (T.stepParameters y).side k) := by
    intro k
    cases k with
    | zero => exact curvatureFamily_mono hfam0 (le_max_right _ _) stepWeight_pos
    | succ t =>
      have h1 := (hSh T hD y hy₀ t).1
      rw [← hCb] at h1
      exact curvatureFamily_mono h1 (le_max_left _ _) stepWeight_pos
  have hsf : ∀ k, HasCurvatureForm (levelShareFamily (T.stepParameters y).coupling (T.stepParameters y).side k) 1 := by
    intro k
    cases k with
    | zero => exact hform0
    | succ t => exact hFo T hD t
  exact curvedFieldResponse_core hfit hKr hmax0 hsh hsf
    (fun β k al _ n _ _ z g W _ h => hG (T.stepParameters y) hfit β (flowCouplings (T.stepParameters y) β) al k n z g W h)
    hM hF hWt
end YangMills.Construction.StateLaws
end
