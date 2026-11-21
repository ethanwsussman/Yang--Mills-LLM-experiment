import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
import YangMills.Construction.ColdChainAtEveryLevel.PotentialsInAPatch
import YangMills.Construction.ClusterExpansionOfAStep.MatchingClasses
import YangMills.Construction.ClusterExpansionOfAStep.PlaquettesUnderGaugesAndMoves
import YangMills.Construction.FormsOnATorus.ColumnOfTheLimitFormProof
import YangMills.Construction.LawOnABoxOfTheFlow.BoundsOfTheCurlKernel
import YangMills.Construction.LawOnABoxOfTheFlow.BoundsOnTheEllipsoid
import YangMills.Construction.LawOnABoxOfTheFlow.FormOfACube
import YangMills.Construction.LawOnABoxOfTheFlow.GapOfTheCoveredGradient
import YangMills.Construction.LawOnABoxOfTheFlow.InteriorRegularity
import YangMills.Construction.LawOnABoxOfTheFlow.KernelOfTheCurlOnABox
import YangMills.Construction.LawOnABoxOfTheFlow.LimitFormOfTheCube
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.BoxGaussian
open YangMills.Construction.TorusFields YangMills.Construction.TorusLumps YangMills.Construction.LimitForms
open YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.BlockAverages hiding unitStep adjointAction
open YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.RenormalizationStepParameters
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
variable {n : ℕ} [NeZero n]
private def liftReal (f : TorusBond n → ℝ) : TorusBond n → imaginaryQuaternions := fun b => f b • imaginaryUnitI
private def hessEntry (a : ℝ) (L k : ℕ) (S : Finset (TorusSite n)) (b b' : TorusBond n) : ℝ :=
  mixedDeriv (actionAtLevel a L k S) (trivialField n) ![b, b'] ![imaginaryUnitI, imaginaryUnitI]
private def realHess (a : ℝ) (L k : ℕ) (S : Finset (TorusSite n)) (u v : TorusBond n → ℝ) : ℝ :=
  ∑ b : TorusBond n, ∑ b' : TorusBond n, hessEntry a L k S b b' * u b * v b'
private def realCurl (f : TorusBond n → ℝ) (p : TorusPlaquette n) : ℝ :=
  f (p.1, p.2.1) + f (p.1 + unitStep n p.2.1, p.2.2) - f (p.1 + unitStep n p.2.2, p.2.1) - f (p.1, p.2.2)
private theorem component_unitI (e : Fin 3) : imaginaryComponent e imaginaryUnitI = if e = 0 then 1 else 0 := by
  fin_cases e <;> simp [imaginaryComponent, imaginaryUnitI]
private theorem component_smul (e : Fin 3) (c : ℝ) (w : imaginaryQuaternions) :
    imaginaryComponent e (c • w) = c * imaginaryComponent e w := by
  fin_cases e <;> simp [imaginaryComponent]
private theorem norm_unitI : ‖imaginaryUnitI‖ = 1 := by
  have h : ‖(imaginaryUnitI : imaginaryQuaternions)‖ = ‖((imaginaryUnitI : imaginaryQuaternions) : ℍ[ℝ])‖ := rfl
  have h2 : ‖((imaginaryUnitI : imaginaryQuaternions) : ℍ[ℝ])‖ * ‖((imaginaryUnitI : imaginaryQuaternions) : ℍ[ℝ])‖ = 1 := by
    rw [← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
    simp [imaginaryUnitI]
  rw [h]
  nlinarith [norm_nonneg ((imaginaryUnitI : imaginaryQuaternions) : ℍ[ℝ])]
abbrev _root_.YangMills.SharedProofs.p16675 := @norm_unitI
private theorem abs_component_le_norm (w : imaginaryQuaternions) : |imaginaryComponent 0 w| ≤ ‖w‖ := by
  have h : ‖w‖ = ‖(w : ℍ[ℝ])‖ := rfl
  have h2 : |(w : ℍ[ℝ]).imI| ≤ ‖(w : ℍ[ℝ])‖ := by
    have h3 := Quaternion.normSq_eq_norm_mul_self (w : ℍ[ℝ])
    rw [Quaternion.normSq_def'] at h3
    apply abs_le_of_sq_le_sq _ (norm_nonneg _)
    nlinarith [sq_nonneg (w : ℍ[ℝ]).re, sq_nonneg (w : ℍ[ℝ]).imJ, sq_nonneg (w : ℍ[ℝ]).imK]
  simpa [imaginaryComponent, h] using h2
private theorem sum_curlCoeff_mul (p : TorusPlaquette n) (f : TorusBond n → ℝ) :
    ∑ b : TorusBond n, curlCoeff p b * f b = realCurl f p := by
  classical
  simp only [curlCoeff, realCurl, add_mul, sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
private theorem sum_gradCoeff_mul (f : TorusSite n → ℝ) (b : TorusBond n) :
    ∑ z : TorusSite n, gradCoeff z b * f z = f b.1 - f (b.1 + unitStep n b.2) := by
  classical
  simp only [gradCoeff, sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
abbrev _root_.YangMills.SharedProofs.p55520 := @sum_gradCoeff_mul
private theorem sum_touching {o : TorusSite n} {R : ℕ} (g : TorusBond n → ℝ)
    (hg : ∀ b, b ∉ bondsTouching o R → g b = 0) :
    ∑ b : TouchingBond o R, g b.1 = ∑ b : TorusBond n, g b := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ (bondsTouching o R)) (fun b _ hb => hg b hb)]
  exact Finset.sum_coe_sort (bondsTouching o R) g
private theorem adjointAction_expUnit_zero (X : imaginaryQuaternions) : adjointAction (expUnit 0) X = X := by
  have h := expUnit_zero
  rw [h]
  ext <;> simp [adjointAction]
private theorem covariantGrad_zero (χ : TorusSite n → imaginaryQuaternions) (b : TorusBond n) :
    covariantGrad (0 : TorusBond n → imaginaryQuaternions) χ b = latticeGrad χ b := by
  simp [covariantGrad, latticeGrad, adjointAction_expUnit_zero]
private theorem hessianForm_liftReal {a : ℝ} {L k : ℕ} {S : Finset (TorusSite n)}
    (hcol : ∀ u v : TorusBond n → imaginaryQuaternions, hessianForm a L k S u v =
      ∑ e : Fin 3, ∑ b : TorusBond n, ∑ b' : TorusBond n,
        hessEntry a L k S b b' * imaginaryComponent e (u b) * imaginaryComponent e (v b'))
    (f : TorusBond n → ℝ) (η : TorusBond n → imaginaryQuaternions) :
    hessianForm a L k S (liftReal f) η = realHess a L k S f (fun b => imaginaryComponent 0 (η b)) := by
  rw [hcol, Fin.sum_univ_three]
  simp [liftReal, component_smul, component_unitI, realHess]
private theorem component_liftReal (f : TorusBond n → ℝ) (b : TorusBond n) :
    imaginaryComponent 0 (liftReal f b) = f b := by
  simp [liftReal, component_smul, component_unitI]
open Classical in
private def boxGreenColumn (a : ℝ) (L k : ℕ) (o : TorusSite n) (R : ℕ) (p' : TorusPlaquette n) (b : TorusBond n) : ℝ :=
  if h : b ∈ bondsTouching o R then
    ((regularizedHessian a L k o R)⁻¹.mulVec (fun b' : TouchingBond o R => curlCoeff p' b'.1)) ⟨b, h⟩ else 0
private theorem boxGreenColumn_of_not_mem {a : ℝ} {L k : ℕ} {o : TorusSite n} {R : ℕ} {p' : TorusPlaquette n}
    {b : TorusBond n} (h : b ∉ bondsTouching o R) : boxGreenColumn a L k o R p' b = 0 := by
  simp [boxGreenColumn, h]
private theorem curlCovariance_eq_realCurl {a : ℝ} {L k : ℕ} {o : TorusSite n} {R : ℕ} (p p' : TorusPlaquette n) :
    curlCovariance a L k o R p p' = realCurl (boxGreenColumn a L k o R p') p := by
  classical
  rw [← sum_curlCoeff_mul, ← sum_touching (o := o) (R := R)]
  · unfold curlCovariance
    refine Finset.sum_congr rfl fun b _ => ?_
    have hb : boxGreenColumn a L k o R p' b.1 =
        ((regularizedHessian a L k o R)⁻¹.mulVec (fun b' : TouchingBond o R => curlCoeff p' b'.1)) b := by
      simp [boxGreenColumn, b.2]
    rw [hb, Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b' _ => ?_
    ring
  · intro b hb
    rw [boxGreenColumn_of_not_mem hb, mul_zero]
private def boxDivergence (o : TorusSite n) (R : ℕ) (B : TorusBond n → ℝ) (z : TorusSite n) : ℝ :=
  open Classical in if z ∈ supBall o R then ∑ b : TorusBond n, gradCoeff z b * B b else 0
private theorem boxGreenColumn_equation {a : ℝ} {L k : ℕ} {o : TorusSite n} {R : ℕ} {p' : TorusPlaquette n}
    (hdet : IsUnit (regularizedHessian a L k o R).det) (b : TorusBond n) (hb : b ∈ bondsTouching o R) :
    ∑ b' : TorusBond n, hessEntry a L k (supBall o (2 * R)) b b' * boxGreenColumn a L k o R p' b' +
      (boxDivergence o R (boxGreenColumn a L k o R p') b.1 -
        boxDivergence o R (boxGreenColumn a L k o R p') (b.1 + unitStep n b.2)) =
      curlCoeff p' b := by
  classical
  set B := boxGreenColumn a L k o R p' with hB
  set c : TouchingBond o R → ℝ := fun b' => curlCoeff p' b'.1 with hc
  have hM : (regularizedHessian a L k o R).mulVec ((regularizedHessian a L k o R)⁻¹.mulVec c) = c := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hx : ∀ b' : TouchingBond o R, (regularizedHessian a L k o R)⁻¹.mulVec c b' = B b'.1 := by
    intro b'
    simp [hB, boxGreenColumn, b'.2, hc]
  have h1 := congrFun hM ⟨b, hb⟩
  simp only [Matrix.mulVec, dotProduct] at h1
  have h2 : ∑ b' : TouchingBond o R, regularizedHessian a L k o R ⟨b, hb⟩ b' * B b'.1 = c ⟨b, hb⟩ := by
    rw [← h1]
    refine Finset.sum_congr rfl fun b' _ => ?_
    rw [← hx]
    rfl
  have hoff : ∀ b', b' ∉ bondsTouching o R → B b' = 0 := fun b' h => boxGreenColumn_of_not_mem h
  have h3 : ∑ b' : TouchingBond o R, regularizedHessian a L k o R ⟨b, hb⟩ b' * B b'.1 =
      ∑ b' : TorusBond n, hessEntry a L k (supBall o (2 * R)) b b' * B b' +
        ∑ z ∈ supBall o R, gradCoeff z b * ∑ b' : TorusBond n, gradCoeff z b' * B b' := by
    have e1 : ∑ b' : TouchingBond o R, regularizedHessian a L k o R ⟨b, hb⟩ b' * B b'.1 =
        ∑ b' : TouchingBond o R, (hessEntry a L k (supBall o (2 * R)) b b'.1 * B b'.1 +
          ∑ z ∈ supBall o R, gradCoeff z b * (gradCoeff z b'.1 * B b'.1)) := by
      refine Finset.sum_congr rfl fun b' _ => ?_
      simp only [regularizedHessian, hessEntry, add_mul, Finset.sum_mul, mul_assoc]
    rw [e1, Finset.sum_add_distrib,
      sum_touching (fun b' => hessEntry a L k (supBall o (2 * R)) b b' * B b') (fun b' h => by simp [hoff b' h]),
      Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.mul_sum, ← sum_touching (o := o) (R := R)]
    intro b' h
    simp [hoff b' h]
  have h4 : ∑ z ∈ supBall o R, gradCoeff z b * ∑ b' : TorusBond n, gradCoeff z b' * B b' =
      boxDivergence o R B b.1 - boxDivergence o R B (b.1 + unitStep n b.2) := by
    rw [← sum_gradCoeff_mul (boxDivergence o R B) b]
    rw [← Finset.sum_subset (Finset.subset_univ (supBall o R))]
    · refine Finset.sum_congr rfl fun z hz => ?_
      simp [boxDivergence, hz]
    · intro z _ hz
      simp [boxDivergence, hz]
  rw [h4] at h3
  rw [← h3, h2]
private theorem mem_supBall {o z : TorusSite n} {r : ℝ} : z ∈ supBall o r ↔ (supDist z o : ℝ) ≤ r := by
  simp [supBall]
private theorem supDist_add_unitStep_le_succ (x o : TorusSite n) (i : Fin 4) :
    supDist (x + unitStep n i) o ≤ supDist x o + 1 := by
  have h1 := supDist_triangle (x + unitStep n i) x o
  have h2 := supDist_add_unitStep_le x i
  rw [supDist_comm] at h2
  omega
abbrev _root_.YangMills.SharedProofs.p13239 := @supDist_add_unitStep_le_succ
private theorem supDist_le_add_unitStep_succ (x o : TorusSite n) (i : Fin 4) :
    supDist x o ≤ supDist (x + unitStep n i) o + 1 := by
  have h1 := supDist_triangle x (x + unitStep n i) o
  have h2 := supDist_add_unitStep_le x i
  omega
abbrev _root_.YangMills.SharedProofs.p7518 := @supDist_le_add_unitStep_succ
private theorem touching_near {o : TorusSite n} {R : ℕ} {b : TorusBond n} (hb : b ∈ bondsTouching o R) :
    supDist b.1 o ≤ R + 1 ∧ supDist (b.1 + unitStep n b.2) o ≤ R + 1 := by
  have h1 := supDist_add_unitStep_le_succ b.1 o b.2
  have h2 := supDist_le_add_unitStep_succ b.1 o b.2
  simp only [bondsTouching, Finset.mem_filter, Finset.mem_univ, true_and, mem_supBall] at hb
  rcases hb with hb | hb
  · have : supDist b.1 o ≤ R := by exact_mod_cast hb
    omega
  · have : supDist (b.1 + unitStep n b.2) o ≤ R := by exact_mod_cast hb
    omega
private theorem touching_mem_bondsWithin {o : TorusSite n} {R : ℕ} (hR : 1 ≤ R) {b : TorusBond n}
    (hb : b ∈ bondsTouching o R) : b ∈ bondsWithin (supBall o (2 * (R : ℝ))) := by
  obtain ⟨h1, h2⟩ := touching_near hb
  have hR' : (1 : ℝ) ≤ R := by exact_mod_cast hR
  simp only [bondsWithin, Finset.mem_filter, Finset.mem_univ, true_and, mem_supBall]
  have h3 : (supDist b.1 o : ℝ) ≤ R + 1 := by exact_mod_cast h1
  have h4 : (supDist (b.1 + unitStep n b.2) o : ℝ) ≤ R + 1 := by exact_mod_cast h2
  constructor <;> linarith
abbrev _root_.YangMills.SharedProofs.p15112 := @touching_mem_bondsWithin
private theorem realHess_grad_left {a : ℝ} {L k : ℕ} {S : Finset (TorusSite n)}
    (hcol : ∀ u v : TorusBond n → imaginaryQuaternions, hessianForm a L k S u v =
      ∑ e : Fin 3, ∑ b : TorusBond n, ∑ b' : TorusBond n,
        hessEntry a L k S b b' * imaginaryComponent e (u b) * imaginaryComponent e (v b'))
    (hblind : ∀ (φ : TorusSite n → imaginaryQuaternions) (v : TorusBond n → imaginaryQuaternions),
      hessianForm a L k S (latticeGrad φ) v = 0)
    (φ : TorusSite n → ℝ) (v : TorusBond n → ℝ) :
    realHess a L k S (fun b => φ b.1 - φ (b.1 + unitStep n b.2)) v = 0 := by
  have h1 := hblind (fun z => φ z • imaginaryUnitI) (liftReal v)
  have h2 : latticeGrad (fun z => φ z • imaginaryUnitI) =
      liftReal (fun b : TorusBond n => φ b.1 - φ (b.1 + unitStep n b.2)) := by
    funext b
    simp only [latticeGrad, liftReal]
    exact (sub_smul _ _ _).symm
  rw [h2, hessianForm_liftReal hcol] at h1
  simpa [component_liftReal] using h1
private theorem realCurl_grad (φ : TorusSite n → ℝ) (p : TorusPlaquette n) :
    realCurl (fun b => φ b.1 - φ (b.1 + unitStep n b.2)) p = 0 := by
  simp only [realCurl]
  have : p.1 + unitStep n p.2.1 + unitStep n p.2.2 = p.1 + unitStep n p.2.2 + unitStep n p.2.1 := by abel
  rw [this]
  ring
private theorem boxGreenColumn_spec {a cK : ℝ} {L k : ℕ} {o : TorusSite n} {R : ℕ} (p' : TorusPlaquette n)
    (hR : 1 ≤ R) (hcK : 0 < cK)
    (hcol : ∀ u v : TorusBond n → imaginaryQuaternions, hessianForm a L k (supBall o (2 * R)) u v =
      ∑ e : Fin 3, ∑ b : TorusBond n, ∑ b' : TorusBond n,
        hessEntry a L k (supBall o (2 * R)) b b' * imaginaryComponent e (u b) * imaginaryComponent e (v b'))
    (hblind : ∀ (φ : TorusSite n → imaginaryQuaternions) (v : TorusBond n → imaginaryQuaternions),
      hessianForm a L k (supBall o (2 * R)) (latticeGrad φ) v = 0)
    (hdet : IsUnit (regularizedHessian a L k o R).det)
    (hgap : ∀ χ : TorusSite n → imaginaryQuaternions, (∀ z, z ∉ supBall o R → χ z = 0) →
      4 * ((R : ℝ) + 1)⁻¹ ^ 2 * ∑ z : TorusSite n, ‖χ z‖ ^ 2 ≤
        ∑ b : TorusBond n, ‖covariantGrad (0 : TorusBond n → imaginaryQuaternions) χ b‖ ^ 2)
    (hslice : ∀ ζ ∈ gaugeSlice o R (0 : TorusBond n → imaginaryQuaternions),
      2 * cK * ((R : ℝ) ^ 2)⁻¹ * bondNormSq (supBall o (2 * R)) ζ ≤
        hessianForm a L k (supBall o (2 * R)) ζ ζ) :
    (∀ η : TorusBond n → ℝ, (∀ b, b ∉ bondsTouching o R → η b = 0) →
      realHess a L k (supBall o (2 * R)) η (boxGreenColumn a L k o R p') = realCurl η p') ∧
    ∀ b, |boxGreenColumn a L k o R p' b| ≤ 2 * (R : ℝ) ^ 2 / cK := by
  classical
  set S := supBall o (2 * (R : ℝ)) with hS
  set B := boxGreenColumn a L k o R p' with hB
  have hoff : ∀ b', b' ∉ bondsTouching o R → B b' = 0 := fun b' h => boxGreenColumn_of_not_mem h
  set φ := boxDivergence o R B with hφ
  set ψ : TorusBond n → ℝ := fun b => φ b.1 - φ (b.1 + unitStep n b.2) with hψ
  have hφoff : ∀ z, z ∉ supBall o R → φ z = 0 := fun z hz => by simp [hφ, boxDivergence, hz]
  have hψoff : ∀ b, b ∉ bondsTouching o R → ψ b = 0 := by
    intro b hb
    have h1 : b.1 ∉ supBall o R := fun h => hb (by simp [bondsTouching, h])
    have h2 : b.1 + unitStep n b.2 ∉ supBall o R := fun h => hb (by simp [bondsTouching, h])
    simp [hψ, hφoff _ h1, hφoff _ h2]
  have heq : ∀ b, b ∈ bondsTouching o R → ∑ b', hessEntry a L k S b b' * B b' + ψ b = curlCoeff p' b :=
    fun b hb => boxGreenColumn_equation hdet b hb
  have hψ2 : ∑ b, ψ b ^ 2 = 0 := by
    have h1 : realHess a L k S ψ B = 0 := realHess_grad_left hcol hblind φ B
    have h2 : ∑ b, ψ b * (∑ b', hessEntry a L k S b b' * B b' + ψ b) = ∑ b, curlCoeff p' b * ψ b := by
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases hb : b ∈ bondsTouching o R
      · rw [heq b hb]; ring
      · simp [hψoff b hb]
    have h3 : ∑ b, ψ b * (∑ b', hessEntry a L k S b b' * B b' + ψ b) = realHess a L k S ψ B + ∑ b, ψ b ^ 2 := by
      simp only [realHess, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      · refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
        ring
      · refine Finset.sum_congr rfl fun b _ => ?_
        ring
    rw [h3, h1, sum_curlCoeff_mul, realCurl_grad φ p'] at h2
    simpa using h2
  have hψ0 : ∀ b, ψ b = 0 := by
    intro b
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => sq_nonneg (ψ b))).1 hψ2 b (Finset.mem_univ b)
    exact pow_eq_zero_iff (two_ne_zero) |>.1 this
  have hφ0 : ∀ z, φ z = 0 := by
    have h1 := hgap (fun z => φ z • imaginaryUnitI) (fun z hz => by simp [hφoff z hz])
    have h2 : ∑ b : TorusBond n,
        ‖covariantGrad (0 : TorusBond n → imaginaryQuaternions) (fun z => φ z • imaginaryUnitI) b‖ ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun b _ => ?_
      rw [covariantGrad_zero]
      have : latticeGrad (fun z => φ z • imaginaryUnitI) b = ψ b • imaginaryUnitI := by
        simp only [latticeGrad, hψ]
        exact (sub_smul _ _ _).symm
      rw [this, hψ0 b]
      simp
    rw [h2] at h1
    have hpos : 0 < 4 * ((R : ℝ) + 1)⁻¹ ^ 2 := by positivity
    have h3 : ∑ z : TorusSite n, ‖φ z • (imaginaryUnitI : imaginaryQuaternions)‖ ^ 2 ≤ 0 := by
      by_contra hc
      rw [not_le] at hc
      have := mul_pos hpos hc
      linarith
    have h4 : ∑ z : TorusSite n, ‖φ z • (imaginaryUnitI : imaginaryQuaternions)‖ ^ 2 = 0 :=
      le_antisymm h3 (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    intro z
    have h5 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun z _ => sq_nonneg ‖φ z • (imaginaryUnitI : imaginaryQuaternions)‖)).1 h4 z (Finset.mem_univ z)
    rw [norm_smul, norm_unitI, mul_one] at h5
    simpa using h5
  have heq2 : ∀ b, b ∈ bondsTouching o R → ∑ b', hessEntry a L k S b b' * B b' = curlCoeff p' b := by
    intro b hb
    have := heq b hb
    rwa [hψ0 b, add_zero] at this
  have hcrit : ∀ η : TorusBond n → ℝ, (∀ b, b ∉ bondsTouching o R → η b = 0) →
      realHess a L k S η B = realCurl η p' := by
    intro η hη
    rw [← sum_curlCoeff_mul]
    simp only [realHess]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : b ∈ bondsTouching o R
    · rw [← heq2 b hb, Finset.sum_mul]
      refine Finset.sum_congr rfl fun b' _ => ?_
      ring
    · simp [hη b hb]
  refine ⟨hcrit, ?_⟩
  have hsq : bondNormSq S (liftReal B) = ∑ b, B b ^ 2 := by
    rw [bondNormSq, ← Finset.sum_subset (Finset.subset_univ (bondsWithin S))]
    · refine Finset.sum_congr rfl fun b _ => ?_
      simp only [liftReal]
      rw [norm_smul, norm_unitI, mul_one, Real.norm_eq_abs, sq_abs]
    · intro b _ hb
      have : b ∉ bondsTouching o R := fun h => hb (touching_mem_bondsWithin hR h)
      rw [hoff b this]
      simp
  have hslc : liftReal B ∈ gaugeSlice o R (0 : TorusBond n → imaginaryQuaternions) := by
    refine ⟨fun b hb => by simp [liftReal, hoff b hb], fun χ hχ => ?_⟩
    set hh : TorusSite n → ℝ := fun z => inner ℝ (imaginaryUnitI : imaginaryQuaternions) (χ z) with hhdef
    have h1 : ∀ b : TorusBond n,
        inner ℝ (liftReal B b) (covariantGrad (0 : TorusBond n → imaginaryQuaternions) χ b) =
          B b * (hh b.1 - hh (b.1 + unitStep n b.2)) := by
      intro b
      rw [covariantGrad_zero]
      simp [liftReal, latticeGrad, inner_smul_left, inner_sub_right, hhdef]
      ring
    simp only [h1]
    have h2 : ∀ b : TorusBond n, B b * (hh b.1 - hh (b.1 + unitStep n b.2)) =
        ∑ z : TorusSite n, hh z * (gradCoeff z b * B b) := by
      intro b
      rw [← sum_gradCoeff_mul hh b, Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      ring
    simp only [h2]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun z _ => ?_
    rw [← Finset.mul_sum]
    by_cases hz : z ∈ supBall o R
    · have : ∑ b, gradCoeff z b * B b = φ z := by simp [hφ, boxDivergence, hz]
      rw [this, hφ0 z, mul_zero]
    · simp [hhdef, hχ z hz]
  have hco := hslice _ hslc
  rw [hsq, hessianForm_liftReal hcol] at hco
  have hco2 : realHess a L k S B (fun b => imaginaryComponent 0 (liftReal B b)) = realCurl B p' := by
    simp only [component_liftReal]
    have := hcrit B hoff
    exact this
  rw [hco2] at hco
  set s := Real.sqrt (∑ b, B b ^ 2) with hs
  have hs2 : s ^ 2 = ∑ b, B b ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hbs : ∀ b, |B b| ≤ s := by
    intro b
    apply Real.abs_le_sqrt
    exact Finset.single_le_sum (f := fun b => B b ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ b)
  have hcurl : realCurl B p' ≤ 4 * s := by
    simp only [realCurl]
    have h1 := abs_le.1 (hbs (p'.1, p'.2.1))
    have h2 := abs_le.1 (hbs (p'.1 + unitStep n p'.2.1, p'.2.2))
    have h3 := abs_le.1 (hbs (p'.1 + unitStep n p'.2.2, p'.2.1))
    have h4 := abs_le.1 (hbs (p'.1, p'.2.2))
    linarith [h1.2, h2.2, h3.1, h4.1]
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hfin : s ≤ 2 * (R : ℝ) ^ 2 / cK := by
    rw [le_div_iff₀ hcK]
    have h5 : 2 * cK * ((R : ℝ) ^ 2)⁻¹ * s ^ 2 ≤ 4 * s := by rw [hs2]; linarith
    by_cases h0 : s = 0
    · rw [h0, zero_mul]; positivity
    · have hs' : 0 < s := lt_of_le_of_ne hs0 (Ne.symm h0)
      have h6 : 2 * cK * ((R : ℝ) ^ 2)⁻¹ * s ≤ 4 := by
        have : (2 * cK * ((R : ℝ) ^ 2)⁻¹ * s) * s ≤ 4 * s := by nlinarith
        exact le_of_mul_le_mul_right this hs'
      have h7 : cK * s * 2 ≤ 4 * (R : ℝ) ^ 2 := by
        have hR2 : (0:ℝ) < (R:ℝ)^2 := by positivity
        have : 2 * cK * ((R : ℝ) ^ 2)⁻¹ * s * (R:ℝ)^2 ≤ 4 * (R:ℝ)^2 := mul_le_mul_of_nonneg_right h6 hR2.le
        have e : 2 * cK * ((R : ℝ) ^ 2)⁻¹ * s * (R:ℝ)^2 = cK * s * 2 := by field_simp
        linarith
      nlinarith
  intro b
  exact (hbs b).trans hfin
private def supNormInt (z : Fin 4 → ℤ) : ℕ := Finset.univ.sup fun i => (z i).natAbs
private theorem le_supNormInt (z : Fin 4 → ℤ) (i : Fin 4) : (z i).natAbs ≤ supNormInt z := by apply _root_.YangMills.Construction.LatticePaths.natAbs_le_supNorm <;> assumption
private theorem supNormInt_le {z : Fin 4 → ℤ} {m : ℕ} : supNormInt z ≤ m ↔ ∀ i, (z i).natAbs ≤ m := by apply _root_.YangMills.Construction.LatticePaths.supNorm_le_iff <;> assumption
private theorem supNormInt_add (x y : Fin 4 → ℤ) : supNormInt (x + y) ≤ supNormInt x + supNormInt y := by apply _root_.YangMills.Construction.LatticePaths.supNorm_add_le <;> assumption
private theorem supNormInt_sub (x y : Fin 4 → ℤ) : supNormInt (x - y) ≤ supNormInt x + supNormInt y := by apply _root_.YangMills.Construction.PatchPotentials.supNorm_sub_le <;> assumption
private theorem supNormInt_single (i : Fin 4) : supNormInt (Pi.single i (1 : ℤ)) ≤ 1 := by
  rw [supNormInt_le]
  intro j
  by_cases h : j = i
  · subst h; simp
  · simp [h]
abbrev _root_.YangMills.DeltaSharedProofs.p501726 := @supNormInt_single
private theorem supNormInt_le_sqrt (z : Fin 4 → ℤ) : (supNormInt z : ℝ) ≤ Real.sqrt (intNormSq z) := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty (fun i => (z i).natAbs)
  have h1 : (supNormInt z : ℝ) = |(z i : ℝ)| := by
    simp only [supNormInt, hi]
    simp
  rw [h1]
  apply Real.abs_le_sqrt
  exact Finset.single_le_sum (f := fun l => (z l : ℝ) ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
private def offsetFrom (o z : TorusSite n) : Fin 4 → ℤ := fun i => (z i - o i).valMinAbs
private theorem supDist_eq_supNormInt (o z : TorusSite n) : supDist z o = supNormInt (offsetFrom o z) := rfl
private def toIntBond (o : TorusSite n) (b : TorusBond n) : IntBond := (offsetFrom o b.1, b.2)
private theorem add_siteOfInt_offsetFrom (o z : TorusSite n) : o + siteOfInt (offsetFrom o z) = z := by
  funext i
  simp [siteOfInt, offsetFrom]
abbrev _root_.YangMills.DeltaSharedProofs.p500399 := @add_siteOfInt_offsetFrom
private theorem bondFrom_toIntBond (o : TorusSite n) (b : TorusBond n) : bondFrom o (toIntBond o b) = b := by
  have : (o + siteOfInt (offsetFrom o b.1), b.2) = b := by rw [add_siteOfInt_offsetFrom]
  exact this
private theorem toIntBond_injective (o : TorusSite n) : Function.Injective (toIntBond o) := fun b b' h => by
  rw [← bondFrom_toIntBond o b, ← bondFrom_toIntBond o b', h]
private theorem offsetFrom_eq {o z : TorusSite n} {y : Fin 4 → ℤ} (hz : z = o + siteOfInt y)
    (hy : ∀ i, 2 * (y i).natAbs < n) : offsetFrom o z = y := by
  funext i
  have hyi := hy i
  refine (ZMod.valMinAbs_spec _ _).2 ⟨?_, ?_⟩
  · rw [hz]
    simp [siteOfInt]
  · constructor <;> omega
private theorem unitStep_eq_siteOfInt (i : Fin 4) : unitStep n i = (siteOfInt (Pi.single i 1) : TorusSite n) := by apply _root_.YangMills.Construction.TorusLumps.unitStep_eq_siteOfInt <;> assumption
private theorem offsetFrom_add_unitStep {o x : TorusSite n} (i : Fin 4) (h : 2 * (supDist x o + 1) < n) :
    offsetFrom o (x + unitStep n i) = offsetFrom o x + Pi.single i 1 := by
  apply offsetFrom_eq
  · rw [siteOfInt_add, ← unitStep_eq_siteOfInt, ← add_assoc, add_siteOfInt_offsetFrom]
  · intro j
    have h1 := le_supNormInt (offsetFrom o x + Pi.single i 1) j
    have h2 := supNormInt_add (offsetFrom o x) (Pi.single i 1)
    have h3 := supNormInt_single i
    rw [← supDist_eq_supNormInt] at h2
    omega
private def onTorus (o : TorusSite n) (g : IntBond → ℝ) : TorusBond n → ℝ := fun b => g (toIntBond o b)
private theorem realCurl_onTorus (o : TorusSite n) (g : IntBond → ℝ) (p : TorusPlaquette n)
    (h : 2 * (supDist p.1 o + 1) < n) :
    realCurl (onTorus o g) p = intCurl g (offsetFrom o p.1, p.2.1, p.2.2) := by
  simp only [realCurl, onTorus, toIntBond, intCurl, offsetFrom_add_unitStep _ h]
private theorem summable_exp_neg_natAbs {c : ℝ} (hc : 0 < c) :
    Summable fun z : ℤ => Real.exp (-(c * z.natAbs)) := by apply _root_.YangMills.SharedProofs.p17292 <;> assumption
private theorem exp_bondSupDist_summable {c : ℝ} (hc : 0 < c) : ∃ W : ℝ, 0 ≤ W ∧ ∀ b₀ : IntBond,
    Summable (fun b => Real.exp (-(c * bondSupDist b₀ b))) ∧ ∑' b, Real.exp (-(c * bondSupDist b₀ b)) ≤ W := by
  classical
  set A := ∑' z : ℤ, Real.exp (-(c / 4 * z.natAbs)) with hA
  have hsum := summable_exp_neg_natAbs (c := c / 4) (by positivity)
  refine ⟨4 * A ^ 4, by positivity, fun b₀ => ?_⟩
  set e : Fin 4 → ℤ → ℝ := fun i t => Real.exp (-(c / 4 * ((b₀.1 i - t).natAbs : ℝ))) with he
  have he0 : ∀ i t, 0 ≤ e i t := fun i t => (Real.exp_pos _).le
  have hes : ∀ i, Summable (e i) := fun i => hsum.comp_injective (Equiv.subLeft (b₀.1 i)).injective
  have het : ∀ i, ∑' t, e i t = A := fun i =>
    (Equiv.subLeft (b₀.1 i)).tsum_eq fun z : ℤ => Real.exp (-(c / 4 * (z.natAbs : ℝ)))
  set Ψ : IntBond → ℝ := fun b => ∏ i, e i (b.1 i) with hΨ
  have hΨ0 : ∀ b, 0 ≤ Ψ b := fun b => Finset.prod_nonneg fun i _ => he0 i _
  have hfin : ∀ s : Finset IntBond, ∑ b ∈ s, Ψ b ≤ 4 * A ^ 4 := by
    intro s
    set U : Fin 4 → Finset ℤ := fun i => s.image fun b => b.1 i with hU
    have hsub : s ⊆ (Fintype.piFinset U) ×ˢ (Finset.univ : Finset (Fin 4)) := by
      intro b hb
      simp only [Finset.mem_product, Fintype.mem_piFinset, Finset.mem_univ, and_true]
      intro i
      exact Finset.mem_image_of_mem _ hb
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun b _ _ => hΨ0 b).trans ?_
    rw [Finset.sum_product]
    simp only [hΨ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h1 : ∑ z ∈ Fintype.piFinset U, ∏ i, e i (z i) = ∏ i, ∑ t ∈ U i, e i t :=
      (Finset.prod_univ_sum U (fun i t => e i t)).symm
    rw [← Finset.mul_sum, h1]
    have h2 : ∏ i, ∑ t ∈ U i, e i t ≤ ∏ _i : Fin 4, A := by
      refine Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun t _ => he0 i t) fun i _ => ?_
      rw [← het i]
      exact (hes i).sum_le_tsum _ (fun t _ => he0 i t)
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h2
    push_cast
    linarith
  have hbound : ∀ b, Real.exp (-(c * bondSupDist b₀ b)) ≤ Ψ b := by
    intro b
    simp only [hΨ, he]
    rw [← Real.exp_sum]
    apply Real.exp_le_exp.2
    have h1 : ∀ i, ((b₀.1 i - b.1 i).natAbs : ℝ) ≤ bondSupDist b₀ b := fun i => by
      exact_mod_cast Finset.le_sup (f := fun i => (b₀.1 i - b.1 i).natAbs) (Finset.mem_univ i)
    have h2 : ∑ i, -(c / 4 * ((b₀.1 i - b.1 i).natAbs : ℝ)) ≥ ∑ _i : Fin 4, -(c / 4 * (bondSupDist b₀ b : ℝ)) :=
      Finset.sum_le_sum fun i _ => by nlinarith [h1 i]
    have h3 : ∑ _i : Fin 4, -(c / 4 * (bondSupDist b₀ b : ℝ)) = -(c * bondSupDist b₀ b) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
    linarith
  have hΨs : Summable Ψ := summable_of_sum_le hΨ0 hfin
  have hS := Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) hbound hΨs
  refine ⟨hS, ?_⟩
  exact (hS.tsum_le_tsum hbound hΨs).trans (hΨs.tsum_le_of_sum_le hfin)
private theorem row_sum_estimate {Q : IntBond → IntBond → ℝ} {c₁ C₁ W K ε₀ D : ℝ}
    (hc₁ : 0 < c₁) (hK : 0 ≤ K) (hC₁ : 0 ≤ C₁)
    (hdecay : ∀ b b', |Q b b'| ≤ C₁ * Real.exp (-(c₁ * bondSupDist b b')))
    (hW : ∀ b₀ : IntBond, Summable (fun b => Real.exp (-(c₁ / 2 * bondSupDist b₀ b))) ∧
      ∑' b, Real.exp (-(c₁ / 2 * bondSupDist b₀ b)) ≤ W)
    {o : TorusSite n} {row : TorusBond n → ℝ} {ℓ : IntBond} {Bh χ : IntBond → ℝ} {c' : ℝ}
    (hsum : HasSum (fun ℓ' => Q ℓ ℓ' * Bh ℓ') c')
    (hBh : ∀ ℓ', |Bh ℓ'| ≤ K) (hχ0 : ∀ ℓ', 0 ≤ χ ℓ') (hχ1 : ∀ ℓ', χ ℓ' ≤ 1)
    (T : Finset IntBond) (hT : ∀ ℓ', ℓ' ∉ T → χ ℓ' = 0) (hTb : ∀ ℓ' ∈ T, toIntBond o (bondFrom o ℓ') = ℓ')
    (hclose : ∀ ℓ' ∈ T, |row (bondFrom o ℓ') - Q ℓ ℓ'| ≤ ε₀)
    (hfar : ∀ ℓ', χ ℓ' ≠ 1 → D ≤ bondSupDist ℓ ℓ') :
    |∑ b' : TorusBond n, row b' * onTorus o (fun ℓ' => χ ℓ' * Bh ℓ') b' - c'| ≤
      T.card * ε₀ * K + K * C₁ * Real.exp (-(c₁ / 2 * D)) * W := by
  classical
  set G : IntBond → ℝ := fun ℓ' => χ ℓ' * Bh ℓ' with hG
  have hG0 : ∀ ℓ', ℓ' ∉ T → G ℓ' = 0 := fun ℓ' h => by simp [hG, hT ℓ' h]
  have hGK : ∀ ℓ', |G ℓ'| ≤ K := fun ℓ' => by
    simp only [hG, abs_mul]
    have h1 : |χ ℓ'| ≤ 1 := by rw [abs_of_nonneg (hχ0 ℓ')]; exact hχ1 ℓ'
    calc |χ ℓ'| * |Bh ℓ'| ≤ 1 * K := mul_le_mul h1 (hBh ℓ') (abs_nonneg _) zero_le_one
      _ = K := one_mul K
  have hinj : Set.InjOn (bondFrom o) (T : Set IntBond) := by
    intro x hx y hy hxy
    have := congrArg (toIntBond o) hxy
    rwa [hTb x hx, hTb y hy] at this
  have e1 : ∑ b' : TorusBond n, row b' * onTorus o G b' = ∑ ℓ' ∈ T, row (bondFrom o ℓ') * G ℓ' := by
    have h2 : ∑ ℓ' ∈ T, row (bondFrom o ℓ') * G ℓ' = ∑ b' ∈ T.image (bondFrom o), row b' * onTorus o G b' := by
      rw [Finset.sum_image hinj]
      refine Finset.sum_congr rfl fun ℓ' h => ?_
      simp only [onTorus, hTb ℓ' h]
    rw [h2]
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro b' _ hb'
    have : toIntBond o b' ∉ T := fun h => hb' (Finset.mem_image.2 ⟨_, h, bondFrom_toIntBond o b'⟩)
    simp [onTorus, hG0 _ this]
  have e2 : |∑ ℓ' ∈ T, row (bondFrom o ℓ') * G ℓ' - ∑ ℓ' ∈ T, Q ℓ ℓ' * G ℓ'| ≤ T.card * ε₀ * K := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ ℓ' ∈ T, |row (bondFrom o ℓ') * G ℓ' - Q ℓ ℓ' * G ℓ'| ≤ ε₀ * K := by
      intro ℓ' h
      rw [← sub_mul, abs_mul]
      exact mul_le_mul (hclose ℓ' h) (hGK ℓ') (abs_nonneg _) ((abs_nonneg _).trans (hclose ℓ' h))
    refine (Finset.sum_le_sum this).trans ?_
    simp [mul_assoc]
  set F : IntBond → ℝ := fun ℓ' => Q ℓ ℓ' * Bh ℓ' with hF
  have hs1 : HasSum (fun ℓ' => Q ℓ ℓ' * G ℓ') (∑ ℓ' ∈ T, Q ℓ ℓ' * G ℓ') :=
    hasSum_sum_of_ne_finset_zero fun ℓ' h => by simp [hG0 ℓ' h]
  have hs2 : HasSum (fun ℓ' => F ℓ' - Q ℓ ℓ' * G ℓ') (c' - ∑ ℓ' ∈ T, Q ℓ ℓ' * G ℓ') := hsum.sub hs1
  have hb : ∀ ℓ', |F ℓ' - Q ℓ ℓ' * G ℓ'| ≤
      K * C₁ * Real.exp (-(c₁ / 2 * D)) * Real.exp (-(c₁ / 2 * bondSupDist ℓ ℓ')) := by
    intro ℓ'
    by_cases h1 : χ ℓ' = 1
    · have : F ℓ' - Q ℓ ℓ' * G ℓ' = 0 := by simp [hF, hG, h1]
      rw [this, abs_zero]
      positivity
    · have hD := hfar ℓ' h1
      have e : F ℓ' - Q ℓ ℓ' * G ℓ' = Q ℓ ℓ' * ((1 - χ ℓ') * Bh ℓ') := by simp only [hF, hG]; ring
      rw [e, abs_mul, abs_mul]
      have h2 : |1 - χ ℓ'| ≤ 1 := by
        rw [abs_of_nonneg (by linarith [hχ1 ℓ'])]
        linarith [hχ0 ℓ']
      have h3 : |1 - χ ℓ'| * |Bh ℓ'| ≤ K := by
        calc |1 - χ ℓ'| * |Bh ℓ'| ≤ 1 * K := mul_le_mul h2 (hBh ℓ') (abs_nonneg _) zero_le_one
          _ = K := one_mul K
      have h4 : Real.exp (-(c₁ * bondSupDist ℓ ℓ')) ≤
          Real.exp (-(c₁ / 2 * D)) * Real.exp (-(c₁ / 2 * bondSupDist ℓ ℓ')) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.2
        nlinarith
      calc |Q ℓ ℓ'| * (|1 - χ ℓ'| * |Bh ℓ'|)
          ≤ (C₁ * (Real.exp (-(c₁ / 2 * D)) * Real.exp (-(c₁ / 2 * bondSupDist ℓ ℓ')))) * K :=
            mul_le_mul ((hdecay ℓ ℓ').trans (mul_le_mul_of_nonneg_left h4 hC₁)) h3 (by positivity) (by positivity)
        _ = _ := by ring
  have hsw := (hW ℓ).1
  have hbs : Summable fun ℓ' => K * C₁ * Real.exp (-(c₁ / 2 * D)) * Real.exp (-(c₁ / 2 * bondSupDist ℓ ℓ')) :=
    hsw.mul_left _
  have e3 : |c' - ∑ ℓ' ∈ T, Q ℓ ℓ' * G ℓ'| ≤ K * C₁ * Real.exp (-(c₁ / 2 * D)) * W := by
    rw [← hs2.tsum_eq]
    have h5 : ‖∑' ℓ', (F ℓ' - Q ℓ ℓ' * G ℓ')‖ ≤
        ∑' ℓ', K * C₁ * Real.exp (-(c₁ / 2 * D)) * Real.exp (-(c₁ / 2 * bondSupDist ℓ ℓ')) :=
      tsum_of_norm_bounded hbs.hasSum (fun ℓ' => by simpa using hb ℓ')
    rw [Real.norm_eq_abs, tsum_mul_left] at h5
    refine h5.trans (mul_le_mul_of_nonneg_left (hW ℓ).2 (by positivity))
  rw [e1]
  calc |∑ ℓ' ∈ T, row (bondFrom o ℓ') * G ℓ' - c'|
      ≤ |∑ ℓ' ∈ T, row (bondFrom o ℓ') * G ℓ' - ∑ ℓ' ∈ T, Q ℓ ℓ' * G ℓ'| +
          |∑ ℓ' ∈ T, Q ℓ ℓ' * G ℓ' - c'| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add e2 (by rw [abs_sub_comm]; exact e3)
private def bondSupNorm (ℓ : IntBond) : ℝ := supNormInt ℓ.1
private def clampUnit (x : ℝ) : ℝ := max 0 (min 1 x)
private theorem clampUnit_lipschitz (x y : ℝ) : |clampUnit x - clampUnit y| ≤ |x - y| := by
  have h1 := le_abs_self (x - y)
  have h2 := neg_abs_le (x - y)
  simp only [clampUnit, max_def, min_def]
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith
abbrev _root_.YangMills.DeltaSharedProofs.p500476 := @clampUnit_lipschitz
private theorem clampUnit_nonneg (x : ℝ) : 0 ≤ clampUnit x := le_max_left _ _
private theorem clampUnit_le_one (x : ℝ) : clampUnit x ≤ 1 := max_le zero_le_one (min_le_left _ _)
private theorem clampUnit_of_one_le {x : ℝ} (h : 1 ≤ x) : clampUnit x = 1 := by simp [clampUnit, h]
private theorem clampUnit_of_nonpos {x : ℝ} (h : x ≤ 0) : clampUnit x = 0 := by
  have : min 1 x ≤ 0 := (min_le_right _ _).trans h
  simp [clampUnit, this]
private def innerCutoff (ρ : ℝ) (ℓ : IntBond) : ℝ := clampUnit ((5 * ρ / 4 - bondSupNorm ℓ) / (ρ / 8))
private def outerCutoff (ρ : ℝ) (ℓ : IntBond) : ℝ := clampUnit ((bondSupNorm ℓ - ρ / 2) / (ρ / 4))
private def shellCutoff (ρ : ℝ) (ℓ : IntBond) : ℝ := min (outerCutoff ρ ℓ) (innerCutoff ρ ℓ)
private theorem shellCutoff_nonneg (ρ : ℝ) (ℓ : IntBond) : 0 ≤ shellCutoff ρ ℓ :=
  le_min (clampUnit_nonneg _) (clampUnit_nonneg _)
private theorem shellCutoff_le_one (ρ : ℝ) (ℓ : IntBond) : shellCutoff ρ ℓ ≤ 1 :=
  (min_le_left _ _).trans (clampUnit_le_one _)
private theorem innerCutoff_eq_one {ρ : ℝ} (hρ : 0 < ρ) {ℓ : IntBond} (h : bondSupNorm ℓ ≤ 9 * ρ / 8) :
    innerCutoff ρ ℓ = 1 := by
  apply clampUnit_of_one_le
  rw [le_div_iff₀ (by positivity)]
  linarith
private theorem innerCutoff_eq_zero {ρ : ℝ} (hρ : 0 < ρ) {ℓ : IntBond} (h : 5 * ρ / 4 ≤ bondSupNorm ℓ) :
    innerCutoff ρ ℓ = 0 := by
  apply clampUnit_of_nonpos
  apply div_nonpos_of_nonpos_of_nonneg <;> linarith
private theorem outerCutoff_eq_one {ρ : ℝ} (hρ : 0 < ρ) {ℓ : IntBond} (h : 3 * ρ / 4 ≤ bondSupNorm ℓ) :
    outerCutoff ρ ℓ = 1 := by
  apply clampUnit_of_one_le
  rw [le_div_iff₀ (by positivity)]
  linarith
private theorem outerCutoff_eq_zero {ρ : ℝ} (hρ : 0 < ρ) {ℓ : IntBond} (h : bondSupNorm ℓ ≤ ρ / 2) :
    outerCutoff ρ ℓ = 0 := by
  apply clampUnit_of_nonpos
  apply div_nonpos_of_nonpos_of_nonneg <;> linarith
private theorem shellCutoff_lipschitz {ρ : ℝ} (hρ : 0 < ρ) (ℓ ℓ' : IntBond) :
    |shellCutoff ρ ℓ - shellCutoff ρ ℓ'| ≤ 8 / ρ * |bondSupNorm ℓ - bondSupNorm ℓ'| := by
  have h1 : |outerCutoff ρ ℓ - outerCutoff ρ ℓ'| ≤ 8 / ρ * |bondSupNorm ℓ - bondSupNorm ℓ'| := by
    refine (clampUnit_lipschitz _ _).trans ?_
    have e : (bondSupNorm ℓ - ρ / 2) / (ρ / 4) - (bondSupNorm ℓ' - ρ / 2) / (ρ / 4) =
        4 / ρ * (bondSupNorm ℓ - bondSupNorm ℓ') := by
      field_simp
      ring
    rw [e, abs_mul, abs_of_pos (by positivity : 0 < 4 / ρ)]
    have : 4 / ρ ≤ 8 / ρ := by
      apply div_le_div_of_nonneg_right <;> linarith
    exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
  have h2 : |innerCutoff ρ ℓ - innerCutoff ρ ℓ'| ≤ 8 / ρ * |bondSupNorm ℓ - bondSupNorm ℓ'| := by
    refine (clampUnit_lipschitz _ _).trans ?_
    have e : (5 * ρ / 4 - bondSupNorm ℓ) / (ρ / 8) - (5 * ρ / 4 - bondSupNorm ℓ') / (ρ / 8) =
        8 / ρ * (bondSupNorm ℓ' - bondSupNorm ℓ) := by
      field_simp
      ring
    rw [e, abs_mul, abs_of_pos (by positivity : 0 < 8 / ρ), abs_sub_comm]
  set A := outerCutoff ρ ℓ
  set A' := outerCutoff ρ ℓ'
  set D := innerCutoff ρ ℓ
  set D' := innerCutoff ρ ℓ'
  set X := 8 / ρ * |bondSupNorm ℓ - bondSupNorm ℓ'|
  have a1 := abs_le.1 h1
  have a2 := abs_le.1 h2
  simp only [shellCutoff, min_def]
  change |(if A ≤ D then A else D) - (if A' ≤ D' then A' else D')| ≤ X
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]
private theorem bondSupNorm_step (x : Fin 4 → ℤ) (i j j' : Fin 4) :
    |bondSupNorm (x + Pi.single i 1, j) - bondSupNorm (x, j')| ≤ 1 := by
  have h1 := supNormInt_add x (Pi.single i 1)
  have h2 := supNormInt_single i
  have h3 := supNormInt_sub (x + Pi.single i 1) (Pi.single i 1)
  have e : x + Pi.single i (1 : ℤ) - Pi.single i 1 = x := by simp
  rw [e] at h3
  have h4 : (supNormInt (x + Pi.single i 1) : ℝ) ≤ supNormInt x + 1 := by
    exact_mod_cast (by omega : supNormInt (x + Pi.single i 1) ≤ supNormInt x + 1)
  have h5 : (supNormInt x : ℝ) ≤ supNormInt (x + Pi.single i 1) + 1 := by
    exact_mod_cast (by omega : supNormInt x ≤ supNormInt (x + Pi.single i 1) + 1)
  simp only [bondSupNorm]
  rw [abs_le]
  constructor <;> linarith
private theorem le_one_add_sqrt {s : ℝ} (hs : 0 < s) {z : Fin 4 → ℤ} (h : s ≤ supNormInt z) :
    s ≤ 1 + Real.sqrt (intNormSq z) := by
  have := supNormInt_le_sqrt z
  linarith
private theorem curl_shell_bound {K ρ : ℝ} (hK : 0 ≤ K) (hρ : 16 ≤ ρ) {Bc : IntBond → ℝ} {h : Fin 4 → ℤ}
    (hh : (supNormInt h : ℝ) ≤ ρ / 8)
    (hB : ∀ b : IntBond, |Bc b| ≤ K * ((1 + Real.sqrt (intNormSq b.1)) ^ 3)⁻¹)
    (hC : ∀ (z : Fin 4 → ℤ) (m n' : Fin 4), m < n' →
      |intCurl Bc (z, m, n')| ≤ K * ((1 + Real.sqrt (intNormSq z)) ^ 4)⁻¹)
    (x : Fin 4 → ℤ) (m n' : Fin 4) (hmn : m < n') :
    |intCurl (fun ℓ => shellCutoff ρ ℓ * Bc (ℓ.1 - h, ℓ.2)) (x, m, n')| ≤ 1280 * K * (ρ ^ 4)⁻¹ := by
  have hρ0 : 0 < ρ := by linarith
  set w := shellCutoff ρ with hw
  simp only [intCurl]
  by_cases hx : (supNormInt x : ℝ) + 1 ≤ ρ / 2
  · have z1 : ∀ (i : Fin 4) (j : Fin 4), w (x + Pi.single i 1, j) = 0 := by
      intro i j
      have := abs_le.1 (bondSupNorm_step x i j j)
      have h2 : bondSupNorm (x + Pi.single i 1, j) ≤ ρ / 2 := by
        have : bondSupNorm (x, j) = supNormInt x := rfl
        linarith
      have : outerCutoff ρ (x + Pi.single i 1, j) = 0 := outerCutoff_eq_zero hρ0 h2
      have h3 := shellCutoff_nonneg ρ (x + Pi.single i 1, j)
      have h4 : w (x + Pi.single i 1, j) ≤ 0 := by
        rw [hw]
        exact (min_le_left _ _).trans this.le
      linarith
    have z2 : ∀ j : Fin 4, w (x, j) = 0 := by
      intro j
      have h2 : bondSupNorm (x, j) ≤ ρ / 2 := by
        have : bondSupNorm (x, j) = supNormInt x := rfl
        linarith
      have : outerCutoff ρ (x, j) = 0 := outerCutoff_eq_zero hρ0 h2
      have h3 := shellCutoff_nonneg ρ (x, j)
      have h4 : w (x, j) ≤ 0 := by
        rw [hw]
        exact (min_le_left _ _).trans this.le
      linarith
    simp only [z1, z2]
    simp only [zero_mul, add_zero, sub_zero, abs_zero]
    positivity
  · rw [not_le] at hx
    set y := x - h with hy
    set s := ρ / 4 with hs
    have hs0 : 0 < s := by positivity
    have hsy : s + 1 ≤ (supNormInt y : ℝ) := by
      have h1 := supNormInt_sub y (-h)
      have e : y - -h = x := by simp [hy]
      rw [e] at h1
      have h2 : supNormInt (-h) = supNormInt h := by simp [supNormInt]
      rw [h2] at h1
      have h3 : (supNormInt x : ℝ) ≤ supNormInt y + supNormInt h := by exact_mod_cast h1
      rw [hs]
      linarith
    have hstep : ∀ i : Fin 4, s ≤ (supNormInt (y + Pi.single i 1) : ℝ) := by
      intro i
      have := abs_le.1 (bondSupNorm_step y i 0 0)
      have e1 : bondSupNorm (y, (0 : Fin 4)) = supNormInt y := rfl
      have e2 : bondSupNorm (y + Pi.single i 1, (0 : Fin 4)) = supNormInt (y + Pi.single i 1) := rfl
      rw [e1, e2] at this
      linarith [this.1]
    have hb : ∀ (i j : Fin 4), |Bc (y + Pi.single i 1, j)| ≤ K * (s ^ 3)⁻¹ := by
      intro i j
      refine (hB _).trans (mul_le_mul_of_nonneg_left ?_ hK)
      apply inv_anti₀ (by positivity)
      exact pow_le_pow_left₀ hs0.le (le_one_add_sqrt hs0 (hstep i)) 3
    have hcu : |intCurl Bc (y, m, n')| ≤ K * (s ^ 4)⁻¹ := by
      refine (hC y m n' hmn).trans (mul_le_mul_of_nonneg_left ?_ hK)
      apply inv_anti₀ (by positivity)
      exact pow_le_pow_left₀ hs0.le (le_one_add_sqrt hs0 (by linarith)) 4
    simp only [intCurl] at hcu
    have e2 : ∀ i : Fin 4, x + Pi.single i (1 : ℤ) - h = y + Pi.single i 1 := fun i => by
      rw [hy]; abel
    simp only [e2]
    have w1 : w (x, n') = w (x, m) := by
      have : bondSupNorm (x, n') = bondSupNorm (x, m) := rfl
      simp only [hw, shellCutoff, outerCutoff, innerCutoff, this]
    have l2 : |w (x + Pi.single m 1, n') - w (x, m)| ≤ 8 / ρ := by
      refine (shellCutoff_lipschitz hρ0 _ _).trans ?_
      have := bondSupNorm_step x m n' m
      calc 8 / ρ * |bondSupNorm (x + Pi.single m 1, n') - bondSupNorm (x, m)| ≤ 8 / ρ * 1 :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = 8 / ρ := mul_one _
    have l3 : |w (x + Pi.single n' 1, m) - w (x, m)| ≤ 8 / ρ := by
      refine (shellCutoff_lipschitz hρ0 _ _).trans ?_
      have := bondSupNorm_step x n' m m
      calc 8 / ρ * |bondSupNorm (x + Pi.single n' 1, m) - bondSupNorm (x, m)| ≤ 8 / ρ * 1 :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = 8 / ρ := mul_one _
    have w0 := shellCutoff_nonneg ρ (x, m)
    have w1' := shellCutoff_le_one ρ (x, m)
    set b₁ := Bc (y, m)
    set b₂ := Bc (y + Pi.single m 1, n')
    set b₃ := Bc (y + Pi.single n' 1, m)
    set b₄ := Bc (y, n')
    set W₁ := w (x, m)
    set W₂ := w (x + Pi.single m 1, n')
    set W₃ := w (x + Pi.single n' 1, m)
    rw [w1]
    have e3 : W₁ * b₁ + W₂ * b₂ - W₃ * b₃ - W₁ * b₄ =
        W₁ * (b₁ + b₂ - b₃ - b₄) + (W₂ - W₁) * b₂ - (W₃ - W₁) * b₃ := by ring
    rw [e3]
    have t1 : |W₁ * (b₁ + b₂ - b₃ - b₄)| ≤ K * (s ^ 4)⁻¹ := by
      rw [abs_mul, abs_of_nonneg w0]
      calc W₁ * |b₁ + b₂ - b₃ - b₄| ≤ 1 * |b₁ + b₂ - b₃ - b₄| := mul_le_mul_of_nonneg_right w1' (abs_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact hcu
    have t2 : |(W₂ - W₁) * b₂| ≤ 8 / ρ * (K * (s ^ 3)⁻¹) := by
      rw [abs_mul]
      exact mul_le_mul l2 (hb m n') (abs_nonneg _) (by positivity)
    have t3 : |(W₃ - W₁) * b₃| ≤ 8 / ρ * (K * (s ^ 3)⁻¹) := by
      rw [abs_mul]
      exact mul_le_mul l3 (hb n' m) (abs_nonneg _) (by positivity)
    have t4 := abs_sub (W₁ * (b₁ + b₂ - b₃ - b₄) + (W₂ - W₁) * b₂) ((W₃ - W₁) * b₃)
    have t5 := abs_add_le (W₁ * (b₁ + b₂ - b₃ - b₄)) ((W₂ - W₁) * b₂)
    have fin : K * (s ^ 4)⁻¹ + 8 / ρ * (K * (s ^ 3)⁻¹) + 8 / ρ * (K * (s ^ 3)⁻¹) = 1280 * K * (ρ ^ 4)⁻¹ := by
      rw [hs]
      field_simp
      ring
    linarith
private theorem lieFormCurl_liftReal (f : TorusBond n → ℝ) (p : TorusPlaquette n) :
    lieFormCurl (liftReal f) p = realCurl f p • imaginaryUnitI := by
  simp only [lieFormCurl, liftReal, realCurl]
  have e1 : ∀ x y : ℝ, x • (imaginaryUnitI : imaginaryQuaternions) - y • imaginaryUnitI = (x - y) • imaginaryUnitI :=
    fun x y => (sub_smul x y _).symm
  have e2 : ∀ x y : ℝ, x • (imaginaryUnitI : imaginaryQuaternions) + y • imaginaryUnitI = (x + y) • imaginaryUnitI :=
    fun x y => (add_smul x y _).symm
  rw [e2, e1, e1]
private theorem norm_lieFormCurl_liftReal (f : TorusBond n → ℝ) (p : TorusPlaquette n) :
    ‖lieFormCurl (liftReal f) p‖ = |realCurl f p| := by
  rw [lieFormCurl_liftReal, norm_smul, norm_unitI, mul_one, Real.norm_eq_abs]
private theorem curlNormSq_liftReal (S : Finset (TorusSite n)) (f : TorusBond n → ℝ) :
    curlNormSq S (liftReal f) = ∑ p ∈ plaquettesIn S, realCurl f p ^ 2 := by
  simp only [curlNormSq, norm_lieFormCurl_liftReal, sq_abs]
private theorem realHess_add_right {a : ℝ} {L k : ℕ} {S : Finset (TorusSite n)} (u v v' : TorusBond n → ℝ) :
    realHess a L k S u (v + v') = realHess a L k S u v + realHess a L k S u v' := by
  simp only [realHess, Pi.add_apply, mul_add, Finset.sum_add_distrib]
private theorem realHess_sub_right {a : ℝ} {L k : ℕ} {S : Finset (TorusSite n)} (u v v' : TorusBond n → ℝ) :
    realHess a L k S u (v - v') = realHess a L k S u v - realHess a L k S u v' := by
  simp only [realHess, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
private theorem realHess_sub_left {a : ℝ} {L k : ℕ} {S : Finset (TorusSite n)} (u u' v : TorusBond n → ℝ) :
    realHess a L k S (u - u') v = realHess a L k S u v - realHess a L k S u' v := by
  simp only [realHess, Pi.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]
private theorem card_supBall_le (o : TorusSite n) (r : ℕ) : (supBall o (r : ℝ)).card ≤ (2 * r + 1) ^ 4 := by
  classical
  have h : (Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(r : ℤ)) r).card = (2 * r + 1) ^ 4 := by
    simp only [Fintype.card_piFinset, Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 1
    omega
  rw [← h]
  refine Finset.card_le_card_of_injOn (offsetFrom o) ?_ ?_
  · intro z hz
    have hz' : (supDist z o : ℝ) ≤ r := by simpa [supBall] using hz
    have hz2 : supDist z o ≤ r := by exact_mod_cast hz'
    refine Finset.mem_coe.2 (Fintype.mem_piFinset.2 fun i => Finset.mem_Icc.2 ?_)
    have := le_supNormInt (offsetFrom o z) i
    rw [← supDist_eq_supNormInt] at this
    constructor <;> omega
  · intro z _ z' _ h
    rw [← add_siteOfInt_offsetFrom o z, ← add_siteOfInt_offsetFrom o z', h]
abbrev _root_.YangMills.SharedProofs.p9908 := @card_supBall_le
private theorem limitForm_translate {a cK c C : ℝ} {L k : ℕ} {Q : IntBond → IntBond → ℝ}
    (hQ : IsLimitForm a cK c C L k Q) (t : Fin 4 → ℤ) (b b' : IntBond) :
    Q (b.1 + t, b.2) (b'.1 + t, b'.2) = Q b b' := by
  have h := hQ.invariant ⟨Equiv.refl _, fun _ => 1, t, fun _ => Or.inl rfl⟩ b b'
  simp [bondImage] at h
  exact h
private theorem curlCoeff_eq_intCurl {o : TorusSite n} {p' : TorusPlaquette n} (b : TorusBond n)
    (hn : 2 * (supDist p'.1 o + 1) < n) :
    curlCoeff p' b = intCurl
      (Pi.single ((toIntBond o b).1 - offsetFrom o p'.1, (toIntBond o b).2) (1 : ℝ)) (0, p'.2.1, p'.2.2) := by
  classical
  set h := offsetFrom o p'.1 with hh
  set ℓ := toIntBond o b with hℓ
  have key : ∀ (b₀ : TorusBond n) (v : Fin 4 → ℤ) (j : Fin 4), toIntBond o b₀ = (h + v, j) →
      (if b = b₀ then (1 : ℝ) else 0) = (Pi.single (ℓ.1 - h, ℓ.2) (1 : ℝ) : IntBond → ℝ) (v, j) := by
    intro b₀ v j hb
    rw [Pi.single_apply]
    refine if_congr ?_ rfl rfl
    constructor
    · intro e
      subst e
      have e1 : ℓ = (h + v, j) := hb
      rw [e1]
      simp
    · intro e
      apply toIntBond_injective o
      rw [hb]
      have e1 : v = ℓ.1 - h := congrArg Prod.fst e
      have e2 : j = ℓ.2 := congrArg Prod.snd e
      rw [e1, e2]
      simp [hℓ]
  simp only [curlCoeff, intCurl]
  have k1 := key (p'.1, p'.2.1) 0 p'.2.1 (by simp [toIntBond, hh])
  have k2 := key (p'.1 + unitStep n p'.2.1, p'.2.2) (0 + Pi.single p'.2.1 1) p'.2.2
    (by simp [toIntBond, hh, offsetFrom_add_unitStep _ hn])
  have k3 := key (p'.1 + unitStep n p'.2.2, p'.2.1) (0 + Pi.single p'.2.2 1) p'.2.1
    (by simp [toIntBond, hh, offsetFrom_add_unitStep _ hn])
  have k4 := key (p'.1, p'.2.2) 0 p'.2.2 (by simp [toIntBond, hh])
  rw [k1, k2, k3, k4]
private theorem pow_mul_exp_eventually_le (K c : ℝ) (m : ℕ) (hc : 0 < c) :
    ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → K * (R : ℝ) ^ m * Real.exp (-(c * R)) ≤ 1 := by
  have h1 : Filter.Tendsto (fun x : ℝ => x ^ m * Real.exp (-(c * x))) Filter.atTop (nhds 0) := by
    have h2 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero m).comp
      (Filter.tendsto_id.const_mul_atTop hc)
    have h3 := h2.const_mul ((c ^ m)⁻¹)
    simp only [mul_zero] at h3
    refine h3.congr fun x => ?_
    simp only [Function.comp, id]
    rw [mul_pow]
    field_simp
  have h2 : Filter.Tendsto (fun x : ℝ => K * (x ^ m * Real.exp (-(c * x)))) Filter.atTop (nhds 0) := by
    simpa using h1.const_mul K
  have h3 := (h2.comp tendsto_natCast_atTop_atTop).eventually (ge_mem_nhds (zero_lt_one' ℝ))
  obtain ⟨R₀, h⟩ := Filter.eventually_atTop.1 h3
  refine ⟨R₀, fun R hR => ?_⟩
  have := h R hR
  simp only [Function.comp] at this
  linarith [this, mul_assoc K ((R : ℝ) ^ m) (Real.exp (-(c * R)))]
set_option maxHeartbeats 4000000 in
private theorem curlCovariance_box_estimate {a cK CQ K c₁ C₁ W Cj₀ e₁ e₂ : ℝ} {L k : ℕ}
    {Q : IntBond → IntBond → ℝ} {Bc : IntBond → ℝ} {o : TorusSite n} {R : ℕ} {p p' : TorusPlaquette n}
    (hcK : 0 < cK) (hCQ : 0 ≤ CQ) (hK : 0 ≤ K) (hc₁ : 0 < c₁) (hC₁ : 0 ≤ C₁) (hCj : 0 ≤ Cj₀) (hR : 64 ≤ R)
    (hn : 16 * R < n)
    (hcol : ∀ u v : TorusBond n → imaginaryQuaternions, hessianForm a L k (supBall o (2 * R)) u v =
      ∑ e : Fin 3, ∑ b : TorusBond n, ∑ b' : TorusBond n,
        hessEntry a L k (supBall o (2 * R)) b b' * imaginaryComponent e (u b) * imaginaryComponent e (v b'))
    (hblind : ∀ (φ : TorusSite n → imaginaryQuaternions) (v : TorusBond n → imaginaryQuaternions),
      hessianForm a L k (supBall o (2 * R)) (latticeGrad φ) v = 0)
    (hsym : ∀ u v : TorusBond n → imaginaryQuaternions,
      hessianForm a L k (supBall o (2 * R)) u v = hessianForm a L k (supBall o (2 * R)) v u)
    (hfloor : ∀ v : TorusBond n → imaginaryQuaternions,
      2 * cK * curlNormSq (supBall o (2 * R)) v ≤ hessianForm a L k (supBall o (2 * R)) v v ∧
      hessianForm a L k (supBall o (2 * R)) v v ≤ CQ * curlNormSq (supBall o (2 * R)) v)
    (hdet : IsUnit (regularizedHessian a L k o R).det)
    (hgap : ∀ χ : TorusSite n → imaginaryQuaternions, (∀ z, z ∉ supBall o R → χ z = 0) →
      4 * ((R : ℝ) + 1)⁻¹ ^ 2 * ∑ z : TorusSite n, ‖χ z‖ ^ 2 ≤
        ∑ b : TorusBond n, ‖covariantGrad (0 : TorusBond n → imaginaryQuaternions) χ b‖ ^ 2)
    (hslice : ∀ ζ ∈ gaugeSlice o R (0 : TorusBond n → imaginaryQuaternions),
      2 * cK * ((R : ℝ) ^ 2)⁻¹ * bondNormSq (supBall o (2 * R)) ζ ≤
        hessianForm a L k (supBall o (2 * R)) ζ ζ)
    (hdecay : ∀ b b', |Q b b'| ≤ C₁ * Real.exp (-(c₁ * bondSupDist b b')))
    (hW : ∀ b₀ : IntBond, Summable (fun b => Real.exp (-(c₁ / 2 * bondSupDist b₀ b))) ∧
      ∑' b, Real.exp (-(c₁ / 2 * bondSupDist b₀ b)) ≤ W)
    (hshift : ∀ (t : Fin 4 → ℤ) (b b' : IntBond), Q (b.1 + t, b.2) (b'.1 + t, b'.2) = Q b b')
    (hclose : ∀ b b' : IntBond, BondOffsetInBox (3 * R / 2) b → BondOffsetInBox (3 * R / 2) b' →
      |hessEntry a L k (supBall o (2 * R)) (bondFrom o b) (bondFrom o b') - Q b b'| ≤ Real.exp (-(c₁ * R)))
    (hBeq : ∀ b : IntBond, HasSum (fun b' => Q b b' * Bc b') (intCurl (Pi.single b 1) (0, p'.2.1, p'.2.2)))
    (hBsz : ∀ b : IntBond, |Bc b| ≤ K * ((1 + Real.sqrt (intNormSq b.1)) ^ 3)⁻¹)
    (hBcu : ∀ (z : Fin 4 → ℤ) (m n' : Fin 4), m < n' →
      |intCurl Bc (z, m, n')| ≤ K * ((1 + Real.sqrt (intNormSq z)) ^ 4)⁻¹)
    (hIR : ∀ A : TorusBond n → imaginaryQuaternions,
      (∀ b ∈ bondsWithin (supBall o (2 * R)), ‖A b‖ ≤ (R : ℝ) ^ (3 : ℝ)) →
      (∀ η : TorusBond n → imaginaryQuaternions, (∀ b, b ∉ bondsTouching o R → η b = 0) →
        |hessianForm a L k (supBall o (2 * R)) A η| ≤ e₁ * ∑ b : TorusBond n, ‖η b‖) →
      ‖lieFormCurl A p‖ ≤ Cj₀ * Real.sqrt (((R : ℝ) ^ 4)⁻¹ * curlNormSq (supBall o R) A) + e₂)
    (hs1 : 1024 * (R : ℝ) ^ 4 * Real.exp (-(c₁ * R)) * K +
      K * C₁ * Real.exp (-(c₁ / 2 * ((R : ℝ) / 16))) * W ≤ e₁)
    (hs2 : 2 * e₁ * (4 * (2 * (R : ℝ) + 3) ^ 4 * (2 * (R : ℝ) ^ 2 / cK + K)) ≤ ((R : ℝ) ^ 4)⁻¹)
    (hs3 : 2 * (R : ℝ) ^ 2 / cK + K ≤ (R : ℝ) ^ 3)
    (hs4 : e₂ ≤ ((R : ℝ) ^ 4)⁻¹)
    (he₁ : 0 ≤ e₁)
    (hp : p ∈ plaquettesIn (supBall o ((R : ℝ) / 8))) (hp' : p' ∈ plaquettesIn (supBall o ((R : ℝ) / 8))) :
    |curlCovariance a L k o R p p' - intCurl Bc (offsetFrom o p.1 - offsetFrom o p'.1, p.2.1, p.2.2)| ≤
      (Cj₀ * Real.sqrt ((CQ * (16 * 625 * 1280 ^ 2 * K ^ 2) + 1) / cK + 2 * (16 * 625 * 1280 ^ 2 * K ^ 2)) + 1) *
        ((R : ℝ) ^ 4)⁻¹ := by
  classical
  set ρ : ℝ := (R : ℝ) with hρdef
  have hρ64 : (64 : ℝ) ≤ ρ := by rw [hρdef]; exact_mod_cast hR
  have hρ0 : 0 < ρ := by linarith
  set S := supBall o (2 * ρ) with hS
  have hmem : ∀ {q : TorusPlaquette n}, q ∈ plaquettesIn (supBall o (ρ / 8)) →
      (supDist q.1 o : ℝ) ≤ ρ / 8 ∧ q.2.1 < q.2.2 := by
    intro q hq
    simp only [plaquettesIn, Finset.mem_filter, Finset.mem_univ, true_and] at hq
    exact ⟨mem_supBall.1 (hq.2 q.1 (by simp [plaquetteVertices])), hq.1⟩
  obtain ⟨hp1, hpmn⟩ := hmem hp
  obtain ⟨hq1, hqmn⟩ := hmem hp'
  have hRr : ρ * 16 < n := by rw [hρdef]; exact_mod_cast (by omega : R * 16 < n)
  have hnear : ∀ {x : TorusSite n}, (supDist x o : ℝ) ≤ 2 * ρ → 2 * (supDist x o + 1) < n := by
    intro x hx
    have h1 : ((2 * (supDist x o + 1) : ℕ) : ℝ) < n := by
      push_cast
      linarith
    exact_mod_cast h1
  set h := offsetFrom o p'.1 with hh
  have hhs : (supNormInt h : ℝ) ≤ ρ / 8 := by rw [hh, ← supDist_eq_supNormInt]; exact hq1
  set Bh : IntBond → ℝ := fun ℓ => Bc (ℓ.1 - h, ℓ.2) with hBh
  have hKB : ∀ b, |Bc b| ≤ K := by
    intro b
    refine (hBsz b).trans ?_
    have h1 : (1 : ℝ) ≤ 1 + Real.sqrt (intNormSq b.1) := by linarith [Real.sqrt_nonneg (intNormSq b.1)]
    have h2 : ((1 + Real.sqrt (intNormSq b.1)) ^ 3)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ h1)
    calc K * ((1 + Real.sqrt (intNormSq b.1)) ^ 3)⁻¹ ≤ K * 1 := mul_le_mul_of_nonneg_left h2 hK
      _ = K := mul_one K
  have hKh : ∀ ℓ, |Bh ℓ| ≤ K := fun ℓ => hKB _
  obtain ⟨hcrit, hBsize⟩ := boxGreenColumn_spec (cK := cK) p' (by omega : 1 ≤ R) hcK hcol hblind hdet hgap hslice
  set B := boxGreenColumn a L k o R p' with hB
  have hBoff : ∀ b, b ∉ bondsTouching o R → B b = 0 := fun b hb => boxGreenColumn_of_not_mem hb
  set dn := innerCutoff ρ with hdn
  set w := shellCutoff ρ with hw
  set G : IntBond → ℝ := fun ℓ => dn ℓ * Bh ℓ with hG
  set U : IntBond → ℝ := fun ℓ => w ℓ * Bh ℓ with hU
  set A : TorusBond n → ℝ := B - onTorus o G with hA
  set u : TorusBond n → ℝ := onTorus o U with hu
  set eta : TorusBond n → ℝ := A + u with heta
  have hsumℓ : ∀ ℓ : IntBond, HasSum (fun ℓ' => Q ℓ ℓ' * Bh ℓ')
      (intCurl (Pi.single (ℓ.1 - h, ℓ.2) 1) (0, p'.2.1, p'.2.2)) := by
    intro ℓ
    let sh : IntBond ≃ IntBond := (Equiv.subRight h).prodCongr (Equiv.refl _)
    have h1 := (sh.hasSum_iff).2 (hBeq (ℓ.1 - h, ℓ.2))
    convert h1 using 1
    funext ℓ'
    have h2 := hshift (-h) ℓ ℓ'
    simp only [Function.comp, sh, Equiv.prodCongr_apply, Prod.map, Equiv.subRight_apply, Equiv.refl_apply, hBh]
    rw [← sub_eq_add_neg, ← sub_eq_add_neg] at h2
    rw [h2]
  set r₁ := 3 * R / 2 - 1 with hr₁
  set T : Finset IntBond := (Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(r₁ : ℤ)) r₁) ×ˢ Finset.univ with hTdef
  have memT : ∀ ℓ : IntBond, ℓ ∈ T ↔ supNormInt ℓ.1 ≤ r₁ := by
    intro ℓ
    simp only [hTdef, Finset.mem_product, Fintype.mem_piFinset, Finset.mem_Icc, Finset.mem_univ, and_true,
      supNormInt_le]
    refine forall_congr' fun i => ?_
    omega
  have hTcard : (T.card : ℝ) ≤ 1024 * ρ ^ 4 := by
    have h1 : T.card = (2 * r₁ + 1) ^ 4 * 4 := by
      simp only [hTdef, Finset.card_product, Fintype.card_piFinset, Int.card_Icc, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]
      congr 2
      omega
    have h2 : 2 * r₁ + 1 ≤ 4 * R := by omega
    have h3 : T.card ≤ (4 * R) ^ 4 * 4 := by
      rw [h1]
      exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h2 4)
    have h4 : (T.card : ℝ) ≤ ((4 * R) ^ 4 * 4 : ℕ) := by exact_mod_cast h3
    push_cast at h4
    have e : (4 * ρ) ^ 4 * 4 = 1024 * ρ ^ 4 := by ring
    rw [← e]
    exact h4
  have hbox : ∀ ℓ : IntBond, supNormInt ℓ.1 ≤ 3 * R / 2 - 1 → BondOffsetInBox (3 * R / 2) ℓ := by
    intro ℓ hℓ
    have h2 := supNormInt_add ℓ.1 (Pi.single ℓ.2 1)
    have h3 := supNormInt_single ℓ.2
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have := le_supNormInt ℓ.1 i
      rw [Int.abs_eq_natAbs]
      omega
    · have := le_supNormInt (ℓ.1 + Pi.single ℓ.2 1) i
      rw [Int.abs_eq_natAbs]
      omega
  have hTb : ∀ ℓ ∈ T, toIntBond o (bondFrom o ℓ) = ℓ := by
    intro ℓ hℓ
    have h1 := (memT ℓ).1 hℓ
    have h2 : offsetFrom o (bondFrom o ℓ).1 = ℓ.1 := by
      apply offsetFrom_eq rfl
      intro i
      have := le_supNormInt ℓ.1 i
      omega
    simp only [toIntBond, h2]
    rfl
  have hT : ∀ ℓ', ℓ' ∉ T → dn ℓ' = 0 := by
    intro ℓ' hℓ'
    rw [memT, not_le] at hℓ'
    apply innerCutoff_eq_zero hρ0
    have h1 : 5 * R ≤ 4 * supNormInt ℓ'.1 := by omega
    have h2 : (5 * ρ) ≤ 4 * supNormInt ℓ'.1 := by rw [hρdef]; exact_mod_cast h1
    simp only [bondSupNorm]
    linarith
  have hdn0 : ∀ ℓ', 0 ≤ dn ℓ' := fun ℓ' => clampUnit_nonneg _
  have hdn1 : ∀ ℓ', dn ℓ' ≤ 1 := fun ℓ' => clampUnit_le_one _
  have hrow : ∀ b ∈ bondsTouching o R,
      |∑ b' : TorusBond n, hessEntry a L k S b b' * onTorus o G b' - curlCoeff p' b| ≤ e₁ := by
    intro b hb
    have hnearb := (touching_near hb).1
    have hℓ : supNormInt (toIntBond o b).1 ≤ R + 1 := by
      have : supNormInt (toIntBond o b).1 = supDist b.1 o := rfl
      omega
    have hDpos : (0 : ℝ) ≤ ρ / 16 := by positivity
    have h1 := row_sum_estimate (n := n) (o := o) (row := fun b' => hessEntry a L k S b b') (ℓ := toIntBond o b)
      (Bh := Bh) (χ := dn)
      (c' := intCurl (Pi.single ((toIntBond o b).1 - h, (toIntBond o b).2) 1) (0, p'.2.1, p'.2.2))
      (ε₀ := Real.exp (-(c₁ * R))) (D := ρ / 16)
      hc₁ hK hC₁ hdecay hW (hsumℓ _) hKh hdn0 hdn1 T hT hTb
      (fun ℓ' hℓ' => by
        have h2 := hclose (toIntBond o b) ℓ' (hbox _ (by omega)) (hbox _ ((memT ℓ').1 hℓ'))
        rwa [bondFrom_toIntBond] at h2)
      (fun ℓ' hne => by
        have h2 : 9 * ρ / 8 < bondSupNorm ℓ' := by
          by_contra hc
          exact hne (innerCutoff_eq_one hρ0 (not_lt.1 hc))
        have h3 := supNormInt_sub (toIntBond o b).1 ((toIntBond o b).1 - ℓ'.1)
        have e : (toIntBond o b).1 - ((toIntBond o b).1 - ℓ'.1) = ℓ'.1 := by abel
        rw [e] at h3
        have h4 : supNormInt ((toIntBond o b).1 - ℓ'.1) = bondSupDist (toIntBond o b) ℓ' := rfl
        rw [h4] at h3
        have h5 : (supNormInt ℓ'.1 : ℝ) ≤ ((R + 1 : ℕ) : ℝ) + bondSupDist (toIntBond o b) ℓ' := by
          exact_mod_cast (by omega : supNormInt ℓ'.1 ≤ R + 1 + bondSupDist (toIntBond o b) ℓ')
        have h6 : bondSupNorm ℓ' = supNormInt ℓ'.1 := rfl
        push_cast at h5
        linarith)
    rw [← curlCoeff_eq_intCurl b (hnear (by linarith [hq1]))] at h1
    refine h1.trans (le_trans ?_ hs1)
    have h7 : (T.card : ℝ) * Real.exp (-(c₁ * R)) * K ≤ 1024 * ρ ^ 4 * Real.exp (-(c₁ * R)) * K :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hTcard (Real.exp_pos _).le) hK
    linarith
  have hqcut : ∀ f g : TorusBond n → ℝ, realHess a L k S f g = hessianForm a L k S (liftReal f) (liftReal g) := by
    intro f g
    rw [hessianForm_liftReal hcol]
    simp only [component_liftReal]
  have hqsym : ∀ f g : TorusBond n → ℝ, realHess a L k S f g = realHess a L k S g f := by
    intro f g
    rw [hqcut, hqcut, hsym]
  have hqfl : ∀ v : TorusBond n → ℝ, 2 * cK * ∑ p ∈ plaquettesIn S, realCurl v p ^ 2 ≤ realHess a L k S v v ∧
      realHess a L k S v v ≤ CQ * ∑ p ∈ plaquettesIn S, realCurl v p ^ 2 := by
    intro v
    have := hfloor (liftReal v)
    rw [curlNormSq_liftReal, ← hqcut] at this
    exact this
  have hcritA : ∀ η : TorusBond n → ℝ, (∀ b, b ∉ bondsTouching o R → η b = 0) →
      |realHess a L k S η A| ≤ e₁ * ∑ b : TorusBond n, |η b| := by
    intro η hη
    have e1 : realHess a L k S η A = realCurl η p' - realHess a L k S η (onTorus o G) := by
      rw [hA, realHess_sub_right, hcrit η hη]
    have e2 : realCurl η p' - realHess a L k S η (onTorus o G) =
        ∑ b : TorusBond n, η b * (curlCoeff p' b - ∑ b' : TorusBond n, hessEntry a L k S b b' * onTorus o G b') := by
      rw [← sum_curlCoeff_mul]
      simp only [realHess]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      have : ∑ b' : TorusBond n, hessEntry a L k S b b' * η b * onTorus o G b' =
          η b * ∑ b' : TorusBond n, hessEntry a L k S b b' * onTorus o G b' := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b' _ => ?_
        ring
      rw [this]
      ring
    rw [e1, e2]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b _ => ?_
    by_cases hb : b ∈ bondsTouching o R
    · rw [abs_mul, mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      rw [abs_sub_comm]
      exact hrow b hb
    · simp [hη b hb]
  have hetaform : ∀ b, eta b = B b - (dn (toIntBond o b) - w (toIntBond o b)) * Bh (toIntBond o b) := by
    intro b
    simp only [heta, hA, hu, onTorus, hG, hU, Pi.add_apply, Pi.sub_apply]
    ring
  have hwd : ∀ ℓ, w ℓ ≤ dn ℓ := fun ℓ => min_le_right _ _
  have hw0 : ∀ ℓ, 0 ≤ w ℓ := fun ℓ => shellCutoff_nonneg ρ ℓ
  have hetaoff : ∀ b, b ∉ bondsTouching o R → eta b = 0 := by
    intro b hb
    have h1 : b.1 ∉ supBall o ρ := fun h' => hb (by simp [bondsTouching, hρdef ▸ h'])
    have h2 : ρ < bondSupNorm (toIntBond o b) := by
      have := mem_supBall.not.1 h1
      have e : bondSupNorm (toIntBond o b) = supDist b.1 o := rfl
      rw [e]
      exact not_le.1 this
    have h3 : outerCutoff ρ (toIntBond o b) = 1 := outerCutoff_eq_one hρ0 (by linarith)
    have h4 : w (toIntBond o b) = dn (toIntBond o b) := by
      simp only [hw, shellCutoff, h3]
      exact min_eq_right (hdn1 _)
    rw [hetaform, hBoff b hb, h4]
    ring
  have hetasz : ∀ b, |eta b| ≤ 2 * ρ ^ 2 / cK + K := by
    intro b
    rw [hetaform]
    refine (abs_sub _ _).trans (add_le_add (hBsize b) ?_)
    rw [abs_mul]
    have h1 : |dn (toIntBond o b) - w (toIntBond o b)| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hdn0 (toIntBond o b), hdn1 (toIntBond o b), hw0 (toIntBond o b),
        hwd (toIntBond o b)]
    calc |dn (toIntBond o b) - w (toIntBond o b)| * |Bh (toIntBond o b)| ≤ 1 * K :=
          mul_le_mul h1 (hKh _) (abs_nonneg _) zero_le_one
      _ = K := one_mul K
  have hcardin : ((bondsTouching o R).card : ℝ) ≤ 4 * (2 * ρ + 3) ^ 4 := by
    have hsub : bondsTouching o R ⊆ (supBall o ((R + 1 : ℕ) : ℝ)) ×ˢ (Finset.univ : Finset (Fin 4)) := by
      intro b hb
      have := (touching_near hb).1
      rcases b with ⟨b1, b2⟩
      simp only [Finset.mem_product, Finset.mem_univ, and_true, mem_supBall]
      exact_mod_cast this
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_product] at h1
    have h2 := card_supBall_le o (R + 1)
    simp only [Finset.card_univ, Fintype.card_fin] at h1
    have h3 : (bondsTouching o R).card ≤ (2 * (R + 1) + 1) ^ 4 * 4 := h1.trans (Nat.mul_le_mul_right _ h2)
    have h4 : ((bondsTouching o R).card : ℝ) ≤ (((2 * (R + 1) + 1) ^ 4 * 4 : ℕ) : ℝ) := by exact_mod_cast h3
    push_cast at h4
    rw [hρdef]
    have e : (2 * ((R : ℝ) + 1) + 1) ^ 4 * 4 = 4 * (2 * (R : ℝ) + 3) ^ 4 := by ring
    linarith
  have hnorm1 : ∑ b : TorusBond n, |eta b| ≤ 4 * (2 * ρ + 3) ^ 4 * (2 * ρ ^ 2 / cK + K) := by
    rw [← Finset.sum_subset (Finset.subset_univ (bondsTouching o R)) (fun b _ hb => by simp [hetaoff b hb])]
    refine (Finset.sum_le_card_nsmul _ _ _ fun b _ => hetasz b).trans ?_
    rw [nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hcardin (by positivity)
  have hcu : ∀ q ∈ plaquettesIn S, |realCurl u q| ≤ 1280 * K * (ρ ^ 4)⁻¹ := by
    intro q hq
    have hq' := hq
    simp only [plaquettesIn, Finset.mem_filter, Finset.mem_univ, true_and] at hq'
    have h1 : (supDist q.1 o : ℝ) ≤ 2 * ρ := mem_supBall.1 (hq'.2 q.1 (by simp [plaquetteVertices]))
    rw [hu, realCurl_onTorus o U q (hnear h1)]
    exact curl_shell_bound hK (by linarith) hhs hBsz hBcu _ _ _ hq'.1
  have hcardp : ((plaquettesIn S).card : ℝ) ≤ 16 * (5 * ρ) ^ 4 := by
    have hsub : plaquettesIn S ⊆ S ×ˢ ((Finset.univ : Finset (Fin 4)) ×ˢ (Finset.univ : Finset (Fin 4))) := by
      intro q hq
      simp only [plaquettesIn, Finset.mem_filter, Finset.mem_univ, true_and] at hq
      simp only [Finset.mem_product, Finset.mem_univ, and_true]
      exact hq.2 q.1 (by simp [plaquetteVertices])
    have h1 := Finset.card_le_card hsub
    simp only [Finset.card_product, Finset.card_univ, Fintype.card_fin] at h1
    have hS2 : S = supBall o ((2 * R : ℕ) : ℝ) := by
      rw [hS, hρdef]
      push_cast
      rfl
    have h2 : S.card ≤ (2 * (2 * R) + 1) ^ 4 := by
      rw [hS2]
      exact card_supBall_le o (2 * R)
    have h3 : (plaquettesIn S).card ≤ (2 * (2 * R) + 1) ^ 4 * 16 := h1.trans (Nat.mul_le_mul_right _ h2)
    have h4 : (2 * (2 * R) + 1) ^ 4 * 16 ≤ (5 * R) ^ 4 * 16 :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) 4)
    have h5 : ((plaquettesIn S).card : ℝ) ≤ (((5 * R) ^ 4 * 16 : ℕ) : ℝ) := by exact_mod_cast h3.trans h4
    push_cast at h5
    rw [hρdef]
    linarith
  set K₃ : ℝ := 16 * 625 * 1280 ^ 2 * K ^ 2 with hK₃
  have hK₃0 : 0 ≤ K₃ := by positivity
  have hρ4 : 0 < ρ ^ 4 := by positivity
  have hcus : ∑ q ∈ plaquettesIn S, realCurl u q ^ 2 ≤ K₃ * (ρ ^ 4)⁻¹ := by
    have h1 : ∀ q ∈ plaquettesIn S, realCurl u q ^ 2 ≤ (1280 * K * (ρ ^ 4)⁻¹) ^ 2 := by
      intro q hq
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hcu q hq) 2
    refine (Finset.sum_le_card_nsmul _ _ _ h1).trans ?_
    rw [nsmul_eq_mul]
    have h2 : ((plaquettesIn S).card : ℝ) * (1280 * K * (ρ ^ 4)⁻¹) ^ 2 ≤
        16 * (5 * ρ) ^ 4 * (1280 * K * (ρ ^ 4)⁻¹) ^ 2 :=
      mul_le_mul_of_nonneg_right hcardp (by positivity)
    refine h2.trans (le_of_eq ?_)
    rw [hK₃]
    field_simp
    ring
  have hX : realHess a L k S eta eta ≤ 2 * |realHess a L k S eta A| + realHess a L k S u u := by
    have e3 : realHess a L k S eta eta = realHess a L k S eta A + realHess a L k S eta u := by
      conv_lhs => rw [show eta = eta from rfl]
      rw [← realHess_add_right]
    have hnn : 0 ≤ realHess a L k S (eta - u) (eta - u) := by
      have h1 := (hqfl (eta - u)).1
      have h2 : 0 ≤ ∑ p ∈ plaquettesIn S, realCurl (eta - u) p ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      have h3 : 0 ≤ 2 * cK * ∑ p ∈ plaquettesIn S, realCurl (eta - u) p ^ 2 := by positivity
      linarith
    have e4 : realHess a L k S (eta - u) (eta - u) =
        realHess a L k S eta eta - realHess a L k S eta u - realHess a L k S eta u + realHess a L k S u u := by
      rw [realHess_sub_left, realHess_sub_right, realHess_sub_right, hqsym u eta]
      ring
    have := le_abs_self (realHess a L k S eta A)
    linarith
  have hen : 2 * cK * ∑ q ∈ plaquettesIn S, realCurl eta q ^ 2 ≤ (1 + CQ * K₃) * (ρ ^ 4)⁻¹ := by
    have h1 := (hqfl eta).1
    have h2 := (hqfl u).2
    have h3 := hcritA eta hetaoff
    have h4 : 2 * (e₁ * ∑ b : TorusBond n, |eta b|) ≤ (ρ ^ 4)⁻¹ := by
      refine le_trans ?_ hs2
      have := mul_le_mul_of_nonneg_left hnorm1 he₁
      linarith
    have h5 := mul_le_mul_of_nonneg_left hcus hCQ
    have e : (1 + CQ * K₃) * (ρ ^ 4)⁻¹ = (ρ ^ 4)⁻¹ + CQ * (K₃ * (ρ ^ 4)⁻¹) := by ring
    rw [e]
    linarith
  have hsplit : ∀ q, realCurl A q = realCurl eta q - realCurl u q := by
    intro q
    simp only [realCurl, heta, Pi.add_apply]
    ring
  have hAS : ∑ q ∈ plaquettesIn S, realCurl A q ^ 2 ≤ ((CQ * K₃ + 1) / cK + 2 * K₃) * (ρ ^ 4)⁻¹ := by
    have h1 : ∑ q ∈ plaquettesIn S, realCurl A q ^ 2 ≤
        2 * ∑ q ∈ plaquettesIn S, realCurl eta q ^ 2 + 2 * ∑ q ∈ plaquettesIn S, realCurl u q ^ 2 := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun q _ => ?_
      rw [hsplit]
      have := sq_nonneg (realCurl eta q + realCurl u q)
      linarith
    have h2 : 2 * ∑ q ∈ plaquettesIn S, realCurl eta q ^ 2 ≤ (CQ * K₃ + 1) / cK * (ρ ^ 4)⁻¹ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hcK]
      linarith
    have e : ((CQ * K₃ + 1) / cK + 2 * K₃) * (ρ ^ 4)⁻¹ =
        (CQ * K₃ + 1) / cK * (ρ ^ 4)⁻¹ + 2 * (K₃ * (ρ ^ 4)⁻¹) := by ring
    rw [e]
    linarith
  have hsubp : plaquettesIn (supBall o ρ) ⊆ plaquettesIn S := by
    intro q hq
    simp only [plaquettesIn, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    refine ⟨hq.1, fun z hz => ?_⟩
    have := mem_supBall.1 (hq.2 z hz)
    exact mem_supBall.2 (by linarith)
  have hAR : curlNormSq (supBall o ρ) (liftReal A) ≤ ((CQ * K₃ + 1) / cK + 2 * K₃) * (ρ ^ 4)⁻¹ := by
    rw [curlNormSq_liftReal]
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsubp fun _ _ _ => sq_nonneg _).trans hAS
  have hsize : ∀ b ∈ bondsWithin S, ‖liftReal A b‖ ≤ ρ ^ (3 : ℝ) := by
    intro b _
    have e : ρ ^ (3 : ℝ) = ρ ^ 3 := by
      rw [← Real.rpow_natCast]
      norm_num
    rw [e]
    simp only [liftReal]
    rw [norm_smul, norm_unitI, mul_one, Real.norm_eq_abs]
    refine le_trans ?_ hs3
    simp only [hA, Pi.sub_apply, onTorus, hG]
    refine (abs_sub _ _).trans (add_le_add (hBsize b) ?_)
    rw [abs_mul]
    have h1 : |dn (toIntBond o b)| ≤ 1 := by rw [abs_of_nonneg (hdn0 _)]; exact hdn1 _
    calc |dn (toIntBond o b)| * |Bh (toIntBond o b)| ≤ 1 * K := mul_le_mul h1 (hKh _) (abs_nonneg _) zero_le_one
      _ = K := one_mul K
  have hcritL : ∀ η : TorusBond n → imaginaryQuaternions, (∀ b, b ∉ bondsTouching o R → η b = 0) →
      |hessianForm a L k S (liftReal A) η| ≤ e₁ * ∑ b : TorusBond n, ‖η b‖ := by
    intro η hη
    rw [hessianForm_liftReal hcol, hqsym]
    refine (hcritA _ fun b hb => by simp [hη b hb, imaginaryComponent]).trans ?_
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b _ => abs_component_le_norm _) he₁
  have hfin := hIR (liftReal A) hsize hcritL
  rw [norm_lieFormCurl_liftReal] at hfin
  have hx := hnear (x := p.1) (by linarith)
  have hGcurl : realCurl (onTorus o G) p = intCurl Bc (offsetFrom o p.1 - h, p.2.1, p.2.2) := by
    rw [realCurl_onTorus o G p hx]
    set x := offsetFrom o p.1 with hxd
    have hxs : bondSupNorm (x, p.2.1) ≤ ρ / 8 := hp1
    have d1 : ∀ j : Fin 4, dn (x, j) = 1 := fun j => innerCutoff_eq_one hρ0 (by
      have : bondSupNorm (x, j) = bondSupNorm (x, p.2.1) := rfl
      linarith)
    have d2 : ∀ i j : Fin 4, dn (x + Pi.single i 1, j) = 1 := fun i j => innerCutoff_eq_one hρ0 (by
      have h1 := abs_le.1 (bondSupNorm_step x i j p.2.1)
      linarith [h1.2])
    simp only [intCurl, hG, d1, d2, one_mul, hBh]
    have e2 : ∀ i : Fin 4, x + Pi.single i (1 : ℤ) - h = x - h + Pi.single i 1 := fun i => by abel
    simp only [e2]
  have hfinal : realCurl A p =
      curlCovariance a L k o R p p' - intCurl Bc (offsetFrom o p.1 - h, p.2.1, p.2.2) := by
    rw [curlCovariance_eq_realCurl, ← hGcurl]
    simp only [realCurl, hA, Pi.sub_apply]
    ring
  rw [hfinal] at hfin
  refine hfin.trans ?_
  have hsq : Real.sqrt ((ρ ^ 4)⁻¹ * curlNormSq (supBall o ρ) (liftReal A)) ≤
      Real.sqrt ((CQ * K₃ + 1) / cK + 2 * K₃) * (ρ ^ 4)⁻¹ := by
    have hKK : 0 ≤ (CQ * K₃ + 1) / cK + 2 * K₃ := by positivity
    have h1 : (ρ ^ 4)⁻¹ * curlNormSq (supBall o ρ) (liftReal A) ≤
        ((CQ * K₃ + 1) / cK + 2 * K₃) * ((ρ ^ 4)⁻¹) ^ 2 := by
      have := mul_le_mul_of_nonneg_left hAR (by positivity : 0 ≤ (ρ ^ 4)⁻¹)
      have e : (ρ ^ 4)⁻¹ * (((CQ * K₃ + 1) / cK + 2 * K₃) * (ρ ^ 4)⁻¹) =
          ((CQ * K₃ + 1) / cK + 2 * K₃) * ((ρ ^ 4)⁻¹) ^ 2 := by ring
      linarith
    refine (Real.sqrt_le_sqrt h1).trans ?_
    rw [Real.sqrt_mul hKK, Real.sqrt_sq (by positivity)]
  have := mul_le_mul_of_nonneg_left hsq hCj
  have e : (Cj₀ * Real.sqrt ((CQ * K₃ + 1) / cK + 2 * K₃) + 1) * (ρ ^ 4)⁻¹ =
      Cj₀ * (Real.sqrt ((CQ * K₃ + 1) / cK + 2 * K₃) * (ρ ^ 4)⁻¹) + (ρ ^ 4)⁻¹ := by ring
  rw [e]
  linarith
private theorem isAxialSmall_zero {o : TorusSite n} {R : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) :
    IsAxialSmall o R δ (0 : TorusBond n → imaginaryQuaternions) := by
  have hplaq : ∀ (x : TorusSite n) (μ ν : Fin 4),
      curvature (exponentialField (0 : TorusBond n → imaginaryQuaternions)) x μ ν = 0 := by
    intro x μ ν
    simp [curvature, holonomy, exponentialField, expUnit_zero]
  refine ⟨fun p _ => ?_, fun b _ => ?_, ?_, ?_⟩
  · rw [hplaq]; exact hδ
  · simp only [Pi.zero_apply, norm_zero]; positivity
  · have : curlNormSq (supBall o (2 * R)) (0 : TorusBond n → imaginaryQuaternions) = 0 := by
      simp [curlNormSq, lieFormCurl]
    rw [this]; positivity
  · have : bondNormSq (supBall o (2 * R)) (0 : TorusBond n → imaginaryQuaternions) = 0 := by
      simp [bondNormSq]
    rw [this]; positivity
abbrev _root_.YangMills.SharedProofs.p91808 := @isAxialSmall_zero
private theorem boxRadius_pow {R : ℕ} (hR : 1 ≤ R) : boxRadius (1 / 27) ((R : ℝ) ^ 27) = R := by
  have h : ((R : ℝ) ^ 27) ^ ((1 : ℝ) / 27) = R := by
    have := Real.pow_rpow_inv_natCast (x := (R : ℝ)) (n := 27) (by positivity) (by norm_num)
    simpa using this
  unfold boxRadius
  rw [h]
  exact Nat.ceil_natCast R
private theorem boxScale_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ boxScale x := by
  have h1 : 0 ≤ Real.log x := Real.log_nonneg hx
  simp only [boxScale]
  positivity
abbrev _root_.YangMills.SharedProofs.p57587 := @boxScale_nonneg
private theorem curlCovariance_near_maxwell_core (Tb : ParameterAssignment) (hD : Tb.Admissible)
    (hI : ∀ Cp c : ℝ, 0 < c → ∀ j : ℕ, ∃ (C c' : ℝ) (R₀ : ℕ), 0 < c' ∧
      ∀ (k n : ℕ) [NeZero n] (o : TorusSite n) (R : ℕ) (A : TorusBond n → imaginaryQuaternions), R₀ ≤ R → 16 * R < n →
      (∀ b ∈ bondsWithin (supBall o (2 * R)), ‖A b‖ ≤ (R : ℝ) ^ Cp) →
      (∀ η : TorusBond n → imaginaryQuaternions, (∀ b, b ∉ bondsTouching o R → η b = 0) →
        |hessianForm Tb.coupling Tb.side k (supBall o (2 * R)) A η| ≤
          Real.exp (-(c * R)) * ∑ b : TorusBond n, ‖η b‖) →
      ∀ (l : List (Fin 4)), l.length = j → ∀ p ∈ plaquettesIn (supBall o ((R : ℝ) / 4)),
        ‖iteratedDiff l (lieFormCurl A) p‖ ≤
          C * ((R : ℝ) ^ j)⁻¹ *
              Real.sqrt (((R : ℝ) ^ 4)⁻¹ * curlNormSq (supBall o R) A) + Real.exp (-(c' * R)))
    (hC : ∀ c₁ C₁ : ℝ, 0 < c₁ → ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (Q : IntBond → IntBond → ℝ),
      IsLimitForm Tb.coupling Tb.coercivity c₁ C₁ Tb.side k Q → ∀ r s : Fin 4, r < s → ∃ B : IntBond → ℝ,
      (∀ b : IntBond, HasSum (fun b' => Q b b' * B b') (intCurl (Pi.single b 1) (0, r, s))) ∧
      (∀ b : IntBond, |B b| ≤ C * ((1 + Real.sqrt (intNormSq b.1)) ^ 3)⁻¹) ∧
      ∀ (z : Fin 4 → ℤ) (m n' : Fin 4), m < n' →
        |intCurl B (z, m, n')| ≤ C * ((1 + Real.sqrt (intNormSq z)) ^ 4)⁻¹ ∧
        (z ≠ 0 → |intCurl B (z, m, n') - maxwellKernel z m n' r s| ≤
          C * ((1 + Real.sqrt (intNormSq z)) ^ 5)⁻¹))
    (h1 : cubeLimitFormStatement) (h2 : cubeHessianStatement) (h4 : curlCovarianceBoundsStatement)
    (h5 : ellipsoidBoundsStatement) (h6 : covariantGradientGapStatement) :
    ∃ (C : ℝ) (R₀ : ℕ), ∀ (k n : ℕ) [NeZero n] (o : TorusSite n) (R : ℕ), R₀ ≤ R → 16 * R < n →
      ∀ p ∈ plaquettesIn (supBall o ((R : ℝ) / 8)), ∀ p' ∈ plaquettesIn (supBall o ((R : ℝ) / 8)),
      ∀ z : Fin 4 → ℤ, (∀ i, z i = ((p.1 - p'.1) i).valMinAbs) → z ≠ 0 →
        |curlCovariance Tb.coupling Tb.side k o R p p' - maxwellKernel z p.2.1 p.2.2 p'.2.1 p'.2.2| ≤
          C * ((1 + Real.sqrt (intNormSq z)) ^ 5)⁻¹ + C * ((R : ℝ) ^ 4)⁻¹ := by
  obtain ⟨c₁, C₁, R₁, hc₁, hL⟩ := h1 Tb hD
  obtain ⟨K, hK, hCol⟩ := hC c₁ C₁ hc₁
  obtain ⟨CQ, R₂, hCQ, hF⟩ := h2 Tb hD
  obtain ⟨R₃, hB⟩ := h4 Tb hD
  obtain ⟨Ke, xs, _, hE⟩ := h5 Tb hD (1 / 27) (by norm_num) (by norm_num) 1 one_pos
  have hcK := hD.cK_pos
  set c₂ := c₁ / 64 with hc₂
  have hc₂0 : 0 < c₂ := by positivity
  obtain ⟨Ci, c', R₄, hc', hI'⟩ := hI 3 c₂ hc₂0 0
  obtain ⟨W, hW0, hW⟩ := exp_bondSupDist_summable (c := c₁ / 2) (by positivity)
  obtain ⟨R₅, hR₅⟩ := pow_mul_exp_eventually_le (2048 * K) (c₁ - c₂) 4 (by rw [hc₂]; linarith)
  obtain ⟨R₆, hR₆⟩ := pow_mul_exp_eventually_le (2 * K * C₁ * W) (c₁ / 64) 0 (by positivity)
  obtain ⟨R₇, hR₇⟩ := pow_mul_exp_eventually_le (5000 * (2 / Tb.coercivity + K)) c₂ 10 hc₂0
  obtain ⟨R₈, hR₈⟩ := pow_mul_exp_eventually_le 1 c' 4 hc'
  set K₃ : ℝ := 16 * 625 * 1280 ^ 2 * K ^ 2 with hK₃
  set K₄ : ℝ := (CQ * K₃ + 1) / Tb.coercivity + 2 * K₃ with hK₄
  set Cf : ℝ := |Ci| * Real.sqrt K₄ + 1 with hCf
  have hCf0 : 0 ≤ Cf := by positivity
  refine ⟨K + Cf, max (max (max (max R₁ R₂) (max R₃ R₄)) (max (max R₅ R₆) (max R₇ R₈)))
    (max (max 64 ⌈2 / Tb.coercivity + K⌉₊) ⌈xs⌉₊), ?_⟩
  intro k n _ o R hR hn p hp p' hp' z hz hz0
  simp only [max_le_iff] at hR
  obtain ⟨⟨⟨⟨hR1, hR2⟩, hR3, hR4⟩, ⟨hR5, hR6⟩, hR7, hR8⟩, ⟨hR64, hRc⟩, hRx⟩ := hR
  obtain ⟨Q, hQ, hcl⟩ := hL k
  have hC₁ : 0 ≤ C₁ := by
    have := hQ.decay ((0 : Fin 4 → ℤ), (0 : Fin 4)) ((0 : Fin 4 → ℤ), (0 : Fin 4))
    have h2 := (abs_nonneg _).trans this
    exact nonneg_of_mul_nonneg_left h2 (Real.exp_pos _)
  have hq' := hp'
  simp only [plaquettesIn, Finset.mem_filter, Finset.mem_univ, true_and] at hq'
  have hqp := hp
  simp only [plaquettesIn, Finset.mem_filter, Finset.mem_univ, true_and] at hqp
  obtain ⟨Bc, hB1, hB2, hB3⟩ := hCol k Q hQ p'.2.1 p'.2.2 hq'.1
  obtain ⟨_, _, hsym, _, hfl, hbl, hcolor⟩ := hF k n o R hR2 hn
  obtain ⟨hdet, _, _⟩ := hB k n o R hR3 hn
  have hR1' : 1 ≤ R := by omega
  have hρ1 : (1 : ℝ) ≤ R := by exact_mod_cast hR1'
  have hgap := (h6 n o R hR1' (by omega) 0).1
  have hx1 : (1 : ℝ) ≤ (R : ℝ) ^ 27 := one_le_pow₀ hρ1
  have hxs : xs ≤ (R : ℝ) ^ 27 := by
    have h7 : xs ≤ R := (Nat.le_ceil xs).trans (by exact_mod_cast hRx)
    have h8 : (R : ℝ) ≤ (R : ℝ) ^ 27 := le_self_pow₀ hρ1 (by norm_num)
    linarith
  have hslice := (hE ((R : ℝ) ^ 27) R k n o 0 hxs (boxRadius_pow hR1').symm hn
    (isAxialSmall_zero (boxScale_nonneg hx1))).1
  set e₁ := Real.exp (-(c₂ * R)) with he₁
  have hIR : ∀ A : TorusBond n → imaginaryQuaternions,
      (∀ b ∈ bondsWithin (supBall o (2 * R)), ‖A b‖ ≤ (R : ℝ) ^ (3 : ℝ)) →
      (∀ η : TorusBond n → imaginaryQuaternions, (∀ b, b ∉ bondsTouching o R → η b = 0) →
        |hessianForm Tb.coupling Tb.side k (supBall o (2 * R)) A η| ≤ e₁ * ∑ b : TorusBond n, ‖η b‖) →
      ‖lieFormCurl A p‖ ≤
        |Ci| * Real.sqrt (((R : ℝ) ^ 4)⁻¹ * curlNormSq (supBall o R) A) + Real.exp (-(c' * R)) := by
    intro A hs hc
    have hp4 : p ∈ plaquettesIn (supBall o ((R : ℝ) / 4)) := by
      simp only [plaquettesIn, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hqp.1, fun y hy => ?_⟩
      have := mem_supBall.1 (hqp.2 y hy)
      exact mem_supBall.2 (by linarith)
    have h8 := hI' k n o R A hR4 hn hs hc [] rfl p hp4
    simp only [iteratedDiff, List.foldr_nil, pow_zero, inv_one, mul_one] at h8
    refine h8.trans ?_
    have := mul_le_mul_of_nonneg_right (le_abs_self Ci)
      (Real.sqrt_nonneg (((R : ℝ) ^ 4)⁻¹ * curlNormSq (supBall o R) A))
    linarith
  have hρpos : (0 : ℝ) < R := by linarith
  have hexp : ∀ u v : ℝ, Real.exp (-(u * R)) = Real.exp (-((u - v) * R)) * Real.exp (-(v * R)) := by
    intro u v
    rw [← Real.exp_add]
    congr 1
    ring
  have hs1 : 1024 * (R : ℝ) ^ 4 * Real.exp (-(c₁ * R)) * K +
      K * C₁ * Real.exp (-(c₁ / 2 * ((R : ℝ) / 16))) * W ≤ e₁ := by
    have a1 := hR₅ R hR5
    have a2 := hR₆ R hR6
    simp only [pow_zero, mul_one] at a2
    have e0 : 0 < e₁ := Real.exp_pos _
    have b1 : 1024 * (R : ℝ) ^ 4 * Real.exp (-(c₁ * R)) * K ≤ e₁ / 2 := by
      rw [hexp c₁ c₂]
      have := mul_le_mul_of_nonneg_right a1 e0.le
      linarith
    have b2 : K * C₁ * Real.exp (-(c₁ / 2 * ((R : ℝ) / 16))) * W ≤ e₁ / 2 := by
      have e : Real.exp (-(c₁ / 2 * ((R : ℝ) / 16))) = Real.exp (-(c₁ / 64 * R)) * e₁ := by
        rw [he₁, ← Real.exp_add]
        congr 1
        rw [hc₂]
        ring
      rw [e]
      have := mul_le_mul_of_nonneg_right a2 e0.le
      linarith
    linarith
  have hs2 : 2 * e₁ * (4 * (2 * (R : ℝ) + 3) ^ 4 * (2 * (R : ℝ) ^ 2 / Tb.coercivity + K)) ≤ ((R : ℝ) ^ 4)⁻¹ := by
    have a1 := hR₇ R hR7
    have hR64' : (64 : ℝ) ≤ R := by exact_mod_cast hR64
    have b1 : (2 * (R : ℝ) + 3) ^ 4 ≤ (5 * (R : ℝ)) ^ 4 := pow_le_pow_left₀ (by positivity) (by linarith) 4
    have b2 : 2 * (R : ℝ) ^ 2 / Tb.coercivity + K ≤ (2 / Tb.coercivity + K) * (R : ℝ) ^ 2 := by
      have h0 : 0 ≤ (R : ℝ) ^ 2 - 1 := by nlinarith
      have e : (2 / Tb.coercivity + K) * (R : ℝ) ^ 2 = 2 * (R : ℝ) ^ 2 / Tb.coercivity + K * (R : ℝ) ^ 2 := by ring
      rw [e]
      nlinarith
    have e0 : 0 < e₁ := Real.exp_pos _
    have hq0 : 0 ≤ 2 / Tb.coercivity + K := by positivity
    rw [← one_div, le_div_iff₀ (by positivity)]
    have b3 : 4 * (2 * (R : ℝ) + 3) ^ 4 * (2 * (R : ℝ) ^ 2 / Tb.coercivity + K) ≤
        4 * (5 * (R : ℝ)) ^ 4 * ((2 / Tb.coercivity + K) * (R : ℝ) ^ 2) :=
      mul_le_mul (by linarith) b2 (by positivity) (by positivity)
    have b4 := mul_le_mul_of_nonneg_left b3 (by positivity : 0 ≤ 2 * e₁ * (R : ℝ) ^ 4)
    calc 2 * e₁ * (4 * (2 * (R : ℝ) + 3) ^ 4 * (2 * (R : ℝ) ^ 2 / Tb.coercivity + K)) * (R : ℝ) ^ 4
        = 2 * e₁ * (R : ℝ) ^ 4 * (4 * (2 * (R : ℝ) + 3) ^ 4 * (2 * (R : ℝ) ^ 2 / Tb.coercivity + K)) := by ring
      _ ≤ 2 * e₁ * (R : ℝ) ^ 4 * (4 * (5 * (R : ℝ)) ^ 4 * ((2 / Tb.coercivity + K) * (R : ℝ) ^ 2)) := b4
      _ = 5000 * (2 / Tb.coercivity + K) * (R : ℝ) ^ 10 * e₁ := by ring
      _ ≤ 1 := a1
  have hs3 : 2 * (R : ℝ) ^ 2 / Tb.coercivity + K ≤ (R : ℝ) ^ 3 := by
    have h7 : 2 / Tb.coercivity + K ≤ R := (Nat.le_ceil _).trans (by exact_mod_cast hRc)
    have h8 : (0 : ℝ) ≤ (R : ℝ) ^ 2 := by positivity
    have h9 : K ≤ K * (R : ℝ) ^ 2 := le_mul_of_one_le_right hK (one_le_pow₀ hρ1)
    have h10 := mul_le_mul_of_nonneg_right h7 h8
    have e : (R : ℝ) ^ 3 = (R : ℝ) * (R : ℝ) ^ 2 := by ring
    have e2 : 2 * (R : ℝ) ^ 2 / Tb.coercivity = 2 / Tb.coercivity * (R : ℝ) ^ 2 := by ring
    rw [e, e2]
    linarith
  have hs4 : Real.exp (-(c' * R)) ≤ ((R : ℝ) ^ 4)⁻¹ := by
    have a1 := hR₈ R hR8
    rw [← one_div, le_div_iff₀ (by positivity)]
    linarith
  have hmain := curlCovariance_box_estimate (a := Tb.coupling) (cK := Tb.coercivity) (CQ := CQ) (K := K)
    (c₁ := c₁) (C₁ := C₁) (W := W) (Cj₀ := |Ci|)
    (e₁ := e₁) (e₂ := Real.exp (-(c' * R))) (L := Tb.side) (k := k) (Q := Q) (Bc := Bc) (o := o) (R := R)
    (p := p) (p' := p')
    hcK (by linarith) hK hc₁ hC₁ (abs_nonneg _) hR64 hn hcolor hbl hsym hfl hdet hgap hslice hQ.decay hW
    (limitForm_translate hQ) (fun b b' => hcl n o R hR1 hn b b') hB1 hB2 (fun z m n' h => (hB3 z m n' h).1) hIR
    hs1 hs2 hs3 hs4 (Real.exp_pos _).le hp hp'
  have hzoff : z = offsetFrom o p.1 - offsetFrom o p'.1 := by
    have h7 : z = offsetFrom p'.1 p.1 := by
      funext i
      rw [hz i]
      rfl
    rw [h7]
    apply offsetFrom_eq
    · funext i
      simp [siteOfInt, offsetFrom]
    · intro i
      have t1 : (supDist p.1 o : ℝ) ≤ (R : ℝ) / 8 := mem_supBall.1 (hqp.2 p.1 (by simp [plaquetteVertices]))
      have t2 : (supDist p'.1 o : ℝ) ≤ (R : ℝ) / 8 := mem_supBall.1 (hq'.2 p'.1 (by simp [plaquetteVertices]))
      have t3 : 8 * supDist p.1 o ≤ R := by
        have : (8 * supDist p.1 o : ℝ) ≤ R := by linarith
        exact_mod_cast this
      have t4 : 8 * supDist p'.1 o ≤ R := by
        have : (8 * supDist p'.1 o : ℝ) ≤ R := by linarith
        exact_mod_cast this
      have t5 := le_supNormInt (offsetFrom o p.1 - offsetFrom o p'.1) i
      have t6 := supNormInt_sub (offsetFrom o p.1) (offsetFrom o p'.1)
      rw [← supDist_eq_supNormInt, ← supDist_eq_supNormInt] at t6
      omega
  rw [← hzoff] at hmain
  have hmax := (hB3 z p.2.1 p.2.2 hqp.1).2 hz0
  have hmain' : |curlCovariance Tb.coupling Tb.side k o R p p' - intCurl Bc (z, p.2.1, p.2.2)| ≤
      Cf * ((R : ℝ) ^ 4)⁻¹ := hmain
  have hi5 : 0 ≤ ((1 + Real.sqrt (intNormSq z)) ^ 5)⁻¹ := by positivity
  have hi4 : 0 ≤ ((R : ℝ) ^ 4)⁻¹ := by positivity
  have t1 := abs_sub_le (curlCovariance Tb.coupling Tb.side k o R p p') (intCurl Bc (z, p.2.1, p.2.2))
    (maxwellKernel z p.2.1 p.2.2 p'.2.1 p'.2.2)
  have t2 : K * ((1 + Real.sqrt (intNormSq z)) ^ 5)⁻¹ ≤ (K + Cf) * ((1 + Real.sqrt (intNormSq z)) ^ 5)⁻¹ :=
    mul_le_mul_of_nonneg_right (by linarith) hi5
  have t3 : Cf * ((R : ℝ) ^ 4)⁻¹ ≤ (K + Cf) * ((R : ℝ) ^ 4)⁻¹ := mul_le_mul_of_nonneg_right (by linarith) hi4
  linarith
theorem curlCovarianceNearMaxwellStatement_holds (h1 : cubeLimitFormStatement) (h2 : cubeHessianStatement)
    (h3 : interiorRegularityStatement) (h4 : curlCovarianceBoundsStatement) (h5 : ellipsoidBoundsStatement)
    (h6 : covariantGradientGapStatement) (h7 : greenColumnStatement) : curlCovarianceNearMaxwellStatement := by
  intro a ha
  obtain ⟨L₁, r₁, hr₁, H₁⟩ := h3 a ha
  obtain ⟨L₂, r₂, hr₂, H₂⟩ := h7 a ha
  refine ⟨max L₁ L₂, fun c => min (r₁ c) (r₂ c), fun c => lt_min (hr₁ c) (hr₂ c), ?_⟩
  intro L hL hLL T hTa hTL hD hrt
  obtain ⟨y₁, G₁⟩ := H₁ L hL (le_trans (le_max_left _ _) hLL) T hTa hTL hD (hrt.trans (min_le_left _ _))
  obtain ⟨y₂, G₂⟩ := H₂ L hL (le_trans (le_max_right _ _) hLL) T hTa hTL hD (hrt.trans (min_le_right _ _))
  refine ⟨max y₁ y₂, fun y hy hret hrow => ?_⟩
  exact curlCovariance_near_maxwell_core T hD (G₁ y (le_trans (le_max_left _ _) hy) hret hrow)
    (G₂ y (le_trans (le_max_right _ _) hy) hret hrow) h1 h2 h4 h5 h6
end YangMills.Construction.BoxGaussian
end
