import YangMills.Construction.RunningCouplingSlope.CompositionKeepsTheCoefficientProof
import YangMills.Construction.FreeKernel.MultipliersSymbolCharactersAndGreensFunctionsOnClasses
import YangMills.Construction.LawByMomentsOfTheFlow.CurlOfTheGreenPotential
import YangMills.Construction.LawByMomentsOfTheFlow.KernelOfTheCurvatureOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MomentLaw
open TorusFields WeightedResponses PeriodicLattice.ShortDistanceTwoPoint PeriodicLattice.VectorClasses
open PeriodicLattice.DiscreteTorusData
private theorem discreteLaplacian_apply {A R : Type*} [Ring A] [AddCommGroup R] (f : (Fin 4 → A) → R)
    (z : Fin 4 → A) :
    discreteLaplacian f z = ∑ ν, ((f z - f (z + unitVector ν)) + (f z - f (z - unitVector ν))) := by
  simp only [discreteLaplacian, backwardDiff, forwardDiff, Pi.neg_apply, Finset.sum_apply,
    sub_add_cancel, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  abel
variable {n : ℕ}
private def realGreen (n : ℕ) (x : Fin 4 → ZMod n) : ℝ := (latticeGreenFunction n x).re
private theorem greenOnVectors_re (N : Fin 4 → ℤ) :
    (greenOnVectors n N).re = realGreen n (zmodClass n N) := rfl
private theorem zmodClass_add_int (N M : Fin 4 → ℤ) :
    zmodClass n (N + M) = zmodClass n N + zmodClass n M := by
  funext μ
  simp [zmodClass]
private theorem zmodClass_sub_int (N M : Fin 4 → ℤ) :
    zmodClass n (N - M) = zmodClass n N - zmodClass n M := by apply _root_.YangMills.Construction.SlopeCoefficient.Pullback.siteOfInt_sub <;> assumption
private theorem zmodClass_unitVector (μ : Fin 4) : zmodClass n (unitVector μ) = unitVector μ := by
  funext ν
  by_cases h : ν = μ
  · subst h
    simp [zmodClass, unitVector]
  · simp [zmodClass, unitVector, Pi.single_eq_of_ne h]
open Classical in
private theorem discreteLaplacian_realGreen [NeZero n] (hL : DiscreteLaplacianOfGreen n)
    (z : Fin 4 → ZMod n) :
    discreteLaplacian (realGreen n) z = (if z = 0 then 1 else 0) - ((n : ℝ) ^ 4)⁻¹ := by
  obtain ⟨N, rfl⟩ : ∃ N, zmodClass n N = z := ⟨residueLift z, zmodClass_residueLift z⟩
  have h := congrArg Complex.re (congrFun hL N)
  rw [discreteLaplacian_apply] at h
  rw [discreteLaplacian_apply]
  have e : ∑ ν, ((realGreen n (zmodClass n N) - realGreen n (zmodClass n N + unitVector ν)) +
      (realGreen n (zmodClass n N) - realGreen n (zmodClass n N - unitVector ν))) =
      (∑ ν, ((greenOnVectors n N - greenOnVectors n (N + unitVector ν)) +
        (greenOnVectors n N - greenOnVectors n (N - unitVector ν)))).re := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    simp only [Complex.add_re, Complex.sub_re, greenOnVectors_re, zmodClass_add_int, zmodClass_sub_int,
      zmodClass_unitVector]
  rw [e, h]
  have h0 : zmodClass n (0 : Fin 4 → ℤ) = 0 := by
    funext μ
    simp [zmodClass]
  have hc : (((n : ℂ) ^ 4)⁻¹).re = ((n : ℝ) ^ 4)⁻¹ := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_inv, Complex.ofReal_re]
  simp only [deltaAtZeroClass, h0, Complex.sub_re, Complex.ofReal_re, hc,
    FourVector.propIndicator]
private def directionPairOf (p : OrientedPlaquette n) : CyclicFormula.OrderedDirectionPair := ⟨p.1.2, p.2⟩
private def plaquetteEquiv (n : ℕ) :
    (Fin 4 → ZMod n) × CyclicFormula.OrderedDirectionPair ≃ OrientedPlaquette n where
  toFun a := ⟨(a.1, a.2.1), a.2.2⟩
  invFun q := (q.1.1, ⟨q.1.2, q.2⟩)
  left_inv _ := rfl
  right_inv _ := rfl
private theorem sum_orientedPlaquette [NeZero n] (f : OrientedPlaquette n → ℝ) :
    ∑ q, f q = ∑' x : Fin 4 → ZMod n, ∑ r : CyclicFormula.OrderedDirectionPair, f (plaquetteEquiv n (x, r)) := by
  rw [tsum_fintype, ← Fintype.sum_prod_type', Fintype.sum_equiv (plaquetteEquiv n).symm f
    (fun a => f (plaquetteEquiv n a)) (fun q => by simp)]
theorem torusCurvatureProjection_eq_curl_green (hC : curlGreenPotentialStatement)
    (hM : FourierFactsAndGreenIdentities.Statement) :
    torusCurvatureProjectionGreenStatement := by
  classical
  intro n _ hn p p' P P' hP hP'
  obtain ⟨-, -, -, hL, -⟩ := hM n hn
  have hlift : ∀ (Q : IntPlaquette) (q : OrientedPlaquette n), IsLift Q q → zmodClass n Q.1 = q.1.1 :=
    fun Q q h => funext h.1
  set y : Fin 4 → ZMod n := p'.1.1 with hy
  set g := realGreen n with hg
  set B₀ := greenPlaquettePotential g y P'.2.1.1 P'.2.1.2 with hB₀
  set Bf : TorusBond n → ℝ := fun b => B₀ b.1 b.2 with hBf
  obtain ⟨hval, hpair⟩ := hC (ZMod n) g y P'.2
  have hp := hpair (((n : ℝ) ^ 4)⁻¹) (fun z => by
    have := discreteLaplacian_realGreen hL z
    convert this)
  have hv : curlVec Bf ∈ curvatureSubspace n := Submodule.subset_span ⟨Bf, rfl⟩
  have horth : ∀ A : TorusBond n → ℝ,
      inner ℝ (EuclideanSpace.single p' (1 : ℝ) - curlVec Bf) (curlVec A) = 0 := by
    intro A
    have hfin : (Function.support (Function.uncurry fun x μ => A (x, μ))).Finite := Set.toFinite _
    have h1 := hp (fun x μ => A (x, μ)) hfin
    have h2 : inner ℝ (curlVec Bf) (curlVec A) = ∑ q : OrientedPlaquette n, curl Bf q.1 * curl A q.1 := by
      simp [PiLp.inner_apply, curlVec, mul_comm]
    have hpe : p'.1 = (y, P'.2.1.1, P'.2.1.2) := by
      rw [hP'.2]
    have h3 : (curlVec A) p' = plaquetteCurlAt (fun x μ => A (x, μ)) y P'.2.1.1 P'.2.1.2 := by
      show curl A p'.1 = _
      rw [hpe]
      rfl
    rw [inner_sub_left, EuclideanSpace.inner_single_left, h2, sum_orientedPlaquette, h3, ← h1]
    simp only [map_one, one_mul, sub_eq_zero]
    rfl
  have hproj : (curvatureSubspace n).starProjection (EuclideanSpace.single p' (1 : ℝ)) = curlVec Bf := by
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero hv fun w hw => ?_
    induction hw using Submodule.span_induction with
    | mem x h =>
      obtain ⟨A, rfl⟩ := h
      exact horth A
    | zero => simp
    | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
    | smul a x _ hx => rw [inner_smul_right, hx, mul_zero]
  have hpe : p.1 = (p.1.1, P.2.1.1, P.2.1.2) := by
    rw [hP.2]
  have hxy : p.1.1 - y = zmodClass n (P.1 - P'.1) := by
    rw [zmodClass_sub_int, hlift P p hP, hlift P' p' hP']
  have hfin : torusCurvatureProjection p p' = plaquetteCurlAt B₀ p.1.1 P.2.1.1 P.2.1.2 := by
    unfold torusCurvatureProjection
    rw [hproj, EuclideanSpace.inner_single_left]
    simp only [map_one, one_mul]
    show curl Bf p.1 = _
    rw [hpe]
    rfl
  rw [hfin, hval p.1.1 P.2]
  congr 1
  funext ν ν'
  simp only [secondDiffMatrix, FourDimKernel.mixedSecondDiff, forwardDiff,
    backwardDiff, greenOnVectors_re, zmodClass_add_int, zmodClass_sub_int, zmodClass_unitVector, hxy, hg]
end YangMills.Construction.MomentLaw
end
