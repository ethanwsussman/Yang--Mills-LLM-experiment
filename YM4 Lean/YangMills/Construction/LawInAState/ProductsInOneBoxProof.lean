import YangMills.Construction.ClusterExpansionOfAStep.CountsOnATorus
import YangMills.Construction.PeriodicOperators.NormOfTheSymbolProof
import YangMills.Construction.ClusterExpansionOfAStep.SumsOnATorus
import YangMills.Construction.FormsOnATorus.ColumnOfTheLimitFormProof
import YangMills.Construction.FormsOnATorus.InteriorRegularityProof
import YangMills.Construction.LawInAState.MomentsOfTheResponses
import YangMills.Construction.LawInAState.ProductsInOneBox
import YangMills.Construction.LawInAState.SitesOfATranslate
import YangMills.Construction.LawInAState.TheCouplingOfTheLevelGrows
import YangMills.Construction.LawInAState.TheLevelOfTheLaw
import YangMills.Construction.LawInAState.TheSizesOfTheBox
import YangMills.Construction.LawOnABoxOfTheFlow.BoundsOfTheCurlKernel
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal
namespace YangMills.Construction.StateLaws
open TorusFields TorusLumps BoxGaussian BoxMarks BoxResponses QuadraticConcentration WeightedResponses BlockAverages
  CellAverages ResponseInTheExpansion
open InfiniteLattice (AmbientSpace)
section TorusDistance
variable {N : ℕ} [NeZero N]
private lemma natAbs_coord_le_supDist (x y : TorusSite N) (i : Fin 4) : ((x i - y i).valMinAbs).natAbs ≤ _root_.YangMills.Construction.TorusFields.supDist x y :=
  Finset.le_sup (f := fun i => ((x i - y i).valMinAbs).natAbs) (Finset.mem_univ i)
private lemma supDist_comm (x y : TorusSite N) : _root_.YangMills.Construction.TorusFields.supDist x y = _root_.YangMills.Construction.TorusFields.supDist y x := by apply _root_.YangMills.Construction.TorusFields.supDist_comm <;> assumption
private lemma supDist_triangle (x y z : TorusSite N) : _root_.YangMills.Construction.TorusFields.supDist x z ≤ _root_.YangMills.Construction.TorusFields.supDist x y + _root_.YangMills.Construction.TorusFields.supDist y z := by apply _root_.YangMills.Construction.TorusFields.supDist_triangle <;> assumption
private lemma summable_exp_neg_mul_natAbs {c : ℝ} (hc : 0 < c) : Summable (fun m : ℤ => Real.exp (-(c * (m.natAbs : ℝ)))) := by apply _root_.YangMills.SharedProofs.p17292 <;> assumption
private def expIntSum (c : ℝ) : ℝ := ∑' m : ℤ, Real.exp (-(c * (m.natAbs : ℝ)))
private lemma expIntSum_nonneg (c : ℝ) : 0 ≤ expIntSum c := tsum_nonneg fun m => (Real.exp_pos _).le
private lemma sum_zmod_exp_le {c : ℝ} (hc : 0 < c) (a : ZMod N) :
    ∑ b : ZMod N, Real.exp (-(c * (((b - a).valMinAbs).natAbs : ℝ))) ≤ expIntSum c := by apply _root_.YangMills.Construction.TorusCounting.sum_exp_valMinAbs_le <;> assumption
private lemma sum_sites_exp_le {c : ℝ} (hc : 0 < c) (y : TorusSite N) :
    ∑ z : TorusSite N, Real.exp (-(c * (_root_.YangMills.Construction.TorusFields.supDist z y : ℝ))) ≤ expIntSum (c / 4) ^ 4 := by apply _root_.YangMills.Construction.TorusCounting.sum_exp_neg_supDist_le <;> assumption
private lemma card_supBall_le (o : TorusSite N) (r : ℕ) :
    (Finset.univ.filter fun z : TorusSite N => _root_.YangMills.Construction.TorusFields.supDist z o ≤ r).card ≤ (2 * r + 1) ^ 4 := by apply _root_.YangMills.Construction.TorusFields.card_supDist_ball_le <;> assumption
private lemma natAbs_valMinAbs_intCast (t : ℤ) (h : 2 * t.natAbs ≤ N) : ((t : ZMod N).valMinAbs).natAbs = t.natAbs := by
  obtain ⟨k, rfl | rfl⟩ := t.eq_nat_or_neg
  · have hk : k ≤ N / 2 := by
      simp only [Int.natAbs_natCast] at h
      omega
    have := ZMod.valMinAbs_natCast_of_le_half hk
    simp only [Int.cast_natCast, this, Int.natAbs_natCast]
  · have hk : k ≤ N / 2 := by
      simp only [Int.natAbs_neg, Int.natAbs_natCast] at h
      omega
    have := ZMod.valMinAbs_natCast_of_le_half hk
    simp only [Int.cast_neg, Int.cast_natCast, ZMod.natAbs_valMinAbs_neg, this, Int.natAbs_neg, Int.natAbs_natCast]
private lemma le_supDist_translate (z : TorusSite N) (a b : Fin 4 → ℤ) (i : Fin 4) (h : 2 * (a i - b i).natAbs ≤ N) :
    (a i - b i).natAbs ≤ _root_.YangMills.Construction.TorusFields.supDist (z + siteOfInt a) (z + siteOfInt b) := by
  have h1 := natAbs_coord_le_supDist (z + siteOfInt a) (z + siteOfInt b) i
  have e : (z + siteOfInt a : TorusSite N) i - (z + siteOfInt b : TorusSite N) i = ((a i - b i : ℤ) : ZMod N) := by
    simp only [Pi.add_apply, siteOfInt]
    push_cast
    ring
  rw [e, natAbs_valMinAbs_intCast _ h] at h1
  exact h1
end TorusDistance
section Components
private lemma imaginaryComponent_add (e : Fin 3) (a b : imaginaryQuaternions) :
    imaginaryComponent e (a + b) = imaginaryComponent e a + imaginaryComponent e b := by
  fin_cases e <;> simp [imaginaryComponent]
private lemma imaginaryComponent_sub (e : Fin 3) (a b : imaginaryQuaternions) :
    imaginaryComponent e (a - b) = imaginaryComponent e a - imaginaryComponent e b := by
  fin_cases e <;> simp [imaginaryComponent]
private lemma measurable_imaginaryComponent (e : Fin 3) : Measurable (imaginaryComponent e) := by
  apply Continuous.measurable
  fin_cases e
  · exact Quaternion.continuous_imI.comp continuous_subtype_val
  · exact Quaternion.continuous_imJ.comp continuous_subtype_val
  · exact Quaternion.continuous_imK.comp continuous_subtype_val
private lemma abs_imaginaryComponent_le (e : Fin 3) (w : imaginaryQuaternions) : |imaginaryComponent e w| ≤ ‖w‖ := by apply _root_.YangMills.SharedProofs.p84614 <;> assumption
end Components
section ColourForms
variable {n : ℕ} [NeZero n] (S : Finset (TorusSite n))
abbrev BoxPlaquette : Type := {p : TorusPlaquette n // p ∈ plaquettesIn S}
abbrev BoxIndex : Type := BoxPlaquette S × Fin 3
open Kronecker
private def colourKron (A : TorusPlaquette n → TorusPlaquette n → ℝ) : Matrix (BoxIndex S) (BoxIndex S) ℝ :=
  (Matrix.of fun p p' : BoxPlaquette S => A p.1 p'.1) ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℝ)
private lemma colourKron_apply (A : TorusPlaquette n → TorusPlaquette n → ℝ) (i j : BoxIndex S) :
    colourKron S A i j = A i.1.1 j.1.1 * (if i.2 = j.2 then 1 else 0) := by
  simp [colourKron, Matrix.one_apply]
private lemma dotProduct_colourKron (A : TorusPlaquette n → TorusPlaquette n → ℝ) (y y' : BoxIndex S → ℝ) :
    y ⬝ᵥ (colourKron S A).mulVec y' = ∑ p : BoxPlaquette S, ∑ p' : BoxPlaquette S, A p.1 p'.1 * ∑ e : Fin 3, y (p, e) * y' (p', e) := by
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, colourKron_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p' _ => ?_
  refine Finset.sum_congr rfl fun e _ => ?_
  simp [mul_comm, mul_left_comm]
private lemma trace_colourKron (A B A' B' : TorusPlaquette n → TorusPlaquette n → ℝ) :
    Matrix.trace (colourKron S A * colourKron S B * colourKron S A' * colourKron S B') =
      3 * ∑ p₁ ∈ plaquettesIn S, ∑ p₂ ∈ plaquettesIn S, ∑ p₃ ∈ plaquettesIn S, ∑ p₄ ∈ plaquettesIn S, A p₁ p₂ * B p₂ p₃ * A' p₃ p₄ * B' p₄ p₁ := by
  simp only [colourKron]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker]
  simp only [mul_one, Matrix.trace_one, Fintype.card_fin]
  rw [mul_comm]
  congr 1
  simp only [← Finset.sum_coe_sort (plaquettesIn S)]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  have key : ∀ f : BoxPlaquette S → BoxPlaquette S → BoxPlaquette S → ℝ, ∑ d, ∑ c, ∑ b, f d c b = ∑ b, ∑ c, ∑ d, f d c b := fun f => by
    calc ∑ d, ∑ c, ∑ b, f d c b = ∑ d, ∑ b, ∑ c, f d c b := Finset.sum_congr rfl fun d _ => Finset.sum_comm
      _ = ∑ b, ∑ d, ∑ c, f d c b := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun b _ => Finset.sum_comm
  exact key _
private def extendByZero (t : BoxIndex S → ℝ) (p : TorusPlaquette n) (e : Fin 3) : ℝ :=
  open Classical in if h : p ∈ plaquettesIn S then t (⟨p, h⟩, e) else 0
private lemma extendByZero_coe (t : BoxIndex S → ℝ) (p : BoxPlaquette S) (e : Fin 3) : extendByZero S t p.1 e = t (p, e) := by
  simp [extendByZero, p.2]
private lemma colourPairing_extendByZero (t : BoxIndex S → ℝ) (G : TorusPlaquette n → imaginaryQuaternions) :
    colourPairing S (extendByZero S t) G = ∑ i, t i * imaginaryComponent i.2 (G i.1.1) := by
  simp only [colourPairing, Fintype.sum_prod_type]
  rw [Finset.sum_comm, ← Finset.sum_coe_sort (plaquettesIn S)]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun e _ => by rw [extendByZero_coe]
private lemma quadForm_extendByZero (A : TorusPlaquette n → TorusPlaquette n → ℝ) (t : BoxIndex S → ℝ) :
    ∑ e : Fin 3, ∑ p ∈ plaquettesIn S, ∑ p' ∈ plaquettesIn S, extendByZero S t p e * A p p' * extendByZero S t p' e =
      t ⬝ᵥ (colourKron S A).mulVec t := by
  rw [dotProduct_colourKron, Finset.sum_comm]
  simp only [← Finset.sum_coe_sort (plaquettesIn S)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p' _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [extendByZero_coe, extendByZero_coe]
  ring
private lemma sum_sq_extendByZero (t : BoxIndex S → ℝ) : ∑ e : Fin 3, ∑ p ∈ plaquettesIn S, extendByZero S t p e ^ 2 = t ⬝ᵥ t := by
  simp only [dotProduct, Fintype.sum_prod_type]
  rw [Finset.sum_comm, ← Finset.sum_coe_sort (plaquettesIn S)]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun e _ => by rw [extendByZero_coe]; ring
private def curlVector (B : TorusBond n → imaginaryQuaternions) : BoxIndex S → ℝ :=
  fun i => imaginaryComponent i.2 (lieFormCurl B i.1.1)
private def plaquetteVector (F : TorusPlaquette n → imaginaryQuaternions) : BoxIndex S → ℝ :=
  fun i => imaginaryComponent i.2 (F i.1.1)
private lemma measurable_curlVector : Measurable (curlVector S) := by
  refine measurable_pi_iff.2 fun i => ?_
  have h : ∀ b : TorusBond n, Measurable fun B : TorusBond n → imaginaryQuaternions => imaginaryComponent i.2 (B b) := fun b =>
    (measurable_imaginaryComponent i.2).comp (measurable_pi_apply b)
  simp only [curlVector, lieFormCurl, imaginaryComponent_sub, imaginaryComponent_add]
  exact (((h _).add (h _)).sub (h _)).sub (h _)
private lemma curlVector_eq_add (B : TorusBond n → imaginaryQuaternions) (F : TorusPlaquette n → imaginaryQuaternions) :
    curlVector S B = plaquetteVector S F + fun i => imaginaryComponent i.2 (lieFormCurl B i.1.1 - F i.1.1) := by
  funext i
  simp [curlVector, plaquetteVector, imaginaryComponent_sub]
private lemma curlVector_dotProduct (A : TorusPlaquette n → TorusPlaquette n → ℝ) (B : TorusBond n → imaginaryQuaternions) :
    curlVector S B ⬝ᵥ (colourKron S A).mulVec (curlVector S B) =
      ∑ p ∈ plaquettesIn S, ∑ p' ∈ plaquettesIn S, A p p' * curlPairing B p p' := by
  rw [dotProduct_colourKron]
  simp only [← Finset.sum_coe_sort (plaquettesIn S)]
  rfl
private lemma isCenteredGaussian_curl {γ : Measure (TorusBond n → imaginaryQuaternions)} [IsProbabilityMeasure γ]
    {A : TorusBond n → imaginaryQuaternions} {Fm : TorusPlaquette n → imaginaryQuaternions}
    {Tk : TorusPlaquette n → TorusPlaquette n → ℝ} {x : ℝ} (hx : 0 < x)
    (hg : ∀ u : TorusPlaquette n → Fin 3 → ℝ, γ.map (fun ζ => colourPairing S u fun p => lieFormCurl (A + ζ) p - Fm p) =
      gaussianReal 0 (x⁻¹ * ∑ e : Fin 3, ∑ p ∈ plaquettesIn S, ∑ p' ∈ plaquettesIn S, u p e * Tk p p' * u p' e).toNNReal)
    (hpos : ∀ u : TorusPlaquette n → Fin 3 → ℝ, 0 ≤ ∑ e : Fin 3, ∑ p ∈ plaquettesIn S, ∑ p' ∈ plaquettesIn S, u p e * Tk p p' * u p' e) :
    WickMoments.IsCenteredGaussian (fun i j => colourKron S (fun p p' => x⁻¹ * Tk p p') i j)
      (γ.map fun ζ i => imaginaryComponent i.2 (lieFormCurl (A + ζ) i.1.1 - Fm i.1.1)) := by
  have hxi : Measurable (fun (ζ : TorusBond n → imaginaryQuaternions) (i : BoxIndex S) =>
      imaginaryComponent i.2 (lieFormCurl (A + ζ) i.1.1 - Fm i.1.1)) := by
    refine measurable_pi_iff.2 fun i => ?_
    have h : ∀ b : TorusBond n, Measurable fun ζ : TorusBond n → imaginaryQuaternions => imaginaryComponent i.2 ((A + ζ) b) := fun b => by
      simp only [Pi.add_apply, imaginaryComponent_add]
      exact measurable_const.add ((measurable_imaginaryComponent i.2).comp (measurable_pi_apply b))
    simp only [lieFormCurl, imaginaryComponent_sub, imaginaryComponent_add]
    exact ((((h _).add (h _)).sub (h _)).sub (h _)).sub_const _
  refine ⟨Measure.isProbabilityMeasure_map hxi.aemeasurable, fun t => ?_⟩
  rw [integral_map hxi.aemeasurable (Continuous.aestronglyMeasurable (by fun_prop))]
  have hP : ∀ ζ : TorusBond n → imaginaryQuaternions, ∑ i, t i * imaginaryComponent i.2 (lieFormCurl (A + ζ) i.1.1 - Fm i.1.1) =
      colourPairing S (extendByZero S t) fun p => lieFormCurl (A + ζ) p - Fm p := fun ζ =>
    (colourPairing_extendByZero S t (fun p => lieFormCurl (A + ζ) p - Fm p)).symm
  simp_rw [hP]
  have hm : Measurable (fun ζ : TorusBond n → imaginaryQuaternions => colourPairing S (extendByZero S t) fun p => lieFormCurl (A + ζ) p - Fm p) := by
    have := (measurable_pi_iff.1 hxi)
    have e : (fun ζ : TorusBond n → imaginaryQuaternions => colourPairing S (extendByZero S t) fun p => lieFormCurl (A + ζ) p - Fm p) =
        fun ζ => ∑ i, t i * imaginaryComponent i.2 (lieFormCurl (A + ζ) i.1.1 - Fm i.1.1) := by
      funext ζ; exact (hP ζ).symm
    rw [e]
    exact Finset.measurable_fun_sum _ fun i _ => (this i).const_mul _
  have hv := hg (extendByZero S t)
  have h1 : ∫ ζ, Complex.exp (Complex.I * ((colourPairing S (extendByZero S t) fun p => lieFormCurl (A + ζ) p - Fm p : ℝ) : ℂ)) ∂γ =
      ∫ s, Complex.exp (Complex.I * ((s : ℝ) : ℂ)) ∂(γ.map fun ζ => colourPairing S (extendByZero S t) fun p => lieFormCurl (A + ζ) p - Fm p) := by
    rw [integral_map hm.aemeasurable (Continuous.aestronglyMeasurable (by fun_prop))]
  rw [h1, hv]
  have h2 := charFun_gaussianReal (μ := 0) (v := (x⁻¹ * ∑ e : Fin 3, ∑ p ∈ plaquettesIn S, ∑ p' ∈ plaquettesIn S,
    extendByZero S t p e * Tk p p' * extendByZero S t p' e).toNNReal) 1
  rw [charFun_apply_real] at h2
  simp only [Complex.ofReal_one, one_mul] at h2
  have h3 : ∫ s, Complex.exp (Complex.I * ((s : ℝ) : ℂ)) ∂(gaussianReal 0 (x⁻¹ * ∑ e : Fin 3, ∑ p ∈ plaquettesIn S, ∑ p' ∈ plaquettesIn S,
      extendByZero S t p e * Tk p p' * extendByZero S t p' e).toNNReal) =
      ∫ s, Complex.exp (((s : ℝ) : ℂ) * Complex.I) ∂(gaussianReal 0 (x⁻¹ * ∑ e : Fin 3, ∑ p ∈ plaquettesIn S, ∑ p' ∈ plaquettesIn S,
      extendByZero S t p e * Tk p p' * extendByZero S t p' e).toNNReal) := by
    simp_rw [mul_comm Complex.I]
  rw [h3, h2]
  have hq : ∑ i, ∑ j, t i * colourKron S (fun p p' => x⁻¹ * Tk p p') i j * t j =
      x⁻¹ * ∑ e : Fin 3, ∑ p ∈ plaquettesIn S, ∑ p' ∈ plaquettesIn S, extendByZero S t p e * Tk p p' * extendByZero S t p' e := by
    have h4 := quadForm_extendByZero S (fun p p' => x⁻¹ * Tk p p') t
    have h5 : t ⬝ᵥ (colourKron S (fun p p' => x⁻¹ * Tk p p')).mulVec t =
        ∑ i, ∑ j, t i * colourKron S (fun p p' => x⁻¹ * Tk p p') i j * t j := by
      simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
    rw [← h5, ← h4]
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun p' _ => by ring
  rw [hq, Real.coe_toNNReal _ (mul_nonneg (by positivity) (hpos _))]
  congr 1
  push_cast
  ring
end ColourForms
section Chart
variable {ℓ : StepParameters} {T : WeightedResponses.StageTower ℓ} {k n : ℕ} [NeZero n] {o : TorusSite n} {R : ℕ}
private lemma lintegral_coordLaw_le (c : BoxChart T k o R) {P : Measure (MarkedSample ℓ k n)} {x c₀ ε η : ℝ}
    (hB : c.IsMeasurable) (hL : c.HasLaw P x c₀ ε)
    (he : Real.exp (2 * ε) ≤ (1 + η) * (1 - Real.exp (-((R : ℝ) ^ 4)))) (h1 : 0 < 1 - Real.exp (-((R : ℝ) ^ 4)))
    {q : OuterData T k o R} (hq : q ∈ c.goodOuter) {g : (TorusBond n → imaginaryQuaternions) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ ζ, g ζ ∂(c.coordLaw x c₀ q) ≤
      ENNReal.ofReal (1 + η) * ∫⁻ ζ, g ζ ∂(sliceGaussian ℓ.coupling ℓ.side k o R x (c.background q)) := by
  set γ := sliceGaussian ℓ.coupling ℓ.side k o R x (c.background q) with hγ
  set Ell := sliceEllipsoid ℓ.coupling ℓ.side k o R (c.background q) c₀ with hEll
  obtain ⟨hprob, hmass⟩ := hL.ellipsoid_mass q hq
  have hw : Measurable (fun ζ => c.weight q ζ) :=
    hB.measurable_weight.comp (measurable_const.prodMk measurable_id :
      Measurable fun ζ : TorusBond n → imaginaryQuaternions => ((⟨q, hq⟩ : c.goodOuter), ζ))
  set ν := (γ.restrict Ell).withDensity fun ζ => ENNReal.ofReal (c.weight q ζ) with hν
  have hlaw : c.coordLaw x c₀ q = (ν Set.univ)⁻¹ • ν := rfl
  have hae : ∀ᵐ ζ ∂(γ.restrict Ell), Real.exp (-ε) ≤ c.weight q ζ ∧ c.weight q ζ ≤ Real.exp ε := by
    rw [ae_iff, Measure.restrict_apply]
    · have : {ζ | ¬ (Real.exp (-ε) ≤ c.weight q ζ ∧ c.weight q ζ ≤ Real.exp ε)} ∩ Ell = ∅ :=
        Set.eq_empty_iff_forall_notMem.2 fun ζ hζ => by
          obtain ⟨h2, hmem⟩ := hζ
          obtain ⟨w0, wl⟩ := hL.weight_bounds q hq ζ hmem
          have a1 := abs_le.1 wl
          refine h2 ⟨?_, ?_⟩
          · have := Real.exp_le_exp.2 a1.1
            rwa [Real.exp_log w0] at this
          · have := Real.exp_le_exp.2 a1.2
            rwa [Real.exp_log w0] at this
      rw [this]
      simp
    · exact (((measurableSet_le measurable_const hw).inter (measurableSet_le hw measurable_const))).compl
  have hu : ENNReal.ofReal (1 - Real.exp (-((R : ℝ) ^ 4))) ≤ γ Ell := by
    have : γ Ell = ENNReal.ofReal (γ.real Ell) := by
      rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    rw [this]
    exact ENNReal.ofReal_le_ofReal hmass
  set a := Real.exp (-ε) * (1 - Real.exp (-((R : ℝ) ^ 4))) with ha
  have ha0 : 0 < a := mul_pos (Real.exp_pos _) h1
  have hlow : ENNReal.ofReal a ≤ ν Set.univ := by
    rw [hν, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    calc ENNReal.ofReal a = ENNReal.ofReal (Real.exp (-ε)) * ENNReal.ofReal (1 - Real.exp (-((R : ℝ) ^ 4))) :=
          ENNReal.ofReal_mul (Real.exp_pos _).le
      _ ≤ ENNReal.ofReal (Real.exp (-ε)) * (γ.restrict Ell) Set.univ := by
          rw [Measure.restrict_apply_univ]; gcongr
      _ = ∫⁻ _ζ, ENNReal.ofReal (Real.exp (-ε)) ∂(γ.restrict Ell) := by rw [lintegral_const]
      _ ≤ ∫⁻ ζ, ENNReal.ofReal (c.weight q ζ) ∂(γ.restrict Ell) :=
          lintegral_mono_ae (hae.mono fun ζ h => ENNReal.ofReal_le_ofReal h.1)
  have hup : ∫⁻ ζ, g ζ ∂ν ≤ ENNReal.ofReal (Real.exp ε) * ∫⁻ ζ, g ζ ∂γ := by
    rw [hν, lintegral_withDensity_eq_lintegral_mul _
      (show Measurable fun ζ => ENNReal.ofReal (c.weight q ζ) from ENNReal.measurable_ofReal.comp hw) hg]
    calc ∫⁻ ζ, ((fun ζ => ENNReal.ofReal (c.weight q ζ)) * g) ζ ∂(γ.restrict Ell)
        ≤ ∫⁻ ζ, ENNReal.ofReal (Real.exp ε) * g ζ ∂(γ.restrict Ell) :=
          lintegral_mono_ae (hae.mono fun ζ h => by
            simp only [Pi.mul_apply]
            exact mul_le_mul' (ENNReal.ofReal_le_ofReal h.2) le_rfl)
      _ = ENNReal.ofReal (Real.exp ε) * ∫⁻ ζ, g ζ ∂(γ.restrict Ell) := lintegral_const_mul _ hg
      _ ≤ ENNReal.ofReal (Real.exp ε) * ∫⁻ ζ, g ζ ∂γ := by
          gcongr
          exact Measure.restrict_le_self
  rw [hlaw, lintegral_smul_measure, smul_eq_mul]
  calc (ν Set.univ)⁻¹ * ∫⁻ ζ, g ζ ∂ν ≤ (ENNReal.ofReal a)⁻¹ * (ENNReal.ofReal (Real.exp ε) * ∫⁻ ζ, g ζ ∂γ) :=
        mul_le_mul' (ENNReal.inv_le_inv.2 hlow) hup
    _ = ((ENNReal.ofReal a)⁻¹ * ENNReal.ofReal (Real.exp ε)) * ∫⁻ ζ, g ζ ∂γ := by ring
    _ ≤ ENNReal.ofReal (1 + η) * ∫⁻ ζ, g ζ ∂γ := by
      gcongr
      rw [← ENNReal.ofReal_inv_of_pos ha0, ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      rw [inv_mul_le_iff₀ ha0, ha]
      have e2 : Real.exp ε = Real.exp (-ε) * Real.exp (2 * ε) := by
        rw [← Real.exp_add]; congr 1; ring
      calc Real.exp ε = Real.exp (-ε) * Real.exp (2 * ε) := e2
        _ ≤ Real.exp (-ε) * ((1 + η) * (1 - Real.exp (-((R : ℝ) ^ 4)))) := by gcongr
        _ = _ := by ring
private lemma measurable_restrictOuter : Measurable (restrictOuter o R) :=
  measurable_pi_iff.2 fun b => (measurable_pi_apply b.1.2).comp (measurable_pi_apply b.1.1)
private lemma measurable_restrictInner : Measurable (restrictInner o R) :=
  measurable_pi_iff.2 fun b => (measurable_pi_apply b.1.2).comp (measurable_pi_apply b.1.1)
private lemma measurable_outerData : Measurable (outerData T k o R) :=
  (measurable_restrictOuter.comp measurable_fst).prodMk measurable_snd
private lemma curlVector_add (S : Finset (TorusSite n)) (A B : TorusBond n → imaginaryQuaternions) :
    curlVector S (A + B) = curlVector S A + curlVector S B := by
  funext i
  simp only [curlVector, lieFormCurl, Pi.add_apply, imaginaryComponent_add, imaginaryComponent_sub]
  ring
private def chartCurlVector (c : BoxChart T k o R) (u : MarkedSample ℓ k n) : BoxIndex (supBall o (2 * R)) → ℝ :=
  curlVector (supBall o (2 * R)) (c.background (outerData T k o R (stageState T k n u)) +
    c.coord (outerData T k o R (stageState T k n u)) (restrictInner o R (stageState T k n u).1))
private lemma measurableSet_event (c : BoxChart T k o R) (hB : c.IsMeasurable) (hS : Measurable (stageState T k n)) :
    MeasurableSet c.event :=
  hB.measurableSet_orbitSet.preimage
    ((measurable_outerData.comp hS).prodMk (measurable_restrictInner.comp (measurable_fst.comp hS)))
private lemma measurable_indicator_chartCurlVector (c : BoxChart T k o R) (hB : c.IsMeasurable) (hS : Measurable (stageState T k n)) :
    Measurable (c.event.indicator (chartCurlVector c)) := by
  classical
  have hE := measurableSet_event c hB hS
  have hO : Measurable (fun u => outerData T k o R (stageState T k n u)) := measurable_outerData.comp hS
  have hOn : Measurable (fun u => restrictInner o R (stageState T k n u).1) := measurable_restrictInner.comp (measurable_fst.comp hS)
  have hp : Measurable (fun u : c.event =>
      (⟨(outerData T k o R (stageState T k n u.1), restrictInner o R (stageState T k n u.1).1), u.2⟩ : c.orbitSet)) :=
    ((hO.prodMk hOn).comp measurable_subtype_coe).subtype_mk
  have hq : Measurable (fun u : c.event =>
      (⟨outerData T k o R (stageState T k n u.1), hB.fst_mem_goodOuter _ u.2⟩ : c.goodOuter)) :=
    (hO.comp measurable_subtype_coe).subtype_mk
  have g1 : Measurable (fun u : c.event =>
      curlVector (supBall o (2 * R)) (c.background (outerData T k o R (stageState T k n u.1)))) :=
    (measurable_curlVector _).comp (hB.measurable_background.comp hq)
  have g2 : Measurable (fun u : c.event => curlVector (supBall o (2 * R))
      (c.coord (outerData T k o R (stageState T k n u.1)) (restrictInner o R (stageState T k n u.1).1))) :=
    (measurable_curlVector _).comp (hB.measurable_coord.comp hp)
  have e : c.event.indicator (chartCurlVector c) = fun u => if h : u ∈ c.event then
      (curlVector (supBall o (2 * R)) (c.background (outerData T k o R (stageState T k n u))) +
        curlVector (supBall o (2 * R)) (c.coord (outerData T k o R (stageState T k n u)) (restrictInner o R (stageState T k n u).1)))
      else 0 := by
    funext u
    by_cases h : u ∈ c.event
    · simp [h, chartCurlVector, curlVector_add]
    · simp [h]
  rw [e]
  exact Measurable.dite (f := fun u : c.event =>
      curlVector (supBall o (2 * R)) (c.background (outerData T k o R (stageState T k n u.1))) +
      curlVector (supBall o (2 * R)) (c.coord (outerData T k o R (stageState T k n u.1)) (restrictInner o R (stageState T k n u.1).1)))
    (g1.add g2) measurable_const hE
private lemma measurable_centeredCurl (S : Finset (TorusSite n)) (A : TorusBond n → imaginaryQuaternions)
    (Fm : TorusPlaquette n → imaginaryQuaternions) :
    Measurable (fun (ζ : TorusBond n → imaginaryQuaternions) (i : BoxIndex S) =>
      imaginaryComponent i.2 (lieFormCurl (A + ζ) i.1.1 - Fm i.1.1)) := by
  refine measurable_pi_iff.2 fun i => ?_
  have h : ∀ b : TorusBond n, Measurable fun ζ : TorusBond n → imaginaryQuaternions => imaginaryComponent i.2 ((A + ζ) b) := fun b => by
    simp only [Pi.add_apply, imaginaryComponent_add]
    exact measurable_const.add ((measurable_imaginaryComponent i.2).comp (measurable_pi_apply b))
  simp only [lieFormCurl, imaginaryComponent_sub, imaginaryComponent_add]
  exact ((((h _).add (h _)).sub (h _)).sub (h _)).sub_const _
private def chartGaussians (c : BoxChart T k o R) (x : ℝ) :
    Set ((BoxIndex (supBall o (2 * R)) → ℝ) × Measure (BoxIndex (supBall o (2 * R)) → ℝ)) :=
  {p | ∃ q ∈ c.goodOuter, p = (plaquetteVector (supBall o (2 * R)) (c.meanCurl q),
    (sliceGaussian ℓ.coupling ℓ.side k o R x (c.background q)).map
      fun ζ i => imaginaryComponent i.2 (lieFormCurl (c.background q + ζ) i.1.1 - c.meanCurl q i.1.1))}
private lemma chart_dominatedByGaussians (c : BoxChart T k o R) {P : Measure (MarkedSample ℓ k n)} [IsProbabilityMeasure P]
    {x c₀ ε η : ℝ} (hη : 0 < 1 + η) (hB : c.IsMeasurable) (hS : Measurable (stageState T k n)) (hL : c.HasLaw P x c₀ ε)
    (he : Real.exp (2 * ε) ≤ (1 + η) * (1 - Real.exp (-((R : ℝ) ^ 4)))) (h1 : 0 < 1 - Real.exp (-((R : ℝ) ^ 4))) :
    IsDominatedByGaussianShifts P c.event (chartCurlVector c) (chartGaussians c x) η := by
  classical
  intro h b hh hb
  have hE := measurableSet_event c hB hS
  have hYm := measurable_indicator_chartCurlVector c hB hS
  set Yt := c.event.indicator (chartCurlVector c) with hYt
  have hgauss : ∀ q (hq : q ∈ c.goodOuter), ∫⁻ ζ, h (curlVector (supBall o (2 * R)) (c.background q + ζ))
      ∂(sliceGaussian ℓ.coupling ℓ.side k o R x (c.background q)) ≤ b := by
    intro q hq
    have h2 := hb _ ⟨q, hq, rfl⟩
    simp only at h2
    have hf : Measurable fun ξ : BoxIndex (supBall o (2 * R)) → ℝ => h (plaquetteVector (supBall o (2 * R)) (c.meanCurl q) + ξ) :=
      hh.comp (measurable_const.add measurable_id)
    rw [lintegral_map hf (measurable_centeredCurl (supBall o (2 * R)) (c.background q) (c.meanCurl q))] at h2
    have e : ∀ ζ, curlVector (supBall o (2 * R)) (c.background q + ζ) = plaquetteVector (supBall o (2 * R)) (c.meanCurl q) +
        fun i => imaginaryComponent i.2 (lieFormCurl (c.background q + ζ) i.1.1 - c.meanCurl q i.1.1) := fun ζ =>
      curlVector_eq_add (supBall o (2 * R)) _ _
    simp_rw [e]
    exact h2
  by_cases hbtop : b = ⊤
  · by_cases hPE : P c.event = 0
    · rw [setLIntegral_measure_zero _ _ hPE]
      exact zero_le
    · rw [hbtop, ENNReal.mul_top (mul_ne_zero (by simpa using hη) hPE)]
      exact le_top
  set B := b.toReal with hBd
  have hBb : ENNReal.ofReal B = b := ENNReal.ofReal_toReal hbtop
  set base' : OuterData T k o R → TorusBond n → imaginaryQuaternions :=
    fun q => if hq : q ∈ c.goodOuter then c.background q else 0 with hbase
  have hbase' : Measurable base' :=
    Measurable.dite (f := fun q : c.goodOuter => c.background q) (g := fun _ => (0 : TorusBond n → imaginaryQuaternions))
      hB.measurable_background measurable_const hB.measurableSet_goodOuter
  have hN : ∀ N : ℕ, ∫⁻ u in c.event, min (h (Yt u)) N ∂P ≤ ENNReal.ofReal (1 + η) * P c.event * b := by
    intro N
    have hm : Measurable (fun u => min (h (Yt u)) (N : ℝ≥0∞)) := (hh.comp hYm).min measurable_const
    set F : OuterData T k o R × (TorusBond n → imaginaryQuaternions) → ℝ := fun z =>
      c.goodOuter.indicator (fun _ => (1 : ℝ)) z.1 *
        (min (h (curlVector (supBall o (2 * R)) (base' z.1) + curlVector (supBall o (2 * R)) z.2)) (N : ℝ≥0∞)).toReal with hFd
    have hF : Measurable F := by
      have m1 : Measurable (fun z : OuterData T k o R × (TorusBond n → imaginaryQuaternions) =>
          curlVector (supBall o (2 * R)) (base' z.1) + curlVector (supBall o (2 * R)) z.2) :=
        ((measurable_curlVector (supBall o (2 * R))).comp (hbase'.comp measurable_fst)).add
          ((measurable_curlVector (supBall o (2 * R))).comp measurable_snd)
      have m2 := ((hh.comp m1).min (measurable_const (a := (N : ℝ≥0∞)))).ennreal_toReal
      have m3 : Measurable (fun z : OuterData T k o R × (TorusBond n → imaginaryQuaternions) =>
          c.goodOuter.indicator (fun _ => (1 : ℝ)) z.1) :=
        (measurable_const.indicator hB.measurableSet_goodOuter).comp measurable_fst
      exact m3.mul m2
    have hFb : ∀ z, |F z| ≤ N := by
      intro z
      simp only [hFd]
      have a1 : (min (h (curlVector (supBall o (2 * R)) (base' z.1) + curlVector (supBall o (2 * R)) z.2)) (N : ℝ≥0∞)).toReal ≤ N := by
        have := ENNReal.toReal_mono (ENNReal.natCast_ne_top N)
          (min_le_right (h (curlVector (supBall o (2 * R)) (base' z.1) + curlVector (supBall o (2 * R)) z.2)) (N : ℝ≥0∞))
        simpa using this
      have a0 : 0 ≤ (min (h (curlVector (supBall o (2 * R)) (base' z.1) + curlVector (supBall o (2 * R)) z.2)) (N : ℝ≥0∞)).toReal :=
        ENNReal.toReal_nonneg
      by_cases hz : z.1 ∈ c.goodOuter
      · simp only [Set.indicator_of_mem hz, one_mul]
        rw [abs_of_nonneg a0]; exact a1
      · simp [Set.indicator_of_notMem hz]
    have law := hL.integral_eq F hF ⟨N, hFb⟩
    have hl : ∫ u in c.event, F (outerData T k o R (stageState T k n u),
        c.coord (outerData T k o R (stageState T k n u)) (restrictInner o R (stageState T k n u).1)) ∂P =
        (∫⁻ u in c.event, min (h (Yt u)) (N : ℝ≥0∞) ∂P).toReal := by
      rw [← integral_toReal hm.aemeasurable
        (Filter.Eventually.of_forall fun u => lt_of_le_of_lt (min_le_right _ _) (ENNReal.natCast_lt_top N))]
      refine setIntegral_congr_fun hE fun u hu => ?_
      have hq := hB.fst_mem_goodOuter _ hu
      simp only at hq
      simp only [hFd, Set.indicator_of_mem hq, one_mul, hbase, dif_pos hq, hYt, Set.indicator_of_mem hu, chartCurlVector,
        curlVector_add]
    have hin : ∀ u ∈ c.event, ∫ ζ, F (outerData T k o R (stageState T k n u), ζ)
        ∂(c.coordLaw x c₀ (outerData T k o R (stageState T k n u))) ≤ (1 + η) * B := by
      intro u hu
      have hq := hB.fst_mem_goodOuter _ hu
      simp only at hq
      set q := outerData T k o R (stageState T k n u) with hqd
      have e : ∀ ζ, F (q, ζ) = (min (h (curlVector (supBall o (2 * R)) (c.background q + ζ))) (N : ℝ≥0∞)).toReal := by
        intro ζ
        simp only [hFd, Set.indicator_of_mem hq, one_mul, hbase, dif_pos hq, curlVector_add]
      simp_rw [e]
      have hmm : Measurable (fun ζ => h (curlVector (supBall o (2 * R)) (c.background q + ζ))) := by
        have e2 : (fun ζ => h (curlVector (supBall o (2 * R)) (c.background q + ζ))) =
            fun ζ => h (curlVector (supBall o (2 * R)) (c.background q) + curlVector (supBall o (2 * R)) ζ) :=
          funext fun ζ => by rw [curlVector_add]
        rw [e2]
        exact hh.comp (measurable_const.add (measurable_curlVector _))
      rw [integral_toReal (hmm.min measurable_const).aemeasurable
        (Filter.Eventually.of_forall fun ζ => lt_of_le_of_lt (min_le_right _ _) (ENNReal.natCast_lt_top N))]
      have i1 : ∫⁻ ζ, min (h (curlVector (supBall o (2 * R)) (c.background q + ζ))) (N : ℝ≥0∞) ∂(c.coordLaw x c₀ q) ≤
          ENNReal.ofReal (1 + η) * b :=
        (lintegral_mono fun ζ => min_le_left _ _).trans
          ((lintegral_coordLaw_le c hB hL he h1 hq hmm).trans (mul_le_mul' le_rfl (hgauss q hq)))
      refine ENNReal.toReal_le_of_le_ofReal (by positivity) (i1.trans (le_of_eq ?_))
      rw [ENNReal.ofReal_mul hη.le, hBb]
    have hrhs : ∫ u in c.event, ∫ ζ, F (outerData T k o R (stageState T k n u), ζ)
        ∂(c.coordLaw x c₀ (outerData T k o R (stageState T k n u))) ∂P ≤ (1 + η) * B * P.real c.event := by
      by_cases hint : IntegrableOn (fun u => ∫ ζ, F (outerData T k o R (stageState T k n u), ζ)
          ∂(c.coordLaw x c₀ (outerData T k o R (stageState T k n u)))) c.event P
      · have := setIntegral_mono_on hint (integrableOn_const (measure_ne_top _ _)) hE hin
        refine this.trans (le_of_eq ?_)
        rw [setIntegral_const]
        simp [smul_eq_mul, mul_comm]
      · rw [integral_undef hint]
        positivity
    rw [hl] at law
    have hfin : ∫⁻ u in c.event, min (h (Yt u)) (N : ℝ≥0∞) ∂P ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (lintegral_mono fun u => min_le_right _ _)
      simp [lintegral_const, ENNReal.mul_eq_top]
    have hPE : P c.event = ENNReal.ofReal (P.real c.event) := by
      rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    rw [← ENNReal.ofReal_toReal hfin, law, ← hBb, hPE, ← ENNReal.ofReal_mul hη.le, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal (hrhs.trans (le_of_eq ?_))
    ring
  have hsup : ∫⁻ u in c.event, h (chartCurlVector c u) ∂P = ⨆ N : ℕ, ∫⁻ u in c.event, min (h (Yt u)) N ∂P := by
    rw [← lintegral_iSup (f := fun (N : ℕ) u => min (h (Yt u)) (N : ℝ≥0∞)) (fun N => (hh.comp hYm).min measurable_const)
      (fun a b hab u => min_le_min le_rfl (by exact_mod_cast hab))]
    refine setLIntegral_congr_fun hE fun u hu => ?_
    have e : Yt u = chartCurlVector c u := by simp [hYt, hu]
    simp only [e]
    have : ⨆ N : ℕ, min (h (chartCurlVector c u)) (N : ℝ≥0∞) = min (h (chartCurlVector c u)) (⨆ N : ℕ, (N : ℝ≥0∞)) :=
      (inf_iSup_eq _ _).symm
    rw [this, ENNReal.iSup_natCast]
    simp
  rw [hsup]
  exact iSup_le hN
end Chart
section Domination
variable {n : ℕ} [NeZero n] (S : Finset (TorusSite n))
private def siteWeight (c : ℝ) (i : BoxIndex S) (y : TorusSite n) : ℝ := Real.exp (-(c / 2 * (_root_.YangMills.Construction.TorusFields.supDist i.1.1.1 y : ℝ)))
private lemma sum_boxIndex_exp_le {a : ℝ} (ha : 0 < a) (y : TorusSite n) :
    ∑ i : BoxIndex S, Real.exp (-(a * (_root_.YangMills.Construction.TorusFields.supDist i.1.1.1 y : ℝ))) ≤ 48 * expIntSum (a / 4) ^ 4 := by
  have h1 : ∑ i : BoxIndex S, Real.exp (-(a * (_root_.YangMills.Construction.TorusFields.supDist i.1.1.1 y : ℝ))) =
      3 * ∑ p : BoxPlaquette S, Real.exp (-(a * (_root_.YangMills.Construction.TorusFields.supDist p.1.1 y : ℝ))) := by
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by simp
  have h2 : ∑ p : BoxPlaquette S, Real.exp (-(a * (_root_.YangMills.Construction.TorusFields.supDist p.1.1 y : ℝ))) ≤
      ∑ p : TorusPlaquette n, Real.exp (-(a * (_root_.YangMills.Construction.TorusFields.supDist p.1 y : ℝ))) := by
    rw [Finset.sum_coe_sort (plaquettesIn S) (fun p : TorusPlaquette n => Real.exp (-(a * (_root_.YangMills.Construction.TorusFields.supDist p.1 y : ℝ))))]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun p _ _ => (Real.exp_pos _).le
  have h3 : ∑ p : TorusPlaquette n, Real.exp (-(a * (_root_.YangMills.Construction.TorusFields.supDist p.1 y : ℝ))) =
      16 * ∑ z : TorusSite n, Real.exp (-(a * (_root_.YangMills.Construction.TorusFields.supDist z y : ℝ))) := by
    rw [Fintype.sum_prod_type]
    simp [Finset.mul_sum]
  have h4 := sum_sites_exp_le ha y
  rw [h1]
  nlinarith
private lemma exp_neg_mul_max_le {c a b : ℝ} (hc : 0 < c) :
    Real.exp (-(c * max a b)) ≤ Real.exp (-(c / 2 * a)) * Real.exp (-(c / 2 * b)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  have h1 : a ≤ max a b := le_max_left _ _
  have h2 : b ≤ max a b := le_max_right _ _
  nlinarith
private lemma dominatedBySites_of_kernels {V : Type} (κ : V → TorusSite n → TorusPlaquette n → TorusPlaquette n → ℝ)
    (Y : V → Finset (TorusSite n)) (Near : V → V → Prop)
    (In : Set (BoxIndex S)) {C c Nc Dd Dd₂ : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (symm : ∀ v y p p', κ v y p p' = κ v y p' p)
    (dec : ∀ v y p p', |κ v y p p'| ≤ C * Real.exp (-(c * max (_root_.YangMills.Construction.TorusFields.supDist p.1 y : ℝ) (_root_.YangMills.Construction.TorusFields.supDist p'.1 y : ℝ))))
    (off : ∀ v y, y ∉ Y v → ∀ p p', κ v y p p' = 0) (card : ∀ v, ((Y v).card : ℝ) ≤ Nc)
    (far : ∀ v w, ¬ Near v w → ∀ y ∈ Y v, ∀ y' ∈ Y w, Dd ≤ (_root_.YangMills.Construction.TorusFields.supDist y y' : ℝ))
    (out : ∀ v, ∀ y ∈ Y v, ∀ i, i ∉ In → Dd₂ ≤ (_root_.YangMills.Construction.TorusFields.supDist i.1.1.1 y : ℝ)) :
    DominatedBySites (siteWeight S c) Y (fun v => colourKron S (totalKernel (κ v))) Near In C
      (max (48 * expIntSum (c / 8) ^ 4) 1) Nc
      (48 * expIntSum (c / 16) ^ 4 * Real.exp (-(c / 4 * Dd))) (48 * expIntSum (c / 16) ^ 4 * Real.exp (-(c / 4 * Dd₂))) := by
  classical
  have e8 : c / 2 / 4 = c / 8 := by ring
  have e16 : c / 4 / 4 = c / 16 := by ring
  refine ⟨fun v => ?_, fun i y => (Real.exp_pos _).le, fun v i j => ?_, fun y => ?_, fun i => ?_, card,
    fun v w hn y hy y' hy' => ?_, fun v y hy => ?_⟩
  · ext i j
    simp only [Matrix.transpose_apply, colourKron_apply, totalKernel]
    have : ∑ y, κ v y j.1.1 i.1.1 = ∑ y, κ v y i.1.1 j.1.1 := Finset.sum_congr rfl fun y _ => symm v y _ _
    rw [this]
    simp only [eq_comm]
  · rw [colourKron_apply]
    have h1 : |totalKernel (κ v) i.1.1 j.1.1 * (if i.2 = j.2 then 1 else 0)| ≤ |totalKernel (κ v) i.1.1 j.1.1| := by
      by_cases h : i.2 = j.2 <;> simp [h]
    refine h1.trans ?_
    have h2 : totalKernel (κ v) i.1.1 j.1.1 = ∑ y ∈ Y v, κ v y i.1.1 j.1.1 := by
      simp only [totalKernel]
      exact (Finset.sum_subset (Finset.subset_univ _) fun y _ hy => off v y hy _ _).symm
    rw [h2, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ => ?_)
    exact (dec v y _ _).trans (mul_le_mul_of_nonneg_left (exp_neg_mul_max_le hc) hC)
  · have := sum_boxIndex_exp_le S (by positivity : 0 < c / 2) y
    rw [e8] at this
    exact this.trans (le_max_left _ _)
  · have h1 : ∑ y, siteWeight S c i y = ∑ y : TorusSite n, Real.exp (-(c / 2 * (_root_.YangMills.Construction.TorusFields.supDist y i.1.1.1 : ℝ))) :=
      Finset.sum_congr rfl fun y _ => by simp only [siteWeight, supDist_comm i.1.1.1 y]
    rw [h1]
    have h2 := sum_sites_exp_le (by positivity : 0 < c / 2) i.1.1.1
    rw [e8] at h2
    refine h2.trans (le_trans ?_ (le_max_left _ _))
    have : 0 ≤ expIntSum (c / 8) ^ 4 := by positivity
    linarith
  · have key := far v w hn y hy y' hy'
    have h1 : ∀ i : BoxIndex S, siteWeight S c i y * siteWeight S c i y' ≤
        Real.exp (-(c / 4 * Dd)) * Real.exp (-(c / 4 * (_root_.YangMills.Construction.TorusFields.supDist i.1.1.1 y : ℝ))) := by
      intro i
      simp only [siteWeight]
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.2
      have h2 : (_root_.YangMills.Construction.TorusFields.supDist y y' : ℝ) ≤ (_root_.YangMills.Construction.TorusFields.supDist i.1.1.1 y : ℝ) + (_root_.YangMills.Construction.TorusFields.supDist i.1.1.1 y' : ℝ) := by
        have := supDist_triangle y i.1.1.1 y'
        rw [supDist_comm y i.1.1.1] at this
        exact_mod_cast this
      have h3 : (0 : ℝ) ≤ _root_.YangMills.Construction.TorusFields.supDist i.1.1.1 y' := by positivity
      nlinarith
    have h2 := sum_boxIndex_exp_le S (by positivity : 0 < c / 4) y
    rw [e16] at h2
    calc ∑ i, siteWeight S c i y * siteWeight S c i y' ≤
          ∑ i : BoxIndex S, Real.exp (-(c / 4 * Dd)) * Real.exp (-(c / 4 * (_root_.YangMills.Construction.TorusFields.supDist i.1.1.1 y : ℝ))) :=
          Finset.sum_le_sum fun i _ => h1 i
      _ = Real.exp (-(c / 4 * Dd)) * ∑ i : BoxIndex S, Real.exp (-(c / 4 * (_root_.YangMills.Construction.TorusFields.supDist i.1.1.1 y : ℝ))) := by rw [Finset.mul_sum]
      _ ≤ Real.exp (-(c / 4 * Dd)) * (48 * expIntSum (c / 16) ^ 4) := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ = _ := by ring
  · have h1 : ∀ i ∈ Finset.univ.filter (fun i => i ∉ In), siteWeight S c i y ≤
        Real.exp (-(c / 4 * Dd₂)) * Real.exp (-(c / 4 * (_root_.YangMills.Construction.TorusFields.supDist i.1.1.1 y : ℝ))) := by
      intro i hi
      have h3 := out v y hy i (Finset.mem_filter.1 hi).2
      simp only [siteWeight]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      nlinarith
    have h2 := sum_boxIndex_exp_le S (by positivity : 0 < c / 4) y
    rw [e16] at h2
    calc ∑ i ∈ Finset.univ.filter (fun i => i ∉ In), siteWeight S c i y
        ≤ ∑ i ∈ Finset.univ.filter (fun i => i ∉ In), Real.exp (-(c / 4 * Dd₂)) * Real.exp (-(c / 4 * (_root_.YangMills.Construction.TorusFields.supDist i.1.1.1 y : ℝ))) :=
          Finset.sum_le_sum h1
      _ ≤ ∑ i : BoxIndex S, Real.exp (-(c / 4 * Dd₂)) * Real.exp (-(c / 4 * (_root_.YangMills.Construction.TorusFields.supDist i.1.1.1 y : ℝ))) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ => by positivity
      _ = Real.exp (-(c / 4 * Dd₂)) * ∑ i : BoxIndex S, Real.exp (-(c / 4 * (_root_.YangMills.Construction.TorusFields.supDist i.1.1.1 y : ℝ))) := by rw [Finset.mul_sum]
      _ ≤ Real.exp (-(c / 4 * Dd₂)) * (48 * expIntSum (c / 16) ^ 4) := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ = _ := by ring
end Domination
section Neighbourhoods
variable {n : ℕ} [NeZero n]
open Classical in
private def neighbourhood (W : Finset (TorusSite n)) : Finset (TorusSite n) :=
  Finset.univ.filter fun y => ∃ z ∈ W, _root_.YangMills.Construction.TorusFields.supDist y z ≤ 2
private lemma lt_supDist_of_not_mem_neighbourhood {W : Finset (TorusSite n)} {y : TorusSite n} (hy : y ∉ neighbourhood W) :
    ∀ z ∈ W, 2 < _root_.YangMills.Construction.TorusFields.supDist y z := by
  intro z hz
  by_contra h
  exact hy (Finset.mem_filter.2 ⟨Finset.mem_univ _, z, hz, not_lt.1 h⟩)
private lemma supDist_le_of_mem_neighbourhood {W : Finset (TorusSite n)} {z₀ : TorusSite n} {r : ℝ} (hW : W ⊆ supBall z₀ r)
    {y : TorusSite n} (hy : y ∈ neighbourhood W) : (_root_.YangMills.Construction.TorusFields.supDist y z₀ : ℝ) ≤ r + 2 := by
  obtain ⟨z, hz, hd⟩ := (Finset.mem_filter.1 hy).2
  have h1 : (_root_.YangMills.Construction.TorusFields.supDist z z₀ : ℝ) ≤ r := (Finset.mem_filter.1 (hW hz)).2
  have h2 := supDist_triangle y z z₀
  have h3 : (_root_.YangMills.Construction.TorusFields.supDist y z₀ : ℝ) ≤ (_root_.YangMills.Construction.TorusFields.supDist y z : ℝ) + (_root_.YangMills.Construction.TorusFields.supDist z z₀ : ℝ) := by exact_mod_cast h2
  have h4 : (_root_.YangMills.Construction.TorusFields.supDist y z : ℝ) ≤ 2 := by exact_mod_cast hd
  linarith
private lemma card_neighbourhood_le {W : Finset (TorusSite n)} {z₀ : TorusSite n} {r : ℝ} (hr : 0 ≤ r) (hW : W ⊆ supBall z₀ r) :
    ((neighbourhood W).card : ℝ) ≤ (2 * (r + 2) + 1) ^ 4 := by
  have h1 : neighbourhood W ⊆ Finset.univ.filter fun z : TorusSite n => _root_.YangMills.Construction.TorusFields.supDist z z₀ ≤ ⌊r + 2⌋₊ := by
    intro y hy
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, Nat.le_floor (supDist_le_of_mem_neighbourhood hW hy)⟩
  have h2 := (Finset.card_le_card h1).trans (card_supBall_le z₀ ⌊r + 2⌋₊)
  have h3 : ((neighbourhood W).card : ℝ) ≤ (2 * (⌊r + 2⌋₊ : ℝ) + 1) ^ 4 := by exact_mod_cast h2
  refine h3.trans (pow_le_pow_left₀ (by positivity) ?_ 4)
  have := Nat.floor_le (show 0 ≤ r + 2 by linarith)
  linarith
private lemma le_supDist_of_translates {W W' : Finset (TorusSite n)} {z : TorusSite n} {a b : Fin 4 → ℤ} {r : ℝ}
    (hW : W ⊆ supBall (z + siteOfInt a) r) (hW' : W' ⊆ supBall (z + siteOfInt b) r) (i : Fin 4)
    (h2 : 2 * (a i - b i).natAbs ≤ n) {y y' : TorusSite n} (hy : y ∈ neighbourhood W) (hy' : y' ∈ neighbourhood W') :
    ((a i - b i).natAbs : ℝ) - 2 * (r + 2) ≤ (_root_.YangMills.Construction.TorusFields.supDist y y' : ℝ) := by
  have h3 := le_supDist_translate z a b i h2
  have h4 : _root_.YangMills.Construction.TorusFields.supDist (z + siteOfInt a) (z + siteOfInt b) ≤
      _root_.YangMills.Construction.TorusFields.supDist (z + siteOfInt a) y + _root_.YangMills.Construction.TorusFields.supDist y y' + _root_.YangMills.Construction.TorusFields.supDist y' (z + siteOfInt b) :=
    (supDist_triangle _ y' _).trans (add_le_add (supDist_triangle _ y _) le_rfl)
  have d1 := supDist_le_of_mem_neighbourhood hW hy
  have d2 := supDist_le_of_mem_neighbourhood hW' hy'
  rw [supDist_comm (z + siteOfInt a) y] at h4
  have h5 : ((a i - b i).natAbs : ℝ) ≤ (_root_.YangMills.Construction.TorusFields.supDist y (z + siteOfInt a) : ℝ) + (_root_.YangMills.Construction.TorusFields.supDist y y' : ℝ) + (_root_.YangMills.Construction.TorusFields.supDist y' (z + siteOfInt b) : ℝ) := by
    exact_mod_cast h3.trans h4
  linarith
private lemma natAbs_valMinAbs_one_le (hn : 2 ≤ n) : (((1 : ZMod n)).valMinAbs).natAbs ≤ 1 := by
  have := natAbs_valMinAbs_intCast (N := n) 1 (by simpa using hn)
  simp at this
  omega
abbrev _root_.YangMills.SharedProofs.p10270 := @natAbs_valMinAbs_one_le
private lemma supDist_vertex_le_one (hn : 2 ≤ n) {x z : TorusSite n} {μ ν : Fin 4} (hμν : μ ≠ ν)
    (hz : z ∈ plaquetteVertices x μ ν) : _root_.YangMills.Construction.TorusFields.supDist z x ≤ 1 := by
  have h1 := natAbs_valMinAbs_one_le hn
  simp only [plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false] at hz
  refine Finset.sup_le fun i _ => ?_
  rcases hz with rfl | rfl | rfl | rfl
  · simp
  · by_cases h : i = μ
    · subst h; simpa [TorusFields.unitStep] using h1
    · simp [TorusFields.unitStep, h]
  · by_cases h : i = ν
    · subst h; simpa [TorusFields.unitStep] using h1
    · simp [TorusFields.unitStep, h]
  · by_cases h : i = μ
    · subst h
      have : i ≠ ν := hμν
      simpa [TorusFields.unitStep, Pi.single_apply, this] using h1
    · by_cases h' : i = ν
      · subst h'; simpa [TorusFields.unitStep, Pi.single_apply, h] using h1
      · simp [TorusFields.unitStep, h, h']
private lemma le_supDist_of_not_mem_inner (hn : 2 ≤ n) {o : TorusSite n} {R : ℕ} {W : Finset (TorusSite n)}
    (hW : W ⊆ supBall o (3 * (R : ℝ) / 32))
    {y : TorusSite n} (hy : y ∈ neighbourhood W) {p : TorusPlaquette n} (hp : p.2.1 < p.2.2)
    (hnot : p ∉ plaquettesIn (supBall o ((R : ℝ) / 8))) :
    (R : ℝ) / 32 - 4 ≤ (_root_.YangMills.Construction.TorusFields.supDist p.1 y : ℝ) := by
  classical
  have h1 : ∃ z ∈ plaquetteVertices p.1 p.2.1 p.2.2, z ∉ supBall o ((R : ℝ) / 8) := by
    by_contra h
    push Not at h
    exact hnot (Finset.mem_filter.2 ⟨Finset.mem_univ _, hp, h⟩)
  obtain ⟨z, hz, hz'⟩ := h1
  have h2 : (R : ℝ) / 8 < (_root_.YangMills.Construction.TorusFields.supDist z o : ℝ) := by
    by_contra h
    exact hz' (Finset.mem_filter.2 ⟨Finset.mem_univ _, not_lt.1 h⟩)
  have h3 : (_root_.YangMills.Construction.TorusFields.supDist z p.1 : ℝ) ≤ 1 := by exact_mod_cast supDist_vertex_le_one hn hp.ne hz
  have h4 := supDist_le_of_mem_neighbourhood hW hy
  have h5 : _root_.YangMills.Construction.TorusFields.supDist z o ≤ _root_.YangMills.Construction.TorusFields.supDist z p.1 + _root_.YangMills.Construction.TorusFields.supDist p.1 y + _root_.YangMills.Construction.TorusFields.supDist y o :=
    (supDist_triangle _ y _).trans (add_le_add (supDist_triangle _ p.1 _) le_rfl)
  have h6 : (_root_.YangMills.Construction.TorusFields.supDist z o : ℝ) ≤ (_root_.YangMills.Construction.TorusFields.supDist z p.1 : ℝ) + (_root_.YangMills.Construction.TorusFields.supDist p.1 y : ℝ) + (_root_.YangMills.Construction.TorusFields.supDist y o : ℝ) := by exact_mod_cast h5
  linarith
end Neighbourhoods
section Shifts
private def ShiftsNear (B : ℕ) {m : ℕ} (v w : ↥(shiftSet m)) : Prop := ∀ i, |v.1 i - w.1 i| ≤ (B : ℤ)
private lemma card_shiftSet (m : ℕ) : ((shiftSet m).card : ℝ) = (2 * (m : ℝ) + 1) ^ 4 := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolNorm.card_intCube <;> assumption
open Classical in
private lemma card_nearShiftPairs_le (B m : ℕ) :
    ((Finset.univ.filter fun p : ↥(shiftSet m) × ↥(shiftSet m) => ShiftsNear B p.1 p.2).card : ℝ) ≤
      ((2 * (B : ℝ) + 1) ^ 4 / (2 * (m : ℝ) + 1) ^ 4) * (Fintype.card ↥(shiftSet m) : ℝ) ^ 2 := by
  set s := Finset.univ.filter fun p : ↥(shiftSet m) × ↥(shiftSet m) => ShiftsNear B p.1 p.2 with hs
  have h1 : s.card ≤ (2 * B + 1) ^ 4 * (s.image Prod.fst).card := by
    refine Finset.card_le_mul_card_image s _ fun a _ => ?_
    have h2 := Finset.card_le_card_of_injOn (s := s.filter fun x => x.1 = a)
      (t := Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(B : ℤ)) B) (fun p i => p.2.1 i - a.1 i)
      (fun p hp => by
        have hp' := Finset.mem_filter.1 hp
        have hn := (Finset.mem_filter.1 hp'.1).2
        refine Fintype.mem_piFinset.2 fun i => ?_
        have h3 := hn i
        rw [hp'.2] at h3
        rw [abs_sub_comm] at h3
        exact Finset.mem_Icc.2 (abs_le.1 h3))
      (fun p hp p' hp' h => by
        have e1 := (Finset.mem_filter.1 hp).2
        have e2 := (Finset.mem_filter.1 hp').2
        refine Prod.ext (e1.trans e2.symm) (Subtype.ext ?_)
        funext i
        have := congrFun h i
        simpa using this)
    refine h2.trans (le_of_eq ?_)
    rw [Fintype.card_piFinset]
    simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 1
    omega
  have h3 : (s.image Prod.fst).card ≤ Fintype.card ↥(shiftSet m) := Finset.card_le_univ _
  have h4 : (s.card : ℝ) ≤ (2 * (B : ℝ) + 1) ^ 4 * (Fintype.card ↥(shiftSet m) : ℝ) := by
    have : s.card ≤ (2 * B + 1) ^ 4 * Fintype.card ↥(shiftSet m) := h1.trans (Nat.mul_le_mul_left _ h3)
    exact_mod_cast this
  have h5 : (Fintype.card ↥(shiftSet m) : ℝ) = (2 * (m : ℝ) + 1) ^ 4 := by
    rw [Fintype.card_coe, card_shiftSet]
  refine h4.trans (le_of_eq ?_)
  rw [h5]
  have : (2 * (m : ℝ) + 1) ^ 4 ≠ 0 := by positivity
  field_simp
private lemma average_subtype_eq {m : ℕ} (F : (Fin 4 → ℤ) → ℝ) :
    average (fun v : ↥(shiftSet m) => F v.1) = ((shiftSet m).card : ℝ)⁻¹ * ∑ v ∈ shiftSet m, F v := by
  simp only [QuadraticConcentration.average, Fintype.card_coe]
  rw [Finset.sum_coe_sort (shiftSet m) F]
end Shifts
section Parameters
private lemma holdsForShapes_odd_side : HoldsForShapes fun T _ _ _ _ => Odd T.side := by
  intro a ha
  refine ⟨0, fun _ => 1, 0, fun _ => one_pos, ?_⟩
  intro L hL hLL T e₁ e₂ hD hS hH hrt hC Kr
  exact ⟨0, fun y hy hR hK Xi hXi vt hv hv1 => by show Odd T.side; rw [e₂]; exact hL⟩
private lemma three_terms_le_sum {C₂ G N o t : ℝ} (hC : 0 ≤ C₂) (hG : 0 ≤ G) (hN : 0 ≤ N) (ho : 0 ≤ o) (ht : 0 ≤ t) :
    C₂ ^ 2 * N ^ 2 * o ^ 2 ≤ C₂ ^ 2 * N ^ 2 * o ^ 2 + C₂ ^ 2 * o * N * G ^ 2 + t ^ 2 * C₂ ^ 2 * G ^ 2 * N ^ 2 * o ∧
    C₂ ^ 2 * o * N * G ^ 2 ≤ C₂ ^ 2 * N ^ 2 * o ^ 2 + C₂ ^ 2 * o * N * G ^ 2 + t ^ 2 * C₂ ^ 2 * G ^ 2 * N ^ 2 * o ∧
    t ^ 2 * C₂ ^ 2 * G ^ 2 * N ^ 2 * o ≤ C₂ ^ 2 * N ^ 2 * o ^ 2 + C₂ ^ 2 * o * N * G ^ 2 + t ^ 2 * C₂ ^ 2 * G ^ 2 * N ^ 2 * o := by
  have a1 : 0 ≤ C₂ ^ 2 * N ^ 2 * o ^ 2 := by positivity
  have a2 : 0 ≤ C₂ ^ 2 * o * N * G ^ 2 := by positivity
  have a3 : 0 ≤ t ^ 2 * C₂ ^ 2 * G ^ 2 * N ^ 2 * o := by positivity
  exact ⟨by linarith, by linarith, by linarith⟩
end Parameters
set_option maxHeartbeats 6400000 in
theorem boxProductsStatement_of_components (h₁ : formsOnEventStatement) (h₂ : sitesDominatedFormFamilyStatement)
    (h₃ : boxExponentsStatement) (h₄ : boxSizesStatement) (h₅ : responseMomentsStatement)
    (h₆ : translateSitesStatement) (h₇ : separationLevelStatement) (h₈ : couplingAtSeparation_tendsto_statement)
    (h₉ : curlCovarianceBoundsStatement) : boxProductsStatement := by
  have hAll := HoldsForShapes.and h₅ (HoldsForShapes.and (HoldsForShapes.of_holdsOnParameters h₇)
    (HoldsForShapes.and (HoldsForShapes.of_holdsOnParameters h₈) (HoldsForShapes.and HoldsForShapes.params holdsForShapes_odd_side)))
  unfold boxProductsStatement
  refine hAll.mono ?_
  rintro Tb y Kr Xi vt ⟨hM, hLv, hCp, ⟨hDrawn, -, -, hKr, hXi, hvt0, hvt1⟩, hOdd⟩ C₁ c₁ Cj xp hc₁
  obtain ⟨Cm, dm, hCm, hdm, hmom⟩ := hM
  obtain ⟨R₀, hR₀⟩ := h₉ Tb hDrawn
  set C₂ := max C₁ 1 with hC₂
  have hC₂1 : 1 ≤ C₂ := le_max_right _ _
  have hC₁₂ : C₁ ≤ C₂ := le_max_left _ _
  have hC₂0 : 0 ≤ C₂ := by linarith
  set G := max (48 * expIntSum (c₁ / 8) ^ 4) 1 with hG
  have hG1 : 1 ≤ G := le_max_right _ _
  have hG0 : 0 ≤ G := by linarith
  set Tt := 48 * expIntSum (c₁ / 16) ^ 4 with hTt
  have hTt0 : 0 ≤ Tt := by have := expIntSum_nonneg (c₁ / 16); positivity
  have hLr : (1 : ℝ) ≤ ((Tb.stepParameters y).side : ℝ) := by
    have : 1 ≤ (Tb.stepParameters y).side := Nat.one_le_iff_ne_zero.2 (NeZero.ne _)
    exact_mod_cast this
  obtain ⟨x₀, hx₀1, hsz⟩ := h₄ C₂ c₁ G Tt ((Tb.stepParameters y).side : ℝ) Cm R₀ hC₂1 hc₁ hG1 hTt0 hLr hCm
  obtain ⟨C₀, hC₀, hform⟩ := h₁ (C₂ * G ^ 2) (by positivity)
  obtain ⟨Cc, x₁, hx₁, hexp⟩ := h₃ C₀ Cm hC₀ hCm
  set pN := ⌈32 * (2 * Cm + 4)⌉₊ with hpN
  obtain ⟨d₁, hd₁, hd⟩ := hCp Xi hXi (max x₀ (max x₁ (xp pN)))
  refine ⟨Cc, min d₁ (min dm (1 / 2)), lt_min hd₁ (lt_min hdm (by norm_num)), ?_⟩
  intro d hd0 hdd K β al T hCh k m R x hk hx hR hm hW f h hpair o hf hh c c₀ hChart κ κ' κ₀ κ₀' hM1 hM2
  subst hR
  subst hm
  have hdd1 : d ≤ d₁ := hdd.trans (min_le_left _ _)
  have hddm : d ≤ dm := hdd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdlt : d < 1 := lt_of_le_of_lt (hdd.trans ((min_le_right _ _).trans (min_le_right _ _))) (by norm_num)
  have hXx : max x₀ (max x₁ (xp pN)) ≤ x := by
    rw [hx]; exact hd d hd0 hdd1 K β hCh.isFlowDatum hCh.minimalCutoff_le
  have hx₀x : x₀ ≤ x := (le_max_left _ _).trans hXx
  have hx₁x : x₁ ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hXx
  have hxpx : xp pN ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hXx
  have hx1 : 1 ≤ x := hx₀1.trans hx₀x
  have hx0 : 0 < x := by linarith
  obtain ⟨far, klt, nle⟩ := hLv Xi hXi d hd0 hdlt K β hCh.isFlowDatum hCh.minimalCutoff_le
  have hkK : k ≤ K := by rw [hk]; exact klt.le
  set nn := lengthInSites (Tb.stepParameters y).side K k d with hnn
  have far' : 2 ^ 12 * (clusterRange x : ℝ) ≤ nn := by
    rw [hnn, hx, hk]; exact far
  have nle' : nn ≤ 2 ^ 13 * ((Tb.stepParameters y).side : ℝ) * (clusterRange x : ℝ) := by
    rw [hnn, hx, hk]; exact nle
  obtain ⟨sizes, hR₀R, hm16, hlog1, hτ, he, hu, hmassA, hmassB⟩ := hsz x nn hx₀x far' nle'
  obtain ⟨hprob, hstate, hresp⟩ := hmom d hd0 hddm K β al T hCh k x hk hx
  have := hprob
  have ht := hpair.mem_class
  simp only [TestFunctions.separatedPairsR4, TestFunctions.separatedPairs, Set.mem_ofPred_eq] at ht
  obtain ⟨xf, xh, bf, bh, -, -⟩ := ht
  obtain ⟨zf, hzf⟩ := h₆ (Tb.stepParameters y).side K k hOdd hkK d xf f hd0 bf.2.2.2.1
  obtain ⟨zh, hzh⟩ := h₆ (Tb.stepParameters y).side K k hOdd hkK d xh h hd0 bh.2.2.2.1
  have hRbig : 256 ≤ boxRadius x := by
    have : 16 ≤ boxRadius x / 16 := hm16
    omega
  have hm4 : 4 * averagingRadius x ≤ boxRadius x := by
    have : averagingRadius x = boxRadius x / 16 := rfl
    omega
  have hN2 : 2 ≤ (boxSide (Tb.stepParameters y).side K k) := by omega
  have hn0 : 0 ≤ nn := le_trans (by positivity) far'
  have hDiff : ∀ (v w : ↥(shiftSet (averagingRadius x))) (i : Fin 4),
      2 * (v.1 i - w.1 i).natAbs ≤ (boxSide (Tb.stepParameters y).side K k) := by
    intro v w i
    have a1 := Finset.mem_Icc.1 (Fintype.mem_piFinset.1 v.2 i)
    have a2 := Finset.mem_Icc.1 (Fintype.mem_piFinset.1 w.2 i)
    omega
  have hfarS : ∀ (W : (Fin 4 → ℤ) → Finset (TorusSite (boxSide (Tb.stepParameters y).side K k)))
      (z : TorusSite (boxSide (Tb.stepParameters y).side K k)), (∀ v, W v ⊆ supBall (z + siteOfInt v) (nn + 4)) →
      ∀ v w : ↥(shiftSet (averagingRadius x)), ¬ ShiftsNear (nearTranslateRadius nn) v w →
        ∀ y ∈ neighbourhood (W v.1), ∀ y' ∈ neighbourhood (W w.1), nn ≤ (_root_.YangMills.Construction.TorusFields.supDist y y' : ℝ) := by
    intro W z hWz v w hn y hy y' hy'
    simp only [ShiftsNear, not_forall, not_le] at hn
    obtain ⟨i, hi⟩ := hn
    have a1 := le_supDist_of_translates (hWz v.1) (hWz w.1) i (hDiff v w i) hy hy'
    have a2 : nearTranslateRadius nn + 1 ≤ (v.1 i - w.1 i).natAbs := by
      have : ((nearTranslateRadius nn : ℕ) : ℤ) < ((v.1 i - w.1 i).natAbs : ℤ) := by
        rw [Int.natCast_natAbs]; exact hi
      omega
    have a3 : ((nearTranslateRadius nn : ℝ)) + 1 ≤ ((v.1 i - w.1 i).natAbs : ℝ) := by exact_mod_cast a2
    have a4 : 3 * nn + 12 ≤ (nearTranslateRadius nn : ℝ) := by
      have : (nearTranslateRadius nn : ℝ) = (⌈3 * nn⌉₊ : ℝ) + 12 := by simp [nearTranslateRadius]
      rw [this]
      have := Nat.le_ceil (3 * nn)
      linarith
    linarith
  have hcardS : ∀ (W : Finset (TorusSite (boxSide (Tb.stepParameters y).side K k)))
      (z : TorusSite (boxSide (Tb.stepParameters y).side K k)), W ⊆ supBall z (nn + 4) →
      ((neighbourhood W).card : ℝ) ≤ translateSiteBound nn := by
    intro W z hWz
    have := card_neighbourhood_le (by linarith) hWz
    refine this.trans (le_of_eq ?_)
    unfold translateSiteBound
    ring
  set In : Set (BoxIndex (supBall o (2 * (boxRadius x : ℝ)))) :=
    {i | i.1.1 ∈ plaquettesIn (supBall o ((boxRadius x : ℝ) / 8))} with hIn
  have houtS : ∀ W : Finset (TorusSite (boxSide (Tb.stepParameters y).side K k)),
      W ⊆ supBall o (3 * (boxRadius x : ℝ) / 32) → ∀ y ∈ neighbourhood W, ∀ i : BoxIndex (supBall o (2 * (boxRadius x : ℝ))),
        i ∉ In → (boxRadius x : ℝ) / 32 - 4 ≤ (_root_.YangMills.Construction.TorusFields.supDist i.1.1.1 y : ℝ) := by
    intro W hWo y hy i hi
    exact le_supDist_of_not_mem_inner hN2 hWo hy (Finset.mem_filter.1 i.1.2).2.1 hi
  have hKf := fun v : ↥(shiftSet (averagingRadius x)) => hM1.isWeightKernel v.1 v.2
  have hKh := fun v : ↥(shiftSet (averagingRadius x)) => hM2.isWeightKernel v.1 v.2
  have domF := dominatedBySites_of_kernels (supBall o (2 * (boxRadius x : ℝ))) (fun v : ↥(shiftSet (averagingRadius x)) => κ v.1)
    (fun v => neighbourhood (weightSitesOf (Tb.stepParameters y).side K k (translateBy (Tb.stepParameters y).side K k v.1 f)))
    (ShiftsNear (nearTranslateRadius nn)) In
    (C := C₂) (c := c₁) (Nc := translateSiteBound nn) (Dd := nn) (Dd₂ := (boxRadius x : ℝ) / 32 - 4) hc₁ hC₂0
    (fun v y p p' => (hKf v).symm y p p')
    (fun v y p p' => ((hKf v).decay y p p').trans (mul_le_mul_of_nonneg_right hC₁₂ (Real.exp_pos _).le))
    (fun v y hy p p' => (hKf v).vanish_far y (lt_supDist_of_not_mem_neighbourhood hy) p p')
    (fun v => hcardS _ _ (hzf v.1))
    (fun v w hn => hfarS _ zf (fun v => hzf v) v w hn)
    (fun v y hy => houtS _ (hf v.1 v.2) y hy)
  have domH := dominatedBySites_of_kernels (supBall o (2 * (boxRadius x : ℝ))) (fun v : ↥(shiftSet (averagingRadius x)) => κ' v.1)
    (fun v => neighbourhood (weightSitesOf (Tb.stepParameters y).side K k (translateBy (Tb.stepParameters y).side K k v.1 h)))
    (ShiftsNear (nearTranslateRadius nn)) In
    (C := C₂) (c := c₁) (Nc := translateSiteBound nn) (Dd := nn) (Dd₂ := (boxRadius x : ℝ) / 32 - 4) hc₁ hC₂0
    (fun v y p p' => (hKh v).symm y p p')
    (fun v y p p' => ((hKh v).decay y p p').trans (mul_le_mul_of_nonneg_right hC₁₂ (Real.exp_pos _).le))
    (fun v y hy p p' => (hKh v).vanish_far y (lt_supDist_of_not_mem_neighbourhood hy) p p')
    (fun v => hcardS _ _ (hzh v.1))
    (fun v w hn => hfarS _ zh (fun v => hzh v) v w hn)
    (fun v y hy => houtS _ (hh v.1 v.2) y hy)
  have hs0 : 0 ≤ boxScale x := by
    have := Real.log_nonneg hx1
    unfold boxScale
    positivity
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hR0 : (0 : ℝ) ≤ (boxRadius x : ℝ) := by positivity
  have hflat0 : 0 ≤ boxFlatness C₂ x := by
    have := sizes.φ_nonneg
    linarith
  have htop0 : 0 ≤ boxMeanCurlBound C₂ x := by unfold boxMeanCurlBound; positivity
  have hover0 : 0 ≤ farSiteOverlap Tt c₁ nn := by unfold farSiteOverlap; positivity
  have hout0 : 0 ≤ outsideBoxMass Tt c₁ x := by unfold outsideBoxMass; positivity
  have hNc0 : 0 ≤ translateSiteBound nn := by unfold translateSiteBound; positivity
  have hfarP := three_terms_le_sum (t := boxMeanCurlBound C₂ x) hC₂0 hG0 hNc0 hover0 htop0
  have hA1 : C₂ ^ 2 * G ^ 4 * translateSiteBound nn ≤ formFamilyMass C₂ G nn := by
    unfold formFamilyMass
    refine mul_le_mul_of_nonneg_right ?_ hNc0
    have : 0 ≤ C₂ * G ^ 2 := by positivity
    linarith
  have flatB : ∀ q ∈ c.goodOuter, ∀ i ∈ In,
      |plaquetteVector (supBall o (2 * (boxRadius x : ℝ))) (c.meanCurl q) i| ≤ boxFlatness C₂ x := by
    intro q hq i hi
    refine (abs_imaginaryComponent_le _ _).trans ((hChart.curl.meanCurl_le_inner q hq i.1.1 hi).trans ?_)
    unfold boxFlatness
    gcongr
  have topB : ∀ q ∈ c.goodOuter, ∀ i,
      |plaquetteVector (supBall o (2 * (boxRadius x : ℝ))) (c.meanCurl q) i| ≤ boxMeanCurlBound C₂ x := by
    intro q hq i
    refine (abs_imaginaryComponent_le _ _).trans ((hChart.curl.meanCurl_le q hq i.1.1 i.1.2).trans ?_)
    unfold boxMeanCurlBound
    gcongr
  have famOf : ∀ (Yv : ↥(shiftSet (averagingRadius x)) → Finset (TorusSite (boxSide (Tb.stepParameters y).side K k)))
      (Mv : ↥(shiftSet (averagingRadius x)) →
        Matrix (BoxIndex (supBall o (2 * (boxRadius x : ℝ)))) (BoxIndex (supBall o (2 * (boxRadius x : ℝ)))) ℝ),
      DominatedBySites (siteWeight (supBall o (2 * (boxRadius x : ℝ))) c₁) Yv Mv (ShiftsNear (nearTranslateRadius nn)) In C₂ G
        (translateSiteBound nn) (farSiteOverlap Tt c₁ nn) (outsideBoxMass Tt c₁ x) →
      ∀ q ∈ c.goodOuter, IsAdmissibleFormFamily (plaquetteVector (supBall o (2 * (boxRadius x : ℝ))) (c.meanCurl q)) Mv
        (ShiftsNear (nearTranslateRadius nn)) (C₂ * G ^ 2)
        (formFamilyMass C₂ G nn) (2 * boxFlatness C₂ x) (farPairError C₂ G Tt c₁ nn x) := fun Yv Mv hD q hq =>
    h₂ _ _ _ (siteWeight (supBall o (2 * (boxRadius x : ℝ))) c₁) Yv Mv (ShiftsNear (nearTranslateRadius nn)) In C₂ G
      (translateSiteBound nn) (farSiteOverlap Tt c₁ nn)
      (outsideBoxMass Tt c₁ x) (boxFlatness C₂ x) (boxMeanCurlBound C₂ x) (formFamilyMass C₂ G nn) (2 * boxFlatness C₂ x)
      (farPairError C₂ G Tt c₁ nn x) (plaquetteVector (supBall o (2 * (boxRadius x : ℝ))) (c.meanCurl q))
      hC₂0 hG0 hNc0 hover0 hout0 hflat0 htop0 sizes.ε_nonneg hD
      (flatB q hq) (topB q hq) hA1 hmassA hmassB hfarP.1 hfarP.2.1 hfarP.2.2
  obtain ⟨-, hTsym, -⟩ := hR₀ k (boxSide (Tb.stepParameters y).side K k) o (boxRadius x) hR₀R hW
  set Cm' := colourKron (supBall o (2 * (boxRadius x : ℝ)))
    (fun p p' => x⁻¹ * curlCovariance (Tb.stepParameters y).coupling (Tb.stepParameters y).side k o (boxRadius x) p p') with hCm'
  have hquad : ∀ t : BoxIndex (supBall o (2 * (boxRadius x : ℝ))) → ℝ, t ⬝ᵥ Cm'.mulVec t =
      x⁻¹ * curlQuadForm (Tb.stepParameters y).coupling (Tb.stepParameters y).side k o (boxRadius x)
        (extendByZero (supBall o (2 * (boxRadius x : ℝ))) t) := by
    intro t
    rw [hCm', ← quadForm_extendByZero]
    simp only [curlQuadForm, Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun p' _ => by ring
  have hxi : 0 < x⁻¹ := by positivity
  have hCsym : Cm'.IsSymm := by
    ext i j
    simp only [Matrix.transpose_apply, hCm', colourKron_apply]
    have e : curlCovariance (Tb.stepParameters y).coupling (Tb.stepParameters y).side k o (boxRadius x) j.1.1 i.1.1 =
        curlCovariance (Tb.stepParameters y).coupling (Tb.stepParameters y).side k o (boxRadius x) i.1.1 j.1.1 := hTsym j.1.1 i.1.1
    rw [e]
    simp only [eq_comm]
  have hPos : ∀ t : BoxIndex (supBall o (2 * (boxRadius x : ℝ))) → ℝ, 0 ≤ t ⬝ᵥ Cm'.mulVec t := fun t => by
    rw [hquad]
    exact mul_nonneg hxi.le (hChart.quadForm_bounds _).1
  have hTop : ∀ t : BoxIndex (supBall o (2 * (boxRadius x : ℝ))) → ℝ, t ⬝ᵥ Cm'.mulVec t ≤ C₂ / x * (t ⬝ᵥ t) := fun t => by
    rw [hquad]
    have h1 := (hChart.quadForm_bounds (extendByZero (supBall o (2 * (boxRadius x : ℝ))) t)).2
    rw [sum_sq_extendByZero] at h1
    have ht : 0 ≤ t ⬝ᵥ t := by simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    calc x⁻¹ * curlQuadForm (Tb.stepParameters y).coupling (Tb.stepParameters y).side k o (boxRadius x)
          (extendByZero (supBall o (2 * (boxRadius x : ℝ))) t) ≤ x⁻¹ * (C₁ * (t ⬝ᵥ t)) := by gcongr
      _ ≤ x⁻¹ * (C₂ * (t ⬝ᵥ t)) := by gcongr
      _ = C₂ / x * (t ⬝ᵥ t) := by rw [div_eq_mul_inv]; ring
  have hE := measurableSet_event c hChart.measurable hstate
  have hp32 : 32 * (2 * Cm + 4) ≤ (pN : ℝ) := Nat.le_ceil _
  have hlike : stageLaw T β K k c.eventᶜ ≤ ENNReal.ofReal (x ^ (-(32 * (2 * Cm + 4)) : ℝ)) := by
    have h1 := hChart.prob_event_ge pN hxpx
    have h2 : (stageLaw T β K k).real c.eventᶜ = 1 - (stageLaw T β K k).real c.event := probReal_compl_eq_one_sub hE
    have h3 : (stageLaw T β K k).real c.eventᶜ ≤ x ^ (-(32 * (2 * Cm + 4)) : ℝ) := by
      have h4 : x ^ (-(pN : ℝ)) ≤ x ^ (-(32 * (2 * Cm + 4)) : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      linarith
    have h5 : stageLaw T β K k c.eventᶜ = ENNReal.ofReal ((stageLaw T β K k).real c.eventᶜ) := by
      rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    rw [h5]
    exact ENNReal.ofReal_le_ofReal h3
  have hxq : x ^ (-(1 / 7) : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)
  have he' : Real.exp (2 * (C₁ * (boxRadius x : ℝ) ^ 9 * x ^ (-(1 / 2) : ℝ) * Real.log x ^ 3)) ≤
      (1 + weightExcess C₂ x) * (1 - Real.exp (-((boxRadius x : ℝ) ^ 4))) := by
    refine (Real.exp_le_exp.2 ?_).trans he
    unfold logWeightBound
    gcongr
  have hη1 : 0 < 1 + weightExcess C₂ x := by
    have := sizes.η_pos
    linarith
  have hbelow := chart_dominatedByGaussians c (P := stageLaw T β K k) hη1 hChart.measurable hstate hChart.law he' hu
  have errLe : C₁ * lengthInSites (Tb.stepParameters y).side K k d ^ 4 * (boxRadius x : ℝ) ^ 8 * boxScale x ^ 3 +
      Real.exp (-(c₁ * (boxRadius x : ℝ))) ≤ marksRemainder C₂ c₁ nn x := by
    unfold marksRemainder
    gcongr
  have hzero : ∀ w : AmbientSpace → ℝ, MemLp (centeredBoxResponse T β al K k w) 64 (stageLaw T β K k) →
      ∫ u, centeredBoxResponse T β al K k w u ∂stageLaw T β K k = 0 := by
    intro w hw
    have hi : Integrable (centeredBoxResponse T β al K k w) (stageLaw T β K k) := hw.integrable (by norm_num)
    have hF : Integrable (boxResponse T β al K k w) (stageLaw T β K k) := by
      refine (hi.add (integrable_const (∫ u', boxResponse T β al K k w u' ∂stageLaw T β K k))).congr
        (Filter.Eventually.of_forall fun u => ?_)
      simp [centeredBoxResponse]
    simp only [centeredBoxResponse]
    rw [integral_sub hF (integrable_const _)]
    simp
  have H : QuadraticFormsOnEvent (stageLaw T β K k) c.event (chartCurlVector c) Cm' (chartGaussians c x)
      (fun v : ↥(shiftSet (averagingRadius x)) => colourKron (supBall o (2 * (boxRadius x : ℝ))) (totalKernel (κ v.1)))
      (fun v : ↥(shiftSet (averagingRadius x)) => colourKron (supBall o (2 * (boxRadius x : ℝ))) (totalKernel (κ' v.1)))
      (ShiftsNear (nearTranslateRadius nn))
      (fun (v : ↥(shiftSet (averagingRadius x))) u =>
        centeredBoxResponse T β al K k (translateBy (Tb.stepParameters y).side K k v.1 f) u)
      (fun (v : ↥(shiftSet (averagingRadius x))) u =>
        centeredBoxResponse T β al K k (translateBy (Tb.stepParameters y).side K k v.1 h) u)
      (fun v => κ₀ v.1 - ∫ w, boxResponse T β al K k (translateBy (Tb.stepParameters y).side K k v.1 f) w ∂stageLaw T β K k)
      (fun v => κ₀' v.1 - ∫ w, boxResponse T β al K k (translateBy (Tb.stepParameters y).side K k v.1 h) w ∂stageLaw T β K k)
      (C₂ * G ^ 2) (C₂ / x) (formFamilyMass C₂ G nn) (2 * boxFlatness C₂ x)
      (farPairError C₂ G Tt c₁ nn x) (nearPairShare nn x) (weightExcess C₂ x) (marksRemainder C₂ c₁ nn x) (x ^ Cm)
      (x ^ (-(32 * (2 * Cm + 4)) : ℝ)) :=
    { isProbability := hprob
      measurableSet := hE
      compl_le := hlike
      τ_nonneg := sizes.τ_nonneg
      τ_le := hτ
      measurable_indicator := measurable_indicator_chartCurlVector c hChart.measurable hstate
      dominated := hbelow
      η_pos := sizes.η_pos
      η_le := sizes.η_le.trans hxq
      lam_pos := sizes.lam_pos
      one_le_A := sizes.one_le_A
      φ_nonneg := sizes.φ_nonneg
      ε_nonneg := sizes.ε_nonneg
      ρ_nonneg := sizes.ρ_nonneg
      err_nonneg := sizes.err_nonneg
      D_nonneg := sizes.D_nonneg
      symm := hCsym
      posSemidef := hPos
      quad_le := hTop
      gaussian_family := fun p hp => by
        obtain ⟨q, hq, rfl⟩ := hp
        have := (hChart.law.ellipsoid_mass q hq).1
        exact ⟨isCenteredGaussian_curl _ hx0 (hChart.curl.map_eq_gaussian q hq) (fun u => (hChart.quadForm_bounds u).1),
          famOf _ _ domF q hq, famOf _ _ domH q hq⟩
      near_card_le := card_nearShiftPairs_le (nearTranslateRadius nn) (averagingRadius x)
      approx_left := hM1.response_approx.mono fun u hu hmem v => by
        have a := hu hmem v.1 v.2
        have e : (1 / 2 : ℝ) * (chartCurlVector c u ⬝ᵥ
            (colourKron (supBall o (2 * (boxRadius x : ℝ))) (totalKernel (κ v.1))).mulVec (chartCurlVector c u)) =
            (1 / 2) * ∑ p ∈ plaquettesIn (supBall o (2 * (boxRadius x : ℝ))), ∑ p' ∈ plaquettesIn (supBall o (2 * (boxRadius x : ℝ))),
              totalKernel (κ v.1) p p' * curlPairing (chartConnection c u) p p' := by
          rw [show chartCurlVector c u = curlVector (supBall o (2 * (boxRadius x : ℝ))) (chartConnection c u) from rfl,
            curlVector_dotProduct]
        have e2 : centeredBoxResponse T β al K k (translateBy (Tb.stepParameters y).side K k v.1 f) u -
            (κ₀ v.1 - ∫ w, boxResponse T β al K k (translateBy (Tb.stepParameters y).side K k v.1 f) w ∂stageLaw T β K k) =
            boxResponse T β al K k (translateBy (Tb.stepParameters y).side K k v.1 f) u - κ₀ v.1 := by
          simp only [centeredBoxResponse]; ring
        rw [e, e2]
        exact a.trans errLe
      approx_right := hM2.response_approx.mono fun u hu hmem v => by
        have a := hu hmem v.1 v.2
        have e : (1 / 2 : ℝ) * (chartCurlVector c u ⬝ᵥ
            (colourKron (supBall o (2 * (boxRadius x : ℝ))) (totalKernel (κ' v.1))).mulVec (chartCurlVector c u)) =
            (1 / 2) * ∑ p ∈ plaquettesIn (supBall o (2 * (boxRadius x : ℝ))), ∑ p' ∈ plaquettesIn (supBall o (2 * (boxRadius x : ℝ))),
              totalKernel (κ' v.1) p p' * curlPairing (chartConnection c u) p p' := by
          rw [show chartCurlVector c u = curlVector (supBall o (2 * (boxRadius x : ℝ))) (chartConnection c u) from rfl,
            curlVector_dotProduct]
        have e2 : centeredBoxResponse T β al K k (translateBy (Tb.stepParameters y).side K k v.1 h) u -
            (κ₀' v.1 - ∫ w, boxResponse T β al K k (translateBy (Tb.stepParameters y).side K k v.1 h) w ∂stageLaw T β K k) =
            boxResponse T β al K k (translateBy (Tb.stepParameters y).side K k v.1 h) u - κ₀' v.1 := by
          simp only [centeredBoxResponse]; ring
        rw [e, e2]
        exact a.trans errLe
      memLp_left := fun v => (hresp f h hpair v.1).1
      memLp_right := fun v => (hresp f h hpair v.1).2 }
  have : Nonempty ↥(shiftSet (averagingRadius x)) :=
    ⟨⟨0, Fintype.mem_piFinset.2 fun i => Finset.mem_Icc.2 ⟨by simp, by simp⟩⟩⟩
  obtain ⟨k1, k2, k3⟩ := hform _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H
  obtain ⟨b1, b2⟩ := hexp x _ _ _ _ _ _ _ _ _ hx₁x sizes
  have trE : ∀ v : Fin 4 → ℤ, (3 / 2) * (x ^ 2)⁻¹ * boxTrace (Tb.stepParameters y).coupling (Tb.stepParameters y).side k o (boxRadius x)
        (totalKernel (κ v)) (totalKernel (κ' v)) =
      (1 / 2) * Matrix.trace (colourKron (supBall o (2 * (boxRadius x : ℝ))) (totalKernel (κ v)) * Cm' *
        colourKron (supBall o (2 * (boxRadius x : ℝ))) (totalKernel (κ' v)) * Cm') := by
    intro v
    rw [hCm', trace_colourKron]
    simp only [boxTrace, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p₁ _ => Finset.sum_congr rfl fun p₂ _ => Finset.sum_congr rfl fun p₃ _ =>
      Finset.sum_congr rfl fun p₄ _ => ?_
    ring
  have hnum : boxCoefficient (Tb.stepParameters y).coupling (Tb.stepParameters y).side k (averagingRadius x) o (boxRadius x) x κ κ' =
      average (fun v : ↥(shiftSet (averagingRadius x)) => (1 / 2) *
        Matrix.trace (colourKron (supBall o (2 * (boxRadius x : ℝ))) (totalKernel (κ v.1)) * Cm' *
          colourKron (supBall o (2 * (boxRadius x : ℝ))) (totalKernel (κ' v.1)) * Cm')) := by
    simp only [boxCoefficient, shiftAverage]
    rw [← average_subtype_eq]
    congr 1
    funext v
    exact trE v.1
  refine ⟨?_, ?_, ?_⟩
  · have e : (fun u => shiftAveragedProduct T β al K k (averagingRadius x)
          (fun v => translateBy (Tb.stepParameters y).side K k v f) (fun v => translateBy (Tb.stepParameters y).side K k v h) u -
        boxCoefficient (Tb.stepParameters y).coupling (Tb.stepParameters y).side k (averagingRadius x) o (boxRadius x) x κ κ') =
        fun u => average (fun v : ↥(shiftSet (averagingRadius x)) =>
            (centeredBoxResponse T β al K k (translateBy (Tb.stepParameters y).side K k v.1 f) u -
              ∫ w, centeredBoxResponse T β al K k (translateBy (Tb.stepParameters y).side K k v.1 f) w ∂stageLaw T β K k) *
            (centeredBoxResponse T β al K k (translateBy (Tb.stepParameters y).side K k v.1 h) u -
              ∫ w, centeredBoxResponse T β al K k (translateBy (Tb.stepParameters y).side K k v.1 h) w ∂stageLaw T β K k)) -
          average (fun v : ↥(shiftSet (averagingRadius x)) => (1 / 2) *
            Matrix.trace (colourKron (supBall o (2 * (boxRadius x : ℝ))) (totalKernel (κ v.1)) * Cm' *
              colourKron (supBall o (2 * (boxRadius x : ℝ))) (totalKernel (κ' v.1)) * Cm')) := by
      funext u
      rw [hnum]
      simp only [shiftAveragedProduct]
      rw [← average_subtype_eq (F := fun v => centeredBoxResponse T β al K k (translateBy (Tb.stepParameters y).side K k v f) u *
        centeredBoxResponse T β al K k (translateBy (Tb.stepParameters y).side K k v h) u)]
      congr 2
      funext v
      rw [hzero _ (hresp f h hpair v.1).1.1, hzero _ (hresp f h hpair v.1).2.1, sub_zero, sub_zero]
    rw [e]
    exact k1.trans (ENNReal.ofReal_le_ofReal b1)
  · have e : shiftAveragedResponse T β al K k (averagingRadius x) (fun v => translateBy (Tb.stepParameters y).side K k v f) =
        fun u => average (fun v : ↥(shiftSet (averagingRadius x)) =>
          centeredBoxResponse T β al K k (translateBy (Tb.stepParameters y).side K k v.1 f) u -
          ∫ w, centeredBoxResponse T β al K k (translateBy (Tb.stepParameters y).side K k v.1 f) w ∂stageLaw T β K k) := by
      funext u
      simp only [shiftAveragedResponse]
      rw [← average_subtype_eq (F := fun v => centeredBoxResponse T β al K k (translateBy (Tb.stepParameters y).side K k v f) u)]
      congr 1
      funext v
      rw [hzero _ (hresp f h hpair v.1).1.1, sub_zero]
    rw [e]
    exact k2.trans (ENNReal.ofReal_le_ofReal b2)
  · have e : shiftAveragedResponse T β al K k (averagingRadius x) (fun v => translateBy (Tb.stepParameters y).side K k v h) =
        fun u => average (fun v : ↥(shiftSet (averagingRadius x)) =>
          centeredBoxResponse T β al K k (translateBy (Tb.stepParameters y).side K k v.1 h) u -
          ∫ w, centeredBoxResponse T β al K k (translateBy (Tb.stepParameters y).side K k v.1 h) w ∂stageLaw T β K k) := by
      funext u
      simp only [shiftAveragedResponse]
      rw [← average_subtype_eq (F := fun v => centeredBoxResponse T β al K k (translateBy (Tb.stepParameters y).side K k v h) u)]
      congr 1
      funext v
      rw [hzero _ (hresp f h hpair v.1).2.1, sub_zero]
    rw [e]
    exact k3.trans (ENNReal.ofReal_le_ofReal b2)
end YangMills.Construction.StateLaws
end
