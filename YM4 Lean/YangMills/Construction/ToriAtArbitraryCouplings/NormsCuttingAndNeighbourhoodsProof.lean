import YangMills.Construction.PassageToTheLimit.PartitionOfUnityOfClassC1WithSmallPiecesProof
import YangMills.Construction.ToriAtArbitraryCouplings.NormsCuttingAndNeighbourhoods
import YangMills.Construction.TorusOrFourSpace.ClassC1FunctionsProductsAndNeighbourhoods
import YangMills.Construction.TorusOrFourSpace.ClassesAreVectorSpacesWithTheSharpNorm
import YangMills.Construction.TorusOrFourSpace.QuotientMapCompactSetsAndFunctionsOfClassC1
import YangMills.Construction.TorusOrFourSpace.SpaceAndItsFunctionsAreWellDefined
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ToriAtArbitraryCouplings.LipschitzEstimates
open YangMills.Construction.TestFunctions (IsBoundedFun IsLipschitzFor uniformNorm bestLipschitzConstant)
open YangMills.Construction.MetricNotions (IsCompactWrt IsOpenWrt closureWrt)
section Abstract
variable {X : Type} {d : X → X → ℝ} {V : Type} [NormedAddCommGroup V]
private theorem norm_sub_le_bestLip (hd : ∀ x y, 0 ≤ d x y) {f : X → V} (hf : IsLipschitzFor d f)
    (x y : X) : ‖f x - f y‖ ≤ bestLipschitzConstant d f * d x y := by
  have hne : {C : ℝ | 0 ≤ C ∧ ∀ x y, ‖f x - f y‖ ≤ C * d x y}.Nonempty := hf
  rcases (hd x y).eq_or_lt with hzero | hpos
  · obtain ⟨C, -, hC⟩ := hf
    have hxy := hC x y
    rw [← hzero, mul_zero] at hxy ⊢
    exact hxy
  · rw [← div_le_iff₀ hpos]
    exact le_csInf hne fun C hC => (div_le_iff₀ hpos).2 (hC.2 x y)
private theorem bestLip_nonneg (f : X → V) : 0 ≤ bestLipschitzConstant d f :=
  Real.sInf_nonneg fun _ hC => hC.1
private theorem bestLip_le {f : X → V} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x y, ‖f x - f y‖ ≤ C * d x y) : bestLipschitzConstant d f ≤ C :=
  csInf_le ⟨0, fun _ hc => hc.1⟩ ⟨hC0, hC⟩
private theorem norm_le_uniformNorm {f : X → V} (hf : IsBoundedFun f) (x : X) :
    ‖f x‖ ≤ uniformNorm f := by
  obtain ⟨C, hC⟩ := hf
  exact le_ciSup (f := fun x => ‖f x‖) ⟨C, by rintro _ ⟨y, rfl⟩; exact hC y⟩ x
private theorem uniformNorm_nonneg (f : X → V) : 0 ≤ uniformNorm f :=
  Real.iSup_nonneg fun _ => norm_nonneg _
private theorem uniformNorm_le [Nonempty X] {f : X → V} {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) :
    uniformNorm f ≤ C :=
  ciSup_le hC
private def maxNorm (d : X → X → ℝ) (c : ℝ) (f : X → V) : ℝ :=
  max (uniformNorm f) (c * bestLipschitzConstant d f)
private theorem maxNorm_nonneg (c : ℝ) (f : X → V) : 0 ≤ maxNorm d c f :=
  (uniformNorm_nonneg f).trans (le_max_left _ _)
private theorem maxNorm_add [Nonempty X] (hd : ∀ x y, 0 ≤ d x y) {c : ℝ} (hc : 0 ≤ c)
    {f g : X → ℝ} (hfb : IsBoundedFun f) (hgb : IsBoundedFun g) (hf : IsLipschitzFor d f)
    (hg : IsLipschitzFor d g) : maxNorm d c (f + g) ≤ maxNorm d c f + maxNorm d c g := by
  have hs1 : uniformNorm f ≤ maxNorm d c f := le_max_left _ _
  have hs2 : uniformNorm g ≤ maxNorm d c g := le_max_left _ _
  have hl1 : c * bestLipschitzConstant d f ≤ maxNorm d c f := le_max_right _ _
  have hl2 : c * bestLipschitzConstant d g ≤ maxNorm d c g := le_max_right _ _
  refine max_le (uniformNorm_le fun x => ?_) ?_
  · have h1 := norm_le_uniformNorm hfb x
    have h2 := norm_le_uniformNorm hgb x
    have h3 : ‖(f + g) x‖ ≤ ‖f x‖ + ‖g x‖ := norm_add_le _ _
    linarith
  · have hlip : bestLipschitzConstant d (f + g) ≤
        bestLipschitzConstant d f + bestLipschitzConstant d g := by
      refine bestLip_le (add_nonneg (bestLip_nonneg _) (bestLip_nonneg _)) fun x y => ?_
      have h1 := norm_sub_le_bestLip hd hf x y
      have h2 := norm_sub_le_bestLip hd hg x y
      have h3 : ‖(f + g) x - (f + g) y‖ ≤ ‖f x - f y‖ + ‖g x - g y‖ := by
        have : (f + g) x - (f + g) y = (f x - f y) + (g x - g y) := by
          simp only [Pi.add_apply]; ring
        rw [this]
        exact norm_add_le _ _
      rw [add_mul]
      linarith
    have := mul_le_mul_of_nonneg_left hlip hc
    rw [mul_add] at this
    linarith
private theorem maxNorm_smul [Nonempty X] (hd : ∀ x y, 0 ≤ d x y) {c : ℝ} (hc : 0 ≤ c)
    {f : X → ℝ} (hfb : IsBoundedFun f) (hf : IsLipschitzFor d f) (r : ℝ) :
    maxNorm d c (r • f) ≤ ‖r‖ * maxNorm d c f := by
  have hr : 0 ≤ ‖r‖ := norm_nonneg r
  have hs1 : uniformNorm f ≤ maxNorm d c f := le_max_left _ _
  have hl1 : c * bestLipschitzConstant d f ≤ maxNorm d c f := le_max_right _ _
  refine max_le (uniformNorm_le fun x => ?_) ?_
  · rw [Pi.smul_apply, norm_smul]
    exact mul_le_mul_of_nonneg_left ((norm_le_uniformNorm hfb x).trans hs1) hr
  · have hlip : bestLipschitzConstant d (r • f) ≤ ‖r‖ * bestLipschitzConstant d f := by
      refine bestLip_le (mul_nonneg hr (bestLip_nonneg _)) fun x y => ?_
      have h1 := norm_sub_le_bestLip hd hf x y
      have : (r • f) x - (r • f) y = r • (f x - f y) := by
        simp only [Pi.smul_apply, smul_sub]
      rw [this, norm_smul, mul_assoc]
      exact mul_le_mul_of_nonneg_left h1 hr
    calc c * bestLipschitzConstant d (r • f) ≤ c * (‖r‖ * bestLipschitzConstant d f) :=
          mul_le_mul_of_nonneg_left hlip hc
      _ = ‖r‖ * (c * bestLipschitzConstant d f) := by ring
      _ ≤ ‖r‖ * maxNorm d c f := mul_le_mul_of_nonneg_left hl1 hr
private theorem maxNorm_zero [Nonempty X] {c : ℝ} (hc : 0 ≤ c) :
    maxNorm d c (0 : X → ℝ) = 0 := by
  refine le_antisymm (max_le (uniformNorm_le fun x => by simp) ?_) (maxNorm_nonneg _ _)
  have hz : bestLipschitzConstant d (0 : X → ℝ) ≤ 0 := bestLip_le le_rfl fun x y => by simp
  exact mul_nonpos_of_nonneg_of_nonpos hc hz
private theorem maxNorm_mul_cutoff {𝕜 : Type} [RCLike 𝕜] [Nonempty X] (hd : ∀ x y, 0 ≤ d x y)
    {c : ℝ} (hc : 0 ≤ c) {χ : X → ℝ} {h : X → 𝕜} (h01 : ∀ x, χ x ∈ Icc (0 : ℝ) 1)
    (hχ : IsLipschitzFor d χ) (hb : IsBoundedFun h) (hl : IsLipschitzFor d h) :
    IsLipschitzFor d (fun x => ((χ x : ℝ) : 𝕜) * h x) ∧
      maxNorm d c (fun x => ((χ x : ℝ) : 𝕜) * h x) ≤
        (1 + c * bestLipschitzConstant d χ) * maxNorm d c h := by
  have hsup : 0 ≤ uniformNorm h := uniformNorm_nonneg h
  have hLχ : 0 ≤ bestLipschitzConstant d χ := bestLip_nonneg χ
  have hLh : 0 ≤ bestLipschitzConstant d h := bestLip_nonneg h
  have hχ1 : ∀ x, ‖((χ x : ℝ) : 𝕜)‖ ≤ 1 := fun x => by
    rw [RCLike.norm_ofReal, abs_of_nonneg (h01 x).1]
    exact (h01 x).2
  have key : ∀ x y, ‖((χ x : ℝ) : 𝕜) * h x - ((χ y : ℝ) : 𝕜) * h y‖ ≤
      (bestLipschitzConstant d h + uniformNorm h * bestLipschitzConstant d χ) * d x y :=
    fun x y => by
    have e : ((χ x : ℝ) : 𝕜) * h x - ((χ y : ℝ) : 𝕜) * h y =
        ((χ x : ℝ) : 𝕜) * (h x - h y) + ((χ x - χ y : ℝ) : 𝕜) * h y := by
      push_cast
      ring
    have h1 : ‖((χ x : ℝ) : 𝕜) * (h x - h y)‖ ≤ bestLipschitzConstant d h * d x y := by
      rw [norm_mul]
      calc ‖((χ x : ℝ) : 𝕜)‖ * ‖h x - h y‖ ≤ 1 * ‖h x - h y‖ :=
            mul_le_mul_of_nonneg_right (hχ1 x) (norm_nonneg _)
        _ = ‖h x - h y‖ := one_mul _
        _ ≤ _ := norm_sub_le_bestLip hd hl x y
    have h2 : ‖((χ x - χ y : ℝ) : 𝕜) * h y‖ ≤
        uniformNorm h * bestLipschitzConstant d χ * d x y := by
      rw [norm_mul, RCLike.norm_ofReal, mul_comm, mul_assoc]
      have h3 : |χ x - χ y| ≤ bestLipschitzConstant d χ * d x y := by
        simpa [Real.norm_eq_abs] using norm_sub_le_bestLip hd hχ x y
      exact mul_le_mul (norm_le_uniformNorm hb y) h3 (abs_nonneg _) hsup
    rw [e, add_mul]
    exact (norm_add_le _ _).trans (add_le_add h1 h2)
  have hs1 : uniformNorm h ≤ maxNorm d c h := le_max_left _ _
  have hl1 : c * bestLipschitzConstant d h ≤ maxNorm d c h := le_max_right _ _
  have hcL : 0 ≤ c * bestLipschitzConstant d χ := mul_nonneg hc hLχ
  refine ⟨⟨_, add_nonneg hLh (mul_nonneg hsup hLχ), key⟩,
    max_le (uniformNorm_le fun x => ?_) ?_⟩
  · rw [norm_mul]
    calc ‖((χ x : ℝ) : 𝕜)‖ * ‖h x‖ ≤ 1 * ‖h x‖ :=
          mul_le_mul_of_nonneg_right (hχ1 x) (norm_nonneg _)
      _ = ‖h x‖ := one_mul _
      _ ≤ uniformNorm h := norm_le_uniformNorm hb x
      _ ≤ maxNorm d c h := hs1
      _ ≤ (1 + c * bestLipschitzConstant d χ) * maxNorm d c h := by nlinarith
  · have hlip : bestLipschitzConstant d (fun x => ((χ x : ℝ) : 𝕜) * h x) ≤
        bestLipschitzConstant d h + uniformNorm h * bestLipschitzConstant d χ :=
      bestLip_le (add_nonneg hLh (mul_nonneg hsup hLχ)) key
    have h5 := mul_le_mul_of_nonneg_left hlip hc
    have h6 : c * (uniformNorm h * bestLipschitzConstant d χ) ≤
        c * bestLipschitzConstant d χ * maxNorm d c h := by
      rw [mul_comm (uniformNorm h), ← mul_assoc]
      exact mul_le_mul_of_nonneg_left hs1 hcL
    nlinarith
private theorem closureWrt_mono {Z Z' : Set X} (hZ : Z ⊆ Z') :
    closureWrt d Z ⊆ closureWrt d Z' := fun _ hx r hr =>
  let ⟨y, hy, hxy⟩ := hx r hr
  ⟨y, hZ hy, hxy⟩
end Abstract
private theorem abs_le_euclidNormVec (v : Fin 4 → ℝ) (μ : Fin 4) :
    |v μ| ≤ TorusMetric.euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
private theorem euclidNormVec_le_two_mul {v : Fin 4 → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hv : ∀ μ, |v μ| ≤ C) : TorusMetric.euclidNormVec v ≤ 2 * C := by apply _root_.YangMills.Construction.LimitSpaces.FinePartitionOfUnity.euclidNormVec_le <;> assumption
section Quotient
open YangMills.Construction.PeriodicSpace.Kind
variable (D : PeriodicSpace.Params) (K : PeriodicSpace.Kind)
  {d : K.Pt D → K.Pt D → ℝ}
private theorem quot_dist_nonneg (hF : PeriodicSpace.Kind.QuotientCompactC1.Claim)
    (hd : quotDist D K = d) (x y : K.Pt D) : 0 ≤ d x y := by
  subst hd
  exact (hF D K).1.1 x y
private theorem quot_c1_facts (hF : PeriodicSpace.Kind.QuotientCompactC1.Claim)
    (hd : quotDist D K = d) {u : K.Pt D → ℝ} (hu : u ∈ c1Set D K)
    (hc : IsCompactWrt d (closureWrt d {y | u y ≠ 0})) :
    IsBoundedFun u ∧ vecSupNormQ D K (gradVec D K u) < ∞ ∧
      ∀ y y', |u y - u y'| ≤ (vecSupNormQ D K (gradVec D K u)).toReal * d y y' := by
  subst hd
  obtain ⟨-, -, hfin, hlip, -⟩ := (hF D K).2.2.2.2 u hu hc
  have h1 : PeriodicSpace.Kind.supNormQ D K u < ∞ := lt_of_le_of_lt (le_max_left _ _) hfin
  have h2 : vecSupNormQ D K (gradVec D K u) < ∞ := lt_of_le_of_lt (le_max_right _ _) hfin
  refine ⟨⟨(PeriodicSpace.Kind.supNormQ D K u).toReal, fun y => ?_⟩, h2, hlip⟩
  rw [Real.norm_eq_abs]
  exact (ENNReal.ofReal_le_iff_le_toReal h1.ne).1
    (le_iSup (fun y => ENNReal.ofReal |u y|) y)
private theorem quot_bounded (hV : PeriodicSpace.VectorClasses.Claim)
    (hd : quotDist D K = d) {h : K.Pt D → ℝ} (hl : IsLipschitzFor d h)
    (hc : IsCompactWrt d (closureWrt d {y | h y ≠ 0})) : IsBoundedFun h := by
  subst hd
  exact (hV D K).2.1.1 h ⟨hl, hc, subset_univ _⟩
private theorem quot_submodule (hV : PeriodicSpace.VectorClasses.Claim)
    (hd : quotDist D K = d) :
    ∃ W : Submodule ℝ (K.Pt D → ℝ), (W : Set (K.Pt D → ℝ)) =
      {h | IsLipschitzFor d h ∧ IsCompactWrt d (closureWrt d {y | h y ≠ 0}) ∧
        closureWrt d {y | h y ≠ 0} ⊆ univ} := by
  subst hd
  exact ((hV D K).1 univ).1
private theorem quot_setDist_pos (hF : PeriodicSpace.Kind.QuotientCompactC1.Claim)
    (hd : quotDist D K = d) {A A' : Set (K.Pt D)} (hA : IsCompactWrt d A)
    (hA' : IsCompactWrt d A') (hdis : Disjoint A A') :
    0 < ⨅ z ∈ A, ⨅ z' ∈ A', ENNReal.ofReal (d z z') := by
  subst hd
  exact (hF D K).2.2.2.1.1 A A' hA hA' hdis
private theorem quot_thickening (hC : PeriodicSpace.C1ProductsAndThickenings.Statement)
    (hd : quotDist D K = d) {P : Set (K.Pt D)} (hP : IsCompactWrt d P) {η : ℝ}
    (hη : 0 < η) :
    IsOpenWrt d {y | (⨅ z ∈ ({y} : Set (K.Pt D)), ⨅ z' ∈ P, ENNReal.ofReal (d z z')) <
        ENNReal.ofReal η} ∧
      IsCompactWrt d {y | (⨅ z ∈ ({y} : Set (K.Pt D)), ⨅ z' ∈ P, ENNReal.ofReal (d z z')) ≤
        ENNReal.ofReal η} := by
  subst hd
  have hP' := (hC D K).2.2.1.2.1 P hP η hη
  exact ⟨hP'.1, hP'.2.1⟩
private theorem quot_thickening_apart (hC : PeriodicSpace.C1ProductsAndThickenings.Statement)
    (hd : quotDist D K = d) {P P' : Set (K.Pt D)} (hP : IsCompactWrt d P)
    (hP' : IsCompactWrt d P') {δ η : ℝ} (hδ : 0 < δ)
    (hle : ENNReal.ofReal δ ≤ ⨅ z ∈ P, ⨅ z' ∈ P', ENNReal.ofReal (d z z')) (hη : 0 < η) :
    ENNReal.ofReal (δ - η - η) ≤
      ⨅ w ∈ {y | (⨅ z ∈ ({y} : Set (K.Pt D)), ⨅ z' ∈ P, ENNReal.ofReal (d z z')) ≤
          ENNReal.ofReal η},
        ⨅ w' ∈ {y | (⨅ z ∈ ({y} : Set (K.Pt D)), ⨅ z' ∈ P', ENNReal.ofReal (d z z')) ≤
          ENNReal.ofReal η}, ENNReal.ofReal (d w w') := by
  subst hd
  exact (hC D K).2.2.1.2.2.1 P P' hP hP' δ hδ hle η η hη hη
end Quotient
private def asParams (s : TorusSide) : PeriodicSpace.Params :=
  ⟨s.L, s.admissible, s.m, 1, le_rfl⟩
private theorem quotDist_torus (s : TorusSide)
    (hW : PeriodicSpace.WellPosedness.WellPosed) :
    PeriodicSpace.Kind.quotDist (asParams s) .torus = s.pointDist .torus := by
  funext y y'
  exact ((hW (asParams s) .torus).2.2.2.2.2.2.2.2.1 y y').1
private theorem quotDist_euclidean (s : TorusSide)
    (hW : PeriodicSpace.WellPosedness.WellPosed) :
    PeriodicSpace.Kind.quotDist (asParams s) .euclidean = s.pointDist .euclidean := by
  funext y y'
  exact (hW (asParams s) .torus).2.2.2.2.2.2.2.1 y y'
private theorem epsilon_eq_of_unique {X : Type} (q : (Fin 4 → ℝ) → X) (F : (Fin 4 → ℝ) → ℝ)
    (P : X → ℝ) (hP : P ∘ q = F) (hu : ∀ g : X → ℝ, g ∘ q = F → g = P) :
    Classical.epsilon (fun v : X → ℝ => v ∘ q = F) = P :=
  hu _ (Classical.epsilon_spec (p := fun v : X → ℝ => v ∘ q = F) ⟨P, hP⟩)
private theorem gradSupNorm_eq_iSup (s : TorusSide) (E : ReflectionPositivity.AxisMirror.Ambient)
    (f : s.Point E → ℝ) :
    s.gradSupNorm E f =
      ⨆ x, ENNReal.ofReal (TorusMetric.euclidNormVec fun μ => s.partialD μ E f x) := by
  refine iSup_congr fun x => ?_
  rw [TorusSide.gradNorm_eq]
  congr 2
  funext μ
  exact s.gradVec_apply E f x μ
private theorem vecSupNorm_torus (s : TorusSide) (f : s.Point .torus → ℝ) :
    PeriodicSpace.Kind.vecSupNormQ (asParams s) .torus
        (PeriodicSpace.Kind.gradVec (asParams s) .torus f) = s.gradSupNorm .torus f := by
  have hμ : ∀ μ, PeriodicSpace.Kind.partialDeriv (asParams s) .torus μ f =
      s.partialD μ .torus f := fun μ =>
    epsilon_eq_of_unique _ _ _ (s.pullback_partialD μ .torus f)
      (fun g hg => s.eq_partialD_of_pullback μ .torus f g hg)
  rw [gradSupNorm_eq_iSup]
  refine iSup_congr fun x => ?_
  exact congrArg (fun v => ENNReal.ofReal (TorusMetric.euclidNormVec v))
    (funext fun μ => congrFun (hμ μ) x)
private theorem vecSupNorm_euclidean (s : TorusSide) (f : s.Point .euclidean → ℝ) :
    PeriodicSpace.Kind.vecSupNormQ (asParams s) .euclidean
        (PeriodicSpace.Kind.gradVec (asParams s) .euclidean f) =
      s.gradSupNorm .euclidean f := by
  have hμ : ∀ μ, PeriodicSpace.Kind.partialDeriv (asParams s) .euclidean μ f =
      s.partialD μ .euclidean f := fun μ =>
    epsilon_eq_of_unique _ _ _ (s.pullback_partialD μ .euclidean f)
      (fun g hg => s.eq_partialD_of_pullback μ .euclidean f g hg)
  rw [gradSupNorm_eq_iSup]
  refine iSup_congr fun x => ?_
  exact congrArg (fun v => ENNReal.ofReal (TorusMetric.euclidNormVec v))
    (funext fun μ => congrFun (hμ μ) x)
section OnAmbient
variable (hW : PeriodicSpace.WellPosedness.WellPosed)
  (hF : PeriodicSpace.Kind.QuotientCompactC1.Claim)
  (hC : PeriodicSpace.C1ProductsAndThickenings.Statement)
  (hV : PeriodicSpace.VectorClasses.Claim)
  (s : TorusSide) (m' : ℕ) (E : ReflectionPositivity.AxisMirror.Ambient)
include hW hF in
private theorem pointDist_nonneg (x y : s.Point E) : 0 ≤ s.pointDist E x y := by
  cases E
  · exact quot_dist_nonneg (asParams s) .torus hF (quotDist_torus s hW) x y
  · exact quot_dist_nonneg (asParams s) .euclidean hF (quotDist_euclidean s hW) x y
private theorem point_nonempty : Nonempty (s.Point E) := ⟨s.ambientProj E 0⟩
include hW hF in
private theorem c1_facts {f : s.Point E → ℝ} (hf : f ∈ s.c1CompactSet E) :
    IsBoundedFun f ∧ s.gradSupNorm E f < ∞ ∧
      ∀ x y, |f x - f y| ≤ (s.gradSupNorm E f).toReal * s.pointDist E x y := by
  cases E
  · have hq := quot_c1_facts (asParams s) .torus hF (quotDist_torus s hW) (u := f) hf.1 hf.2
    rw [vecSupNorm_torus] at hq
    exact hq
  · have hq := quot_c1_facts (asParams s) .euclidean hF (quotDist_euclidean s hW) (u := f)
      hf.1 hf.2
    rw [vecSupNorm_euclidean] at hq
    exact hq
private theorem lipConst_eq {𝕜 : Type} [RCLike 𝕜] (f : s.Point E → 𝕜) :
    s.lipConst E f = bestLipschitzConstant (s.pointDist E) f := by
  cases E <;> rfl
private theorem sharpNormAt_eq_maxNorm {𝕜 : Type} [RCLike 𝕜] (f : s.Point E → 𝕜) :
    s.sharpNormAt m' E f = maxNorm (s.pointDist E) (40 * (cubeEdge s.L m' : ℝ)) f := by
  rw [TorusSide.sharpNormAt_eq, lipConst_eq]
  rfl
private theorem one_le_edge : (1 : ℝ) ≤ (cubeEdge s.L m' : ℝ) := by
  exact_mod_cast one_le_cubeEdge s.admissible m'
include hW hF in
private theorem isLipschitz_of_c1 {f : s.Point E → ℝ}
    (hf : f ∈ s.c1CompactSet E) : IsLipschitzFor (s.pointDist E) f := by
  obtain ⟨-, -, hlip⟩ := c1_facts hW hF s E hf
  exact ⟨_, ENNReal.toReal_nonneg, fun x y => by simpa [Real.norm_eq_abs] using hlip x y⟩
include hW hF in
private theorem c1NormComparison_holds : C1NormComparison s m' E := by
  intro f hf
  obtain ⟨hb, hG, hlip⟩ := c1_facts hW hF s E hf
  have hL := isLipschitz_of_c1 hW hF s E hf
  have := point_nonempty s E
  have hGr : 0 ≤ (s.gradSupNorm E f).toReal := ENNReal.toReal_nonneg
  have hlen : ∀ x, s.gradNorm E f x ≤ (s.gradSupNorm E f).toReal := fun x =>
    (ENNReal.ofReal_le_iff_le_toReal hG.ne).1
      (le_iSup (fun x => ENNReal.ofReal (s.gradNorm E f x)) x)
  have hpar : ∀ μ x, |s.partialD μ E f x| ≤ (s.gradSupNorm E f).toReal := by
    intro μ x
    have hx := abs_le_euclidNormVec (s.gradVec E f x) μ
    rw [s.gradVec_apply, ← s.gradNorm_eq] at hx
    exact hx.trans (hlen x)
  have hbp : ∀ μ, IsBoundedFun (s.partialD μ E f) := fun μ =>
    ⟨_, fun x => by simpa [Real.norm_eq_abs] using hpar μ x⟩
  obtain ⟨B, hBdef⟩ : ∃ B, B = ⨆ μ : Fin 4, uniformNorm (s.partialD μ E f) := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := hBdef ▸ Real.iSup_nonneg fun μ => uniformNorm_nonneg _
  have hBG : B ≤ (s.gradSupNorm E f).toReal := by
    rw [hBdef]
    exact ciSup_le fun μ => uniformNorm_le fun x => by simpa [Real.norm_eq_abs] using hpar μ x
  have hparB : ∀ μ x, |s.partialD μ E f x| ≤ B := by
    intro μ x
    rw [hBdef]
    exact (norm_le_uniformNorm (hbp μ) x).trans
      (le_ciSup (f := fun μ => uniformNorm (s.partialD μ E f))
        (Set.finite_range _).bddAbove μ)
  have hlen2 : ∀ x, s.gradNorm E f x ≤ 2 * B := by
    intro x
    rw [s.gradNorm_eq]
    refine euclidNormVec_le_two_mul hB0 fun μ => ?_
    rw [s.gradVec_apply]
    exact hparB μ x
  have hG2 : s.gradSupNorm E f ≤ ENNReal.ofReal (2 * B) :=
    iSup_le fun x => ENNReal.ofReal_le_ofReal (hlen2 x)
  have hGr2 : (s.gradSupNorm E f).toReal ≤ 2 * B :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hG2
  have hlipn : s.lipConst E f ≤ (s.gradSupNorm E f).toReal := by
    rw [lipConst_eq]
    exact bestLip_le hGr fun x y => by simpa [Real.norm_eq_abs] using hlip x y
  have hc1 : s.c1NormOn E f = max (uniformNorm f) B := by
    rw [hBdef]
    exact s.c1NormOn_eq_max E f
  have hgn : s.c1GradNorm E f = max (uniformNorm f) (s.gradSupNorm E f).toReal := rfl
  have hsup0 : 0 ≤ uniformNorm f := uniformNorm_nonneg f
  have hM := one_le_edge s m'
  have hc1le : s.c1NormOn E f ≤ s.c1GradNorm E f := by
    rw [hc1, hgn]
    exact max_le_max le_rfl hBG
  have hgnle : s.c1GradNorm E f ≤ 2 * s.c1NormOn E f := by
    rw [hc1, hgn]
    refine max_le ?_ ?_
    · have := le_max_left (uniformNorm f) B
      linarith
    · have := le_max_right (uniformNorm f) B
      linarith
  have h40 : (0 : ℝ) ≤ 40 * (cubeEdge s.L m' : ℝ) := by linarith
  refine ⟨hb, hL, (ENNReal.ofReal_le_iff_le_toReal hG.ne).2 hlipn, ?_, hc1le, hgnle, ?_, ?_⟩
  · refine hG2.trans (le_of_eq ?_)
    rw [← hBdef, ENNReal.ofReal_mul (by norm_num)]
    simp
  · rw [TorusSide.sharpNormAt_eq]
    refine max_le ?_ ?_
    · have h1 : uniformNorm f ≤ s.c1GradNorm E f := le_max_left _ _
      nlinarith
    · exact mul_le_mul_of_nonneg_left (hlipn.trans (le_max_right _ _)) h40
  · have := mul_le_mul_of_nonneg_left hgnle h40
    linarith
include hW hF in
private theorem c1ClassesLipschitz_holds : C1ClassesLipschitz s E := by
  refine ⟨fun A f hf => ?_, fun n X hX => ?_⟩
  · exact ⟨isLipschitz_of_c1 hW hF s E ⟨hf.1, hf.2.1⟩, hf.2.1, hf.2.2⟩
  · obtain ⟨hlen, hmem, hpair⟩ := (s.mem_sepOfLength_iff E n X).1 hX
    exact (s.mem_lipDisjointOfLength_iff E n X).2 ⟨hlen, fun f hf =>
      ⟨isLipschitz_of_c1 hW hF s E ⟨(hmem f hf).1, (hmem f hf).2⟩, (hmem f hf).2⟩, hpair⟩
include hW hV in
private theorem bounded_of_lipSuppIn {f : s.Point E → ℝ}
    (hf : f ∈ s.lipSuppIn E univ) : IsBoundedFun f := by
  cases E
  · exact quot_bounded (asParams s) .torus hV (quotDist_torus s hW) hf.1 hf.2.1
  · exact quot_bounded (asParams s) .euclidean hV (quotDist_euclidean s hW) hf.1 hf.2.1
include hW hV in
private theorem submodule_of_lipSuppIn :
    ∃ W : Submodule ℝ (s.Point E → ℝ),
      (W : Set (s.Point E → ℝ)) = s.lipSuppIn E univ := by
  cases E
  · exact quot_submodule (asParams s) .torus hV (quotDist_torus s hW)
  · exact quot_submodule (asParams s) .euclidean hV (quotDist_euclidean s hW)
include hW hF hV in
private theorem sharpNormSeminorm_holds : SharpNormSeminorm s m' E := by
  have hbd : ∀ f ∈ s.lipSuppIn E univ,
      IsBoundedFun f ∧ IsLipschitzFor (s.pointDist E) f := fun f hf =>
    ⟨bounded_of_lipSuppIn hW hV s E hf, hf.1⟩
  obtain ⟨W, hWs⟩ := submodule_of_lipSuppIn hW hV s E
  have hmem : ∀ f : W, (f : s.Point E → ℝ) ∈ s.lipSuppIn E univ := fun f =>
    hWs ▸ f.2
  have hdn := pointDist_nonneg hW hF s E
  have hc : (0 : ℝ) ≤ 40 * (cubeEdge s.L m' : ℝ) := by
    have := one_le_edge s m'
    linarith
  have := point_nonempty s E
  refine ⟨hbd, W, Seminorm.ofSMulLE (fun f : W => s.sharpNormAt m' E (f : s.Point E → ℝ))
    ?_ ?_ ?_, hWs, fun f => rfl⟩
  · simp only [sharpNormAt_eq_maxNorm, Submodule.coe_zero]
    exact maxNorm_zero hc
  · intro f g
    simp only [sharpNormAt_eq_maxNorm, Submodule.coe_add]
    exact maxNorm_add hdn hc (hbd _ (hmem f)).1 (hbd _ (hmem g)).1 (hbd _ (hmem f)).2
      (hbd _ (hmem g)).2
  · intro r f
    simp only [sharpNormAt_eq_maxNorm, Submodule.coe_smul]
    exact maxNorm_smul hdn hc (hbd _ (hmem f)).1 (hbd _ (hmem f)).2 r
include hW hF in
private theorem lipschitzCutoffBound_holds : LipschitzCutoffBound s m' E := by
  intro 𝕜 _ χ h h01 hχ hb hl
  have hc : (0 : ℝ) ≤ 40 * (cubeEdge s.L m' : ℝ) := by
    have := one_le_edge s m'
    linarith
  have := point_nonempty s E
  obtain ⟨h1, h2⟩ := maxNorm_mul_cutoff (pointDist_nonneg hW hF s E) hc h01 hχ hb hl
  refine ⟨h1, ?_, ?_⟩
  · rw [sharpNormAt_eq_maxNorm, sharpNormAt_eq_maxNorm, lipConst_eq]
    exact h2
  · refine subset_inter (closureWrt_mono ?_) (closureWrt_mono ?_)
    · intro x hx
      show χ x ≠ 0
      intro h0
      exact hx (show ((χ x : ℝ) : 𝕜) * h x = 0 by rw [h0]; simp)
    · intro x hx
      show h x ≠ 0
      intro h0
      exact hx (show ((χ x : ℝ) : 𝕜) * h x = 0 by rw [h0]; simp)
private theorem setDist_eq_iInf (A B : Set (s.Point E)) :
    s.setDist E A B = ⨅ z ∈ A, ⨅ z' ∈ B, ENNReal.ofReal (s.pointDist E z z') := by
  cases E <;> rfl
include hW hF in
private theorem positivelySeparated_of_disjoint {A A' : Set (s.Point E)}
    (hA : s.IsCompactWrt E A) (hA' : s.IsCompactWrt E A') (hdis : Disjoint A A') :
    s.PositivelySeparated E A A' := by
  unfold TorusSide.PositivelySeparated
  rw [setDist_eq_iInf]
  cases E
  · exact quot_setDist_pos (asParams s) .torus hF (quotDist_torus s hW) hA hA' hdis
  · exact quot_setDist_pos (asParams s) .euclidean hF (quotDist_euclidean s hW) hA hA' hdis
abbrev _root_.YangMills.DeltaSharedProofs.p502113 := @positivelySeparated_of_disjoint
private theorem iInf_fin_pos {n : ℕ} {f : Fin n → ℝ≥0∞} (hf : ∀ i, 0 < f i) :
    0 < ⨅ i, f i := by
  rcases isEmpty_or_nonempty (Fin n) with he | he
  · exact lt_of_lt_of_le ENNReal.zero_lt_top (le_iInf fun i => (he.false i).elim)
  · obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := f)
    rw [← hi]
    exact hf i
abbrev _root_.YangMills.SharedProofs.p63321 := @iInf_fin_pos
include hW hF in
private theorem compactSetsSeparated_holds : CompactSetsSeparated s E := by
  refine ⟨fun A A' hA hA' h => positivelySeparated_of_disjoint hW hF s E hA hA' h,
    fun n X hX => ?_⟩
  rw [TorusSide.gapAllLengths_eq_supportGap]
  obtain ⟨-, hmem, hpair⟩ := (s.mem_lipDisjointOfLength_iff E n X).1 hX
  have hij : ∀ i k : Fin X.length, i ≠ k →
      Disjoint (s.closedSupport E (X.get i)) (s.closedSupport E (X.get k)) := by
    intro i k hik
    have hp := List.pairwise_iff_get.1 hpair
    rcases lt_or_gt_of_ne hik with h | h
    · exact hp i k h
    · exact (hp k i h).symm
  unfold TorusSide.supportGap
  refine iInf_fin_pos fun i => iInf_fin_pos fun k => ?_
  by_cases hik : i = k
  · simp [hik]
  · have h := positivelySeparated_of_disjoint hW hF s E (hmem _ (List.get_mem X i)).2
      (hmem _ (List.get_mem X k)).2 (hij i k hik)
    unfold TorusSide.PositivelySeparated at h
    simpa [hik] using h
include hW hC in
private theorem compactThickenings_holds : CompactThickenings s E := by
  intro P η hP hη
  cases E
  · exact quot_thickening (asParams s) .torus hC (quotDist_torus s hW) hP hη
  · exact quot_thickening (asParams s) .euclidean hC (quotDist_euclidean s hW) hP hη
include hW hC in
private theorem thickeningSeparation_holds : ThickeningSeparation s E := by
  intro P P' δ η hP hP' hδ hle hη _
  have e : δ - 2 * η = δ - η - η := by ring
  rw [e]
  refine le_of_le_of_eq ?_ (setDist_eq_iInf s E _ _).symm
  rw [setDist_eq_iInf] at hle
  cases E
  · exact quot_thickening_apart (asParams s) .torus hC (quotDist_torus s hW) hP hP' hδ hle hη
  · exact quot_thickening_apart (asParams s) .euclidean hC (quotDist_euclidean s hW) hP hP'
      hδ hle hη
end OnAmbient
theorem combined_holds (hW : PeriodicSpace.WellPosedness.WellPosed)
    (hF : PeriodicSpace.Kind.QuotientCompactC1.Claim)
    (hC : PeriodicSpace.C1ProductsAndThickenings.Statement)
    (hV : PeriodicSpace.VectorClasses.Claim) : Combined := by
  intro s _ m' E
  exact ⟨⟨c1NormComparison_holds hW hF s m' E, c1ClassesLipschitz_holds hW hF s E,
    sharpNormSeminorm_holds hW hF hV s m' E⟩, lipschitzCutoffBound_holds hW hF s m' E,
    compactSetsSeparated_holds hW hF s E, compactThickenings_holds hW hC s E,
    thickeningSeparation_holds hW hC s E⟩
end YangMills.Construction.ToriAtArbitraryCouplings.LipschitzEstimates
end
