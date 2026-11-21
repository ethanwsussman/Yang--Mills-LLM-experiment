import YangMills.Construction.ColdChainAtEveryLevel.CellContexts
import YangMills.Construction.ColdChainAtEveryLevel.ComplexChainIsAnalytic
import YangMills.Construction.ColdChainAtEveryLevel.LocalFirstVariation
import YangMills.Construction.ColdChainAtEveryLevel.SmallCoordinatesAreRegular
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator Topology
open Metric
namespace YangMills.Construction.CellFirstVariation
open BlockAverages ComplexifiedQuaternions ComplexDifferences CellSpans ComplexCells ComplexContours ComplexChainStep
  ComplexRemainders ComplexLevels CellNormBounds ComplexPlaquettes ComplexAnalyticity ComplexBondTerms LevelRecursion
  CellContexts PlaquettesNearCell CellSources
variable {F : BlockFrame} {j : ℕ}
def cellTerms (a : ℝ) (S : Finset F.Cell) (R : F.FieldChain) (W : ComplexChainChart F) (T : F.ComplexField F.top)
    (z : F.Cell) : ℂ :=
  ∑ p ∈ plaquettesOver S {z} 0, complexPlaquetteTerm (complexChartField R W 0) p +
    (a : ℂ) * ∑ j ∈ Finset.range F.top, ∑ c ∈ bondsOver S {z} (j + 1), complexBondTermOverTop R W T j c
section Sums
private theorem sum_innerPlaquettes_eq_sum_plaquettesOver (hodd : Odd F.blockSide) (S : Finset F.Cell)
    (f : F.Site 0 × Fin 4 × Fin 4 → ℂ) :
    ∑ p ∈ innerPlaquettes S 0, f p = ∑ z ∈ S, ∑ p ∈ plaquettesOver S {z} 0, f p := by
  classical
  have hmaps : ∀ p ∈ innerPlaquettes S 0, enclosingCell p.1 ∈ S := fun p hp =>
    BlockLines.enclosingCell_mem hodd (Finset.mem_product.1 (Finset.mem_filter.1 hp).1).1
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr ?_ fun _ _ => rfl
  ext p
  simp [plaquettesOver, Finset.mem_filter]
abbrev _root_.YangMills.SharedProofs.p67426 := @sum_innerPlaquettes_eq_sum_plaquettesOver
private theorem sum_innerBonds_eq_sum_bondsOver (hodd : Odd F.blockSide) (S : Finset F.Cell) (k : ℕ)
    (f : F.Site k × Fin 4 → ℂ) :
    ∑ c ∈ innerBonds S k, f c = ∑ z ∈ S, ∑ c ∈ bondsOver S {z} k, f c := by
  classical
  have hmaps : ∀ c ∈ innerBonds S k, enclosingCell c.1 ∈ S := fun c hc =>
    BlockLines.enclosingCell_mem hodd (Finset.mem_product.1 (Finset.mem_filter.1 hc).1).1
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr ?_ fun _ _ => rfl
  ext c
  simp [bondsOver, Finset.mem_filter]
abbrev _root_.YangMills.SharedProofs.p65855 := @sum_innerBonds_eq_sum_bondsOver
theorem complexTotalOverTop_eq_sum_cellTerms (hodd : Odd F.blockSide) (a : ℝ) (S : Finset F.Cell) (R : F.FieldChain)
    (T : F.ComplexField F.top) (W : ComplexChainChart F) :
    complexTotalOverTop a S R W T = ∑ z ∈ S, cellTerms a S R W T z := by
  have e2 : ∀ j, ∑ c ∈ innerBonds S (j + 1), complexBondTermOverTop R W T j c =
      ∑ z ∈ S, ∑ c ∈ bondsOver S {z} (j + 1), complexBondTermOverTop R W T j c := fun j =>
    sum_innerBonds_eq_sum_bondsOver hodd S (j + 1) (complexBondTermOverTop R W T j)
  simp only [complexTotalOverTop, cellTerms,
    sum_innerPlaquettes_eq_sum_plaquettesOver hodd S (complexPlaquetteTerm (complexChartField R W 0)), e2,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [Finset.sum_comm (s := Finset.range F.top) (t := S)]
end Sums
section Over
theorem complexChainOverTop_of_ne (R : F.FieldChain) (W : ComplexChainChart F) (T : F.ComplexField F.top) {k : ℕ}
    (h : k ≠ F.top) : complexChainOverTop R W T k = complexChartField R W k := by
  simp [complexChainOverTop, Function.update_of_ne h]
theorem complexChainOverTop_top (R : F.FieldChain) (W : ComplexChainChart F) (T : F.ComplexField F.top) :
    complexChainOverTop R W T F.top = T := by
  simp [complexChainOverTop]
theorem complexBondTermOverTop_eq (R : F.FieldChain) (W : ComplexChainChart F) (T : F.ComplexField F.top) {j : ℕ}
    (hj : j < F.top) (c : F.Site (j + 1) × Fin 4) :
    complexBondTermOverTop R W T j c = complexBlockFit
      (complexGaugedContourAverage (complexChartField R W j) (complexBalancingGauge (complexChartField R W j) (R j)) c)
      (complexChainOverTop R W T (j + 1) c.1 c.2) := by
  have h1 := complexChainOverTop_of_ne R W T (k := j) (by omega)
  simp only [complexBondTermOverTop, h1, complexBalancingGauges]
theorem complexBondTermOverTop_of_lt (R : F.FieldChain) (W : ComplexChainChart F) (T : F.ComplexField F.top)
    (V : F.GaugeField F.top) {j : ℕ} (hj : j + 1 < F.top) (c : F.Site (j + 1) × Fin 4) :
    complexBondTermOverTop R W T j c = complexBondTerm R W V j c := by
  have h1 := complexChainOverTop_of_ne R W T (k := j) (by omega)
  have h2 := complexChainOverTop_of_ne R W T (k := j + 1) (by omega)
  have h3 := complexFieldChain_of_ne R W V (k := j) (by omega)
  have h4 := complexFieldChain_of_ne R W V (k := j + 1) (by omega)
  simp only [complexBondTermOverTop, complexBondTerm, h1, h2, h3, h4]
theorem complexBondTermOverTop_depth (R : F.FieldChain) (W : ComplexChainChart F) (T : F.ComplexField F.top)
    (c : F.Site (F.depth + 1) × Fin 4) :
    complexBondTermOverTop R W T F.depth c = complexBlockFit
      (complexGaugedContourAverage (complexChartField R W F.depth)
        (complexBalancingGauge (complexChartField R W F.depth) (R F.depth)) c) (T c.1 c.2) := by
  rw [complexBondTermOverTop_eq R W T (Nat.lt_succ_self _) c, complexChainOverTop_top R W T]
end Over
section Operations
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] {z : P}
private theorem analyticAt_principalSqrt_comp {g : P → ℂ} (hg : AnalyticAt ℂ g z) (hs : g z ∈ Complex.slitPlane) :
    AnalyticAt ℂ (fun w => principalSqrt (g w)) z := by
  unfold principalSqrt
  exact (analyticAt_const.mul (hg.clog hs)).cexp
private theorem analyticAt_complexBlockFit_comp {M X : P → ComplexQuat} (hM : AnalyticAt ℂ M z)
    (hs : (M z).det ∈ Complex.slitPlane) (hX : AnalyticAt ℂ X z) :
    AnalyticAt ℂ (fun w => complexBlockFit (M w) (X w)) z := by
  simp only [complexBlockFit]
  exact (analyticAt_principalSqrt_comp (analyticAt_det hM) hs).sub
    (analyticAt_trace (hM.mul (analyticAt_adjugate hX))).div_const
abbrev _root_.YangMills.SharedProofs.p33576 := @analyticAt_complexBlockFit_comp
private theorem analyticAt_complexGaugedContourAverage (hodd : Odd F.blockSide) {X : P → F.ComplexField j}
    (R : F.GaugeField j) (hj : j + 1 ≤ F.top) {c : F.Site (j + 1) × Fin 4} {t σ : ℝ} (ht : 0 ≤ t)
    (hτ : 4 * (F.blockSide : ℝ) * t ≤ 1 / 1024) (hg : ContoursNearReal (X z) R t σ c)
    (hX : HoldsOnHull c (fun b i => AnalyticAt ℂ (fun w => X w b i) z)) :
    AnalyticAt ℂ (fun w => complexGaugedContourAverage (X w) (complexBalancingGauge (X w) R) c) z := by
  have hleg : ∀ h ∈ centredCube F.blockSide, ∀ π,
      AnalyticAt ℂ (fun w => complexPathHolonomy (X w) (refineSite c.1) (axisPath h π)) z :=
    fun h hh π => analyticAt_complexPathHolonomy
      (pathBondsSatisfy_axisPath _ hodd.pos (fun v hv k hk => (hX.1 v hv k hk).1) hh π)
  have hleg' : ∀ h ∈ centredCube F.blockSide, ∀ π, AnalyticAt ℂ
      (fun w => complexPathHolonomy (X w) (refineSite (c.1 + unitStep (j + 1) c.2)) (axisPath h π)) z :=
    fun h hh π => analyticAt_complexPathHolonomy
      (pathBondsSatisfy_axisPath _ hodd.pos (fun v hv k hk => (hX.1 v hv k hk).2) hh π)
  have hline : ∀ h ∈ centredCube F.blockSide, AnalyticAt ℂ
      (fun w => complexPathHolonomy (X w) (refineSite c.1 + siteOfCoords j h)
        (List.replicate F.blockSide (c.2, true))) z :=
    fun h hh => analyticAt_complexPathHolonomy (pathBondsSatisfy_replicate _ _ _ fun r hr => hX.2 h hh r hr)
  have hcm : AnalyticAt ℂ (fun w => complexContourAverage (X w) c) z := by
    simp only [complexContourAverage]
    have hs : AnalyticAt ℂ (fun w => ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
        complexPathHolonomy (X w) (refineSite c.1) (bondContour F.blockSide h π c.2)) z := by
      refine Finset.analyticAt_fun_sum _ fun h hh => Finset.analyticAt_fun_sum _ fun π _ => ?_
      simp only [complexPathHolonomy_bondContour hj]
      exact ((hleg h hh π).mul (hline h hh)).mul (analyticAt_adjugate (hleg' h hh π))
    exact analyticAt_const_smul_complexQuat _ hs
  have hτ8 : 4 * (F.blockSide : ℝ) * t ≤ 1 / 8 := by linarith
  have hk := analyticAt_complexBalancingGauge hodd R ht hτ8 hleg hg.nearLegs
  have hk' := analyticAt_complexBalancingGauge hodd R ht hτ8 hleg' hg.nearFarLegs
  simp only [complexGaugedContourAverage]
  exact (hk.mul hcm).mul (analyticAt_adjugate hk')
abbrev _root_.YangMills.SharedProofs.p21606 := @analyticAt_complexGaugedContourAverage
end Operations
private theorem contoursNearReal_of_deviation (hodd : Odd F.blockSide) {X : F.ComplexField j} {R : F.GaugeField j}
    {D : Finset F.Cell} {t σ : ℝ} (hj : j < F.top)
    (hgap : ∀ b ∈ innerBonds D j, ‖linkDeviation X R b.1 b.2‖ ≤ t)
    (hdet : ∀ b ∈ innerBonds D j, ‖linkDeviation X R b.1 b.2‖ ≤ t → (X b.1 b.2).det = 1)
    {c : F.Site (j + 1) × Fin 4} (hc : c ∈ innerBonds D (j + 1))
    (href : ∀ h ∈ centredCube F.blockSide, ∀ π,
      ‖ofUnit (pathHolonomy R (refineSite c.1) (bondContour F.blockSide h π c.2) *
        (polarUnit (_root_.YangMills.Construction.BlockAverages.contourAverage R c))⁻¹) - 1‖ ≤ σ) : ContoursNearReal X R t σ c := by
  have hgood : ∀ b ∈ innerBonds D j, BondNearReal X R t b.1 b.2 := fun b hb => ⟨hgap b hb, hdet b hb (hgap b hb)⟩
  have hhull : HoldsOnHull c (fun b i => BondNearReal X R t b i) := holdsOnHull_of_innerBonds hj hodd hc hgood
  exact ⟨fun h hh π => pathNearReal_axisPath _ hodd.pos (fun v hv k hk => (hhull.1 v hv k hk).1) hh π,
    fun h hh => pathNearReal_replicate _ _ _ fun r hr => hhull.2 h hh r hr,
    fun h hh π => pathNearReal_axisPath _ hodd.pos (fun v hv k hk => (hhull.1 v hv k hk).2) hh π, href⟩
theorem complexGaugedContourAverage_det_good (hodd : Odd F.blockSide) {R : F.FieldChain} {W : ComplexChainChart F}
    {D : Finset F.Cell} {t σ : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) (hσ : σ ≤ 1 / 64)
    (hτ : 4 * (F.blockSide : ℝ) * t ≤ 1 / 1024) (hj : j < F.top)
    (hgap : ∀ b ∈ innerBonds D j, ‖levelDeviation R W j b.1 b.2‖ ≤ t) {c : F.Site (j + 1) × Fin 4}
    (hc : c ∈ innerBonds D (j + 1))
    (href : ∀ h ∈ centredCube F.blockSide, ∀ π,
      ‖ofUnit (pathHolonomy (R j) (refineSite c.1) (bondContour F.blockSide h π c.2) *
        (polarUnit (contourAverage (R j) c))⁻¹) - 1‖ ≤ σ) :
    0 < (complexGaugedContourAverage (complexChartField R W j)
        (complexBalancingGauge (complexChartField R W j) (R j)) c).det.re ∧
      ‖principalSqrt (complexGaugedContourAverage (complexChartField R W j)
        (complexBalancingGauge (complexChartField R W j) (R j)) c).det‖ ≤ 2 := by
  have hg : ContoursNearReal (complexChartField R W j) (R j) t σ c :=
    contoursNearReal_of_deviation hodd hj hgap
      (fun b _ h => det_complexChartField_of_norm_lt_one R W j _ _ (lt_of_le_of_lt h ht1)) hc href
  obtain ⟨h1, -, h3⟩ := unitPart_and_sqrt_near hodd (by omega) ht hσ hτ hg
  refine ⟨h1, ?_⟩
  have hm := BlockAverages.VariationRates.norm_contourAverage_le_one hodd (R j) c
  set τ := 4 * (F.blockSide : ℝ) * t with hτd
  have hτ0 : 0 ≤ τ := by positivity
  have h4 : 1700 * τ ^ 2 + 72 * σ * τ ≤ 1 := by
    have e1 : τ ^ 2 ≤ (1 / 1024) ^ 2 := pow_le_pow_left₀ hτ0 hτ 2
    have e2 : σ * τ ≤ 1 / 64 * τ := mul_le_mul_of_nonneg_right hσ hτ0
    nlinarith
  have h5 := norm_sub_norm_le (principalSqrt (complexGaugedContourAverage (complexChartField R W j)
      (complexBalancingGauge (complexChartField R W j) (R j)) c).det)
    (((‖_root_.YangMills.Construction.BlockAverages.contourAverage (R j) c‖ : ℝ) : ℂ))
  rw [Complex.norm_real, norm_norm] at h5
  linarith
theorem analyticAt_cellTerms (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (a : ℝ) {S : Finset F.Cell}
    {z : F.Cell} {R : F.FieldChain} (T : F.ComplexField F.top) {W : ℂ → ComplexChainChart F} {t₀ : ℂ} {t σ : ℝ}
    (ht : 0 ≤ t) (ht1 : t < 1) (hσ : σ ≤ 1 / 64) (hτ : 4 * (F.blockSide : ℝ) * t ≤ 1 / 1024)
    (hu : ∀ b ∈ innerBonds (cellBall S z 1) 0,
      AnalyticAt ℂ (fun w => complexifiedImaginary ((W w).re.fine b.1 b.2) ((W w).im.fine b.1 b.2)) t₀)
    (hu1 : ∀ b ∈ innerBonds (cellBall S z 1) 0,
      ‖complexifiedImaginary ((W t₀).re.fine b.1 b.2) ((W t₀).im.fine b.1 b.2)‖ ≤ 1 / 16)
    (hmu : ∀ j, j + 1 < F.top → ∀ b ∈ innerBonds (cellBall S z 1) (j + 1),
      AnalyticAt ℂ (fun w => complexifiedImaginary ((W w).re.coarse j b.1 b.2) ((W w).im.coarse j b.1 b.2)) t₀)
    (hmu1 : ∀ j, j + 1 < F.top → ∀ b ∈ innerBonds (cellBall S z 1) (j + 1),
      ‖complexifiedImaginary ((W t₀).re.coarse j b.1 b.2) ((W t₀).im.coarse j b.1 b.2)‖ ≤ 1 / 16)
    (hgap : ∀ j, j < F.top → ∀ b ∈ innerBonds (cellBall S z 1) j, ‖levelDeviation R (W t₀) j b.1 b.2‖ ≤ t)
    (href : ∀ j, j + 1 ≤ F.top → ∀ c ∈ innerBonds (cellBall S z 1) (j + 1), ∀ h ∈ centredCube F.blockSide, ∀ π,
      ‖ofUnit (pathHolonomy (R j) (refineSite c.1) (bondContour F.blockSide h π c.2) *
        (polarUnit (contourAverage (R j) c))⁻¹) - 1‖ ≤ σ) :
    AnalyticAt ℂ (fun w => cellTerms a S R (W w) T z) t₀ := by
  have hF := analyticAt_complexChartField hodd R ht ht1 hσ hτ hu hu1 hmu hmu1 hgap href
  have hF0 : ∀ b ∈ innerBonds (cellBall S z 1) 0, AnalyticAt ℂ (fun w => complexChartField R (W w) 0 b.1 b.2) t₀ := by
    intro b hb
    simp only [complexChartField]
    exact (analyticAt_unitExp (hu b hb) (hu1 b hb)).mul analyticAt_const
  have hplaq : ∀ p ∈ plaquettesOver S {z} 0,
      AnalyticAt ℂ (fun w => complexPlaquetteTerm (complexChartField R (W w) 0) p) t₀ := by
    intro p hp
    obtain ⟨b1, b2, b3, b4⟩ := plaquette_bonds_mem_innerBonds hamb hodd hp
    have hpath : PathBondsSatisfy (fun b i => AnalyticAt ℂ (fun w => complexChartField R (W w) 0 b i) t₀) p.1
        [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] := by
      have e3 : p.1 + unitStep 0 p.2.1 + unitStep 0 p.2.2 - unitStep 0 p.2.1 = p.1 + unitStep 0 p.2.2 := by abel
      have e4 : p.1 + unitStep 0 p.2.1 + unitStep 0 p.2.2 + -unitStep 0 p.2.1 - unitStep 0 p.2.2 = p.1 := by abel
      simp only [PathBondsSatisfy, crossedBond, stepDisplacement, if_true, Bool.false_eq_true, if_false, e3, e4,
        and_true]
      exact ⟨hF0 (p.1, p.2.1) b1, hF0 (p.1 + unitStep 0 p.2.1, p.2.2) b2, hF0 (p.1 + unitStep 0 p.2.2, p.2.1) b3,
        hF0 (p.1, p.2.2) b4⟩
    simp only [complexPlaquetteTerm, complexPlaquetteHolonomy]
    exact analyticAt_const.sub (analyticAt_trace (analyticAt_complexPathHolonomy hpath)).div_const
  have hmean : ∀ j, j < F.top → ∀ c ∈ innerBonds (cellBall S z 1) (j + 1),
      AnalyticAt ℂ (fun w => complexGaugedContourAverage (complexChartField R (W w) j)
        (complexBalancingGauge (complexChartField R (W w) j) (R j)) c) t₀ ∧
        0 < (complexGaugedContourAverage (complexChartField R (W t₀) j)
          (complexBalancingGauge (complexChartField R (W t₀) j) (R j)) c).det.re := by
    intro j hj c hc
    have hcg : ContoursNearReal (complexChartField R (W t₀) j) (R j) t σ c :=
      contoursNearReal_of_deviation hodd hj (hgap j hj)
        (fun b _ h => det_complexChartField_of_norm_lt_one R (W t₀) j _ _ (lt_of_le_of_lt h ht1)) hc
        (fun h hh π => href j (by omega) c hc h hh π)
    have hX : HoldsOnHull c (fun b i => AnalyticAt ℂ (fun w => complexChartField R (W w) j b i) t₀) :=
      holdsOnHull_of_innerBonds hj hodd hc fun b hb => hF j hj b hb
    exact ⟨analyticAt_complexGaugedContourAverage (X := fun w => complexChartField R (W w) j) hodd (R j) (by omega)
        ht hτ hcg hX,
      (unitPart_and_sqrt_near hodd (by omega) ht hσ hτ hcg).1⟩
  have hbond : ∀ j ∈ Finset.range F.top, ∀ c ∈ bondsOver S {z} (j + 1),
      AnalyticAt ℂ (fun w => complexBondTermOverTop R (W w) T j c) t₀ := by
    intro j hj c hc
    have hj' := Finset.mem_range.1 hj
    have hcD : c ∈ innerBonds (cellBall S z 1) (j + 1) :=
      BlockLines.mem_innerBonds_cellBall_of_mem_bondsOver hamb hodd S z (by omega) hc
    obtain ⟨hM, hre⟩ := hmean j hj' c hcD
    have e : (fun w => complexBondTermOverTop R (W w) T j c) = fun w =>
        complexBlockFit (complexGaugedContourAverage (complexChartField R (W w) j)
          (complexBalancingGauge (complexChartField R (W w) j) (R j)) c)
          (complexChainOverTop R (W w) T (j + 1) c.1 c.2) := by
      funext w
      exact complexBondTermOverTop_eq R (W w) T hj' c
    rw [e]
    refine analyticAt_complexBlockFit_comp hM (Or.inl hre) ?_
    by_cases htop : j + 1 = F.top
    · have hjt : j = F.depth := Nat.succ.inj htop
      subst hjt
      have e2 : (fun w => complexChainOverTop R (W w) T (F.depth + 1) c.1 c.2) = fun _ => T c.1 c.2 := by
        funext w
        rw [complexChainOverTop_top R (W w) T]
      rw [e2]
      exact analyticAt_const
    · have e2 : (fun w => complexChainOverTop R (W w) T (j + 1) c.1 c.2) =
          fun w => complexChartField R (W w) (j + 1) c.1 c.2 := by
        funext w
        rw [complexChainOverTop_of_ne R (W w) T htop]
      rw [e2]
      exact hF (j + 1) (by omega) c hcD
  simp only [cellTerms]
  refine (Finset.analyticAt_fun_sum _ hplaq).add (analyticAt_const.mul ?_)
  exact Finset.analyticAt_fun_sum _ fun j hj => Finset.analyticAt_fun_sum _ fun c hc => hbond j hj c hc
section Values
theorem sum_abs_pow_le_of_finsetLpNorm_le {ι : Type} {P : ℕ} (hP : 1 ≤ P) {s : Finset ι} {f : ι → ℝ} {x : ℝ}
    (h : finsetLpNorm P s f ≤ x) : ∑ i ∈ s, |f i| ^ P ≤ x ^ P := by
  have h0 : 0 ≤ ∑ i ∈ s, |f i| ^ P := Finset.sum_nonneg fun _ _ => by positivity
  have hP0 : (P : ℝ) ≠ 0 := by exact_mod_cast (by omega : P ≠ 0)
  have e : finsetLpNorm P s f ^ P = ∑ i ∈ s, |f i| ^ P := by
    unfold finsetLpNorm
    rw [← Real.rpow_natCast, ← Real.rpow_mul h0, one_div, inv_mul_cancel₀ hP0, Real.rpow_one]
  rw [← e]
  exact pow_le_pow_left₀ (finsetLpNorm_nonneg _ _ _) h P
def plaquetteConstant : ℝ := 3 / 2 * (174 ^ 2 * 1296 + 1 + 173 ^ 2 * 128 ^ 2)
theorem sum_norm_complexPlaquetteTerm_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {S : Finset F.Cell}
    {z : F.Cell} {R : F.FieldChain} {C₀ s y : ℝ} (ctx : CellHypotheses S z R C₀ s y) {W : ComplexChainChart F}
    (hz : SourceBounds S z R W y) :
    ∑ q ∈ plaquettesOver S {z} 0, ‖complexPlaquetteTerm (complexChartField R W 0) q‖ ≤ plaquetteConstant * y ^ 2 := by
  have hy0 := ctx.small.pos
  have hy1 := ctx.small.le_bound
  have hL1 : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  set Pq := plaquettesOver S {z} 0 with hPq
  set A : ℝ := (F.blockSide : ℝ) ^ F.top with hA
  have hA0 : 0 < A := by positivity
  have hN4 : finsetLpNorm 4 Pq (fun q => plaquetteSourceNorm q (baseSource W)) ≤ 128 * y := by
    have h4 := finsetLpNorm_plaquetteSourceNorm_le_bonds hamb hodd (S := S) (z := z) (0 : F.Site 0) 4 (by norm_num)
      (baseSource W)
    have := hz.base_le
    linarith
  have hNpt : ∀ q ∈ Pq, plaquetteSourceNorm q (baseSource W) ≤ 128 * y := fun q hq =>
    (le_abs_self _).trans ((abs_le_finsetLpNorm (P := 4) (by norm_num) _ hq).trans hN4)
  have hsum4 := sum_abs_pow_le_of_finsetLpNorm_le (P := 4) (by norm_num) hN4
  have hsum2 := sum_abs_pow_le_of_finsetLpNorm_le (P := 2) (by norm_num) hz.curl_le
  have hpt : ∀ q ∈ Pq, ‖complexPlaquetteTerm (complexChartField R W 0) q‖ ≤
      3 / 2 * (174 ^ 2 * (y / A ^ 2) ^ 2 + |‖covariantCurl (R 0) q (baseSource W)‖| ^ 2 +
        173 ^ 2 * |plaquetteSourceNorm q (baseSource W)| ^ 4) := by
    intro q hq
    set N := plaquetteSourceNorm q (baseSource W) with hN
    set κ := ‖covariantCurl (R 0) q (baseSource W)‖ with hκ
    set σ := ‖ofUnit (basePlaquetteHolonomy (R 0) q) - 1‖ with hσd
    have hN0 : 0 ≤ N := plaquetteSourceNorm_nonneg q _
    have hκ0 : 0 ≤ κ := norm_nonneg _
    have hσ0 : 0 ≤ σ := norm_nonneg _
    have hN1 : N ≤ 1 / 256 := by
      have := hNpt q hq
      linarith
    have hσe : σ ≤ y / A ^ 2 := by
      refine (ctx.plaquette_le q hq).trans ?_
      exact div_le_div_of_nonneg_right ctx.const_mul_scale_le (by positivity)
    have hrem := norm_plaquetteRemainder_le (R 0) q hN1 (le_refl σ)
    have hgap : ‖plaquetteGap (R 0) q (baseSource W)‖ ≤ 174 * σ + κ + 173 * N ^ 2 := by
      rw [plaquetteGap_eq]
      refine (norm_add_le _ _).trans ?_
      have h1 := norm_add_le (ofUnit (basePlaquetteHolonomy (R 0) q) - 1) (covariantCurl (R 0) q (baseSource W))
      have h2 : σ * N ≤ σ := mul_le_of_le_one_right hσ0 (by linarith)
      have h3 : ‖plaquetteRemainder (R 0) q (baseSource W)‖ ≤ 173 * N ^ 2 + 173 * σ := by nlinarith
      linarith
    have hterm : ‖complexPlaquetteTerm (complexChartField R W 0) q‖ ≤
        ‖plaquetteGap (R 0) q (baseSource W)‖ ^ 2 / 2 := by
      rw [CellSources.complexChartField_zero, complexPlaquetteTerm_expField_eq, norm_div, Complex.norm_ofNat]
      have := norm_det_le (plaquetteGap (R 0) q (baseSource W))
      linarith
    have hg0 := norm_nonneg (plaquetteGap (R 0) q (baseSource W))
    have hsq : ‖plaquetteGap (R 0) q (baseSource W)‖ ^ 2 ≤ (174 * σ + κ + 173 * N ^ 2) ^ 2 :=
      pow_le_pow_left₀ hg0 hgap 2
    have h3 : (174 * σ + κ + 173 * N ^ 2) ^ 2 ≤ 3 * (174 ^ 2 * σ ^ 2 + κ ^ 2 + 173 ^ 2 * N ^ 4) := by
      nlinarith [sq_nonneg (174 * σ - κ), sq_nonneg (174 * σ - 173 * N ^ 2), sq_nonneg (κ - 173 * N ^ 2)]
    have h4 : σ ^ 2 ≤ (y / A ^ 2) ^ 2 := pow_le_pow_left₀ hσ0 hσe 2
    rw [abs_of_nonneg hκ0, abs_of_nonneg hN0]
    nlinarith
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum,
    nsmul_eq_mul]
  have hcard := card_plaquettesOver_singleton_le hamb hodd S z
  have hc1 : (Pq.card : ℝ) * (174 ^ 2 * (y / A ^ 2) ^ 2) ≤ 174 ^ 2 * 1296 * y ^ 2 := by
    have e : (174 : ℝ) ^ 2 * 1296 * y ^ 2 = (1296 * A ^ 4) * (174 ^ 2 * (y / A ^ 2) ^ 2) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right hcard (by positivity)
  have hy128 : 128 * y ≤ 1 := by linarith
  have hc3 : (173 : ℝ) ^ 2 * ∑ q ∈ Pq, |plaquetteSourceNorm q (baseSource W)| ^ 4 ≤ 173 ^ 2 * 128 ^ 2 * y ^ 2 := by
    have h1 : (128 * y) ^ 4 ≤ (128 * y) ^ 2 := pow_le_pow_of_le_one (by positivity) hy128 (by norm_num)
    have e : (128 * y) ^ 2 = 128 ^ 2 * y ^ 2 := by ring
    have h2 : ∑ q ∈ Pq, |plaquetteSourceNorm q (baseSource W)| ^ 4 ≤ 128 ^ 2 * y ^ 2 := by
      rw [← e]
      exact hsum4.trans h1
    have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 173 ^ 2)
    linarith
  unfold plaquetteConstant
  nlinarith
theorem sum_norm_complexBondTerm_lowerBonds_le (hodd : Odd F.blockSide) {S : Finset F.Cell} {z : F.Cell}
    {R : F.FieldChain} (V : F.GaugeField F.top) {C₀ s y : ℝ} (ctx : CellHypotheses S z R C₀ s y)
    {W : ComplexChainChart F} (hz : SourceBounds S z R W y) (hss : SourcesSmall (cellBall S z 1) W)
    (hball : DeviationBall R (cellBall S z 1) W (8 * y) (8 * y))
    (hτ : 4 * (F.blockSide : ℝ) * (8 * y) ≤ 1 / 1024)
    (href : ∀ j, j + 1 ≤ F.top → ∀ c ∈ innerBonds (cellBall S z 1) (j + 1),
      ∀ h ∈ centredCube F.blockSide, ∀ π, ‖ofUnit (pathHolonomy (R j) (refineSite c.1)
        (bondContour F.blockSide h π c.2) * (polarUnit (_root_.YangMills.Construction.BlockAverages.contourAverage (R j) c))⁻¹) - 1‖ ≤ y) :
    ∑ x ∈ lowerBonds (cellBall S z 1), ‖complexBondTerm R W V x.1 x.2‖ ≤ 10 * y ^ 2 := by
  have hy0 := ctx.small.pos
  have hy1 := ctx.small.le_bound
  set D := cellBall S z 1 with hD
  have hsrc := sum_abs_pow_le_of_finsetLpNorm_le (P := 2) (by norm_num)
    (finsetLpNorm_levelSource_sub_one_le hss hz.upper_le)
  have hmis := sum_abs_pow_le_of_finsetLpNorm_le (P := 2) (by norm_num) ctx.defect_le
  have hpt : ∀ x ∈ lowerBonds D, ‖complexBondTerm R W V x.1 x.2‖ ≤
      2 * |‖levelSource W x.1 x.2.1 x.2.2 - 1‖| ^ 2 + 2 * |‖ofUnit (referenceDefect R x.1 x.2) - 1‖| ^ 2 := by
    intro x hx
    obtain ⟨hxn, hxb⟩ := ComplexCells.mem_lowerBonds hx
    obtain ⟨hre, hroot⟩ := complexGaugedContourAverage_det_good hodd (R := R) (W := W) (D := D) (t := 8 * y)
      (σ := y) (by positivity) (by linarith) (by linarith) hτ (by omega)
      (hball.norm_deviation_le _ (by omega)) hxb (href x.1 (by omega) x.2 hxb)
    have hne : (complexGaugedContourAverage (complexChartField R W x.1)
        (complexBalancingGauge (complexChartField R W x.1) (R x.1)) x.2).det ≠ 0 := by
      intro h0
      rw [h0] at hre
      simp at hre
    rw [complexBondTerm_of_lt_top R W V hxn x.2 hne, norm_mul, norm_div, Complex.norm_ofNat]
    set E := levelSource W x.1 x.2.1 x.2.2 with hE
    set g := referenceDefect R x.1 x.2 with hg
    have h1 : ‖E * ofUnit g - 1‖ ≤ ‖E - 1‖ + ‖ofUnit g - 1‖ := by
      have e : E * ofUnit g - 1 = (E - 1) * ofUnit g + (ofUnit g - 1) := by noncomm_ring
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul_ofUnit]
    have h2 := norm_det_le (E * ofUnit g - 1)
    have h3 := norm_nonneg (E * ofUnit g - 1)
    have h4 : ‖E * ofUnit g - 1‖ ^ 2 ≤ (‖E - 1‖ + ‖ofUnit g - 1‖) ^ 2 := pow_le_pow_left₀ h3 h1 2
    have h5 : 0 ≤ ‖(E * ofUnit g - 1).det‖ / 2 := by positivity
    have h6 := mul_le_mul_of_nonneg_right hroot h5
    rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)]
    nlinarith [sq_nonneg (‖E - 1‖ - ‖ofUnit g - 1‖)]
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  nlinarith
theorem norm_complexBlockFit_top_le (hodd : Odd F.blockSide) {S : Finset F.Cell} {z : F.Cell} {R : F.FieldChain}
    {C₀ s y : ℝ} (ctx : CellHypotheses S z R C₀ s y) {W : ComplexChainChart F}
    (hball : DeviationBall R (cellBall S z 1) W (8 * y) (8 * y)) (hτ : 4 * (F.blockSide : ℝ) * (8 * y) ≤ 1 / 1024)
    {X' : ComplexQuat} (hX : X'.det = 1) {c : F.Site (F.depth + 1) × Fin 4}
    (hc : c ∈ innerBonds (cellBall S z 1) (F.depth + 1))
    (href : ∀ h ∈ centredCube F.blockSide, ∀ π, ‖ofUnit (pathHolonomy (R F.depth) (refineSite c.1)
        (bondContour F.blockSide h π c.2) * (polarUnit (_root_.YangMills.Construction.BlockAverages.contourAverage (R F.depth) c))⁻¹) - 1‖ ≤ C₀ * s)
    (hQ : ‖ofUnit (polarUnit (_root_.YangMills.Construction.BlockAverages.contourAverage (R F.depth) c)) * Matrix.adjugate X' - 1‖ ≤ y) :
    ‖complexBlockFit (complexGaugedContourAverage (complexChartField R W F.depth)
        (complexBalancingGauge (complexChartField R W F.depth) (R F.depth)) c) X'‖ ≤
      ((32 * hullBondCount F.blockSide + 1) * y) ^ 2 := by
  have hy := ctx.small
  have hy0 := hy.pos
  have hy1 := hy.le_bound
  have hCs := ctx.const_mul_scale_le
  have hC0 : 0 < C₀ * s := mul_pos ctx.const_pos ctx.scale_pos
  have hL1 : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  have hH0 := hullBondCount_nonneg F.blockSide
  have hj : F.depth + 1 ≤ F.top := le_rfl
  have hjn : F.depth < F.top := Nat.lt_succ_self _
  set gp := levelDeviation R W F.depth with hgp
  set t := hullBondCount F.blockSide * (8 * y) with ht
  set σ := C₀ * s with hσd
  have ht0 : 0 ≤ t := by positivity
  have hd := hball.det_eq_one hodd (by linarith) hjn hc
  have e1 : complexGaugedContourAverage (complexChartField R W F.depth)
      (complexBalancingGauge (complexChartField R W F.depth) (R F.depth)) c = liftedBondMean (R F.depth) c gp :=
    complexGaugedContourAverage_eq_liftedBondMean hodd hj hd
  obtain ⟨hre, hroot⟩ := complexGaugedContourAverage_det_good hodd (R := R) (W := W) (D := cellBall S z 1)
    (t := 8 * y) (σ := σ) (by positivity) (by linarith) (by linarith) hτ hjn (hball.norm_deviation_le _ hjn) hc href
  rw [e1] at hre hroot ⊢
  have hhull : bondHullNorm c gp ≤ t := hball.bondHullNorm_le hodd (by positivity) hjn hc
  have hhull0 : 0 ≤ bondHullNorm c gp := bondHullSum_nonneg c fun _ _ => norm_nonneg _
  have hsmall : 8 * (F.blockSide : ℝ) * bondHullNorm c gp ≤ 1 / 1024 := by
    have h1 := hy.count_le_radius
    unfold hullBallRadius at h1
    rw [le_div_iff₀ (by positivity)] at h1
    have h2 : 0 ≤ hullBondCount F.blockSide * y * F.blockSide := by positivity
    have h3 : 0 ≤ y * (F.blockSide : ℝ) := by positivity
    have h4 : 8 * (F.blockSide : ℝ) * bondHullNorm c gp ≤ 8 * (F.blockSide : ℝ) * t :=
      mul_le_mul_of_nonneg_left hhull (by positivity)
    have e2 : 8 * (F.blockSide : ℝ) * t = 64 * (hullBondCount F.blockSide * y * F.blockSide) := by rw [ht]; ring
    have e3 : 48 * (48 * hullBondCount F.blockSide + 1) * y * (8192 * (F.blockSide : ℝ)) =
        48 * 48 * 8192 * (hullBondCount F.blockSide * y * F.blockSide) + 48 * 8192 * (y * F.blockSide) := by ring
    rw [e3] at h1
    linarith
  have hσ64 : σ ≤ 1 / 64 := by linarith
  have hfit := topBlockFit_eq hodd hj hσ64 href hsmall X'
  have efit : complexBlockFit (liftedBondMean (R F.depth) c gp) X' = topBlockFit (R F.depth) c X' gp := rfl
  rw [efit, hfit]
  set w := polarUnit (_root_.YangMills.Construction.BlockAverages.contourAverage (R F.depth) c) with hw
  set M := liftedBondMean (R F.depth) c gp with hM
  have hne : M.det ≠ 0 := by
    intro h0
    rw [h0] at hre
    simp at hre
  set U := linearizedUnit (R F.depth) c gp with hU
  set Q := ofUnit w * Matrix.adjugate X' with hQd
  have eU : U = unitPart M * ofUnit w⁻¹ := by
    simp only [hU, linearizedUnit, unitRemainder, ← hM, ← hw]
    abel
  have eroot : ((‖_root_.YangMills.Construction.BlockAverages.contourAverage (R F.depth) c‖ : ℝ) : ℂ) + sqrtRemainder (R F.depth) c gp = principalSqrt M.det := by
    simp only [sqrtRemainder, ← hM]
    abel
  rw [eroot]
  have hdetG : (U * Q).det = 1 := by
    rw [eU, hQd, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, det_unitPart hne, det_ofUnit, det_ofUnit,
      Matrix.det_adjugate, hX]
    simp
  rw [one_sub_half_trace_eq_half_det hdetG, norm_mul, norm_div, Complex.norm_ofNat]
  have hU1 : ‖U - 1‖ ≤ 2 * t := by
    have hz0 : bondHullNorm c (0 : F.Site F.depth → Fin 4 → ComplexQuat) ≤ t := by
      have e : bondHullNorm c (0 : F.Site F.depth → Fin 4 → ComplexQuat) = 0 := by
        simp [bondHullNorm, bondHullSum]
      rw [e]
      exact ht0
    have hrad : 3 * (t + σ) < hullBallRadius F.blockSide := by
      have h1 := hy.count_le_radius
      have h2 : 0 ≤ hullBondCount F.blockSide * y := by positivity
      have e : 48 * (48 * hullBondCount F.blockSide + 1) * y = 2304 * (hullBondCount F.blockSide * y) + 48 * y := by
        ring
      have e2 : t = 8 * (hullBondCount F.blockSide * y) := by rw [ht]; ring
      rw [e] at h1
      rw [e2]
      linarith
    have hsub := norm_linearizedUnit_sub_le hodd hj hC0 hσ64 href ht0 hrad hz0 hhull
    have hzero := (linearizedUnit_zero hodd hj hσ64 href).1
    rw [hzero] at hsub
    have e0 : gp - 0 = gp := sub_zero gp
    simp only [e0] at hsub
    have hav := lineBlockAverage_le_bondHullSum hodd (f := fun x d => ‖gp x d‖) (fun _ _ => norm_nonneg _) c
    have hK : 12 * (200000 * (F.blockSide : ℝ) ^ 2) * (t + σ) ≤ 1 := by
      have h1 := hy.scaled_count_le
      have h2 : t + σ ≤ (48 * hullBondCount F.blockSide + 1) * y := by
        have e2 : t = 8 * (hullBondCount F.blockSide * y) := by rw [ht]; ring
        have h3 : 0 ≤ hullBondCount F.blockSide * y := by positivity
        rw [e2]
        nlinarith
      have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 12 * (200000 * (F.blockSide : ℝ) ^ 2))
      linarith
    have h5 : 12 * (200000 * (F.blockSide : ℝ) ^ 2) * (t + σ) * bondHullNorm c gp ≤ bondHullNorm c gp :=
      mul_le_of_le_one_left hhull0 hK
    have h6 : bondHullSum c (fun x d => ‖gp x d‖) = bondHullNorm c gp := rfl
    linarith
  have hQ2 : ‖Q‖ ≤ 2 := by
    have e : Q = (Q - 1) + 1 := by abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_one]
    linarith
  have hG : ‖U * Q - 1‖ ≤ (32 * hullBondCount F.blockSide + 1) * y := by
    have e : U * Q - 1 = (U - 1) * Q + (Q - 1) := by noncomm_ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have h1 := norm_mul_le (U - 1) Q
    have h2 : ‖U - 1‖ * ‖Q‖ ≤ 2 * t * 2 := mul_le_mul hU1 hQ2 (norm_nonneg _) (by positivity)
    have e2 : 2 * t * 2 = 32 * hullBondCount F.blockSide * y := by rw [ht]; ring
    nlinarith
  have h2 := norm_det_le (U * Q - 1)
  have h3 := norm_nonneg (U * Q - 1)
  have h4 : ‖U * Q - 1‖ ^ 2 ≤ ((32 * hullBondCount F.blockSide + 1) * y) ^ 2 := pow_le_pow_left₀ h3 hG 2
  have h5 : 0 ≤ ‖(U * Q - 1).det‖ / 2 := by positivity
  have h6 := mul_le_mul_of_nonneg_right hroot h5
  nlinarith
def cellConstant (L : ℕ) (a : ℝ) : ℝ := plaquetteConstant + |a| * (10 + 4 * (32 * hullBondCount L + 1) ^ 2)
theorem cellConstant_nonneg (L : ℕ) (a : ℝ) : 0 ≤ cellConstant L a := by
  unfold cellConstant plaquetteConstant
  positivity
theorem norm_cellTerms_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (a : ℝ) {S : Finset F.Cell}
    {z : F.Cell} {R : F.FieldChain} (V : F.GaugeField F.top) {C₀ s y : ℝ} (ctx : CellHypotheses S z R C₀ s y)
    {W : ComplexChainChart F} (hz : SourceBounds S z R W y) (T : F.ComplexField F.top)
    (hT : ∀ c ∈ bondsOver S {z} (F.depth + 1), (T c.1 c.2).det = 1 ∧
      ‖ofUnit (polarUnit (contourAverage (R F.depth) c)) * Matrix.adjugate (T c.1 c.2) - 1‖ ≤ y) :
    ‖cellTerms a S R W T z‖ ≤ cellConstant F.blockSide a * y ^ 2 := by
  have hy := ctx.small
  have hy0 := hy.pos
  have hy1 := hy.le_bound
  have hCs := ctx.const_mul_scale_le
  have hC0 : 0 < C₀ * s := mul_pos ctx.const_pos ctx.scale_pos
  have hL1 : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  obtain ⟨hss, hball⟩ := CellSources.deviationBall_of_finsetLpNorm_le (ctx.level_le W) hz.base_le hz.upper_le
    (by linarith)
  have hH1 : (1 : ℝ) ≤ hullBondCount F.blockSide := by
    unfold hullBondCount
    have h1 : (1 : ℝ) ≤ (F.blockSide : ℝ) ^ 4 := one_le_pow₀ hL1
    have h2 : (0 : ℝ) ≤ (F.blockSide : ℝ) ^ 5 := by positivity
    linarith
  have hτ : 4 * (F.blockSide : ℝ) * (8 * y) ≤ 1 / 1024 := by
    have h1 := hy.count_le_radius
    unfold hullBallRadius at h1
    rw [le_div_iff₀ (by positivity)] at h1
    have h3 : 0 ≤ y * (F.blockSide : ℝ) := by positivity
    have h2 : y * (F.blockSide : ℝ) ≤ hullBondCount F.blockSide * y * F.blockSide := by
      have := mul_le_mul_of_nonneg_right hH1 h3
      nlinarith
    have e3 : 48 * (48 * hullBondCount F.blockSide + 1) * y * (8192 * (F.blockSide : ℝ)) =
        48 * 48 * 8192 * (hullBondCount F.blockSide * y * F.blockSide) + 48 * 8192 * (y * F.blockSide) := by ring
    rw [e3] at h1
    nlinarith
  have hnear : ∀ j, j + 1 ≤ F.top → ∀ c ∈ innerBonds (cellBall S z 1) (j + 1), ∀ h ∈ centredCube F.blockSide, ∀ π,
      ‖ofUnit (pathHolonomy (R j) (refineSite c.1) (bondContour F.blockSide h π c.2) *
        (polarUnit (_root_.YangMills.Construction.BlockAverages.contourAverage (R j) c))⁻¹) - 1‖ ≤ C₀ * s := by
    intro j hj c hc h hh π
    refine (ctx.near j hj c hc h hh π).trans ?_
    have h3 : ((1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1))) ^ 2 ≤ 1 :=
      pow_le_one₀ (by positivity) (inv_pow_le_one hodd.pos _)
    exact mul_le_of_le_one_right hC0.le h3
  have hmid := sum_norm_complexBondTerm_lowerBonds_le hodd V ctx hz hss hball hτ
    (fun j hj c hc h hh π => (hnear j hj c hc h hh π).trans hCs)
  have hplaq := sum_norm_complexPlaquetteTerm_le hamb hodd ctx hz
  set D := cellBall S z 1 with hD
  set B := ((32 * hullBondCount F.blockSide + 1) * y) ^ 2 with hB
  have hB0 : 0 ≤ B := by positivity
  have htop : ∑ c ∈ bondsOver S {z} (F.depth + 1), ‖complexBondTermOverTop R W T F.depth c‖ ≤ 4 * B := by
    have h1 : ∀ c ∈ bondsOver S {z} (F.depth + 1), ‖complexBondTermOverTop R W T F.depth c‖ ≤ B := by
      intro c hc
      have hcD : c ∈ innerBonds D (F.depth + 1) :=
        BlockLines.mem_innerBonds_cellBall_of_mem_bondsOver hamb hodd S z le_rfl hc
      rw [complexBondTermOverTop_depth]
      obtain ⟨h1, h2⟩ := hT c hc
      exact norm_complexBlockFit_top_le hodd ctx hball hτ h1 hcD (hnear F.depth le_rfl c hcD) h2
    refine (Finset.sum_le_card_nsmul _ _ B h1).trans ?_
    rw [nsmul_eq_mul]
    have hcard : ((bondsOver S {z} (F.depth + 1)).card : ℝ) ≤ 4 := by
      exact_mod_cast card_bondsOver_singleton_top_le (S := S) (z := z) (k := F.depth + 1) rfl
    exact mul_le_mul_of_nonneg_right hcard hB0
  have hmid2 : ∑ j ∈ Finset.range F.depth, ∑ c ∈ bondsOver S {z} (j + 1), ‖complexBondTermOverTop R W T j c‖ ≤
      10 * y ^ 2 := by
    refine le_trans ?_ hmid
    rw [lowerBonds, Finset.sum_sigma]
    have e : F.top - 1 = F.depth := rfl
    rw [e]
    refine Finset.sum_le_sum fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    have h1 : ∀ c ∈ bondsOver S {z} (j + 1), ‖complexBondTermOverTop R W T j c‖ = ‖complexBondTerm R W V j c‖ :=
      fun c _ => by rw [complexBondTermOverTop_of_lt R W T V (by omega) c]
    rw [Finset.sum_congr rfl h1]
    exact Finset.sum_le_sum_of_subset_of_nonneg (bondsOver_singleton_subset_innerBonds hamb hodd (by omega))
      fun _ _ _ => norm_nonneg _
  unfold cellTerms
  refine (norm_add_le _ _).trans ?_
  have h1 := norm_sum_le (plaquettesOver S {z} 0) fun p => complexPlaquetteTerm (complexChartField R W 0) p
  have h2 : ‖∑ j ∈ Finset.range F.top, ∑ c ∈ bondsOver S {z} (j + 1), complexBondTermOverTop R W T j c‖ ≤
      10 * y ^ 2 + 4 * B := by
    refine (norm_sum_le _ _).trans ?_
    have h3 : ∑ j ∈ Finset.range F.top, ‖∑ c ∈ bondsOver S {z} (j + 1), complexBondTermOverTop R W T j c‖ ≤
        ∑ j ∈ Finset.range F.top, ∑ c ∈ bondsOver S {z} (j + 1), ‖complexBondTermOverTop R W T j c‖ :=
      Finset.sum_le_sum fun _ _ => norm_sum_le _ _
    refine h3.trans ?_
    rw [Finset.sum_range_succ]
    linarith
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h4 := mul_le_mul_of_nonneg_left h2 (abs_nonneg a)
  have e : cellConstant F.blockSide a * y ^ 2 = plaquetteConstant * y ^ 2 + |a| * (10 * y ^ 2 + 4 * B) := by
    rw [hB]
    unfold cellConstant
    ring
  rw [e]
  linarith
end Values
section Twist
private theorem trace_ofQuat_imaginary (w : imaginaryQuaternions) : (ofQuat (w : ℍ[ℝ])).trace = 0 := by
  have h0 : (w : ℍ[ℝ]).re = 0 := w.2
  simp only [ofQuat, Matrix.trace_fin_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  apply Complex.ext <;> simp [h0]
private theorem adjugate_eq_neg_of_trace_eq_zero {e : ComplexQuat} (h : e.trace = 0) : Matrix.adjugate e = -e := by
  rw [Matrix.trace_fin_two] at h
  rw [Matrix.adjugate_fin_two]
  ext i k
  fin_cases i <;> fin_cases k <;> simp
  · linear_combination h
  · linear_combination h
private theorem adjugate_sub_one_eq (A : ComplexQuat) : Matrix.adjugate A - 1 = Matrix.adjugate (A - 1) := by
  rw [Matrix.adjugate_fin_two, Matrix.adjugate_fin_two]
  ext i k
  fin_cases i <;> fin_cases k <;> simp
private def jMatrix : ComplexQuat := !![0, 1; -1, 0]
private def jMatrixInv : ComplexQuat := !![0, -1; 1, 0]
private theorem jMatrix_mul_jMatrixInv : jMatrix * jMatrixInv = 1 := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [jMatrix, jMatrixInv, Matrix.mul_apply, Fin.sum_univ_two]
private theorem jMatrixInv_mul_jMatrix : jMatrixInv * jMatrix = 1 := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [jMatrix, jMatrixInv, Matrix.mul_apply, Fin.sum_univ_two]
private theorem adjugate_eq_jMatrix_conj (A : ComplexQuat) :
    Matrix.adjugate A = jMatrix * A.transpose * jMatrix⁻¹ := by
  rw [Matrix.inv_eq_right_inv jMatrix_mul_jMatrixInv, Matrix.adjugate_fin_two]
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [jMatrix, jMatrixInv, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
theorem det_exp_of_trace_eq_zero {e : ComplexQuat} (h : e.trace = 0) : (NormedSpace.exp e).det = 1 := by
  have hU : IsUnit jMatrix := ⟨⟨jMatrix, jMatrixInv, jMatrix_mul_jMatrixInv, jMatrixInv_mul_jMatrix⟩, rfl⟩
  have e1 : Matrix.adjugate (NormedSpace.exp e) = NormedSpace.exp (-e) := by
    rw [adjugate_eq_jMatrix_conj, ← Matrix.exp_transpose, ← Matrix.exp_conj _ _ hU, ← adjugate_eq_jMatrix_conj,
      adjugate_eq_neg_of_trace_eq_zero h]
  have e2 : NormedSpace.exp e * NormedSpace.exp (-e) = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_right (Commute.refl e)), add_neg_cancel,
      NormedSpace.exp_zero]
  have e3 := Matrix.mul_adjugate (NormedSpace.exp e)
  rw [e1, e2] at e3
  have e4 := congrFun (congrFun e3 0) 0
  simpa using e4.symm
variable {k : ℕ}
theorem complexTwistedTop_fits (b : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (hX : AreUnitVectors X) (ζ : Fin k → ℂ) (V : F.GaugeField F.top) (c : F.Site F.top × Fin 4) {v : ℝ}
    (hv : ∑ l, (if b l = c then ‖ζ l‖ else 0) ≤ v) (hv1 : v ≤ 1) (w : UnitQuaternion) :
    (complexTwistedTop b X ζ V c.1 c.2).det = 1 ∧
      ‖ofUnit w * Matrix.adjugate (complexTwistedTop b X ζ V c.1 c.2) - 1‖ ≤
        2 * v + ‖ofUnit (V c.1 c.2 * w⁻¹) - 1‖ := by
  classical
  set E : ComplexQuat := ∑ l, if b l = (c.1, c.2) then ζ l • ofQuat (X l : ℍ[ℝ]) else 0 with hE
  have eT : complexTwistedTop b X ζ V c.1 c.2 = NormedSpace.exp E * ofUnit (V c.1 c.2) := rfl
  have htr : E.trace = 0 := by
    rw [hE, Matrix.trace_sum]
    refine Finset.sum_eq_zero fun l _ => ?_
    split_ifs
    · rw [Matrix.trace_smul, trace_ofQuat_imaginary, smul_zero]
    · simp
  have hdet := det_exp_of_trace_eq_zero htr
  have hnE : ‖E‖ ≤ v := by
    refine le_trans ?_ hv
    rw [hE]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
    have ec : (c.1, c.2) = c := rfl
    rw [ec]
    split_ifs
    · rw [norm_smul, norm_ofQuat_imaginary, hX l, mul_one]
    · simp
  have hexp : ‖NormedSpace.exp E - 1‖ ≤ 2 * v := by
    have h1 := norm_exp_sub_one_sub_le (hnE.trans hv1)
    have h2 : NormedSpace.exp E - 1 = (NormedSpace.exp E - 1 - E) + E := by abel
    have hn0 := norm_nonneg E
    have h3 : ‖E‖ ^ 2 ≤ ‖E‖ := by nlinarith [hnE.trans hv1]
    rw [h2]
    refine (norm_add_le _ _).trans ?_
    linarith
  refine ⟨by rw [eT, Matrix.det_mul, hdet, det_ofUnit, one_mul], ?_⟩
  set Ex := NormedSpace.exp E with hEx
  set g := V c.1 c.2 with hg
  have eQ : ofUnit w * Matrix.adjugate (Ex * ofUnit g) = ofUnit (w * g⁻¹) * Matrix.adjugate Ex := by
    rw [Matrix.adjugate_mul_distrib, ← ofUnit_inv, ofUnit_mul, mul_assoc]
  rw [eT, eQ]
  have e1 : ofUnit (w * g⁻¹) * Matrix.adjugate Ex - 1 =
      ofUnit (w * g⁻¹) * (Matrix.adjugate Ex - 1) + (ofUnit (w * g⁻¹) - 1) := by noncomm_ring
  rw [e1]
  refine (norm_add_le _ _).trans ?_
  rw [norm_ofUnit_mul, adjugate_sub_one_eq, norm_adjugate]
  have e2 : ofUnit (w * g⁻¹) - 1 = ofUnit (w * g⁻¹) * (1 - ofUnit (g * w⁻¹)) := by
    rw [mul_sub, mul_one, ← ofUnit_mul]
    simp [ofUnit_one]
  have e3 : ‖ofUnit (w * g⁻¹) - 1‖ = ‖ofUnit (g * w⁻¹) - 1‖ := by
    rw [e2, norm_ofUnit_mul, norm_sub_rev]
  rw [e3]
  linarith
end Twist
section Line
theorem complexChartMove_eq_spanChart (W : ComplexChainChart F) (B : ChainChart F) (τ : ℂ) :
    complexChartMove W B τ = spanChart W.re ![W.im, B] ![Complex.I, τ] := by
  simp only [complexChartMove, spanChart, chartMove, chartShiftMulti, zeroChart, Fin.sum_univ_two]
  simp
theorem baseSource_complexChartMove (W : ComplexChainChart F) (B : ChainChart F) (τ : ℂ) (x : F.Site 0)
    (i : Fin 4) : baseSource (complexChartMove W B τ) x i = baseSource W x i + τ • ofQuat (B.fine x i : ℍ[ℝ]) := by
  rw [complexChartMove_eq_spanChart, baseSource_spanChart, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [← add_assoc]
  rfl
theorem upperSource_complexChartMove (W : ComplexChainChart F) (B : ChainChart F) (τ : ℂ)
    (x : Σ m : ℕ, F.Site (m + 1) × Fin 4) :
    upperSource (complexChartMove W B τ) x = upperSource W x + τ • ofQuat (B.coarse x.1 x.2.1 x.2.2 : ℍ[ℝ]) := by
  rw [complexChartMove_eq_spanChart, upperSource_spanChart, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [← add_assoc]
  rfl
theorem sourceBounds_complexChartMove (hodd : Odd F.blockSide) {S : Finset F.Cell} {z : F.Cell} (R : F.FieldChain)
    (W : ComplexChainChart F) (B : ChainChart F) (τ : ℂ) {y : ℝ}
    (hy : localNorm S R W.re (constOneWeights F) z + localNorm S R W.im (constOneWeights F) z +
      ‖τ‖ * localNorm S R B (constOneWeights F) z ≤ y) : SourceBounds S z R (complexChartMove W B τ) y := by
  rw [complexChartMove_eq_spanChart]
  refine sourceBounds_spanChart hodd R W.re _ _ ?_
  unfold spanLocalNorm
  rw [Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Complex.norm_I, one_mul]
  linarith
end Line
section Cauchy
theorem cellTerms_deriv_bound (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (a : ℝ) {S : Finset F.Cell}
    {z : F.Cell} {R : F.FieldChain} (V : F.GaugeField F.top) {C₀ s y : ℝ} (ctx : CellHypotheses S z R C₀ s y)
    (W : ComplexChainChart F) (B : ChainChart F) (T : F.ComplexField F.top) {size β : ℝ} (hsize : 0 < size)
    (hβ : 0 < β) (hB : localNorm S R B (constOneWeights F) z ≤ β)
    (hW : localNorm S R W.re (constOneWeights F) z + localNorm S R W.im (constOneWeights F) z ≤ size)
    (hy2 : 2 * size ≤ y)
    (hT : ∀ c ∈ bondsOver S {z} (F.depth + 1), (T c.1 c.2).det = 1 ∧
      ‖ofUnit (polarUnit (contourAverage (R F.depth) c)) * Matrix.adjugate (T c.1 c.2) - 1‖ ≤ y) :
    DifferentiableAt ℂ (fun τ : ℂ => cellTerms a S R (complexChartMove W B τ) T z) 0 ∧
      ‖deriv (fun τ : ℂ => cellTerms a S R (complexChartMove W B τ) T z) 0‖ ≤
        cellConstant F.blockSide a * y ^ 2 * β / size := by
  have hy := ctx.small
  have hy0 := hy.pos
  have hy1 := hy.le_bound
  have hCs := ctx.const_mul_scale_le
  have hC0 : 0 < C₀ * s := mul_pos ctx.const_pos ctx.scale_pos
  have hL1 : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  set r := size / β with hr
  have hr0 : 0 < r := div_pos hsize hβ
  have hsz : ∀ τ : ℂ, ‖τ‖ ≤ r → SourceBounds S z R (complexChartMove W B τ) y := by
    intro τ hτ
    refine sourceBounds_complexChartMove hodd R W B τ ?_
    have hn0 : 0 ≤ localNorm S R B (constOneWeights F) z := Real.sqrt_nonneg _
    have h1 : ‖τ‖ * localNorm S R B (constOneWeights F) z ≤ r * β :=
      mul_le_mul hτ hB hn0 hr0.le
    have e : r * β = size := by
      rw [hr]
      field_simp
    linarith
  have hH1 : (1 : ℝ) ≤ hullBondCount F.blockSide := by
    unfold hullBondCount
    have h1 : (1 : ℝ) ≤ (F.blockSide : ℝ) ^ 4 := one_le_pow₀ hL1
    have h2 : (0 : ℝ) ≤ (F.blockSide : ℝ) ^ 5 := by positivity
    linarith
  have hτs : 4 * (F.blockSide : ℝ) * (8 * y) ≤ 1 / 1024 := by
    have h1 := hy.count_le_radius
    unfold hullBallRadius at h1
    rw [le_div_iff₀ (by positivity)] at h1
    have h3 : 0 ≤ y * (F.blockSide : ℝ) := by positivity
    have h2 : y * (F.blockSide : ℝ) ≤ hullBondCount F.blockSide * y * F.blockSide := by
      have := mul_le_mul_of_nonneg_right hH1 h3
      nlinarith
    have e3 : 48 * (48 * hullBondCount F.blockSide + 1) * y * (8192 * (F.blockSide : ℝ)) =
        48 * 48 * 8192 * (hullBondCount F.blockSide * y * F.blockSide) + 48 * 8192 * (y * F.blockSide) := by ring
    rw [e3] at h1
    nlinarith
  have han : ∀ τ : ℂ, ‖τ‖ ≤ r →
      AnalyticAt ℂ (fun w : ℂ => cellTerms a S R (complexChartMove W B w) T z) τ := by
    intro τ hτ
    have hs := hsz τ hτ
    obtain ⟨hss, hball⟩ := CellSources.deviationBall_of_finsetLpNorm_le (ctx.level_le (complexChartMove W B τ))
      hs.base_le hs.upper_le (by linarith)
    refine analyticAt_cellTerms hamb hodd a T (W := fun w => complexChartMove W B w) (t := 8 * y) (σ := C₀ * s)
      (by positivity) (by linarith) (by linarith) hτs ?_ ?_ ?_ ?_ hball.norm_deviation_le ?_
    · intro b _
      have e : (fun w : ℂ => complexifiedImaginary ((complexChartMove W B w).re.fine b.1 b.2)
          ((complexChartMove W B w).im.fine b.1 b.2)) =
          fun w => baseSource W b.1 b.2 + w • ofQuat (B.fine b.1 b.2 : ℍ[ℝ]) := by
        funext w
        exact baseSource_complexChartMove W B w b.1 b.2
      rw [e]
      exact analyticAt_const.add (analyticAt_id.smul analyticAt_const)
    · intro b hb
      exact (hss.base_le b hb).trans (by norm_num)
    · intro j _ b _
      have e : (fun w : ℂ => complexifiedImaginary ((complexChartMove W B w).re.coarse j b.1 b.2)
          ((complexChartMove W B w).im.coarse j b.1 b.2)) =
          fun w => upperSource W ⟨j, b⟩ + w • ofQuat (B.coarse j b.1 b.2 : ℍ[ℝ]) := by
        funext w
        exact upperSource_complexChartMove W B w ⟨j, b⟩
      rw [e]
      exact analyticAt_const.add (analyticAt_id.smul analyticAt_const)
    · intro j hj b hb
      exact (hss.upper_le _ (CellSources.mem_lowerBonds hj hb)).trans (by norm_num)
    · intro j hj c hc h hh π
      refine (ctx.near j hj c hc h hh π).trans ?_
      have h3 : ((1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1))) ^ 2 ≤ 1 :=
        pow_le_one₀ (by positivity) (inv_pow_le_one hodd.pos _)
      exact mul_le_of_le_one_right hC0.le h3
  refine ⟨(han 0 (by simpa using hr0.le)).differentiableAt, ?_⟩
  have hdo : DifferentiableOn ℂ (fun τ : ℂ => cellTerms a S R (complexChartMove W B τ) T z)
      (closedBall (0 : ℂ) r) := by
    intro τ hτ
    have h1 : ‖τ‖ ≤ r := by simpa using hτ
    exact (han τ h1).differentiableAt.differentiableWithinAt
  have hdc : DiffContOnCl ℂ (fun τ : ℂ => cellTerms a S R (complexChartMove W B τ) T z) (ball (0 : ℂ) r) :=
    hdo.diffContOnCl_ball le_rfl
  have hb := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr0 hdc
    (C := cellConstant F.blockSide a * y ^ 2) (fun τ hτ => by
      have h1 : ‖τ‖ ≤ r := by
        have : ‖τ‖ = r := by simpa using hτ
        exact this.le
      exact norm_cellTerms_le hamb hodd a V ctx (hsz τ h1) T hT)
  refine hb.trans (le_of_eq ?_)
  rw [hr]
  field_simp
end Cauchy
theorem sum_bond_weights_le_near {k : ℕ} (b : Fin k → F.Site F.top × Fin 4) (ζ : Fin k → ℂ) {z : F.Cell}
    {c : F.Site F.top × Fin 4} (hc : c.1 = z) :
    ∑ l, (if b l = c then ‖ζ l‖ else 0) ≤ ∑ l, if cellSupDist z (b l).1 ≤ 1 then ‖ζ l‖ else 0 := by
  refine Finset.sum_le_sum fun l _ => ?_
  by_cases h : b l = c
  · have hd : cellSupDist z (b l).1 ≤ 1 := by
      rw [h, hc]
      simp [cellSupDist]
    rw [if_pos h, if_pos hd]
  · rw [if_neg h]
    split_ifs
    · exact norm_nonneg _
    · exact le_rfl
theorem referenceFieldChain_top (S : Finset F.Cell) (V : F.GaugeField F.top) :
    referenceFieldChain S V F.top = V := by apply _root_.YangMills.Construction.ReferenceBounds.referenceFieldChain_top <;> assumption
theorem le_of_forall_pos_bound {K size β Yc d : ℝ} (hK : 0 ≤ K) (hs : 0 < size) (hβ : 0 ≤ β)
    (hd : ∀ ε : ℝ, 0 < ε → d ≤ K * (Yc * size) ^ 2 * (β + ε) / size) : d ≤ K * Yc ^ 2 * (size * β) := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hA : 0 ≤ K * Yc ^ 2 * size := by positivity
  have hκ0 : 0 < K * Yc ^ 2 * size + 1 := by linarith
  refine (hd (ε / (K * Yc ^ 2 * size + 1)) (by positivity)).trans ?_
  have e : K * (Yc * size) ^ 2 * (β + ε / (K * Yc ^ 2 * size + 1)) / size =
      K * Yc ^ 2 * (size * β) + K * Yc ^ 2 * size * (ε / (K * Yc ^ 2 * size + 1)) := by
    field_simp
  rw [e]
  have h2 : K * Yc ^ 2 * size * (ε / (K * Yc ^ 2 * size + 1)) ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ hκ0]
    nlinarith
  linarith
set_option maxHeartbeats 1000000 in
theorem localFirstVariation_holds (hrec : UniformQuarticBoundAcrossLevels) (hbd : referenceBoundsStatement)
    (hsm : smallChartIsRegularStatement) : localFirstVariationStatement := by
  obtain ⟨C, L1, hC, hctx⟩ := cellHypotheses_of_referenceBounds hrec hbd
  obtain ⟨Lr, hregL⟩ := hsm
  obtain ⟨C', cb, Lb, hC', hcb, hb⟩ := hbd
  intro a del ha hd0 hd8
  refine ⟨max (max L1 Lr) (max Lb 5), ?_⟩
  intro L hodd hL
  have hL1 : L1 ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have hLr : Lr ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  have hLb : Lb ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have h5 : 5 ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  obtain ⟨c₁, y₀, hc₁, hy₀, hc⟩ := hctx L hodd hL1 h5
  obtain ⟨c₂, hc₂, hr⟩ := hregL L hodd hLr del hd0 hd8
  set Yc := 26 * C + C' + 2 with hYc
  have hYc0 : 0 < Yc := by positivity
  set c := min (min (min c₁ c₂) (min cb 1)) (y₀ / (4 * Yc)) with hcd
  have hc0 : 0 < c := lt_min (lt_min (lt_min hc₁ hc₂) (lt_min hcb one_pos)) (by positivity)
  have hcc₁ : c ≤ c₁ := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hcc₂ : c ≤ c₂ := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hccb : c ≤ cb := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hc1 : c ≤ 1 := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hcy : 4 * Yc * c ≤ y₀ := by
    have h1 : c ≤ y₀ / (4 * Yc) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1
    linarith
  refine ⟨c, cellConstant L a * Yc ^ 2 + 1, hc0, by
    have := cellConstant_nonneg L a
    positivity, ?_⟩
  intro F m S hFL hamb hm hreg s V hs hsc hcold k b X hX W ζ B hWc hζ
  have hoddF : Odd F.blockSide := hFL ▸ hodd
  set R := referenceFieldChain S V with hR
  obtain ⟨-, -, -, b4, -, -⟩ := hb F m S hoddF (hFL ▸ hLb) hamb hm hreg s V hs (hsc.trans hccb) hcold
  have hre0 : 0 ≤ supWeightedNorm S del R W.re := Real.iSup_nonneg fun _ => Real.sqrt_nonneg _
  have him0 : 0 ≤ supWeightedNorm S del R W.im := Real.iSup_nonneg fun _ => Real.sqrt_nonneg _
  have hnre : supWeightedNorm S del R W.re ≤ c := by
    have : complexSupWeightedNorm S del R W = supWeightedNorm S del R W.re + supWeightedNorm S del R W.im := rfl
    linarith
  have hnim : supWeightedNorm S del R W.im ≤ c := by
    have : complexSupWeightedNorm S del R W = supWeightedNorm S del R W.re + supWeightedNorm S del R W.im := rfl
    linarith
  have hregre := (hr F m S hFL hamb hm hreg s V hs (hsc.trans hcc₂) hcold W.re (hnre.trans hcc₂)).2
  have hregim := (hr F m S hFL hamb hm hreg s V hs (hsc.trans hcc₂) hcold W.im (hnim.trans hcc₂)).2
  have hcell : ∀ z ∈ S, DifferentiableAt ℂ
      (fun τ : ℂ => cellTerms a S R (complexChartMove W B τ) (complexTwistedTop b X ζ V) z) 0 ∧
      ‖deriv (fun τ : ℂ => cellTerms a S R (complexChartMove W B τ) (complexTwistedTop b X ζ V) z) 0‖ ≤
        (cellConstant L a * Yc ^ 2 + 1) *
          (firstVariationCellWeight S R s W b ζ z * localNorm S R B (constOneWeights F) z) := by
    intro z hz
    set size := firstVariationCellWeight S R s W b ζ z with hsz
    set nre := localNorm S R W.re (constOneWeights F) z with hnr
    set nim := localNorm S R W.im (constOneWeights F) z with hni
    set nz : ℝ := ∑ l, if cellSupDist z (b l).1 ≤ 1 then ‖ζ l‖ else 0 with hnz
    have esz : size = s + nre + nim + nz := rfl
    have hnre0 : 0 ≤ nre := Real.sqrt_nonneg _
    have hnim0 : 0 ≤ nim := Real.sqrt_nonneg _
    have hnz0 : 0 ≤ nz := Finset.sum_nonneg fun l _ => by
      split_ifs
      · exact norm_nonneg _
      · exact le_rfl
    have hnzc : nz ≤ c := by
      refine le_trans (Finset.sum_le_sum fun l _ => ?_) hζ
      split_ifs
      · exact le_rfl
      · exact norm_nonneg _
    have hsize : 0 < size := by rw [esz]; linarith
    have hnre2 : nre ≤ 2 * supWeightedNorm S del R W.re := hregre z hz
    have hnim2 : nim ≤ 2 * supWeightedNorm S del R W.im := hregim z hz
    have hsz4 : size ≤ 4 * c := by
      have : complexSupWeightedNorm S del R W = supWeightedNorm S del R W.re + supWeightedNorm S del R W.im := rfl
      rw [esz]
      linarith
    set y := Yc * size with hyd
    have hs_le : s ≤ size := by rw [esz]; linarith
    have hy26 : 26 * C * s ≤ y := by
      have h1 : 26 * C * s ≤ 26 * C * size := mul_le_mul_of_nonneg_left hs_le (by positivity)
      have h2 : (C' + 2) * size ≥ 0 := by positivity
      rw [hyd, hYc]
      nlinarith
    have hyy : y ≤ y₀ := by
      have h1 : Yc * size ≤ Yc * (4 * c) := mul_le_mul_of_nonneg_left hsz4 hYc0.le
      rw [hyd]
      linarith
    have ctx := hc F m S hFL hamb hm hreg s V hs (hsc.trans hcc₁) hcold z y hy26 hyy
    have h2size : 2 * size ≤ y := by
      rw [hyd, hYc]
      have h2 : (26 * C + C') * size ≥ 0 := by positivity
      nlinarith
    have hWs : nre + nim ≤ size := by rw [esz]; linarith
    have hT : ∀ c' ∈ bondsOver S {z} (F.depth + 1), (complexTwistedTop b X ζ V c'.1 c'.2).det = 1 ∧
        ‖ofUnit (polarUnit (_root_.YangMills.Construction.BlockAverages.contourAverage (R F.depth) c')) *
          Matrix.adjugate (complexTwistedTop b X ζ V c'.1 c'.2) - 1‖ ≤ y := by
      intro c' hc'
      obtain ⟨hcS, hcell⟩ := Finset.mem_filter.1 hc'
      have hcz : enclosingCell c'.1 = z := Finset.mem_singleton.1 hcell
      have hc1' : c'.1 = z := by
        rw [← hcz]
        exact (enclosingCell_top c'.1).symm
      have hv := sum_bond_weights_le_near b ζ (c := c') hc1'
      have hv1 : nz ≤ 1 := hnzc.trans hc1
      obtain ⟨h1, h2⟩ := complexTwistedTop_fits b X hX ζ V c' hv hv1 (polarUnit (_root_.YangMills.Construction.BlockAverages.contourAverage (R F.depth) c'))
      refine ⟨h1, h2.trans ?_⟩
      have hmis := b4 c' hcS
      rw [← norm_ofUnit_sub_one] at hmis
      have emis : referenceDefect (referenceFieldChain S V) F.depth c' =
          V c'.1 c'.2 * (polarUnit (_root_.YangMills.Construction.BlockAverages.contourAverage (R F.depth) c'))⁻¹ := by
        simp only [referenceDefect, ← hR]
        rw [show R (F.depth + 1) = V from referenceFieldChain_top S V]
      rw [emis] at hmis
      have h3 : C' * s ≤ C' * size := mul_le_mul_of_nonneg_left hs_le hC'.le
      have h4 : nz ≤ size := by rw [esz]; linarith
      have h5 : 0 ≤ 26 * C * size := by positivity
      rw [hyd, hYc]
      nlinarith
    have hnB0 : 0 ≤ localNorm S R B (constOneWeights F) z := Real.sqrt_nonneg _
    have hd : ∀ ε : ℝ, 0 < ε → DifferentiableAt ℂ
        (fun τ : ℂ => cellTerms a S R (complexChartMove W B τ) (complexTwistedTop b X ζ V) z) 0 ∧
        ‖deriv (fun τ : ℂ => cellTerms a S R (complexChartMove W B τ) (complexTwistedTop b X ζ V) z) 0‖ ≤
          cellConstant F.blockSide a * y ^ 2 * (localNorm S R B (constOneWeights F) z + ε) / size := fun ε hε =>
      cellTerms_deriv_bound hamb hoddF a V ctx W B (complexTwistedTop b X ζ V) hsize (by linarith) (by linarith)
        hWs h2size hT
    refine ⟨(hd 1 one_pos).1, ?_⟩
    have hK0 := cellConstant_nonneg L a
    have hle := le_of_forall_pos_bound hK0 hsize hnB0 (Yc := Yc)
      (d := ‖deriv (fun τ : ℂ => cellTerms a S R (complexChartMove W B τ) (complexTwistedTop b X ζ V) z) 0‖)
      (fun ε hε => by
        have h1 := (hd ε hε).2
        rw [hFL] at h1
        exact h1)
    have h0 : 0 ≤ size * localNorm S R B (constOneWeights F) z := by positivity
    rw [add_mul, one_mul]
    linarith
  have etotal : (fun τ : ℂ => complexTotalOverTop a S R (complexChartMove W B τ) (complexTwistedTop b X ζ V)) =
      fun τ => ∑ z ∈ S, cellTerms a S R (complexChartMove W B τ) (complexTwistedTop b X ζ V) z := by
    funext τ
    exact complexTotalOverTop_eq_sum_cellTerms hoddF a S R _ _
  have hderiv : complexFirstVariation a S R W (complexTwistedTop b X ζ V) B =
      ∑ z ∈ S, deriv (fun τ : ℂ => cellTerms a S R (complexChartMove W B τ) (complexTwistedTop b X ζ V) z) 0 := by
    unfold complexFirstVariation
    rw [etotal]
    exact deriv_fun_sum fun z hz => (hcell z hz).1
  rw [hderiv, Finset.mul_sum]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun z hz => (hcell z hz).2)
end YangMills.Construction.CellFirstVariation
end
