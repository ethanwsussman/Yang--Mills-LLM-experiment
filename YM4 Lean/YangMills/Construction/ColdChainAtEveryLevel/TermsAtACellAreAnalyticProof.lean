import YangMills.Construction.ColdChainAtEveryLevel.LocalFirstVariationProof
import YangMills.Construction.ColdChainAtEveryLevel.TermsAtACellAreAnalytic
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
namespace YangMills.Construction.ComplexCellTerms
open BlockAverages ComplexAnalyticity ComplexLevels ComplexContours ComplexChainStep ComplexRemainders BlockLines
  PlaquettesNearCell ComplexifiedQuaternions
variable {F : BlockFrame} {j : ℕ}
section Sums
private theorem sum_innerPlaquettes_eq_sum_cells (hodd : Odd F.blockSide) (S : Finset F.Cell)
    (f : F.Site 0 × Fin 4 × Fin 4 → ℂ) :
    ∑ p ∈ innerPlaquettes S 0, f p = ∑ z ∈ S, ∑ p ∈ plaquettesOver S {z} 0, f p := by apply _root_.YangMills.SharedProofs.p67426 <;> assumption
private theorem sum_innerBonds_eq_sum_cells (hodd : Odd F.blockSide) (S : Finset F.Cell) (k : ℕ)
    (f : F.Site k × Fin 4 → ℂ) :
    ∑ c ∈ innerBonds S k, f c = ∑ z ∈ S, ∑ c ∈ bondsOver S {z} k, f c := by apply _root_.YangMills.SharedProofs.p65855 <;> assumption
private theorem complexTotalOverTop_eq_sum_complexCellTerms (hodd : Odd F.blockSide) (a : ℝ) (S : Finset F.Cell)
    (R : F.FieldChain) (V : F.GaugeField F.top) (W : ComplexChainChart F) :
    complexTotalOverTop a S R W (complexifyField V) = ∑ z ∈ S, complexCellTerms a S R W V z := by
  have hbonds : ∀ j, ∑ c ∈ innerBonds S (j + 1), complexBondTermOverTop R W (complexifyField V) j c =
      ∑ z ∈ S, ∑ c ∈ bondsOver S {z} (j + 1), complexBondTerm R W V j c := fun j =>
    sum_innerBonds_eq_sum_cells hodd S (j + 1) (complexBondTerm R W V j)
  simp only [complexTotalOverTop, complexCellTerms,
    sum_innerPlaquettes_eq_sum_cells hodd S (complexPlaquetteTerm (complexChartField R W 0)), hbonds,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [Finset.sum_comm (s := Finset.range F.top) (t := S)]
end Sums
private theorem complexFieldChain_top_eq (R : F.FieldChain) (V : F.GaugeField F.top) {k : ℕ} (hk : k = F.top)
    (W W' : ComplexChainChart F) :
    complexFieldChain R W V k = complexFieldChain R W' V k := by
  subst hk
  simp [complexFieldChain]
section Operations
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] {z : P}
private theorem analyticAt_complexBlockFit_comp {M X : P → ComplexQuat} (hM : AnalyticAt ℂ M z)
    (hs : (M z).det ∈ Complex.slitPlane) (hX : AnalyticAt ℂ X z) :
    AnalyticAt ℂ (fun w => complexBlockFit (M w) (X w)) z := by apply _root_.YangMills.SharedProofs.p33576 <;> assumption
private theorem analyticAt_complexGaugedContourAverage_comp (hodd : Odd F.blockSide) {X : P → F.ComplexField j}
    (R : F.GaugeField j) (hj : j + 1 ≤ F.top) {c : F.Site (j + 1) × Fin 4} {t σ : ℝ} (ht : 0 ≤ t)
    (hτ : 4 * (F.blockSide : ℝ) * t ≤ 1 / 1024) (hnear : ContoursNearReal (X z) R t σ c)
    (hX : HoldsOnHull c (fun b i => AnalyticAt ℂ (fun w => X w b i) z)) :
    AnalyticAt ℂ (fun w => complexGaugedContourAverage (X w) (complexBalancingGauge (X w) R) c) z := by apply _root_.YangMills.SharedProofs.p21606 <;> assumption
end Operations
theorem complexCellTermsAnalyticStatement_holds : complexCellTermsAnalyticStatement := by
  intro F S R V a hodd hamb
  refine ⟨complexTotalOverTop_eq_sum_complexCellTerms hodd a S R V, ?_⟩
  intro m W t₀ z t σ ht ht1 hσ hsm hu hu1 hmu hmu1 hgap href
  have hL1 : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  have hτ : 4 * (F.blockSide : ℝ) * t ≤ 1 / 1024 := by
    have hcount : (1 : ℝ) ≤ hullBondCount F.blockSide := by
      unfold hullBondCount
      have h1 : (1 : ℝ) ≤ (F.blockSide : ℝ) ^ 4 := one_le_pow₀ hL1
      have h2 : (0 : ℝ) ≤ (F.blockSide : ℝ) ^ 5 := by positivity
      linarith
    have h1 : t ≤ hullBondCount F.blockSide * t := le_mul_of_one_le_left ht hcount
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 8 * (F.blockSide : ℝ))
    have h3 : 0 ≤ (F.blockSide : ℝ) * t := by positivity
    linarith
  have hfield := analyticAt_complexChartField hodd R ht ht1 hσ hτ hu hu1 hmu hmu1 hgap href
  have hfield0 : ∀ b ∈ innerBonds (cellBall S z 1) 0,
      AnalyticAt ℂ (fun w => complexChartField R (W w) 0 b.1 b.2) t₀ := by
    intro b hb
    simp only [complexChartField]
    exact (analyticAt_unitExp (hu b hb) (hu1 b hb)).mul analyticAt_const
  have hplaq : ∀ p ∈ plaquettesOver S {z} 0,
      AnalyticAt ℂ (fun w => complexPlaquetteTerm (complexChartField R (W w) 0) p) t₀ := by
    intro p hp
    obtain ⟨b1, b2, b3, b4⟩ := plaquette_bonds_mem_innerBonds hamb hodd hp
    have hpath : PathBondsSatisfy (fun b i => AnalyticAt ℂ (fun w => complexChartField R (W w) 0 b i) t₀) p.1
        [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] := by
      have e3 : p.1 + unitStep 0 p.2.1 + unitStep 0 p.2.2 - unitStep 0 p.2.1 = p.1 + unitStep 0 p.2.2 := by
        abel
      have e4 : p.1 + unitStep 0 p.2.1 + unitStep 0 p.2.2 + -unitStep 0 p.2.1 - unitStep 0 p.2.2 = p.1 := by
        abel
      simp only [PathBondsSatisfy, crossedBond, stepDisplacement, if_true, Bool.false_eq_true, if_false, e3, e4,
        and_true]
      exact ⟨hfield0 (p.1, p.2.1) b1, hfield0 (p.1 + unitStep 0 p.2.1, p.2.2) b2,
        hfield0 (p.1 + unitStep 0 p.2.2, p.2.1) b3, hfield0 (p.1, p.2.2) b4⟩
    simp only [complexPlaquetteTerm, complexPlaquetteHolonomy]
    exact analyticAt_const.sub (analyticAt_trace (analyticAt_complexPathHolonomy hpath)).div_const
  have haverage : ∀ j, j < F.top → ∀ c ∈ innerBonds (cellBall S z 1) (j + 1),
      AnalyticAt ℂ (fun w => complexGaugedContourAverage (complexChartField R (W w) j)
        (complexBalancingGauge (complexChartField R (W w) j) (R j)) c) t₀ ∧
        0 < (complexGaugedContourAverage (complexChartField R (W t₀) j)
          (complexBalancingGauge (complexChartField R (W t₀) j) (R j)) c).det.re := by
    intro j hj c hc
    have hnearBonds : ∀ b ∈ innerBonds (cellBall S z 1) j,
        BondNearReal (complexChartField R (W t₀) j) (R j) t b.1 b.2 := fun b hb =>
      ⟨hgap j hj b hb, det_complexChartField_of_norm_lt_one R (W t₀) j _ _ (lt_of_le_of_lt (hgap j hj b hb) ht1)⟩
    have hhull : HoldsOnHull c (fun b i => BondNearReal (complexChartField R (W t₀) j) (R j) t b i) :=
      holdsOnHull_of_innerBonds hj hodd hc hnearBonds
    have hcontours : ContoursNearReal (complexChartField R (W t₀) j) (R j) t σ c :=
      ⟨fun h hh π => pathNearReal_axisPath _ hodd.pos (fun v hv k hk => (hhull.1 v hv k hk).1) hh π,
        fun h hh => pathNearReal_replicate _ _ _ fun r hr => hhull.2 h hh r hr,
        fun h hh π => pathNearReal_axisPath _ hodd.pos (fun v hv k hk => (hhull.1 v hv k hk).2) hh π,
        fun h hh π => href j (by omega) c hc h hh π⟩
    have hX : HoldsOnHull c (fun b i => AnalyticAt ℂ (fun w => complexChartField R (W w) j b i) t₀) :=
      holdsOnHull_of_innerBonds hj hodd hc fun b hb => hfield j hj b hb
    exact ⟨analyticAt_complexGaugedContourAverage_comp (X := fun w => complexChartField R (W w) j) hodd (R j)
        (by omega) ht hτ hcontours hX,
      (unitPart_and_sqrt_near hodd (by omega) ht hσ hτ hcontours).1⟩
  have hbond : ∀ j ∈ Finset.range F.top, ∀ c ∈ bondsOver S {z} (j + 1),
      AnalyticAt ℂ (fun w => complexBondTerm R (W w) V j c) t₀ := by
    intro j hj c hc
    have hj' := Finset.mem_range.1 hj
    have hcBall : c ∈ innerBonds (cellBall S z 1) (j + 1) :=
      mem_innerBonds_cellBall_of_mem_bondsOver hamb hodd S z (by omega) hc
    obtain ⟨hM, hre⟩ := haverage j hj' c hcBall
    have e : (fun w => complexBondTerm R (W w) V j c) = fun w =>
        complexBlockFit (complexGaugedContourAverage (complexChartField R (W w) j)
            (complexBalancingGauge (complexChartField R (W w) j) (R j)) c)
          (complexFieldChain R (W w) V (j + 1) c.1 c.2) := by
      funext w
      simp only [complexBondTerm, ComplexBondTerms.complexFieldChain_of_ne R (W w) V (k := j) (by omega), complexBalancingGauges]
    rw [e]
    refine analyticAt_complexBlockFit_comp hM (Or.inl hre) ?_
    by_cases htop : j + 1 = F.top
    · have e2 : (fun w => complexFieldChain R (W w) V (j + 1) c.1 c.2) =
          fun _ => complexFieldChain R (W t₀) V (j + 1) c.1 c.2 := by
        funext w
        rw [complexFieldChain_top_eq R V htop (W w) (W t₀)]
      rw [e2]
      exact analyticAt_const
    · have e2 : (fun w => complexFieldChain R (W w) V (j + 1) c.1 c.2) =
          fun w => complexChartField R (W w) (j + 1) c.1 c.2 := by
        funext w
        rw [ComplexBondTerms.complexFieldChain_of_ne R (W w) V htop]
      rw [e2]
      exact hfield (j + 1) (by omega) c hcBall
  simp only [complexCellTerms]
  refine (Finset.analyticAt_fun_sum _ hplaq).add (analyticAt_const.mul ?_)
  exact Finset.analyticAt_fun_sum _ fun j hj => Finset.analyticAt_fun_sum _ fun c hc => hbond j hj c hc
end YangMills.Construction.ComplexCellTerms
end
