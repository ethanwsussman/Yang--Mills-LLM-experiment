import YangMills.Construction.LawByMomentsOfTheFlow.MeanAtTheCutOfAGoodStateProof
import YangMills.Construction.LawByMomentsOfTheFlow.MomentsOfTheCompletedFormsProof
import YangMills.Construction.LawByMomentsOfTheFlow.QuadraticFormsOnCurvature
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open TorusFields WeightedResponses LevelTestFunctions
private theorem forAllParameters_and {P Q : MomentParameters → Prop} (hP : ForAllParameters P)
    (hQ : ForAllParameters Q) :
    ForAllParameters fun Λ => P Λ ∧ Q Λ := by apply _root_.YangMills.SharedProofs.p2495 <;> assumption
private theorem forAllParameters_mono {P Q : MomentParameters → Prop} (hPQ : ∀ Λ, P Λ → Q Λ)
    (hP : ForAllParameters P) : ForAllParameters Q := by apply _root_.YangMills.SharedProofs.p432 <;> assumption
private theorem forAllParameters_weightRate_pos :
    ForAllParameters fun Λ => 0 < Λ.stepParams.weightRate := by apply _root_.YangMills.SharedProofs.p57148 <;> assumption
section Torus
variable {n : ℕ} [NeZero n]
private theorem weightNorm_nonneg (L t : ℕ) {m : ℕ} (h : PlaquetteWeight m) : 0 ≤ weightNorm L t h :=
  le_max_of_le_left (Real.iSup_nonneg fun _ => abs_nonneg _)
private theorem bilinearEval_finset_sum (A : Finset (TorusSite n)) (qf : TorusSite n → BondBilinear n)
    (U U' : TorusBond n → ℝ) :
    bilinearEval (fun b b' => ∑ y ∈ A, qf y b b') U U' = ∑ y ∈ A, bilinearEval (qf y) U U' := by apply _root_.YangMills.SharedProofs.p7164 <;> assumption
private theorem colourEval_finset_sum (Ps : Finset (TorusPlaquette n)) (A : Finset (TorusSite n))
    (qf : TorusSite n → BondBilinear n)
    (k : TorusSite n → TorusPlaquette n → TorusPlaquette n → ℝ)
    (hid : ∀ y ∈ A, ∀ U U' : TorusBond n → ℝ, bilinearEval (qf y) U U' =
      ∑ p ∈ Ps, ∑ p' ∈ Ps, k y p p' * curl U p * curl U' p') (X X' : ColourForm n) :
    colourEval (fun b b' => ∑ y ∈ A, qf y b b') X X' =
      ∑ p ∈ Ps, ∑ p' ∈ Ps, (∑ y ∈ A, k y p p') * ∑ e : Fin 3, curl (X e) p * curl (X' e) p' := by
  unfold colourEval
  simp_rw [bilinearEval_finset_sum]
  rw [Finset.sum_comm]
  calc ∑ y ∈ A, ∑ e : Fin 3, bilinearEval (qf y) (X e) (X' e)
      = ∑ y ∈ A, ∑ p ∈ Ps, ∑ p' ∈ Ps, k y p p' * ∑ e : Fin 3, curl (X e) p * curl (X' e) p' := by
        refine Finset.sum_congr rfl fun y hy => ?_
        simp_rw [hid y hy]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p' _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun e _ => by ring
    _ = ∑ p ∈ Ps, ∑ y ∈ A, ∑ p' ∈ Ps, k y p p' * ∑ e : Fin 3, curl (X e) p * curl (X' e) p' :=
        Finset.sum_comm
    _ = ∑ p ∈ Ps, ∑ p' ∈ Ps, ∑ y ∈ A, k y p p' * ∑ e : Fin 3, curl (X e) p * curl (X' e) p' :=
        Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun p' _ => ?_
        rw [Finset.sum_mul]
omit [NeZero n] in
private theorem abs_kernel_sum_le (Ps : Finset (TorusPlaquette n)) (A : Finset (TorusSite n))
    (k : TorusSite n → TorusPlaquette n → TorusPlaquette n → ℝ)
    (v : TorusPlaquette n → ℝ) (hv : ∀ p, 0 ≤ v p) (B : ℝ)
    (hk : ∀ y ∈ A, ∑ p ∈ Ps, ∑ p' ∈ Ps, |k y p p'| * v p * v p' ≤ B) :
    ∑ p ∈ Ps, ∑ p' ∈ Ps, |∑ y ∈ A, k y p p'| * v p * v p' ≤ (A.card : ℝ) * B := by
  calc ∑ p ∈ Ps, ∑ p' ∈ Ps, |∑ y ∈ A, k y p p'| * v p * v p'
      ≤ ∑ p ∈ Ps, ∑ p' ∈ Ps, ∑ y ∈ A, |k y p p'| * v p * v p' := by
        refine Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun p' _ => ?_
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (hv p)) (hv p')
    _ = ∑ p ∈ Ps, ∑ y ∈ A, ∑ p' ∈ Ps, |k y p p'| * v p * v p' :=
        Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ = ∑ y ∈ A, ∑ p ∈ Ps, ∑ p' ∈ Ps, |k y p p'| * v p * v p' := Finset.sum_comm
    _ ≤ ∑ _y ∈ A, B := Finset.sum_le_sum hk
    _ = (A.card : ℝ) * B := by rw [Finset.sum_const, nsmul_eq_mul]
omit [NeZero n] in
private theorem measurable_curl (p : TorusPlaquette n) (e : Fin 3) :
    Measurable fun X : ColourForm n => curl (X e) p := by
  unfold curl
  fun_prop
omit [NeZero n] in
private theorem measurable_curlNorm (p : TorusPlaquette n) :
    Measurable fun X : ColourForm n => curlNorm X p := by
  unfold curlNorm
  exact Real.continuous_sqrt.measurable.comp
    (Finset.measurable_fun_sum _ fun e _ => (measurable_curl p e).pow_const 2)
omit [NeZero n] in
private theorem abs_colour_pair_le (X X' : ColourForm n) (p p' : TorusPlaquette n) :
    |∑ e : Fin 3, curl (X e) p * curl (X' e) p'| ≤ curlNorm X p * curlNorm X' p' := by
  unfold curlNorm
  rw [← Real.sqrt_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  exact Real.abs_le_sqrt (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
private theorem holderTriple_double {q : ℝ} (hq : 1 ≤ q) :
    ENNReal.HolderTriple (ENNReal.ofReal (2 * q)) (ENNReal.ofReal (2 * q)) (ENNReal.ofReal q) := by
  have h0 : 0 < q := by linarith
  refine ⟨?_⟩
  rw [← ENNReal.ofReal_inv_of_pos (by linarith : 0 < 2 * q), ← ENNReal.ofReal_inv_of_pos h0,
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  field_simp
  norm_num
omit [NeZero n] in
private theorem eLpNorm_kernel_term_le {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (X X' : Ω → ColourForm n) (hX : Measurable X) (hX' : Measurable X') {q : ℝ} (hq : 1 ≤ q)
    (p p' : TorusPlaquette n) (c : ℝ) :
    eLpNorm (fun w => c * ∑ e : Fin 3, curl (X w e) p * curl (X' w e) p') (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal |c| * (eLpNorm (fun w => curlNorm (X w) p) (ENNReal.ofReal (2 * q)) μ *
        eLpNorm (fun w => curlNorm (X' w) p') (ENNReal.ofReal (2 * q)) μ) := by
  have := holderTriple_double hq
  have ha : AEStronglyMeasurable (fun w => curlNorm (X w) p) μ :=
    ((measurable_curlNorm p).comp hX).aestronglyMeasurable
  have hb : AEStronglyMeasurable (fun w => curlNorm (X' w) p') μ :=
    ((measurable_curlNorm p').comp hX').aestronglyMeasurable
  have h1 : eLpNorm (fun w => c * ∑ e : Fin 3, curl (X w e) p * curl (X' w e) p') (ENNReal.ofReal q) μ ≤
      eLpNorm (c • ((fun w => curlNorm (X w) p) • fun w => curlNorm (X' w) p')) (ENNReal.ofReal q) μ := by
    refine eLpNorm_mono fun w => ?_
    have hab : 0 ≤ curlNorm (X w) p * curlNorm (X' w) p' :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have h2 := abs_colour_pair_le (X w) (X' w) p p'
    show ‖c * ∑ e : Fin 3, curl (X w e) p * curl (X' w e) p'‖ ≤
      ‖c * (curlNorm (X w) p * curlNorm (X' w) p')‖
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul c, abs_of_nonneg hab]
    exact mul_le_mul_of_nonneg_left h2 (abs_nonneg c)
  refine h1.trans (eLpNorm_const_smul_le.trans ?_)
  rw [Real.enorm_eq_ofReal_abs]
  gcongr
  exact eLpNorm_smul_le_mul_eLpNorm hb ha
private theorem eLpNorm_colourEval_le_of_kernel (Qf : BondBilinear n)
    (κ : TorusPlaquette n → TorusPlaquette n → ℝ) (ω : TorusPlaquette n → ℝ) (hω : ∀ p, 0 < ω p) (B : ℝ)
    (hid : ∀ X X' : ColourForm n, colourEval Qf X X' =
      ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)),
        ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)),
          κ p p' * ∑ e : Fin 3, curl (X e) p * curl (X' e) p')
    (hB : ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)),
      ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)),
        |κ p p'| * (ω p)⁻¹ * (ω p')⁻¹ ≤ B)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (X X' : Ω → ColourForm n) {q : ℝ} (hq : 1 ≤ q)
    (hX : Measurable X) (hX' : Measurable X') :
    eLpNorm (fun w => colourEval Qf (X w) (X' w)) (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal B * weightedCurvatureNorm μ ω (ENNReal.ofReal (2 * q)) X *
        weightedCurvatureNorm μ ω (ENNReal.ofReal (2 * q)) X' := by
  have hpt : ∀ (Y : Ω → ColourForm n) (p : TorusPlaquette n),
      p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)) →
      eLpNorm (fun w => curlNorm (Y w) p) (ENNReal.ofReal (2 * q)) μ ≤
        ENNReal.ofReal (ω p)⁻¹ * weightedCurvatureNorm μ ω (ENNReal.ofReal (2 * q)) Y := by
    intro Y p hp
    have hord : p.2.1 < p.2.2 := (Finset.mem_filter.1 hp).2.1
    have h1 : ENNReal.ofReal (ω p) * eLpNorm (fun w => curlNorm (Y w) p) (ENNReal.ofReal (2 * q)) μ ≤
        weightedCurvatureNorm μ ω (ENNReal.ofReal (2 * q)) Y :=
      le_iSup (fun p : OrientedPlaquette n => ENNReal.ofReal (ω p.1) *
        eLpNorm (fun e => curlNorm (Y e) p.1) (ENNReal.ofReal (2 * q)) μ) ⟨p, hord⟩
    calc eLpNorm (fun w => curlNorm (Y w) p) (ENNReal.ofReal (2 * q)) μ
        = ENNReal.ofReal (ω p)⁻¹ * (ENNReal.ofReal (ω p) *
            eLpNorm (fun w => curlNorm (Y w) p) (ENNReal.ofReal (2 * q)) μ) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 (hω p).le), inv_mul_cancel₀ (hω p).ne',
            ENNReal.ofReal_one, one_mul]
      _ ≤ _ := by gcongr
  have hsum : (fun w => colourEval Qf (X w) (X' w)) =
      ∑ pp ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)) ×ˢ
          plaquettesIn (Finset.univ : Finset (TorusSite n)),
        fun w => κ pp.1 pp.2 * ∑ e : Fin 3, curl (X w e) pp.1 * curl (X' w e) pp.2 := by
    funext w
    rw [hid, Finset.sum_apply, Finset.sum_product]
  have hq1 : (1 : ENNReal) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hq
  rw [hsum]
  refine (eLpNorm_sum_le (fun pp _ => ?_) hq1).trans ?_
  · have hm : Measurable fun w => κ pp.1 pp.2 * ∑ e : Fin 3, curl (X w e) pp.1 * curl (X' w e) pp.2 :=
      measurable_const.mul (Finset.measurable_fun_sum _ fun e _ =>
        ((measurable_curl pp.1 e).comp hX).mul ((measurable_curl pp.2 e).comp hX'))
    exact hm.aestronglyMeasurable
  · set N := weightedCurvatureNorm μ ω (ENNReal.ofReal (2 * q)) X
    set N' := weightedCurvatureNorm μ ω (ENNReal.ofReal (2 * q)) X'
    have hnn : ∀ pp : TorusPlaquette n × TorusPlaquette n,
        0 ≤ |κ pp.1 pp.2| * (ω pp.1)⁻¹ * (ω pp.2)⁻¹ := fun pp =>
      mul_nonneg (mul_nonneg (abs_nonneg _) (inv_nonneg.2 (hω _).le)) (inv_nonneg.2 (hω _).le)
    calc _ ≤ ∑ pp ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)) ×ˢ
              plaquettesIn (Finset.univ : Finset (TorusSite n)),
            ENNReal.ofReal (|κ pp.1 pp.2| * (ω pp.1)⁻¹ * (ω pp.2)⁻¹) * N * N' := by
          refine Finset.sum_le_sum fun pp hpp => ?_
          obtain ⟨h1, h2⟩ := Finset.mem_product.1 hpp
          refine (eLpNorm_kernel_term_le μ X X' hX hX' hq pp.1 pp.2 _).trans ?_
          have e1 : ENNReal.ofReal (|κ pp.1 pp.2| * (ω pp.1)⁻¹ * (ω pp.2)⁻¹) * N * N' =
              ENNReal.ofReal |κ pp.1 pp.2| *
                ((ENNReal.ofReal (ω pp.1)⁻¹ * N) * (ENNReal.ofReal (ω pp.2)⁻¹ * N')) := by
            rw [ENNReal.ofReal_mul (mul_nonneg (abs_nonneg _) (inv_nonneg.2 (hω _).le)),
              ENNReal.ofReal_mul (abs_nonneg _)]
            ring
          rw [e1]
          gcongr
          · exact hpt X pp.1 h1
          · exact hpt X' pp.2 h2
      _ = ENNReal.ofReal (∑ pp ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)) ×ˢ
              plaquettesIn (Finset.univ : Finset (TorusSite n)),
            |κ pp.1 pp.2| * (ω pp.1)⁻¹ * (ω pp.2)⁻¹) * N * N' := by
          rw [ENNReal.ofReal_sum_of_nonneg fun pp _ => hnn pp, Finset.sum_mul, Finset.sum_mul]
      _ ≤ ENNReal.ofReal B * N * N' := by
          rw [Finset.sum_product]
          gcongr
end Torus
private theorem natAbs_coord_sub_round_le {k : ℕ} (P : LevelData k) (L u : ℕ) [NeZero L]
    (hu : u ≤ P.windowLevel) (y : TorusSite (P.sideAt L u)) (b : ℕ)
    (hy : P.distFromCenter L u y ≤ b) (a : Fin 4) :
    ((y a - ((round (P.center a * (L : ℝ) ^ P.windowLevel / (L : ℝ) ^ u) : ℤ) :
      ZMod (P.sideAt L u))).valMinAbs).natAbs ≤ b := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hterm : |circleRep (P.period L) (((y a).val : ℝ) * (L : ℝ) ^ u / (L : ℝ) ^ P.windowLevel - P.center a)| *
      (L : ℝ) ^ P.windowLevel / (L : ℝ) ^ u ≤ b :=
    (le_ciSup (f := fun a : Fin 4 => |circleRep (P.period L)
      (((y a).val : ℝ) * (L : ℝ) ^ u / (L : ℝ) ^ P.windowLevel - P.center a)| *
      (L : ℝ) ^ P.windowLevel / (L : ℝ) ^ u) (Set.finite_range _).bddAbove a).trans hy
  have hKu : (L : ℝ) ^ P.windowLevel = (L : ℝ) ^ u * (L : ℝ) ^ (P.windowLevel - u) := by
    rw [← pow_add]
    congr 1
    omega
  obtain ⟨Lq, hLq⟩ : ∃ Lq : ℝ, Lq = (L : ℝ) ^ (P.windowLevel - u) := ⟨_, rfl⟩
  have hLq0 : 0 < Lq := by
    rw [hLq]
    positivity
  have hq : (L : ℝ) ^ P.windowLevel / (L : ℝ) ^ u = Lq := by
    rw [hKu, hLq]
    field_simp
  have hside : ((P.sideAt L u : ℕ) : ℝ) = (P.period L : ℝ) * Lq := by
    rw [hLq]
    simp [LevelData.sideAt]
  obtain ⟨ξ, hξ⟩ : ∃ ξ : ℝ, ξ = P.center a * (L : ℝ) ^ P.windowLevel / (L : ℝ) ^ u := ⟨_, rfl⟩
  have hξ' : ξ = P.center a * Lq := by
    rw [hξ, mul_div_assoc, hq]
  rw [← hξ]
  obtain ⟨V, hV⟩ : ∃ V : ℝ,
      V = ((y a).val : ℝ) * (L : ℝ) ^ u / (L : ℝ) ^ P.windowLevel - P.center a := ⟨_, rfl⟩
  rw [← hV] at hterm
  obtain ⟨R, hR⟩ : ∃ R : ℤ, R = round (V / (P.period L : ℝ)) := ⟨_, rfl⟩
  have hw : |circleRep (P.period L) V * Lq| ≤ b := by
    rw [abs_mul, abs_of_pos hLq0]
    rw [mul_div_assoc, hq] at hterm
    exact hterm
  have hval : circleRep (P.period L) V * Lq = ((y a).val : ℝ) - ξ - ((P.sideAt L u : ℕ) : ℝ) * R := by
    unfold circleRep
    rw [← hR, hside, hξ', hV, hKu, hLq]
    field_simp
  obtain ⟨z, hz⟩ : ∃ z : ℤ, z = ((y a).val : ℤ) - round ξ - ((P.sideAt L u : ℕ) : ℤ) * R := ⟨_, rfl⟩
  have hzr : (z : ℝ) = circleRep (P.period L) V * Lq + (ξ - round ξ) := by
    rw [hval, hz]
    push_cast
    ring
  have hzb : |(z : ℝ)| ≤ b + 1 / 2 := by
    rw [hzr]
    exact (abs_add_le _ _).trans (add_le_add hw (abs_sub_round ξ))
  have hzn : z.natAbs ≤ b := by
    have h1 : ((z.natAbs : ℕ) : ℝ) = |(z : ℝ)| := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    have h2 : ((z.natAbs : ℕ) : ℝ) < (b : ℝ) + 1 := by
      rw [h1]
      linarith
    have h3 : z.natAbs < b + 1 := by exact_mod_cast h2
    omega
  have hcast : ((z : ℤ) : ZMod (P.sideAt L u)) = y a - ((round ξ : ℤ) : ZMod (P.sideAt L u)) := by
    rw [hz]
    push_cast
    simp
  rw [← hcast]
  exact (natAbs_valMinAbs_intCast_le z).trans hzn
open Classical in
private theorem lastSeparated_le {Λ : MomentParameters} (S : MomentPoint Λ) :
    S.lastSeparated ≤ S.data.scaleLevel := by apply _root_.YangMills.SharedProofs.p10799 <;> assumption
private theorem supportForm_kernel_at {Λ : MomentParameters} (S : MomentPoint Λ) (i : Fin Λ.k)
    (hr : 0 < Λ.stepParams.weightRate) (cf cs sz : ℝ) (hsz0 : 0 < sz)
    (k : TorusSite (S.levelSide S.lastSeparated) → TorusPlaquette (S.levelSide S.lastSeparated) →
      TorusPlaquette (S.levelSide S.lastSeparated) → ℝ)
    (hkid : ∀ (y : TorusSite (S.levelSide S.lastSeparated)) (X X' : TorusBond (S.levelSide S.lastSeparated) → ℝ),
      bilinearEval (classicalQuadratic S.tower S.resp S.lastSeparated (S.levelSide S.lastSeparated)
          (S.weight i _) y) X X' =
        ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (S.levelSide S.lastSeparated))),
          ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite (S.levelSide S.lastSeparated))),
            k y p p' * curl X p * curl X' p')
    (hkb : ∀ y : TorusSite (S.levelSide S.lastSeparated),
      ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (S.levelSide S.lastSeparated))),
        ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite (S.levelSide S.lastSeparated))), |k y p p'| *
          Real.exp (Λ.stepParams.weightRate / 8 * ((TorusFields.supDist p.1 y : ℝ) + (TorusFields.supDist p'.1 y : ℝ))) ≤ cf * sz)
    (hcard : ((S.supportAt S.lastSeparated (S.levelSide S.lastSeparated) i).card : ℝ) ≤
      cs * (S.range : ℝ) ^ 4)
    (hnear : ∀ y ∈ S.supportAt S.lastSeparated (S.levelSide S.lastSeparated) i,
      TorusFields.supDist y (S.originSite S.lastSeparated (S.levelSide S.lastSeparated)) ≤ S.radius) :
    ∃ κ : TorusPlaquette (S.levelSide S.lastSeparated) → TorusPlaquette (S.levelSide S.lastSeparated) → ℝ,
      (∀ X X' : ColourForm (S.levelSide S.lastSeparated),
        colourEval (S.supportForm S.lastSeparated (S.levelSide S.lastSeparated) i) X X' =
          ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (S.levelSide S.lastSeparated))),
            ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite (S.levelSide S.lastSeparated))),
              κ p p' * ∑ e : Fin 3, curl (X e) p * curl (X' e) p') ∧
      ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (S.levelSide S.lastSeparated))),
        ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite (S.levelSide S.lastSeparated))),
          |κ p p'| * (S.distanceWeight S.lastSeparated (S.levelSide S.lastSeparated) p)⁻¹ *
            (S.distanceWeight S.lastSeparated (S.levelSide S.lastSeparated) p')⁻¹ ≤
          |cs| * (|cf| * sz) * (S.range : ℝ) ^ 4 ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (X X' : Ω → ColourForm (S.levelSide S.lastSeparated))
        (q : ℝ), 1 ≤ q → Measurable X → Measurable X' →
        eLpNorm (fun e => colourEval (S.supportForm S.lastSeparated (S.levelSide S.lastSeparated) i)
            (X e) (X' e)) (ENNReal.ofReal q) μ ≤
          ENNReal.ofReal (|cs| * (|cf| * sz) * (S.range : ℝ) ^ 4) *
            weightedCurvatureNorm μ (S.distanceWeight S.lastSeparated (S.levelSide S.lastSeparated))
              (ENNReal.ofReal (2 * q)) X *
            weightedCurvatureNorm μ (S.distanceWeight S.lastSeparated (S.levelSide S.lastSeparated))
              (ENNReal.ofReal (2 * q)) X' := by
  have hω : ∀ p, 0 < S.distanceWeight S.lastSeparated (S.levelSide S.lastSeparated) p :=
    fun p => Real.exp_pos _
  have hc : 0 ≤ Λ.stepParams.weightRate / 8 := by
    have := hr.le
    positivity
  have hinv : ∀ y ∈ S.supportAt S.lastSeparated (S.levelSide S.lastSeparated) i,
      ∀ p : TorusPlaquette (S.levelSide S.lastSeparated),
      (S.distanceWeight S.lastSeparated (S.levelSide S.lastSeparated) p)⁻¹ ≤
        Real.exp (Λ.stepParams.weightRate / 8 * (TorusFields.supDist p.1 y : ℝ)) := by
    intro y hy p
    unfold MomentPoint.distanceWeight
    rw [← Real.exp_neg, neg_neg]
    refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (max_le (Nat.cast_nonneg _) ?_) hc)
    have h1 := supDist_triangle p.1 y (S.originSite S.lastSeparated (S.levelSide S.lastSeparated))
    have h2 := hnear y hy
    have h3 : (TorusFields.supDist p.1 (S.originSite S.lastSeparated (S.levelSide S.lastSeparated)) : ℝ) ≤
        (TorusFields.supDist p.1 y : ℝ) + (S.radius : ℝ) := by
      exact_mod_cast h1.trans (Nat.add_le_add_left h2 _)
    linarith
  have hone : ∀ y ∈ S.supportAt S.lastSeparated (S.levelSide S.lastSeparated) i,
      ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (S.levelSide S.lastSeparated))),
        ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite (S.levelSide S.lastSeparated))),
          |k y p p'| * (S.distanceWeight S.lastSeparated (S.levelSide S.lastSeparated) p)⁻¹ *
            (S.distanceWeight S.lastSeparated (S.levelSide S.lastSeparated) p')⁻¹ ≤ cf * sz := by
    intro y hy
    refine le_trans (Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun p' _ => ?_) (hkb y)
    rw [mul_add, Real.exp_add, ← mul_assoc]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hinv y hy p) (abs_nonneg _)) (hinv y hy p')
      (inv_nonneg.2 (hω p').le) (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)
  have hB : ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (S.levelSide S.lastSeparated))),
      ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite (S.levelSide S.lastSeparated))),
        |∑ y ∈ S.supportAt S.lastSeparated (S.levelSide S.lastSeparated) i, k y p p'| *
          (S.distanceWeight S.lastSeparated (S.levelSide S.lastSeparated) p)⁻¹ *
          (S.distanceWeight S.lastSeparated (S.levelSide S.lastSeparated) p')⁻¹ ≤
        |cs| * (|cf| * sz) * (S.range : ℝ) ^ 4 := by
    refine (abs_kernel_sum_le _ _ k
      (fun p => (S.distanceWeight S.lastSeparated (S.levelSide S.lastSeparated) p)⁻¹)
      (fun p => (inv_pos.2 (hω p)).le) _ hone).trans ?_
    have hr4 : (0 : ℝ) ≤ (S.range : ℝ) ^ 4 := by positivity
    have hb : 0 ≤ |cf| * sz := mul_nonneg (abs_nonneg _) hsz0.le
    calc ((S.supportAt S.lastSeparated (S.levelSide S.lastSeparated) i).card : ℝ) * (cf * sz)
        ≤ ((S.supportAt S.lastSeparated (S.levelSide S.lastSeparated) i).card : ℝ) * (|cf| * sz) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self _) hsz0.le) (Nat.cast_nonneg _)
      _ ≤ (|cs| * (S.range : ℝ) ^ 4) * (|cf| * sz) :=
          mul_le_mul_of_nonneg_right (hcard.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hr4)) hb
      _ = _ := by ring
  have hid : ∀ X X' : ColourForm (S.levelSide S.lastSeparated),
      colourEval (S.supportForm S.lastSeparated (S.levelSide S.lastSeparated) i) X X' =
        ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (S.levelSide S.lastSeparated))),
          ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite (S.levelSide S.lastSeparated))),
            (∑ y ∈ S.supportAt S.lastSeparated (S.levelSide S.lastSeparated) i, k y p p') *
              ∑ e : Fin 3, curl (X e) p * curl (X' e) p' :=
    fun X X' => colourEval_finset_sum _ (S.supportAt S.lastSeparated (S.levelSide S.lastSeparated) i)
      (fun y => classicalQuadratic S.tower S.resp S.lastSeparated (S.levelSide S.lastSeparated)
        (S.weight i _) y) k (fun y _ U U' => hkid y U U') X X'
  exact ⟨fun p p' => ∑ y ∈ S.supportAt S.lastSeparated (S.levelSide S.lastSeparated) i, k y p p', hid, hB,
    fun Ω _ μ X X' q hq1 hX hX' => eLpNorm_colourEval_le_of_kernel _ _ _ hω _ hid hB μ X X' hq1 hX hX'⟩
theorem supportFormCurvatureKernel_proof (hF : formsReadCurvatureStatement)
    (hK : classicalFormsAnnihilateClosedStatement) (hT : thirdDerivativeBoundsStatement)
    (hW : weightsSitesBelowScaleStatement) (hS : farLevelSupportSitesStatement) :
    supportFormCurvatureKernelStatement := by
  unfold formsReadCurvatureStatement ForAllPoints at hF
  unfold classicalFormsAnnihilateClosedStatement ForAllPoints at hK
  unfold thirdDerivativeBoundsStatement ForAllPoints at hT
  unfold weightsSitesBelowScaleStatement ForAllPoints at hW
  unfold farLevelSupportSitesStatement ForAllPoints at hS
  unfold supportFormCurvatureKernelStatement ForAllPoints
  refine forAllParameters_mono ?_ (forAllParameters_and forAllParameters_weightRate_pos
    (forAllParameters_and hF (forAllParameters_and hK (forAllParameters_and hT (forAllParameters_and hW hS)))))
  rintro Λ ⟨hr, ⟨CF, _, XF, _, _, fF⟩, ⟨CK, _, XK, _, _, fK⟩, ⟨CT, _, XT, _, _, fT⟩, ⟨CW, _, XW, _, _, fW⟩,
    ⟨CS, _, XS, _, _, fS⟩⟩
  obtain ⟨sz, hszd⟩ : ∃ sz : ℝ, sz = |CT 1| + 1 := ⟨_, rfl⟩
  have hsz0 : 0 < sz := by
    rw [hszd]
    positivity
  refine ⟨fun _ => |CS 0| * (|CF 0| * sz), 1, Λ.floor, one_pos, le_rfl, fun S i => ?_⟩
  have hts : S.lastSeparated ≤ S.data.scaleLevel := lastSeparated_le S
  have htK : S.lastSeparated ≤ S.data.windowLevel := hts.trans S.supAdmissible.scaleLevel_le
  have hlev : (S.tower.stage S.lastSeparated).depth = S.lastSeparated :=
    (congrArg (fun z : ResponseInTheExpansion.StageWithResponse Λ.stepParams => z.1.depth)
      (S.stage_eq S.lastSeparated htK)).trans (S.onFlow S.lastSeparated htK).depth_eq
  have hL0 : 0 < Λ.stepParams.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hn₀ : Λ.stepParams.n₀ ≤ S.levelSide S.lastSeparated := by
    have h1 : Λ.stepParams.side * Λ.stepParams.n₀ ≤ S.data.period Λ.stepParams.side := S.side_le
    have h2 : Λ.stepParams.n₀ ≤ Λ.stepParams.side * Λ.stepParams.n₀ := Nat.le_mul_of_pos_left _ hL0
    have h3 : S.data.period Λ.stepParams.side ≤ S.levelSide S.lastSeparated :=
      Nat.le_mul_of_pos_right _ (pow_pos hL0 _)
    omega
  have hsize : weightNorm Λ.stepParams.side (S.tower.stage S.lastSeparated).depth
      (S.weight i (fineSide Λ.stepParams.side (S.tower.stage S.lastSeparated).depth
        (S.levelSide S.lastSeparated))) ≤ 1 := by
    have h0 := ((fW S) S.lastSeparated hts i).1
    rw [hlev]
    exact h0
  have hq : ∀ y : TorusSite (S.levelSide S.lastSeparated), IsDecayingAbout Λ.stepParams sz y
      (classicalQuadratic S.tower S.resp S.lastSeparated (S.levelSide S.lastSeparated) (S.weight i _) y) := by
    intro y b b'
    have h1 := ((fT S) S.lastSeparated htK (S.levelSide S.lastSeparated) hn₀ y (S.weight i _)).2 b b'
    refine h1.trans ?_
    have hw : 0 < Λ.stepParams.weight (tripleDiam y b b') :=
      mul_pos (lt_max_of_lt_left one_pos) (Real.exp_pos _)
    refine div_le_div_of_nonneg_right ?_ hw.le
    have hs0 := weightNorm_nonneg Λ.stepParams.side (S.tower.stage S.lastSeparated).depth
      (S.weight i (fineSide Λ.stepParams.side (S.tower.stage S.lastSeparated).depth
        (S.levelSide S.lastSeparated)))
    calc CT 1 * weightNorm Λ.stepParams.side (S.tower.stage S.lastSeparated).depth
          (S.weight i (fineSide Λ.stepParams.side (S.tower.stage S.lastSeparated).depth
            (S.levelSide S.lastSeparated)))
        ≤ |CT 1| * weightNorm Λ.stepParams.side (S.tower.stage S.lastSeparated).depth
          (S.weight i (fineSide Λ.stepParams.side (S.tower.stage S.lastSeparated).depth
            (S.levelSide S.lastSeparated))) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hs0
      _ ≤ |CT 1| * 1 := mul_le_mul_of_nonneg_left hsize (abs_nonneg _)
      _ ≤ sz := by
          rw [hszd]
          linarith
  have hk : ∀ y : TorusSite (S.levelSide S.lastSeparated),
      ∃ κ : TorusPlaquette (S.levelSide S.lastSeparated) → TorusPlaquette (S.levelSide S.lastSeparated) → ℝ,
      (∀ X X' : TorusBond (S.levelSide S.lastSeparated) → ℝ,
        bilinearEval (classicalQuadratic S.tower S.resp S.lastSeparated (S.levelSide S.lastSeparated)
          (S.weight i _) y) X X' =
        ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (S.levelSide S.lastSeparated))),
          ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite (S.levelSide S.lastSeparated))),
            κ p p' * curl X p * curl X' p') ∧
      ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (S.levelSide S.lastSeparated))),
        ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite (S.levelSide S.lastSeparated))), |κ p p'| *
          Real.exp (Λ.stepParams.weightRate / 8 * ((TorusFields.supDist p.1 y : ℝ) + (TorusFields.supDist p'.1 y : ℝ))) ≤
          CF 0 * sz := fun y =>
    ((fF S) S.lastSeparated htK (S.levelSide S.lastSeparated) rfl y sz _ hsz0 (hq y)).1
      ((fK S) S.lastSeparated htK (S.levelSide S.lastSeparated) hn₀ y (S.weight i _)).2.1
  choose k hkid hkb using hk
  have hnear : ∀ y ∈ S.supportAt S.lastSeparated (S.levelSide S.lastSeparated) i,
      TorusFields.supDist y (S.originSite S.lastSeparated (S.levelSide S.lastSeparated)) ≤ S.radius := by
    intro y hy
    have h1 : S.data.distFromCenter Λ.stepParams.side S.lastSeparated y ≤ S.radius :=
      (fS S).2.2 S.lastSeparated le_rfl htK i y hy
    rw [supDist_le_iff]
    exact fun a => natAbs_coord_sub_round_le S.data Λ.stepParams.side S.lastSeparated htK y S.radius h1 a
  exact supportForm_kernel_at S i hr (CF 0) (CS 0) sz hsz0 k hkid hkb ((fS S).1 i) hnear
end YangMills.Construction.MomentLaw
end
