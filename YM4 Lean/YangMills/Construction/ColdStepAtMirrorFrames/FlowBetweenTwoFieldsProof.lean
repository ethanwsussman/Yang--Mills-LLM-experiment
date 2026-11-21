import YangMills.Construction.ColdStepAtMirrorFrames.FlowBetweenTwoFields
import YangMills.Construction.ColdStepAtMirrorFrames.HolonomyIsLipschitz
import YangMills.Construction.ColdStepAtMirrorFrames.LogarithmOfANearElement
import YangMills.Construction.ColdStepAtMirrorFrames.SumAgainstThreeFlatResponses
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
open BlockOffsets
theorem flowBetweenFields_of_logNearOne (hlog : LogNearOne) (hHol : PathHolonomyLipschitz) :
    FlowBetweenFields := by
  intro F F' T W W' y y' R ε s σ hT hper hper' hε hε1 hW hsσ hgap
  classical
  have hne : ∀ i, NeZero (F.period F.depth i) := fun i => ⟨by have := hper i; omega⟩
  set logOf : UnitQuaternion → imaginaryQuaternions := fun e => if h : _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne e ≤ 1 then (hlog e h).choose else 0 with hlogOf
  have hlogOf1 : ∀ e, _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne e ≤ 1 → expUnit (logOf e) = e ∧ ‖logOf e‖ ≤ 2 * _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne e := by
    intro e he
    simp only [hlogOf, dif_pos he]
    exact (hlog e he).choose_spec
  have hback : ∀ x : F.Site F.depth, y + siteOfCoords F.depth (siteOffset y x) = x := by
    intro x
    funext i
    have e : ((((x - y) i).valMinAbs : ℤ) : ZMod (F.period F.depth i)) = (x - y) i := ZMod.coe_valMinAbs _
    show y i + ((((x - y) i).valMinAbs : ℤ) : ZMod (F.period F.depth i)) = x i
    rw [e]
    simp
  have hoff : ∀ g : Fin 4 → ℤ, WithinRadius R g → siteOffset y (y + siteOfCoords F.depth g) = g := by
    intro g hg
    funext i
    unfold siteOffset
    rw [add_sub_cancel_left]
    refine valMinAbs_intCast_of_small (Or.inr ?_)
    have h1 := hg i
    have h2 := hper i
    have h3 : (2 * (R : ℤ) + 2) < (F.period F.depth i : ℤ) := by exact_mod_cast h2
    linarith
  set B : F.Site F.depth → Fin 4 → imaginaryQuaternions := fun x i =>
    if WithinRadius R (siteOffset y x) then logOf (W' (y' + siteOfCoords F'.depth (siteOffset y x)) i * (W x i)⁻¹) else 0 with hBdef
  have hdist : ∀ (x : F.Site F.depth) (i : Fin 4), WithinRadius R (siteOffset y x) →
      _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne (W' (y' + siteOfCoords F'.depth (siteOffset y x)) i * (W x i)⁻¹) ≤ ε := by
    intro x i hx
    have h := hgap _ i hx
    rwa [hback] at h
  have hB : ∀ x i, ‖B x i‖ ≤ 2 * ε := by
    intro x i
    simp only [hBdef]
    split_ifs with hx
    · have h1 := hdist x i hx
      exact (hlogOf1 _ (h1.trans hε1)).2.trans (by linarith)
    · simp
      linarith
  refine ⟨B, fun u hu0 hu1 => ?_, ⟨hper, hper', fun b hb => ?_⟩, ?_⟩
  · intro p hp
    have hclose : ∀ x i, ‖((expFlow B W u x i : UnitQuaternion) : ℍ[ℝ]) - ((W x i : UnitQuaternion) : ℍ[ℝ])‖ ≤ 2 * ε := by
      intro x i
      have e : ((expFlow B W u x i : UnitQuaternion) : ℍ[ℝ]) - ((W x i : UnitQuaternion) : ℍ[ℝ]) =
          (((expUnit (u • B x i) : UnitQuaternion) : ℍ[ℝ]) - 1) * ((W x i : UnitQuaternion) : ℍ[ℝ]) := by
        simp only [expFlow, leftTranslate, Submonoid.coe_mul, sub_mul, one_mul]
      rw [e, norm_mul, _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.norm_coe_unitQuaternion, mul_one]
      have h1 : _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne (expUnit (u • B x i)) ≤ ‖u • B x i‖ := distFromOne_expUnit_le _
      have h2 : ‖u • B x i‖ ≤ 2 * ε := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hu0]
        have := hB x i
        have h3 : 0 ≤ ‖B x i‖ := norm_nonneg _
        nlinarith
      exact h1.trans h2
    have hh := hHol F F.depth (expFlow B W u) W (2 * ε) hclose p.1 [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)]
    have hc := hW p hp
    have e1 : plaquetteDefect (expFlow B W u) p ≤
        ‖((pathHolonomy (expFlow B W u) p.1 [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] : UnitQuaternion) : ℍ[ℝ]) -
          ((pathHolonomy W p.1 [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] : UnitQuaternion) : ℍ[ℝ])‖ + plaquetteDefect W p := by
      unfold plaquetteDefect plaquetteHolonomy
      exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    simp only [List.length_cons, List.length_nil] at hh
    push_cast at hh
    linarith
  · have h1 := hb.1
    have e := hoff b.1 h1
    have hg := hgap b.1 b.2 h1
    simp only [expFlow, leftTranslate, one_smul, hBdef]
    rw [e, if_pos h1, (hlogOf1 _ (hg.trans hε1)).1]
    group
  · set S : Finset ((Fin 4 → ℤ) × Fin 4) := (Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(R : ℤ)) R) ×ˢ Finset.univ with hS
    have hcard : (S.card : ℝ) = 4 * (2 * (R : ℝ) + 1) ^ 4 := by
      have h1 : (Finset.Icc (-(R : ℤ)) R).card = 2 * R + 1 := by
        rw [Int.card_Icc]
        omega
      rw [hS, Finset.card_product, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin, h1]
      push_cast
      ring
    set ι : (Fin 4 → ℤ) × Fin 4 → F.Site F.depth × Fin 4 := fun p => (y + siteOfCoords F.depth p.1, p.2) with hι
    have hsub : T.filter (fun b => WithinRadius R (siteOffset y b.1)) ⊆ S.image ι := by
      intro b hb
      have h1 := (Finset.mem_filter.1 hb).2
      refine Finset.mem_image.2 ⟨(siteOffset y b.1, b.2), ?_, ?_⟩
      · refine Finset.mem_product.2 ⟨Fintype.mem_piFinset.2 fun i => ?_, Finset.mem_univ _⟩
        exact Finset.mem_Icc.2 (abs_le.1 (h1 i))
      · exact Prod.ext (hback _) rfl
    have e : ∑ b ∈ T, ‖B b.1 b.2‖ = ∑ b ∈ T.filter (fun b => WithinRadius R (siteOffset y b.1)), ‖B b.1 b.2‖ := by
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) fun b hb hb' => ?_
      have hn : ¬ WithinRadius R (siteOffset y b.1) := fun h => hb' (Finset.mem_filter.2 ⟨hb, h⟩)
      simp [hBdef, if_neg hn]
    rw [e]
    have h2 := Finset.sum_le_card_nsmul (T.filter (fun b => WithinRadius R (siteOffset y b.1))) (fun b => ‖B b.1 b.2‖) (2 * ε)
      (fun b _ => hB _ _)
    refine h2.trans ?_
    rw [nsmul_eq_mul]
    have h3 : ((T.filter (fun b => WithinRadius R (siteOffset y b.1))).card : ℝ) ≤ S.card := by
      exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_image_le
    rw [← hcard]
    exact mul_le_mul_of_nonneg_right h3 (by linarith)
end YangMills.Construction.ColdStepAtMirrorFrames
end
