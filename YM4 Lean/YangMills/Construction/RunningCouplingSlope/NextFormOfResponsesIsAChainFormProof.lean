import YangMills.Construction.ColdStepAtMirrorFrames.BlockEnergyOnTwoToriProof
import YangMills.Construction.ClusterExpansionOfAStep.ImageStateKeepsTranslationsProof
import YangMills.Construction.ClusterExpansionOfAStep.OffsetsOfABlock
import YangMills.Construction.ClusterExpansionOfAStep.OffsetsOfAContour
import YangMills.Construction.RunningCouplingSlope.CurlOfTheMeanOverContoursProof
import YangMills.Construction.RunningCouplingSlope.NextFormOfResponsesIsAChainForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.RunningCouplingSlope
open BlockAverages (PathStep centredCube bondContour axisPath reversePath)
open FlatPairing (stepDisplacement)
open LatticeFractionalIntegration (basisVector)
open TorusFields (TorusSite TorusBond unitStep siteOfInt siteOfInt_add supDist supDist_comm supDist_self
  supDist_triangle)
open TorusLumps (parentBlock bondFrom offsetNorm LatticeBond eq_of_siteOfInt_eq)
open TorusBlocks (parentBlock_blockCentreSite_add parentBlock_blockCentreSite supDist_parentBlock_le
  exists_eq_blockCentreSite_add)
open BlockOffsets (mem_centredCube_iff siteOfInt_cast_self)
open TorusContours (siteOfInt_single card_centredCube length_bondContour_le)
open PathForms (formPathSum pathEnd stepShift stepForm pathBonds stepBond formPathSum_append pathEnd_append
  pathEnd_add pathEnd_reversePath formPathSum_reversePath formPathSum_replicate pathEnd_replicate
  supDist_le_length_of_mem_pathBonds blockCentreSite_add_siteOfInt blockCentreSite_add_unitStep)
open FlatLinearization (stepEndpoint pathIntegral contourAverage RealOneForm CrossesBlockBoundary IsBlockTreeBond
  reflectedBond offsetFromCentre coarseSite kernelPairing plaquetteCurl curlEnergy indicatorForm
  renormalizedKernel BondKernel IsMinimizerFamily VanishesOnBlockTrees IsPositiveOnTreeGauge
  latticeContourAverage latticeLineSum blockCentreOnLattice LatticeOneForm)
variable {m n L : ℕ}
private theorem stepEndpoint_eq_add_stepShift (x : TorusSite m) (st : PathStep) :
    stepEndpoint x st = x + stepShift m st := by
  rcases st with ⟨i, s⟩
  cases s <;> simp [stepEndpoint, stepShift, sub_eq_add_neg]
private theorem pathIntegral_eq_formPathSum (ξ : RealOneForm m) (x : TorusSite m) (l : List PathStep) :
    pathIntegral ξ x l = formPathSum ξ x l := by
  induction l generalizing x with
  | nil => rfl
  | cons st r ih =>
    simp only [pathIntegral, formPathSum, ih, stepEndpoint_eq_add_stepShift, stepForm]
private theorem contourAverage_eq_sum (ξ : RealOneForm (n * L)) (c : TorusBond n) :
    _root_.YangMills.Construction.FlatLinearization.contourAverage L ξ c = (1 / (24 * (L : ℝ) ^ 4)) * ∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4),
      formPathSum ξ (SlopeCoefficient.blockCentreSite L c.1) (bondContour L h π c.2) := by
  simp only [_root_.YangMills.Construction.FlatLinearization.contourAverage, pathIntegral_eq_formPathSum]
private theorem formPathSum_add_forms (f g : RealOneForm m) (x : TorusSite m) (l : List PathStep) :
    formPathSum (fun b => f b + g b) x l = formPathSum f x l + formPathSum g x l := by
  induction l generalizing x with
  | nil => simp [formPathSum]
  | cons st r ih =>
    simp only [formPathSum, ih, stepForm]
    split_ifs <;> ring
private theorem formPathSum_mul_form (t : ℝ) (f : RealOneForm m) (x : TorusSite m) (l : List PathStep) :
    formPathSum (fun b => t * f b) x l = t * formPathSum f x l := by
  induction l generalizing x with
  | nil => simp [formPathSum]
  | cons st r ih =>
    simp only [formPathSum, ih, stepForm]
    split_ifs <;> ring
private def contourAverageLinear (L : ℕ) (c : TorusBond n) : RealOneForm (n * L) →ₗ[ℝ] ℝ where
  toFun ξ := _root_.YangMills.Construction.FlatLinearization.contourAverage L ξ c
  map_add' ξ ζ := by
    simp only [contourAverage_eq_sum]
    have e : ∀ x l, formPathSum (ξ + ζ) x l = formPathSum ξ x l + formPathSum ζ x l :=
      formPathSum_add_forms ξ ζ
    simp only [e, Finset.sum_add_distrib]
    ring
  map_smul' t ξ := by
    simp only [contourAverage_eq_sum, RingHom.id_apply, smul_eq_mul]
    have e : ∀ x l, formPathSum (t • ξ) x l = t * formPathSum ξ x l := formPathSum_mul_form t ξ
    simp only [e, ← Finset.mul_sum]
    ring
private theorem contourAverageLinear_apply (c : TorusBond n) (ξ : RealOneForm (n * L)) :
    contourAverageLinear L c ξ = _root_.YangMills.Construction.FlatLinearization.contourAverage L ξ c := rfl
private theorem abs_formPathSum_le (f : RealOneForm m) (x : TorusSite m) (l : List PathStep) {B : ℝ}
    (h : ∀ b ∈ pathBonds x l, |f b| ≤ B) : |formPathSum f x l| ≤ l.length * B := by
  induction l generalizing x with
  | nil => simp [formPathSum]
  | cons st r ih =>
    have h1 : |stepForm f x st| ≤ B := by
      have := h (stepBond x st) (by simp [pathBonds])
      rcases st with ⟨i, s⟩
      cases s <;> simpa [stepForm, stepBond] using this
    have h2 := ih (x + stepShift m st) fun b hb => h b (by simp [pathBonds, hb])
    simp only [formPathSum, List.length_cons]
    push_cast
    calc |stepForm f x st + formPathSum f (x + stepShift m st) r|
        ≤ |stepForm f x st| + |formPathSum f (x + stepShift m st) r| := abs_add_le _ _
      _ ≤ B + r.length * B := add_le_add h1 h2
      _ = (r.length + 1) * B := by ring
private theorem pathEnd_bondContour (x : TorusSite m) (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) (i : Fin 4) :
    pathEnd x (bondContour L h π i) = x + L • unitStep m i := by
  unfold bondContour
  rw [pathEnd_append, pathEnd_append, pathEnd_replicate, pathEnd_add, pathEnd_reversePath]
private theorem formPathSum_gradient (f : TorusSite m → ℝ) (x : TorusSite m) (l : List PathStep) :
    formPathSum (fun b : TorusBond m => f (b.1 + unitStep m b.2) - f b.1) x l = f (pathEnd x l) - f x := by
  induction l generalizing x with
  | nil => simp [formPathSum, pathEnd]
  | cons st r ih =>
    rcases st with ⟨i, s⟩
    cases s
    · simp only [formPathSum, pathEnd, ih, stepForm, stepShift, Bool.false_eq_true, if_false, sub_add_cancel,
        ← sub_eq_add_neg]
      ring
    · simp only [formPathSum, pathEnd, ih, stepForm, stepShift, if_true]
      ring
private theorem contourWeight_sum_const [NeZero L] (hL : Odd L) (t : ℝ) :
    (1 / (24 * (L : ℝ) ^ 4)) * ∑ _h ∈ centredCube L, ∑ _π : Equiv.Perm (Fin 4), t = t := by
  have hL0 : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, card_centredCube hL,
    nsmul_eq_mul]
  have : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [this]
  push_cast
  field_simp
private theorem contourAverage_of_const [NeZero L] (hL : Odd L) (ξ : RealOneForm (n * L)) (c : TorusBond n)
    (t : ℝ)
    (h : ∀ h ∈ centredCube L, ∀ π,
      formPathSum ξ (SlopeCoefficient.blockCentreSite L c.1) (bondContour L h π c.2) = t) :
    _root_.YangMills.Construction.FlatLinearization.contourAverage L ξ c = t := by
  rw [contourAverage_eq_sum]
  conv_rhs => rw [← contourWeight_sum_const hL t]
  congr 1
  exact Finset.sum_congr rfl fun g hg => Finset.sum_congr rfl fun π _ => h g hg π
private theorem abs_contourAverage_le [NeZero L] (hL : Odd L) (ξ : RealOneForm (n * L)) (c : TorusBond n)
    {B : ℝ}
    (h : ∀ h ∈ centredCube L, ∀ π,
      |formPathSum ξ (SlopeCoefficient.blockCentreSite L c.1) (bondContour L h π c.2)| ≤ B) :
    |_root_.YangMills.Construction.FlatLinearization.contourAverage L ξ c| ≤ B := by
  have hL0 : (0 : ℝ) < L := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne L))
  have hw : (0 : ℝ) ≤ 1 / (24 * (L : ℝ) ^ 4) := by positivity
  rw [contourAverage_eq_sum, abs_mul, abs_of_nonneg hw]
  conv_rhs => rw [← contourWeight_sum_const hL B]
  refine mul_le_mul_of_nonneg_left ?_ hw
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun g hg => ?_)
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun π _ => h g hg π)
private theorem coarseCentre_eq_blockCentreSite [NeZero n] (y : TorusSite n) :
    SlopeCoefficient.blockCentreSite L y = TorusBlocks.blockCentreSite L y := by apply _root_.YangMills.SharedProofs.p7467 <;> assumption
private theorem blockCentreSite_add [NeZero n] [NeZero L] (y u : TorusSite n) :
    TorusBlocks.blockCentreSite L (y + u) =
      TorusBlocks.blockCentreSite L y + TorusBlocks.blockCentreSite L u := by
  have h := blockCentreSite_add_siteOfInt (L := L) y (fun i => ((u i).cast : ℤ))
  rwa [siteOfInt_cast_self] at h
private theorem blockCentreSite_zero [NeZero n] : TorusBlocks.blockCentreSite L (0 : TorusSite n) = 0 := by
  funext i
  simp [TorusBlocks.blockCentreSite, siteOfInt]
private theorem blockCentreSite_neg [NeZero n] [NeZero L] (y : TorusSite n) :
    TorusBlocks.blockCentreSite L (-y) = - TorusBlocks.blockCentreSite L y := by
  have h := blockCentreSite_add (L := L) (-y) y
  rw [neg_add_cancel, blockCentreSite_zero] at h
  exact eq_neg_of_add_eq_zero_left h.symm
private theorem odd_eq_two_mul_half_add_one (hL : Odd L) : (L : ℤ) = 2 * (((L : ℤ) - 1) / 2) + 1 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoTori.cast_eq_two_mul_halfSide_add_one <;> assumption
private theorem parentBlock_blockCentreSite_add_offset [NeZero n] [NeZero L] (hL : Odd L) (y : TorusSite n)
    {o : Fin 4 → ℤ} (ho : o ∈ centredCube L) :
    parentBlock L (TorusBlocks.blockCentreSite L y + siteOfInt o) = y := by
  rw [parentBlock_blockCentreSite_add]
  have h0 : (siteOfInt fun i => (o i + ((L : ℤ) - 1) / 2) / (L : ℤ) : TorusSite n) = 0 := by
    funext k
    have hb := (_root_.YangMills.Construction.BlockOffsets.mem_centredCube_iff o).mp ho k
    have hh := odd_eq_two_mul_half_add_one hL
    have : (o k + ((L : ℤ) - 1) / 2) / (L : ℤ) = 0 := by
      apply Int.ediv_eq_zero_of_lt <;> omega
    simp [siteOfInt, this]
  rw [h0, add_zero]
private theorem exists_offset_decomposition [NeZero n] [NeZero L] (hL : Odd L) (x : TorusSite (n * L)) :
    ∃ o ∈ centredCube L, x = TorusBlocks.blockCentreSite L (parentBlock L x) + siteOfInt o := by
  obtain ⟨o, ho, hx⟩ := exists_eq_blockCentreSite_add hL x
  refine ⟨o, (_root_.YangMills.Construction.BlockOffsets.mem_centredCube_iff o).mpr fun i => ?_, hx⟩
  have hh := odd_eq_two_mul_half_add_one hL
  have := ho i
  omega
private theorem offsetFromCentre_blockCentreSite_add [NeZero n] [NeZero L] (hL : Odd L) (y : TorusSite n)
    {o : Fin 4 → ℤ} (ho : o ∈ centredCube L) :
    offsetFromCentre L (TorusBlocks.blockCentreSite L y + siteOfInt o) = o := by
  funext i
  have hb : coarseSite L (TorusBlocks.blockCentreSite L y + siteOfInt o) = y :=
    parentBlock_blockCentreSite_add_offset hL y ho
  have hnL : (L : ℤ) ≤ ((n * L : ℕ) : ℤ) := by
    have : L ≤ n * L := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (NeZero.ne n))
    exact_mod_cast this
  have hc := (_root_.YangMills.Construction.BlockOffsets.mem_centredCube_iff o).mp ho i
  have hh := odd_eq_two_mul_half_add_one hL
  haveI : NeZero (n * L) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne L)⟩
  simp only [offsetFromCentre, hb, coarseCentre_eq_blockCentreSite]
  have e : (TorusBlocks.blockCentreSite L y + siteOfInt o - TorusBlocks.blockCentreSite L y :
      TorusSite (n * L)) i = ((o i : ℤ) : ZMod (n * L)) := by
    simp [siteOfInt]
  rw [e]
  apply ContourOffsets.valMinAbs_intCast_of_small
  have : |o i| ≤ ((L : ℤ) - 1) / 2 := abs_le.mpr hc
  omega
private theorem siteOfInt_neg (z : Fin 4 → ℤ) : (siteOfInt (-z) : TorusSite m) = - siteOfInt z := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.siteOfInt_neg <;> assumption
private theorem exists_decomposition_of_not_crosses [NeZero n] [NeZero L] (hn : 2 ≤ n) (hL : Odd L)
    (b : TorusBond (n * L)) (hb : ¬ CrossesBlockBoundary L b) :
    ∃ (y : TorusSite n) (o : Fin 4 → ℤ), o ∈ centredCube L ∧ o + Pi.single b.2 1 ∈ centredCube L ∧
      b.1 = TorusBlocks.blockCentreSite L y + siteOfInt o := by
  obtain ⟨o, ho, hx⟩ := exists_offset_decomposition hL b.1
  obtain ⟨o', ho', hx'⟩ := exists_offset_decomposition hL (b.1 + unitStep (n * L) b.2)
  have hsame : parentBlock L (b.1 + unitStep (n * L) b.2) = parentBlock L b.1 := not_not.mp hb
  rw [hsame] at hx'
  have e : (siteOfInt o' : TorusSite (n * L)) = siteOfInt (o + Pi.single b.2 1) := by
    rw [siteOfInt_add, siteOfInt_single]
    have h1 : TorusBlocks.blockCentreSite L (parentBlock L b.1) + siteOfInt o' =
        TorusBlocks.blockCentreSite L (parentBlock L b.1) + (siteOfInt o + unitStep (n * L) b.2) := by
      rw [← add_assoc, ← hx]
      exact hx'.symm
    exact add_left_cancel h1
  have hnL : 2 * (L : ℤ) ≤ ((n * L : ℕ) : ℤ) := by
    have : 2 * L ≤ n * L := Nat.mul_le_mul_right _ hn
    exact_mod_cast this
  have hh := odd_eq_two_mul_half_add_one hL
  have e2 : o' = o + Pi.single b.2 1 := by
    apply eq_of_siteOfInt_eq e
    intro i
    have h1 := (_root_.YangMills.Construction.BlockOffsets.mem_centredCube_iff o).mp ho i
    have h2 := (_root_.YangMills.Construction.BlockOffsets.mem_centredCube_iff o').mp ho' i
    have h3 : (Pi.single b.2 1 : Fin 4 → ℤ) i = 0 ∨ (Pi.single b.2 1 : Fin 4 → ℤ) i = 1 := by
      by_cases hi : i = b.2
      · subst hi
        simp
      · simp [hi]
    rw [Pi.add_apply, abs_lt]
    rcases h3 with h3 | h3 <;> rw [h3] <;> constructor <;> omega
  exact ⟨parentBlock L b.1, o, ho, e2 ▸ ho', hx⟩
private theorem offsetFromCentre_step [NeZero n] [NeZero L] (hn : 2 ≤ n) (hL : Odd L) (b : TorusBond (n * L))
    (hb : ¬ CrossesBlockBoundary L b) :
    offsetFromCentre L (b.1 + unitStep (n * L) b.2) = offsetFromCentre L b.1 + Pi.single b.2 1 := by
  obtain ⟨y, o, ho, ho1, hx⟩ := exists_decomposition_of_not_crosses hn hL b hb
  have e : b.1 + unitStep (n * L) b.2 = TorusBlocks.blockCentreSite L y + siteOfInt (o + Pi.single b.2 1) := by
    rw [hx, siteOfInt_add, siteOfInt_single, add_assoc]
  rw [e, offsetFromCentre_blockCentreSite_add hL y ho1, hx, offsetFromCentre_blockCentreSite_add hL y ho]
private theorem isBlockTreeBond_reflectedBond [NeZero n] [NeZero L] (hn : 2 ≤ n) (hL : Odd L)
    (b : TorusBond (n * L)) (hb : IsBlockTreeBond L b) : IsBlockTreeBond L (reflectedBond b) := by
  obtain ⟨hc, hz⟩ := hb
  obtain ⟨y, o, ho, ho1, hx⟩ := exists_decomposition_of_not_crosses hn hL b hc
  have hneg : ∀ {p : Fin 4 → ℤ}, p ∈ centredCube L → -p ∈ centredCube L := fun {p} hp =>
    (mem_centredCube_iff _).mpr fun i => by
      have := (_root_.YangMills.Construction.BlockOffsets.mem_centredCube_iff p).mp hp i
      simp only [Pi.neg_apply]
      omega
  have e1 : (reflectedBond b).1 =
      TorusBlocks.blockCentreSite L (-y) + siteOfInt (-(o + Pi.single b.2 1)) := by
    simp only [reflectedBond]
    rw [hx, blockCentreSite_neg, siteOfInt_neg, siteOfInt_add, siteOfInt_single]
    abel
  have e2 : (reflectedBond b).1 + unitStep (n * L) (reflectedBond b).2 =
      TorusBlocks.blockCentreSite L (-y) + siteOfInt (-o) := by
    simp only [reflectedBond]
    rw [hx, blockCentreSite_neg, siteOfInt_neg]
    abel
  refine ⟨fun hcr => hcr ?_, fun l hl => ?_⟩
  · show parentBlock L _ = parentBlock L _
    rw [e2, e1, parentBlock_blockCentreSite_add_offset hL _ (hneg ho),
      parentBlock_blockCentreSite_add_offset hL _ (hneg ho1)]
  · have hl' : b.2 < l := hl
    have h0 := hz l hl'
    rw [hx, offsetFromCentre_blockCentreSite_add hL y ho] at h0
    rw [e1, offsetFromCentre_blockCentreSite_add hL _ (hneg ho1)]
    simp [h0, Pi.single_apply, (ne_of_gt hl')]
private theorem formPathSum_translate (f : RealOneForm m) (u x : TorusSite m) (l : List PathStep) :
    formPathSum (fun b => f (b.1 + u, b.2)) x l = formPathSum f (x + u) l := by
  induction l generalizing x with
  | nil => rfl
  | cons st r ih =>
    have e : x + stepShift m st + u = x + u + stepShift m st := by abel
    simp only [formPathSum, ih, e]
    congr 1
    rcases st with ⟨i, s⟩
    cases s
    · simp only [stepForm, Bool.false_eq_true, if_false]
      have : x - unitStep m i + u = x + u - unitStep m i := by abel
      rw [this]
    · simp [stepForm]
private theorem pathEnd_neg_reverse (x : TorusSite m) (l : List PathStep) :
    pathEnd (-(pathEnd x l)) l.reverse = -x := by
  induction l generalizing x with
  | nil => simp [pathEnd]
  | cons st r ih =>
    have e : pathEnd x (st :: r) = pathEnd (x + stepShift m st) r := rfl
    rw [List.reverse_cons, pathEnd_append, e, ih]
    simp [pathEnd]
private theorem formPathSum_reflect (f : RealOneForm m) (x : TorusSite m) (l : List PathStep) :
    formPathSum (fun b => f (reflectedBond b)) x l = formPathSum f (-(pathEnd x l)) l.reverse := by
  induction l generalizing x with
  | nil => simp [formPathSum]
  | cons st r ih =>
    have e : pathEnd x (st :: r) = pathEnd (x + stepShift m st) r := rfl
    rw [List.reverse_cons, formPathSum_append, e, pathEnd_neg_reverse, formPathSum, ih, add_comm]
    congr 1
    simp only [formPathSum, add_zero]
    rcases st with ⟨i, s⟩
    cases s
    · simp only [stepForm, stepShift, Bool.false_eq_true, if_false, reflectedBond]
      have e1 : -(x - unitStep m i) - unitStep m i = -x := by abel
      have e2 : -(x + -unitStep m i) - unitStep m i = -x := by abel
      rw [e1, e2]
    · simp only [stepForm, stepShift, if_true, reflectedBond]
      have e1 : -x - unitStep m i = -(x + unitStep m i) := by abel
      rw [e1]
private theorem axisPath_neg (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) :
    axisPath (-h) π = (axisPath h π).map fun st => (st.1, !st.2) := by
  unfold axisPath
  rw [List.map_flatMap]
  congr 1
  funext k
  rw [List.map_replicate]
  simp only [Pi.neg_apply, Int.natAbs_neg]
  rcases lt_trichotomy (h (π k)) 0 with h0 | h0 | h0
  · have h1 : 0 ≤ - h (π k) := by omega
    have h2 : ¬ 0 ≤ h (π k) := by omega
    simp [h1, h2]
    omega
  · simp [h0]
  · have h1 : ¬ 0 ≤ - h (π k) := by omega
    have h2 : 0 ≤ h (π k) := by omega
    simp [h1, h2]
    omega
private theorem bondContour_reverse (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) (i : Fin 4) :
    (bondContour L h π i).reverse = bondContour L (-h) π i := by
  unfold bondContour reversePath
  rw [axisPath_neg]
  simp [List.reverse_append, List.map_reverse, List.reverse_replicate, List.append_assoc, Function.comp_def]
private theorem reflectedBond_reflectedBond (b : TorusBond m) : reflectedBond (reflectedBond b) = b := by
  simp only [reflectedBond]
  ext1
  · simp only
    abel
  · rfl
private theorem contourAverage_reflect [NeZero n] [NeZero L] (ξ : RealOneForm (n * L)) (c : TorusBond n) :
    _root_.YangMills.Construction.FlatLinearization.contourAverage L (fun b => ξ (reflectedBond b)) c = _root_.YangMills.Construction.FlatLinearization.contourAverage L ξ (reflectedBond c) := by
  rw [contourAverage_eq_sum, contourAverage_eq_sum]
  congr 1
  have hb : SlopeCoefficient.blockCentreSite L (reflectedBond c).1 =
      -(SlopeCoefficient.blockCentreSite L c.1 + L • unitStep (n * L) c.2) := by
    simp only [reflectedBond, coarseCentre_eq_blockCentreSite]
    have e : -c.1 - unitStep n c.2 = -(c.1 + unitStep n c.2) := by abel
    rw [e, blockCentreSite_neg, blockCentreSite_add_unitStep]
  have hm : ∀ g : Fin 4 → ℤ, g ∈ centredCube L → -g ∈ centredCube L := fun g hg =>
    (mem_centredCube_iff _).mpr fun i => by
      have := (_root_.YangMills.Construction.BlockOffsets.mem_centredCube_iff g).mp hg i
      simp only [Pi.neg_apply]
      omega
  refine Finset.sum_nbij' (fun g => -g) (fun g => -g) hm hm (fun g _ => neg_neg g) (fun g _ => neg_neg g) ?_
  intro g _
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [formPathSum_reflect, pathEnd_bondContour, bondContour_reverse, hb]
  rfl
private theorem formPathSum_directional_indep (g : Fin 4 → ℝ) (x y : TorusSite m) (l : List PathStep) :
    formPathSum (fun b : TorusBond m => g b.2) x l = formPathSum (fun b : TorusBond m => g b.2) y l := by
  induction l generalizing x y with
  | nil => rfl
  | cons st r ih =>
    simp only [formPathSum]
    rw [ih (x + stepShift m st) (y + stepShift m st)]
    congr 1
private theorem formPathSum_directional_bondContour (g : Fin 4 → ℝ) (x : TorusSite m) (h : Fin 4 → ℤ)
    (π : Equiv.Perm (Fin 4)) (i : Fin 4) :
    formPathSum (fun b : TorusBond m => g b.2) x (bondContour L h π i) = L * g i := by
  unfold bondContour
  rw [formPathSum_append, formPathSum_append, formPathSum_replicate,
    formPathSum_directional_indep g _ (pathEnd x (axisPath h π)) (reversePath _), formPathSum_reversePath]
  simp
private theorem contourAverage_directional [NeZero L] (hL : Odd L) (g : Fin 4 → ℝ) (c : TorusBond n) :
    _root_.YangMills.Construction.FlatLinearization.contourAverage L (fun b : TorusBond (n * L) => g b.2) c = L * g c.2 :=
  contourAverage_of_const hL _ c _ fun h _ π => formPathSum_directional_bondContour g _ h π c.2
private theorem contourAverage_gradient [NeZero n] [NeZero L] (hL : Odd L) (f : TorusSite (n * L) → ℝ)
    (c : TorusBond n) :
    _root_.YangMills.Construction.FlatLinearization.contourAverage L (fun b : TorusBond (n * L) => f (b.1 + unitStep (n * L) b.2) - f b.1) c =
      f (TorusBlocks.blockCentreSite L (c.1 + unitStep n c.2)) - f (TorusBlocks.blockCentreSite L c.1) := by
  refine contourAverage_of_const hL _ c _ fun g _ π => ?_
  rw [formPathSum_gradient, pathEnd_bondContour, coarseCentre_eq_blockCentreSite, blockCentreSite_add_unitStep]
private theorem zero_mem_centredCube (hL : Odd L) : (0 : Fin 4 → ℤ) ∈ centredCube L := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.zero_mem_centredCube <;> assumption
private theorem offsetFromCentre_blockCentreSite [NeZero n] [NeZero L] (hL : Odd L) (y : TorusSite n) :
    offsetFromCentre L (TorusBlocks.blockCentreSite L y) = 0 := by
  have h := offsetFromCentre_blockCentreSite_add hL y (zero_mem_centredCube hL)
  have h0 : (siteOfInt (0 : Fin 4 → ℤ) : TorusSite (n * L)) = 0 := by
    funext k
    simp [siteOfInt]
  rwa [h0, add_zero] at h
section KernelPairing
variable [NeZero m]
private theorem kernelPairing_comm {K : TorusBond m → TorusBond m → ℝ} (hs : ∀ b c, K b c = K c b)
    (ξ ζ : RealOneForm m) :
    kernelPairing K ξ ζ = kernelPairing K ζ ξ := by
  simp only [kernelPairing]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  rw [hs c b]
  ring
private theorem kernelPairing_sub_left (K : TorusBond m → TorusBond m → ℝ) (ξ₁ ξ₂ ζ : RealOneForm m) :
    kernelPairing K (fun b => ξ₁ b - ξ₂ b) ζ = kernelPairing K ξ₁ ζ - kernelPairing K ξ₂ ζ := by
  simp only [kernelPairing, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  ring
private theorem kernelPairing_sum_left {ι : Type} [Fintype ι] (K : TorusBond m → TorusBond m → ℝ) (w : ι → ℝ)
    (f : ι → RealOneForm m) (ζ : RealOneForm m) :
    kernelPairing K (fun b => ∑ c, w c * f c b) ζ = ∑ c, w c * kernelPairing K (f c) ζ := by
  simp only [kernelPairing, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_congr rfl fun b _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun b' _ => ?_
  ring
private theorem kernelPairing_eq_zero_of_annihilates (K : TorusBond m → TorusBond m → ℝ) (ξ η : RealOneForm m)
    (hk : ∀ b, ∑ b', K b b' * η b' = 0) : kernelPairing K ξ η = 0 := by
  simp only [kernelPairing]
  refine Finset.sum_eq_zero fun b _ => ?_
  calc ∑ b', K b b' * ξ b * η b' = ξ b * ∑ b', K b b' * η b' := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun b' _ => by ring
    _ = 0 := by rw [hk b, mul_zero]
private theorem plaquetteCurl_add (u v : RealOneForm m) (x : TorusSite m) (μ ν : Fin 4) :
    plaquetteCurl (fun c => u c + v c) x μ ν = plaquetteCurl u x μ ν + plaquetteCurl v x μ ν := by
  simp only [plaquetteCurl]
  ring
private theorem curlEnergy_add_le (u v : RealOneForm m) :
    curlEnergy (fun c => u c + v c) ≤ 2 * curlEnergy u + 2 * curlEnergy v := by
  simp only [curlEnergy, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun μ _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun ν _ => ?_
  split_ifs
  · rw [plaquetteCurl_add]
    nlinarith [sq_nonneg (plaquetteCurl u x μ ν - plaquetteCurl v x μ ν)]
  · simp
private theorem curlEnergy_nonneg (u : RealOneForm m) : 0 ≤ curlEnergy u := by
  refine Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun μ _ => Finset.sum_nonneg fun ν _ => ?_
  split_ifs
  · positivity
  · exact le_rfl
abbrev _root_.YangMills.SharedProofs.p115143 := @curlEnergy_nonneg
private theorem curlEnergy_le_sum_sq (D : RealOneForm m) : curlEnergy D ≤ 64 * ∑ b, D b ^ 2 := by
  set T : Fin 4 → ℝ := fun μ => ∑ x : TorusSite m, D (x, μ) ^ 2 with hT
  have hs : ∀ (u : TorusSite m) (μ : Fin 4), ∑ x : TorusSite m, D (x + u, μ) ^ 2 = T μ := fun u μ =>
    Equiv.sum_comp (Equiv.addRight u) (fun x => D (x, μ) ^ 2)
  have hS : ∑ b, D b ^ 2 = ∑ μ, T μ := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
  have hterm : ∀ (x : TorusSite m) (μ ν : Fin 4), (if μ < ν then plaquetteCurl D x μ ν ^ 2 else 0) ≤
      4 * (D (x, μ) ^ 2 + D (x + unitStep m μ, ν) ^ 2 + D (x + unitStep m ν, μ) ^ 2 + D (x, ν) ^ 2) := by
    intro x μ ν
    split_ifs
    · simp only [plaquetteCurl]
      nlinarith [sq_nonneg (D (x, μ) + D (x + unitStep m μ, ν)), sq_nonneg (D (x, μ) - D (x + unitStep m μ, ν)),
        sq_nonneg (D (x + unitStep m ν, μ) + D (x, ν)), sq_nonneg (D (x + unitStep m ν, μ) - D (x, ν)),
        sq_nonneg (D (x, μ) + D (x + unitStep m ν, μ)), sq_nonneg (D (x, μ) - D (x + unitStep m ν, μ)),
        sq_nonneg (D (x, μ) + D (x, ν)), sq_nonneg (D (x, μ) - D (x, ν)),
        sq_nonneg (D (x + unitStep m μ, ν) + D (x + unitStep m ν, μ)),
        sq_nonneg (D (x + unitStep m μ, ν) - D (x + unitStep m ν, μ)),
        sq_nonneg (D (x + unitStep m μ, ν) + D (x, ν)), sq_nonneg (D (x + unitStep m μ, ν) - D (x, ν))]
    · positivity
  calc curlEnergy D ≤ ∑ x : TorusSite m, ∑ μ : Fin 4, ∑ ν : Fin 4,
        4 * (D (x, μ) ^ 2 + D (x + unitStep m μ, ν) ^ 2 + D (x + unitStep m ν, μ) ^ 2 + D (x, ν) ^ 2) :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun μ _ => Finset.sum_le_sum fun ν _ => hterm x μ ν
    _ = ∑ μ : Fin 4, ∑ ν : Fin 4, ∑ x : TorusSite m,
        4 * (D (x, μ) ^ 2 + D (x + unitStep m μ, ν) ^ 2 + D (x + unitStep m ν, μ) ^ 2 + D (x, ν) ^ 2) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun μ _ => Finset.sum_comm
    _ = ∑ μ : Fin 4, ∑ ν : Fin 4, 4 * (2 * T μ + 2 * T ν) := by
        refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
          hs, hs]
        simp only [hT]
        ring
    _ = 64 * ∑ b, D b ^ 2 := by
        rw [hS]
        simp only [Fin.sum_univ_four]
        ring
end KernelPairing
section FixedSide
variable [NeZero n] [NeZero L]
private def coarseKernel (a : ℝ) (L : ℕ) [NeZero L] (K : TorusBond (n * L) → TorusBond (n * L) → ℝ)
    (Pn : TorusBond (n * L) → TorusBond n → ℝ) (c c' : TorusBond n) : ℝ :=
  kernelPairing K (fun b => Pn b c) (fun b => Pn b c') +
    a * ∑ c'', (indicatorForm c c'' - _root_.YangMills.Construction.FlatLinearization.contourAverage L (fun b => Pn b c) c'') *
      (indicatorForm c' c'' - _root_.YangMills.Construction.FlatLinearization.contourAverage L (fun b => Pn b c') c'')
private theorem renormalizedKernel_eq_coarseKernel (a : ℝ) (h : BondKernel)
    (P : (n : ℕ) → TorusBond (n * L) → TorusBond n → ℝ) (c c' : TorusBond n) :
    renormalizedKernel a L h P n c c' = coarseKernel a L (h (n * L)) (P n) c c' := by
  simp only [renormalizedKernel]
  rw [dif_pos ⟨NeZero.ne n, NeZero.ne L⟩]
  rfl
variable {a : ℝ} {K : TorusBond (n * L) → TorusBond (n * L) → ℝ} {Pn : TorusBond (n * L) → TorusBond n → ℝ}
private theorem sum_mul_indicatorForm (f : TorusBond n → ℝ) (c : TorusBond n) :
    ∑ c'', f c'' * indicatorForm c c'' = f c := by
  simp [indicatorForm]
private theorem coarseKernel_eq (hR : IsMinimizerFamily a L K Pn) (c c' : TorusBond n) :
    coarseKernel a L K Pn c c' = a * (indicatorForm c c' - _root_.YangMills.Construction.FlatLinearization.contourAverage L (fun b => Pn b c) c') := by
  have hcrit := (hR c).2 (fun b => Pn b c') (hR c').1
  have e1 := sum_mul_indicatorForm
    (fun c'' => indicatorForm c c'' - _root_.YangMills.Construction.FlatLinearization.contourAverage L (fun b => Pn b c) c'') c'
  have e2 : ∑ c'', (indicatorForm c c'' - _root_.YangMills.Construction.FlatLinearization.contourAverage L (fun b => Pn b c) c'') *
      (indicatorForm c' c'' - _root_.YangMills.Construction.FlatLinearization.contourAverage L (fun b => Pn b c') c'') =
      (indicatorForm c c' - _root_.YangMills.Construction.FlatLinearization.contourAverage L (fun b => Pn b c) c') -
      ∑ c'', (indicatorForm c c'' - _root_.YangMills.Construction.FlatLinearization.contourAverage L (fun b => Pn b c) c'') *
        contourAverage L (fun b => Pn b c') c'' := by
    rw [← e1, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun c'' _ => by ring
  have e3 : ∑ c'', (_root_.YangMills.Construction.FlatLinearization.contourAverage L (fun b => Pn b c) c'' - indicatorForm c c'') *
        _root_.YangMills.Construction.FlatLinearization.contourAverage L (fun b => Pn b c') c'' =
      - ∑ c'', (indicatorForm c c'' - _root_.YangMills.Construction.FlatLinearization.contourAverage L (fun b => Pn b c) c'') *
        contourAverage L (fun b => Pn b c') c'' := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun c'' _ => by ring
  rw [e3] at hcrit
  unfold coarseKernel
  rw [e2]
  linear_combination hcrit
private theorem coarseKernel_comm (hs : ∀ b c, K b c = K c b) (c c' : TorusBond n) :
    coarseKernel a L K Pn c c' = coarseKernel a L K Pn c' c := by
  unfold coarseKernel
  rw [kernelPairing_comm hs]
  congr 2
  exact Finset.sum_congr rfl fun c'' _ => by ring
private theorem sum_coarseKernel_mul_contourAverage_eq_zero (hR : IsMinimizerFamily a L K Pn) (c : TorusBond n)
    (η : RealOneForm (n * L)) (hoff : VanishesOnBlockTrees L η) (hk : ∀ b, ∑ b', K b b' * η b' = 0) :
    ∑ c', coarseKernel a L K Pn c c' * _root_.YangMills.Construction.FlatLinearization.contourAverage L η c' = 0 := by
  have hcrit := (hR c).2 η hoff
  rw [kernelPairing_eq_zero_of_annihilates K _ η hk, zero_add] at hcrit
  have e : ∑ c', coarseKernel a L K Pn c c' * _root_.YangMills.Construction.FlatLinearization.contourAverage L η c' =
      - (a * ∑ c', (_root_.YangMills.Construction.FlatLinearization.contourAverage L (fun b => Pn b c) c' - indicatorForm c c') * _root_.YangMills.Construction.FlatLinearization.contourAverage L η c') := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [coarseKernel_eq hR]
    ring
  rw [e, hcrit, neg_zero]
private theorem minimizer_unique (hpos : IsPositiveOnTreeGauge (n := n) a L K) {ξ₁ ξ₂ : RealOneForm (n * L)}
    (s : TorusBond n → ℝ) (h₁ : VanishesOnBlockTrees L ξ₁) (h₂ : VanishesOnBlockTrees L ξ₂)
    (c₁ : ∀ ζ : RealOneForm (n * L), VanishesOnBlockTrees L ζ → kernelPairing K ξ₁ ζ +
      a * ∑ c', (_root_.YangMills.Construction.FlatLinearization.contourAverage L ξ₁ c' - s c') * _root_.YangMills.Construction.FlatLinearization.contourAverage L ζ c' = 0)
    (c₂ : ∀ ζ : RealOneForm (n * L), VanishesOnBlockTrees L ζ → kernelPairing K ξ₂ ζ +
      a * ∑ c', (_root_.YangMills.Construction.FlatLinearization.contourAverage L ξ₂ c' - s c') * _root_.YangMills.Construction.FlatLinearization.contourAverage L ζ c' = 0) : ξ₁ = ξ₂ := by
  by_contra hne
  set d : RealOneForm (n * L) := fun b => ξ₁ b - ξ₂ b with hd
  have hoff : VanishesOnBlockTrees L d := fun b hb => by simp [hd, h₁ b hb, h₂ b hb]
  have hd0 : d ≠ 0 := fun h0 => hne (funext fun b => sub_eq_zero.mp (congrFun h0 b))
  have hp := hpos d hoff hd0
  have hq : ∀ c', _root_.YangMills.Construction.FlatLinearization.contourAverage L d c' = _root_.YangMills.Construction.FlatLinearization.contourAverage L ξ₁ c' - _root_.YangMills.Construction.FlatLinearization.contourAverage L ξ₂ c' := fun c' =>
    map_sub (contourAverageLinear L c') ξ₁ ξ₂
  have e1 := c₁ d hoff
  have e2 := c₂ d hoff
  have e3 : ∑ c, _root_.YangMills.Construction.FlatLinearization.contourAverage L d c ^ 2 =
      ∑ c', (_root_.YangMills.Construction.FlatLinearization.contourAverage L ξ₁ c' - s c') * _root_.YangMills.Construction.FlatLinearization.contourAverage L d c' -
      ∑ c', (_root_.YangMills.Construction.FlatLinearization.contourAverage L ξ₂ c' - s c') * _root_.YangMills.Construction.FlatLinearization.contourAverage L d c' := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [hq]
    ring
  have e4 : kernelPairing K d d = kernelPairing K ξ₁ d - kernelPairing K ξ₂ d := kernelPairing_sub_left K ξ₁ ξ₂ d
  rw [e3, e4] at hp
  linarith
private theorem kernelPairing_reflect (hi : ∀ b c, K (reflectedBond b) (reflectedBond c) = K b c)
    (ξ ζ : RealOneForm (n * L)) :
    kernelPairing K (fun b => ξ (reflectedBond b)) ζ = kernelPairing K ξ (fun b => ζ (reflectedBond b)) := by
  have hE : ∀ g : TorusBond (n * L) → ℝ, ∑ b, g (reflectedBond b) = ∑ b, g b := fun g =>
    Equiv.sum_comp ⟨reflectedBond, reflectedBond, reflectedBond_reflectedBond, reflectedBond_reflectedBond⟩ g
  simp only [kernelPairing]
  rw [← hE]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← hE]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [reflectedBond_reflectedBond, hi]
private theorem indicatorForm_reflect (c c' : TorusBond n) :
    indicatorForm (reflectedBond c) (reflectedBond c') = indicatorForm c c' := by
  simp only [indicatorForm]
  have : reflectedBond c' = reflectedBond c ↔ c' = c :=
    ⟨fun h => by rw [← reflectedBond_reflectedBond c', h, reflectedBond_reflectedBond], fun h => by rw [h]⟩
  simp only [this]
private theorem minimizer_reflect (hn : 2 ≤ n) (hL : Odd L) (hR : IsMinimizerFamily a L K Pn)
    (hpos : IsPositiveOnTreeGauge (n := n) a L K)
    (hi : ∀ b c, K (reflectedBond b) (reflectedBond c) = K b c) (c : TorusBond n) :
    (fun b => Pn b (reflectedBond c)) = fun b => Pn (reflectedBond b) c := by
  have hE : ∀ g : TorusBond n → ℝ, ∑ b, g (reflectedBond b) = ∑ b, g b := fun g =>
    Equiv.sum_comp ⟨reflectedBond, reflectedBond, reflectedBond_reflectedBond, reflectedBond_reflectedBond⟩ g
  refine minimizer_unique hpos (indicatorForm (reflectedBond c)) (hR _).1 ?_ (hR _).2 ?_
  · exact fun b hb => (hR c).1 _ (isBlockTreeBond_reflectedBond hn hL b hb)
  · intro ζ hζ
    have hoff : VanishesOnBlockTrees L fun b => ζ (reflectedBond b) := fun b hb =>
      hζ _ (isBlockTreeBond_reflectedBond hn hL b hb)
    have h1 := (hR c).2 _ hoff
    have e0 : kernelPairing K (fun b => Pn (reflectedBond b) c) ζ =
        kernelPairing K (fun b => Pn b c) (fun b => ζ (reflectedBond b)) :=
      kernelPairing_reflect hi (fun b => Pn b c) ζ
    rw [e0, ← hE]
    have e : ∑ c', (_root_.YangMills.Construction.FlatLinearization.contourAverage L (fun b => Pn (reflectedBond b) c) (reflectedBond c') -
        indicatorForm (reflectedBond c) (reflectedBond c')) * _root_.YangMills.Construction.FlatLinearization.contourAverage L ζ (reflectedBond c') =
        ∑ c'', (_root_.YangMills.Construction.FlatLinearization.contourAverage L (fun b => Pn b c) c'' - indicatorForm c c'') *
          _root_.YangMills.Construction.FlatLinearization.contourAverage L (fun b => ζ (reflectedBond b)) c'' := by
      refine Finset.sum_congr rfl fun c' _ => ?_
      rw [contourAverage_reflect (fun b => Pn b c), reflectedBond_reflectedBond, contourAverage_reflect ζ,
        indicatorForm_reflect]
    rw [e]
    exact h1
private theorem kernelPairing_coarseKernel (hR : IsMinimizerFamily a L K Pn) (B : RealOneForm n) :
    kernelPairing (coarseKernel a L K Pn) B B =
      kernelPairing K (fun b => ∑ c, B c * Pn b c) (fun b => ∑ c, B c * Pn b c) +
        a * ∑ c, (B c - _root_.YangMills.Construction.FlatLinearization.contourAverage L (fun b => ∑ c', B c' * Pn b c') c) ^ 2 := by
  set ξ : RealOneForm (n * L) := fun b => ∑ c, B c * Pn b c with hξ
  have hQ : ∀ c'', _root_.YangMills.Construction.FlatLinearization.contourAverage L ξ c'' = ∑ c, B c * _root_.YangMills.Construction.FlatLinearization.contourAverage L (fun b => Pn b c) c'' := by
    intro c''
    have e : ξ = ∑ c, B c • (fun b => Pn b c) := by
      funext b
      simp [hξ, Finset.sum_apply]
    rw [← contourAverageLinear_apply, e, map_sum]
    simp only [map_smul, contourAverageLinear_apply, smul_eq_mul]
  have hU : ∀ c'', ∑ c, B c * indicatorForm c c'' = B c'' := by
    intro c''
    simp [indicatorForm]
  have hoff : VanishesOnBlockTrees L ξ := fun b hb => by
    simp only [hξ]
    refine Finset.sum_eq_zero fun c _ => ?_
    have h0 : Pn b c = 0 := (hR c).1 b hb
    rw [h0, mul_zero]
  have s1 : kernelPairing (coarseKernel a L K Pn) B B =
      a * ∑ c', (B c' - _root_.YangMills.Construction.FlatLinearization.contourAverage L ξ c') * B c' := by
    simp only [kernelPairing, coarseKernel_eq hR]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [← hU c', hQ c', ← Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
    simp only [hU]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  have s2 : kernelPairing K ξ ξ = a * ∑ c', (B c' - _root_.YangMills.Construction.FlatLinearization.contourAverage L ξ c') * _root_.YangMills.Construction.FlatLinearization.contourAverage L ξ c' := by
    have h1 : kernelPairing K ξ ξ = ∑ c, B c * kernelPairing K (fun b => Pn b c) ξ :=
      kernelPairing_sum_left K B (fun c b => Pn b c) ξ
    have h2 : ∀ c, kernelPairing K (fun b => Pn b c) ξ = - (a * ∑ c'',
        (_root_.YangMills.Construction.FlatLinearization.contourAverage L (fun b => Pn b c) c'' - indicatorForm c c'') * _root_.YangMills.Construction.FlatLinearization.contourAverage L ξ c'') := fun c =>
      eq_neg_of_add_eq_zero_left ((hR c).2 ξ hoff)
    rw [h1]
    simp only [h2]
    have h3 : ∀ c', B c' - _root_.YangMills.Construction.FlatLinearization.contourAverage L ξ c' =
        ∑ c, B c * (indicatorForm c c' - _root_.YangMills.Construction.FlatLinearization.contourAverage L (fun b => Pn b c) c') := by
      intro c'
      rw [hQ c']
      conv_lhs => rw [← hU c']
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun c _ => by ring
    calc ∑ c, B c * -(a * ∑ c'', (_root_.YangMills.Construction.FlatLinearization.contourAverage L (fun b => Pn b c) c'' - indicatorForm c c'') *
            _root_.YangMills.Construction.FlatLinearization.contourAverage L ξ c'')
        = a * ∑ c, ∑ c'', B c * ((indicatorForm c c'' - _root_.YangMills.Construction.FlatLinearization.contourAverage L (fun b => Pn b c) c'') *
            _root_.YangMills.Construction.FlatLinearization.contourAverage L ξ c'') := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun c _ => ?_
          have : ∑ c'', B c * ((indicatorForm c c'' - _root_.YangMills.Construction.FlatLinearization.contourAverage L (fun b => Pn b c) c'') *
              _root_.YangMills.Construction.FlatLinearization.contourAverage L ξ c'') = - (B c * ∑ c'', (_root_.YangMills.Construction.FlatLinearization.contourAverage L (fun b => Pn b c) c'' -
                indicatorForm c c'') * _root_.YangMills.Construction.FlatLinearization.contourAverage L ξ c'') := by
            rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
            exact Finset.sum_congr rfl fun c'' _ => by ring
          rw [this]
          ring
      _ = a * ∑ c'', ∑ c, B c * ((indicatorForm c c'' - _root_.YangMills.Construction.FlatLinearization.contourAverage L (fun b => Pn b c) c'') *
            _root_.YangMills.Construction.FlatLinearization.contourAverage L ξ c'') := by rw [Finset.sum_comm]
      _ = a * ∑ c', (B c' - _root_.YangMills.Construction.FlatLinearization.contourAverage L ξ c') * _root_.YangMills.Construction.FlatLinearization.contourAverage L ξ c' := by
          congr 1
          refine Finset.sum_congr rfl fun c' _ => ?_
          rw [h3 c', Finset.sum_mul]
          exact Finset.sum_congr rfl fun c _ => by ring
  rw [s1, s2]
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun c _ => by ring
end FixedSide
private theorem abs_contourAverage_le_exp [NeZero n] [NeZero L] (hL : Odd L) {M θ : ℝ} (hθ : 0 < θ)
    {ξ : RealOneForm (n * L)} (z : TorusSite n)
    (hd : ∀ b : TorusBond (n * L),
      |ξ b| ≤ M * Real.exp (-(θ * _root_.YangMills.Construction.TorusFields.supDist b.1 (SlopeCoefficient.blockCentreSite L z))))
    (c' : TorusBond n) :
    |_root_.YangMills.Construction.FlatLinearization.contourAverage L ξ c'| ≤
      (5 * L) * (|M| * Real.exp (θ * (5 * L + 1))) * Real.exp (-(θ * _root_.YangMills.Construction.TorusFields.supDist z c'.1)) := by
  haveI : NeZero (n * L) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne L)⟩
  have hB : 0 ≤ |M| * Real.exp (θ * (5 * L + 1)) * Real.exp (-(θ * _root_.YangMills.Construction.TorusFields.supDist z c'.1)) := by positivity
  apply abs_contourAverage_le hL
  intro g hg π
  have hlen := length_bondContour_le hL hg π c'.2
  have hbd : ∀ b ∈ pathBonds (SlopeCoefficient.blockCentreSite L c'.1) (bondContour L g π c'.2),
      |ξ b| ≤ |M| * Real.exp (θ * (5 * L + 1)) * Real.exp (-(θ * _root_.YangMills.Construction.TorusFields.supDist z c'.1)) := by
    intro b hb
    have h1 := (_root_.YangMills.Construction.PathForms.supDist_le_length_of_mem_pathBonds _ _ hb).1
    have h2 : _root_.YangMills.Construction.TorusFields.supDist z c'.1 ≤
        _root_.YangMills.Construction.TorusFields.supDist (TorusBlocks.blockCentreSite L z) (TorusBlocks.blockCentreSite L c'.1) + 1 := by
      have := _root_.YangMills.Construction.TorusBlocks.supDist_parentBlock_le hL (TorusBlocks.blockCentreSite L z) (TorusBlocks.blockCentreSite L c'.1)
      rwa [parentBlock_blockCentreSite hL, parentBlock_blockCentreSite hL] at this
    have h3 := _root_.YangMills.Construction.TorusFields.supDist_triangle (TorusBlocks.blockCentreSite L z) b.1 (TorusBlocks.blockCentreSite L c'.1)
    have h3' : _root_.YangMills.Construction.TorusFields.supDist (TorusBlocks.blockCentreSite L z) b.1 =
        _root_.YangMills.Construction.TorusFields.supDist b.1 (SlopeCoefficient.blockCentreSite L z) := by
      rw [supDist_comm, coarseCentre_eq_blockCentreSite]
    have h3'' : _root_.YangMills.Construction.TorusFields.supDist b.1 (TorusBlocks.blockCentreSite L c'.1) =
        _root_.YangMills.Construction.TorusFields.supDist (SlopeCoefficient.blockCentreSite L c'.1) b.1 := by
      rw [supDist_comm, coarseCentre_eq_blockCentreSite]
    have h4 : (_root_.YangMills.Construction.TorusFields.supDist z c'.1 : ℝ) ≤
        (_root_.YangMills.Construction.TorusFields.supDist b.1 (SlopeCoefficient.blockCentreSite L z) : ℝ) + (5 * L + 1) := by
      have : _root_.YangMills.Construction.TorusFields.supDist z c'.1 ≤ _root_.YangMills.Construction.TorusFields.supDist b.1 (SlopeCoefficient.blockCentreSite L z) + (5 * L + 1) := by omega
      exact_mod_cast this
    have h5 := mul_le_mul_of_nonneg_left h4 hθ.le
    calc |ξ b| ≤ M * Real.exp (-(θ * _root_.YangMills.Construction.TorusFields.supDist b.1 (SlopeCoefficient.blockCentreSite L z))) := hd b
      _ ≤ |M| * Real.exp (-(θ * _root_.YangMills.Construction.TorusFields.supDist b.1 (SlopeCoefficient.blockCentreSite L z))) :=
          mul_le_mul_of_nonneg_right (le_abs_self M) (Real.exp_pos _).le
      _ ≤ |M| * (Real.exp (θ * (5 * L + 1)) * Real.exp (-(θ * _root_.YangMills.Construction.TorusFields.supDist z c'.1))) := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg M)
          rw [← Real.exp_add]
          apply Real.exp_le_exp.mpr
          rw [mul_add] at h5
          linarith
      _ = |M| * Real.exp (θ * (5 * L + 1)) * Real.exp (-(θ * _root_.YangMills.Construction.TorusFields.supDist z c'.1)) := by ring
  have key := abs_formPathSum_le ξ (SlopeCoefficient.blockCentreSite L c'.1) (bondContour L g π c'.2) hbd
  calc _ ≤ ((bondContour L g π c'.2).length : ℝ) *
        (|M| * Real.exp (θ * (5 * L + 1)) * Real.exp (-(θ * _root_.YangMills.Construction.TorusFields.supDist z c'.1))) := key
    _ ≤ (5 * L) * (|M| * Real.exp (θ * (5 * L + 1)) * Real.exp (-(θ * _root_.YangMills.Construction.TorusFields.supDist z c'.1))) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hlen) hB
    _ = _ := by ring
private theorem formPathSum_siteOfInt [NeZero m] (ξ : RealOneForm m) (z : Fin 4 → ℤ) (l : List PathStep) :
    formPathSum ξ (siteOfInt z) l = latticeLineSum (fun b => ξ (bondFrom 0 b)) z l := by
  induction l generalizing z with
  | nil => rfl
  | cons st r ih =>
    have e : (siteOfInt z : TorusSite m) + stepShift m st = siteOfInt (z + stepDisplacement st) := by
      rcases st with ⟨i, s⟩
      have hu : (siteOfInt (basisVector i) : TorusSite m) = unitStep m i := siteOfInt_single i
      cases s
      · simp only [stepShift, stepDisplacement, Bool.false_eq_true, if_false]
        rw [siteOfInt_add, siteOfInt_neg, hu]
      · simp only [stepShift, stepDisplacement, if_true]
        rw [siteOfInt_add, hu]
    simp only [formPathSum, latticeLineSum, e, ih]
    congr 1
    rcases st with ⟨i, s⟩
    have hu : (siteOfInt (basisVector i) : TorusSite m) = unitStep m i := siteOfInt_single i
    cases s
    · simp only [stepForm, Bool.false_eq_true, if_false, bondFrom, zero_add]
      rw [sub_eq_add_neg z, siteOfInt_add, siteOfInt_neg, hu, sub_eq_add_neg]
    · simp [stepForm, bondFrom]
private theorem tendsto_latticeLineSum {f : ℕ → LatticeOneForm} {g : LatticeOneForm}
    (h : ∀ b, Filter.Tendsto (fun n => f n b) Filter.atTop (𝓝 (g b))) (z : Fin 4 → ℤ) (l : List PathStep) :
    Filter.Tendsto (fun n => latticeLineSum (f n) z l) Filter.atTop (𝓝 (latticeLineSum g z l)) := by
  induction l generalizing z with
  | nil => simpa [latticeLineSum] using tendsto_const_nhds
  | cons st r ih =>
    simp only [latticeLineSum]
    refine Filter.Tendsto.add ?_ (ih _)
    by_cases hs : st.2 = true
    · simpa [hs] using h _
    · simpa [hs] using (h _).neg
private theorem contourAverage_bondFrom_zero [NeZero n] [NeZero L] (ξ : RealOneForm (n * L)) (c : LatticeBond) :
    _root_.YangMills.Construction.FlatLinearization.contourAverage L ξ (bondFrom 0 c : TorusBond n) =
      latticeContourAverage L (fun x => ξ (bondFrom 0 x)) c := by
  haveI : NeZero (n * L) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne L)⟩
  have hb : SlopeCoefficient.blockCentreSite L (bondFrom 0 c : TorusBond n).1 =
      siteOfInt (blockCentreOnLattice L c.1) := by
    simp only [bondFrom, zero_add, coarseCentre_eq_blockCentreSite]
    have := blockCentreSite_add_siteOfInt (L := L) (0 : TorusSite n) c.1
    rw [zero_add, blockCentreSite_zero, zero_add] at this
    exact this
  rw [contourAverage_eq_sum, hb]
  unfold latticeContourAverage
  congr 1
  exact Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun π _ => formPathSum_siteOfInt ξ _ _
private theorem indicatorForm_bondFrom_zero [NeZero n] (b c : LatticeBond) (hn : offsetNorm (c.1 - b.1) < n) :
    indicatorForm (bondFrom 0 b : TorusBond n) (bondFrom 0 c) = if c = b then 1 else 0 := by
  by_cases e : c = b
  · subst e
    simp [indicatorForm]
  · have hne : (bondFrom 0 c : TorusBond n) ≠ bondFrom 0 b := by
      intro heq
      have h1 : (siteOfInt c.1 : TorusSite n) = siteOfInt b.1 := by
        simpa [bondFrom] using congrArg Prod.fst heq
      have h2' : (bondFrom 0 c : TorusBond n).2 = (bondFrom 0 b : TorusBond n).2 := by rw [heq]
      have h2 : c.2 = b.2 := h2'
      refine e (Prod.ext (eq_of_siteOfInt_eq h1 fun i => ?_) h2)
      have h3 : ((c.1 - b.1) i).natAbs ≤ offsetNorm (c.1 - b.1) :=
        Finset.le_sup (f := fun i => ((c.1 - b.1) i).natAbs) (Finset.mem_univ i)
      simp only [Pi.sub_apply] at h3
      rw [Int.abs_eq_natAbs]
      exact_mod_cast h3.trans_lt hn
    simp [indicatorForm, hne, e]
theorem renormalizedKernelIsFlowKernel_of_contourAverageCurlBound (hCurl : ContourAverageCurlBound) :
    RenormalizedKernelIsFlowKernel := by
  intro a ha L hL h P Pl hc hf
  haveI hL0 : NeZero L := ⟨by have := hL.2; omega⟩
  have hodd : Odd L := hL.1
  have hlift : Filter.Tendsto (fun n : ℕ => n * L) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_right n (Nat.pos_of_ne_zero (NeZero.ne L)))
      Filter.tendsto_id
  have hbig : ∀ᶠ n : ℕ in Filter.atTop, 2 ≤ n := Filter.eventually_ge_atTop 2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hlift.eventually hc.symm, hbig] with n hs h2 c c'
    haveI : NeZero n := ⟨by omega⟩
    rw [renormalizedKernel_eq_coarseKernel, renormalizedKernel_eq_coarseKernel]
    exact coarseKernel_comm hs c c'
  · obtain ⟨M, θ, hθ, hd⟩ := hf.exp_decay
    refine ⟨a * (1 + (5 * L) * (|M| * Real.exp (θ * (5 * L + 1)))), θ, hθ, ?_⟩
    filter_upwards [hd, hf.minimizer_and_pos, hbig] with n hd hr h2 c c'
    haveI : NeZero n := ⟨by omega⟩
    rw [renormalizedKernel_eq_coarseKernel, coarseKernel_eq hr.1, abs_mul, abs_of_pos ha]
    have h1 := abs_contourAverage_le_exp hodd hθ c.1 (fun b => hd b c) c'
    have h3 : |indicatorForm c c'| ≤ Real.exp (-(θ * _root_.YangMills.Construction.TorusFields.supDist c.1 c'.1)) := by
      by_cases e : c' = c
      · subst e
        simp [indicatorForm, _root_.YangMills.Construction.TorusFields.supDist_self]
      · simp only [indicatorForm, e, if_false, abs_zero]
        positivity
    calc a * |indicatorForm c c' - _root_.YangMills.Construction.FlatLinearization.contourAverage L (fun b => P n b c) c'|
        ≤ a * (|indicatorForm c c'| + |_root_.YangMills.Construction.FlatLinearization.contourAverage L (fun b => P n b c) c'|) :=
          mul_le_mul_of_nonneg_left (abs_sub _ _) ha.le
      _ ≤ a * (Real.exp (-(θ * _root_.YangMills.Construction.TorusFields.supDist c.1 c'.1)) +
            (5 * L) * (|M| * Real.exp (θ * (5 * L + 1))) * Real.exp (-(θ * _root_.YangMills.Construction.TorusFields.supDist c.1 c'.1))) :=
          mul_le_mul_of_nonneg_left (add_le_add h3 h1) ha.le
      _ = _ := by ring
  · filter_upwards [hf.translation_invariant, hf.minimizer_and_pos, hbig] with n hcar hr h2 u c c'
    haveI : NeZero n := ⟨by omega⟩
    rw [renormalizedKernel_eq_coarseKernel, renormalizedKernel_eq_coarseKernel, coarseKernel_eq hr.1,
      coarseKernel_eq hr.1]
    have hu : indicatorForm (c.1 + u, c.2) (c'.1 + u, c'.2) = indicatorForm c c' := by
      simp [indicatorForm, Prod.ext_iff]
    have hm : _root_.YangMills.Construction.FlatLinearization.contourAverage L (fun b => P n b (c.1 + u, c.2)) (c'.1 + u, c'.2) =
        _root_.YangMills.Construction.FlatLinearization.contourAverage L (fun b => P n b c) c' := by
      rw [contourAverage_eq_sum, contourAverage_eq_sum]
      congr 1
      refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun π _ => ?_
      have hb : SlopeCoefficient.blockCentreSite L (c'.1 + u) =
          SlopeCoefficient.blockCentreSite L c'.1 + SlopeCoefficient.blockCentreSite L u := by
        simp only [coarseCentre_eq_blockCentreSite, blockCentreSite_add]
      simp only
      rw [hb, ← formPathSum_translate]
      congr 1
      funext b
      exact hcar b c u
    rw [hu, hm]
  · filter_upwards [hlift.eventually hc.reflection_invariant, hf.minimizer_and_pos, hbig] with n hi hr h2 c c'
    haveI : NeZero n := ⟨by omega⟩
    rw [renormalizedKernel_eq_coarseKernel, renormalizedKernel_eq_coarseKernel, coarseKernel_eq hr.1,
      coarseKernel_eq hr.1, indicatorForm_reflect, minimizer_reflect h2 hodd hr.1 hr.2 hi c,
      contourAverage_reflect (fun b => P n b c), reflectedBond_reflectedBond]
  · filter_upwards [hlift.eventually hc.annihilates_gradients, hf.minimizer_and_pos, hbig] with n hg hr h2
    intro _ c φ
    set f : TorusSite (n * L) → ℝ := fun x => φ (parentBlock L x) with hf'
    have hoff : VanishesOnBlockTrees L
        (fun b : TorusBond (n * L) => f (b.1 + unitStep (n * L) b.2) - f b.1) := by
      intro b hb
      have e : parentBlock L (b.1 + unitStep (n * L) b.2) = parentBlock L b.1 := not_not.mp hb.1
      simp only [hf', e, sub_self]
    have key := sum_coarseKernel_mul_contourAverage_eq_zero hr.1 c _ hoff (fun b => hg b f)
    have hq : ∀ c' : TorusBond n,
        _root_.YangMills.Construction.FlatLinearization.contourAverage L (fun b : TorusBond (n * L) => f (b.1 + unitStep (n * L) b.2) - f b.1) c' =
        φ (c'.1 + unitStep n c'.2) - φ c'.1 := fun c' => by
      rw [contourAverage_gradient hodd f c']
      simp only [hf', parentBlock_blockCentreSite hodd]
    simp only [hq] at key
    simpa only [renormalizedKernel_eq_coarseKernel] using key
  · filter_upwards [hlift.eventually hc.annihilates_gradients, hlift.eventually hc.annihilates_constants,
      hf.minimizer_and_pos, hbig] with n hg hk' hr h2
    intro _ c ν
    have hLr : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
    set lam : TorusSite (n * L) → ℝ := fun x => -(L : ℝ)⁻¹ * (offsetFromCentre L x ν : ℝ) with hlam
    set dir : Fin 4 → ℝ := fun μ => if μ = ν then 1 else 0 with hdir
    set η : RealOneForm (n * L) := fun b =>
      (L : ℝ)⁻¹ * dir b.2 + (lam (b.1 + unitStep (n * L) b.2) - lam b.1) with hη
    have hoff : VanishesOnBlockTrees L η := by
      intro b hb
      have e := congrFun (offsetFromCentre_step h2 hodd b hb.1) ν
      simp only [hη, hlam, hdir, e, Pi.add_apply]
      by_cases hν : b.2 = ν
      · rw [hν]
        simp only [if_true, Pi.single_eq_same]
        push_cast
        ring
      · have h0 : (Pi.single b.2 1 : Fin 4 → ℤ) ν = 0 := Pi.single_eq_of_ne (Ne.symm hν) _
        rw [h0]
        simp only [hν, if_false, add_zero, mul_zero, zero_add, sub_self]
    have hk : ∀ b, ∑ b', h (n * L) b b' * η b' = 0 := by
      intro b
      have g1 := hg b lam
      have g2 := hk' b ν
      calc ∑ b', h (n * L) b b' * η b' =
          (L : ℝ)⁻¹ * ∑ c, h (n * L) b c * (if c.2 = ν then 1 else 0) +
            ∑ c, h (n * L) b c * (lam (c.1 + unitStep (n * L) c.2) - lam c.1) := by
            rw [Finset.mul_sum, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun c _ => by simp only [hη, hdir]; ring
        _ = 0 := by rw [g1, g2, mul_zero, add_zero]
    have key := sum_coarseKernel_mul_contourAverage_eq_zero hr.1 c η hoff hk
    have hq : ∀ c' : TorusBond n, _root_.YangMills.Construction.FlatLinearization.contourAverage L η c' = dir c'.2 := by
      intro c'
      have e : η = (L : ℝ)⁻¹ • (fun b : TorusBond (n * L) => dir b.2) +
          fun b : TorusBond (n * L) => lam (b.1 + unitStep (n * L) b.2) - lam b.1 := by
        funext b
        simp [hη]
      rw [← contourAverageLinear_apply, e, map_add, map_smul, contourAverageLinear_apply,
        contourAverageLinear_apply, contourAverage_directional hodd, contourAverage_gradient hodd lam c']
      simp only [hlam, offsetFromCentre_blockCentreSite hodd, Pi.zero_apply, smul_eq_mul]
      field_simp
      simp
    simp only [hq] at key
    simpa only [renormalizedKernel_eq_coarseKernel, hdir] using key
  · refine ⟨fun b c => a * ((if c = b then 1 else 0) - latticeContourAverage L (fun x => Pl x b) c),
      fun b c => ?_⟩
    have hT : Filter.Tendsto (fun n : ℕ => a * ((if c = b then (1 : ℝ) else 0) -
        latticeContourAverage L (fun x => P n (bondFrom 0 x) (bondFrom 0 b)) c)) Filter.atTop
        (𝓝 (a * ((if c = b then 1 else 0) - latticeContourAverage L (fun x => Pl x b) c))) := by
      refine Filter.Tendsto.const_mul a (Filter.Tendsto.const_sub _ ?_)
      unfold latticeContourAverage
      refine Filter.Tendsto.const_mul _ (tendsto_finset_sum _ fun g _ => tendsto_finset_sum _ fun π _ =>
        tendsto_latticeLineSum (fun x => hf.tendsto x b) _ _)
    refine hT.congr' ?_
    filter_upwards [hf.minimizer_and_pos, Filter.eventually_gt_atTop (max 1 (offsetNorm (c.1 - b.1)))]
      with n hr hn
    have hn1 : 1 < n := (le_max_left _ _).trans_lt hn
    have hn2 : offsetNorm (c.1 - b.1) < n := (le_max_right _ _).trans_lt hn
    haveI : NeZero n := ⟨by omega⟩
    rw [renormalizedKernel_eq_coarseKernel, coarseKernel_eq hr.1, contourAverage_bondFrom_zero,
      indicatorForm_bondFrom_zero b c hn2]
  · obtain ⟨κ₀, hκ₀, hfl⟩ := hc.curl_lower_bound
    obtain ⟨C, hC, hcurl⟩ := hCurl L hL
    refine ⟨1 / (128 / a + 2 * C / κ₀), by positivity, ?_⟩
    filter_upwards [hlift.eventually hfl, hcurl, hf.minimizer_and_pos, hbig] with n hfl hcurl hr h2
    intro _ B
    have hform : renormalizedKernel a L h P n = coarseKernel a L (h (n * L)) (P n) := by
      funext c c'
      exact renormalizedKernel_eq_coarseKernel a h P c c'
    rw [hform, kernelPairing_coarseKernel hr.1]
    set ξ : RealOneForm (n * L) := fun b => ∑ c, B c * P n b c with hξ
    set D : RealOneForm n := fun c => B c - _root_.YangMills.Construction.FlatLinearization.contourAverage L ξ c with hD
    set S : ℝ := ∑ c, D c ^ 2 with hS
    set H : ℝ := kernelPairing (h (n * L)) ξ ξ with hH
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun c _ => sq_nonneg _
    have e0 : B = fun c => D c + _root_.YangMills.Construction.FlatLinearization.contourAverage L ξ c := by
      funext c
      simp [hD]
    have h1 : curlEnergy B ≤
        2 * curlEnergy D + 2 * curlEnergy (fun c : TorusBond n => _root_.YangMills.Construction.FlatLinearization.contourAverage L ξ c) := by
      conv_lhs => rw [e0]
      exact curlEnergy_add_le _ _
    have h3 := curlEnergy_le_sum_sq D
    have h4 := hcurl ξ
    have h5 := hfl ξ
    have h6 := curlEnergy_nonneg ξ
    have hH0 : 0 ≤ H := (mul_nonneg hκ₀.le h6).trans h5
    have hA : 128 / a * a = 128 := div_mul_cancel₀ _ ha.ne'
    have hB : 2 * C / κ₀ * κ₀ = 2 * C := div_mul_cancel₀ _ hκ₀.ne'
    have hA0 : 0 ≤ 128 / a := by positivity
    have hB0 : 0 ≤ 2 * C / κ₀ := by positivity
    have hpos : 0 < 128 / a + 2 * C / κ₀ := by positivity
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hpos]
    have h7 : curlEnergy B ≤ 128 * S + 2 * C / κ₀ * H := by
      have h8 : 2 * C * curlEnergy ξ ≤ 2 * C / κ₀ * H := by
        calc 2 * C * curlEnergy ξ = 2 * C / κ₀ * (κ₀ * curlEnergy ξ) := by rw [← mul_assoc, hB]
          _ ≤ 2 * C / κ₀ * H := mul_le_mul_of_nonneg_left h5 hB0
      linarith
    have h9 : 0 ≤ 128 / a * H := mul_nonneg hA0 hH0
    have h10 : 0 ≤ 2 * C / κ₀ * (a * S) := mul_nonneg hB0 (mul_nonneg ha.le hS0)
    have e1 : (H + a * S) * (128 / a + 2 * C / κ₀) =
        128 / a * H + (128 / a * a) * S + 2 * C / κ₀ * H + 2 * C / κ₀ * (a * S) := by ring
    rw [e1, hA]
    linarith
end YangMills.Construction.RunningCouplingSlope
end
