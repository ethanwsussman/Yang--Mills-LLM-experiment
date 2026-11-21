import YangMills.Construction.ClusterExpansionOfAStep.SecondOrderOnMultiplesOfASideProof
import YangMills.Construction.ResponseInTheExpansion.ALocalFunctionIsQuadraticInTheCurvatureProof
import YangMills.Construction.ColdStepAtMirrorFrames.MirrorAgreesOnItsBoxProof
import YangMills.Construction.LawInAState.DecayOverATorusProof
import YangMills.Construction.ResponseInTheExpansion.FieldsOfOneColour
import YangMills.Construction.ResponseInTheExpansion.TheResponseContractsCurvature
import YangMills.Construction.ResponseInTheExpansion.TheResponseContractsCurvatureLocally
import YangMills.Construction.RunningCouplingSlope.TangentsOfTheLeastFieldProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace ResponseInTheExpansion.LocalContraction
open TorusFields
private def expLineSum (κ : ℝ) : ℝ := ∑' k : ℤ, Real.exp (-(κ * |(k : ℝ)|))
private theorem sum_zmod_le_expLineSum (m : ℕ) [NeZero m] {κ : ℝ} (hκ : 0 < κ) :
    ∑ x : ZMod m, Real.exp (-(κ * |((x.valMinAbs : ℤ) : ℝ)|)) ≤ expLineSum κ := by apply _root_.YangMills.DeltaSharedProofs.p502213 <;> assumption
private theorem exp_supDist_le_prod {m : ℕ} {κ : ℝ} (hκ : 0 < κ) (Z z : TorusSite m) :
    Real.exp (-(κ * (_root_.YangMills.Construction.TorusFields.supDist Z z : ℝ))) ≤
      ∏ i, Real.exp (-(κ / 4 * |(((Z i - z i).valMinAbs : ℤ) : ℝ)|)) := by
  rw [← Real.exp_sum]
  apply Real.exp_le_exp.mpr
  have hcoord : ∀ i, |(((Z i - z i).valMinAbs : ℤ) : ℝ)| ≤ (_root_.YangMills.Construction.TorusFields.supDist Z z : ℝ) := by
    intro i
    have hle : ((Z i - z i).valMinAbs).natAbs ≤ _root_.YangMills.Construction.TorusFields.supDist Z z :=
      Finset.le_sup (f := fun i => ((Z i - z i).valMinAbs).natAbs) (Finset.mem_univ i)
    have habs : |(((Z i - z i).valMinAbs : ℤ) : ℝ)| = (((Z i - z i).valMinAbs).natAbs : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [habs]
    exact_mod_cast hle
  have hsum : ∑ i : Fin 4, |(((Z i - z i).valMinAbs : ℤ) : ℝ)| ≤ 4 * (_root_.YangMills.Construction.TorusFields.supDist Z z : ℝ) := by
    calc _ ≤ ∑ _i : Fin 4, (_root_.YangMills.Construction.TorusFields.supDist Z z : ℝ) := Finset.sum_le_sum fun i _ => hcoord i
      _ = 4 * (_root_.YangMills.Construction.TorusFields.supDist Z z : ℝ) := by simp
  have hpull : ∑ i : Fin 4, -(κ / 4 * |(((Z i - z i).valMinAbs : ℤ) : ℝ)|) =
      -(κ / 4 * ∑ i : Fin 4, |(((Z i - z i).valMinAbs : ℤ) : ℝ)|) := by
    rw [Finset.mul_sum, Finset.sum_neg_distrib]
  rw [hpull]
  nlinarith
abbrev _root_.YangMills.SharedProofs.p58634 := @exp_supDist_le_prod
private theorem sum_sites_exp_le {m : ℕ} [NeZero m] {κ : ℝ} (hκ : 0 < κ) (Z : TorusSite m) :
    ∑ z : TorusSite m, Real.exp (-(κ * (_root_.YangMills.Construction.TorusFields.supDist Z z : ℝ))) ≤ expLineSum (κ / 4) ^ 4 := by apply _root_.YangMills.DeltaSharedProofs.p501803 <;> assumption
private theorem sum_bonds_exp_le {m : ℕ} [NeZero m] {κ : ℝ} (hκ : 0 < κ) (Z : TorusSite m) :
    ∑ c : TorusBond m, Real.exp (-(κ * (_root_.YangMills.Construction.TorusFields.supDist Z c.1 : ℝ))) ≤ 4 * expLineSum (κ / 4) ^ 4 := by
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have := sum_sites_exp_le hκ Z
  rw [← Finset.mul_sum]
  push_cast
  linarith
abbrev _root_.YangMills.DeltaSharedProofs.p3109 := @sum_bonds_exp_le
end ResponseInTheExpansion.LocalContraction
namespace ResponseInTheExpansion.LocalContraction
open TorusFields ColdStepAtMirrorFrames BlockAverages
private theorem reflectCoord_eq (m : ℕ) (c : ℤ) : ColdStepAtMirrorFrames.reflectCoord m c =
    if -(m : ℤ) ≤ c ∧ c ≤ m then c else if 0 < c then 2 * (m : ℤ) - c else -(2 * (m : ℤ)) - c := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ReflectionOnBox.reflectCoord_eq <;> assumption
private def foldValue (r : ℕ) (x : ZMod (4 * r)) : ℤ := ColdStepAtMirrorFrames.reflectCoord r x.valMinAbs
section Fold
variable {r : ℕ} [NeZero (4 * r)]
private theorem valMinAbs_bounds (x : ZMod (4 * r)) : -(2 * (r : ℤ)) < x.valMinAbs ∧ x.valMinAbs ≤ 2 * r := by
  have hmem := ZMod.valMinAbs_mem_Ioc x
  simp only [Set.mem_Ioc] at hmem
  push_cast at hmem
  omega
private theorem foldValue_bounds (x : ZMod (4 * r)) : -(r : ℤ) ≤ foldValue r x ∧ foldValue r x ≤ r := by
  have hb := valMinAbs_bounds x
  unfold foldValue
  rw [reflectCoord_eq]
  split_ifs <;> omega
private theorem valMinAbs_intCast_of_mem {e : ℤ} (h1 : -(2 * (r : ℤ)) < e) (h2 : e ≤ 2 * r) :
    ((e : ZMod (4 * r))).valMinAbs = e := by
  rw [ZMod.valMinAbs_spec]
  refine ⟨rfl, ?_⟩
  simp only [Set.mem_Ioc]
  push_cast
  omega
private theorem foldValue_intCast {e : ℤ} (h1 : -(r : ℤ) ≤ e) (h2 : e ≤ r) (hr : 1 ≤ r) :
    foldValue r (e : ZMod (4 * r)) = e := by
  unfold foldValue
  rw [valMinAbs_intCast_of_mem (by omega) (by omega), reflectCoord_eq, if_pos ⟨h1, h2⟩]
private theorem foldValue_add_one (hr : 1 ≤ r) (x : ZMod (4 * r)) :
    foldValue r (x + 1) = foldValue r x + 1 ∨ foldValue r (x + 1) = foldValue r x - 1 := by
  have hb := valMinAbs_bounds x
  have hx : x = ((x.valMinAbs : ℤ) : ZMod (4 * r)) := (ZMod.coe_valMinAbs x).symm
  set c := x.valMinAbs with hc
  by_cases hc2 : c + 1 ≤ 2 * r
  · have hsucc : (x + 1).valMinAbs = c + 1 := by
      have : x + 1 = ((c + 1 : ℤ) : ZMod (4 * r)) := by
        rw [hx]; push_cast; simp
      rw [this]
      exact valMinAbs_intCast_of_mem (by omega) hc2
    unfold foldValue
    rw [hsucc, ← hc, reflectCoord_eq, reflectCoord_eq]
    split_ifs <;> omega
  · have hc3 : c = 2 * r := by omega
    have hwrap : (x + 1).valMinAbs = -(2 * (r : ℤ)) + 1 := by
      have : x + 1 = ((-(2 * (r : ℤ)) + 1 : ℤ) : ZMod (4 * r)) := by
        have hzero : (((4 * r : ℕ) : ℤ) : ZMod (4 * r)) = 0 := by
          rw [Int.cast_natCast]; exact ZMod.natCast_self _
        have hshift : ((-(2 * (r : ℤ)) + 1 : ℤ) : ZMod (4 * r)) =
            ((c + 1 : ℤ) : ZMod (4 * r)) - (((4 * r : ℕ) : ℤ) : ZMod (4 * r)) := by
          rw [← Int.cast_sub]
          congr 1
          push_cast
          omega
        rw [hshift, hzero, sub_zero, hx]
        push_cast
        simp
      rw [this]
      exact valMinAbs_intCast_of_mem (by omega) (by omega)
    unfold foldValue
    rw [hwrap, ← hc, reflectCoord_eq, reflectCoord_eq]
    split_ifs <;> omega
end Fold
section Mirror
variable {n : ℕ} [NeZero n]
private def foldedOffsets (r : ℕ) (x : TorusSite (4 * r)) : Fin 4 → ℤ := fun l => foldValue r (x l)
private def mirrorExtension (r : ℕ) (Y : TorusSite n) (A : TorusBond n → ℝ) (c : TorusBond (4 * r)) : ℝ :=
  if foldValue r (c.1 c.2 + 1) = foldValue r (c.1 c.2) + 1 then A (Y + siteOfInt (foldedOffsets r c.1), c.2)
  else - A (Y + siteOfInt (foldedOffsets r (c.1 + TorusFields.unitStep (4 * r) c.2)), c.2)
variable {r : ℕ} [NeZero (4 * r)] (Y : TorusSite n) (A : TorusBond n → ℝ)
private theorem abs_mirrorExtension_le {sA : ℝ} (hA : ∀ b, |A b| ≤ sA) (c : TorusBond (4 * r)) :
    |mirrorExtension r Y A c| ≤ sA := by
  unfold mirrorExtension
  split_ifs
  · exact hA _
  · rw [abs_neg]; exact hA _
private theorem foldedOffsets_siteOfInt (hr : 1 ≤ r) {h : Fin 4 → ℤ} (hh : BlockAverages.WithinRadius r h) :
    foldedOffsets r (siteOfInt h) = h := by
  funext l
  have := abs_le.mp (hh l)
  exact foldValue_intCast this.1 this.2 hr
private theorem mirrorExtension_of_mem_box (hr : 1 ≤ r) {h : Fin 4 → ℤ} {k : Fin 4}
    (hb : BlockAverages.BondWithinRadius r (h, k)) :
    mirrorExtension r Y A (siteOfInt h, k) = A (Y + siteOfInt h, k) := by
  obtain ⟨h1, h2⟩ := hb
  have h2k : -(r : ℤ) ≤ h k + 1 ∧ h k + 1 ≤ r := by
    have := abs_le.mp (h2 k)
    simpa using this
  have hk := abs_le.mp (h1 k)
  have hstep : foldValue r ((siteOfInt h : TorusSite (4 * r)) k + 1) =
      foldValue r ((siteOfInt h : TorusSite (4 * r)) k) + 1 := by
    have hcast : (siteOfInt h : TorusSite (4 * r)) k + 1 = ((h k + 1 : ℤ) : ZMod (4 * r)) := by
      simp [siteOfInt]
    rw [hcast]
    show foldValue r ((h k + 1 : ℤ) : ZMod (4 * r)) = foldValue r ((h k : ℤ) : ZMod (4 * r)) + 1
    rw [foldValue_intCast h2k.1 h2k.2 hr, foldValue_intCast hk.1 hk.2 hr]
  unfold mirrorExtension
  simp only
  rw [if_pos hstep, foldedOffsets_siteOfInt hr h1]
private theorem abs_curl_mirrorExtension (hr : 1 ≤ r) {S : Finset (TorusSite n)}
    (hS : ∀ z, _root_.YangMills.Construction.TorusFields.supDist z Y ≤ r → z ∈ S) (x : TorusSite (4 * r)) {μ ν : Fin 4} (hμν : μ < ν) :
    ∃ w : TorusSite n, (w, μ, ν) ∈ plaquettesIn S ∧
      |WeightedResponses.curl (mirrorExtension r Y A) (x, μ, ν)| = |WeightedResponses.curl A (w, μ, ν)| := by
  have hne : μ ≠ ν := hμν.ne
  have hne' : ν ≠ μ := hne.symm
  let E := foldedOffsets r x
  let q : ℤ → ℤ → TorusSite n := fun s t => Y + siteOfInt (Function.update (Function.update E μ s) ν t)
  obtain ⟨a, ha0⟩ : ∃ a, a = foldValue r (x μ) := ⟨_, rfl⟩
  obtain ⟨b, hb0⟩ : ∃ b, b = foldValue r (x ν) := ⟨_, rfl⟩
  obtain ⟨a', ha1⟩ : ∃ a', a' = foldValue r (x μ + 1) := ⟨_, rfl⟩
  obtain ⟨b', hb1⟩ : ∃ b', b' = foldValue r (x ν + 1) := ⟨_, rfl⟩
  have hE : Function.update (Function.update E μ a) ν b = E := by
    funext l
    by_cases h2 : l = ν
    · subst h2; simp [E, foldedOffsets, hb0]
    · by_cases h1 : l = μ
      · subst h1; simp [h2, E, foldedOffsets, ha0]
      · simp [h1, h2]
  have f1 : foldedOffsets r (x + TorusFields.unitStep (4 * r) μ) = Function.update (Function.update E μ a') ν b := by
    funext l
    by_cases h2 : l = ν
    · subst h2; simp [foldedOffsets, hb0, TorusFields.unitStep, hne']
    · by_cases h1 : l = μ
      · subst h1; simp [h2, foldedOffsets, ha1, TorusFields.unitStep]
      · simp [h1, h2, E, foldedOffsets, TorusFields.unitStep]
  have f2 : foldedOffsets r (x + TorusFields.unitStep (4 * r) ν) = Function.update (Function.update E μ a) ν b' := by
    funext l
    by_cases h2 : l = ν
    · subst h2; simp [foldedOffsets, hb1, TorusFields.unitStep]
    · by_cases h1 : l = μ
      · subst h1; simp [h2, foldedOffsets, ha0, TorusFields.unitStep]
      · simp [h2, h1, E, foldedOffsets, TorusFields.unitStep]
  have f3 : foldedOffsets r (x + TorusFields.unitStep (4 * r) μ + TorusFields.unitStep (4 * r) ν) =
      Function.update (Function.update E μ a') ν b' := by
    funext l
    by_cases h2 : l = ν
    · subst h2; simp [foldedOffsets, hb1, TorusFields.unitStep, hne']
    · by_cases h1 : l = μ
      · subst h1; simp [h2, foldedOffsets, ha1, TorusFields.unitStep]
      · simp [h2, h1, E, foldedOffsets, TorusFields.unitStep]
  have hqμ : ∀ s t, q (s + 1) t = q s t + TorusFields.unitStep n μ := by
    intro s t
    simp only [q]
    rw [add_assoc]
    congr 1
    funext l
    by_cases h2 : l = ν
    · subst h2; simp [siteOfInt, TorusFields.unitStep, hne']
    · by_cases h1 : l = μ
      · subst h1; simp [siteOfInt, TorusFields.unitStep, h2]
      · simp [siteOfInt, TorusFields.unitStep, h1, h2]
  have hqν : ∀ s t, q s (t + 1) = q s t + TorusFields.unitStep n ν := by
    intro s t
    simp only [q]
    rw [add_assoc]
    congr 1
    funext l
    by_cases h2 : l = ν
    · subst h2; simp [siteOfInt, TorusFields.unitStep]
    · by_cases h1 : l = μ
      · subst h1; simp [siteOfInt, TorusFields.unitStep, h2]
      · simp [siteOfInt, TorusFields.unitStep, h1, h2]
  have hEb : ∀ l, -(r : ℤ) ≤ E l ∧ E l ≤ r := fun l => foldValue_bounds (x l)
  have hq : ∀ s t, (-(r : ℤ) ≤ s ∧ s ≤ r) → (-(r : ℤ) ≤ t ∧ t ≤ r) → q s t ∈ S := by
    intro s t hs ht
    apply hS
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
    refine _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le Y _ r fun l => ?_
    have : -(r : ℤ) ≤ (Function.update (Function.update E μ s) ν t) l ∧
        (Function.update (Function.update E μ s) ν t) l ≤ r := by
      by_cases h2 : l = ν
      · subst h2; simpa using ht
      · by_cases h1 : l = μ
        · subst h1; simpa [h2] using hs
        · simpa [h1, h2] using hEb l
    omega
  have m1 : mirrorExtension r Y A (x, μ) = if a' = a + 1 then A (q a b, μ) else - A (q a' b, μ) := by
    simp only [mirrorExtension, ← ha0, ← ha1, q, f1, hE]
    rfl
  have m2 : mirrorExtension r Y A (x + TorusFields.unitStep (4 * r) μ, ν) =
      if b' = b + 1 then A (q a' b, ν) else - A (q a' b', ν) := by
    have e1 : (x + TorusFields.unitStep (4 * r) μ) ν = x ν := by simp [TorusFields.unitStep, hne']
    simp only [mirrorExtension, e1, ← hb0, ← hb1, q, f1, f3]
  have m3 : mirrorExtension r Y A (x + TorusFields.unitStep (4 * r) ν, μ) =
      if a' = a + 1 then A (q a b', μ) else - A (q a' b', μ) := by
    have e1 : (x + TorusFields.unitStep (4 * r) ν) μ = x μ := by simp [TorusFields.unitStep, hne]
    have e2 : x + TorusFields.unitStep (4 * r) ν + TorusFields.unitStep (4 * r) μ =
        x + TorusFields.unitStep (4 * r) μ + TorusFields.unitStep (4 * r) ν := by abel
    simp only [mirrorExtension, e1, e2, ← ha0, ← ha1, q, f2, f3]
  have m4 : mirrorExtension r Y A (x, ν) = if b' = b + 1 then A (q a b, ν) else - A (q a b', ν) := by
    simp only [mirrorExtension, ← hb0, ← hb1, q, f2, hE]
    rfl
  have key : ∀ s t, WeightedResponses.curl A (q s t, μ, ν) =
      A (q s t, μ) + A (q (s + 1) t, ν) - A (q s (t + 1), μ) - A (q s t, ν) := by
    intro s t
    rw [hqμ, hqν]
    rfl
  have hmem : ∀ s t, (-(r : ℤ) ≤ s ∧ s + 1 ≤ r) → (-(r : ℤ) ≤ t ∧ t + 1 ≤ r) →
      (q s t, μ, ν) ∈ plaquettesIn S := by
    intro s t hs ht
    simp only [plaquettesIn, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hμν, fun z hz => ?_⟩
    simp only [plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact hq s t ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    · rw [← hqμ]; exact hq _ t ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    · rw [← hqν]; exact hq s _ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    · rw [← hqμ, ← hqν]; exact hq _ _ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  have hcurl : WeightedResponses.curl (mirrorExtension r Y A) (x, μ, ν) = mirrorExtension r Y A (x, μ) +
      mirrorExtension r Y A (x + TorusFields.unitStep (4 * r) μ, ν) -
      mirrorExtension r Y A (x + TorusFields.unitStep (4 * r) ν, μ) -
      mirrorExtension r Y A (x, ν) := rfl
  have aa : -(r : ℤ) ≤ a ∧ a ≤ r := ha0 ▸ foldValue_bounds (x μ)
  have ab : -(r : ℤ) ≤ b ∧ b ≤ r := hb0 ▸ foldValue_bounds (x ν)
  have aa' : -(r : ℤ) ≤ a' ∧ a' ≤ r := ha1 ▸ foldValue_bounds (x μ + 1)
  have ab' : -(r : ℤ) ≤ b' ∧ b' ≤ r := hb1 ▸ foldValue_bounds (x ν + 1)
  have sa : a' = a + 1 ∨ a' = a - 1 := by rw [ha0, ha1]; exact foldValue_add_one hr _
  have sb : b' = b + 1 ∨ b' = b - 1 := by rw [hb0, hb1]; exact foldValue_add_one hr _
  rw [hcurl, m1, m2, m3, m4]
  rcases sa with ha | ha <;> rcases sb with hb | hb
  · refine ⟨q a b, hmem a b (by omega) (by omega), ?_⟩
    simp only [if_pos ha, if_pos hb]
    rw [key, ha, hb]
  · have hb2 : b = b' + 1 := by omega
    refine ⟨q a b', hmem a b' (by omega) (by omega), ?_⟩
    have nb : ¬ b' = b + 1 := by omega
    simp only [if_pos ha, if_neg nb]
    rw [key, ha, hb2, ← abs_neg]
    congr 1
    ring
  · have ha2 : a = a' + 1 := by omega
    refine ⟨q a' b, hmem a' b (by omega) (by omega), ?_⟩
    have na : ¬ a' = a + 1 := by omega
    simp only [if_neg na, if_pos hb]
    rw [key, hb, ha2, ← abs_neg]
    congr 1
    ring
  · have ha2 : a = a' + 1 := by omega
    have hb2 : b = b' + 1 := by omega
    refine ⟨q a' b', hmem a' b' (by omega) (by omega), ?_⟩
    have na : ¬ a' = a + 1 := by omega
    have nb : ¬ b' = b + 1 := by omega
    simp only [if_neg na, if_neg nb]
    rw [key, ha2, hb2]
    congr 1
    ring
end Mirror
end ResponseInTheExpansion.LocalContraction
namespace ResponseInTheExpansion.LocalContraction
open TorusFields ColdStepAtMirrorFrames BlockAverages BlockAverages.SameOffsets
section Offsets
private theorem cellCentre_add_siteOfCoords {F : BlockFrame} (Y : F.Cell) (h : Fin 4 → ℤ) :
    cellCentre F.depth (Y + siteOfCoords F.top h) = siteAtOffset Y F.depth (scaleOffset F.blockSide h) := by apply _root_.YangMills.SharedProofs.p18452 <;> assumption
private def blockPlace (L : ℕ) (p : Fin 4 → ℤ) : Fin 4 → ℤ := p - scaleOffset L (CongruentBoxes.coarseOffset L p)
private theorem blockPlace_mem {L : ℕ} (hL : Odd L) (p : Fin 4 → ℤ) : blockPlace L p ∈ centredCube L := by apply _root_.YangMills.DeltaSharedProofs.p502368 <;> assumption
private theorem abs_coarseOffset_le {L : ℕ} (hL : Odd L) {c : ℤ} (hc : 0 ≤ c) {p : Fin 4 → ℤ} {i : Fin 4}
    (hp : |p i| ≤ c * L) : |CongruentBoxes.coarseOffset L p i| ≤ c := by apply _root_.YangMills.SharedProofs.p21677 <;> assumption
private theorem siteAtOffset_eq_cellCentre_add {F : BlockFrame} (Y : F.Cell) (p : Fin 4 → ℤ) :
    siteAtOffset Y F.depth p = cellCentre F.depth (Y + siteOfCoords F.top (CongruentBoxes.coarseOffset F.blockSide p)) +
      siteOfCoords F.depth (blockPlace F.blockSide p) := by apply _root_.YangMills.DeltaSharedProofs.p502588 <;> assumption
end Offsets
section Sites
variable {L u m : ℕ} [NeZero L] [NeZero m]
private theorem period_top_torusFrame (i : Fin 4) : (torusFrame L u m).period (torusFrame L u m).top i = m :=
  TorusFrame.period_torusFrame i
private theorem torusSiteInFrame_blockCentre_add (Y : TorusSite m) (p : Fin 4 → ℤ) :
    StepCosts.torusSiteInFrame (torusFrame L u m) (torusFrame L u m).depth
        (CongruentBoxes.blockCentre L Y + siteOfInt p : TorusSite (m * L)) =
      siteAtOffset (StepCosts.torusSiteInFrame (torusFrame L u m) (torusFrame L u m).top Y)
        (torusFrame L u m).depth p := by apply _root_.YangMills.SharedProofs.p4320 <;> assumption
private theorem torusSiteInFrame_top_add (Y : TorusSite m) (e : Fin 4 → ℤ) :
    StepCosts.torusSiteInFrame (torusFrame L u m) (torusFrame L u m).top (Y + siteOfInt e) =
      StepCosts.torusSiteInFrame (torusFrame L u m) (torusFrame L u m).top Y + siteOfCoords (torusFrame L u m).top e := by
  rw [TorusChain.torusSiteInFrame_add period_top_torusFrame, TorusChain.torusSiteInFrame_siteOfInt period_top_torusFrame]
private theorem cellSupDist_add_siteOfCoords_le (Y : TorusSite m) {e : Fin 4 → ℤ} {c : ℕ}
    (he : ∀ i, (e i).natAbs ≤ c) :
    cellSupDist (StepCosts.torusSiteInFrame (torusFrame L u m) (torusFrame L u m).top Y)
      (StepCosts.torusSiteInFrame (torusFrame L u m) (torusFrame L u m).top Y + siteOfCoords (torusFrame L u m).top e) ≤ c := by
  rw [← torusSiteInFrame_top_add, TorusChain.cellSupDist_torusSiteInFrame period_top_torusFrame]
  exact _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le Y e c he
end Sites
section Chain
variable {F : BlockFrame}
private theorem minimizingBondCoordinate_of_not_mem {a ρ : ℝ} {S : Finset F.Cell} {b : F.Site F.depth × Fin 4}
    (hb : b ∉ chordBonds S) (V : F.GaugeField F.top) : minimizingBondCoordinate a ρ S b V = 0 := by apply _root_.YangMills.SharedProofs.p70322 <;> assumption
private def coordSlope (F : BlockFrame) (a ρ : ℝ) (b : F.Site F.depth × Fin 4) (c : F.Site F.top × Fin 4) :
    imaginaryQuaternions :=
  bondDeriv (torusCoordinate a ρ b) (uniformField F F.top) ![c] ![WeightedResponses.unitGenerator]
private theorem coordSlope_of_not_mem {a ρ : ℝ} {b : F.Site F.depth × Fin 4} (hb : b ∉ chordBonds (finiteCells F))
    (c : F.Site F.top × Fin 4) : coordSlope F a ρ b c = 0 := by
  unfold coordSlope bondDeriv
  have hconst : (fun τ : Fin 1 → ℝ => torusCoordinate a ρ b
      (leftTranslate (ColdStepAtMirrorFrames.bondSpread ![c] ![WeightedResponses.unitGenerator] τ)
        (uniformField F F.top))) = fun _ => 0 := by
    funext τ
    exact minimizingBondCoordinate_of_not_mem hb _
  rw [hconst, iteratedFDeriv_fun_zero]
  rfl
private theorem norm_unitGenerator : ‖((WeightedResponses.unitGenerator : imaginaryQuaternions) : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.ResponseInTheExpansion.SingleColourFields.norm_unitGenerator <;> assumption
private theorem areUnitVectors_unitGenerator : AreUnitVectors ![WeightedResponses.unitGenerator] := by
  intro l
  fin_cases l
  exact norm_unitGenerator
private theorem abs_re_mul_unitGenerator_le (q : ℍ[ℝ]) :
    |(q * ((WeightedResponses.unitGenerator : imaginaryQuaternions) : ℍ[ℝ])).re| ≤ ‖q‖ := by
  have h : ∀ x : ℍ[ℝ], |x.re| ≤ ‖x‖ := by
    intro x
    apply abs_le_of_sq_le_sq _ (norm_nonneg x)
    rw [pow_two ‖x‖, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
    nlinarith [sq_nonneg x.imI, sq_nonneg x.imJ, sq_nonneg x.imK]
  calc _ ≤ ‖q * ((WeightedResponses.unitGenerator : imaginaryQuaternions) : ℍ[ℝ])‖ := h _
    _ = ‖q‖ := by rw [norm_mul, norm_unitGenerator, mul_one]
open Classical in
private theorem minimizerResponse_eq (a ρ : ℝ) (b : F.Site F.depth × Fin 4) (c : F.Site F.top × Fin 4) :
    minimizerResponse (F := F) a ρ c WeightedResponses.unitGenerator b.1 b.2 =
      - (((coordSlope F a ρ b c : imaginaryQuaternions) : ℍ[ℝ]) *
          ((WeightedResponses.unitGenerator : imaginaryQuaternions) : ℍ[ℝ])).re +
        if IsCrossingBond b ∧ enclosingCell b.1 = c.1 ∧ b.2 = c.2 then 1 else 0 := rfl
private theorem bondListDistance_single (Y : F.Cell) (c : F.Site F.top × Fin 4) :
    bondListDistance Y ![c] = cellSupDist Y c.1 := by
  simp [bondListDistance]
private theorem cellSupDist_self' (Y : F.Cell) : cellSupDist Y Y = 0 := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_self <;> assumption
variable {a ρ δ lam σA cg : ℝ} {N : ℕ → ℝ} {L : ℕ}
private theorem chain_at_flat (hc : ColdChain.ColdChainConstants a δ L lam ρ σA cg N) {u m : ℕ} [NeZero m] (hm : 64 ≤ m) :
    HasRegularCoordinates a δ ρ N (finiteCells (torusFrame L u m)) (BlockAverages.flatTopField) ∧
    ∀ (m' : ℕ) [NeZero m'], 64 ≤ m' → ∀ (Y : (torusFrame L u m).Cell) (Y' : (torusFrame L u m').Cell) (r : ℕ),
      AgreeOnBall (finiteCells (torusFrame L u m)) BlockAverages.flatTopField
        (finiteCells (torusFrame L u m')) BlockAverages.flatTopField Y Y' r →
      HasComparableCoordinates a δ ρ σA N (finiteCells (torusFrame L u m)) BlockAverages.flatTopField
        (finiteCells (torusFrame L u m')) BlockAverages.flatTopField Y Y' r := by apply _root_.YangMills.SharedProofs.p11303 <;> assumption
private theorem norm_coordSlope_le (hc : ColdChain.ColdChainConstants a δ L lam ρ σA cg N) {u m : ℕ} [NeZero m]
    (hm : 64 ≤ m) (b : (torusFrame L u m).Site (torusFrame L u m).depth × Fin 4)
    (c : (torusFrame L u m).Site (torusFrame L u m).top × Fin 4) :
    ‖coordSlope (torusFrame L u m) a ρ b c‖ ≤ N 1 * Real.exp (-δ * (cellSupDist (enclosingCell b.1) c.1 : ℝ)) := by
  have hN : 0 < N 1 := hc.2.2.2.2.2.2.2.1 1
  by_cases hb : b ∈ chordBonds (finiteCells (torusFrame L u m))
  · have h := ((chain_at_flat hc (u := u) hm).1 b hb).2 1 ![c] ![WeightedResponses.unitGenerator] le_rfl
      areUnitVectors_unitGenerator
    rw [bondListDistance_single] at h
    exact h
  · rw [coordSlope_of_not_mem hb, norm_zero]
    positivity
end Chain
section Compare
variable {a ρ δ lam σA cg : ℝ} {N : ℕ → ℝ} {L : ℕ}
private theorem siteAtOffset_mem_sitesOfCells {F : BlockFrame} (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (Y : F.Cell) (p : Fin 4 → ℤ) :
    siteAtOffset Y F.depth p ∈ sitesOfCells (finiteCells F) F.depth := by apply _root_.YangMills.SharedProofs.p15166 <;> assumption
private theorem isAxialTreeBond_cellCentre_add_iff {F : BlockFrame} (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (z : F.Cell) {o : Fin 4 → ℤ} (ho : o ∈ centredCube F.blockSide) (i : Fin 4) :
    IsAxialTreeBond ((cellCentre F.depth z + siteOfCoords F.depth o : F.Site F.depth), i) ↔
      ¬ o i = ColdStepAtMirrorFrames.BlockOffsets.halfSide F.blockSide ∧ ∀ l, i < l → o l = 0 := by
  unfold IsAxialTreeBond
  rw [ColdStepAtMirrorFrames.BlockOffsets.isCrossingBond_iff hL hs z o ho i]
  simp only [ColdStepAtMirrorFrames.BlockOffsets.cellOffset_offset hL hs z o ho]
private theorem siteOfCoords_top_injective {u m : ℕ} [NeZero m] {h e : Fin 4 → ℤ} (hh : ∀ i, 2 * |h i| < m)
    (he : ∀ i, 2 * |e i| < m)
    (hq : (siteOfCoords (torusFrame L u m).top h : (torusFrame L u m).Cell) = siteOfCoords (torusFrame L u m).top e) :
    h = e := by
  funext i
  have h1 := congrArg ZMod.valMinAbs (congrFun hq i)
  have e1 : ((siteOfCoords (torusFrame L u m).top h : (torusFrame L u m).Cell) i).valMinAbs = h i :=
    BlockAverages.valMinAbs_intCast_of_small (Or.inr (by rw [TorusFrame.period_torusFrame]; exact hh i))
  have e2 : ((siteOfCoords (torusFrame L u m).top e : (torusFrame L u m).Cell) i).valMinAbs = e i :=
    BlockAverages.valMinAbs_intCast_of_small (Or.inr (by rw [TorusFrame.period_torusFrame]; exact he i))
  rw [← e1, ← e2]
  exact h1
private theorem crossing_term_iff {u m : ℕ} [NeZero m] (hodd : Odd L) (hm : 64 ≤ m) (Y : (torusFrame L u m).Cell)
    {p e : Fin 4 → ℤ} (hp : ∀ i, 2 * |CongruentBoxes.coarseOffset L p i| < m) (he : ∀ i, 2 * |e i| < m) (i k : Fin 4) :
    (IsCrossingBond ((siteAtOffset Y (torusFrame L u m).depth p, i) :
        (torusFrame L u m).Site (torusFrame L u m).depth × Fin 4) ∧
      enclosingCell (siteAtOffset Y (torusFrame L u m).depth p) = Y + siteOfCoords (torusFrame L u m).top e ∧ i = k) ↔
    (blockPlace L p i = ColdStepAtMirrorFrames.BlockOffsets.halfSide L ∧ CongruentBoxes.coarseOffset L p = e ∧ i = k) := by
  have hs : ∀ i, 2 ≤ (torusFrame L u m).extent i := fun _ => (show 2 ≤ m by omega)
  have hLo : Odd (torusFrame L u m).blockSide := hodd
  have ho : blockPlace L p ∈ centredCube (torusFrame L u m).blockSide := blockPlace_mem hodd p
  rw [siteAtOffset_eq_cellCentre_add Y p]
  have hcell := ColdStepAtMirrorFrames.BlockOffsets.enclosingCell_offset hLo hs
    (Y + siteOfCoords (torusFrame L u m).top (CongruentBoxes.coarseOffset L p)) (blockPlace L p) ho
  have hcr := ColdStepAtMirrorFrames.BlockOffsets.isCrossingBond_iff hLo hs
    (Y + siteOfCoords (torusFrame L u m).top (CongruentBoxes.coarseOffset L p)) (blockPlace L p) ho i
  show (IsCrossingBond (cellCentre (torusFrame L u m).depth
        (Y + siteOfCoords (torusFrame L u m).top (CongruentBoxes.coarseOffset L p)) +
      siteOfCoords (torusFrame L u m).depth (blockPlace L p), i) ∧
      enclosingCell (cellCentre (torusFrame L u m).depth
        (Y + siteOfCoords (torusFrame L u m).top (CongruentBoxes.coarseOffset L p)) +
      siteOfCoords (torusFrame L u m).depth (blockPlace L p)) = _ ∧ _) ↔ _
  rw [hcr, hcell]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, siteOfCoords_top_injective hp he (add_left_cancel h2), h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, by rw [h2], h3⟩
private theorem mem_chordBonds_iff {F : BlockFrame} {S : Finset F.Cell} {b : F.Site F.depth × Fin 4} :
    b ∈ chordBonds S ↔ b ∈ innerBonds S F.depth ∧ ¬ IsAxialTreeBond b := by apply _root_.YangMills.Construction.BlockAverages.ChartFloor.mem_chordBonds_iff <;> assumption
private theorem responseKernel_blockCentre_add (a ρ : ℝ) [NeZero L] {u m : ℕ} [NeZero m] (Y : TorusSite m)
    (p e : Fin 4 → ℤ) (i k : Fin 4) :
    WeightedResponses.responseKernel a ρ L u (CongruentBoxes.blockCentre L Y + siteOfInt p, i) (Y + siteOfInt e, k) =
      minimizerResponse (F := torusFrame L u m) a ρ
        (StepCosts.torusSiteInFrame (torusFrame L u m) (torusFrame L u m).top Y +
          siteOfCoords (torusFrame L u m).top e, k) WeightedResponses.unitGenerator
        (siteAtOffset (StepCosts.torusSiteInFrame (torusFrame L u m) (torusFrame L u m).top Y)
          (torusFrame L u m).depth p) i := by
  unfold WeightedResponses.responseKernel
  simp only []
  rw [torusSiteInFrame_blockCentre_add, torusSiteInFrame_top_add]
private theorem coordSlope_eq_mixed {F : BlockFrame} (a ρ : ℝ) (b : F.Site F.depth × Fin 4) (c : F.Site F.top × Fin 4) :
    ((coordSlope F a ρ b c : imaginaryQuaternions) : ℍ[ℝ]) =
      ((mixedBondDerivative (minimizingBondCoordinate a ρ (finiteCells F) b) BlockAverages.flatTopField ![c]
        ![WeightedResponses.unitGenerator] : imaginaryQuaternions) : ℍ[ℝ]) := rfl
private theorem abs_single_le_one (i j : Fin 4) : |(Pi.single i 1 : Fin 4 → ℤ) j| ≤ 1 := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryInvariance.abs_single_one_le <;> assumption
private theorem coordSlope_compare [NeZero L] (hc : ColdChain.ColdChainConstants a δ L lam ρ σA cg N) (hodd : Odd L)
    {u n n' r : ℕ} [NeZero n] [NeZero n']
    (hn : 64 ≤ n) (hn' : 64 ≤ n') (hr : 16 ≤ r) (h2 : 2 * r + 2 < n) (h2' : 2 * r + 2 < n')
    (Y : TorusSite n) (Y' : TorusSite n') {p : Fin 4 → ℤ} (hp : ∀ i, |p i| ≤ 2 * (L : ℤ)) (i : Fin 4)
    {e : Fin 4 → ℤ} {k : Fin 4} (he : BlockAverages.BondWithinRadius r (e, k)) :
    ‖((coordSlope (torusFrame L u n) a ρ
        (siteAtOffset (StepCosts.torusSiteInFrame (torusFrame L u n) (torusFrame L u n).top Y) (torusFrame L u n).depth p, i)
        (StepCosts.torusSiteInFrame (torusFrame L u n) (torusFrame L u n).top Y + siteOfCoords (torusFrame L u n).top e, k) :
          imaginaryQuaternions) : ℍ[ℝ]) -
      ((coordSlope (torusFrame L u n') a ρ
        (siteAtOffset (StepCosts.torusSiteInFrame (torusFrame L u n') (torusFrame L u n').top Y') (torusFrame L u n').depth p, i)
        (StepCosts.torusSiteInFrame (torusFrame L u n') (torusFrame L u n').top Y' + siteOfCoords (torusFrame L u n').top e, k) :
          imaginaryQuaternions) : ℍ[ℝ])‖ ≤
      N 1 * Real.exp (-δ * ((r : ℝ) - 2)) := by
  have hδ : 0 < δ := hc.1
  have hN : 0 < N 1 := hc.2.2.2.2.2.2.2.1 1
  have hs : ∀ i, 2 ≤ (torusFrame L u n).extent i := fun _ => (show 2 ≤ n by omega)
  have hs' : ∀ i, 2 ≤ (torusFrame L u n').extent i := fun _ => (show 2 ≤ n' by omega)
  have hLo : Odd (torusFrame L u n).blockSide := hodd
  have hLo' : Odd (torusFrame L u n').blockSide := hodd
  obtain ⟨Yc, hYc⟩ : ∃ Yc, Yc = StepCosts.torusSiteInFrame (torusFrame L u n) (torusFrame L u n).top Y := ⟨_, rfl⟩
  obtain ⟨Yd, hYd⟩ : ∃ Yd, Yd = StepCosts.torusSiteInFrame (torusFrame L u n') (torusFrame L u n').top Y' := ⟨_, rfl⟩
  rw [← hYc, ← hYd]
  obtain ⟨h, hh0⟩ : ∃ h, h = CongruentBoxes.coarseOffset L p := ⟨_, rfl⟩
  obtain ⟨o, ho0⟩ : ∃ o, o = blockPlace L p := ⟨_, rfl⟩
  have ho : o ∈ centredCube L := ho0 ▸ blockPlace_mem hodd p
  have hh : ∀ i, |h i| ≤ 2 := fun i => by
    rw [hh0]
    exact abs_coarseOffset_le hodd (by norm_num) (hp i)
  have hX : siteAtOffset Yc (torusFrame L u n).depth p = (fineBondAt Yc h o i).1 := by
    rw [hh0, ho0]
    exact siteAtOffset_eq_cellCentre_add Yc p
  have hX' : siteAtOffset Yd (torusFrame L u n').depth p = (fineBondAt Yd h o i).1 := by
    rw [hh0, ho0]
    exact siteAtOffset_eq_cellCentre_add Yd p
  have hB : (siteAtOffset Yc (torusFrame L u n).depth p, i) = fineBondAt Yc h o i := by rw [hX]; rfl
  have hB' : (siteAtOffset Yd (torusFrame L u n').depth p, i) = fineBondAt Yd h o i := by rw [hX']; rfl
  rw [hB, hB']
  have hEe : (fineBondAt Yc h o i : (torusFrame L u n).Site (torusFrame L u n).depth × Fin 4) =
      (cellCentre (torusFrame L u n).depth (Yc + siteOfCoords (torusFrame L u n).top h) +
        siteOfCoords (torusFrame L u n).depth o, i) := rfl
  have hEe' : (fineBondAt Yd h o i : (torusFrame L u n').Site (torusFrame L u n').depth × Fin 4) =
      (cellCentre (torusFrame L u n').depth (Yd + siteOfCoords (torusFrame L u n').top h) +
        siteOfCoords (torusFrame L u n').depth o, i) := rfl
  have hbound : 0 ≤ N 1 * Real.exp (-δ * ((r : ℝ) - 2)) := by positivity
  by_cases ht : IsAxialTreeBond (fineBondAt Yc h o i)
  · have ht' : IsAxialTreeBond (fineBondAt Yd h o i) := by
      rw [hEe'] at *
      rw [hEe] at ht
      exact (isAxialTreeBond_cellCentre_add_iff hLo' hs' _ ho i).mpr
        ((isAxialTreeBond_cellCentre_add_iff hLo hs _ ho i).mp ht)
    have off : fineBondAt Yc h o i ∉ chordBonds (finiteCells (torusFrame L u n)) :=
      fun hm => (mem_chordBonds_iff.mp hm).2 ht
    have off' : fineBondAt Yd h o i ∉ chordBonds (finiteCells (torusFrame L u n')) :=
      fun hm => (mem_chordBonds_iff.mp hm).2 ht'
    rw [coordSlope_of_not_mem off, coordSlope_of_not_mem off']
    simpa using hbound
  · have hmem : fineBondAt Yc h o i ∈ chordBonds (finiteCells (torusFrame L u n)) := by
      refine mem_chordBonds_iff.mpr ⟨?_, ht⟩
      simp only [innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
      rw [← hX, siteAtOffset_add_unitStep]
      exact ⟨siteAtOffset_mem_sitesOfCells hLo hs Yc p, siteAtOffset_mem_sitesOfCells hLo hs Yc _⟩
    have hag : AgreeOnBall (finiteCells (torusFrame L u n)) BlockAverages.flatTopField
        (finiteCells (torusFrame L u n')) BlockAverages.flatTopField Yc Yd r :=
      ⟨fun _ => Or.inr h2, fun _ => Or.inr h2', fun _ => by
        simp [ColdStepAtMirrorFrames.BlockOffsets.mem_finiteCells hs,
          ColdStepAtMirrorFrames.BlockOffsets.mem_finiteCells hs'], fun _ _ => rfl⟩
    have hloc := (chain_at_flat hc (u := u) hn).2 n' hn' Yc Yd r hag
    have hbox : BlockAverages.WithinRadius r h := fun i => by
      have := hh i
      have : (2 : ℤ) ≤ r := by omega
      omega
    have hnext : cellSupDist Yc (enclosingCell ((fineBondAt Yc h o i).1 + BlockAverages.unitStep (torusFrame L u n).depth i)) ≤ r := by
      rw [← hX, siteAtOffset_add_unitStep, siteAtOffset_eq_cellCentre_add Yc (p + LatticeFractionalIntegration.basisVector i),
        ColdStepAtMirrorFrames.BlockOffsets.enclosingCell_offset hLo hs _ _ (blockPlace_mem hLo _), hYc]
      refine le_trans (cellSupDist_add_siteOfCoords_le Y (c := 3) fun j => ?_) (by omega)
      have hb : |(p + LatticeFractionalIntegration.basisVector i) j| ≤ 3 * (L : ℤ) := by
        have h1 := hp j
        have h2 : |(LatticeFractionalIntegration.basisVector i : Fin 4 → ℤ) j| ≤ 1 := abs_single_le_one i j
        have h3 : (1 : ℤ) ≤ L := by exact_mod_cast hodd.pos
        calc |(p + LatticeFractionalIntegration.basisVector i) j|
            ≤ |p j| + |(LatticeFractionalIntegration.basisVector i : Fin 4 → ℤ) j| := abs_add_le _ _
          _ ≤ 3 * (L : ℤ) := by omega
      have := abs_le.mp (abs_coarseOffset_le hodd (c := 3) (by norm_num) hb)
      show (CongruentBoxes.coarseOffset L (p + LatticeFractionalIntegration.basisVector i) j).natAbs ≤ 3
      omega
    have hmain := (hloc h o i ho hmem hbox hnext).2 1 ![(e, k)] ![WeightedResponses.unitGenerator] le_rfl
      (fun l => by fin_cases l; exact he) areUnitVectors_unitGenerator
    have hbs : offsetBonds Yc ![(e, k)] = ![(Yc + siteOfCoords (torusFrame L u n).top e, k)] := by
      funext l; fin_cases l; rfl
    have hbs' : offsetBonds Yd ![(e, k)] = ![(Yd + siteOfCoords (torusFrame L u n').top e, k)] := by
      funext l; fin_cases l; rfl
    rw [hbs, hbs'] at hmain
    rw [coordSlope_eq_mixed, coordSlope_eq_mixed]
    refine le_trans hmain ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hN.le
    have hcd : cellSupDist Yc (enclosingCell (fineBondAt Yc h o i).1) ≤ 2 := by
      rw [← hX, siteAtOffset_eq_cellCentre_add Yc p,
        ColdStepAtMirrorFrames.BlockOffsets.enclosingCell_offset hLo hs _ _ (blockPlace_mem hLo _), hYc]
      refine cellSupDist_add_siteOfCoords_le Y (c := 2) fun j => ?_
      have := hh j
      rw [hh0] at this
      have := abs_le.mp this
      show (CongruentBoxes.coarseOffset L p j).natAbs ≤ 2
      omega
    have hcd' : (cellSupDist Yc (enclosingCell (fineBondAt Yc h o i).1) : ℝ) ≤ 2 := by exact_mod_cast hcd
    nlinarith
private theorem abs_responseKernel_le [NeZero L] (hc : ColdChain.ColdChainConstants a δ L lam ρ σA cg N) {u m : ℕ}
    [NeZero m] (hm : 64 ≤ m) (b : TorusBond (m * L)) (c : TorusBond m) :
    |WeightedResponses.responseKernel a ρ L u b c| ≤
      (N 1 + 1) * Real.exp (-δ * (_root_.YangMills.Construction.TorusFields.supDist (TorusLumps.parentBlock L b.1) c.1 : ℝ)) := by
  have : NeZero (m * (torusFrame L u m).blockSide) := inferInstanceAs (NeZero (m * L))
  have hcell : enclosingCell (StepCosts.torusSiteInFrame (torusFrame L u m) (torusFrame L u m).depth b.1) =
      StepCosts.torusSiteInFrame (torusFrame L u m) (torusFrame L u m).top (TorusLumps.parentBlock L b.1) :=
    TopLevelSites.enclosingCell_torusSiteInFrame (F := torusFrame L u m) (n := m) (fun _ => rfl) b.1
  have hd : cellSupDist (enclosingCell (StepCosts.torusSiteInFrame (torusFrame L u m) (torusFrame L u m).depth b.1))
      (StepCosts.torusSiteInFrame (torusFrame L u m) (torusFrame L u m).top c.1) =
        _root_.YangMills.Construction.TorusFields.supDist (TorusLumps.parentBlock L b.1) c.1 := by
    rw [hcell, TorusChain.cellSupDist_torusSiteInFrame period_top_torusFrame]
  have hs := norm_coordSlope_le (a := a) (ρ := ρ) hc (u := u) hm
    (StepCosts.torusSiteInFrame (torusFrame L u m) (torusFrame L u m).depth b.1, b.2)
    (StepCosts.torusSiteInFrame (torusFrame L u m) (torusFrame L u m).top c.1, c.2)
  simp only [hd] at hs
  have hr := minimizerResponse_eq (F := torusFrame L u m) a ρ
    (StepCosts.torusSiteInFrame (torusFrame L u m) (torusFrame L u m).depth b.1, b.2)
    (StepCosts.torusSiteInFrame (torusFrame L u m) (torusFrame L u m).top c.1, c.2)
  have hE : 0 < Real.exp (-δ * (_root_.YangMills.Construction.TorusFields.supDist (TorusLumps.parentBlock L b.1) c.1 : ℝ)) := Real.exp_pos _
  unfold WeightedResponses.responseKernel
  refine (congrArg abs hr).le.trans ?_
  refine (abs_add_le _ _).trans ?_
  rw [add_mul, one_mul]
  refine add_le_add ?_ ?_
  · rw [abs_neg]
    exact (abs_re_mul_unitGenerator_le _).trans hs
  · split_ifs with hq
    · have h0 : _root_.YangMills.Construction.TorusFields.supDist (TorusLumps.parentBlock L b.1) c.1 = 0 := by
        rw [← hd]
        have : enclosingCell (StepCosts.torusSiteInFrame (torusFrame L u m) (torusFrame L u m).depth b.1) =
            StepCosts.torusSiteInFrame (torusFrame L u m) (torusFrame L u m).top c.1 := hq.2.1
        rw [this]
        exact cellSupDist_self' _
      rw [h0]
      simp
    · simpa using hE.le
abbrev _root_.YangMills.SharedProofs.p72842 := @abs_responseKernel_le
private theorem responseKernel_compare [NeZero L] (hc : ColdChain.ColdChainConstants a δ L lam ρ σA cg N) (hodd : Odd L)
    {u n n' r : ℕ} [NeZero n] [NeZero n'] (hn : 64 ≤ n) (hn' : 64 ≤ n') (hr : 16 ≤ r) (h2 : 2 * r + 2 < n)
    (h2' : 2 * r + 2 < n') (Y : TorusSite n) (Y' : TorusSite n') {p : Fin 4 → ℤ} (hp : ∀ i, |p i| ≤ 2 * (L : ℤ))
    (i : Fin 4) {e : Fin 4 → ℤ} {k : Fin 4} (he : BlockAverages.BondWithinRadius r (e, k)) :
    |WeightedResponses.responseKernel a ρ L u (CongruentBoxes.blockCentre L Y + siteOfInt p, i) (Y + siteOfInt e, k) -
      WeightedResponses.responseKernel a ρ L u (CongruentBoxes.blockCentre L Y' + siteOfInt p, i) (Y' + siteOfInt e, k)| ≤
      N 1 * Real.exp (-δ * ((r : ℝ) - 2)) := by
  have hsl := coordSlope_compare (a := a) (ρ := ρ) hc hodd (u := u) hn hn' hr h2 h2' Y Y' hp i he
  rw [responseKernel_blockCentre_add, responseKernel_blockCentre_add]
  obtain ⟨Yc, hYc⟩ : ∃ Yc, Yc = StepCosts.torusSiteInFrame (torusFrame L u n) (torusFrame L u n).top Y := ⟨_, rfl⟩
  obtain ⟨Yd, hYd⟩ : ∃ Yd, Yd = StepCosts.torusSiteInFrame (torusFrame L u n') (torusFrame L u n').top Y' := ⟨_, rfl⟩
  rw [← hYc, ← hYd] at hsl ⊢
  have r1 := minimizerResponse_eq (F := torusFrame L u n) a ρ (siteAtOffset Yc (torusFrame L u n).depth p, i)
    (Yc + siteOfCoords (torusFrame L u n).top e, k)
  have r2 := minimizerResponse_eq (F := torusFrame L u n') a ρ (siteAtOffset Yd (torusFrame L u n').depth p, i)
    (Yd + siteOfCoords (torusFrame L u n').top e, k)
  have hb : ∀ j, |CongruentBoxes.coarseOffset L p j| ≤ 2 := fun j => abs_coarseOffset_le hodd (by norm_num) (hp j)
  have hc1 := crossing_term_iff (u := u) hodd hn Yc (p := p) (e := e)
    (fun j => by have := hb j; omega)
    (fun j => by have := he.1 j; simp only at this; omega) i k
  have hc2 := crossing_term_iff (u := u) hodd hn' Yd (p := p) (e := e)
    (fun j => by have := hb j; omega)
    (fun j => by have := he.1 j; simp only at this; omega) i k
  have hcond := hc1.trans hc2.symm
  simp only at r1 r2
  rw [r1, r2]
  have e1 : ∀ (x y : ℍ[ℝ]) (t t' : ℝ), t = t' →
      (-(x * ((WeightedResponses.unitGenerator : imaginaryQuaternions) : ℍ[ℝ])).re + t) -
      (-(y * ((WeightedResponses.unitGenerator : imaginaryQuaternions) : ℍ[ℝ])).re + t') =
        -((x - y) * ((WeightedResponses.unitGenerator : imaginaryQuaternions) : ℍ[ℝ])).re := by
    intro x y t t' ht
    rw [sub_mul, Quaternion.re_sub, ht]
    ring
  rw [e1 _ _ _ _ (by
    split_ifs with q1 q2 q2
    · rfl
    · exact absurd (hcond.mp q1) q2
    · exact absurd (hcond.mpr q2) q1
    · rfl), abs_neg]
  exact (abs_re_mul_unitGenerator_le _).trans hsl
end Compare
end ResponseInTheExpansion.LocalContraction
namespace ResponseInTheExpansion
open TorusFields ColdStepAtMirrorFrames BlockAverages BlockAverages.SameOffsets
namespace LocalContraction
section Split
open Classical in
private def boxBondOffsets (r : ℕ) : Finset ((Fin 4 → ℤ) × Fin 4) :=
  ((Fintype.piFinset fun _ => Finset.Icc (-(r : ℤ)) r) ×ˢ Finset.univ).filter
    fun b => BlockAverages.BondWithinRadius r b
private theorem mem_boxBondOffsets {r : ℕ} {b : (Fin 4 → ℤ) × Fin 4} :
    b ∈ boxBondOffsets r ↔ BlockAverages.BondWithinRadius r b := by apply _root_.YangMills.Construction.AbelianSecondOrder.mem_offsetBoxBonds <;> assumption
variable {m : ℕ} [NeZero m]
private def bondAtOffset (Y : TorusSite m) (h : (Fin 4 → ℤ) × Fin 4) : TorusBond m := (Y + siteOfInt h.1, h.2)
private theorem bondAtOffset_injOn {r : ℕ} (hm : 2 * r < m) (Y : TorusSite m) :
    Set.InjOn (bondAtOffset Y) (boxBondOffsets r : Set ((Fin 4 → ℤ) × Fin 4)) := by
  rintro ⟨h, i⟩ hh ⟨h', i'⟩ hh' heq
  have hb := (mem_boxBondOffsets.mp hh).1
  have hb' := (mem_boxBondOffsets.mp hh').1
  have e1 : (siteOfInt h : TorusSite m) = siteOfInt h' := add_left_cancel (congrArg Prod.fst heq)
  have e2 : i = i' := congrArg Prod.snd heq
  subst e2
  congr 1
  funext l
  have c1 : ((h l : ℤ) : ZMod m).valMinAbs = h l :=
    BlockAverages.valMinAbs_intCast_of_small (Or.inr (by have := hb l; simp only at this; omega))
  have c2 : ((h' l : ℤ) : ZMod m).valMinAbs = h' l :=
    BlockAverages.valMinAbs_intCast_of_small (Or.inr (by have := hb' l; simp only at this; omega))
  have c3 : ((h l : ℤ) : ZMod m) = ((h' l : ℤ) : ZMod m) := congrFun e1 l
  rw [← c1, ← c2, c3]
open Classical in
private def bondsOffBox (r : ℕ) (Y : TorusSite m) : Finset (TorusBond m) :=
  Finset.univ \ (boxBondOffsets r).image (bondAtOffset Y)
private theorem sum_eq_box_add_off {r : ℕ} (hm : 2 * r < m) (Y : TorusSite m) (f : TorusBond m → ℝ) :
    ∑ c, f c = ∑ h ∈ boxBondOffsets r, f (bondAtOffset Y h) + ∑ c ∈ bondsOffBox r Y, f c := by
  classical
  rw [← Finset.sum_image (f := f) (bondAtOffset_injOn hm Y), add_comm]
  exact (Finset.sum_sdiff (Finset.subset_univ _)).symm
private theorem le_supDist_of_mem_bondsOffBox {r : ℕ} {Y : TorusSite m} {c : TorusBond m}
    (hc : c ∈ bondsOffBox r Y) : r ≤ _root_.YangMills.Construction.TorusFields.supDist Y c.1 := by
  classical
  by_contra hlt
  have hmem : c ∈ (boxBondOffsets r).image (bondAtOffset Y) := by
    refine Finset.mem_image.mpr ⟨(fun i => (c.1 i - Y i).valMinAbs, c.2), ?_, ?_⟩
    · have hb : ∀ i, |(c.1 i - Y i).valMinAbs| < r := by
        intro i
        have h : ((c.1 i - Y i).valMinAbs).natAbs ≤ _root_.YangMills.Construction.TorusFields.supDist c.1 Y :=
          Finset.le_sup (f := fun i => ((c.1 i - Y i).valMinAbs).natAbs) (Finset.mem_univ i)
        rw [_root_.YangMills.Construction.TorusFields.supDist_comm] at h
        rw [Int.abs_eq_natAbs]
        omega
      refine mem_boxBondOffsets.mpr ⟨fun i => (hb i).le, fun i => ?_⟩
      have h1 := hb i
      have h2 := abs_single_le_one c.2 i
      show |(c.1 i - Y i).valMinAbs + (Pi.single c.2 1 : Fin 4 → ℤ) i| ≤ (r : ℤ)
      refine (abs_add_le _ _).trans ?_
      omega
    · unfold bondAtOffset
      ext1
      · funext i
        simp [siteOfInt, ZMod.coe_valMinAbs]
      · rfl
  exact (Finset.mem_sdiff.mp hc).2 hmem
private theorem le_mul_exp_half_of_le_both {δ α β K x : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K)
    (h1 : x ≤ K * Real.exp (-δ * α)) (h2 : x ≤ K * Real.exp (-δ * β)) :
    x ≤ K * (Real.exp (-(δ / 2 * α)) * Real.exp (-(δ / 2 * β))) := by
  rw [← Real.exp_add]
  rcases le_total α β with h | h
  · refine h2.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hK)
    nlinarith
  · refine h1.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hK)
    nlinarith
private theorem abs_sum_bondsOffBox_le {r : ℕ} {δ K sA : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K) (hsA : 0 ≤ sA)
    (Y Z : TorusSite m) (hZ : _root_.YangMills.Construction.TorusFields.supDist Y Z ≤ 2)
    (f : TorusBond m → ℝ) (hf : ∀ c, |f c| ≤ sA * (K * Real.exp (-δ * (_root_.YangMills.Construction.TorusFields.supDist Z c.1 : ℝ)))) :
    |∑ c ∈ bondsOffBox r Y, f c| ≤
      sA * (K * Real.exp (-(δ / 2 * ((r : ℝ) - 2)))) * (4 * expLineSum (δ / 2 / 4) ^ 4) := by
  have hδ2 : 0 < δ / 2 := by positivity
  have hw : ∀ c ∈ bondsOffBox r Y, |f c| ≤
      sA * (K * Real.exp (-(δ / 2 * ((r : ℝ) - 2)))) * Real.exp (-(δ / 2 * (_root_.YangMills.Construction.TorusFields.supDist Z c.1 : ℝ))) := by
    intro c hc
    have h1 := le_supDist_of_mem_bondsOffBox hc
    have h2 := _root_.YangMills.Construction.TorusFields.supDist_triangle Y Z c.1
    have h3 : (r : ℝ) - 2 ≤ _root_.YangMills.Construction.TorusFields.supDist Z c.1 := by
      have : r ≤ 2 + _root_.YangMills.Construction.TorusFields.supDist Z c.1 := by omega
      have h4 : (r : ℝ) ≤ 2 + (_root_.YangMills.Construction.TorusFields.supDist Z c.1 : ℝ) := by exact_mod_cast this
      linarith
    refine (hf c).trans ?_
    rw [mul_assoc sA]
    refine mul_le_mul_of_nonneg_left ?_ hsA
    rw [mul_assoc K, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hK
    nlinarith
  calc |∑ c ∈ bondsOffBox r Y, f c| ≤ ∑ c ∈ bondsOffBox r Y, |f c| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ c ∈ bondsOffBox r Y, sA * (K * Real.exp (-(δ / 2 * ((r : ℝ) - 2)))) *
          Real.exp (-(δ / 2 * (_root_.YangMills.Construction.TorusFields.supDist Z c.1 : ℝ))) :=
        Finset.sum_le_sum hw
    _ = sA * (K * Real.exp (-(δ / 2 * ((r : ℝ) - 2)))) *
          ∑ c ∈ bondsOffBox r Y, Real.exp (-(δ / 2 * (_root_.YangMills.Construction.TorusFields.supDist Z c.1 : ℝ))) := by
        rw [Finset.mul_sum]
    _ ≤ sA * (K * Real.exp (-(δ / 2 * ((r : ℝ) - 2)))) * (4 * expLineSum (δ / 2 / 4) ^ 4) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine le_trans ?_ (sum_bonds_exp_le hδ2 Z)
        exact Finset.sum_le_univ_sum_of_nonneg fun _ => (Real.exp_pos _).le
end Split
section Bonds
variable {a ρ δ lam σA cg : ℝ} {N : ℕ → ℝ} {L : ℕ} [NeZero L]
private theorem supDist_near_le_mirror {n r : ℕ} [NeZero n] [NeZero (4 * r)] (hr : 16 ≤ r) (Y : TorusSite n)
    {w e : Fin 4 → ℤ} (hw : ∀ i, |w i| ≤ 2) (he : BlockAverages.WithinRadius r e) :
    _root_.YangMills.Construction.TorusFields.supDist (Y + siteOfInt w) (Y + siteOfInt e) ≤ _root_.YangMills.Construction.TorusFields.supDist (0 + siteOfInt w : TorusSite (4 * r)) (0 + siteOfInt e) := by
  rw [add_comm Y, add_comm Y, _root_.YangMills.Construction.TorusFields.supDist_add_right, zero_add, zero_add, _root_.YangMills.Construction.TorusFields.supDist_le_iff]
  intro i
  have h1 : ((w i - e i : ℤ) : ZMod (4 * r)).valMinAbs = w i - e i := by
    refine BlockAverages.valMinAbs_intCast_of_small (Or.inr ?_)
    have a1 := abs_le.mp (hw i)
    have a2 := abs_le.mp (he i)
    have : |w i - e i| ≤ (r : ℤ) + 2 := by
      rw [abs_le]
      constructor <;> omega
    push_cast
    omega
  have h2 : (((siteOfInt w : TorusSite (4 * r)) i - (siteOfInt e : TorusSite (4 * r)) i).valMinAbs).natAbs ≤
      _root_.YangMills.Construction.TorusFields.supDist (siteOfInt w : TorusSite (4 * r)) (siteOfInt e) :=
    Finset.le_sup
      (f := fun i => (((siteOfInt w : TorusSite (4 * r)) i - (siteOfInt e : TorusSite (4 * r)) i).valMinAbs).natAbs)
      (Finset.mem_univ i)
  have h3 : (siteOfInt w : TorusSite (4 * r)) i - (siteOfInt e : TorusSite (4 * r)) i =
      ((w i - e i : ℤ) : ZMod (4 * r)) := by
    simp [siteOfInt]
  rw [h3, h1] at h2
  have h4 : (siteOfInt w : TorusSite n) i - (siteOfInt e : TorusSite n) i = ((w i - e i : ℤ) : ZMod n) := by
    simp [siteOfInt]
  rw [h4]
  exact (_root_.YangMills.Construction.TorusFields.natAbs_valMinAbs_intCast_le _).trans h2
private theorem abs_box_sum_le (hc : ColdChain.ColdChainConstants a δ L lam ρ σA cg N) (hodd : Odd L) {u n r : ℕ}
    [NeZero n] [NeZero (4 * r)] (hn : 64 ≤ n) (hr : 16 ≤ r) (h2 : 2 * r + 2 < n) (Y : TorusSite n)
    {p : Fin 4 → ℤ} (hp : ∀ i, |p i| ≤ 2 * (L : ℤ)) (i : Fin 4) (A : TorusBond n → ℝ) {sA : ℝ} (hsA : 0 ≤ sA)
    (hA : ∀ b, |A b| ≤ sA) :
    |∑ h ∈ boxBondOffsets r,
      (WeightedResponses.responseKernel a ρ L u (CongruentBoxes.blockCentre L Y + siteOfInt p, i) (bondAtOffset Y h) *
          A (bondAtOffset Y h) -
       WeightedResponses.responseKernel a ρ L u (CongruentBoxes.blockCentre L (0 : TorusSite (4 * r)) + siteOfInt p, i)
          (bondAtOffset 0 h) * mirrorExtension r Y A (bondAtOffset 0 h))| ≤
      sA * (2 * (N 1 + 1) * Real.exp (-(δ / 2 * ((r : ℝ) - 2)))) * (4 * expLineSum (δ / 2 / 4) ^ 4) := by
  have hδ : 0 < δ := hc.1
  have hδ2 : 0 < δ / 2 := by positivity
  have hN : 0 < N 1 := hc.2.2.2.2.2.2.2.1 1
  have hK : 0 ≤ 2 * (N 1 + 1) := by positivity
  have h4r : 64 ≤ 4 * r := by omega
  obtain ⟨w, hw0⟩ : ∃ w, w = CongruentBoxes.coarseOffset L p := ⟨_, rfl⟩
  have hw : ∀ i, |w i| ≤ 2 := fun i => by rw [hw0]; exact abs_coarseOffset_le hodd (by norm_num) (hp i)
  have hZ : TorusLumps.parentBlock L (CongruentBoxes.blockCentre L Y + siteOfInt p : TorusSite (n * L)) =
      Y + siteOfInt w := by
    rw [hw0]; exact TorusBlocks.parentBlock_blockCentreSite_add Y p
  have hZ' : TorusLumps.parentBlock L (CongruentBoxes.blockCentre L (0 : TorusSite (4 * r)) + siteOfInt p :
      TorusSite (4 * r * L)) = 0 + siteOfInt w := by
    rw [hw0]; exact TorusBlocks.parentBlock_blockCentreSite_add 0 p
  have hterm : ∀ h ∈ boxBondOffsets r,
      |WeightedResponses.responseKernel a ρ L u (CongruentBoxes.blockCentre L Y + siteOfInt p, i) (bondAtOffset Y h) *
          A (bondAtOffset Y h) -
       WeightedResponses.responseKernel a ρ L u (CongruentBoxes.blockCentre L (0 : TorusSite (4 * r)) + siteOfInt p, i)
          (bondAtOffset 0 h) * mirrorExtension r Y A (bondAtOffset 0 h)| ≤
      sA * (2 * (N 1 + 1) * Real.exp (-(δ / 2 * ((r : ℝ) - 2)))) *
        Real.exp (-(δ / 2 * (_root_.YangMills.Construction.TorusFields.supDist (Y + siteOfInt w) (bondAtOffset Y h).1 : ℝ))) := by
    rintro ⟨e, k⟩ hh
    have hb := mem_boxBondOffsets.mp hh
    have hm : mirrorExtension r Y A (bondAtOffset 0 (e, k)) = A (bondAtOffset Y (e, k)) := by
      unfold bondAtOffset
      simp only [zero_add]
      exact mirrorExtension_of_mem_box Y A (by omega) hb
    rw [hm, ← sub_mul, abs_mul, mul_comm]
    have hAb := hA (bondAtOffset Y (e, k))
    rw [mul_assoc sA]
    refine mul_le_mul hAb ?_ (abs_nonneg _) hsA
    have c1 := responseKernel_compare (a := a) (ρ := ρ) hc hodd (u := u) hn h4r hr h2 (by omega) Y
      (0 : TorusSite (4 * r)) hp i hb
    have d1 := abs_responseKernel_le (a := a) (ρ := ρ) hc (u := u) hn
      (CongruentBoxes.blockCentre L Y + siteOfInt p, i) (bondAtOffset Y (e, k))
    have d2 := abs_responseKernel_le (a := a) (ρ := ρ) hc (u := u) h4r
      (CongruentBoxes.blockCentre L (0 : TorusSite (4 * r)) + siteOfInt p, i) (bondAtOffset 0 (e, k))
    simp only [hZ, hZ'] at d1 d2
    have hd := supDist_near_le_mirror hr Y hw hb.1
    have hdR : (_root_.YangMills.Construction.TorusFields.supDist (Y + siteOfInt w) (bondAtOffset Y (e, k)).1 : ℝ) ≤
        _root_.YangMills.Construction.TorusFields.supDist (0 + siteOfInt w : TorusSite (4 * r)) (bondAtOffset 0 (e, k)).1 := by
      exact_mod_cast hd
    have hmono : Real.exp (-δ * (_root_.YangMills.Construction.TorusFields.supDist (0 + siteOfInt w : TorusSite (4 * r)) (bondAtOffset 0 (e, k)).1 : ℝ)) ≤
        Real.exp (-δ * (_root_.YangMills.Construction.TorusFields.supDist (Y + siteOfInt w) (bondAtOffset Y (e, k)).1 : ℝ)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hE : 0 ≤ Real.exp (-δ * (_root_.YangMills.Construction.TorusFields.supDist (Y + siteOfInt w) (bondAtOffset Y (e, k)).1 : ℝ)) := (Real.exp_pos _).le
    have b1 : |WeightedResponses.responseKernel a ρ L u (CongruentBoxes.blockCentre L Y + siteOfInt p, i)
          (bondAtOffset Y (e, k)) -
        WeightedResponses.responseKernel a ρ L u (CongruentBoxes.blockCentre L (0 : TorusSite (4 * r)) + siteOfInt p, i)
          (bondAtOffset 0 (e, k))| ≤
        2 * (N 1 + 1) * Real.exp (-δ * ((r : ℝ) - 2)) := by
      have c2 : N 1 * Real.exp (-δ * ((r : ℝ) - 2)) ≤ 2 * (N 1 + 1) * Real.exp (-δ * ((r : ℝ) - 2)) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
      refine le_trans ?_ c2
      have := c1
      simpa only [bondAtOffset, zero_add] using this
    have b2 : |WeightedResponses.responseKernel a ρ L u (CongruentBoxes.blockCentre L Y + siteOfInt p, i)
          (bondAtOffset Y (e, k)) -
        WeightedResponses.responseKernel a ρ L u (CongruentBoxes.blockCentre L (0 : TorusSite (4 * r)) + siteOfInt p, i)
          (bondAtOffset 0 (e, k))| ≤
        2 * (N 1 + 1) * Real.exp (-δ * (_root_.YangMills.Construction.TorusFields.supDist (Y + siteOfInt w) (bondAtOffset Y (e, k)).1 : ℝ)) := by
      refine (abs_sub _ _).trans ?_
      have d3 := mul_le_mul_of_nonneg_left hmono (show 0 ≤ N 1 + 1 by positivity)
      nlinarith
    have := le_mul_exp_half_of_le_both hδ hK b1 b2
    rwa [← mul_assoc] at this
  calc _ ≤ ∑ h ∈ boxBondOffsets r,
        |WeightedResponses.responseKernel a ρ L u (CongruentBoxes.blockCentre L Y + siteOfInt p, i) (bondAtOffset Y h) *
            A (bondAtOffset Y h) -
         WeightedResponses.responseKernel a ρ L u (CongruentBoxes.blockCentre L (0 : TorusSite (4 * r)) + siteOfInt p, i)
            (bondAtOffset 0 h) * mirrorExtension r Y A (bondAtOffset 0 h)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ h ∈ boxBondOffsets r, sA * (2 * (N 1 + 1) * Real.exp (-(δ / 2 * ((r : ℝ) - 2)))) *
        Real.exp (-(δ / 2 * (_root_.YangMills.Construction.TorusFields.supDist (Y + siteOfInt w) (bondAtOffset Y h).1 : ℝ))) := Finset.sum_le_sum hterm
    _ = sA * (2 * (N 1 + 1) * Real.exp (-(δ / 2 * ((r : ℝ) - 2)))) *
        ∑ h ∈ boxBondOffsets r, Real.exp (-(δ / 2 * (_root_.YangMills.Construction.TorusFields.supDist (Y + siteOfInt w) (bondAtOffset Y h).1 : ℝ))) := by
        rw [Finset.mul_sum]
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine le_trans ?_ (sum_bonds_exp_le hδ2 (Y + siteOfInt w))
        classical
        rw [← Finset.sum_image
          (f := fun c : TorusBond n => Real.exp (-(δ / 2 * (_root_.YangMills.Construction.TorusFields.supDist (Y + siteOfInt w) c.1 : ℝ))))
          (bondAtOffset_injOn (by omega) Y)]
        exact Finset.sum_le_univ_sum_of_nonneg fun _ => (Real.exp_pos _).le
private theorem abs_responseMap_sub_mirror_le (hc : ColdChain.ColdChainConstants a δ L lam ρ σA cg N) (hodd : Odd L)
    {u n r : ℕ} [NeZero n] [NeZero (4 * r)] (hn : 64 ≤ n) (hr : 16 ≤ r) (h2 : 2 * r + 2 < n) (Y : TorusSite n)
    {p : Fin 4 → ℤ} (hp : ∀ i, |p i| ≤ 2 * (L : ℤ)) (i : Fin 4) (A : TorusBond n → ℝ) {sA : ℝ} (hsA : 0 ≤ sA)
    (hA : ∀ b, |A b| ≤ sA) :
    |WeightedResponses.responseMap a ρ L u A (CongruentBoxes.blockCentre L Y + siteOfInt p, i) -
      WeightedResponses.responseMap a ρ L u (mirrorExtension r Y A)
        (CongruentBoxes.blockCentre L (0 : TorusSite (4 * r)) + siteOfInt p, i)| ≤
      sA * (4 * (N 1 + 1) * Real.exp (-(δ / 2 * ((r : ℝ) - 2)))) * (4 * expLineSum (δ / 2 / 4) ^ 4) := by
  have hδ : 0 < δ := hc.1
  have hN : 0 < N 1 := hc.2.2.2.2.2.2.2.1 1
  have hK : 0 ≤ N 1 + 1 := by positivity
  have h4r : 64 ≤ 4 * r := by omega
  obtain ⟨w, hw0⟩ : ∃ w, w = CongruentBoxes.coarseOffset L p := ⟨_, rfl⟩
  have hw : ∀ i, |w i| ≤ 2 := fun i => by rw [hw0]; exact abs_coarseOffset_le hodd (by norm_num) (hp i)
  have hZ : TorusLumps.parentBlock L (CongruentBoxes.blockCentre L Y + siteOfInt p : TorusSite (n * L)) =
      Y + siteOfInt w := by
    rw [hw0]; exact TorusBlocks.parentBlock_blockCentreSite_add Y p
  have hZ' : TorusLumps.parentBlock L (CongruentBoxes.blockCentre L (0 : TorusSite (4 * r)) + siteOfInt p :
      TorusSite (4 * r * L)) = 0 + siteOfInt w := by
    rw [hw0]; exact TorusBlocks.parentBlock_blockCentreSite_add 0 p
  have hna : ∀ i, (w i).natAbs ≤ 2 := fun i => by
    have := abs_le.mp (hw i)
    omega
  have hb := abs_box_sum_le (a := a) (ρ := ρ) hc hodd (u := u) hn hr h2 Y hp i A hsA hA
  have ho1 := abs_sum_bondsOffBox_le (r := r) hδ hK hsA Y (Y + siteOfInt w) (_root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le Y w 2 hna)
    (fun c => WeightedResponses.responseKernel a ρ L u (CongruentBoxes.blockCentre L Y + siteOfInt p, i) c * A c)
    (fun c => by
      rw [abs_mul, mul_comm]
      have d := abs_responseKernel_le (a := a) (ρ := ρ) hc (u := u) hn
        (CongruentBoxes.blockCentre L Y + siteOfInt p, i) c
      simp only [hZ] at d
      exact mul_le_mul (hA c) d (abs_nonneg _) hsA)
  have ho2 := abs_sum_bondsOffBox_le (r := r) hδ hK hsA (0 : TorusSite (4 * r)) (0 + siteOfInt w)
    (_root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le 0 w 2 hna)
    (fun c => WeightedResponses.responseKernel a ρ L u
      (CongruentBoxes.blockCentre L (0 : TorusSite (4 * r)) + siteOfInt p, i) c * mirrorExtension r Y A c)
    (fun c => by
      rw [abs_mul, mul_comm]
      have d := abs_responseKernel_le (a := a) (ρ := ρ) hc (u := u) h4r
        (CongruentBoxes.blockCentre L (0 : TorusSite (4 * r)) + siteOfInt p, i) c
      simp only [hZ'] at d
      exact mul_le_mul (abs_mirrorExtension_le Y A hA c) d (abs_nonneg _) hsA)
  unfold WeightedResponses.responseMap
  rw [sum_eq_box_add_off (r := r) (by omega) Y, sum_eq_box_add_off (r := r) (by omega) (0 : TorusSite (4 * r))]
  rw [Finset.sum_sub_distrib] at hb
  set S := 4 * expLineSum (δ / 2 / 4) ^ 4
  set E := Real.exp (-(δ / 2 * ((r : ℝ) - 2)))
  have e : sA * (4 * (N 1 + 1) * E) * S =
      sA * (2 * (N 1 + 1) * E) * S + sA * ((N 1 + 1) * E) * S + sA * ((N 1 + 1) * E) * S := by ring
  rw [e]
  obtain ⟨b1, b2⟩ := abs_le.mp hb
  obtain ⟨c1, c2⟩ := abs_le.mp ho1
  obtain ⟨d1, d2⟩ := abs_le.mp ho2
  rw [abs_le]
  constructor <;> linarith
end Bonds
section Core
variable {a ρ δ lam σA cg : ℝ} {N : ℕ → ℝ} {L : ℕ} [NeZero L]
private theorem curl_eq_four {m : ℕ} (B : TorusBond m → ℝ) (x : TorusSite m) (μ ν : Fin 4) :
    WeightedResponses.curl B (x, μ, ν) =
      B (x, μ) + B (x + TorusFields.unitStep m μ, ν) - B (x + TorusFields.unitStep m ν, μ) - B (x, ν) := rfl
private theorem add_siteOfInt_add_unitStep {M : ℕ} [NeZero M] (Z : TorusSite M) (p : Fin 4 → ℤ) (j : Fin 4) :
    Z + siteOfInt p + TorusFields.unitStep M j = Z + siteOfInt (p + Pi.single j 1) := by apply _root_.YangMills.Construction.AbelianSecondOrder.add_siteOfInt_unitStep <;> assumption
private theorem exists_offset_of_parentBlock_near (hodd : Odd L) {n : ℕ} [NeZero n] (Y : TorusSite n)
    (x : TorusSite (n * L)) (hx : _root_.YangMills.Construction.TorusFields.supDist (TorusLumps.parentBlock L x) Y ≤ 1) :
    ∃ p₀ : Fin 4 → ℤ, x = CongruentBoxes.blockCentre L Y + siteOfInt p₀ ∧ ∀ i, |p₀ i| + 1 ≤ 2 * (L : ℤ) := by
  obtain ⟨w, hw0⟩ : ∃ w : Fin 4 → ℤ, w = fun i => (TorusLumps.parentBlock L x i - Y i).valMinAbs := ⟨_, rfl⟩
  have hb : TorusLumps.parentBlock L x = Y + siteOfInt w := by
    funext i
    simp [siteOfInt, hw0, ZMod.coe_valMinAbs]
  have hw : ∀ i, |w i| ≤ 1 := by
    intro i
    have h : ((TorusLumps.parentBlock L x i - Y i).valMinAbs).natAbs ≤ _root_.YangMills.Construction.TorusFields.supDist (TorusLumps.parentBlock L x) Y :=
      Finset.le_sup (f := fun i => ((TorusLumps.parentBlock L x i - Y i).valMinAbs).natAbs) (Finset.mem_univ i)
    rw [hw0, Int.abs_eq_natAbs]
    show (((TorusLumps.parentBlock L x i - Y i).valMinAbs).natAbs : ℤ) ≤ 1
    omega
  refine ⟨CongruentBoxes.refinedOffset L w (StepSettings.siteOffset x),
    CongruentBoxes.eq_blockCentre_add_of_parentBlock hb, fun i => ?_⟩
  obtain ⟨k, hk⟩ := hodd
  have hh2 : ((L : ℤ) - 1) / 2 = k := by omega
  have ho1 : (((StepSettings.siteOffset x i : Fin L) : ℕ) : ℤ) < L := by
    exact_mod_cast (StepSettings.siteOffset x i).2
  have e : CongruentBoxes.refinedOffset L w (StepSettings.siteOffset x) i =
      (L : ℤ) * w i + ((((StepSettings.siteOffset x i : Fin L) : ℕ) : ℤ) - k) := by
    rw [← hh2]
    rfl
  obtain ⟨w1, w2⟩ := abs_le.mp (hw i)
  have hc3 : w i = -1 ∨ w i = 0 ∨ w i = 1 := by omega
  have hpb : |CongruentBoxes.refinedOffset L w (StepSettings.siteOffset x) i| ≤ (L : ℤ) + k := by
    rw [e, abs_le]
    rcases hc3 with h | h | h <;> rw [h] <;> constructor <;> omega
  omega
private theorem abs_curl_mirrorExtension_le {n r : ℕ} [NeZero n] [NeZero (4 * r)] (hr : 16 ≤ r) (Y : TorusSite n)
    (A : TorusBond n → ℝ) {s : ℝ} {S : Finset (TorusSite n)} (hS : ∀ z, _root_.YangMills.Construction.TorusFields.supDist z Y ≤ r → z ∈ S)
    (hcurl : ∀ p ∈ plaquettesIn S, |WeightedResponses.curl A p| ≤ s) :
    ∀ q ∈ plaquettesIn (Finset.univ : Finset (TorusSite (4 * r))),
      |WeightedResponses.curl (mirrorExtension r Y A) q| ≤ s := by
  rintro ⟨x', μ', ν'⟩ hq
  have hlt : μ' < ν' := (Finset.mem_filter.mp hq).2.1
  obtain ⟨w', hw', he⟩ := abs_curl_mirrorExtension Y A (by omega) hS x' hlt
  rw [he]
  exact hcurl _ hw'
private theorem abs_four_terms_le {x x' y y' z z' t t' s B : ℝ} (hk : |x' + y' - z' - t'| ≤ s) (h1 : |x - x'| ≤ B)
    (h2 : |y - y'| ≤ B) (h3 : |z - z'| ≤ B) (h4 : |t - t'| ≤ B) : |x + y - z - t| ≤ s + 4 * B := by
  obtain ⟨k1, k2⟩ := abs_le.mp hk
  obtain ⟨e1, e2⟩ := abs_le.mp h1
  obtain ⟨f1, f2⟩ := abs_le.mp h2
  obtain ⟨g1, g2⟩ := abs_le.mp h3
  obtain ⟨l1, l2⟩ := abs_le.mp h4
  rw [abs_le]
  constructor <;> linarith
private theorem abs_curl_responseMap_le (hc : ColdChain.ColdChainConstants a δ L lam ρ σA cg N) (hodd : Odd L)
    {u n r : ℕ} [NeZero n] [NeZero (4 * r)] (hn : 64 ≤ n) (hr : 16 ≤ r) (h2 : 2 * r + 2 < n) (Y : TorusSite n)
    {p₀ : Fin 4 → ℤ} (hbd : ∀ i, |p₀ i| + 1 ≤ 2 * (L : ℤ)) {μ ν : Fin 4} (A : TorusBond n → ℝ) {s sA : ℝ}
    (hsA : 0 ≤ sA) (hA : ∀ b, |A b| ≤ sA)
    (key : |WeightedResponses.curl (WeightedResponses.responseMap a ρ L u (mirrorExtension r Y A))
      (CongruentBoxes.blockCentre L (0 : TorusSite (4 * r)) + siteOfInt p₀, μ, ν)| ≤ s / 8) :
    |WeightedResponses.curl (WeightedResponses.responseMap a ρ L u A)
      (CongruentBoxes.blockCentre L Y + siteOfInt p₀, μ, ν)| ≤
      s / 8 + 4 * (sA * (4 * (N 1 + 1) * Real.exp (-(δ / 2 * ((r : ℝ) - 2)))) * (4 * expLineSum (δ / 2 / 4) ^ 4)) := by
  have hq1 : ∀ i, |p₀ i| ≤ 2 * (L : ℤ) := fun i => by have := hbd i; omega
  have hq2 : ∀ (j i : Fin 4), |(p₀ + Pi.single j 1 : Fin 4 → ℤ) i| ≤ 2 * (L : ℤ) := fun j i => by
    have h1 := hbd i
    have h2 := abs_single_le_one j i
    show |p₀ i + (Pi.single j 1 : Fin 4 → ℤ) i| ≤ 2 * (L : ℤ)
    refine (abs_add_le _ _).trans ?_
    omega
  have b1 := abs_responseMap_sub_mirror_le (a := a) (ρ := ρ) hc hodd (u := u) hn hr h2 Y hq1 μ A hsA hA
  have b2 := abs_responseMap_sub_mirror_le (a := a) (ρ := ρ) hc hodd (u := u) hn hr h2 Y (hq2 μ) ν A hsA hA
  have b3 := abs_responseMap_sub_mirror_le (a := a) (ρ := ρ) hc hodd (u := u) hn hr h2 Y (hq2 ν) μ A hsA hA
  have b4 := abs_responseMap_sub_mirror_le (a := a) (ρ := ρ) hc hodd (u := u) hn hr h2 Y hq1 ν A hsA hA
  rw [curl_eq_four, add_siteOfInt_add_unitStep, add_siteOfInt_add_unitStep] at key ⊢
  exact abs_four_terms_le key b1 b2 b3 b4
private theorem localContraction_of_global (hc : ColdChain.ColdChainConstants a δ L lam ρ σA cg N) (hodd : Odd L)
    (hglobal : ∀ (u n : ℕ) [NeZero n], 64 ≤ n → ∀ (A : TorusBond n → ℝ) (s : ℝ),
      (∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), |WeightedResponses.curl A p| ≤ s) →
      ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (n * L))),
        |WeightedResponses.curl (WeightedResponses.responseMap a ρ L u A) p| ≤ s / 8) :
    ∃ C c : ℝ, 0 < c ∧ ∀ (u n : ℕ) [NeZero n], 64 ≤ n → ∀ r : ℕ, 16 ≤ r → 2 * r + 2 < n →
      ∀ (Y : TorusSite n) (A : TorusBond n → ℝ) (s sA : ℝ) (S : Finset (TorusSite n)), (∀ z, _root_.YangMills.Construction.TorusFields.supDist z Y ≤ r → z ∈ S) →
      (∀ p ∈ plaquettesIn S, |WeightedResponses.curl A p| ≤ s) → (∀ b, |A b| ≤ sA) →
      ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (n * L))),
        (∀ z ∈ plaquetteVertices p.1 p.2.1 p.2.2, _root_.YangMills.Construction.TorusFields.supDist (TorusLumps.parentBlock L z) Y ≤ 1) →
        |WeightedResponses.curl (WeightedResponses.responseMap a ρ L u A) p| ≤
          s / 8 + C * Real.exp (-(c * (r : ℝ))) * sA := by
  have hδ : 0 < δ := hc.1
  refine ⟨4 * (4 * (N 1 + 1) * Real.exp δ) * (4 * expLineSum (δ / 2 / 4) ^ 4), δ / 2, by positivity, ?_⟩
  intro u n _ hn r hr h2 Y A s sA S hS hcurl hA p hp hnear
  obtain ⟨x, μ, ν⟩ := p
  have hμν : μ < ν := (Finset.mem_filter.mp hp).2.1
  have : NeZero (4 * r) := ⟨by omega⟩
  have hsA : 0 ≤ sA := (abs_nonneg _).trans (hA (0, 0))
  have hx : _root_.YangMills.Construction.TorusFields.supDist (TorusLumps.parentBlock L x) Y ≤ 1 := hnear x (by simp [plaquetteVertices])
  obtain ⟨p₀, hsite, hbd⟩ := exists_offset_of_parentBlock_near hodd Y x hx
  subst hsite
  have hmem : (CongruentBoxes.blockCentre L (0 : TorusSite (4 * r)) + siteOfInt p₀, μ, ν) ∈
      plaquettesIn (Finset.univ : Finset (TorusSite (4 * r * L))) := by
    simp only [plaquettesIn, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hμν, fun _ _ => trivial⟩
  have key := hglobal u (4 * r) (by omega) (mirrorExtension r Y A) s
    (abs_curl_mirrorExtension_le hr Y A hS hcurl) _ hmem
  have hexp : Real.exp (-(δ / 2 * ((r : ℝ) - 2))) = Real.exp δ * Real.exp (-(δ / 2 * (r : ℝ))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have efin : 4 * (4 * (N 1 + 1) * Real.exp δ) * (4 * expLineSum (δ / 2 / 4) ^ 4) *
        Real.exp (-(δ / 2 * (r : ℝ))) * sA =
      4 * (sA * (4 * (N 1 + 1) * Real.exp (-(δ / 2 * ((r : ℝ) - 2)))) * (4 * expLineSum (δ / 2 / 4) ^ 4)) := by
    rw [hexp]
    ring
  rw [efin]
  exact abs_curl_responseMap_le hc hodd hn hr h2 Y hbd A hsA hA key
end Core
end LocalContraction
theorem responseLocalCurvatureContraction_of_global
    (h : ResponseContractsCurvatureStatement) : responseLocalCurvatureContractionStatement := by
  intro a ha
  obtain ⟨L₀, rt₀, C₀, hrt, hh⟩ := h a ha
  refine ⟨L₀, rt₀, C₀, hrt, fun L hL hL₀ T hTa hTL hD hCS hCH hr hC => ?_⟩
  obtain ⟨y₀, hy⟩ := hh L hL hL₀ T hTa hTL hD hCS hCH hr hC
  refine ⟨y₀, fun y hy0 hrow hw => ?_⟩
  have hglobal := hy y hy0 hrow hw
  obtain ⟨C, c, hc, hbody⟩ :=
    LocalContraction.localContraction_of_global (L := (T.stepParameters y).side) hD.chain hD.L_odd hglobal
  refine ⟨C, c, hc, fun u n _ hn r hr2 h2 Y A s sA hcurl hA p hp hnear => ?_⟩
  exact hbody u n hn r hr2 h2 Y A s sA _ (fun z hz => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩)
    hcurl hA p hp hnear
end ResponseInTheExpansion
end YangMills.Construction
end
