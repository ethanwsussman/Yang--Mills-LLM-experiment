import YangMills.Construction.ClusterExpansionOfAStep.MirrorOfABox
import YangMills.Construction.ColdChainAtEveryLevel.PlaquettesNearAPoint
import YangMills.Construction.ColdStepAtMirrorFrames.ClassicalChainAtGivenNumbersProof
import YangMills.Construction.ColdStepAtMirrorFrames.MirrorAgreesOnItsBoxProof
import YangMills.Construction.ColdStepAtMirrorFrames.MirrorFieldIsCold
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
namespace Reflection
theorem norm_inv_sub_one (g : UnitQuaternion) :
    ‖((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ = ‖(g : ℍ[ℝ]) - 1‖ := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_inv_sub_one <;> assumption
theorem norm_conj_sub_one (h g : UnitQuaternion) :
    ‖((h * g * h⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ = ‖(g : ℍ[ℝ]) - 1‖ := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_conj_sub_one <;> assumption
theorem reflectCoord_eq_ite (m : ℕ) (c : ℤ) : reflectCoord m c =
    if -(m : ℤ) ≤ c ∧ c ≤ m then c else if 0 < c then 2 * (m : ℤ) - c else -(2 * (m : ℤ)) - c := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ReflectionOnBox.reflectCoord_eq <;> assumption
theorem reflectCoord_succ_eq (m : ℕ) (c : ℤ) :
    reflectCoord m (c + 1) = reflectCoord m c + 1 ∨
      reflectCoord m (c + 1) = reflectCoord m c - 1 := by apply _root_.YangMills.Construction.TorusMirror.triangleFold_add_one <;> assumption
theorem reflectCoord_valMinAbs_add_one (m N : ℕ) (hm : 0 < m) (hN : N = 4 * m) (z : ZMod N) :
    reflectCoord m (z + 1).valMinAbs = reflectCoord m (z.valMinAbs + 1) := by
  subst hN
  have : NeZero (4 * m) := ⟨by omega⟩
  set v := z.valMinAbs with hv
  set v' := (z + 1).valMinAbs with hv'
  have r1 := ZMod.valMinAbs_mem_Ioc z
  have r2 := ZMod.valMinAbs_mem_Ioc (z + 1)
  have hc : ((v' : ℤ) : ZMod (4 * m)) = ((v + 1 : ℤ) : ZMod (4 * m)) := by
    push_cast
    rw [hv, hv', ZMod.coe_valMinAbs, ZMod.coe_valMinAbs]
  obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hc
  simp only [Set.mem_Ioc] at r1 r2
  push_cast at r1 r2 hk
  rw [← hv] at r1
  rw [← hv'] at r2
  have hk01 : k = 0 ∨ k = 1 := by
    by_contra hcon
    push Not at hcon
    rcases lt_or_gt_of_ne hcon.1 with h | h
    · have : k ≤ -1 := by omega
      nlinarith
    · have : 2 ≤ k := by
        have := hcon.2
        omega
      nlinarith
  rcases hk01 with rfl | rfl
  · have : v' = v + 1 := by linarith
    rw [this]
  · have : v' = v + 1 - 4 * m := by linarith
    rw [this, reflectCoord_eq_ite, reflectCoord_eq_ite]
    split_ifs <;> omega
theorem siteOfCoords_add {j : ℕ} (a b : Fin 4 → ℤ) :
    (siteOfCoords j (a + b) : F.Site j) = siteOfCoords j a + siteOfCoords j b := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_add <;> assumption
theorem siteOfCoords_sub {j : ℕ} (a b : Fin 4 → ℤ) :
    (siteOfCoords j (a - b) : F.Site j) = siteOfCoords j a - siteOfCoords j b := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.AdmissibleParameters.siteOfCoords_sub <;> assumption
theorem plaquetteHolonomy_eq {j : ℕ} (X : F.GaugeField j) (x : F.Site j) (μ ν : Fin 4) :
    plaquetteHolonomy X (x, μ, ν) =
      X x μ * X (x + unitStep j μ) ν * (X (x + unitStep j ν) μ)⁻¹ * (X x ν)⁻¹ := by apply _root_.YangMills.Construction.PlaquetteExpansion.plaquetteHolonomy_eq <;> assumption
theorem norm_square_sub_one_lt {s : ℝ} {V : F.GaugeField F.top} (hV : IsSmallCurvature s V)
    (a : F.Cell) (μ ν : Fin 4) (h : μ < ν) (e₁ e₂ : Bool) :
    ‖(((linkValue V a (μ, e₁) * linkValue V (a + stepDisplacement F.top (μ, e₁)) (ν, e₂) *
      (linkValue V (a + stepDisplacement F.top (ν, e₂)) (μ, e₁))⁻¹ *
        (linkValue V a (ν, e₂))⁻¹ : UnitQuaternion)) : ℍ[ℝ]) - 1‖ < s := by
  have small : ∀ a' : F.Cell, ‖((V a' μ * V (a' + unitStep F.top μ) ν *
      (V (a' + unitStep F.top ν) μ)⁻¹ * (V a' ν)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ < s := by
    intro a'
    have := hV (a', μ, ν) h
    unfold plaquetteDefect at this
    rwa [plaquetteHolonomy_eq] at this
  cases e₁ <;> cases e₂
  · obtain ⟨a', rfl⟩ : ∃ a' : F.Cell, a = a' + unitStep F.top μ + unitStep F.top ν :=
      ⟨a - unitStep F.top ν - unitStep F.top μ, by abel⟩
    have f1 : a' + unitStep F.top μ + unitStep F.top ν - unitStep F.top μ =
        a' + unitStep F.top ν := by abel
    have f2 : a' + unitStep F.top μ + unitStep F.top ν + -unitStep F.top μ -
        unitStep F.top ν = a' := by abel
    have f3 : a' + unitStep F.top μ + unitStep F.top ν + -unitStep F.top ν -
        unitStep F.top μ = a' := by abel
    have f4 : a' + unitStep F.top μ + unitStep F.top ν - unitStep F.top ν =
        a' + unitStep F.top μ := by abel
    simp only [linkValue, stepDisplacement, Bool.false_eq_true, if_false, f1, f2, f3, f4]
    have := small a'
    rw [← norm_conj_sub_one ((V (a' + unitStep F.top ν) μ)⁻¹ * (V a' ν)⁻¹)] at this
    convert this using 3
    group
  · obtain ⟨a', rfl⟩ : ∃ a' : F.Cell, a = a' + unitStep F.top μ :=
      ⟨a - unitStep F.top μ, by abel⟩
    have f1 : a' + unitStep F.top μ - unitStep F.top μ = a' := by abel
    have f2 : a' + unitStep F.top μ + -unitStep F.top μ = a' := by abel
    have f3 : a' + unitStep F.top μ + unitStep F.top ν - unitStep F.top μ =
        a' + unitStep F.top ν := by abel
    simp only [linkValue, stepDisplacement, Bool.false_eq_true, if_false, if_true, f1, f2, f3]
    have := small a'
    rw [← norm_inv_sub_one, ← norm_conj_sub_one (V a' μ)⁻¹] at this
    convert this using 3
    group
  · obtain ⟨a', rfl⟩ : ∃ a' : F.Cell, a = a' + unitStep F.top ν :=
      ⟨a - unitStep F.top ν, by abel⟩
    have f1 : a' + unitStep F.top ν - unitStep F.top ν = a' := by abel
    have f2 : a' + unitStep F.top ν + -unitStep F.top ν = a' := by abel
    have f3 : a' + unitStep F.top ν + unitStep F.top μ - unitStep F.top ν =
        a' + unitStep F.top μ := by abel
    simp only [linkValue, stepDisplacement, Bool.false_eq_true, if_false, if_true, f1, f2, f3]
    have := small a'
    rw [← norm_inv_sub_one, ← norm_conj_sub_one (V a' ν)⁻¹] at this
    convert this using 3
    group
  · simp only [linkValue, stepDisplacement, if_true]
    have := small a
    convert this using 3
variable (m : ℕ) (y : F.Cell) (V : F.GaugeField F.top)
def reflectedCoords (z : (reflectedFrame F m).Site (reflectedFrame F m).top) : Fin 4 → ℤ :=
  fun l => reflectCoord m (z l).valMinAbs
def orientation (z : (reflectedFrame F m).Site (reflectedFrame F m).top) (i : Fin 4) : Bool :=
  decide (reflectCoord m ((z i).valMinAbs + 1) = reflectCoord m (z i).valMinAbs + 1)
theorem period_top (l : Fin 4) :
    (reflectedFrame F m).period (reflectedFrame F m).top l = 4 * m := by
  simp [BlockFrame.period, reflectedFrame]
theorem reflectedCoords_add_unitStep (hm : 0 < m)
    (z : (reflectedFrame F m).Site (reflectedFrame F m).top) (i : Fin 4) :
    reflectedCoords m (z + unitStep _ i) = reflectedCoords m z +
      Pi.single i (if orientation m z i then (1 : ℤ) else -1) := by
  funext l
  by_cases h : l = i
  · subst h
    have e : (z + unitStep (reflectedFrame F m).top l :
        (reflectedFrame F m).Site (reflectedFrame F m).top) l = z l + 1 := by
      simp [unitStep, siteOfCoords]
    simp only [reflectedCoords, Pi.add_apply, Pi.single_eq_same, e]
    rw [reflectCoord_valMinAbs_add_one m _ hm (period_top m l)]
    unfold orientation
    rcases reflectCoord_succ_eq m (z l).valMinAbs with h1 | h1
    · simp [h1]
    · have : ¬ reflectCoord m (z l).valMinAbs - 1 = reflectCoord m (z l).valMinAbs + 1 := by
        omega
      simp only [h1, decide_eq_true_eq, this, decide_false]
      simp
      ring
  · have e : (z + unitStep (reflectedFrame F m).top i :
        (reflectedFrame F m).Site (reflectedFrame F m).top) l = z l := by
      simp [unitStep, siteOfCoords, Pi.single_eq_of_ne h]
    simp only [reflectedCoords, Pi.add_apply, e, Pi.single_eq_of_ne h, add_zero]
theorem orientation_add_unitStep (z : (reflectedFrame F m).Site (reflectedFrame F m).top)
    (μ ν : Fin 4) (h : μ ≠ ν) :
    orientation m (z + unitStep _ μ) ν = orientation m z ν := by
  have e : (z + unitStep (reflectedFrame F m).top μ :
      (reflectedFrame F m).Site (reflectedFrame F m).top) ν = z ν := by
    simp [unitStep, siteOfCoords, Pi.single_eq_of_ne h.symm]
  simp only [orientation, e]
def reflectedSite (z : (reflectedFrame F m).Site (reflectedFrame F m).top) : F.Cell :=
  y + siteOfCoords F.top (reflectedCoords m z)
theorem siteOfCoords_step (z : (reflectedFrame F m).Site (reflectedFrame F m).top) (i : Fin 4) :
    (siteOfCoords F.top (reflectedCoords m z +
        Pi.single i (if orientation m z i then (1 : ℤ) else -1)) : F.Cell) =
      siteOfCoords F.top (reflectedCoords m z) + stepDisplacement F.top (i, orientation m z i) := by
  rw [siteOfCoords_add]
  congr 1
  cases orientation m z i
  · simp only [stepDisplacement, Bool.false_eq_true, if_false, unitStep]
    funext l
    by_cases h : l = i
    · subst h
      simp [siteOfCoords]
    · simp [siteOfCoords, Pi.single_eq_of_ne h]
  · simp only [stepDisplacement, if_true, unitStep]
theorem reflectedSite_add_unitStep (hm : 0 < m)
    (z : (reflectedFrame F m).Site (reflectedFrame F m).top) (i : Fin 4) :
    reflectedSite m y (z + unitStep _ i) =
      reflectedSite m y z + stepDisplacement F.top (i, orientation m z i) := by
  unfold reflectedSite
  rw [reflectedCoords_add_unitStep m hm, siteOfCoords_step, add_assoc]
theorem reflectedField_eq_linkValue (z : (reflectedFrame F m).Site (reflectedFrame F m).top)
    (i : Fin 4) :
    reflectedField m y V z i = linkValue V (reflectedSite m y z) (i, orientation m z i) := by
  unfold reflectedField linkValue reflectedSite orientation
  dsimp only
  by_cases h : reflectCoord m ((z i).valMinAbs + 1) = reflectCoord m (z i).valMinAbs + 1
  · simp [h, reflectedCoords]
    rfl
  · have h1 : reflectCoord m ((z i).valMinAbs + 1) = reflectCoord m (z i).valMinAbs - 1 :=
      (reflectCoord_succ_eq m _).resolve_left h
    simp only [Pi.single_eq_same, h, if_false, decide_false, Bool.false_eq_true]
    congr 2
    have e : (fun l => reflectCoord m ((z l).valMinAbs + (Pi.single i 1 : Fin 4 → ℤ) l)) =
        reflectedCoords m z - Pi.single i 1 := by
      funext l
      by_cases hl : l = i
      · subst hl
        simp [reflectedCoords, h1]
      · simp [reflectedCoords, Pi.single_eq_of_ne hl]
    rw [e, siteOfCoords_sub, unitStep]
    change y + (siteOfCoords F.top (reflectedCoords m z) - _) =
      y + siteOfCoords F.top (reflectedCoords m z) - _
    abel
end Reflection
open Reflection in
theorem reflectedField_smallCurvature : ReflectedFieldSmallCurvature := by
  intro F m y V s hm hV p hp
  obtain ⟨z, μ, ν⟩ := p
  have hne : μ ≠ ν := ne_of_lt hp
  unfold plaquetteDefect
  rw [plaquetteHolonomy_eq, reflectedField_eq_linkValue, reflectedField_eq_linkValue,
    reflectedField_eq_linkValue, reflectedField_eq_linkValue, reflectedSite_add_unitStep m y hm,
    reflectedSite_add_unitStep m y hm, orientation_add_unitStep m z μ ν hne,
    orientation_add_unitStep m z ν μ hne.symm]
  exact norm_square_sub_one_lt hV _ μ ν hp _ _
end YangMills.Construction.ColdStepAtMirrorFrames
end
