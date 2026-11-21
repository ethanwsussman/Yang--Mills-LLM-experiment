import YangMills.Construction.ColdChainAtEveryLevel.ChartOverAnotherTopProof
import YangMills.Construction.SummableBoundsOfTheFlow.LinesOfTwoTops
import YangMills.Construction.SummableBoundsOfTheFlow.ShortMovesOfAChart
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.ChartLipschitz
namespace YangMills.Construction.DerivativeInterpolation
namespace HolonomyPerturbation
variable {F : BlockFrame}
theorem norm_coe_unitQuaternion (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := CStarRing.norm_coe_unitary g
theorem unitQuaternion_coe_mul (a b : UnitQuaternion) :
    ((a * b : UnitQuaternion) : ℍ[ℝ]) = (a : ℍ[ℝ]) * (b : ℍ[ℝ]) := rfl
theorem norm_sub_mul_le (a a' b b' : UnitQuaternion) :
    ‖((a * b : UnitQuaternion) : ℍ[ℝ]) - ((a' * b' : UnitQuaternion) : ℍ[ℝ])‖ ≤
      ‖(a : ℍ[ℝ]) - (a' : ℍ[ℝ])‖ + ‖(b : ℍ[ℝ]) - (b' : ℍ[ℝ])‖ := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.coe_mul_sub_mul_le <;> assumption
theorem norm_sub_inv_eq (a a' : UnitQuaternion) :
    ‖((a⁻¹ : UnitQuaternion) : ℍ[ℝ]) - ((a'⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ = ‖(a : ℍ[ℝ]) - (a' : ℍ[ℝ])‖ := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.norm_sub_inv_inv <;> assumption
theorem norm_sub_pathHolonomy_le {j : ℕ} {W W' : F.GaugeField j} {ε : ℝ}
    (h : ∀ y i, ‖((W y i : UnitQuaternion) : ℍ[ℝ]) - ((W' y i : UnitQuaternion) : ℍ[ℝ])‖ ≤ ε)
    (l : List PathStep) :
    ∀ x : F.Site j, ‖((pathHolonomy W x l : UnitQuaternion) : ℍ[ℝ]) -
      ((pathHolonomy W' x l : UnitQuaternion) : ℍ[ℝ])‖ ≤ l.length * ε := by
  induction l with
  | nil =>
    intro x
    simp [pathHolonomy]
  | cons st r ih =>
    intro x
    simp only [pathHolonomy, List.length_cons, Nat.cast_add, Nat.cast_one]
    refine (norm_sub_mul_le _ _ _ _).trans ?_
    have hs : ‖((linkValue W x st : UnitQuaternion) : ℍ[ℝ]) -
        ((linkValue W' x st : UnitQuaternion) : ℍ[ℝ])‖ ≤ ε := by
      unfold linkValue
      split_ifs
      · exact h _ _
      · rw [norm_sub_inv_eq]
        exact h _ _
    have := ih (x + stepDisplacement j st)
    linarith
theorem plaquetteDefect_le_add {j : ℕ} {W W' : F.GaugeField j} {ε : ℝ}
    (h : ∀ y i, ‖((W y i : UnitQuaternion) : ℍ[ℝ]) - ((W' y i : UnitQuaternion) : ℍ[ℝ])‖ ≤ ε) (h0 : 0 ≤ ε)
    (p : F.Site j × Fin 4 × Fin 4) : plaquetteDefect W p ≤ plaquetteDefect W' p + 4 * ε := by
  unfold plaquetteDefect plaquetteHolonomy
  have h1 := norm_sub_pathHolonomy_le h [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] p.1
  simp only [List.length_cons, List.length_nil] at h1
  have h2 := norm_sub_le_norm_sub_add_norm_sub
    ((pathHolonomy W p.1 [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] : UnitQuaternion) : ℍ[ℝ])
    ((pathHolonomy W' p.1 [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] : UnitQuaternion) : ℍ[ℝ]) 1
  norm_num at h1
  linarith
theorem norm_bondSpread_le {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (s : ℝ) (hX : ∀ l, ‖X l‖ ≤ 1) (y : F.Site F.top) (i : Fin 4) :
    ‖ColdStepAtMirrorFrames.bondSpread c X (fun _ => s) y i‖ ≤ k * |s| := by
  unfold ColdStepAtMirrorFrames.bondSpread
  refine (norm_sum_le _ _).trans ?_
  calc _ ≤ ∑ _l : Fin k, |s| := by
        refine Finset.sum_le_sum fun l _ => ?_
        split_ifs
        · rw [norm_smul, Real.norm_eq_abs]
          calc |s| * ‖X l‖ ≤ |s| * 1 := mul_le_mul_of_nonneg_left (hX l) (abs_nonneg _)
            _ = |s| := mul_one _
        · simp
    _ = k * |s| := by simp
theorem eq_of_siteOfCoords_eq {r : ℕ} {u v : Fin 4 → ℤ} (hu : WithinRadius r u) (hv : WithinRadius r v)
    (hs : ∀ i, F.extent i = 0 ∨ 2 * r + 2 < F.extent i)
    (h : (siteOfCoords F.top u : F.Site F.top) = siteOfCoords F.top v) :
    u = v := by
  funext i
  have hi := congrFun h i
  simp only [siteOfCoords] at hi
  have hper : F.period F.top i = F.extent i := by
    simp [BlockFrame.period]
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hi
  obtain ⟨q, hq⟩ := hi
  have a1 := abs_le.1 (hu i)
  have a2 := abs_le.1 (hv i)
  rw [hper] at hq
  rcases hs i with h0 | h0
  · rw [h0] at hq
    simp at hq
    omega
  · have hpos : (2 * (r : ℤ) + 2) < (F.extent i : ℤ) := by exact_mod_cast h0
    have hb : |(F.extent i : ℤ) * q| ≤ 2 * r := by
      rw [← hq]
      exact abs_le.2 ⟨by omega, by omega⟩
    have hq0 : q = 0 := by
      by_contra hne
      have h1 : (1 : ℤ) ≤ |q| := Int.one_le_abs hne
      have h2 : |(F.extent i : ℤ) * q| = (F.extent i : ℤ) * |q| := by
        rw [abs_mul, abs_of_nonneg (by positivity)]
      rw [h2] at hb
      nlinarith
    rw [hq0] at hq
    simp at hq
    omega
end HolonomyPerturbation
open HolonomyPerturbation in
theorem smallCurvatureAlongLineAndAgreeOn (hs : ChartedFieldLipschitz) :
    SmallCurvatureAlongLineAndAgreeOn := by
  refine ⟨?_, ?_⟩
  · intro F V k c X s u hX hV p hp
    have hclose : ∀ y i, ‖((alongLine c X s V y i : UnitQuaternion) : ℍ[ℝ]) -
        ((V y i : UnitQuaternion) : ℍ[ℝ])‖ ≤ k * |s| := by
      intro y i
      have h1 := hs.1 (ColdStepAtMirrorFrames.bondSpread c X (fun _ => s) y i) 0
      have h2 : expUnit (0 : imaginaryQuaternions) = 1 := Subtype.ext (by simp [expUnit, NormedSpace.exp_zero])
      rw [h2] at h1
      simp only [sub_zero] at h1
      have e : ((alongLine c X s V y i : UnitQuaternion) : ℍ[ℝ]) - ((V y i : UnitQuaternion) : ℍ[ℝ]) =
          (((expUnit (ColdStepAtMirrorFrames.bondSpread c X (fun _ => s) y i) : UnitQuaternion) : ℍ[ℝ]) -
            (((1 : UnitQuaternion)) : ℍ[ℝ])) * ((V y i : UnitQuaternion) : ℍ[ℝ]) := by
        have e1 : (((1 : UnitQuaternion)) : ℍ[ℝ]) = 1 := rfl
        simp only [alongLine, leftTranslate, unitQuaternion_coe_mul, e1, sub_mul, one_mul]
      rw [e, norm_mul, _root_.YangMills.Construction.DerivativeInterpolation.HolonomyPerturbation.norm_coe_unitQuaternion, mul_one]
      exact h1.trans (norm_bondSpread_le c X s hX y i)
    have h3 := plaquetteDefect_le_add hclose (by positivity) p
    have h4 := hV p hp
    have : 4 * ((k : ℝ) * |s|) = 4 * k * |s| := by ring
    linarith
  · intro F F' V V' Y Y' r k h X s hA hb
    obtain ⟨a1, a2, a3, a4⟩ := hA
    refine ⟨a1, a2, a3, fun b hbb => ?_⟩
    simp only [alongLine, leftTranslate]
    rw [a4 b hbb]
    congr 2
    simp only [ColdStepAtMirrorFrames.bondSpread, bondsAt]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hiff : ((Y + siteOfCoords F.top (h l).1, (h l).2) = (Y + siteOfCoords F.top b.1, b.2)) ↔
        ((Y' + siteOfCoords F'.top (h l).1, (h l).2) = (Y' + siteOfCoords F'.top b.1, b.2)) := by
      simp only [Prod.mk.injEq, add_right_inj]
      constructor
      · rintro ⟨e1, e2⟩
        rw [eq_of_siteOfCoords_eq (hb l).1 hbb.1 a1 e1]
        exact ⟨rfl, e2⟩
      · rintro ⟨e1, e2⟩
        rw [eq_of_siteOfCoords_eq (hb l).1 hbb.1 a2 e1]
        exact ⟨rfl, e2⟩
    exact if_congr hiff rfl rfl
end YangMills.Construction.DerivativeInterpolation
end
