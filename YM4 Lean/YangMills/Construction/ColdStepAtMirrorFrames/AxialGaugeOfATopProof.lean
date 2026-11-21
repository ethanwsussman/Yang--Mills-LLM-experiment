import YangMills.Construction.ClusterExpansionOfAStep.TreesOfABlock
import YangMills.Construction.ColdStepAtMirrorFrames.AxialGaugeOfATop
import YangMills.Construction.ColdStepAtMirrorFrames.PlainChainAtLevelZeroProof
import YangMills.Construction.ColdStepAtMirrorFrames.ResponsesNearAFlatTopProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
namespace AxialGauge
variable {F : BlockFrame}
theorem siteOfCoords_add {j : ℕ} (a b : Fin 4 → ℤ) :
    (siteOfCoords j (a + b) : F.Site j) = siteOfCoords j a + siteOfCoords j b := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_add <;> assumption
theorem axisPath_add_single {j : ℕ} (X : F.GaugeField j) (z : F.Site j) (o : Fin 4 → ℤ) (i : Fin 4)
    (ho : ∀ l, i < l → o l = 0) :
    pathHolonomy X z (axisPath (o + Pi.single i 1) 1) =
      pathHolonomy X z (axisPath o 1) * X (z + siteOfCoords j o) i := by apply _root_.YangMills.Construction.BlockTrees.pathHolonomy_axisPath_add_single <;> assumption
theorem plaquetteHolonomy_gaugeTransform {j : ℕ} (γ : F.Site j → UnitQuaternion) (V : F.GaugeField j)
    (x : F.Site j) (μ ν : Fin 4) :
    plaquetteHolonomy (gaugeTransform γ V) (x, μ, ν) = γ x * plaquetteHolonomy V (x, μ, ν) * (γ x)⁻¹ := by apply _root_.YangMills.SharedProofs.p16452 <;> assumption
theorem norm_conj_sub_one (g q : UnitQuaternion) :
    ‖((g * q * g⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ = ‖(q : ℍ[ℝ]) - 1‖ := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_conj_sub_one <;> assumption
theorem norm_sub_eq_norm_mul_inv_sub_one (a b : UnitQuaternion) :
    ‖(a : ℍ[ℝ]) - (b : ℍ[ℝ])‖ = ‖((a * b⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ := by apply _root_.YangMills.Construction.GaugedCriticality.norm_coe_sub_coe <;> assumption
theorem minimalOffset_of_withinRadius {r : ℕ} (z : F.Cell) (h : Fin 4 → ℤ) (hb : WithinRadius r h)
    (hs : ∀ i, 2 * r + 2 < F.extent i) : minimalOffset z (z + siteOfCoords F.top h) = h := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.NearUniformTop.minimalOffset_add_siteOfCoords <;> assumption
def tailLength (i : Fin 4) (o : Fin 4 → ℤ) : ℕ := ∑ l ∈ Finset.univ.filter (i < ·), (o l).natAbs
theorem tailLength_add_single (a : Fin 4 → ℤ) (i l : Fin 4) (hil : i < l) (d : ℤ)
    (h : ((a l + d).natAbs) + 1 = (a l).natAbs) : tailLength i (a + Pi.single l d) + 1 = tailLength i a := by
  unfold tailLength
  have hm : l ∈ Finset.univ.filter (i < ·) := by simp [hil]
  rw [← Finset.add_sum_erase _ _ hm, ← Finset.add_sum_erase _ (fun m => (a m).natAbs) hm]
  have e : ∑ m ∈ (Finset.univ.filter (i < ·)).erase l, ((a + Pi.single l d : Fin 4 → ℤ) m).natAbs =
      ∑ m ∈ (Finset.univ.filter (i < ·)).erase l, (a m).natAbs :=
    Finset.sum_congr rfl fun m hm' => by
      have : m ≠ l := (Finset.mem_erase.mp hm').1
      simp [Pi.single_eq_of_ne this]
  rw [e]
  simp only [Pi.add_apply, Pi.single_eq_same]
  omega
theorem withinRadius_add_single {r : ℕ} (a : Fin 4 → ℤ) (l : Fin 4) (d : ℤ) (h : WithinRadius r a)
    (h' : |a l + d| ≤ (r : ℤ)) : WithinRadius r (a + Pi.single l d) := by
  intro m
  by_cases hm : m = l
  · subst hm; simpa using h'
  · simpa [Pi.single_eq_of_ne hm] using h m
theorem tailLength_le {r : ℕ} (o : Fin 4 → ℤ) (i : Fin 4) (h : WithinRadius r o) :
    tailLength i o ≤ 3 * r := by
  unfold tailLength
  have hc : (Finset.univ.filter (fun l : Fin 4 => i < l)).card ≤ 3 := by
    have : Finset.univ.filter (fun l : Fin 4 => i < l) ⊆ Finset.univ.erase 0 := by
      intro l hl
      have : i < l := (Finset.mem_filter.mp hl).2
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      intro h0
      subst h0
      exact absurd this (Fin.not_lt_zero _)
    simpa using Finset.card_le_card this
  have hb : ∀ l ∈ Finset.univ.filter (fun l : Fin 4 => i < l), (o l).natAbs ≤ r := fun l _ => by
    have := abs_le.mp (h l)
    omega
  have := Finset.sum_le_card_nsmul _ _ _ hb
  simp only [smul_eq_mul] at this
  nlinarith
end AxialGauge
open AxialGauge
theorem axialGaugeBondBound_holds : AxialGaugeBondBound := by
  intro F V Y s r hs hs0 hcold
  set γ := axialGaugeHolonomy V Y with hγdef
  set X := gaugeTransform γ V with hXdef
  let P : (Fin 4 → ℤ) → UnitQuaternion := fun o => pathHolonomy V Y (axisPath o 1)
  have hγ : ∀ o, WithinRadius r o → γ (Y + siteOfCoords F.top o) = P o := fun o ho => by
    simp only [hγdef, axialGaugeHolonomy, P]
    rw [minimalOffset_of_withinRadius Y o ho hs]
  have hpos : ∀ (o : Fin 4 → ℤ) (i : Fin 4), Y + siteOfCoords F.top o + unitStep F.top i =
      Y + siteOfCoords F.top (o + Pi.single i 1) := fun o i => by
    rw [siteOfCoords_add, add_assoc]
    rfl
  have hX : ∀ (o : Fin 4 → ℤ) (i : Fin 4), WithinRadius r o → WithinRadius r (o + Pi.single i 1) →
      X (Y + siteOfCoords F.top o) i = P o * V (Y + siteOfCoords F.top o) i * (P (o + Pi.single i 1))⁻¹ := by
    intro o i h1 h2
    simp only [hXdef, gaugeTransform]
    rw [hpos, hγ o h1, hγ _ h2]
  have htree : ∀ (o : Fin 4 → ℤ) (i : Fin 4), WithinRadius r o → WithinRadius r (o + Pi.single i 1) →
      (∀ l, i < l → o l = 0) → X (Y + siteOfCoords F.top o) i = 1 := by
    intro o i h1 h2 ho
    rw [hX o i h1 h2]
    have := axisPath_add_single V Y o i ho
    simp only [P]
    rw [this]
    group
  have hplaq : ∀ (c : Fin 4 → ℤ) (i l : Fin 4), i < l → WithinRadius r c →
      WithinRadius r (c + Pi.single i 1) → WithinRadius r (c + Pi.single l 1) →
      WithinRadius r (c + Pi.single i 1 + Pi.single l 1) → (∀ m, l < m → c m = 0) →
      ‖((X (Y + siteOfCoords F.top c) i : UnitQuaternion) : ℍ[ℝ]) -
        (X (Y + siteOfCoords F.top (c + Pi.single l 1)) i : UnitQuaternion)‖ < s := by
    intro c i l hil h1 h2 h3 h4 hc
    have hp := hcold (Y + siteOfCoords F.top c, i, l) hil
    have hg : plaquetteHolonomy X (Y + siteOfCoords F.top c, i, l) =
        X (Y + siteOfCoords F.top c) i * (X (Y + siteOfCoords F.top (c + Pi.single l 1)) i)⁻¹ := by
      have a1 : X (Y + siteOfCoords F.top (c + Pi.single i 1)) l = 1 := by
        refine htree _ l h2 h4 fun m hm => ?_
        have hmi : m ≠ i := (hil.trans hm).ne'
        simp [Pi.single_eq_of_ne hmi, hc m hm]
      have a2 : X (Y + siteOfCoords F.top c) l = 1 := htree c l h1 h3 hc
      have e1 : Y + siteOfCoords F.top c + unitStep F.top i + unitStep F.top l - unitStep F.top i =
          Y + siteOfCoords F.top (c + Pi.single l 1) := by
        rw [← hpos]; abel
      have e2 : Y + siteOfCoords F.top c + unitStep F.top i + unitStep F.top l + -unitStep F.top i =
          Y + siteOfCoords F.top (c + Pi.single l 1) := by
        rw [← hpos]; abel
      have e3 : Y + siteOfCoords F.top (c + Pi.single l 1) - unitStep F.top l = Y + siteOfCoords F.top c := by
        rw [← hpos]; abel
      simp only [plaquetteHolonomy, pathHolonomy, linkValue, stepDisplacement, if_true, Bool.false_eq_true,
        if_false, e1, e2, e3, mul_one]
      rw [hpos c i, a1, a2]
      simp
    have hc2 : plaquetteDefect X (Y + siteOfCoords F.top c, i, l) =
        plaquetteDefect V (Y + siteOfCoords F.top c, i, l) := by
      simp only [plaquetteDefect]
      rw [hXdef, _root_.YangMills.Construction.ColdStepAtMirrorFrames.AxialGauge.plaquetteHolonomy_gaugeTransform, norm_conj_sub_one]
    rw [norm_sub_eq_norm_mul_inv_sub_one, ← hg]
    show plaquetteDefect X _ < s
    rw [hc2]
    exact hp
  have main : ∀ (n : ℕ) (o : Fin 4 → ℤ) (i : Fin 4), tailLength i o = n → WithinRadius r o →
      WithinRadius r (o + Pi.single i 1) →
      ‖((X (Y + siteOfCoords F.top o) i : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ n * s := by
    intro n
    induction n with
    | zero =>
      intro o i hd h1 h2
      have hz : ∀ l, i < l → o l = 0 := fun l hl => by
        have := (Finset.sum_eq_zero_iff.mp hd) l (by simp [hl])
        omega
      rw [htree o i h1 h2 hz]
      simp
    | succ n ih =>
      intro o i hd h1 h2
      have hne : (Finset.univ.filter fun l : Fin 4 => i < l ∧ o l ≠ 0).Nonempty := by
        by_contra hcon
        have hz : ∀ l ∈ Finset.univ.filter (i < ·), (o l).natAbs = 0 := fun l hl => by
          by_contra h0
          exact hcon ⟨l, by
            have : i < l := (Finset.mem_filter.mp hl).2
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨this, fun e => h0 (by simp [e])⟩⟩
        have : tailLength i o = 0 := Finset.sum_eq_zero hz
        omega
      set l := (Finset.univ.filter fun l : Fin 4 => i < l ∧ o l ≠ 0).max' hne with hl
      have hlm := (Finset.mem_filter.mp (Finset.max'_mem _ hne)).2
      rw [← hl] at hlm
      obtain ⟨hil, hol⟩ := hlm
      have hmax : ∀ m, l < m → o m = 0 := fun m hm => by
        by_contra h0
        have : m ≤ l := Finset.le_max' _ m (by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hil.trans hm, h0⟩)
        exact absurd hm (not_lt.mpr this)
      have hli : l ≠ i := hil.ne'
      have hbl := abs_le.mp (h1 l)
      rcases lt_or_gt_of_ne hol with hneg | hpos'
      · have b1 : WithinRadius r (o + Pi.single l 1) := withinRadius_add_single _ _ _ h1 (abs_le.mpr (by omega))
        have b2 : WithinRadius r (o + Pi.single i 1 + Pi.single l 1) :=
          withinRadius_add_single _ _ _ h2 (abs_le.mpr (by simp [Pi.single_eq_of_ne hli]; omega))
        have b3 : WithinRadius r (o + Pi.single l 1 + Pi.single i 1) := by
          rwa [add_right_comm]
        have hd' : tailLength i (o + Pi.single l 1) = n := by
          have := tailLength_add_single o i l hil 1 (by omega)
          omega
        have a1 := ih _ i hd' b1 b3
        have a2 := hplaq o i l hil h1 h2 b1 b2 hmax
        have := norm_sub_le_norm_sub_add_norm_sub ((X (Y + siteOfCoords F.top o) i : UnitQuaternion) : ℍ[ℝ])
          ((X (Y + siteOfCoords F.top (o + Pi.single l 1)) i : UnitQuaternion) : ℍ[ℝ]) 1
        push_cast
        nlinarith
      · have hc : o + Pi.single l (-1) + Pi.single l 1 = o := by
          funext m
          by_cases hm : m = l
          · subst hm; simp
          · simp [Pi.single_eq_of_ne hm]
        have b0 : WithinRadius r (o + Pi.single l (-1)) := withinRadius_add_single _ _ _ h1 (abs_le.mpr (by omega))
        have b1 : WithinRadius r (o + Pi.single l (-1) + Pi.single i 1) := by
          rw [add_right_comm]
          exact withinRadius_add_single _ _ _ h2 (abs_le.mpr (by simp [Pi.single_eq_of_ne hli]; omega))
        have b3 : WithinRadius r (o + Pi.single l (-1) + Pi.single i 1 + Pi.single l 1) := by
          rw [add_right_comm, hc]; exact h2
        have hd' : tailLength i (o + Pi.single l (-1)) = n := by
          have := tailLength_add_single o i l hil (-1) (by omega)
          omega
        have a1 := ih _ i hd' b0 b1
        have hmax' : ∀ m, l < m → (o + Pi.single l (-1) : Fin 4 → ℤ) m = 0 := fun m hm => by
          simp [Pi.single_eq_of_ne hm.ne', hmax m hm]
        have a2 := hplaq _ i l hil b0 b1 (by rw [hc]; exact h1) b3 hmax'
        rw [hc] at a2
        have := norm_sub_le_norm_sub_add_norm_sub ((X (Y + siteOfCoords F.top o) i : UnitQuaternion) : ℍ[ℝ])
          ((X (Y + siteOfCoords F.top (o + Pi.single l (-1))) i : UnitQuaternion) : ℍ[ℝ]) 1
        rw [norm_sub_rev] at a2
        push_cast
        nlinarith
  intro b hb
  have h := main _ b.1 b.2 rfl hb.1 hb.2
  have h3 := tailLength_le b.1 b.2 hb.1
  have h4 : ((tailLength b.2 b.1 : ℕ) : ℝ) ≤ 3 * r := by exact_mod_cast h3
  calc _ ≤ ((tailLength b.2 b.1 : ℕ) : ℝ) * s := h
    _ ≤ 3 * r * s := by gcongr
end ColdStepAtMirrorFrames
end YangMills.Construction
end
