import YangMills.Construction.ColdStepAtMirrorFrames.AxialRotationsOfATop
import YangMills.Construction.ColdStepAtMirrorFrames.FieldNearTheFlatField
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
open BlockOffsets
theorem chartedField_near_one : ChartedFieldNearOne := by
  intro F w V Y q s R b hs hq hs0 hn hw hb
  obtain ⟨x, i⟩ := b
  have hpos : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  set d := cellSupDist Y (enclosingCell x) with hd
  have hnear : distFromOne (V (enclosingCell x) i) ≤ 3 * ((d : ℝ) + 1) * s := by
    set z := enclosingCell x with hz
    set o := minimalOffset Y z with ho
    have hzo : Y + siteOfCoords F.top o = z := by
      funext l
      have : NeZero (F.period F.top l) := ⟨by rw [period_top]; have := hpos l; omega⟩
      show Y l + (((((z - Y : F.Cell)) l).valMinAbs : ℤ) : ZMod (F.period F.top l)) = z l
      rw [ZMod.coe_valMinAbs]
      simp
    have hsz : ∀ l, (o l).natAbs ≤ d := by
      intro l
      have h1 : (((Y - z : F.Cell)) l).valMinAbs.natAbs ≤ cellSupDist Y z :=
        Finset.le_sup (f := fun l => (((Y - z : F.Cell)) l).valMinAbs.natAbs) (Finset.mem_univ l)
      have : NeZero (F.period F.top l) := ⟨by rw [period_top]; have := hpos l; omega⟩
      have e : ((Y - z : F.Cell)) l = -(((z - Y : F.Cell)) l) := by simp
      rw [e, ZMod.natAbs_valMinAbs_neg] at h1
      exact h1
    have hbox : BondWithinRadius (d + 1) (o, i) := by
      refine ⟨fun l => ?_, fun l => ?_⟩
      · have := hsz l
        show |o l| ≤ ((d + 1 : ℕ) : ℤ)
        rw [abs_le]
        push_cast
        omega
      · have := hsz l
        show |((o + Pi.single i 1 : Fin 4 → ℤ)) l| ≤ ((d + 1 : ℕ) : ℤ)
        rw [abs_le]
        push_cast
        by_cases e : l = i
        · subst e
          simp only [Pi.add_apply, Pi.single_eq_same]
          omega
        · simp only [Pi.add_apply, Pi.single_eq_of_ne e, add_zero]
          omega
    have := hn (d + 1) (o, i) hb hbox
    simp only [hzo] at this
    push_cast at this
    exact this
  have hd0 : (0 : ℝ) ≤ 3 * ((d : ℝ) + 1) * s := by positivity
  unfold chartedField
  split_ifs with hc ht
  · have h1 := (distFromOne_mul (expUnit (w x i)) (V (enclosingCell x) i)).trans (add_le_add (distFromOne_expUnit_le (w x i)) hnear)
    have h2 := hw (x, i) (fun q' => q'.1 hc)
    linarith
  · rw [distFromOne_one]
    positivity
  · have h1 := distFromOne_expUnit_le (w x i)
    have h2 := hw (x, i) ht
    linarith
end YangMills.Construction.ColdStepAtMirrorFrames
end
