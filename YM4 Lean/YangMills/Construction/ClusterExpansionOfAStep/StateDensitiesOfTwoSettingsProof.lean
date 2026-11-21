import YangMills.Construction.ClusterExpansionOfAStep.StateDensitiesOfTwoSettings
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages StepSettings TorusFields TorusLumps BlockOffsets
theorem blockDensitiesClose : BlockDensitiesClose := by
  intro R n n' _ _ s s' Y Y' m k η η' hadm hexp hn hn' hs hs' hag hk2 hk hr hnear hb hb'
  have hodd := hadm.L_odd
  have hn0 := hadm.n₀_ge
  have h2 : 2 ≤ n := by omega
  have h2' : 2 ≤ n' := by omega
  have hL : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hk1 : 1 ≤ k := by omega
  set m₂ := R.params.side * k - 2 * R.params.side with hm₂
  have hm₂le : m₂ ≤ R.params.side * k - R.params.side := by omega
  have hbs : IsBlockTorusSide R.params (n * R.params.side) :=
    ⟨Dvd.intro_left _ rfl, by rw [mul_comm]; exact Nat.mul_le_mul_right _ hn⟩
  have hbs' : IsBlockTorusSide R.params (n' * R.params.side) :=
    ⟨Dvd.intro_left _ rfl, by rw [mul_comm]; exact Nat.mul_le_mul_right _ hn'⟩
  have hext : ∀ N : ℕ, 2 * m + 2 < N → 2 * m₂ + 2 < N * R.params.side := by
    intro N hN
    have h1 : (2 * m + 3) * R.params.side ≤ N * R.params.side := Nat.mul_le_mul_right _ hN
    have h2 : R.params.side * k ≤ R.params.side * m := Nat.mul_le_mul_left _ hk
    have h3 : (2 * m + 3) * R.params.side = 2 * (R.params.side * m) + 3 * R.params.side := by ring
    omega
  have hterm : ∀ o ∈ centredCube R.params.side,
      |R.siteDensity (n * R.params.side) (fineSite R.params.side Y 0 o) (s.field η) s.support s.labelling -
        R.siteDensity (n' * R.params.side) (fineSite R.params.side Y' 0 o) (s'.field η') s'.support s'.labelling| ≤
        Real.exp (-R.params.decayRate * (m₂ : ℝ)) := by
    intro o ho
    have hfa := fieldsAgreeNear_of_settings hodd h2 h2' hs.subset_chart hag hk1 hk hnear ho
    refine hexp.2.forget (n * R.params.side) (n' * R.params.side) hbs hbs' _ _ _ _ _ _ _ _ m₂
      (hs.isHull η hb) (hs'.isHull η' hb') (hs.factor_ne_zero η hb) (hs'.factor_ne_zero η' hb') hr ?_
    refine ⟨hext n hag.lt_extent, hext n' hag.lt_extent', ?_, ?_, ?_, ?_⟩
    · intro b hbb
      exact hfa b ⟨fun l => (hbb.1 l).trans (by exact_mod_cast hm₂le),
        fun l => (hbb.2 l).trans (by exact_mod_cast hm₂le)⟩
    · intro h hh
      obtain ⟨j, o', ho', hj, hx⟩ := exists_fineSite_add hodd hk1 ho
        (fun l => (hh l).trans (by exact_mod_cast hm₂le) :
          OffsetInBox (R.params.side * k - R.params.side) h)
      rw [hx, hx]
      exact hag.support_iff j o' (fun l => by have := hj l; omega) ho'
    · intro h hh hz hz' _
      obtain ⟨j, o', ho', hj, hx⟩ := exists_fineSite_add hodd hk1 ho
        (fun l => (hh l).trans (by exact_mod_cast hm₂le) :
          OffsetInBox (R.params.side * k - R.params.side) h)
      have e1 := hx _ Y
      have e2 := hx _ Y'
      have hz1 : fineSite R.params.side Y j o' ∈ s.support := e1 ▸ hz
      have hz2 : fineSite R.params.side Y' j o' ∈ s'.support := e2 ▸ hz'
      have := hag.labelling_eq j o' hz1 hz2 (fun l => by have := hj l; omega) ho'
      calc s.labelling ⟨_, hz⟩ = s.labelling ⟨_, hz1⟩ := by congr 1; exact Subtype.ext e1
        _ = s'.labelling ⟨_, hz2⟩ := this
        _ = s'.labelling ⟨_, hz'⟩ := by congr 1; exact Subtype.ext e2.symm
    · intro _
      exact sameBlockPosition_fineSite R.params Y Y' 0 o
  have hsum : ∀ (N : ℕ) [NeZero N] (s₀ : ChartSetting R N) (Z : TorusSite N) (ζ : FreeCoords s₀.free),
      s₀.blockDensityAt Z ζ = ∑ o ∈ centredCube R.params.side,
        R.siteDensity (N * R.params.side) (fineSite R.params.side Z 0 o) (s₀.field ζ) s₀.support s₀.labelling := by
    intro N _ s₀ Z ζ
    exact sum_sitesInBlocks hodd Z _
  rw [hsum, hsum, ← Finset.sum_sub_distrib]
  calc |∑ o ∈ centredCube R.params.side, _| ≤ ∑ o ∈ centredCube R.params.side, _ := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _o ∈ centredCube R.params.side, Real.exp (-R.params.decayRate * (m₂ : ℝ)) := Finset.sum_le_sum hterm
    _ = (R.params.side : ℝ) ^ 4 * Real.exp (-R.params.decayRate * (m₂ : ℝ)) := by
      rw [Finset.sum_const, card_centredCube hodd, nsmul_eq_mul]
      push_cast
      ring
end YangMills.Construction.ClusterExpansionOfAStep
end
