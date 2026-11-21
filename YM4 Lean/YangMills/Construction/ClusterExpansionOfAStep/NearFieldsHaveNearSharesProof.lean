import YangMills.Construction.ClusterExpansionOfAStep.NearFieldsHaveNearShares
import YangMills.Construction.ClusterExpansionOfAStep.TopFrameOfATorus
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ShareContinuity
open BlockAverages LumpContours GaugeFixing TorusFields TorusShares TorusLumps TorusFrame StepCosts
variable {m : ℕ}
def spliceOn (S : Finset (TorusBond m)) (W W' : TorusField m) : TorusField m :=
  open Classical in fun x i => if (x, i) ∈ S then W' x i else W x i
theorem norm_coe_unitQuaternion (g : UnitQuaternion) : ‖((g : UnitQuaternion) : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
theorem norm_mul_sub_right (g h : UnitQuaternion) :
    ‖((g * h : UnitQuaternion) : ℍ[ℝ]) - h‖ = ‖(g : ℍ[ℝ]) - 1‖ := by
  have : ((g * h : UnitQuaternion) : ℍ[ℝ]) - h = ((g : ℍ[ℝ]) - 1) * h := by
    rw [Submonoid.coe_mul, sub_mul, one_mul]
  rw [this, norm_mul, norm_coe_unitQuaternion, mul_one]
theorem norm_mul_inv_sub_one (g h : UnitQuaternion) :
    ‖((g * h⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ = ‖(g : ℍ[ℝ]) - h‖ := by apply _root_.YangMills.Construction.GaugeFixing.norm_mul_inv_sub_one <;> assumption
theorem isColdOn_of_near {X : Finset (TorusSite m)} {s e : ℝ} {W F : TorusField m} (hW : IsColdOn X s W)
    (hc : ∀ x i, ‖(F x i : ℍ[ℝ]) - W x i‖ ≤ e) : IsColdOn X (s + 4 * e) F := by
  intro x μ ν hμν hcor
  have h1 := curvature_le_add F W x μ ν
  have h2 := hW x μ ν hμν hcor
  have h3 := hc x μ
  have h4 := hc (x + TorusFields.unitStep m μ) ν
  have h5 := hc (x + TorusFields.unitStep m ν) μ
  have h6 := hc x ν
  linarith
theorem share_spliceOn_le {a : ℝ} {L : ℕ} {s₀ A δ : ℝ} (hS : ShareLocality a L s₀ A δ) (hA : 0 ≤ A)
    (hδ : 0 ≤ δ) (t : ℕ) [NeZero m] {X : Finset (TorusSite m)} {W W' : TorusField m} {y : TorusSite m}
    {s ε : ℝ} (hm : 64 ≤ m) (hs : 0 < s)
    (hε : 0 ≤ ε) (hs₀ : s + 8 * ε ≤ s₀) (hX : IsLocallyOrthantClosed X 1024) (hcW : IsColdOn X s W)
    {Bx : Finset (TorusBond m)} (hclose : ∀ b ∈ Bx, ‖(W b.1 b.2 : ℍ[ℝ]) - W' b.1 b.2‖ ≤ ε) :
    ∀ S : Finset (TorusBond m), S ⊆ Bx → (∀ x i, ‖(spliceOn S W W' x i : ℍ[ℝ]) - W x i‖ ≤ ε) ∧
      |levelShare a L t X y (spliceOn S W W') - levelShare a L t X y W| ≤ A * (2 * ε) * S.card := by
  classical
  have hε2 : ε ≤ 2 * ε := by linarith
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _
    have h0 : spliceOn ∅ W W' = W := by
      funext x i
      simp [spliceOn]
    rw [h0]
    simp [hε]
  | insert b S hbS ih =>
    intro hsub
    obtain ⟨ih1, ih2⟩ := ih fun c hc => hsub (Finset.mem_insert_of_mem hc)
    have hbB : b ∈ Bx := hsub (Finset.mem_insert_self _ _)
    set W₁ := spliceOn S W W' with hW₁
    have hW₁b : W₁ b.1 b.2 = W b.1 b.2 := by
      simp [hW₁, spliceOn, hbS]
    set v : imaginaryQuaternions := minimalLog (W' b.1 b.2 * (W b.1 b.2)⁻¹) with hv
    have hvn : ‖(v : ℍ[ℝ])‖ ≤ 2 * ε := by
      have h1 := norm_minimalLog_le (W' b.1 b.2 * (W b.1 b.2)⁻¹)
      rw [norm_mul_inv_sub_one, norm_sub_rev] at h1
      have h2 := hclose b hbB
      linarith
    have hturn : spliceOn (insert b S) W W' = multiplyAtBond b v W₁ := by
      funext x i
      by_cases hxb : (x, i) = b
      · have e1 : multiplyAtBond b v W₁ x i = expUnit v * W₁ x i := by
          simp [multiplyAtBond, hxb]
        subst hxb
        have e2 : spliceOn (insert (x, i) S) W W' x i = W' x i := by
          simp [spliceOn]
        rw [e1, e2]
        have hW₁b' : W₁ x i = W x i := hW₁b
        rw [hW₁b', hv, expUnit_minimalLog]
        simp
      · have e1 : multiplyAtBond b v W₁ x i = W₁ x i := by
          simp [multiplyAtBond, hxb]
        rw [e1]
        simp [spliceOn, hW₁, hxb]
    have hcold : ∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 →
        IsColdOn X (s + 8 * ε) (multiplyAtBond b (τ • v) W₁) := by
      intro τ h0 h1
      have hc := isColdOn_of_near (e := 2 * ε) (F := multiplyAtBond b (τ • v) W₁) hcW (fun x i => ?_)
      · have e : s + 4 * (2 * ε) = s + 8 * ε := by ring
        rwa [e] at hc
      · by_cases hxb : (x, i) = b
        · have e1 : multiplyAtBond b (τ • v) W₁ x i = expUnit (τ • v) * W₁ x i := by
            simp [multiplyAtBond, hxb]
          subst hxb
          have hW₁b' : W₁ x i = W x i := hW₁b
          rw [e1, hW₁b', norm_mul_sub_right]
          refine (norm_expUnit_sub_one_le _).trans ?_
          have e2 : ‖((τ • v : imaginaryQuaternions) : ℍ[ℝ])‖ = τ * ‖(v : ℍ[ℝ])‖ := by
            rw [Submodule.coe_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg h0]
          rw [e2]
          have := norm_nonneg (v : ℍ[ℝ])
          nlinarith
        · have e1 : multiplyAtBond b (τ • v) W₁ x i = W₁ x i := by
            simp [multiplyAtBond, hxb]
          rw [e1]
          exact (ih1 x i).trans hε2
    have hpos : 0 < s + 8 * ε := by positivity
    have h3 := hS.twist_bound t m X W₁ b v y (s + 8 * ε) hm hpos hs₀ hX hcold
    have hE : Real.exp (-(δ * supDist y b.1)) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      have : 0 ≤ δ * (supDist y b.1 : ℝ) := by positivity
      linarith
    have h4 : A * ‖(v : ℍ[ℝ])‖ * Real.exp (-(δ * supDist y b.1)) ≤ A * (2 * ε) := by
      have h5 : A * ‖(v : ℍ[ℝ])‖ ≤ A * (2 * ε) := mul_le_mul_of_nonneg_left hvn hA
      have h6 : 0 ≤ A * ‖(v : ℍ[ℝ])‖ := by positivity
      nlinarith [Real.exp_pos (-(δ * supDist y b.1))]
    constructor
    · intro x i
      rw [hturn]
      by_cases hxb : (x, i) = b
      · have e1 : multiplyAtBond b v W₁ x i = expUnit v * W₁ x i := by
          simp [multiplyAtBond, hxb]
        have e2 : spliceOn (insert b S) W W' x i = W' x i := by
          simp [spliceOn, hxb]
        rw [← hturn, e2]
        subst hxb
        rw [norm_sub_rev]
        exact hclose _ hbB
      · have e1 : multiplyAtBond b v W₁ x i = W₁ x i := by
          simp [multiplyAtBond, hxb]
        rw [e1]
        exact ih1 x i
    · rw [hturn, Finset.card_insert_of_notMem hbS]
      have h7 := abs_sub_le (levelShare a L t X y (multiplyAtBond b v W₁)) (levelShare a L t X y W₁)
        (levelShare a L t X y W)
      push_cast
      have h8 : |levelShare a L t X y (multiplyAtBond b v W₁) - levelShare a L t X y W₁| ≤ A * (2 * ε) :=
        h3.trans h4
      nlinarith
theorem shareLipschitzInField_holds : ShareLipschitzInField := by
  classical
  intro a L s₀ A δ hS hA hδ t m _ X X' W W' y ρ s ε hm hs hε hs₀ hX hX' hcW hcW'
  refine ⟨fun hρ hbox hnear => ?_, fun hXX hall => ?_⟩
  swap
  · subst hXX
    have hclose : ∀ b ∈ (Finset.univ : Finset (TorusBond m)), ‖(W b.1 b.2 : ℍ[ℝ]) - W' b.1 b.2‖ ≤ ε :=
      fun b _ => hall b.1 b.2
    obtain ⟨-, k2⟩ := share_spliceOn_le hS hA hδ t (y := y) hm hs hε hs₀ hX hcW hclose Finset.univ
      (Finset.Subset.refl _)
    have hW : spliceOn Finset.univ W W' = W' := by
      funext x i
      simp [spliceOn]
    rw [hW, abs_sub_comm] at k2
    have hcard : ((Finset.univ : Finset (TorusBond m)).card : ℝ) = (m : ℝ) ^ 4 * 4 := by
      simp [Finset.card_univ, Fintype.card_prod, ZMod.card]
    rw [hcard] at k2
    refine k2.trans (le_of_eq ?_)
    ring
  set I : Finset ((Fin 4 → ℤ) × Fin 4) := ((Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(ρ : ℤ)) ρ) ×ˢ
    (Finset.univ : Finset (Fin 4))).filter (BondOffsetInBox ρ) with hI
  set Bx : Finset (TorusBond m) := I.image (fun q => bondFrom y q) with hBx
  have hclose : ∀ b ∈ Bx, ‖(W b.1 b.2 : ℍ[ℝ]) - W' b.1 b.2‖ ≤ ε := by
    intro b hb
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hb
    exact hnear q (Finset.mem_filter.mp hq).2
  have key := share_spliceOn_le hS hA hδ t (y := y) hm hs hε hs₀ hX hcW hclose
  obtain ⟨k1, k2⟩ := key Bx (Finset.Subset.refl _)
  set W₂ := spliceOn Bx W W' with hW₂
  have hcold₂ : IsColdOn X (s + 8 * ε) W₂ := by
    have hc := isColdOn_of_near (e := ε) hcW k1
    intro x μ ν hμν hcor
    have := hc x μ ν hμν hcor
    linarith
  have hcold' : IsColdOn X' (s + 8 * ε) W' := by
    intro x μ ν hμν hcor
    have := hcW' x μ ν hμν hcor
    linarith
  have hpos : 0 < s + 8 * ε := by positivity
  have hagree : RegionsAgreeNear X X' W₂ W' y ρ := by
    refine ⟨hρ, hbox, fun b hb => ?_⟩
    have hmem : bondFrom y b ∈ Bx := by
      refine Finset.mem_image.mpr ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩, hb⟩, rfl⟩
      refine Fintype.mem_piFinset.mpr fun i => Finset.mem_Icc.mpr ?_
      exact abs_le.mp (hb.1 i)
    show W₂ (bondFrom y b).1 (bondFrom y b).2 = _
    simp only [hW₂, spliceOn]
    rw [if_pos hmem]
  have h1 := hS.decay_of_agreement t m X X' W₂ W' y ρ (s + 8 * ε) hm hpos hs₀ hX hX' hcold₂ hcold' hagree
  have hcard : (Bx.card : ℝ) ≤ 4 * (2 * (ρ : ℝ) + 1) ^ 4 := by
    have h2 : Bx.card ≤ I.card := Finset.card_image_le
    have h3 : I.card ≤ (2 * ρ + 1) ^ 4 * 4 := by
      refine (Finset.card_filter_le _ _).trans ?_
      rw [Finset.card_product, Fintype.card_piFinset]
      simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      have : ((ρ : ℤ) + 1 - -(ρ : ℤ)).toNat = 2 * ρ + 1 := by omega
      rw [this]
    have h4 : (Bx.card : ℝ) ≤ ((2 * ρ + 1) ^ 4 * 4 : ℕ) := by exact_mod_cast h2.trans h3
    push_cast at h4
    linarith
  have h5 : A * (2 * ε) * (Bx.card : ℝ) ≤ A * (2 * ε) * (4 * (2 * (ρ : ℝ) + 1) ^ 4) :=
    mul_le_mul_of_nonneg_left hcard (by positivity)
  have h6 := abs_sub_le (levelShare a L t X y W) (levelShare a L t X y W₂) (levelShare a L t X' y W')
  have h7 : |levelShare a L t X y W - levelShare a L t X y W₂| =
      |levelShare a L t X y W₂ - levelShare a L t X y W| :=
    abs_sub_comm _ _
  rw [h7] at h6
  linarith
end YangMills.Construction.ShareContinuity
end
