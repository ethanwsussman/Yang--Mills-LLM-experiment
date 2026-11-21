import YangMills.Construction.TorusOrFourSpace.ClassesAreVectorSpacesWithTheSharpNormProof
import YangMills.Construction.TorusOrFourSpace.CompactnessAndLiftsOfClosedBallsAndOriginBallsProof
import YangMills.Construction.TorusOrFourSpace.FiniteCoversByBallsAndPartitionsOfUnity
import Mathlib
set_option autoImplicit false
open scoped ContDiff
noncomputable section
namespace YangMills.Construction.PeriodicSpace
open Kind
namespace BallCoverProof
section Metric
variable {X : Type*} {d : X → X → ℝ}
theorem isOpenWrt_ball (hsymm : ∀ a b, d a b = d b a) (htri : ∀ a b c, d a c ≤ d a b + d b c)
    (x : X) (r : ℝ) : YangMills.Construction.MetricNotions.IsOpenWrt d {z | d z x < r} := by
  intro z hz
  have hz' : d z x < r := hz
  refine ⟨r - d z x, by linarith, fun w hw => ?_⟩
  have h1 := htri w z x
  have h2 := hsymm w z
  show d w x < r
  linarith
theorem exists_finite_subcover [Nonempty X]
    (hc : YangMills.Construction.MetricNotions.IsCompactWrt d (Set.univ : Set X))
    (V : X → Set X) (hV : ∀ y, YangMills.Construction.MetricNotions.IsOpenWrt d (V y))
    (hy : ∀ y, y ∈ V y) :
    ∃ s : Finset X, s.Nonempty ∧ ∀ z, ∃ y ∈ s, z ∈ V y := by
  classical
  obtain ⟨W, hsub, hfin, hcov⟩ := hc (Set.range V) (by rintro _ ⟨y, rfl⟩; exact hV y)
    (fun z _ => ⟨V z, ⟨z, rfl⟩, hy z⟩)
  have hpick : ∀ U : W, ∃ y, V y = U := fun U => hsub U.2
  choose f hf using hpick
  have := hfin.fintype
  have hall : ∀ z, ∃ y ∈ Finset.univ.image f, z ∈ V y := by
    intro z
    obtain ⟨U, hU, hz⟩ := hcov (Set.mem_univ z)
    refine ⟨f ⟨U, hU⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    rw [hf]
    exact hz
  obtain ⟨z⟩ := ‹Nonempty X›
  obtain ⟨y, hy', _⟩ := hall z
  exact ⟨_, ⟨y, hy'⟩, hall⟩
theorem isOpenWrt_compl_closureWrt
    (htri : ∀ a b c, d a c ≤ d a b + d b c) (Z : Set X) :
    YangMills.Construction.MetricNotions.IsOpenWrt d
      (YangMills.Construction.MetricNotions.closureWrt d Z)ᶜ := by apply _root_.YangMills.DeltaSharedProofs.p500759 <;> assumption
theorem isCompactWrt_closureWrt
    (htri : ∀ a b c, d a c ≤ d a b + d b c)
    (hc : YangMills.Construction.MetricNotions.IsCompactWrt d (Set.univ : Set X)) (Z : Set X) :
    YangMills.Construction.MetricNotions.IsCompactWrt d
      (YangMills.Construction.MetricNotions.closureWrt d Z) := by
  intro U hU hcov
  set C : Set X := (YangMills.Construction.MetricNotions.closureWrt d Z)ᶜ with hC
  obtain ⟨W, hsub, hfin, hW⟩ := hc (insert C U)
    (by
      intro V hV
      rcases Set.mem_insert_iff.1 hV with rfl | hV
      · exact isOpenWrt_compl_closureWrt htri Z
      · exact hU V hV)
    (by
      intro z _
      by_cases hz : z ∈ YangMills.Construction.MetricNotions.closureWrt d Z
      · obtain ⟨V, hV, hzV⟩ := hcov hz
        exact ⟨V, Set.mem_insert_of_mem _ hV, hzV⟩
      · exact ⟨C, Set.mem_insert _ _, hz⟩)
  refine ⟨W \ {C}, ?_, hfin.subset Set.sdiff_subset, ?_⟩
  · rintro V ⟨hV, hVC⟩
    rcases Set.mem_insert_iff.1 (hsub hV) with h | h
    · exact absurd h hVC
    · exact h
  · intro z hz
    obtain ⟨V, hV, hzV⟩ := hW (Set.mem_univ z)
    refine ⟨V, ⟨hV, ?_⟩, hzV⟩
    rintro rfl
    exact hzV hz
theorem le_of_mem_closureWrt (htri : ∀ a b c, d a c ≤ d a b + d b c) {Z : Set X} {c : X}
    {e : ℝ} (hZ : ∀ z ∈ Z, d z c < e) {y : X}
    (hy : y ∈ YangMills.Construction.MetricNotions.closureWrt d Z) : d y c ≤ e := by
  refine le_of_forall_pos_le_add fun r hr => ?_
  obtain ⟨z, hz, hyz⟩ := hy r hr
  have h1 := htri y z c
  have h2 := hZ z hz
  linarith
theorem isOpenWrt_ne_zero_of_lipschitz {u : X → ℝ}
    (hu : YangMills.Construction.TestFunctions.IsLipschitzFor d u) :
    YangMills.Construction.MetricNotions.IsOpenWrt d {z | u z ≠ 0} := by
  obtain ⟨C, hC0, hC⟩ := hu
  intro z hz
  have hz' : u z ≠ 0 := hz
  have hpos : 0 < |u z| := abs_pos.2 hz'
  refine ⟨|u z| / (C + 1), by positivity, fun w hw => ?_⟩
  intro hw0
  have h1 := hC z w
  rw [hw0, sub_zero, Real.norm_eq_abs] at h1
  have h2 : (C + 1) * d z w < |u z| := by
    rw [lt_div_iff₀ (by linarith)] at hw
    linarith
  by_cases hd : 0 ≤ d z w
  · nlinarith
  · have h3 : C * d z w ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hC0 (by linarith)
    linarith
end Metric
theorem two_mul_div_sq_le_sin_sq {ℓ s : ℝ} (hℓ : 0 < ℓ) (hs : |s| ≤ ℓ / 2) :
    (2 * s / ℓ) ^ 2 ≤ Real.sin (Real.pi * s / ℓ) ^ 2 := by
  have hπ := Real.pi_pos
  have hu0 : 0 ≤ Real.pi * |s| / ℓ := by positivity
  have hu1 : Real.pi * |s| / ℓ ≤ Real.pi / 2 := by
    rw [div_le_iff₀ hℓ]
    nlinarith
  have key := Real.mul_le_sin hu0 hu1
  have e1 : 2 / Real.pi * (Real.pi * |s| / ℓ) = 2 * |s| / ℓ := by
    field_simp
  rw [e1] at key
  have h0 : 0 ≤ 2 * |s| / ℓ := by positivity
  have h2 : (2 * |s| / ℓ) ^ 2 ≤ Real.sin (Real.pi * |s| / ℓ) ^ 2 := pow_le_pow_left₀ h0 key 2
  have e2 : (2 * |s| / ℓ) ^ 2 = (2 * s / ℓ) ^ 2 := by
    rw [div_pow, div_pow, mul_pow, mul_pow, sq_abs]
  have e3 : Real.sin (Real.pi * |s| / ℓ) ^ 2 = Real.sin (Real.pi * s / ℓ) ^ 2 := by
    rcases abs_cases s with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · have e : Real.pi * -s / ℓ = -(Real.pi * s / ℓ) := by ring
      rw [h, e, Real.sin_neg, neg_sq]
  rwa [e2, e3] at h2
theorem sin_sq_add_int_mul_pi_eq (a : ℝ) (n : ℤ) :
    Real.sin (a + n * Real.pi) ^ 2 = Real.sin a ^ 2 := by
  rw [Real.sin_add_int_mul_pi, mul_pow]
  rcases Int.even_or_odd n with h | h
  · rw [h.neg_one_zpow]; ring
  · rw [h.neg_one_zpow]; ring
def sinSqDist (ℓ : ℝ) (x₀ x : Fin 4 → ℝ) : ℝ :=
  ∑ μ, Real.sin (Real.pi * (x μ - x₀ μ) / ℓ) ^ 2
theorem contDiff_sinSqDist (ℓ : ℝ) (x₀ : Fin 4 → ℝ) : ContDiff ℝ ∞ (sinSqDist ℓ x₀) := by
  unfold sinSqDist
  refine ContDiff.sum fun μ _ => ?_
  have h1 : ContDiff ℝ ∞ fun x : Fin 4 → ℝ => Real.pi * (x μ - x₀ μ) / ℓ :=
    ((contDiff_const.mul ((contDiff_apply ℝ ℝ μ).sub contDiff_const)).div_const ℓ)
  exact (Real.contDiff_sin.comp h1).pow 2
theorem sinSqDist_self (ℓ : ℝ) (x₀ : Fin 4 → ℝ) : sinSqDist ℓ x₀ x₀ = 0 := by
  simp [sinSqDist]
theorem side_pos (D : Params) : 0 < D.side := by apply _root_.YangMills.SharedProofs.p25685 <;> assumption
theorem exists_smooth_bump (hS : QuotientCompactC1.Claim)
    (hW : WellPosedness.WellPosed) (D : Params) (y₀ : Pt D torus) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ ψ : Pt D torus → ℝ, ψ ∈ smoothSet D torus ∧ (∀ y, 0 ≤ ψ y) ∧ 0 < ψ y₀ ∧
      ∀ y, ψ y ≠ 0 → quotDist D torus y y₀ < ε := by
  classical
  obtain ⟨-, -, -, -, hq, -⟩ := (hS D torus).1
  obtain ⟨-, hlift, hper, -⟩ := hW D torus
  have hℓ := side_pos D
  have hne : D.side ≠ 0 := hℓ.ne'
  choose lift hliftq using hlift
  set x₀ := lift y₀ with hx₀
  set δ : ℝ := 4 * ε ^ 2 / D.side ^ 2 with hδ
  have hδpos : 0 < δ := by positivity
  set g : (Fin 4 → ℝ) → ℝ := fun x => expNegInvGlue (δ - sinSqDist D.side x₀ x) with hg
  have hgsmooth : ContDiff ℝ ∞ g :=
    expNegInvGlue.contDiff.comp (contDiff_const.sub (contDiff_sinSqDist _ _))
  have hgper : ∀ x x' : Fin 4 → ℝ, quotMap D torus x = quotMap D torus x' → g x = g x' := by
    intro x x' hxx
    obtain ⟨n, hn⟩ := (hper x x').1 ⟨_, rfl, hxx.symm⟩
    have hw : sinSqDist D.side x₀ x = sinSqDist D.side x₀ x' := by
      unfold sinSqDist
      refine Finset.sum_congr rfl fun μ _ => ?_
      have hμ : x μ = x' μ + (n μ : ℝ) * D.side := by
        have := hn μ
        simp only [Pi.sub_apply] at this
        linarith
      have e : Real.pi * (x μ - x₀ μ) / D.side =
          Real.pi * (x' μ - x₀ μ) / D.side + (n μ : ℝ) * Real.pi := by
        rw [hμ]
        field_simp
        ring
      rw [e, sin_sq_add_int_mul_pi_eq]
    show expNegInvGlue (δ - sinSqDist D.side x₀ x) = expNegInvGlue (δ - sinSqDist D.side x₀ x')
    rw [hw]
  have hcomp : ∀ x, g (lift (quotMap D torus x)) = g x := fun x =>
    hgper _ _ (hliftq _)
  refine ⟨fun y => g (lift y), ?_, fun y => expNegInvGlue.nonneg _, ?_, ?_⟩
  · have e : (fun y => g (lift y)) ∘ quotMap D torus = g := funext hcomp
    show ContDiff ℝ ∞ ((fun y => g (lift y)) ∘ quotMap D torus)
    rw [e]
    exact hgsmooth
  · show 0 < expNegInvGlue (δ - sinSqDist D.side x₀ (lift y₀))
    rw [← hx₀, sinSqDist_self, sub_zero]
    exact expNegInvGlue.pos_of_pos hδpos
  · intro y hy
    have hy' : expNegInvGlue (δ - sinSqDist D.side x₀ (lift y)) ≠ 0 := hy
    have hlt : sinSqDist D.side x₀ (lift y) < δ := by
      by_contra hcon
      exact hy' (expNegInvGlue.zero_of_nonpos (by linarith))
    set x := lift y with hx
    set k : Fin 4 → ℤ := fun μ => round ((x μ - x₀ μ) / D.side) with hk
    set s : Fin 4 → ℝ := fun μ => x μ - x₀ μ - (k μ : ℝ) * D.side with hs
    have hsabs : ∀ μ, |s μ| ≤ D.side / 2 := by
      intro μ
      have h := abs_sub_round ((x μ - x₀ μ) / D.side)
      have e : s μ = ((x μ - x₀ μ) / D.side - (k μ : ℝ)) * D.side := by
        simp only [hs]
        field_simp
      rw [e, abs_mul, abs_of_pos hℓ]
      nlinarith
    have hterm : ∀ μ, (2 * s μ / D.side) ^ 2 ≤
        Real.sin (Real.pi * (x μ - x₀ μ) / D.side) ^ 2 := by
      intro μ
      have h := two_mul_div_sq_le_sin_sq hℓ (hsabs μ)
      have e : Real.pi * (x μ - x₀ μ) / D.side =
          Real.pi * s μ / D.side + (k μ : ℝ) * Real.pi := by
        simp only [hs]
        field_simp
        ring
      rw [e, sin_sq_add_int_mul_pi_eq]
      exact h
    have hsum : ∑ μ, (2 * s μ / D.side) ^ 2 < δ :=
      lt_of_le_of_lt (Finset.sum_le_sum fun μ _ => hterm μ) hlt
    have hsq : ∑ μ, s μ ^ 2 < ε ^ 2 := by
      have e : ∑ μ, (2 * s μ / D.side) ^ 2 = 4 * (∑ μ, s μ ^ 2) / D.side ^ 2 := by
        rw [Finset.mul_sum, Finset.sum_div]
        refine Finset.sum_congr rfl fun μ _ => ?_
        field_simp
        ring
      rw [e, hδ] at hsum
      have := (div_lt_div_iff_of_pos_right (by positivity : 0 < D.side ^ 2)).1 hsum
      linarith
    have hnorm : YangMills.Construction.TorusMetric.euclidNormVec s < ε := by
      unfold YangMills.Construction.TorusMetric.euclidNormVec
      rw [Real.sqrt_lt' hε]
      exact hsq
    have hsame : quotMap D torus (x₀ + s) = quotMap D torus x := by
      obtain ⟨y', h1, h2⟩ := (hper (x₀ + s) x).2 ⟨-k, fun μ => by
        simp only [hs, Pi.sub_apply, Pi.add_apply, Pi.neg_apply, Int.cast_neg]
        ring⟩
      exact h1.trans h2.symm
    have hd := hq (x₀ + s) x₀
    rw [hsame, add_sub_cancel_left] at hd
    have e1 : quotMap D torus x = y := hliftq y
    have e2 : quotMap D torus x₀ = y₀ := hliftq y₀
    rw [e1, e2] at hd
    linarith
theorem smooth_regularity (hS : QuotientCompactC1.Claim) (D : Params)
    (χ : Pt D torus → ℝ) (hχ : χ ∈ smoothSet D torus) :
    IsC1Fn D torus χ ∧ IsCompactQ D torus (supportQ D torus χ) ∧
      IsLipschitzQ D torus χ ∧
      vecSupNormQ D torus (gradVec D torus χ) ≠ ⊤ ∧
      ENNReal.ofReal (lipConstQ D torus χ) =
        vecSupNormQ D torus (gradVec D torus χ) := by
  obtain ⟨⟨-, -, hsymm, htri, -, -⟩, -, hc, -, hf⟩ := hS D torus
  have h1 : IsC1Fn D torus χ := by
    have h : ContDiff ℝ ∞ (χ ∘ quotMap D torus) := hχ
    exact show ContDiff ℝ 1 (χ ∘ quotMap D torus) from h.of_le (by exact_mod_cast le_top)
  have h2 : IsCompactQ D torus (supportQ D torus χ) :=
    isCompactWrt_closureWrt htri hc _
  obtain ⟨-, -, h3, -, h4, h5, -, -⟩ := hf χ h1 h2
  refine ⟨h1, h2, h4, ?_, h5⟩
  have h6 : vecSupNormQ D torus (gradVec D torus χ) ≤ euclidC1Norm D torus χ :=
    le_max_right _ _
  exact (lt_of_le_of_lt h6 h3).ne
theorem torusBallCoversAndPartitionsOfUnity_holds (hS : QuotientCompactC1.Claim)
    (hW : WellPosedness.WellPosed) :
    TorusBallCoversAndPartitionsOfUnity := by
  classical
  intro D r hr
  obtain ⟨⟨-, hzero, hsymm, htri, -, -⟩, -, hc, -, -⟩ := hS D torus
  have : Nonempty (Pt D torus) := ⟨0⟩
  have hself : ∀ y : Pt D torus, quotDist D torus y y = 0 := fun y => (hzero y y).2 rfl
  refine ⟨?_, ?_, smooth_regularity hS D⟩
  · obtain ⟨s, hs, hcov⟩ := exists_finite_subcover hc (fun x => torusBall D x r)
      (fun x => isOpenWrt_ball hsymm htri x r)
      (fun y => by
        show quotDist D torus y y < r
        rw [hself]
        exact hr)
    refine ⟨s.card, Finset.card_pos.2 hs, fun i => (s.equivFin.symm i).1, fun z => ?_⟩
    obtain ⟨y, hy, hz⟩ := hcov z
    refine ⟨s.equivFin ⟨y, hy⟩, ?_⟩
    simpa using hz
  · intro J _ x hcov
    choose j hj using hcov
    have hj' : ∀ y, quotDist D torus y (x (j y)) < r := hj
    set ε : Pt D torus → ℝ := fun y => (r - quotDist D torus y (x (j y))) / 2 with hεdef
    have hε : ∀ y, 0 < ε y := fun y => by
      have := hj' y
      simp only [hεdef]
      linarith
    choose ψ hψs hψ0 hψpos hψsupp using fun y => exists_smooth_bump hS hW D y (ε y) (hε y)
    obtain ⟨s, hs, hcov'⟩ := exists_finite_subcover hc (fun y => {z | ψ y z ≠ 0})
      (fun y => isOpenWrt_ne_zero_of_lipschitz (smooth_regularity hS D (ψ y) (hψs y)).2.2.1)
      (fun y => (hψpos y).ne')
    have hsumpos : ∀ y, 0 < ∑ a : s, ψ a y := by
      intro y
      obtain ⟨a, ha, hya⟩ := hcov' y
      refine Finset.sum_pos' (fun b _ => hψ0 _ _) ⟨⟨a, ha⟩, Finset.mem_univ _, ?_⟩
      exact lt_of_le_of_ne (hψ0 a y) (Ne.symm hya)
    refine ⟨s, inferInstance, hs.to_subtype, fun a y => ψ a y / ∑ b : s, ψ b y, ?_, ?_, ?_⟩
    · intro a
      refine ⟨?_, fun y => ⟨div_nonneg (hψ0 _ _) (hsumpos y).le, ?_⟩⟩
      · have hnum : ContDiff ℝ ∞ (ψ a ∘ quotMap D torus) := hψs a
        have hden : ContDiff ℝ ∞ fun v => ∑ b : s, (ψ b ∘ quotMap D torus) v :=
          ContDiff.sum fun b _ => hψs b
        exact hnum.div hden fun v => (hsumpos _).ne'
      · rw [div_le_one (hsumpos y)]
        exact Finset.single_le_sum (f := fun b : s => ψ b y) (fun b _ => hψ0 _ _)
          (Finset.mem_univ a)
    · intro y
      rw [← Finset.sum_div]
      exact div_self (hsumpos y).ne'
    · intro a
      refine ⟨j a, fun y hy => ?_⟩
      have hle : quotDist D torus y a ≤ ε a := by
        refine le_of_mem_closureWrt htri (fun z hz => ?_) hy
        refine hψsupp a z fun h0 => hz ?_
        simp [h0]
      have h1 := htri y a (x (j a))
      have h2 := hj' a
      have h3 : ε a = (r - quotDist D torus a (x (j a))) / 2 := rfl
      show quotDist D torus y (x (j a)) < r
      linarith
end BallCoverProof
end YangMills.Construction.PeriodicSpace
