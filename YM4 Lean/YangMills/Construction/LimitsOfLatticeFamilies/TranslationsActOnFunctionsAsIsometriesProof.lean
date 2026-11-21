import YangMills.Construction.LimitsOfLatticeFamilies.ClassC1AndTheGradientThroughTheLift
import YangMills.Construction.LimitsOfLatticeFamilies.LengthOfAPointGivesAnInvariantDistance
import YangMills.Construction.LimitsOfLatticeFamilies.ProjectionKernelsAndShortestLifts
import YangMills.Construction.LimitsOfLatticeFamilies.TranslationsActOnFunctionsAsIsometries
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.LatticeLimits.ShiftIsometry
open ModelSpace
variable {s : Conventions.StandingParameters} {Y : ModelSpace}
theorem dist_sub_sub (hN : InvariantDistFromNorm.Claim)
    (x y a : Y.Carrier s) : ModelSpace.dist s Y (x - a) (y - a) = ModelSpace.dist s Y x y := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact (hN s Y).2.2.2.2.2.2 x y (-a)
theorem mem_supportIn {E : Type*} [Zero E] (f : Y.Carrier s → E) (x : Y.Carrier s) :
    x ∈ ModelSpace.supportIn s Y f ↔
      ∀ r : ℝ, 0 < r → ∃ y, f y ≠ 0 ∧ ModelSpace.dist s Y x y < r := Iff.rfl
theorem supportIn_shift (hN : InvariantDistFromNorm.Claim) {E : Type*} [Zero E]
    (a : Y.Carrier s) (f : Y.Carrier s → E) :
    ModelSpace.supportIn s Y (ModelSpace.shift a f) =
      ModelSpace.shiftSet (ModelSpace.supportIn s Y f) a := by
  have hinv := (hN s Y).2.2.2.2.2.2
  ext x
  constructor
  · intro hx
    refine ⟨x - a, ?_, sub_add_cancel x a⟩
    rw [mem_supportIn]
    intro r hr
    obtain ⟨y, hy, hxy⟩ := (mem_supportIn _ _).1 hx r hr
    exact ⟨y - a, hy, by rwa [dist_sub_sub hN]⟩
  · rintro ⟨w, hw, rfl⟩
    rw [mem_supportIn]
    intro r hr
    obtain ⟨y, hy, hwy⟩ := (mem_supportIn _ _).1 hw r hr
    refine ⟨y + a, ?_, ?_⟩
    · show f (y + a - a) ≠ 0
      rwa [add_sub_cancel_right]
    · show ModelSpace.dist s Y (w + a) (y + a) < r
      rwa [hinv]
theorem isCompactIn_shiftSet (hN : InvariantDistFromNorm.Claim)
    (a : Y.Carrier s) {K : Set (Y.Carrier s)} (hK : ModelSpace.IsCompactIn s Y K) :
    ModelSpace.IsCompactIn s Y (ModelSpace.shiftSet K a) := by
  have hinv := (hN s Y).2.2.2.2.2.2
  have hK' : MetricNotions.IsCompactWrt (ModelSpace.dist s Y) K := hK
  show MetricNotions.IsCompactWrt (ModelSpace.dist s Y) (ModelSpace.shiftSet K a)
  intro 𝒰 hopen hcover
  let back : Y.Carrier s → Set (Y.Carrier s) → Set (Y.Carrier s) := fun b U => (· + b) ⁻¹' U
  have hback : ∀ U ∈ 𝒰, MetricNotions.IsOpenWrt (ModelSpace.dist s Y) (back a U) := by
    intro U hU x hx
    obtain ⟨r, hr, h⟩ : ∃ r : ℝ, 0 < r ∧ ∀ y, ModelSpace.dist s Y (x + a) y < r → y ∈ U :=
      hopen U hU (x + a) hx
    exact ⟨r, hr, fun y hy => h (y + a) (by rw [hinv]; exact hy)⟩
  have hcov : K ⊆ ⋃₀ (back a '' 𝒰) := by
    intro z hz
    obtain ⟨U, hU, hzU⟩ := hcover ⟨z, hz, rfl⟩
    exact ⟨back a U, ⟨U, hU, rfl⟩, hzU⟩
  obtain ⟨𝒱, hV, hfin, hcovV⟩ :=
    hK' (back a '' 𝒰) (by rintro _ ⟨U, hU, rfl⟩; exact hback U hU) hcov
  refine ⟨back (-a) '' 𝒱, ?_, hfin.image _, ?_⟩
  · rintro _ ⟨V, hVm, rfl⟩
    obtain ⟨U, hU, rfl⟩ := hV hVm
    have hret : back (-a) (back a U) = U := by
      ext y
      simp [back]
    rwa [hret]
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨V, hVm, hzV⟩ := hcovV hz
    refine ⟨back (-a) V, ⟨V, hVm, rfl⟩, ?_⟩
    simpa [back] using hzV
theorem proj_sub_lift (hK : ProjKernelAndMinimalLifts.Claim) {a : Y.Carrier s}
    {v : Fin 4 → ℝ} (hv : ModelSpace.proj s Y v = a) (x : Fin 4 → ℝ) :
    ModelSpace.proj s Y x - a = ModelSpace.proj s Y (x - v) := by
  have h := ((hK s).2 Y).1 (x - v) v
  rw [sub_add_cancel] at h
  rw [h, hv, add_sub_cancel_right]
theorem shift_comp_proj (hK : ProjKernelAndMinimalLifts.Claim)
    {a : Y.Carrier s} {v : Fin 4 → ℝ} (hv : ModelSpace.proj s Y v = a) {E : Type*}
    (f : Y.Carrier s → E) :
    ModelSpace.shift a f ∘ ModelSpace.proj s Y = (f ∘ ModelSpace.proj s Y) ∘ fun x => x - v := by
  funext x
  show f (ModelSpace.proj s Y x - a) = f (ModelSpace.proj s Y (x - v))
  rw [proj_sub_lift hK hv]
theorem isC1_shift (hK : ProjKernelAndMinimalLifts.Claim)
    (hD : C1ViaLift.Claim) (a : Y.Carrier s) {f : Y.Carrier s → ℝ}
    (hf : ModelSpace.IsC1 s Y f) : ModelSpace.IsC1 s Y (ModelSpace.shift a f) := by
  obtain ⟨v, hv⟩ := ((hK s).2 Y).2.1 a
  have h1 : ContDiff ℝ 1 (f ∘ ModelSpace.proj s Y) := ((hD s Y).1 f).1 hf
  refine ((hD s Y).1 _).2 ?_
  show ContDiff ℝ 1 (ModelSpace.shift a f ∘ ModelSpace.proj s Y)
  rw [shift_comp_proj hK hv]
  exact h1.comp (contDiff_id.sub contDiff_const)
theorem gradR4_comp_sub (F : (Fin 4 → ℝ) → ℝ) (v x : Fin 4 → ℝ) :
    ModelSpace.gradR4 (F ∘ fun x => x - v) x = ModelSpace.gradR4 F (x - v) := by
  funext μ
  show deriv (fun t : ℝ => F (x + t • Pi.single μ (1 : ℝ) - v)) 0 =
    deriv (fun t : ℝ => F (x - v + t • Pi.single μ (1 : ℝ))) 0
  have h : (fun t : ℝ => F (x + t • Pi.single μ (1 : ℝ) - v)) =
      fun t : ℝ => F (x - v + t • Pi.single μ (1 : ℝ)) := by
    funext t
    rw [add_sub_right_comm]
  rw [h]
theorem grad_shift (hK : ProjKernelAndMinimalLifts.Claim)
    (hD : C1ViaLift.Claim) (a : Y.Carrier s) {f : Y.Carrier s → ℝ}
    (hf : ModelSpace.IsC1 s Y f) :
    ModelSpace.grad s Y (ModelSpace.shift a f) = ModelSpace.shift a (ModelSpace.grad s Y f) := by
  obtain ⟨v, hv⟩ := ((hK s).2 Y).2.1 a
  have hT := isC1_shift hK hD a hf
  refine (((hD s Y).2.1 _ hT).2 _ ?_).symm
  rw [shift_comp_proj hK hv (ModelSpace.grad s Y f), ((hD s Y).2.1 f hf).1,
    shift_comp_proj hK hv f]
  funext x
  exact (gradR4_comp_sub _ v x).symm
theorem sharpNorm_shift (hN : InvariantDistFromNorm.Claim)
    (M : BlockScale s) (a : Y.Carrier s) (f : Y.Carrier s → ℝ) :
    ModelSpace.sharpNorm s M Y (ModelSpace.shift a f) = ModelSpace.sharpNorm s M Y f := by
  have hinv := (hN s Y).2.2.2.2.2.2
  have h1 : TestFunctions.uniformNorm (ModelSpace.shift a f) = TestFunctions.uniformNorm f :=
    (Equiv.subRight a).iSup_comp (g := fun x => ‖f x‖)
  have h2 : TestFunctions.bestLipschitzConstant (ModelSpace.dist s Y) (ModelSpace.shift a f) =
      TestFunctions.bestLipschitzConstant (ModelSpace.dist s Y) f := by
    unfold TestFunctions.bestLipschitzConstant
    congr 1
    ext C
    constructor
    · rintro ⟨hC0, hC⟩
      refine ⟨hC0, fun x y => ?_⟩
      have h := hC (x + a) (y + a)
      simpa only [ModelSpace.shift, add_sub_cancel_right, hinv] using h
    · rintro ⟨hC0, hC⟩
      refine ⟨hC0, fun x y => ?_⟩
      have h := hC (x - a) (y - a)
      rwa [dist_sub_sub hN] at h
  rw [ModelSpace.sharpNorm_eq_max, ModelSpace.sharpNorm_eq_max,
    ModelSpace.lipNumber_eq_bestLipschitzConstant, ModelSpace.lipNumber_eq_bestLipschitzConstant,
    h1, h2]
theorem shiftIsIsometry_holds (hK : ProjKernelAndMinimalLifts.Claim)
    (hN : InvariantDistFromNorm.Claim)
    (hD : C1ViaLift.Claim) :
    ShiftIsIsometry := by
  intro s M Y a
  refine ⟨⟨⟨Equiv.addRight a, fun x y => (hN s Y).2.2.2.2.2.2 x y a⟩, fun y => rfl, fun f => ?_⟩,
    fun f hf => ?_, fun n _ f hf => ?_, fun K hK' => isCompactIn_shiftSet hN a hK'⟩
  · funext y
    show f ((Equiv.addRight a).symm y) = f (y - a)
    simp [sub_eq_add_neg]
  · refine ⟨⟨isC1_shift hK hD a hf.1, ?_, subset_univ _⟩, supportIn_shift hN a f,
      grad_shift hK hD a hf.1, sharpNorm_shift hN M a f⟩
    rw [supportIn_shift hN]
    exact isCompactIn_shiftSet hN a hf.2.1
  · refine ⟨fun i => isC1_shift hK hD a (hf.1 i), fun i => ?_, fun i k hik => ?_⟩
    · show ModelSpace.IsCompactIn s Y (ModelSpace.supportIn s Y (ModelSpace.shift a (f i)))
      rw [supportIn_shift hN]
      exact isCompactIn_shiftSet hN a (hf.2.1 i)
    · show Disjoint (ModelSpace.supportIn s Y (ModelSpace.shift a (f i)))
        (ModelSpace.supportIn s Y (ModelSpace.shift a (f k)))
      rw [supportIn_shift hN, supportIn_shift hN, Set.disjoint_left]
      rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
      have hyx : y = x := add_right_cancel hxy
      subst hyx
      exact Set.disjoint_left.1 (hf.2.2 i k hik) hx hy
end YangMills.Construction.LatticeLimits.ShiftIsometry
end
