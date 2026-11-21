import YangMills.Construction.TransferOperators.ReversalOfTheFunctionOfTheStepBetweenSymmetricStacksProof
import YangMills.Construction.TransferOperators.TwoEliminationsOfTheStepBetweenSymmetricStacks
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory Set InfiniteLattice SpinHarmonics Matrices.ComplexMatrix2
namespace TransferOperators.CenteredStackElimination
variable {μ : Fin 4}
theorem const_mem_smoothOrder {K : Type} (q : ℕ) (c : ℂ) :
    (fun _ : K → specialUnitary => c) ∈ smoothOrder q := by apply _root_.YangMills.Construction.SpinHarmonics.FieldCalculus.const_mem_smoothOrder <;> assumption
theorem const_mem_smoothSet {K : Type} (c : ℂ) :
    (fun _ : K → specialUnitary => c) ∈ smoothSet :=
  mem_iInter.2 fun q => const_mem_smoothOrder q c
theorem precomp_mem_smoothOrder {K L : Type} {e : K → L} (he : Function.Injective e) (q : ℕ) :
    ∀ F : (K → specialUnitary) → ℂ, F ∈ smoothOrder q →
      (fun u : L → specialUnitary => F fun a => u (e a)) ∈ smoothOrder q := by
  classical
  have hcomp : Continuous fun u : L → specialUnitary => fun a => u (e a) :=
    continuous_pi fun a => continuous_apply (e a)
  induction q with
  | zero =>
    intro F hF
    exact (show Continuous F from hF).comp hcomp
  | succ q ih =>
    intro F hF
    obtain ⟨hc, hfld⟩ := hF
    refine ⟨hc.comp hcomp, fun b ι => ?_⟩
    by_cases hb : ∃ a, e a = b
    · obtain ⟨a, rfl⟩ := hb
      have hm : ∀ (u : L → specialUnitary) (t : ℝ), (fun x => shiftAt u (e a) ι t (e x)) =
          shiftAt (fun x => u (e x)) a ι t := by
        intro u t
        funext x
        unfold shiftAt
        by_cases hx : x = a
        · subst hx
          simp
        · have hne : e x ≠ e a := fun h => hx (he h)
          rw [Function.update_of_ne hx, Function.update_of_ne hne]
      constructor
      · intro u
        have h := (hfld a ι).1 (fun x => u (e x))
        unfold HasDirDerivAt at h ⊢
        simpa only [hm] using h
      · have e₁ : rightField (e a) ι (fun u : L → specialUnitary => F fun x => u (e x)) =
            fun u => rightField a ι F fun x => u (e x) := by
          funext u
          unfold rightField
          simp only [hm]
        rw [e₁]
        exact ih _ (hfld a ι).2
    · have hm : ∀ (u : L → specialUnitary) (t : ℝ), (fun x => shiftAt u b ι t (e x)) =
          fun x => u (e x) := by
        intro u t
        funext x
        unfold shiftAt
        exact Function.update_of_ne (fun h => hb ⟨x, h⟩) _ _
      constructor
      · intro u
        unfold HasDirDerivAt
        simp only [hm]
        exact differentiableAt_const _
      · have e₁ : rightField b ι (fun u : L → specialUnitary => F fun x => u (e x)) = fun _ => 0 := by
          funext u
          unfold rightField
          simp only [hm]
          simp
        rw [e₁]
        exact const_mem_smoothOrder q 0
theorem precomp_mem_smoothSet {K L : Type} {e : K → L} (he : Function.Injective e)
    {F : (K → specialUnitary) → ℂ} (hF : F ∈ smoothSet) :
    (fun u : L → specialUnitary => F fun a => u (e a)) ∈ smoothSet :=
  mem_iInter.2 fun q => precomp_mem_smoothOrder he q F (mem_iInter.1 hF q)
theorem continuous_of_mem_smoothSet {J : Type} {F : (J → specialUnitary) → ℂ} (hF : F ∈ smoothSet) :
    Continuous F :=
  mem_iInter.1 hF 0
section Real
variable {J : Type}
def IsSmoothReal (F : C(J → specialUnitary, ℂ)) : Prop :=
  (F : (J → specialUnitary) → ℂ) ∈ smoothSet ∧ ∀ u, (F u).im = 0
def IsSmoothPos (W : C(J → specialUnitary, ℂ)) : Prop :=
  (W : (J → specialUnitary) → ℂ) ∈ smoothSet ∧ ∀ u, (W u).im = 0 ∧ 0 < (W u).re
theorem IsSmoothPos.isSmoothReal {W : C(J → specialUnitary, ℂ)} (h : IsSmoothPos W) :
    IsSmoothReal W :=
  ⟨h.1, fun u => (h.2 u).1⟩
theorem IsSmoothPos.ne_zero {W : C(J → specialUnitary, ℂ)} (h : IsSmoothPos W) (u : J → specialUnitary) :
    W u ≠ 0 := fun e => by
  have := (h.2 u).2
  rw [e] at this
  simp at this
def recipMap (W : C(J → specialUnitary, ℂ)) (h : IsSmoothPos W) : C(J → specialUnitary, ℂ) :=
  ⟨fun u => (W u)⁻¹, W.continuous.inv₀ h.ne_zero⟩
theorem mul_recipMap {W : C(J → specialUnitary, ℂ)} (h : IsSmoothPos W) :
    W * recipMap W h = 1 := by
  ext u
  exact mul_inv_cancel₀ (h.ne_zero u)
variable (hcalc : FieldCalculus.AllRules) [Finite J] [Nonempty J]
include hcalc
theorem mem_smoothSet_mul {F H : (J → specialUnitary) → ℂ} (hF : F ∈ smoothSet)
    (hH : H ∈ smoothSet) : (fun u => F u * H u) ∈ smoothSet := by
  obtain ⟨⟨A, hA⟩, -⟩ := (hcalc.2.2 J).2.1 ⊤
  have hA' : (A : Set ((J → specialUnitary) → ℂ)) = smoothSet := hA
  rw [← hA'] at hF hH ⊢
  exact A.mul_mem hF hH
theorem mem_smoothSet_neg {F : (J → specialUnitary) → ℂ} (hF : F ∈ smoothSet) :
    (fun u => -F u) ∈ smoothSet := by
  obtain ⟨⟨A, hA⟩, -⟩ := (hcalc.2.2 J).2.1 ⊤
  have hA' : (A : Set ((J → specialUnitary) → ℂ)) = smoothSet := hA
  rw [← hA'] at hF ⊢
  exact A.neg_mem hF
theorem mem_smoothSet_finprod {I : Type} [Finite I] (G : I → (J → specialUnitary) → ℂ)
    (hG : ∀ i, G i ∈ smoothSet) : (fun u => ∏ᶠ i, G i u) ∈ smoothSet := by
  obtain ⟨⟨A, hA⟩, -⟩ := (hcalc.2.2 J).2.1 ⊤
  have hA' : (A : Set ((J → specialUnitary) → ℂ)) = smoothSet := hA
  let _ : Fintype I := Fintype.ofFinite I
  have e : (fun u => ∏ᶠ i, G i u) = ∏ i, G i := by
    funext u
    simp [finprod_eq_prod_of_fintype, Finset.prod_apply]
  rw [e, ← hA']
  refine prod_mem fun i _ => ?_
  exact show G i ∈ (A : Set ((J → specialUnitary) → ℂ)) from by
    rw [hA']
    exact hG i
theorem IsSmoothReal.mul {F H : C(J → specialUnitary, ℂ)} (hF : IsSmoothReal F) (hH : IsSmoothReal H) :
    IsSmoothReal (F * H) := by
  refine ⟨mem_smoothSet_mul hcalc hF.1 hH.1, fun u => ?_⟩
  have h₁ := hF.2 u
  have h₂ := hH.2 u
  simp [Complex.mul_im, h₁, h₂]
theorem IsSmoothPos.mul {F H : C(J → specialUnitary, ℂ)} (hF : IsSmoothPos F)
    (hH : IsSmoothPos H) : IsSmoothPos (F * H) := by
  refine ⟨mem_smoothSet_mul hcalc hF.1 hH.1, fun u => ?_⟩
  have h₁ := hF.2 u
  have h₂ := hH.2 u
  refine ⟨by simp [Complex.mul_im, h₁.1, h₂.1], ?_⟩
  simp only [ContinuousMap.mul_apply, Complex.mul_re, h₁.1, h₂.1, mul_zero, sub_zero]
  exact mul_pos h₁.2 h₂.2
theorem IsSmoothPos.recipMap {W : C(J → specialUnitary, ℂ)} (h : IsSmoothPos W) :
    IsSmoothReal (recipMap W h) := by
  refine ⟨(hcalc.2.2 J).2.2.2.2.1.2 _ h.1 h.2, fun u => ?_⟩
  have h₁ := (h.2 u).1
  show ((W u)⁻¹).im = 0
  simp [Complex.inv_im, h₁]
end Real
theorem exp_im_eq_zero_and_re_pos {x : ℂ} (hx : x.im = 0) :
    (Complex.exp x).im = 0 ∧ 0 < (Complex.exp x).re := by
  have e : x = (x.re : ℂ) := Complex.ext rfl (by simpa using hx)
  rw [e]
  refine ⟨Complex.exp_ofReal_im _, ?_⟩
  rw [Complex.exp_ofReal_re]
  exact Real.exp_pos _
section Hat
theorem hatSum_congr {J : Type} [Finite J] (β : ℝ) {B B' : Set J} (hB : B = B')
    {f : (↥B → specialUnitary) → ℂ} {f' : (↥B' → specialUnitary) → ℂ} (hf : IsRealEntryPolynomial f)
    (hf' : IsRealEntryPolynomial f')
    (hff : ∀ v : ↥B' → specialUnitary, f (fun b => v ⟨b.1, hB ▸ b.2⟩) = f' v) (F : C(J → specialUnitary, ℂ)) :
    hatSum β B f hf F = hatSum β B' f' hf' F := by
  subst hB
  obtain rfl : f = f' := funext fun v => hff v
  rfl
variable (hpass : MulThroughLinkKernelStatement)
  (hfacts : SeveralVariables.SeveralVariablesFacts) (hcalc : FieldCalculus.AllRules)
include hpass hfacts
theorem hatSum_smooth_and_properties {J : Type} [Finite J] [Nonempty J] {β : ℝ} (hβ : 0 < β) {P : Set J}
    (hP : P.Nonempty) {p : (↥P → specialUnitary) → ℂ} (hp : IsRealEntryPolynomial p) :
    (∀ F : C(J → specialUnitary, ℂ), (F : (J → specialUnitary) → ℂ) ∈ smoothSet →
      (hatSum β P p hp F : (J → specialUnitary) → ℂ) ∈ smoothSet) ∧
    HatProperties β P p hp := by
  have : Nonempty P := hP.to_subtype
  obtain ⟨D, hD⟩ := ((hfacts ↥P (fun _ => ⟨0⟩) ⟨0⟩).2.2.2.2.2.2.2.1 p hp.1).2
  obtain ⟨hser, hprop⟩ := (hpass J).2.2.2.2 β P p hp D hβ hP hD
  refine ⟨fun F hF => ?_, hprop⟩
  obtain ⟨-, -, -, -, -, -, -, hsm, -⟩ := hser F hF
  exact hsm
theorem hatSum_isSmoothReal {J : Type} [Finite J] [Nonempty J] {β : ℝ} (hβ : 0 < β) {P : Set J}
    (hP : P.Nonempty) {p : (↥P → specialUnitary) → ℂ} (hp : IsRealEntryPolynomial p) {F : C(J → specialUnitary, ℂ)}
    (hF : IsSmoothReal F) : IsSmoothReal (hatSum β P p hp F) := by
  obtain ⟨hs, ⟨-, hreal, -⟩⟩ := hatSum_smooth_and_properties hpass hfacts hβ hP hp
  exact ⟨hs F hF.1, hreal F hF.1 hF.2⟩
include hcalc
theorem hatSum_mul_of_indep {J : Type} [Finite J] [Nonempty J] {β : ℝ} (hβ : 0 < β) {P : Set J}
    (hP : P.Nonempty) (hPc : Pᶜ.Nonempty) {p : (↥P → specialUnitary) → ℂ} (hp : IsRealEntryPolynomial p)
    {T : C(J → specialUnitary, ℂ)} (hT : (T : (J → specialUnitary) → ℂ) ∈ smoothSet)
    (hind : ∀ u u' : J → specialUnitary, (∀ x, x ∉ P → u x = u' x) → T u = T u')
    {F : C(J → specialUnitary, ℂ)} (hF : (F : (J → specialUnitary) → ℂ) ∈ smoothSet) :
    hatSum β P p hp (T * F) = T * hatSum β P p hp F := by
  obtain ⟨-, ⟨-, -, hcomm, -⟩⟩ := hatSum_smooth_and_properties hpass hfacts hβ hP hp
  have : Nonempty ↥Pᶜ := hPc.to_subtype
  have hne : Pᶜ ≠ univ := fun h => by
    obtain ⟨x, hx⟩ := hP
    have hx' : x ∈ Pᶜ := h ▸ mem_univ x
    exact hx' hx
  let z₀ : ↥Pᶜᶜ → specialUnitary := fun _ => 1
  have hs := (((hcalc.2.2 J).2.2.2.2.2.2.2.2 Pᶜ hPc hne).1) T hT z₀
  let ω : C(↥Pᶜ → specialUnitary, ℂ) := ⟨fun v => T (glue Pᶜ v z₀), continuous_of_mem_smoothSet hs⟩
  have e : pullFromComplement P ω = T := by
    ext u
    refine hind _ _ fun x hx => ?_
    exact glue_of_mem Pᶜ _ _ ⟨x, hx⟩
  have h := hcomm ω F hs hF
  rwa [e] at h
end Hat
section Layer
variable (D : CenteredStackStep μ)
theorem nonempty_links : Nonempty D.block.links := D.block.links_nonempty.to_subtype
instance nonempty_innerPairs : Nonempty D.InnerPairs := by
  have := nonempty_links D
  obtain ⟨b⟩ := this
  exact ⟨D.innerPair D.isInnerLevel_bottom b.1 (D.block.subset_thickened b.2)⟩
def expEnergy (β : ℝ) {j : ℤ} (hj : D.IsInnerLevel j) : C(D.InnerPairs → specialUnitary, ℂ) :=
  ⟨fun u => Complex.exp (-D.sliceEnergyAt β hj u),
    Complex.continuous_exp.comp (D.continuous_sliceEnergyAt β hj).neg⟩
theorem continuous_kernelBetween (β : ℝ) {j k : ℤ} (hj : D.IsInnerLevel j) (hk : D.IsInnerLevel k) :
    Continuous fun u => linkProductKernel β (D.blockRestrict hj u) (D.blockRestrict hk u) := by
  have h := (continuous_linkProductKernel β (B := D.block.links)).comp
    ((D.continuous_blockRestrict hj).prodMk (D.continuous_blockRestrict hk))
  exact h
def kernelBetween (β : ℝ) {j k : ℤ} (hj : D.IsInnerLevel j) (hk : D.IsInnerLevel k) :
    C(D.InnerPairs → specialUnitary, ℂ) :=
  ⟨fun u => linkProductKernel β (D.blockRestrict hj u) (D.blockRestrict hk u),
    continuous_kernelBetween D β hj hk⟩
variable (hker : KernelSymmetryAndGaugeInvariance.Statement)
  (hcalc : FieldCalculus.AllRules)
theorem isRealEntryPolynomial_sliceEnergyAt (hker : KernelSymmetryAndGaugeInvariance.Statement)
    {β : ℝ} (hβ : 0 < β) {j : ℤ} (hj : D.IsInnerLevel j) :
    IsRealEntryPolynomial (D.sliceEnergyAt β hj) := by apply _root_.YangMills.Construction.TransferOperators.CenteredStackReversal.isRealEntryPolynomial_sliceEnergyAt <;> assumption
include hker hcalc
theorem isSmoothPos_expEnergy {β : ℝ} (hβ : 0 < β) {j : ℤ} (hj : D.IsInnerLevel j) :
    IsSmoothPos (expEnergy D β hj) := by
  have hE := isRealEntryPolynomial_sliceEnergyAt D hker hβ hj
  have hEs : D.sliceEnergyAt β hj ∈ smoothSet := (hcalc.2.2 D.InnerPairs).2.2.2.2.2.1.1 _ hE.1
  have hr : ∀ u, (-D.sliceEnergyAt β hj u).im = 0 := fun u => by
    rw [Complex.neg_im, hE.2 u, neg_zero]
  exact ⟨(hcalc.2.2 D.InnerPairs).2.2.2.2.1.1 _ (mem_smoothSet_neg hcalc hEs) hr,
    fun u => exp_im_eq_zero_and_re_pos (hr u)⟩
theorem isSmoothPos_kernelBetween {β : ℝ} (hβ : 0 < β) {j k : ℤ} (hj : D.IsInnerLevel j)
    (hk : D.IsInnerLevel k) (hjk : j ≠ k) : IsSmoothPos (kernelBetween D β hj hk) := by
  have := nonempty_links D
  have hne : ∀ b : D.block.links, D.innerPair hj b.1 (D.block.subset_thickened b.2) ≠
      D.innerPair hk b.1 (D.block.subset_thickened b.2) := fun b h =>
    hjk (congrArg (fun p : D.InnerPairs => p.1.1) h)
  have hw : ∀ b : D.block.links, (fun u : D.InnerPairs → specialUnitary => singleBondWeight β
      (u (D.innerPair hj b.1 (D.block.subset_thickened b.2)) *
        (u (D.innerPair hk b.1 (D.block.subset_thickened b.2)))⁻¹)) ∈ smoothSet :=
    fun b => ((hcalc.2.2 D.InnerPairs).2.2.2.2.2.1.2 β hβ _ _ (hne b)).1
  refine ⟨mem_smoothSet_finprod hcalc _ hw, fun u => ?_⟩
  obtain ⟨-, h₂, h₃, -⟩ := ((hker β hβ).1 D.block.links).1 (D.blockRestrict hj u) (D.blockRestrict hk u)
  exact ⟨h₂, (Real.exp_pos _).trans_le h₃⟩
omit hker hcalc
theorem blockRestrict_congr {j j' : ℤ} (hj : D.IsInnerLevel j) (hj' : D.IsInnerLevel j') (e : j = j')
    (u : D.InnerPairs → specialUnitary) : D.blockRestrict hj u = D.blockRestrict hj' u := by apply _root_.YangMills.Construction.TransferOperators.CenteredStackReversal.blockRestrict_congr <;> assumption
theorem blockRestrict_indep {j m : ℤ} (hj : D.IsInnerLevel j) (hjm : j ≠ m)
    {u u' : D.InnerPairs → specialUnitary}
    (h : ∀ x, x ∉ D.levelPart m → u x = u' x) : D.blockRestrict hj u = D.blockRestrict hj u' := by
  funext b
  exact h _ fun hx => hjm hx.1
theorem collarRestrict_indep {j m : ℤ} (hj : D.IsInnerLevel j) (hjm : j ≠ m)
    {u u' : D.InnerPairs → specialUnitary}
    (h : ∀ x, x ∉ D.levelPart m → u x = u' x) : D.collarRestrict hj u = D.collarRestrict hj u' := by
  funext b
  exact h _ fun hx => hjm hx.1
theorem expEnergy_indep (β : ℝ) {j m : ℤ} (hj : D.IsInnerLevel j) (hjm : j ≠ m)
    {u u' : D.InnerPairs → specialUnitary} (h : ∀ x, x ∉ D.levelPart m → u x = u' x) :
    expEnergy D β hj u = expEnergy D β hj u' := by
  show Complex.exp (-D.sliceEnergyAt β hj u) = Complex.exp (-D.sliceEnergyAt β hj u')
  unfold CenteredStackStep.sliceEnergyAt
  rw [blockRestrict_indep D hj hjm h, collarRestrict_indep D hj hjm h]
theorem kernelBetween_indep (β : ℝ) {j k m : ℤ} (hj : D.IsInnerLevel j) (hk : D.IsInnerLevel k)
    (hjm : j ≠ m) (hkm : k ≠ m) {u u' : D.InnerPairs → specialUnitary}
    (h : ∀ x, x ∉ D.levelPart m → u x = u' x) :
    kernelBetween D β hj hk u = kernelBetween D β hj hk u' := by
  show linkProductKernel β _ _ = linkProductKernel β _ _
  rw [blockRestrict_indep D hj hjm h, blockRestrict_indep D hk hkm h]
end Layer
section Single
variable (D : CenteredStackStep μ) {j k : ℤ} {R : Finset (ℤ × SliceLink μ)}
open Classical in
def splitEmbed (j : ℤ) (hR : ∀ p : D.InnerPairs, p ∉ D.levelPart j → p.1 ∈ R) (p : D.InnerPairs) :
    D.block.links ⊕ R :=
  if hp : p ∈ D.levelPart j then Sum.inl ⟨p.1.2, hp.2⟩ else Sum.inr ⟨p.1, hR p hp⟩
variable (hR : ∀ p : D.InnerPairs, p ∉ D.levelPart j → p.1 ∈ R)
theorem splitEmbed_of_mem {p : D.InnerPairs} (hp : p ∈ D.levelPart j) :
    splitEmbed D j hR p = Sum.inl ⟨p.1.2, hp.2⟩ :=
  dif_pos hp
theorem splitEmbed_of_not_mem {p : D.InnerPairs} (hp : p ∉ D.levelPart j) :
    splitEmbed D j hR p = Sum.inr ⟨p.1, hR p hp⟩ :=
  dif_neg hp
theorem splitEmbed_injective : Function.Injective (splitEmbed D j hR) := by
  intro p q h
  by_cases hp : p ∈ D.levelPart j <;> by_cases hq : q ∈ D.levelPart j
  · rw [splitEmbed_of_mem D hR hp, splitEmbed_of_mem D hR hq] at h
    have hb : p.1.2 = q.1.2 := congrArg Subtype.val (Sum.inl_injective h)
    exact Subtype.ext (Prod.ext (hp.1.trans hq.1.symm) hb)
  · rw [splitEmbed_of_mem D hR hp, splitEmbed_of_not_mem D hR hq] at h
    exact absurd h Sum.inl_ne_inr
  · rw [splitEmbed_of_not_mem D hR hp, splitEmbed_of_mem D hR hq] at h
    exact absurd h.symm Sum.inl_ne_inr
  · rw [splitEmbed_of_not_mem D hR hp, splitEmbed_of_not_mem D hR hq] at h
    have h' : (⟨p.1, hR p hp⟩ : R) = ⟨q.1, hR q hq⟩ := Sum.inr.inj h
    exact Subtype.ext (Subtype.mk.inj h')
theorem splitEmbed_image (hj : D.IsInnerLevel j) :
    splitEmbed D j hR '' D.levelPart j = inlSet D.block.links R := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨⟨p.1.2, hp.2⟩, (splitEmbed_of_mem D hR hp).symm⟩
  · rintro ⟨b, rfl⟩
    exact ⟨D.innerPair hj b.1 (D.block.subset_thickened b.2), ⟨rfl, b.2⟩,
      splitEmbed_of_mem D hR (p := D.innerPair hj b.1 (D.block.subset_thickened b.2)) ⟨rfl, b.2⟩⟩
theorem hatSum_inlSet_precomp (hpass : MulThroughLinkKernelStatement)
    (hfacts : SeveralVariables.SeveralVariablesFacts) {β : ℝ} (hβ : 0 < β)
    (hj : D.IsInnerLevel j) {f : (D.block.links → specialUnitary) → ℂ} (hf : IsRealEntryPolynomial f)
    {G : C(D.InnerPairs → specialUnitary, ℂ)} (hG : (G : (D.InnerPairs → specialUnitary) → ℂ) ∈ smoothSet) :
    hatSum β (inlSet D.block.links R) (restrictInl f) (isRealEntryPolynomial_restrictInl hf)
        (precompAlong (splitEmbed D j hR) G) =
      precompAlong (splitEmbed D j hR)
        (hatSum β (D.levelPart j) (D.pullToLevel hj f) (D.isRealEntryPolynomial_pullToLevel hj hf) G) := by
  have := nonempty_links D
  have hne : (D.levelPart j).Nonempty := ⟨_, (D.levelPartElement hj (Classical.arbitrary _)).2⟩
  obtain ⟨-, ⟨-, -, -, -, -, hinj, -⟩⟩ := hatSum_smooth_and_properties hpass hfacts hβ hne
    (D.isRealEntryPolynomial_pullToLevel hj hf)
  obtain ⟨he, hh⟩ := hinj _ (splitEmbed D j hR) (splitEmbed_injective D hR)
  rw [← hh G hG]
  refine (hatSum_congr β (splitEmbed_image D hR hj) he _ (fun v => ?_) _).symm
  show f _ = f _
  congr 1
  funext a
  exact congrArg v (Subtype.ext
    (splitEmbed_of_mem D hR (p := D.levelPartElement hj a) (D.levelPartElement hj a).2))
variable {hR}
theorem enclosingValues_eq_splitEmbed (U : GaugeField 1) :
    (fun p => D.enclosingStack.blockPairVariables D.block R U j (splitEmbed D j hR p)) =
      D.enclosingValues U := by
  funext p
  by_cases hp : p ∈ D.levelPart j
  · rw [splitEmbed_of_mem D hR hp]
    show D.enclosingStack.transportedLinkVariable μ U j p.1.2 =
      D.enclosingStack.transportedLinkVariable μ U p.1.1 p.1.2
    rw [hp.1]
  · rw [splitEmbed_of_not_mem D hR hp]
    rfl
variable (hR) {k : ℤ}
theorem blockRestrict_splitEmbed (hj : D.IsInnerLevel j) (u : D.block.links ⊕ R → specialUnitary) :
    D.blockRestrict hj (fun p => u (splitEmbed D j hR p)) = fun b => u (Sum.inl b) := by
  funext b
  exact congrArg u (splitEmbed_of_mem D hR (p := D.innerPair hj b.1 (D.block.subset_thickened b.2))
    ⟨rfl, b.2⟩)
theorem collarRestrict_splitEmbed (hj : D.IsInnerLevel j) (hb : D.block.AdjacentPairs j k R)
    (u : D.block.links ⊕ R → specialUnitary) :
    D.collarRestrict hj (fun p => u (splitEmbed D j hR p)) = hb.collarPart fun p => u (Sum.inr p) := by
  funext b
  have hn : D.innerPair hj b.1 b.2.1 ∉ D.levelPart j := fun h => b.2.2 (Finset.mem_coe.2 h.2)
  exact congrArg u (splitEmbed_of_not_mem D hR hn)
theorem blockRestrict_splitEmbed_adjacent (hk : D.IsInnerLevel k) (hjk : j ≠ k)
    (hb : D.block.AdjacentPairs j k R) (u : D.block.links ⊕ R → specialUnitary) :
    D.blockRestrict hk (fun p => u (splitEmbed D j hR p)) = hb.adjacentPart fun p => u (Sum.inr p) := by
  funext b
  have hn : D.innerPair hk b.1 (D.block.subset_thickened b.2) ∉ D.levelPart j := fun h => hjk h.1.symm
  exact congrArg u (splitEmbed_of_not_mem D hR hn)
variable {β : ℝ} (hj : D.IsInnerLevel j) (hk : D.IsInnerLevel k) (hjk : j ≠ k)
  (hb : D.block.AdjacentPairs j k R)
include hjk
theorem weighted_precomp (Ω G : C(D.block.links ⊕ R → specialUnitary, ℂ))
    (H : C(D.InnerPairs → specialUnitary, ℂ))
    (hG : G = precompAlong (splitEmbed D j hR) H) (u : D.block.links ⊕ R → specialUnitary) :
    hb.weighted β (⇑(Ω * G)) u =
      (Ω * precompAlong (splitEmbed D j hR) (expEnergy D β hj * kernelBetween D β hj hk * H)) u := by
  subst hG
  have e₁ : expEnergy D β hj (fun p => u (splitEmbed D j hR p)) =
      Complex.exp (-D.block.sliceEnergy β (fun b => u (Sum.inl b))
        (hb.collarPart fun p => u (Sum.inr p))) := by
    show Complex.exp (-D.block.sliceEnergy β _ _) = _
    rw [blockRestrict_splitEmbed D hR hj, collarRestrict_splitEmbed D hR hj hb]
  have e₂ : kernelBetween D β hj hk (fun p => u (splitEmbed D j hR p)) =
      linkProductKernel β (fun b => u (Sum.inl b)) (hb.adjacentPart fun p => u (Sum.inr p)) := by
    show linkProductKernel β _ _ = _
    rw [blockRestrict_splitEmbed D hR hj, blockRestrict_splitEmbed_adjacent D hR hk hjk hb]
  show Complex.exp _ * linkProductKernel β _ _ * (Ω u * H fun p => u (splitEmbed D j hR p)) =
    Ω u * (expEnergy D β hj (fun p => u (splitEmbed D j hR p)) *
      kernelBetween D β hj hk (fun p => u (splitEmbed D j hR p)) * H fun p => u (splitEmbed D j hR p))
  rw [e₁, e₂]
  ring
theorem flattened_precomp (hW : IsSmoothPos (expEnergy D β hj * kernelBetween D β hj hk))
    (Ω : C(D.block.links ⊕ R → specialUnitary, ℂ)) (X : C(D.InnerPairs → specialUnitary, ℂ))
    (u : D.block.links ⊕ R → specialUnitary) :
    hb.flattened β (⇑(Ω * precompAlong (splitEmbed D j hR) X)) u =
      Ω u * (recipMap _ hW * X) fun p => u (splitEmbed D j hR p) := by
  have e₁ : expEnergy D β hj (fun p => u (splitEmbed D j hR p)) =
      Complex.exp (-D.block.sliceEnergy β (fun b => u (Sum.inl b))
        (hb.collarPart fun p => u (Sum.inr p))) := by
    show Complex.exp (-D.block.sliceEnergy β _ _) = _
    rw [blockRestrict_splitEmbed D hR hj, collarRestrict_splitEmbed D hR hj hb]
  have e₂ : kernelBetween D β hj hk (fun p => u (splitEmbed D j hR p)) =
      linkProductKernel β (fun b => u (Sum.inl b)) (hb.adjacentPart fun p => u (Sum.inr p)) := by
    show linkProductKernel β _ _ = _
    rw [blockRestrict_splitEmbed D hR hj, blockRestrict_splitEmbed_adjacent D hR hk hjk hb]
  show Complex.exp _ / linkProductKernel β _ _ * (Ω u * X fun p => u (splitEmbed D j hR p)) =
    Ω u * ((expEnergy D β hj (fun p => u (splitEmbed D j hR p)) *
      kernelBetween D β hj hk (fun p => u (splitEmbed D j hR p)))⁻¹ * X fun p => u (splitEmbed D j hR p))
  rw [e₁, e₂, Complex.exp_neg, mul_inv, inv_inv, div_eq_mul_inv]
  ring
omit hjk
include hR
theorem integral_eliminate_one (hpass : MulThroughLinkKernelStatement)
    (hfacts : SeveralVariables.SeveralVariablesFacts) (hcalc : FieldCalculus.AllRules)
    (hβ : 0 < β) (hjk : j ≠ k) {ν : Measure (GaugeField 1)}
    {f : (D.block.links → specialUnitary) → ℂ} (hf : IsRealEntryPolynomial f) (k' lo hi : ℤ)
    (hel : ∀ φ ∈ smoothSet, (∀ u, (φ u).im = 0) →
      OuterSliceElimination β ν D.enclosingStack hf hb k' lo hi φ)
    (hW : IsSmoothPos (expEnergy D β hj * kernelBetween D β hj hk))
    {Ω : C(D.block.links ⊕ R → specialUnitary, ℂ)} (hΩ : IsSmoothReal Ω)
    (hΩi : ∀ u u' : D.block.links ⊕ R → specialUnitary,
      (∀ x, x ∉ inlSet D.block.links R → u x = u' x) → Ω u = Ω u')
    {G : C(D.InnerPairs → specialUnitary, ℂ)} (hG : IsSmoothReal G) :
    ∫ U, f (D.enclosingStack.blockValues D.block U k') *
        (Ω (D.enclosingStack.blockPairVariables D.block R U j) * G (D.enclosingValues U)) ∂ν =
      ∫ U, Ω (D.enclosingStack.blockPairVariables D.block R U j) *
        (recipMap _ hW * hatSum β (D.levelPart j) (D.pullToLevel hj f)
          (D.isRealEntryPolynomial_pullToLevel hj hf)
          (expEnergy D β hj * kernelBetween D β hj hk * G)) (D.enclosingValues U) ∂ν := by
  have hbn := nonempty_links D
  have : Nonempty (D.block.links ⊕ R) := ⟨Sum.inl (Classical.arbitrary _)⟩
  have hread : ∀ {H : C(D.InnerPairs → specialUnitary, ℂ)}, IsSmoothReal H →
      IsSmoothReal (precompAlong (splitEmbed D j hR) H) := fun {H} hH =>
    ⟨precomp_mem_smoothSet (splitEmbed_injective D hR) hH.1, fun u => hH.2 _⟩
  have hφ := IsSmoothReal.mul hcalc hΩ (hread hG)
  obtain ⟨-, hc, hd, hrest⟩ := hel _ hφ.1 hφ.2
  obtain ⟨-, -, -, hint⟩ := hrest
  have hψ : (⟨hb.weighted β (⇑(Ω * precompAlong (splitEmbed D j hR) G)), hc⟩ :
      C(D.block.links ⊕ R → specialUnitary, ℂ)) =
      Ω * precompAlong (splitEmbed D j hR) (expEnergy D β hj * kernelBetween D β hj hk * G) := by
    ext u
    exact weighted_precomp D hR hj hk hjk hb Ω _ G rfl u
  have hWG := IsSmoothReal.mul hcalc hW.isSmoothReal hG
  have hleft : (inlSet D.block.links R).Nonempty := ⟨Sum.inl (Classical.arbitrary _), _, rfl⟩
  have hleftc : (inlSet D.block.links R)ᶜ.Nonempty := by
    let b : D.block.links := Classical.arbitrary _
    refine ⟨Sum.inr ⟨(k, b.1), hb.adjacent_mem b.1 b.2⟩, ?_⟩
    rintro ⟨a, ha⟩
    exact Sum.inl_ne_inr ha
  have hop : hatSum β (inlSet D.block.links R) (restrictInl f) (isRealEntryPolynomial_restrictInl hf)
      ⟨hb.weighted β (⇑(Ω * precompAlong (splitEmbed D j hR) G)), hc⟩ =
      Ω * precompAlong (splitEmbed D j hR) (hatSum β (D.levelPart j) (D.pullToLevel hj f)
        (D.isRealEntryPolynomial_pullToLevel hj hf) (expEnergy D β hj * kernelBetween D β hj hk * G)) := by
    rw [hψ, hatSum_mul_of_indep hpass hfacts hcalc hβ hleft hleftc _ hΩ.1 hΩi (hread hWG).1,
      hatSum_inlSet_precomp D hR hpass hfacts hβ hj hf hWG.1]
  refine (integral_congr_ae (ae_of_all _ fun U => ?_)).trans
    (hint.trans (integral_congr_ae (ae_of_all _ fun U => ?_)))
  · show _ * (_ * _) = _ * (_ * G fun p =>
      D.enclosingStack.blockPairVariables D.block R U j (splitEmbed D j hR p))
    rw [enclosingValues_eq_splitEmbed D U]
  · have hop' : hatMap β (inlSet D.block.links R) (restrictInl f)
        (isRealEntryPolynomial_restrictInl hf) ⟨⟨_, hc⟩, hd⟩ = _ := hop
    rw [hop']
    beta_reduce
    rw [flattened_precomp D hR hj hk hjk hb hW, enclosingValues_eq_splitEmbed D U]
end Single
theorem conj_hat_assembly {Q : Type*} [CommRing Q] (Hm Hp : Q → Q) {A Ai B Wm Wmi Wp Wpi Y Yi Φ : Q}
    (hA : A * Ai = 1) (hWm : Wm * Wmi = 1) (hWp : Wp * Wpi = 1) (hY : Y * Yi = 1)
    (hYA : Y = A * Wp) (hYB : Y = B * Wm)
    (hB : Hm (B * (Wm * Φ)) = B * Hm (Wm * Φ))
    (hAi : Hp (Ai * Hm (Y * Φ)) = Ai * Hp (Hm (Y * Φ)))
    (hcomm : Hp (Hm (Y * Φ)) = Hm (Hp (Y * Φ))) :
    Wpi * Hp (Wp * (Wmi * Hm (Wm * Φ))) = Yi * Hm (Hp (Y * Φ)) := by
  have h0 : A * Wp = B * Wm := hYA.symm.trans hYB
  have h1 : Wp * Wmi = Ai * B := by
    linear_combination (-(Wp * Wmi)) * hA + (Ai * Wmi) * h0 + (Ai * B) * hWm
  have h2 : Wp * (Wmi * Hm (Wm * Φ)) = Ai * Hm (Y * Φ) := by
    rw [← mul_assoc, h1, mul_assoc, ← hB, ← mul_assoc B, ← hYB]
  have h4 : Y * (Wpi * Ai) = 1 := by
    rw [hYA]
    linear_combination (A * Ai) * hWp + hA
  have h3 : Yi = Wpi * Ai := by
    linear_combination (-Yi) * h4 + (Wpi * Ai) * hY
  rw [h2, hAi, hcomm, ← mul_assoc, ← h3]
section Factors
variable (D : CenteredStackStep μ)
abbrev lowerSliceWeight (β : ℝ) : C(D.InnerPairs → specialUnitary, ℂ) :=
  expEnergy D β D.isInnerLevel_bottom * kernelBetween D β D.isInnerLevel_bottom D.isInnerLevel_bottom_add_one
abbrev upperSliceWeight (β : ℝ) : C(D.InnerPairs → specialUnitary, ℂ) :=
  expEnergy D β D.isInnerLevel_top * kernelBetween D β D.isInnerLevel_top D.isInnerLevel_top_sub_one
theorem bottom_ne_top : D.bottom ≠ D.top := by
  have := D.one_le_halfWidth
  have e₁ : D.bottom = D.center - D.halfWidth + 1 := rfl
  have e₂ : D.top = D.center + D.halfWidth := rfl
  omega
theorem boundaryWeight_of_eq_one (β : ℝ) (hk : D.halfWidth = 1) (u : D.InnerPairs → specialUnitary) :
    D.boundaryWeight β u = expEnergy D β D.isInnerLevel_bottom u * expEnergy D β D.isInnerLevel_top u *
      kernelBetween D β D.isInnerLevel_bottom D.isInnerLevel_bottom_add_one u := by
  unfold CenteredStackStep.boundaryWeight
  rw [if_pos hk, mul_one, sub_eq_add_neg, Complex.exp_add]
  rfl
theorem boundaryWeight_of_ne_one (β : ℝ) (hk : D.halfWidth ≠ 1) (u : D.InnerPairs → specialUnitary) :
    D.boundaryWeight β u = expEnergy D β D.isInnerLevel_bottom u * expEnergy D β D.isInnerLevel_top u *
      kernelBetween D β D.isInnerLevel_bottom D.isInnerLevel_bottom_add_one u *
      kernelBetween D β D.isInnerLevel_top D.isInnerLevel_top_sub_one u := by
  unfold CenteredStackStep.boundaryWeight
  rw [if_neg hk, sub_eq_add_neg, Complex.exp_add]
  rfl
theorem exists_boundaryWeight_factors (hker : KernelSymmetryAndGaugeInvariance.Statement)
    (hcalc : FieldCalculus.AllRules) {β : ℝ} (hβ : 0 < β) :
    ∃ A B : C(D.InnerPairs → specialUnitary, ℂ), IsSmoothPos A ∧ IsSmoothPos B ∧
      (∀ u u' : D.InnerPairs → specialUnitary, (∀ x, x ∉ D.levelPart D.top → u x = u' x) → A u = A u') ∧
      (∀ u u' : D.InnerPairs → specialUnitary, (∀ x, x ∉ D.levelPart D.bottom → u x = u' x) → B u = B u') ∧
      D.boundaryWeightMap β = A * upperSliceWeight D β ∧ D.boundaryWeightMap β = B * lowerSliceWeight D β := by
  have e₁ : D.bottom = D.center - D.halfWidth + 1 := rfl
  have e₂ : D.top = D.center + D.halfWidth := rfl
  have hlh := bottom_ne_top D
  have hE₁ := isSmoothPos_expEnergy D hker hcalc hβ D.isInnerLevel_bottom
  have hE₂ := isSmoothPos_expEnergy D hker hcalc hβ D.isInnerLevel_top
  by_cases hk : D.halfWidth = 1
  · have := nonempty_links D
    have hc : ∀ u, kernelBetween D β D.isInnerLevel_top D.isInnerLevel_top_sub_one u =
        kernelBetween D β D.isInnerLevel_bottom D.isInnerLevel_bottom_add_one u := by
      intro u
      show linkProductKernel β _ _ = linkProductKernel β _ _
      rw [blockRestrict_congr D D.isInnerLevel_top D.isInnerLevel_bottom_add_one (by omega) u,
        blockRestrict_congr D D.isInnerLevel_top_sub_one D.isInnerLevel_bottom (by omega) u]
      exact (((hker β hβ).1 D.block.links).1 _ _).1
    refine ⟨expEnergy D β D.isInnerLevel_bottom, expEnergy D β D.isInnerLevel_top, hE₁, hE₂,
      fun u u' h => expEnergy_indep D β _ hlh h,
      fun u u' h => expEnergy_indep D β _ hlh.symm h, ?_, ?_⟩
    · ext u
      show D.boundaryWeight β u = expEnergy D β D.isInnerLevel_bottom u * (expEnergy D β D.isInnerLevel_top u *
        kernelBetween D β D.isInnerLevel_top D.isInnerLevel_top_sub_one u)
      rw [boundaryWeight_of_eq_one D β hk, hc, mul_assoc]
    · ext u
      show D.boundaryWeight β u = expEnergy D β D.isInnerLevel_top u * (expEnergy D β D.isInnerLevel_bottom u *
        kernelBetween D β D.isInnerLevel_bottom D.isInnerLevel_bottom_add_one u)
      rw [boundaryWeight_of_eq_one D β hk]
      ring
  · refine ⟨lowerSliceWeight D β, upperSliceWeight D β,
      hE₁.mul hcalc (isSmoothPos_kernelBetween D hker hcalc hβ _ _ (by omega)),
      hE₂.mul hcalc (isSmoothPos_kernelBetween D hker hcalc hβ _ _ (by omega)),
      fun u u' h => ?_, fun u u' h => ?_, ?_, ?_⟩
    · show expEnergy D β _ u * kernelBetween D β _ _ u = expEnergy D β _ u' * kernelBetween D β _ _ u'
      rw [expEnergy_indep D β _ hlh h, kernelBetween_indep D β _ _ hlh (by omega) h]
    · show expEnergy D β _ u * kernelBetween D β _ _ u = expEnergy D β _ u' * kernelBetween D β _ _ u'
      rw [expEnergy_indep D β _ hlh.symm h,
        kernelBetween_indep D β _ _ hlh.symm (by omega) h]
    · ext u
      show D.boundaryWeight β u = expEnergy D β D.isInnerLevel_bottom u *
        kernelBetween D β D.isInnerLevel_bottom D.isInnerLevel_bottom_add_one u *
        (expEnergy D β D.isInnerLevel_top u *
          kernelBetween D β D.isInnerLevel_top D.isInnerLevel_top_sub_one u)
      rw [boundaryWeight_of_ne_one D β hk]
      ring
    · ext u
      show D.boundaryWeight β u = expEnergy D β D.isInnerLevel_top u *
        kernelBetween D β D.isInnerLevel_top D.isInnerLevel_top_sub_one u *
        (expEnergy D β D.isInnerLevel_bottom u *
          kernelBetween D β D.isInnerLevel_bottom D.isInnerLevel_bottom_add_one u)
      rw [boundaryWeight_of_ne_one D β hk]
      ring
end Factors
section Sets
variable (D : CenteredStackStep μ)
def complementPairs (j : ℤ) : Finset (ℤ × SliceLink μ) :=
  ((Set.toFinite (D.levelPart j)ᶜ).image Subtype.val).toFinset
theorem mem_complementPairs {j : ℤ} {q : ℤ × SliceLink μ} :
    q ∈ complementPairs D j ↔ ∃ p : D.InnerPairs, p ∉ D.levelPart j ∧ p.1 = q := by
  simp only [complementPairs, Set.Finite.mem_toFinset]
  exact Iff.rfl
theorem mem_complementPairs_of_not_mem {j : ℤ} {p : D.InnerPairs} (hp : p ∉ D.levelPart j) :
    p.1 ∈ complementPairs D j :=
  (mem_complementPairs D).2 ⟨p, hp, rfl⟩
open Classical in
def bottomRest : Finset (ℤ × SliceLink μ) :=
  complementPairs D D.bottom ∪ D.block.links.image fun b => (D.center + D.halfWidth + 1, b)
theorem above_mem_bottomRest (b : D.block.links) :
    (D.center + D.halfWidth + 1, b.1) ∈ bottomRest D := by
  classical
  exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ b.2)
theorem mem_bottomRest_of_not_mem {p : D.InnerPairs} (hp : p ∉ D.levelPart D.bottom) :
    p.1 ∈ bottomRest D := by
  classical
  exact Finset.mem_union_left _ (mem_complementPairs_of_not_mem D hp)
theorem adjacentPairs_of {j k : ℤ} (hj : D.IsInnerLevel j) (hk : D.IsInnerLevel k) (hjk : j ≠ k)
    {R : Finset (ℤ × SliceLink μ)} (hR : ∀ p : D.InnerPairs, p ∉ D.levelPart j → p.1 ∈ R)
    (hn : ∀ p ∈ R, ¬(p.1 = j ∧ p.2 ∈ D.block.links)) : D.block.AdjacentPairs j k R where
  avoids_block := hn
  collar_mem b hb := hR (D.innerPair hj b hb.1) fun h => hb.2 (Finset.mem_coe.2 h.2)
  adjacent_mem b hb := hR (D.innerPair hk b (D.block.subset_thickened hb)) fun h => hjk h.1.symm
end Sets
section Both
variable (hElim : OutermostSliceElimination.Statement)
  (hpass : MulThroughLinkKernelStatement)
  (hfacts : SeveralVariables.SeveralVariablesFacts)
  (hker : KernelSymmetryAndGaugeInvariance.Statement)
  (hcalc : FieldCalculus.AllRules)
include hElim hpass hfacts hker hcalc
theorem integral_two_eliminations {β : ℝ} (hβ : 0 < β) {ν : Measure (GaugeField 1)}
    (hν : ν ∈ gibbsClass (zero_lt_one (α := ℝ)) β) (D : CenteredStackStep μ)
    {f h : (D.block.links → specialUnitary) → ℂ} (hf : IsRealEntryPolynomial f) (hh : IsRealEntryPolynomial h)
    (Φ : C(D.InnerPairs → specialUnitary, ℂ)) (hΦ : IsRealEntryPolynomial (Φ : (D.InnerPairs → specialUnitary) → ℂ)) :
    D.transferStepFunction β hf hh Φ ∈ smoothSet ∧ (∀ u, (D.transferStepFunction β hf hh Φ u).im = 0) ∧
      ∫ U, f (D.enclosingStack.blockValues D.block U (D.center - D.halfWidth)) *
          h (D.enclosingStack.blockValues D.block U (D.center + D.halfWidth + 1)) *
          Φ (D.enclosingValues U) ∂ν =
        ∫ U, D.transferStepFunction β hf hh Φ (D.enclosingValues U) ∂ν := by
  have hbn := nonempty_links D
  have hone := D.one_le_halfWidth
  have e₁ : D.bottom = D.center - D.halfWidth + 1 := rfl
  have e₂ : D.top = D.center + D.halfWidth := rfl
  have eb : D.enclosingStack.lower = D.center - (D.halfWidth + 1) + 1 := rfl
  have et : D.enclosingStack.upper = D.center + (D.halfWidth + 1) := rfl
  have hlh := bottom_ne_top D
  let b₀ : D.block.links := Classical.arbitrary _
  have hPl : (D.levelPart D.bottom).Nonempty := ⟨_, (D.levelPartElement D.isInnerLevel_bottom b₀).2⟩
  have hPh : (D.levelPart D.top).Nonempty := ⟨_, (D.levelPartElement D.isInnerLevel_top b₀).2⟩
  have hPlc : (D.levelPart D.bottom)ᶜ.Nonempty :=
    ⟨(D.levelPartElement D.isInnerLevel_top b₀).1, fun hx =>
      hlh (hx.1.symm.trans (D.levelPartElement D.isInnerLevel_top b₀).2.1)⟩
  have hPhc : (D.levelPart D.top)ᶜ.Nonempty :=
    ⟨(D.levelPartElement D.isInnerLevel_bottom b₀).1, fun hx =>
      hlh ((D.levelPartElement D.isInnerLevel_bottom b₀).2.1.symm.trans hx.1)⟩
  have hdisj : Disjoint (D.levelPart D.top) (D.levelPart D.bottom) :=
    Set.disjoint_left.2 fun _ h₁ h₂ => hlh (h₂.1.symm.trans h₁.1)
  have hpl := D.isRealEntryPolynomial_pullToLevel D.isInnerLevel_bottom hf
  have hph := D.isRealEntryPolynomial_pullToLevel D.isInnerLevel_top hh
  have hWm : IsSmoothPos (lowerSliceWeight D β) :=
    (isSmoothPos_expEnergy D hker hcalc hβ _).mul hcalc
      (isSmoothPos_kernelBetween D hker hcalc hβ _ _ (by omega))
  have hWp : IsSmoothPos (upperSliceWeight D β) :=
    (isSmoothPos_expEnergy D hker hcalc hβ _).mul hcalc
      (isSmoothPos_kernelBetween D hker hcalc hβ _ _ (by omega))
  obtain ⟨A, B, hA, hB, hAi, hBi, hYA, hYB⟩ := exists_boundaryWeight_factors D hker hcalc hβ
  have hY : IsSmoothPos (D.boundaryWeightMap β) := by
    rw [hYA]
    exact hA.mul hcalc hWp
  have hΦs : IsSmoothReal Φ := ⟨(hcalc.2.2 D.InnerPairs).2.2.2.2.2.1.1 _ hΦ.1, hΦ.2⟩
  have hHl : ∀ {G : C(D.InnerPairs → specialUnitary, ℂ)}, IsSmoothReal G →
      IsSmoothReal (hatSum β (D.levelPart D.bottom) (D.pullToLevel D.isInnerLevel_bottom f) hpl G) :=
    fun hG => hatSum_isSmoothReal hpass hfacts hβ hPl hpl hG
  have hHh : ∀ {G : C(D.InnerPairs → specialUnitary, ℂ)}, IsSmoothReal G →
      IsSmoothReal (hatSum β (D.levelPart D.top) (D.pullToLevel D.isInnerLevel_top h) hph G) :=
    fun hG => hatSum_isSmoothReal hpass hfacts hβ hPh hph hG
  have hYΦ := IsSmoothReal.mul hcalc hY.isSmoothReal hΦs
  have hWΦ := IsSmoothReal.mul hcalc hWm.isSmoothReal hΦs
  have hφ₁ := IsSmoothReal.mul hcalc (hWm.recipMap hcalc) (hHl hWΦ)
  have hass := conj_hat_assembly
    (hatSum β (D.levelPart D.bottom) (D.pullToLevel D.isInnerLevel_bottom f) hpl)
    (hatSum β (D.levelPart D.top) (D.pullToLevel D.isInnerLevel_top h) hph)
    (mul_recipMap hA) (mul_recipMap hWm) (mul_recipMap hWp) (mul_recipMap hY) hYA hYB
    (hatSum_mul_of_indep hpass hfacts hcalc hβ hPl hPlc hpl hB.1 hBi hWΦ.1)
    (hatSum_mul_of_indep hpass hfacts hcalc hβ hPh hPhc hph (hA.recipMap hcalc).1
      (fun u u' hu => by
        show (A u)⁻¹ = (A u')⁻¹
        rw [hAi u u' hu]) (hHl hYΦ).1)
    (by
      obtain ⟨-, ⟨-, -, -, hcomm, -⟩⟩ := hatSum_smooth_and_properties hpass hfacts hβ hPl hpl
      exact (hcomm _ _ hph _ hPh hdisj hYΦ.1).symm)
  have hstep : D.transferStepFunction β hf hh Φ = ⇑(recipMap (D.boundaryWeightMap β) hY *
      hatSum β (D.levelPart D.bottom) (D.pullToLevel D.isInnerLevel_bottom f) hpl
        (hatSum β (D.levelPart D.top) (D.pullToLevel D.isInnerLevel_top h) hph
          (D.boundaryWeightMap β * Φ))) := by
    funext u
    rfl
  have hres := IsSmoothReal.mul hcalc (hY.recipMap hcalc) (hHl (hHh hYΦ))
  refine ⟨by rw [hstep]; exact hres.1, fun u => by rw [hstep]; exact hres.2 u, ?_⟩
  have hin₁ : D.enclosingStack.IsInteriorLevel D.bottom := ⟨by omega, by omega⟩
  have hin₂ : D.enclosingStack.IsInteriorLevel D.top := ⟨by omega, by omega⟩
  have hnb₁ : ∀ p ∈ bottomRest D, ¬(p.1 = D.bottom ∧ p.2 ∈ D.block.links) := by
    classical
    intro p hp hx
    rcases Finset.mem_union.1 hp with hp | hp
    · obtain ⟨q, hq, rfl⟩ := (mem_complementPairs D).1 hp
      exact hq hx
    · obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hp
      have : D.center + D.halfWidth + 1 = D.bottom := hx.1
      omega
  have hlay₁ : ∀ p ∈ bottomRest D, D.bottom ≤ p.1 ∧ p.1 ≤ D.enclosingStack.upper := by
    classical
    intro p hp
    rcases Finset.mem_union.1 hp with hp | hp
    · obtain ⟨q, -, rfl⟩ := (mem_complementPairs D).1 hp
      have h₁ := q.2.1
      have h₂ := q.2.2.1
      omega
    · obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hp
      show D.bottom ≤ D.center + D.halfWidth + 1 ∧ D.center + D.halfWidth + 1 ≤ D.enclosingStack.upper
      omega
  have hR₁ : ∀ p : D.InnerPairs, p ∉ D.levelPart D.bottom → p.1 ∈ bottomRest D :=
    fun p hp => mem_bottomRest_of_not_mem D hp
  have hb₁ : D.block.AdjacentPairs D.bottom (D.bottom + 1) (bottomRest D) :=
    adjacentPairs_of D D.isInnerLevel_bottom D.isInnerLevel_bottom_add_one (by omega) hR₁ hnb₁
  have hel₁ := (hElim μ β hβ ν hν D.enclosingStack D.bottom hin₁ D.block f hf).1 (bottomRest D) hb₁ hlay₁
  let ι : D.block.links → D.block.links ⊕ bottomRest D :=
    fun b => Sum.inr ⟨(D.center + D.halfWidth + 1, b.1), above_mem_bottomRest D b⟩
  have hι : Function.Injective ι := by
    intro b c hbc
    have h' : ((⟨(D.center + D.halfWidth + 1, b.1), above_mem_bottomRest D b⟩ : bottomRest D) =
      ⟨(D.center + D.halfWidth + 1, c.1), above_mem_bottomRest D c⟩) := Sum.inr.inj hbc
    exact Subtype.ext (congrArg Prod.snd (Subtype.mk.inj h'))
  let Ω : C(D.block.links ⊕ bottomRest D → specialUnitary, ℂ) := precompAlong ι ⟨h, hh.1.continuous⟩
  have hΩ : IsSmoothReal Ω :=
    ⟨precomp_mem_smoothSet hι ((hcalc.2.2 D.block.links).2.2.2.2.2.1.1 _ hh.1),
      fun u => hh.2 _⟩
  have hΩi : ∀ u u' : D.block.links ⊕ bottomRest D → specialUnitary,
      (∀ x, x ∉ inlSet D.block.links (bottomRest D) → u x = u' x) → Ω u = Ω u' := by
    intro u u' hu
    show h _ = h _
    congr 1
    funext b
    refine hu _ ?_
    rintro ⟨a, ha⟩
    exact Sum.inl_ne_inr ha
  have s₁ := integral_eliminate_one D hR₁ D.isInnerLevel_bottom D.isInnerLevel_bottom_add_one hb₁
    hpass hfacts hcalc hβ (by omega) hf _ _ _ hel₁ hWm hΩ hΩi hΦs
  have hnb₂ : ∀ p ∈ complementPairs D D.top, ¬(p.1 = D.top ∧ p.2 ∈ D.block.links) := by
    intro p hp hx
    obtain ⟨q, hq, rfl⟩ := (mem_complementPairs D).1 hp
    exact hq hx
  have hlay₂ : ∀ p ∈ complementPairs D D.top, D.enclosingStack.lower ≤ p.1 ∧ p.1 ≤ D.top := by
    intro p hp
    obtain ⟨q, -, rfl⟩ := (mem_complementPairs D).1 hp
    have h₁ := q.2.1
    have h₂ := q.2.2.1
    omega
  have hR₂ : ∀ p : D.InnerPairs, p ∉ D.levelPart D.top → p.1 ∈ complementPairs D D.top :=
    fun p hp => mem_complementPairs_of_not_mem D hp
  have hb₂ : D.block.AdjacentPairs D.top (D.top - 1) (complementPairs D D.top) :=
    adjacentPairs_of D D.isInnerLevel_top D.isInnerLevel_top_sub_one (by omega) hR₂ hnb₂
  have hel₂ := (hElim μ β hβ ν hν D.enclosingStack D.top hin₂ D.block h hh).2
    (complementPairs D D.top) hb₂ hlay₂
  have hOne : IsSmoothReal (1 : C(D.block.links ⊕ complementPairs D D.top → specialUnitary, ℂ)) :=
    ⟨const_mem_smoothSet 1, fun u => by simp⟩
  have s₂ := integral_eliminate_one D hR₂ D.isInnerLevel_top D.isInnerLevel_top_sub_one hb₂
    hpass hfacts hcalc hβ (by omega) hh _ _ _ hel₂ hWp hOne (fun _ _ _ => rfl) hφ₁
  have e₀ : D.bottom - 1 = D.center - D.halfWidth := by omega
  rw [e₀] at s₁
  refine (integral_congr_ae (ae_of_all _ fun U => ?_)).trans (s₁.trans
    ((integral_congr_ae (ae_of_all _ fun U => ?_)).trans (s₂.trans
      (integral_congr_ae (ae_of_all _ fun U => ?_)))))
  · rw [mul_assoc]
    rfl
  · show h _ * _ = _ * (1 * _)
    rw [one_mul]
    rfl
  · rw [hstep, ← hass]
    show 1 * _ = _
    rw [one_mul]
end Both
theorem outerElimination_holds (hElim : OutermostSliceElimination.Statement)
    (hpass : MulThroughLinkKernelStatement)
    (hfacts : SeveralVariables.SeveralVariablesFacts)
    (hker : KernelSymmetryAndGaugeInvariance.Statement)
    (hcalc : FieldCalculus.AllRules) : CenteredStack.OuterEliminationStatement := by
  intro μ β hβ ν hν D f h hf hh Φ hΦ
  exact integral_two_eliminations hElim hpass hfacts hker hcalc hβ hν D hf hh Φ hΦ
end TransferOperators.CenteredStackElimination
end YangMills.Construction
end
