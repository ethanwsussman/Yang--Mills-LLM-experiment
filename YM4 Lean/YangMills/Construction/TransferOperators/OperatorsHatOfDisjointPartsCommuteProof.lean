import YangMills.Construction.Matrices.EveryPolynomialOnPowersOfGHasFiniteDegrees
import YangMills.Construction.Matrices.TensorOperatorsOfDisjointPartsCommuteProof
import YangMills.Construction.TransferOperators.ComponentFunctionsOfTheProjections
import YangMills.Construction.TransferOperators.ComponentsOfAProductWithAPolynomial
import YangMills.Construction.TransferOperators.OperatorsHatOfDisjointPartsCommute
import YangMills.Construction.TransferOperators.SeriesOfTheOperatorHatConverges
import YangMills.Construction.TransferOperators.SmoothFunctionsDecayRapidly
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter YangMills.Construction.Matrices.ComplexMatrix2
noncomputable section
namespace YangMills.Construction.SpinHarmonics
namespace HatDisjointCommute
variable {J : Type} [Finite J]
theorem memLp_two_continuousMap (X : C(J → specialUnitary, ℂ)) :
    MemLp (X : (J → specialUnitary) → ℂ) 2 (haarPi J) := by apply _root_.YangMills.Construction.SpinHarmonics.DisjointParts.memLp_two_continuous <;> assumption
def continuousToHaarL2 : C(J → specialUnitary, ℂ) →ₗ[ℂ] HaarL2 J where
  toFun X := toHaarL2 (X : (J → specialUnitary) → ℂ)
  map_add' X Y := by
    have hX := memLp_two_continuousMap X
    have hY := memLp_two_continuousMap Y
    have hXY := memLp_two_continuousMap (X + Y)
    simp only [toHaarL2, dif_pos hX, dif_pos hY, dif_pos hXY]
    rw [← MemLp.toLp_add]
    rfl
  map_smul' a X := by
    have hX := memLp_two_continuousMap X
    have haX := memLp_two_continuousMap (a • X)
    simp only [toHaarL2, dif_pos hX, dif_pos haX, RingHom.id_apply]
    rw [← MemLp.toLp_const_smul]
    rfl
def isotypicPartSumLinear (l : J → HalfNatural) : HaarL2 J →ₗ[ℂ] C(J → specialUnitary, ℂ) where
  toFun := isotypicPartSum l
  map_add' X Y := by
    simp only [isotypicPartSum, inner_add_right, add_smul, Finset.sum_add_distrib]
  map_smul' a X := by
    simp only [isotypicPartSum, inner_smul_right, mul_smul, Finset.smul_sum, RingHom.id_apply]
def isotypicComponent (l : J → HalfNatural) :
    C(J → specialUnitary, ℂ) →ₗ[ℂ] C(J → specialUnitary, ℂ) :=
  (isotypicPartSumLinear l).comp continuousToHaarL2
def mulPullbackLinear (B : Set J) (f : (↥B → specialUnitary) → ℂ) (hf : IsRealEntryPolynomial f) :
    C(J → specialUnitary, ℂ) →ₗ[ℂ] C(J → specialUnitary, ℂ) where
  toFun := mulPullback B f hf
  map_add' X Y := by simp only [mulPullback, mul_add]
  map_smul' a X := by simp only [mulPullback, mul_smul_comm, RingHom.id_apply]
omit [Finite J] in
theorem mulPullbackLinear_apply (B : Set J) (f : (↥B → specialUnitary) → ℂ)
    (hf : IsRealEntryPolynomial f) (X : C(J → specialUnitary, ℂ)) :
    mulPullbackLinear B f hf X = mulPullback B f hf X := rfl
omit [Finite J] in
theorem mulPullbackLinear_comm (B B' : Set J) (f : (↥B → specialUnitary) → ℂ)
    (hf : IsRealEntryPolynomial f) (f' : (↥B' → specialUnitary) → ℂ)
    (hf' : IsRealEntryPolynomial f') (X : C(J → specialUnitary, ℂ)) :
    mulPullbackLinear B f hf (mulPullbackLinear B' f' hf' X) =
      mulPullbackLinear B' f' hf' (mulPullbackLinear B f hf X) := by
  simp only [mulPullbackLinear_apply, mulPullback, mul_left_comm]
def reachableWeights (B : Set J) (D : ↥B → ℕ) (l : J → HalfNatural) : Set (J → HalfNatural) :=
  {l₀ | (∀ b, b ∉ B → l b = l₀ b) ∧ IsDegreeCompatible D (restrictTo B l₀) (restrictTo B l)}
theorem reachableWeights_finite (B : Set J) (D : ↥B → ℕ) (l : J → HalfNatural) :
    (reachableWeights B D l).Finite := by
  classical
  let R : J → ℕ := fun b => (l b).doubled + (if h : b ∈ B then D ⟨b, h⟩ else 0)
  have hinj : Function.Injective HalfNatural.doubled := fun x y h => by
    cases x; cases y; simpa using h
  have hfin : ∀ b, {t : HalfNatural | t.doubled ≤ R b}.Finite := fun b =>
    (Set.finite_Iic (R b)).preimage hinj.injOn
  refine (Set.Finite.pi' hfin).subset fun l₀ hl₀ b => ?_
  show (l₀ b).doubled ≤ R b
  by_cases h : b ∈ B
  · have hadm := abs_le.mp (hl₀.2 ⟨b, h⟩)
    have h₂ : ((l₀ b).doubled : ℝ) ≤ (l b).doubled + D ⟨b, h⟩ := by
      simp only [restrictTo, HalfNatural.toReal] at hadm
      linarith [hadm.1]
    have h₃ : (l₀ b).doubled ≤ (l b).doubled + D ⟨b, h⟩ := by exact_mod_cast h₂
    simpa [R, h] using h₃
  · have h₂ := hl₀.1 b h
    simp [R, h, h₂]
section WithFacts
variable [Nonempty J]
theorem isotypicComponent_mem (hC : IsotypicPartSums.Statement) (l : J → HalfNatural)
    (X : C(J → specialUnitary, ℂ)) : isotypicComponent l X ∈ prodCoeffSpan l :=
  ((hC J).1 l _).1
theorem isotypicPartSum_isotypicProj (hC : IsotypicPartSums.Statement)
    (l : J → HalfNatural) (X : HaarL2 J) :
    isotypicPartSum l (isotypicProj l X) = isotypicPartSum l X := by
  obtain ⟨h₁, -, h₃⟩ := (hC J).1 l X
  rw [← h₃]
  exact ((hC J).2.2 l l _ h₁).1
theorem isotypicProj_eq_zero (hC : IsotypicPartSums.Statement)
    (l : J → HalfNatural) (X : C(J → specialUnitary, ℂ)) (h : isotypicComponent l X = 0) :
    isotypicProj l (toHaarL2 (X : (J → specialUnitary) → ℂ)) = 0 := by
  obtain ⟨-, -, h₃⟩ := (hC J).1 l (toHaarL2 (X : (J → specialUnitary) → ℂ))
  rw [← h₃]
  have h' : isotypicPartSum l (toHaarL2 (X : (J → specialUnitary) → ℂ)) = 0 := h
  rw [h']
  exact map_zero (continuousToHaarL2 (J := J))
theorem isotypicComponent_mulPullback_eq_zero (hM : MulPullbackComponents.Statement)
    {B : Set J} (hB : B.Nonempty) {f : (↥B → specialUnitary) → ℂ} (hf : IsRealEntryPolynomial f)
    {D : ↥B → ℕ} (hD : HasDegreeBound D f) {μ l : J → HalfNatural}
    {ψ : C(J → specialUnitary, ℂ)} (hψ : ψ ∈ prodCoeffSpan μ) (h : μ ∉ reachableWeights B D l) :
    isotypicComponent l (mulPullbackLinear B f hf ψ) = 0 := by
  by_contra hne
  exact h ((hM J B f hf D μ ψ hB hD hψ).2.1 l hne)
theorem isotypicComponent_hatSum (hC : IsotypicPartSums.Statement)
    (hS : HatSeriesConvergesStatement) {β : ℝ} (hβ : 0 < β) {B : Set J}
    (hB : B.Nonempty) {f : (↥B → specialUnitary) → ℂ} (hf : IsRealEntryPolynomial f)
    {D : ↥B → ℕ} (hD : HasDegreeBound D f) {H : C(J → specialUnitary, ℂ)}
    (hH : (H : (J → specialUnitary) → ℂ) ∈ smoothSet)
    (l : J → HalfNatural) (N : Finset (J → HalfNatural))
    (hN : ∀ μ, μ ∉ N → isotypicComponent l (mulPullbackLinear B f hf (isotypicComponent μ H)) = 0) :
    isotypicComponent l (hatSum β B f hf H) = ∑ μ ∈ N,
      charCoeffRatio β (restrictTo B μ) (restrictTo B l) •
        isotypicComponent l (mulPullbackLinear B f hf (isotypicComponent μ H)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hlast⟩ := hS J β B f hf D hβ hB hD H hH
  obtain ⟨-, -, heq⟩ := hlast l
  have hterm : ∀ μ, hatIsotypicTerm β B f H l μ =
      charCoeffRatio β (restrictTo B μ) (restrictTo B l) •
        isotypicProj l (toHaarL2
          (mulPullbackLinear B f hf (isotypicComponent μ H) : (J → specialUnitary) → ℂ)) := by
    intro μ
    have hfun : (fun u => pullFromPart B f u *
        isotypicPart μ (toHaarL2 (H : (J → specialUnitary) → ℂ)) u) =
        (mulPullbackLinear B f hf (isotypicComponent μ H) : (J → specialUnitary) → ℂ) := by
      funext u
      have h₂ := ((hC J).1 μ (toHaarL2 (H : (J → specialUnitary) → ℂ))).2.1
      rw [← h₂]
      rfl
    rw [hatIsotypicTerm, hfun]
  have hsum : ∑' μ, hatIsotypicTerm β B f H l μ =
      ∑ μ ∈ N, hatIsotypicTerm β B f H l μ := by
    refine tsum_eq_sum fun μ hμ => ?_
    rw [hterm, isotypicProj_eq_zero hC l _ (hN μ hμ), smul_zero]
  rw [hsum] at heq
  calc isotypicComponent l (hatSum β B f hf H)
      = isotypicPartSumLinear l (isotypicProj l
          (toHaarL2 (hatSum β B f hf H : (J → specialUnitary) → ℂ))) :=
        (isotypicPartSum_isotypicProj hC l _).symm
    _ = _ := by
        rw [heq, map_sum]
        refine Finset.sum_congr rfl fun μ _ => ?_
        rw [hterm, map_smul]
        congr 1
        exact isotypicPartSum_isotypicProj hC l _
theorem isotypicComponent_hatSum_hatSum (hC : IsotypicPartSums.Statement)
    (hM : MulPullbackComponents.Statement)
    (hS : HatSeriesConvergesStatement) {β : ℝ} (hβ : 0 < β) {B B' : Set J}
    (hB : B.Nonempty) (hB' : B'.Nonempty) (hdis : Disjoint B' B)
    {f : (↥B → specialUnitary) → ℂ} (hf : IsRealEntryPolynomial f) {D : ↥B → ℕ}
    (hD : HasDegreeBound D f)
    {f' : (↥B' → specialUnitary) → ℂ} (hf' : IsRealEntryPolynomial f') {D' : ↥B' → ℕ}
    (hD' : HasDegreeBound D' f') {F : C(J → specialUnitary, ℂ)}
    (hF : (F : (J → specialUnitary) → ℂ) ∈ smoothSet) (l₂ : J → HalfNatural) :
    isotypicComponent l₂ (hatSum β B f hf (hatSum β B' f' hf' F)) = ∑' μ : J → HalfNatural,
      (charCoeffRatio β (restrictTo B μ) (restrictTo B l₂) *
        charCoeffRatio β (restrictTo B' μ) (restrictTo B' l₂)) •
        isotypicComponent l₂
          (mulPullbackLinear B f hf (mulPullbackLinear B' f' hf' (isotypicComponent μ F))) := by
  classical
  obtain ⟨-, -, -, -, -, -, -, hsm, -, -⟩ := hS J β B' f' hf' D' hβ hB' hD' F hF
  set G := hatSum β B' f' hf' F with hG
  let U₁ : Finset (J → HalfNatural) := (reachableWeights_finite B D l₂).toFinset
  let U₂ : Finset (J → HalfNatural) :=
    U₁.biUnion fun l₁ => (reachableWeights_finite B' D' l₁).toFinset
  have hU₁ : ∀ l, l ∉ U₁ → l ∉ reachableWeights B D l₂ := fun l h h' =>
    h ((Set.Finite.mem_toFinset _).2 h')
  have hU₂ : ∀ μ, μ ∉ U₂ → ∀ l₁ ∈ U₁, μ ∉ reachableWeights B' D' l₁ := fun μ h l₁ hl₁ h' =>
    h (Finset.mem_biUnion.2 ⟨l₁, hl₁, (Set.Finite.mem_toFinset _).2 h'⟩)
  let ψ : (J → HalfNatural) → C(J → specialUnitary, ℂ) := fun μ =>
    mulPullbackLinear B' f' hf' (isotypicComponent μ F)
  let c₀ : (J → HalfNatural) → ℂ := fun μ =>
    charCoeffRatio β (restrictTo B μ) (restrictTo B l₂) *
      charCoeffRatio β (restrictTo B' μ) (restrictTo B' l₂)
  let T : (J → HalfNatural) → (J → HalfNatural) → C(J → specialUnitary, ℂ) := fun μ l₁ =>
    isotypicComponent l₂ (mulPullbackLinear B f hf (isotypicComponent l₁ (ψ μ)))
  have hstep₁ : isotypicComponent l₂ (hatSum β B f hf G) = ∑ l₁ ∈ U₁,
      charCoeffRatio β (restrictTo B l₁) (restrictTo B l₂) •
        isotypicComponent l₂ (mulPullbackLinear B f hf (isotypicComponent l₁ G)) :=
    isotypicComponent_hatSum hC hS hβ hB hf hD hsm l₂ U₁ fun l₁ h =>
      isotypicComponent_mulPullback_eq_zero hM hB hf hD (isotypicComponent_mem hC l₁ G) (hU₁ l₁ h)
  have hstep₂ : ∀ l₁ ∈ U₁, isotypicComponent l₁ G = ∑ μ ∈ U₂,
      charCoeffRatio β (restrictTo B' μ) (restrictTo B' l₁) •
        isotypicComponent l₁ (ψ μ) := fun l₁ hl₁ =>
    isotypicComponent_hatSum hC hS hβ hB' hf' hD' hF l₁ U₂ fun μ h =>
      isotypicComponent_mulPullback_eq_zero hM hB' hf' hD' (isotypicComponent_mem hC μ F)
        (hU₂ μ h l₁ hl₁)
  have hinner : ∀ μ, ∑ l₁ ∈ U₁,
      (charCoeffRatio β (restrictTo B l₁) (restrictTo B l₂) *
        charCoeffRatio β (restrictTo B' μ) (restrictTo B' l₁)) • T μ l₁ =
      c₀ μ • isotypicComponent l₂ (mulPullbackLinear B f hf (ψ μ)) := by
    intro μ
    have hcoef : ∀ l₁, (charCoeffRatio β (restrictTo B l₁) (restrictTo B l₂) *
        charCoeffRatio β (restrictTo B' μ) (restrictTo B' l₁)) • T μ l₁ =
        c₀ μ • T μ l₁ := by
      intro l₁
      by_cases hT : T μ l₁ = 0
      · rw [hT, smul_zero, smul_zero]
      have hnear : l₁ ∈ reachableWeights B D l₂ := by
        by_contra hn
        exact hT (isotypicComponent_mulPullback_eq_zero hM hB hf hD
          (isotypicComponent_mem hC l₁ (ψ μ)) hn)
      have hne : isotypicComponent l₁ (ψ μ) ≠ 0 := by
        intro h0
        apply hT
        show isotypicComponent l₂ (mulPullbackLinear B f hf (isotypicComponent l₁ (ψ μ))) = 0
        rw [h0, map_zero, map_zero]
      have hout := ((hM J B' f' hf' D' μ (isotypicComponent μ F) hB' hD'
        (isotypicComponent_mem hC μ F)).2.1 l₁ hne).1
      have hr₁ : restrictTo B l₁ = restrictTo B μ := by
        funext b
        exact hout b fun hb => Set.disjoint_left.1 hdis hb b.2
      have hr₂ : restrictTo B' l₁ = restrictTo B' l₂ := by
        funext b
        exact (hnear.1 b fun hb => Set.disjoint_left.1 hdis b.2 hb).symm
      simp only [c₀, hr₁, hr₂]
    simp only [hcoef]
    rw [← Finset.smul_sum]
    congr 1
    have hmul := hM J B' f' hf' D' μ (isotypicComponent μ F) hB' hD'
      (isotypicComponent_mem hC μ F)
    let V : Finset (J → HalfNatural) := hmul.1.toFinset
    have hV : ∀ l₁, l₁ ∉ V → isotypicComponent l₁ (ψ μ) = 0 := fun l₁ h => by
      by_contra hn
      exact h ((Set.Finite.mem_toFinset _).2 hn)
    have hψ : ψ μ = ∑ l₁ ∈ V, isotypicComponent l₁ (ψ μ) := by
      ext u
      rw [ContinuousMap.coe_sum, Finset.sum_apply]
      rw [show (ψ μ) u = _ from hmul.2.2 u]
      refine tsum_eq_sum fun l₁ h => ?_
      have h0 := hV l₁ h
      have h0' : isotypicPartSum l₁ (toHaarL2
          (mulPullback B' f' hf' (isotypicComponent μ F) : (J → specialUnitary) → ℂ)) = 0 := h0
      rw [h0']
      rfl
    have hleft : ∑ l₁ ∈ U₁, T μ l₁ = ∑' l₁, T μ l₁ := by
      refine (tsum_eq_sum fun l₁ h => ?_).symm
      exact isotypicComponent_mulPullback_eq_zero hM hB hf hD
        (isotypicComponent_mem hC l₁ (ψ μ)) (hU₁ l₁ h)
    have hright : ∑ l₁ ∈ V, T μ l₁ = ∑' l₁, T μ l₁ := by
      refine (tsum_eq_sum fun l₁ h => ?_).symm
      show isotypicComponent l₂ (mulPullbackLinear B f hf (isotypicComponent l₁ (ψ μ))) = 0
      rw [hV l₁ h, map_zero, map_zero]
    rw [hleft, ← hright]
    conv_rhs => rw [hψ, map_sum, map_sum]
  have hzero : ∀ μ, μ ∉ U₂ →
      c₀ μ • isotypicComponent l₂ (mulPullbackLinear B f hf (ψ μ)) = 0 := by
    intro μ h
    rw [← hinner μ]
    refine Finset.sum_eq_zero fun l₁ hl₁ => ?_
    have h0 : isotypicComponent l₁ (ψ μ) = 0 :=
      isotypicComponent_mulPullback_eq_zero hM hB' hf' hD' (isotypicComponent_mem hC μ F)
        (hU₂ μ h l₁ hl₁)
    show _ • isotypicComponent l₂ (mulPullbackLinear B f hf (isotypicComponent l₁ (ψ μ))) = 0
    rw [h0, map_zero, map_zero, smul_zero]
  have htsum : ∑' μ, c₀ μ • isotypicComponent l₂ (mulPullbackLinear B f hf (ψ μ)) =
      ∑ μ ∈ U₂, c₀ μ • isotypicComponent l₂ (mulPullbackLinear B f hf (ψ μ)) :=
    tsum_eq_sum hzero
  show isotypicComponent l₂ (hatSum β B f hf G) =
    ∑' μ, c₀ μ • isotypicComponent l₂ (mulPullbackLinear B f hf (ψ μ))
  rw [htsum, hstep₁]
  have hexpand : ∀ l₁ ∈ U₁, charCoeffRatio β (restrictTo B l₁) (restrictTo B l₂) •
      isotypicComponent l₂ (mulPullbackLinear B f hf (isotypicComponent l₁ G)) = ∑ μ ∈ U₂,
        (charCoeffRatio β (restrictTo B l₁) (restrictTo B l₂) *
          charCoeffRatio β (restrictTo B' μ) (restrictTo B' l₁)) • T μ l₁ := by
    intro l₁ hl₁
    rw [hstep₂ l₁ hl₁, map_sum, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [map_smul, map_smul, smul_smul]
  rw [Finset.sum_congr rfl hexpand, Finset.sum_comm]
  exact Finset.sum_congr rfl fun μ _ => hinner μ
end WithFacts
end HatDisjointCommute
theorem hatDisjointCommute
    (hC : IsotypicPartSums.Statement)
    (hM : MulPullbackComponents.Statement)
    (hS : HatSeriesConvergesStatement)
    (hDecay : SmoothToSobolevDecayStatement)
    (hDeg : PolynomialDegrees.Statement) :
    HatDisjointCommuteStatement := by
  intro J _ _ β B f hf hβ hB B' f' hf' F hB' hdis hF
  have : Nonempty ↥B := hB.to_subtype
  have : Nonempty ↥B' := hB'.to_subtype
  obtain ⟨D, hD⟩ := ((hDeg ↥B) f hf.1).2
  obtain ⟨D', hD'⟩ := ((hDeg ↥B') f' hf'.1).2
  obtain ⟨-, -, -, -, -, -, -, hsm', -, -⟩ := hS J β B' f' hf' D' hβ hB' hD' F hF
  obtain ⟨-, -, -, -, -, -, -, hsm, -, -⟩ := hS J β B f hf D hβ hB hD F hF
  obtain ⟨-, -, -, -, -, -, -, hT, -, -⟩ := hS J β B f hf D hβ hB hD _ hsm'
  obtain ⟨-, -, -, -, -, -, -, hT', -, -⟩ := hS J β B' f' hf' D' hβ hB' hD' _ hsm
  have hcomp : ∀ l : J → HalfNatural,
      HatDisjointCommute.isotypicComponent l
        (hatSum β B f hf (hatSum β B' f' hf' F)) =
      HatDisjointCommute.isotypicComponent l
        (hatSum β B' f' hf' (hatSum β B f hf F)) := by
    intro l
    rw [HatDisjointCommute.isotypicComponent_hatSum_hatSum hC hM hS hβ hB hB' hdis hf hD
        hf' hD' hF l,
      HatDisjointCommute.isotypicComponent_hatSum_hatSum hC hM hS hβ hB' hB hdis.symm
        hf' hD' hf hD hF l]
    refine tsum_congr fun μ => ?_
    rw [mul_comm, HatDisjointCommute.mulPullbackLinear_comm]
  have hproj : ∀ (X : C(J → specialUnitary, ℂ)) (l : J → HalfNatural),
      isotypicPart l (toHaarL2 (X : (J → specialUnitary) → ℂ)) =
        (HatDisjointCommute.isotypicComponent l X : (J → specialUnitary) → ℂ) := fun X l =>
    (((hC J).1 l (toHaarL2 (X : (J → specialUnitary) → ℂ))).2.1).symm
  ext u
  have h₁ := ((hDecay J _ hT).2).tendsto_at u
  have h₂ := ((hDecay J _ hT').2).tendsto_at u
  simp only [hproj, hcomp] at h₁ h₂
  exact tendsto_nhds_unique h₁ h₂
end YangMills.Construction.SpinHarmonics
end
