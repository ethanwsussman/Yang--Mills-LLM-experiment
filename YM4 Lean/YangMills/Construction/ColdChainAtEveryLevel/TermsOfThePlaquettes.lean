import YangMills.Construction.ColdChainAtEveryLevel.TermsOfTheLevelsBelowTheTop
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
namespace YangMills.Construction.PlaquetteTerms
open BlockAverages LevelRecursion PlaquetteSecondDifference RealDirections LowerLevelTerms WeightedAverages.Chains
  BlockLines HullBounds ComplexDifferences
variable {F : BlockFrame}
theorem plaquetteHolonomy_eq_prod {j : ℕ} (X : F.GaugeField j) (q : F.Site j × Fin 4 × Fin 4) :
    plaquetteHolonomy X q = X q.1 q.2.1 * X (q.1 + unitStep j q.2.1) q.2.2 * (X (q.1 + unitStep j q.2.2) q.2.1)⁻¹ *
      (X q.1 q.2.2)⁻¹ := by apply _root_.YangMills.Construction.SmallCellTerms.plaquetteHolonomy_eq <;> assumption
def plaquetteLinks (q : F.Site 0 × Fin 4 × Fin 4) : Fin 4 → F.Site 0 × Fin 4 :=
  ![(q.1, q.2.1), (q.1 + unitStep 0 q.2.1, q.2.2), (q.1 + unitStep 0 q.2.2, q.2.1), (q.1, q.2.2)]
def plaquetteRefLinks (R : F.GaugeField 0) (q : F.Site 0 × Fin 4 × Fin 4) : Fin 4 → UnitQuaternion :=
  fun i => R (plaquetteLinks q i).1 (plaquetteLinks q i).2
def plaquetteDirections (u : F.Site 0 → Fin 4 → imaginaryQuaternions) (q : F.Site 0 × Fin 4 × Fin 4) :
    Fin 4 → imaginaryQuaternions :=
  fun i => u (plaquetteLinks q i).1 (plaquetteLinks q i).2
theorem plaquetteHolonomy_expUnit_field (R : F.GaugeField 0) (u : F.Site 0 → Fin 4 → imaginaryQuaternions)
    (q : F.Site 0 × Fin 4 × Fin 4) :
    plaquetteHolonomy (fun x i => expUnit (u x i) * R x i) q =
      plaquetteVariation (plaquetteRefLinks R q) (plaquetteDirections u q) * refHolonomy (plaquetteRefLinks R q) := by
  rw [plaquetteHolonomy_eq_prod, ← plaquetteHolonomy_expUnit]
  rfl
theorem plaquetteHolonomy_eq_refHolonomy (R : F.GaugeField 0) (q : F.Site 0 × Fin 4 × Fin 4) :
    plaquetteHolonomy R q = refHolonomy (plaquetteRefLinks R q) := by
  rw [plaquetteHolonomy_eq_prod]
  rfl
theorem linearizedCurl_eq_covariantCurl (R : F.GaugeField 0) (u : F.Site 0 → Fin 4 → imaginaryQuaternions)
    (q : F.Site 0 × Fin 4 × Fin 4) :
    linearizedCurl R u q = covariantCurl (plaquetteRefLinks R q) (plaquetteDirections u q) := rfl
def plaquetteAction (R : F.FieldChain) (W : ChainChart F) (q : F.Site 0 × Fin 4 × Fin 4) : ℝ :=
  1 - ((plaquetteHolonomy (chartField R W 0) q : UnitQuaternion) : ℍ[ℝ]).re
theorem abs_plaquetteAction_second_diff_le (R : F.FieldChain) {W₁ W₂ W₃ : ChainChart F}
    (q : F.Site 0 × Fin 4 × Fin 4) {t₁ t₂ : ℝ}
    (h3 : plaquetteDirections W₃.fine q = plaquetteDirections W₁.fine q + plaquetteDirections W₂.fine q)
    (h1 : ∑ i, ‖(plaquetteDirections W₁.fine q i : ℍ[ℝ])‖ ≤ t₁)
    (h2 : ∑ i, ‖(plaquetteDirections W₂.fine q i : ℍ[ℝ])‖ ≤ t₂)
    (ht1 : t₁ ≤ 1 / 4000) (ht2 : t₂ ≤ 1 / 4000) :
    |plaquetteAction R W₃ q - plaquetteAction R W₁ q - plaquetteAction R W₂ q + plaquetteAction R (zeroChart F) q -
        inner ℝ (linearizedCurl (R 0) W₁.fine q) (linearizedCurl (R 0) W₂.fine q)| ≤
      200000 * t₁ * t₂ * (plaquetteDefect (R 0) q + t₁ + t₂) := by
  have e : ∀ W : ChainChart F, plaquetteAction R W q = 1 -
      ((plaquetteVariation (plaquetteRefLinks (R 0) q) (plaquetteDirections W.fine q) *
        refHolonomy (plaquetteRefLinks (R 0) q) : UnitQuaternion) : ℍ[ℝ]).re := by
    intro W
    have : chartField R W 0 = fun x i => expUnit (W.fine x i) * R 0 x i := rfl
    rw [plaquetteAction, this, plaquetteHolonomy_expUnit_field]
  have e0 : plaquetteDirections (zeroChart F).fine q = 0 := rfl
  have ec : plaquetteDefect (R 0) q = ‖((refHolonomy (plaquetteRefLinks (R 0) q) : UnitQuaternion) : ℍ[ℝ]) - 1‖ := by
    rw [plaquetteDefect, plaquetteHolonomy_eq_refHolonomy]
  rw [e, e, e, e, e0, plaquetteVariation_zero, one_mul, h3, linearizedCurl_eq_covariantCurl,
    linearizedCurl_eq_covariantCurl, ec]
  exact abs_plaquette_second_diff_sub_inner_le _ _ _ h1 h2 ht1 ht2
theorem finsetLpNorm_comp_le {ι κ τ : Type} [DecidableEq κ] [DecidableEq τ] [Fintype τ] (P : Finset ι) (B : Finset κ)
    (β : ι → κ) (ρ : ι → τ) (hτ : Fintype.card τ ≤ 16) (hβ : ∀ q ∈ P, β q ∈ B)
    (hinj : Set.InjOn (fun q => (β q, ρ q)) (P : Set ι))
    (G : κ → ℝ) : finsetLpNorm 4 P (fun q => G (β q)) ≤ 2 * finsetLpNorm 4 B G := by
  refine finsetLpNorm_le_of_sum_pow_le (by norm_num) P B _ G (by norm_num) ?_
  set h : κ → ℝ := fun b => |G b| ^ 4 with hh
  have hh0 : ∀ b, 0 ≤ h b := fun b => by positivity
  have e1 : ∑ q ∈ P, |G (β q)| ^ 4 = ∑ r ∈ P.image (fun q => (β q, ρ q)), h r.1 := by
    rw [Finset.sum_image hinj]
  have hsub : P.image (fun q => (β q, ρ q)) ⊆ B ×ˢ (Finset.univ : Finset τ) := by
    intro r hr
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hr
    exact Finset.mem_product.2 ⟨hβ q hq, Finset.mem_univ _⟩
  have e2 : ∑ r ∈ B ×ˢ (Finset.univ : Finset τ), h r.1 = (Fintype.card τ : ℝ) * ∑ b ∈ B, h b := by
    rw [Finset.sum_product]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Finset.mul_sum]
  have hs : 0 ≤ ∑ b ∈ B, h b := Finset.sum_nonneg fun b _ => hh0 b
  rw [e1]
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun r _ _ => hh0 r.1).trans ?_
  rw [e2]
  have h16 : (Fintype.card τ : ℝ) ≤ 2 ^ 4 := by
    have : (Fintype.card τ : ℝ) ≤ 16 := by exact_mod_cast hτ
    calc _ ≤ (16 : ℝ) := this
      _ = 2 ^ 4 := by norm_num
  exact mul_le_mul_of_nonneg_right h16 hs
theorem sum_mul_le_sqrt_card_mul_finsetLpNorm {ι : Type} (P : Finset ι) (A B : ι → ℝ) :
    ∑ q ∈ P, A q * B q ≤ Real.sqrt (P.card : ℝ) * (finsetLpNorm 4 P A * finsetLpNorm 4 P B) := by
  have hc := Real.sum_mul_le_sqrt_mul_sqrt P (fun q => A q * B q) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul] at hc
  have h2 := finsetLpNorm_two_mul_le P A B
  rw [finsetLpNorm_two_eq_sqrt] at h2
  calc _ ≤ Real.sqrt (∑ q ∈ P, (A q * B q) ^ 2) * Real.sqrt (P.card : ℝ) := hc
    _ ≤ (finsetLpNorm 4 P A * finsetLpNorm 4 P B) * Real.sqrt (P.card : ℝ) :=
        mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _)
    _ = _ := by ring
theorem scaleWeight_le_two_mul_neighbour (hodd : Odd F.blockSide) {θ : ℝ} (hθ : |θ| ≤ 1 / 8) (x : F.Site 0)
    (μ : Fin 4) (p : F.Site 0) :
    scaleWeight p θ 0 x ≤ 2 * scaleWeight p θ 0 (x + unitStep 0 μ) := by apply _root_.YangMills.Construction.PlaquettesNearCell.scaleWeight_le_two_mul_add_unitStep <;> assumption
theorem plaquetteLinks_mem {D : Finset F.Cell} {q : F.Site 0 × Fin 4 × Fin 4} (hq : q ∈ innerPlaquettes D 0)
    (i : Fin 4) : plaquetteLinks q i ∈ innerBonds D 0 := by
  have hc : plaquetteCorners q ⊆ sitesOfCells D 0 := (Finset.mem_filter.1 hq).2.2
  have c0 : q.1 ∈ sitesOfCells D 0 := hc (by simp [plaquetteCorners])
  have c1 : q.1 + unitStep 0 q.2.1 ∈ sitesOfCells D 0 := hc (by simp [plaquetteCorners])
  have c2 : q.1 + unitStep 0 q.2.2 ∈ sitesOfCells D 0 := hc (by simp [plaquetteCorners])
  have c3 : q.1 + unitStep 0 q.2.1 + unitStep 0 q.2.2 ∈ sitesOfCells D 0 := hc (by simp [plaquetteCorners])
  have c3' : q.1 + unitStep 0 q.2.2 + unitStep 0 q.2.1 ∈ sitesOfCells D 0 := by
    rw [add_right_comm]
    exact c3
  have mk : ∀ (b : F.Site 0 × Fin 4), b.1 ∈ sitesOfCells D 0 → b.1 + unitStep 0 b.2 ∈ sitesOfCells D 0 →
      b ∈ innerBonds D 0 :=
    fun b h1 h2 => Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨h1, Finset.mem_univ _⟩, h2⟩
  fin_cases i
  · exact mk _ c0 c1
  · exact mk _ c1 c3
  · exact mk _ c2 c3'
  · exact mk _ c0 c2
theorem plaquetteLinks_injective (i : Fin 4) :
    Function.Injective (fun q : F.Site 0 × Fin 4 × Fin 4 => (plaquetteLinks q i, q.2)) := by
  rintro ⟨x, μ, ν⟩ ⟨x', μ', ν'⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, rfl, rfl⟩ := h
  fin_cases i
  · have : x = x' := (Prod.mk.inj h1).1
    rw [this]
  · have : x + unitStep 0 μ = x' + unitStep 0 μ := (Prod.mk.inj h1).1
    rw [add_right_cancel this]
  · have : x + unitStep 0 ν = x' + unitStep 0 ν := (Prod.mk.inj h1).1
    rw [add_right_cancel this]
  · have : x = x' := (Prod.mk.inj h1).1
    rw [this]
theorem scaleWeight_le_two_mul_plaquetteLinks (hodd : Odd F.blockSide) {θ : ℝ} (hθ : |θ| ≤ 1 / 8) (p : F.Site 0)
    (q : F.Site 0 × Fin 4 × Fin 4) (i : Fin 4) :
    scaleWeight p θ 0 q.1 ≤ 2 * scaleWeight p θ 0 (plaquetteLinks q i).1 := by
  have hw := scaleWeight_pos hodd p θ 0 q.1
  fin_cases i
  · change scaleWeight p θ 0 q.1 ≤ 2 * scaleWeight p θ 0 q.1
    linarith
  · exact scaleWeight_le_two_mul_neighbour hodd hθ _ _ _
  · exact scaleWeight_le_two_mul_neighbour hodd hθ _ _ _
  · change scaleWeight p θ 0 q.1 ≤ 2 * scaleWeight p θ 0 q.1
    linarith
theorem sum_plaquette_pair_le (hodd : Odd F.blockSide) {D : Finset F.Cell} {p : F.Site 0} {θ : ℝ}
    (hθ : |θ| ≤ 1 / 8) {P : Finset (F.Site 0 × Fin 4 × Fin 4)} (hP : P ⊆ innerPlaquettes D 0)
    {f g : F.Site 0 → Fin 4 → ℝ} (hf : ∀ x d, 0 ≤ f x d) (hg : ∀ x d, 0 ≤ g x d) {B₁ B₂ : ℝ}
    (h1 : weightedScaleNorm D p θ 4 0 f ≤ B₁) (h2 : weightedScaleNorm D p (-θ) 4 0 g ≤ B₂) (i i' : Fin 4) :
    ∑ q ∈ P, f (plaquetteLinks q i).1 (plaquetteLinks q i).2 * g (plaquetteLinks q i').1 (plaquetteLinks q i').2 ≤
      Real.sqrt (P.card : ℝ) * ((4 * B₁) * (4 * B₂)) := by
  classical
  have hθ' : |(-θ)| ≤ 1 / 8 := by rwa [abs_neg]
  set A : F.Site 0 × Fin 4 × Fin 4 → ℝ := fun q => scaleWeight p θ 0 q.1 *
    f (plaquetteLinks q i).1 (plaquetteLinks q i).2 with hA
  set B : F.Site 0 × Fin 4 × Fin 4 → ℝ := fun q => scaleWeight p (-θ) 0 q.1 *
    g (plaquetteLinks q i').1 (plaquetteLinks q i').2 with hB
  have e : ∀ q : F.Site 0 × Fin 4 × Fin 4, f (plaquetteLinks q i).1 (plaquetteLinks q i).2 *
      g (plaquetteLinks q i').1 (plaquetteLinks q i').2 = A q * B q := by
    intro q
    have h := scaleWeight_mul_scaleWeight_neg hodd p θ 0 q.1
    simp only [hA, hB]
    calc _ = (scaleWeight p θ 0 q.1 * scaleWeight p (-θ) 0 q.1) *
          (f (plaquetteLinks q i).1 (plaquetteLinks q i).2 * g (plaquetteLinks q i').1 (plaquetteLinks q i').2) := by
          rw [h, one_mul]
      _ = _ := by ring
  simp only [e]
  refine (sum_mul_le_sqrt_card_mul_finsetLpNorm P A B).trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
  have key : ∀ {θ₀ : ℝ} {G : F.Site 0 → Fin 4 → ℝ} {j : Fin 4} {Bd : ℝ}, |θ₀| ≤ 1 / 8 → (∀ x d, 0 ≤ G x d) →
      weightedScaleNorm D p θ₀ 4 0 G ≤ Bd →
      finsetLpNorm 4 P (fun q => scaleWeight p θ₀ 0 q.1 * G (plaquetteLinks q j).1 (plaquetteLinks q j).2) ≤
        4 * Bd := by
    intro θ₀ G j Bd hθ₀ hG hBd
    have s1 : finsetLpNorm 4 P (fun q => scaleWeight p θ₀ 0 q.1 * G (plaquetteLinks q j).1 (plaquetteLinks q j).2) ≤
        finsetLpNorm 4 P (fun q => 2 * (scaleWeight p θ₀ 0 (plaquetteLinks q j).1 *
          G (plaquetteLinks q j).1 (plaquetteLinks q j).2)) := by
      refine finsetLpNorm_mono (by norm_num) _ fun q _ => ?_
      have hw := scaleWeight_pos hodd p θ₀ 0 q.1
      have hw' := scaleWeight_pos hodd p θ₀ 0 (plaquetteLinks q j).1
      have hg0 := hG (plaquetteLinks q j).1 (plaquetteLinks q j).2
      rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
      have := mul_le_mul_of_nonneg_right (scaleWeight_le_two_mul_plaquetteLinks hodd hθ₀ p q j) hg0
      linarith
    have s2 := finsetLpNorm_const_mul_le (P := 4) (by norm_num) P
      (fun q => scaleWeight p θ₀ 0 (plaquetteLinks q j).1 * G (plaquetteLinks q j).1 (plaquetteLinks q j).2)
      (a := 2) (by norm_num)
    have s3 := finsetLpNorm_comp_le P (innerBonds D 0) (fun q => plaquetteLinks q j) (fun q => q.2)
      (by simp [Fintype.card_prod]) (fun q hq => plaquetteLinks_mem (hP hq) j)
      ((plaquetteLinks_injective j).injOn) (fun b => scaleWeight p θ₀ 0 b.1 * G b.1 b.2)
    have s4 : finsetLpNorm 4 (innerBonds D 0) (fun b => scaleWeight p θ₀ 0 b.1 * G b.1 b.2) ≤ Bd := hBd
    linarith
  have kA : finsetLpNorm 4 P A ≤ 4 * B₁ := key (j := i) hθ hf h1
  have kB : finsetLpNorm 4 P B ≤ 4 * B₂ := key (j := i') hθ' hg h2
  exact mul_le_mul kA kB (finsetLpNorm_nonneg _ _ _) ((finsetLpNorm_nonneg _ _ _).trans kA)
theorem card_innerPlaquettes_le (hodd : Odd F.blockSide) {D : Finset F.Cell} (hD : D.card ≤ 81) :
    ((innerPlaquettes D 0).card : ℝ) ≤ (36 * ((F.blockSide : ℝ) ^ F.top) ^ 2) ^ 2 := by
  have h1 : (innerPlaquettes D 0).card ≤ ((sitesOfCells D 0) ×ˢ (Finset.univ : Finset (Fin 4)) ×ˢ
      (Finset.univ : Finset (Fin 4))).card := Finset.card_filter_le _ _
  rw [Finset.card_product, Finset.card_product, Finset.card_univ, Fintype.card_fin] at h1
  have h2 := card_sitesOfCells_le hodd D 0
  have h3 : ((innerPlaquettes D 0).card : ℝ) ≤ (((sitesOfCells D 0).card * (4 * 4) : ℕ) : ℝ) := by
    exact_mod_cast h1
  have h4 : ((sitesOfCells D 0).card : ℝ) ≤ ((D.card * (F.blockSide ^ (F.top - 0)) ^ 4 : ℕ) : ℝ) := by
    exact_mod_cast h2
  push_cast at h3 h4
  rw [Nat.sub_zero] at h4
  have h5 : (D.card : ℝ) ≤ 81 := by exact_mod_cast hD
  have h6 : (0 : ℝ) ≤ ((F.blockSide : ℝ) ^ F.top) ^ 4 := by positivity
  have h7 : (D.card : ℝ) * ((F.blockSide : ℝ) ^ F.top) ^ 4 ≤ 81 * ((F.blockSide : ℝ) ^ F.top) ^ 4 :=
    mul_le_mul_of_nonneg_right h5 h6
  calc _ ≤ ((sitesOfCells D 0).card : ℝ) * 16 := h3
    _ ≤ 81 * ((F.blockSide : ℝ) ^ F.top) ^ 4 * 16 := by linarith
    _ = _ := by ring
theorem sum_plaquette_sizes_le (hodd : Odd F.blockSide) {D : Finset F.Cell} (hD : D.card ≤ 81) {p : F.Site 0}
    {θ : ℝ} (hθ : |θ| ≤ 1 / 8) {P : Finset (F.Site 0 × Fin 4 × Fin 4)} (hP : P ⊆ innerPlaquettes D 0)
    {f g : F.Site 0 → Fin 4 → ℝ} (hf : ∀ x d, 0 ≤ f x d) (hg : ∀ x d, 0 ≤ g x d) {B₁ B₂ : ℝ}
    (h1 : weightedScaleNorm D p θ 4 0 f ≤ B₁) (h2 : weightedScaleNorm D p (-θ) 4 0 g ≤ B₂) :
    ∑ q ∈ P, (∑ i, f (plaquetteLinks q i).1 (plaquetteLinks q i).2) *
        (∑ i, g (plaquetteLinks q i).1 (plaquetteLinks q i).2) ≤
      9216 * ((F.blockSide : ℝ) ^ F.top) ^ 2 * (B₁ * B₂) := by
  have hB₁ : 0 ≤ B₁ := (weightedScaleNorm_nonneg' _ _ _ _ _ _).trans h1
  have hB₂ : 0 ≤ B₂ := (weightedScaleNorm_nonneg' _ _ _ _ _ _).trans h2
  have hs : Real.sqrt (P.card : ℝ) ≤ 36 * ((F.blockSide : ℝ) ^ F.top) ^ 2 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, le_trans ?_ (card_innerPlaquettes_le hodd hD)⟩
    exact_mod_cast Finset.card_le_card hP
  have hx : 0 ≤ (4 * B₁) * (4 * B₂) := by positivity
  have e : ∑ q ∈ P, (∑ i, f (plaquetteLinks q i).1 (plaquetteLinks q i).2) *
      (∑ i, g (plaquetteLinks q i).1 (plaquetteLinks q i).2) =
      ∑ i : Fin 4, ∑ i' : Fin 4, ∑ q ∈ P, f (plaquetteLinks q i).1 (plaquetteLinks q i).2 *
        g (plaquetteLinks q i').1 (plaquetteLinks q i').2 := by
    simp only [Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
  rw [e]
  have hone : ∀ i i' : Fin 4, ∑ q ∈ P, f (plaquetteLinks q i).1 (plaquetteLinks q i).2 *
      g (plaquetteLinks q i').1 (plaquetteLinks q i').2 ≤
        36 * ((F.blockSide : ℝ) ^ F.top) ^ 2 * ((4 * B₁) * (4 * B₂)) :=
    fun i i' => (sum_plaquette_pair_le hodd hθ hP hf hg h1 h2 i i').trans (mul_le_mul_of_nonneg_right hs hx)
  calc _ ≤ ∑ i : Fin 4, ∑ i' : Fin 4, 36 * ((F.blockSide : ℝ) ^ F.top) ^ 2 * ((4 * B₁) * (4 * B₂)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun i' _ => hone i i'
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
theorem sum_abs_plaquetteAction_second_diff_le (hodd : Odd F.blockSide) {D : Finset F.Cell} (hD : D.card ≤ 81)
    {p : F.Site 0} {θ : ℝ} (hθ : |θ| ≤ 1 / 8) {R : F.FieldChain} {W₁ W₂ W₃ : ChainChart F} {c₀ T B₁ B₂ : ℝ}
    {P : Finset (F.Site 0 × Fin 4 × Fin 4)} (hP : P ⊆ innerPlaquettes D 0) (hc₀ : 0 ≤ c₀)
    (hc : ∀ q ∈ innerPlaquettes D 0, plaquetteDefect (R 0) q ≤ c₀ * ((1 / (F.blockSide : ℝ)) ^ F.top) ^ 2)
    (hT0 : 0 ≤ T) (hT : 4 * T ≤ 1 / 4000)
    (hu₁ : ∀ b ∈ innerBonds D 0, ‖(W₁.fine b.1 b.2 : ℍ[ℝ])‖ ≤ T)
    (hu₂ : ∀ b ∈ innerBonds D 0, ‖(W₂.fine b.1 b.2 : ℍ[ℝ])‖ ≤ T)
    (hu₃ : ∀ b ∈ innerBonds D 0, W₃.fine b.1 b.2 = W₁.fine b.1 b.2 + W₂.fine b.1 b.2)
    (h1 : weightedScaleNorm D p θ 4 0 (fun x i => ‖(W₁.fine x i : ℍ[ℝ])‖) ≤ B₁)
    (h2 : weightedScaleNorm D p (-θ) 4 0 (fun x i => ‖(W₂.fine x i : ℍ[ℝ])‖) ≤ B₂) :
    ∑ q ∈ P, |plaquetteAction R W₃ q - plaquetteAction R W₁ q - plaquetteAction R W₂ q +
        plaquetteAction R (zeroChart F) q - inner ℝ (linearizedCurl (R 0) W₁.fine q) (linearizedCurl (R 0) W₂.fine q)| ≤
      200000 * (9216 * (c₀ * (B₁ * B₂))) + (P.card : ℝ) * (200000 * (128 * T ^ 3)) := by
  have hL1 : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  set f : F.Site 0 → Fin 4 → ℝ := fun x i => ‖(W₁.fine x i : ℍ[ℝ])‖ with hf
  set g : F.Site 0 → Fin 4 → ℝ := fun x i => ‖(W₂.fine x i : ℍ[ℝ])‖ with hg
  set κ := c₀ * ((1 / (F.blockSide : ℝ)) ^ F.top) ^ 2 with hκ
  have hpoint : ∀ q ∈ P, |plaquetteAction R W₃ q - plaquetteAction R W₁ q - plaquetteAction R W₂ q +
      plaquetteAction R (zeroChart F) q - inner ℝ (linearizedCurl (R 0) W₁.fine q) (linearizedCurl (R 0) W₂.fine q)| ≤
      200000 * κ * ((∑ i, f (plaquetteLinks q i).1 (plaquetteLinks q i).2) *
        (∑ i, g (plaquetteLinks q i).1 (plaquetteLinks q i).2)) + 200000 * (128 * T ^ 3) := by
    intro q hq
    have hq' := hP hq
    set t₁ := ∑ i, f (plaquetteLinks q i).1 (plaquetteLinks q i).2 with ht₁
    set t₂ := ∑ i, g (plaquetteLinks q i).1 (plaquetteLinks q i).2 with ht₂
    have b1 : t₁ ≤ 4 * T := by
      have := Finset.sum_le_card_nsmul Finset.univ (fun i => f (plaquetteLinks q i).1 (plaquetteLinks q i).2) T
        (fun i _ => hu₁ _ (plaquetteLinks_mem hq' i))
      simpa using this
    have b2 : t₂ ≤ 4 * T := by
      have := Finset.sum_le_card_nsmul Finset.univ (fun i => g (plaquetteLinks q i).1 (plaquetteLinks q i).2) T
        (fun i _ => hu₂ _ (plaquetteLinks_mem hq' i))
      simpa using this
    have t10 : 0 ≤ t₁ := Finset.sum_nonneg fun i _ => norm_nonneg _
    have t20 : 0 ≤ t₂ := Finset.sum_nonneg fun i _ => norm_nonneg _
    have h3 : plaquetteDirections W₃.fine q = plaquetteDirections W₁.fine q + plaquetteDirections W₂.fine q := by
      funext i
      exact hu₃ _ (plaquetteLinks_mem hq' i)
    have key := abs_plaquetteAction_second_diff_le R (W₁ := W₁) (W₂ := W₂) (W₃ := W₃) q (t₁ := t₁) (t₂ := t₂) h3
      le_rfl le_rfl (by linarith) (by linarith)
    refine key.trans ?_
    have hcq := hc q hq'
    have s1 : 200000 * t₁ * t₂ * plaquetteDefect (R 0) q ≤ 200000 * κ * (t₁ * t₂) := by
      have := mul_le_mul_of_nonneg_left hcq (by positivity : 0 ≤ 200000 * (t₁ * t₂))
      linarith
    have s2 : t₁ * t₂ * (t₁ + t₂) ≤ (4 * T) * (4 * T) * (4 * T + 4 * T) :=
      mul_le_mul (mul_le_mul b1 b2 t20 (by positivity)) (by linarith) (by positivity) (by positivity)
    have s3 : 200000 * t₁ * t₂ * (plaquetteDefect (R 0) q + t₁ + t₂) =
        200000 * t₁ * t₂ * plaquetteDefect (R 0) q + 200000 * (t₁ * t₂ * (t₁ + t₂)) := by ring
    have s4 : (4 * T) * (4 * T) * (4 * T + 4 * T) = 128 * T ^ 3 := by ring
    rw [s3]
    rw [s4] at s2
    linarith
  refine (Finset.sum_le_sum hpoint).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
  refine add_le_add_left ?_ _
  have hs := sum_plaquette_sizes_le hodd hD hθ hP (f := f) (g := g) (fun _ _ => norm_nonneg _)
    (fun _ _ => norm_nonneg _) h1 h2
  have hN := (inv_pow_bounds hL1 F.top).2.2
  have e : κ * (9216 * ((F.blockSide : ℝ) ^ F.top) ^ 2 * (B₁ * B₂)) = 9216 * (c₀ * (B₁ * B₂)) := by
    have e1 : ((1 / (F.blockSide : ℝ)) ^ F.top) ^ 2 * ((F.blockSide : ℝ) ^ F.top) ^ 2 = 1 := by
      rw [← mul_pow, hN, one_pow]
    calc _ = 9216 * (c₀ * (B₁ * B₂)) * (((1 / (F.blockSide : ℝ)) ^ F.top) ^ 2 * ((F.blockSide : ℝ) ^ F.top) ^ 2) := by
          rw [hκ]
          ring
      _ = _ := by rw [e1, mul_one]
  have := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 200000 * κ)
  calc _ ≤ 200000 * κ * (9216 * ((F.blockSide : ℝ) ^ F.top) ^ 2 * (B₁ * B₂)) := this
    _ = 200000 * (κ * (9216 * ((F.blockSide : ℝ) ^ F.top) ^ 2 * (B₁ * B₂))) := by ring
    _ = _ := by rw [e]
end YangMills.Construction.PlaquetteTerms
end
