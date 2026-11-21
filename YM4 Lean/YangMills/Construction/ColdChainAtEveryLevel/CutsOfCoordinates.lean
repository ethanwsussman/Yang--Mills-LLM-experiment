import YangMills.Construction.ColdChainAtEveryLevel.PairsAtOffsets
import YangMills.Construction.ColdChainAtEveryLevel.PlaquettesNearACell
import YangMills.Construction.HoleBesideASecondHole.CellsPutBackProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
namespace YangMills.Construction.CoordinateCutoffs
open BlockAverages BlockAverages.Offsets CoordinateSeminorms BlockLines PlaquettesNearCell
variable {F : BlockFrame}
structure IsCutoff (χ : F.SiteWeights) : Prop where
  nonneg : ∀ j (x : F.Site j), 0 ≤ χ j x
  le_one : ∀ j (x : F.Site j), χ j x ≤ 1
  lipschitz : ∀ (x : F.Site 0) (i : Fin 4), |χ 0 (x + unitStep 0 i) - χ 0 x| ≤ 1 / (F.blockSide : ℝ) ^ F.top
theorem abs_clamp_sub_clamp_le (a b : ℝ) : |max 0 (min 1 a) - max 0 (min 1 b)| ≤ |a - b| := by apply _root_.YangMills.Construction.Reinsertion.abs_clamp_sub_clamp_le <;> assumption
theorem tentCutoff_isCutoff (hL : 0 < F.blockSide) (Y : F.Cell) (ρ : ℝ) : IsCutoff (tentCutoff F Y ρ) where
  nonneg _ _ := le_max_left _ _
  le_one _ _ := max_le zero_le_one (min_le_left _ _)
  lipschitz x i := by
    have hN : (0 : ℝ) < (F.blockSide : ℝ) ^ F.top := by
      have : (0 : ℝ) < (F.blockSide : ℝ) := by exact_mod_cast hL
      positivity
    obtain ⟨h1, h2⟩ := baseDistance_add_unitStep x i (cellCentre 0 Y)
    refine (abs_clamp_sub_clamp_le _ _).trans ?_
    have e : ρ - (baseDistance (x + unitStep 0 i) (cellCentre 0 Y) : ℝ) / (F.blockSide : ℝ) ^ F.top -
        (ρ - (baseDistance x (cellCentre 0 Y) : ℝ) / (F.blockSide : ℝ) ^ F.top) =
        ((baseDistance x (cellCentre 0 Y) : ℝ) - baseDistance (x + unitStep 0 i) (cellCentre 0 Y)) / (F.blockSide : ℝ) ^ F.top := by
      ring
    rw [e, abs_div, abs_of_pos hN]
    refine div_le_div_of_nonneg_right ?_ hN.le
    rw [abs_le]
    have h1' : (baseDistance (x + unitStep 0 i) (cellCentre 0 Y) : ℝ) ≤ baseDistance x (cellCentre 0 Y) + 1 := by
      exact_mod_cast h1
    have h2' : (baseDistance x (cellCentre 0 Y) : ℝ) ≤ baseDistance (x + unitStep 0 i) (cellCentre 0 Y) + 1 := by
      exact_mod_cast h2
    constructor <;> linarith
theorem IsCutoff.one_sub {χ : F.SiteWeights} (h : IsCutoff χ) : IsCutoff (fun j x => 1 - χ j x) where
  nonneg j x := by linarith [h.le_one j x]
  le_one j x := by linarith [h.nonneg j x]
  lipschitz x i := by
    have := h.lipschitz x i
    rw [show 1 - χ 0 (x + unitStep 0 i) - (1 - χ 0 x) = -(χ 0 (x + unitStep 0 i) - χ 0 x) by ring, abs_neg]
    exact this
theorem adjointAction_smul (g : UnitQuaternion) (t : ℝ) (x : ℍ[ℝ]) : adjointAction g (t • x) = t • adjointAction g x := by apply _root_.YangMills.Construction.BlockAverages.adjointAction_smul <;> assumption
theorem norm_linearizedCurl_smul_le (R : F.GaugeField 0) (χ : F.Site 0 → ℝ) (u : F.Site 0 → Fin 4 → imaginaryQuaternions)
    (q : F.Site 0 × Fin 4 × Fin 4)
    (hχ : 0 ≤ χ q.1 ∧ χ q.1 ≤ 1) {ε : ℝ} (h1 : |χ (q.1 + unitStep 0 q.2.1) - χ q.1| ≤ ε)
    (h2 : |χ (q.1 + unitStep 0 q.2.2) - χ q.1| ≤ ε) :
    ‖linearizedCurl R (fun x i => χ x • u x i) q‖ ≤ ‖linearizedCurl R u q‖ +
      ε * (‖(u (q.1 + unitStep 0 q.2.1) q.2.2 : ℍ[ℝ])‖ + ‖(u (q.1 + unitStep 0 q.2.2) q.2.1 : ℍ[ℝ])‖) := by
  obtain ⟨x, μ, ν⟩ := q
  simp only at hχ h1 h2 ⊢
  have e : linearizedCurl R (fun x i => χ x • u x i) (x, μ, ν) =
      χ x • linearizedCurl R u (x, μ, ν) +
        (χ (x + unitStep 0 μ) - χ x) • adjointAction (R x μ) (u (x + unitStep 0 μ) ν) -
        (χ (x + unitStep 0 ν) - χ x) • adjointAction (R x μ * R (x + unitStep 0 μ) ν * (R (x + unitStep 0 ν) μ)⁻¹)
          (u (x + unitStep 0 ν) μ) := by
    simp only [linearizedCurl, Submodule.coe_smul, adjointAction_smul, sub_smul, smul_sub, smul_add]
    abel
  rw [e]
  have n1 : ‖χ x • linearizedCurl R u (x, μ, ν)‖ ≤ ‖linearizedCurl R u (x, μ, ν)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hχ.1]
    exact mul_le_of_le_one_left (norm_nonneg _) hχ.2
  have n2 : ‖(χ (x + unitStep 0 μ) - χ x) • adjointAction (R x μ) (u (x + unitStep 0 μ) ν)‖ ≤
      ε * ‖(u (x + unitStep 0 μ) ν : ℍ[ℝ])‖ := by
    rw [norm_smul, Real.norm_eq_abs, PlaquetteLinearization.norm_adjointAction]
    exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  have n3 : ‖(χ (x + unitStep 0 ν) - χ x) • adjointAction (R x μ * R (x + unitStep 0 μ) ν * (R (x + unitStep 0 ν) μ)⁻¹)
      (u (x + unitStep 0 ν) μ)‖ ≤ ε * ‖(u (x + unitStep 0 ν) μ : ℍ[ℝ])‖ := by
    rw [norm_smul, Real.norm_eq_abs, PlaquetteLinearization.norm_adjointAction]
    exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
  have n4 := norm_sub_le (χ x • linearizedCurl R u (x, μ, ν) +
      (χ (x + unitStep 0 μ) - χ x) • adjointAction (R x μ) (u (x + unitStep 0 μ) ν))
    ((χ (x + unitStep 0 ν) - χ x) • adjointAction (R x μ * R (x + unitStep 0 μ) ν * (R (x + unitStep 0 ν) μ)⁻¹)
      (u (x + unitStep 0 ν) μ))
  have n5 := norm_add_le (χ x • linearizedCurl R u (x, μ, ν))
    ((χ (x + unitStep 0 μ) - χ x) • adjointAction (R x μ) (u (x + unitStep 0 μ) ν))
  rw [mul_add]
  linarith
theorem localNormSq_chartSmul_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (S : Finset F.Cell)
    (R : F.FieldChain) {χ : F.SiteWeights} (hχ : IsCutoff χ) (A : ChainChart F) (z : F.Cell) :
    localNormSq S (cellBall S z 3) R (chartSmul χ A) (constOneWeights F) ≤
      20737 * localNormSq S (cellBall S z 4) R A (constOneWeights F) := by
  classical
  set B := cellBall S z 3 with hB
  set D := cellBall S z 4 with hD
  have hBD : B ⊆ D := by
    intro y hy
    have h := Finset.mem_filter.1 hy
    exact Finset.mem_filter.2 ⟨h.1, h.2.trans (by norm_num)⟩
  set X : ℝ := ∑ b ∈ bondsOver S D 0, ‖(A.fine b.1 b.2 : ℍ[ℝ])‖ ^ 4 with hX
  set Y : ℝ := ∑ p ∈ plaquettesOver S D 0, ‖linearizedCurl (R 0) A.fine p‖ ^ 2 with hY
  have hY0 : 0 ≤ Y := Finset.sum_nonneg fun _ _ => by positivity
  set Z : ℝ := ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S D (j + 1), ‖(A.coarse j c.1 c.2 : ℍ[ℝ])‖ ^ 2 with hZ
  have hZ0 : 0 ≤ Z := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  have hrhs : localNormSq S D R A (constOneWeights F) = Real.sqrt X + Y + Z := by
    unfold localNormSq
    simp only [constOneWeights, one_mul]
    rfl
  have hLpos : 0 < F.blockSide := hodd.pos
  set N : ℝ := (F.blockSide : ℝ) ^ F.top with hN
  have hN0 : 0 < N := by positivity
  have a1 : ∑ b ∈ bondsOver S B 0, ‖((chartSmul χ A).fine b.1 b.2 : ℍ[ℝ])‖ ^ 4 ≤ X := by
    refine (Finset.sum_le_sum fun b _ => ?_).trans (Finset.sum_le_sum_of_subset_of_nonneg
      (fun b hb => ?_) fun _ _ _ => by positivity)
    · show ‖((χ 0 b.1 • A.fine b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ])‖ ^ 4 ≤ ‖(A.fine b.1 b.2 : ℍ[ℝ])‖ ^ 4
      rw [Submodule.coe_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hχ.nonneg 0 _)]
      exact pow_le_pow_left₀ (by have := hχ.nonneg 0 b.1; positivity)
        (mul_le_of_le_one_left (norm_nonneg _) (hχ.le_one 0 _)) 4
    · rw [mem_bondsOver] at hb ⊢
      exact ⟨hb.1, hBD hb.2⟩
  have a3 : ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S B (j + 1),
      ‖((chartSmul χ A).coarse j c.1 c.2 : ℍ[ℝ])‖ ^ 2 ≤ Z := by
    refine Finset.sum_le_sum fun j _ => ?_
    refine (Finset.sum_le_sum fun b _ => ?_).trans (Finset.sum_le_sum_of_subset_of_nonneg
      (fun b hb => ?_) fun _ _ _ => by positivity)
    · show ‖((χ (j + 1) b.1 • A.coarse j b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ])‖ ^ 2 ≤ ‖(A.coarse j b.1 b.2 : ℍ[ℝ])‖ ^ 2
      rw [Submodule.coe_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hχ.nonneg _ _)]
      exact pow_le_pow_left₀ (by have := hχ.nonneg (j + 1) b.1; positivity)
        (mul_le_of_le_one_left (norm_nonneg _) (hχ.le_one _ _)) 2
    · rw [mem_bondsOver] at hb ⊢
      exact ⟨hb.1, hBD hb.2⟩
  set T : ℝ := ∑ b ∈ innerBonds D 0, ‖(A.fine b.1 b.2 : ℍ[ℝ])‖ ^ 2 with hT
  have hcardD : (D.card : ℝ) ≤ 9 ^ 4 := by
    have h1 := PatchLocality.card_le_of_cellSupDist_le z 4 D (fun y hy => by
      have h := (Finset.mem_filter.1 hy).2
      rw [CoordinateSeminorms.cellSupDist_comm]
      exact h)
    have h2 : D.card ≤ 6561 := by
      refine h1.trans (le_of_eq ?_)
      norm_num
    have h3 : (D.card : ℝ) ≤ 6561 := by exact_mod_cast h2
    linarith
  have hcardb : ((innerBonds D 0).card : ℝ) ≤ 4 * 9 ^ 4 * N ^ 4 := by
    have h1 : innerBonds D 0 ⊆ sitesOfCells D 0 ×ˢ (Finset.univ : Finset (Fin 4)) := Finset.filter_subset _ _
    have h2 := Finset.card_le_card h1
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin] at h2
    have h3 := card_sitesOfCells_le hodd D 0
    have h4 : ((sitesOfCells D 0).card : ℝ) ≤ D.card * N ^ 4 := by
      have : ((sitesOfCells D 0).card : ℝ) ≤ ((D.card * (F.blockSide ^ (F.top - 0)) ^ 4 : ℕ) : ℝ) := by
        exact_mod_cast h3
      simpa [hN] using this
    have h5 : ((innerBonds D 0).card : ℝ) ≤ (sitesOfCells D 0).card * 4 := by exact_mod_cast h2
    have h6 : (D.card : ℝ) * N ^ 4 ≤ 9 ^ 4 * N ^ 4 := mul_le_mul_of_nonneg_right hcardD (by positivity)
    nlinarith
  have hsubX : ∑ b ∈ innerBonds D 0, ‖(A.fine b.1 b.2 : ℍ[ℝ])‖ ^ 4 ≤ X := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun b hb => ?_) fun _ _ _ => by positivity
    rw [mem_bondsOver]
    have hbS : b ∈ innerBonds S 0 := innerBonds_mono (cellBall_subset S z 4) 0 hb
    refine ⟨hbS, CoordinateSeminorms.enclosingCell_mem hodd (S := D) ?_⟩
    exact (Finset.mem_product.1 (Finset.mem_filter.1 hb).1).1
  have hTsq : T ^ 2 ≤ (162 * N ^ 2) ^ 2 * X := by
    have h1 := sq_sum_le_card_mul_sum_sq (s := innerBonds D 0) (f := fun b => ‖(A.fine b.1 b.2 : ℍ[ℝ])‖ ^ 2)
    have h2 : ∑ b ∈ innerBonds D 0, (‖(A.fine b.1 b.2 : ℍ[ℝ])‖ ^ 2) ^ 2 ≤ X := by
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun b _ => ?_)) hsubX
      ring
    calc T ^ 2 ≤ ((innerBonds D 0).card : ℝ) * ∑ b ∈ innerBonds D 0, (‖(A.fine b.1 b.2 : ℍ[ℝ])‖ ^ 2) ^ 2 := h1
      _ ≤ (4 * 9 ^ 4 * N ^ 4) * X := mul_le_mul hcardb h2 (Finset.sum_nonneg fun _ _ => by positivity)
          (by positivity)
      _ = (162 * N ^ 2) ^ 2 * X := by ring
  have hTle : T ≤ 162 * N ^ 2 * Real.sqrt X := by
    have h1 := Real.le_sqrt_of_sq_le hTsq
    rwa [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)] at h1
  have hmap : ∀ q ∈ plaquettesOver S B 0, (q.1 + unitStep 0 q.2.1, q.2.2) ∈ innerBonds D 0 ∧
      (q.1 + unitStep 0 q.2.2, q.2.1) ∈ innerBonds D 0 := by
    intro q hq
    obtain ⟨hq1, hq2⟩ := mem_plaquettesOver.1 hq
    have hq' : q ∈ plaquettesOver S {enclosingCell q.1} 0 := mem_plaquettesOver.2 ⟨hq1, by simp⟩
    obtain ⟨-, b2, b3, -⟩ := plaquette_bonds_mem_innerBonds hamb hodd hq'
    have hsub : cellBall S (enclosingCell q.1) 1 ⊆ D := by
      intro y hy
      have hy' := Finset.mem_filter.1 hy
      have hzq := (Finset.mem_filter.1 hq2).2
      refine Finset.mem_filter.2 ⟨hy'.1, ?_⟩
      have := CoordinateSeminorms.cellSupDist_triangle z (enclosingCell q.1) y
      omega
    exact ⟨innerBonds_mono hsub 0 b2, innerBonds_mono hsub 0 b3⟩
  have hs1 := sum_comp_bond_le (D := D) (plaquettesOver S B 0) (fun q => (q.1 + unitStep 0 q.2.1, q.2.2))
    (fun q q' h2 e1 => by
      have e2 : q.1 + unitStep 0 q.2.1 = q'.1 + unitStep 0 q'.2.1 := congrArg Prod.fst e1
      rw [h2] at e2
      exact Prod.ext (add_right_cancel e2) h2) (fun q hq => (hmap q hq).1)
    (fun b => ‖(A.fine b.1 b.2 : ℍ[ℝ])‖ ^ 2) (fun _ => by positivity)
  have hs2 := sum_comp_bond_le (D := D) (plaquettesOver S B 0) (fun q => (q.1 + unitStep 0 q.2.2, q.2.1))
    (fun q q' h2 e1 => by
      have e2 : q.1 + unitStep 0 q.2.2 = q'.1 + unitStep 0 q'.2.2 := congrArg Prod.fst e1
      rw [h2] at e2
      exact Prod.ext (add_right_cancel e2) h2) (fun q hq => (hmap q hq).2)
    (fun b => ‖(A.fine b.1 b.2 : ℍ[ℝ])‖ ^ 2) (fun _ => by positivity)
  simp only at hs1 hs2
  have a2 : ∑ p ∈ plaquettesOver S B 0, ‖linearizedCurl (R 0) (chartSmul χ A).fine p‖ ^ 2 ≤
      2 * Y + 20736 * Real.sqrt X := by
    have hpt : ∀ q ∈ plaquettesOver S B 0, ‖linearizedCurl (R 0) (chartSmul χ A).fine q‖ ^ 2 ≤
        2 * ‖linearizedCurl (R 0) A.fine q‖ ^ 2 + 4 * (1 / N) ^ 2 * (‖(A.fine (q.1 + unitStep 0 q.2.1) q.2.2 : ℍ[ℝ])‖ ^ 2 +
          ‖(A.fine (q.1 + unitStep 0 q.2.2) q.2.1 : ℍ[ℝ])‖ ^ 2) := by
      intro q _
      have h1 := norm_linearizedCurl_smul_le (R 0) (χ 0) A.fine q ⟨hχ.nonneg 0 _, hχ.le_one 0 _⟩
        (hχ.lipschitz q.1 q.2.1) (hχ.lipschitz q.1 q.2.2)
      have h0 := norm_nonneg (linearizedCurl (R 0) (chartSmul χ A).fine q)
      have h2 : ‖linearizedCurl (R 0) (chartSmul χ A).fine q‖ ≤ ‖linearizedCurl (R 0) A.fine q‖ +
          1 / N * (‖(A.fine (q.1 + unitStep 0 q.2.1) q.2.2 : ℍ[ℝ])‖ +
            ‖(A.fine (q.1 + unitStep 0 q.2.2) q.2.1 : ℍ[ℝ])‖) := h1
      generalize ‖linearizedCurl (R 0) (chartSmul χ A).fine q‖ = c₁ at *
      generalize ‖linearizedCurl (R 0) A.fine q‖ = c₂ at *
      generalize ‖(A.fine (q.1 + unitStep 0 q.2.1) q.2.2 : ℍ[ℝ])‖ = e₁ at *
      generalize ‖(A.fine (q.1 + unitStep 0 q.2.2) q.2.1 : ℍ[ℝ])‖ = e₂ at *
      generalize 1 / N = ε at *
      have h3 := pow_le_pow_left₀ h0 h2 2
      nlinarith [sq_nonneg (c₂ - ε * (e₁ + e₂)), sq_nonneg (ε * (e₁ - e₂))]
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib]
    have h1 : ∑ q ∈ plaquettesOver S B 0, ‖linearizedCurl (R 0) A.fine q‖ ^ 2 ≤ Y :=
      Finset.sum_le_sum_of_subset_of_nonneg (fun q hq => by
        rw [mem_plaquettesOver] at hq ⊢
        exact ⟨hq.1, hBD hq.2⟩) fun _ _ _ => by positivity
    have h2 : 4 * (1 / N) ^ 2 * (16 * T + 16 * T) ≤ 20736 * Real.sqrt X := by
      have e : 4 * (1 / N) ^ 2 * (16 * T + 16 * T) = 128 * T / N ^ 2 := by
        field_simp
        ring
      rw [e, div_le_iff₀ (by positivity)]
      nlinarith
    have h3 : 4 * (1 / N) ^ 2 * (∑ q ∈ plaquettesOver S B 0, ‖(A.fine (q.1 + unitStep 0 q.2.1) q.2.2 : ℍ[ℝ])‖ ^ 2 +
        ∑ q ∈ plaquettesOver S B 0, ‖(A.fine (q.1 + unitStep 0 q.2.2) q.2.1 : ℍ[ℝ])‖ ^ 2) ≤
        4 * (1 / N) ^ 2 * (16 * T + 16 * T) :=
      mul_le_mul_of_nonneg_left (add_le_add hs1 hs2) (by positivity)
    linarith
  have hsqrt : Real.sqrt (∑ b ∈ bondsOver S B 0, ‖((chartSmul χ A).fine b.1 b.2 : ℍ[ℝ])‖ ^ 4) ≤ Real.sqrt X :=
    Real.sqrt_le_sqrt a1
  have hlhs : localNormSq S B R (chartSmul χ A) (constOneWeights F) =
      Real.sqrt (∑ b ∈ bondsOver S B 0, ‖((chartSmul χ A).fine b.1 b.2 : ℍ[ℝ])‖ ^ 4) +
        ∑ p ∈ plaquettesOver S B 0, ‖linearizedCurl (R 0) (chartSmul χ A).fine p‖ ^ 2 +
        ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S B (j + 1),
          ‖((chartSmul χ A).coarse j c.1 c.2 : ℍ[ℝ])‖ ^ 2 := by
    unfold localNormSq
    simp only [constOneWeights, one_mul]
    rfl
  rw [hlhs, hrhs]
  nlinarith
theorem sum_pow_natAbs_Icc_le {q : ℝ} (hq : 0 ≤ q) (D : ℕ) :
    ∑ n ∈ Finset.Icc (-(D : ℤ)) D, q ^ n.natAbs ≤ 2 * ∑ k ∈ Finset.range (D + 1), q ^ k := by
  induction D with
  | zero => simp
  | succ D ih =>
    have hsub : Finset.Icc (-((D + 1 : ℕ) : ℤ)) ((D + 1 : ℕ) : ℤ) ⊆
        insert (((D + 1 : ℕ) : ℤ)) (insert (-((D + 1 : ℕ) : ℤ)) (Finset.Icc (-(D : ℤ)) D)) := by
      intro n hn
      simp only [Finset.mem_Icc, Finset.mem_insert] at hn ⊢
      push_cast at hn ⊢
      omega
    have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := fun n : ℤ => q ^ n.natAbs)
      (fun _ _ _ => pow_nonneg hq _)
    have hne : ∀ (s : Finset ℤ) (a : ℤ) (g : ℤ → ℝ), (∀ x, 0 ≤ g x) →
        ∑ x ∈ insert a s, g x ≤ g a + ∑ x ∈ s, g x := by
      intro s a g hg
      by_cases ha : a ∈ s
      · rw [Finset.insert_eq_of_mem ha]
        linarith [hg a]
      · rw [Finset.sum_insert ha]
    have h2 := hne (insert (-((D + 1 : ℕ) : ℤ)) (Finset.Icc (-(D : ℤ)) D)) (((D + 1 : ℕ) : ℤ))
      (fun n : ℤ => q ^ n.natAbs) (fun _ => pow_nonneg hq _)
    have h3 := hne (Finset.Icc (-(D : ℤ)) D) (-((D + 1 : ℕ) : ℤ)) (fun n : ℤ => q ^ n.natAbs)
      (fun _ => pow_nonneg hq _)
    simp only [Int.natAbs_neg, Int.natAbs_natCast] at h2 h3
    rw [Finset.sum_range_succ, mul_add]
    linarith
theorem exists_sum_exp_neg_cellSupDist_le {ε : ℝ} (hε : 0 < ε) : ∃ Cd : ℝ, 0 < Cd ∧
    ∀ (F : BlockFrame) (S : Finset F.Cell) (y : F.Cell),
    ∑ z ∈ S, Real.exp (-ε * cellSupDist z y) ≤ Cd := by
  classical
  set q : ℝ := Real.exp (-ε / 4) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by
    rw [hq, Real.exp_lt_one_iff]
    linarith
  refine ⟨(2 / (1 - q)) ^ 4, by have : 0 < 1 - q := by linarith
                                positivity, fun F S y => ?_⟩
  set o : F.Cell → Fin 4 → ℤ := fun z i => ((z i - y i).valMinAbs) with ho
  have hinj : Function.Injective o := by
    intro z z' h
    funext i
    have h1 := congrFun h i
    simp only [ho] at h1
    have h2 := congrArg (fun n : ℤ => ((n : ℤ) : ZMod (F.period F.top i))) h1
    simp only [ZMod.coe_valMinAbs] at h2
    exact sub_left_injective h2
  set D : ℕ := S.sup fun z => cellSupDist z y with hD
  have hterm : ∀ z ∈ S, Real.exp (-ε * cellSupDist z y) ≤ ∏ i, q ^ (o z i).natAbs := by
    intro z _
    have hle : ∀ i, (o z i).natAbs ≤ cellSupDist z y := fun i =>
      Finset.le_sup (f := fun i => ((z i - y i).valMinAbs).natAbs) (Finset.mem_univ i)
    have h1 : ∏ i, q ^ (o z i).natAbs = Real.exp (-ε / 4 * ∑ i, ((o z i).natAbs : ℝ)) := by
      simp only [hq, ← Real.exp_nat_mul]
      rw [← Real.exp_sum, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h1]
    apply Real.exp_le_exp.2
    have h2 : ∑ i, ((o z i).natAbs : ℝ) ≤ 4 * (cellSupDist z y : ℝ) := by
      have : ∑ i : Fin 4, ((o z i).natAbs : ℝ) ≤ ∑ _i : Fin 4, (cellSupDist z y : ℝ) :=
        Finset.sum_le_sum fun i _ => by exact_mod_cast hle i
      simpa using this
    nlinarith
  refine (Finset.sum_le_sum hterm).trans ?_
  have himg : ∑ z ∈ S, ∏ i, q ^ (o z i).natAbs = ∑ v ∈ S.image o, ∏ i, q ^ (v i).natAbs :=
    (Finset.sum_image (f := fun v : Fin 4 → ℤ => ∏ i, q ^ (v i).natAbs) fun a _ b _ h => hinj h).symm
  rw [himg]
  have hsub : S.image o ⊆ Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(D : ℤ)) D := by
    intro v hv
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hv
    refine Fintype.mem_piFinset.2 fun i => ?_
    have h1 : (o z i).natAbs ≤ cellSupDist z y :=
      Finset.le_sup (f := fun i => ((z i - y i).valMinAbs).natAbs) (Finset.mem_univ i)
    have h2 : cellSupDist z y ≤ D := Finset.le_sup (f := fun z => cellSupDist z y) hz
    rw [Finset.mem_Icc]
    omega
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ =>
    Finset.prod_nonneg fun _ _ => pow_nonneg hq0.le _).trans ?_
  rw [← Finset.prod_univ_sum (fun _ : Fin 4 => Finset.Icc (-(D : ℤ)) D) (fun _ n => q ^ n.natAbs)]
  have hone : ∑ n ∈ Finset.Icc (-(D : ℤ)) D, q ^ n.natAbs ≤ 2 / (1 - q) := by
    refine (sum_pow_natAbs_Icc_le hq0.le D).trans ?_
    have h1 := geom_sum_mul_neg q (D + 1)
    have h2 : 0 < 1 - q := by linarith
    have h3 : ∑ k ∈ Finset.range (D + 1), q ^ k ≤ 1 / (1 - q) := by
      rw [le_div_iff₀ h2, h1]
      have := pow_nonneg hq0.le (D + 1)
      linarith
    calc 2 * ∑ k ∈ Finset.range (D + 1), q ^ k ≤ 2 * (1 / (1 - q)) :=
          mul_le_mul_of_nonneg_left h3 (by norm_num)
      _ = 2 / (1 - q) := by ring
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => pow_nonneg hq0.le _) hone 4
theorem localNormSq_le_of_weights_le (S B : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F)
    (w w' : F.SiteWeights) (κ : ℝ) (hκ : 0 ≤ κ)
    (h : ∀ (j : ℕ) (x : F.Site j), enclosingCell x ∈ B → 0 ≤ w' j x ∧ w' j x ≤ κ * w j x) :
    localNormSq S B R U w' ≤ κ ^ 2 * localNormSq S B R U w := by
  have term : ∀ (e j : ℕ) (x : F.Site j) (c : ℝ), 0 ≤ c → enclosingCell x ∈ B →
      (w' j x * c) ^ e ≤ κ ^ e * (w j x * c) ^ e := by
    intro e j x c hc hx
    obtain ⟨h1, h2⟩ := h j x hx
    have h3 : w' j x * c ≤ κ * (w j x * c) := by
      have := mul_le_mul_of_nonneg_right h2 hc
      linarith
    calc (w' j x * c) ^ e ≤ (κ * (w j x * c)) ^ e := pow_le_pow_left₀ (mul_nonneg h1 hc) h3 e
      _ = κ ^ e * (w j x * c) ^ e := mul_pow _ _ _
  have h1 : ∑ b ∈ bondsOver S B 0, (w' 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4 ≤
      κ ^ 4 * ∑ b ∈ bondsOver S B 0, (w 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun b hb => term 4 0 b.1 _ (norm_nonneg _) (mem_bondsOver.1 hb).2
  have h2 : ∑ p ∈ plaquettesOver S B 0, (w' 0 p.1 * ‖linearizedCurl (R 0) U.fine p‖) ^ 2 ≤
      κ ^ 2 * ∑ p ∈ plaquettesOver S B 0, (w 0 p.1 * ‖linearizedCurl (R 0) U.fine p‖) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun b hb => term 2 0 b.1 _ (norm_nonneg _) (mem_plaquettesOver.1 hb).2
  have h3 : ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S B (j + 1),
        (w' (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 ≤
      κ ^ 2 * ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S B (j + 1),
        (w (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun b hb => term 2 (j + 1) b.1 _ (norm_nonneg _) (mem_bondsOver.1 hb).2
  have h4 : Real.sqrt (∑ b ∈ bondsOver S B 0, (w' 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4) ≤
      κ ^ 2 * Real.sqrt (∑ b ∈ bondsOver S B 0, (w 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4) := by
    refine (Real.sqrt_le_sqrt h1).trans (le_of_eq ?_)
    rw [show κ ^ 4 = (κ ^ 2) ^ 2 by ring, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  unfold localNormSq
  rw [mul_add, mul_add]
  linarith
theorem sum_sum_cellBall_le (S : Finset F.Cell) (ρ : ℕ) (f : F.Cell → ℝ) (hf : ∀ y, 0 ≤ f y) :
    ∑ z ∈ S, ∑ y ∈ cellBall S z ρ, f y ≤ ((2 * ρ + 1 : ℕ) : ℝ) ^ 4 * ∑ y ∈ S, f y := by
  classical
  have e : ∑ z ∈ S, ∑ y ∈ cellBall S z ρ, f y = ∑ y ∈ S, ∑ _z ∈ cellBall S y ρ, f y := by
    refine Finset.sum_comm' fun z y => ?_
    constructor
    · rintro ⟨h1, h2⟩
      have h3 := Finset.mem_filter.1 h2
      refine ⟨Finset.mem_filter.2 ⟨h1, ?_⟩, h3.1⟩
      rw [CoordinateSeminorms.cellSupDist_comm]
      exact h3.2
    · rintro ⟨h1, h2⟩
      have h3 := Finset.mem_filter.1 h1
      refine ⟨h3.1, Finset.mem_filter.2 ⟨h2, ?_⟩⟩
      rw [CoordinateSeminorms.cellSupDist_comm]
      exact h3.2
  rw [e, Finset.mul_sum]
  refine Finset.sum_le_sum fun y _ => ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have h1 := PatchLocality.card_le_of_cellSupDist_le y ρ (cellBall S y ρ) (fun z hz => by
    have h := (Finset.mem_filter.1 hz).2
    rw [CoordinateSeminorms.cellSupDist_comm]
    exact h)
  have h2 : ((cellBall S y ρ).card : ℝ) ≤ ((2 * ρ + 1 : ℕ) : ℝ) ^ 4 := by exact_mod_cast h1
  exact mul_le_mul_of_nonneg_right h2 (hf y)
theorem classWeight_zero (φ : F.Cell → ℝ) (p : F.Site 0) (j : ℕ) (x : F.Site j) :
    classWeight F φ 0 p j x = Real.exp (φ (enclosingCell x)) := by
  simp [classWeight]
theorem invertedWeights_classWeight (φ : F.Cell → ℝ) (p : F.Site 0) :
    invertedWeights (classWeight F φ 0 p) = classWeight F (fun y => -φ y) 0 p := by
  funext j x
  simp only [invertedWeights, classWeight_zero, Real.exp_neg]
theorem weightedNorm_chartSmul_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (S : Finset F.Cell)
    (R : F.FieldChain) {χ : F.SiteWeights} (hχ : IsCutoff χ) (A : ChainChart F) (φ : F.Cell → ℝ) (p : F.Site 0)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ8 : δ ≤ 1 / 8) (hφ : ∀ y y', |φ y - φ y'| ≤ δ * cellSupDist y y') :
    weightedNorm S R (chartSmul χ A) (classWeight F φ 0 p) ≤
      Real.exp 1 * (20737 * 6561) * weightedNorm S R A (classWeight F φ 0 p) := by
  set w := classWeight F φ 0 p with hw
  have hcell : ∀ (z : F.Cell) (ρ : ℕ) (j : ℕ) (x : F.Site j), enclosingCell x ∈ cellBall S z ρ →
      |φ (enclosingCell x) - φ z| ≤ δ * ρ := by
    intro z ρ j x hx
    have h1 : cellSupDist z (enclosingCell x) ≤ ρ := (Finset.mem_filter.1 hx).2
    have h2 := hφ (enclosingCell x) z
    rw [CoordinateSeminorms.cellSupDist_comm] at h2
    refine h2.trans (mul_le_mul_of_nonneg_left ?_ hδ)
    exact_mod_cast h1
  have hz : ∀ z ∈ S, localNormSq S (cellBall S z 3) R (chartSmul χ A) w ≤
      (Real.exp 2 * 20737) * ∑ y ∈ cellBall S z 4, localNorm S R A w y ^ 2 := by
    intro z _
    have e1 : localNormSq S (cellBall S z 3) R (chartSmul χ A) w ≤
        (Real.exp (3 * δ) * Real.exp (φ z)) ^ 2 *
          localNormSq S (cellBall S z 3) R (chartSmul χ A) (constOneWeights F) := by
      refine localNormSq_le_of_weights_le S _ R _ (constOneWeights F) w _ (by positivity) fun j x hx => ?_
      have h1 := abs_le.1 (hcell z 3 j x hx)
      refine ⟨(Real.exp_pos _).le.trans_eq (classWeight_zero φ p j x).symm, ?_⟩
      show w j x ≤ Real.exp (3 * δ) * Real.exp (φ z) * 1
      rw [hw, classWeight_zero, mul_one, ← Real.exp_add]
      apply Real.exp_le_exp.2
      push_cast at h1
      linarith [h1.2]
    have e2 := localNormSq_chartSmul_le hamb hodd S R hχ A z
    have e3 : localNormSq S (cellBall S z 4) R A (constOneWeights F) ≤
        (Real.exp (4 * δ) * Real.exp (-φ z)) ^ 2 * localNormSq S (cellBall S z 4) R A w := by
      refine localNormSq_le_of_weights_le S _ R _ w (constOneWeights F) _ (by positivity) fun j x hx => ?_
      refine ⟨zero_le_one, ?_⟩
      show (1 : ℝ) ≤ Real.exp (4 * δ) * Real.exp (-φ z) * w j x
      have h1 := abs_le.1 (hcell z 4 j x hx)
      rw [hw, classWeight_zero, ← Real.exp_add, ← Real.exp_add]
      apply Real.one_le_exp
      push_cast at h1
      linarith [h1.1]
    have e4 : localNormSq S (cellBall S z 4) R A w ≤ ∑ y ∈ cellBall S z 4, localNorm S R A w y ^ 2 := by
      refine (localNormSq_le_sum_singletons S _ R A w).trans (Finset.sum_le_sum fun y hy => ?_)
      have hyS : y ∈ S := (Finset.mem_filter.1 hy).1
      have h1 : localNormSq S {y} R A w ≤ localNormSq S (cellBall S y 3) R A w :=
        localNormSq_mono_cells S (fun x hx => by
          rw [Finset.mem_singleton] at hx
          subst hx
          exact mem_cellBall_self hyS) R A w
      refine h1.trans (le_of_eq ?_)
      unfold localNorm
      rw [Real.sq_sqrt (localNormSq_nonneg S _ R A w)]
    have hn0 : 0 ≤ localNormSq S (cellBall S z 4) R A w := localNormSq_nonneg _ _ _ _ _
    have hm0 : 0 ≤ localNormSq S (cellBall S z 4) R A (constOneWeights F) := localNormSq_nonneg _ _ _ _ _
    have hprod : (Real.exp (3 * δ) * Real.exp (φ z)) ^ 2 * (Real.exp (4 * δ) * Real.exp (-φ z)) ^ 2 ≤
        Real.exp 2 := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
      apply Real.exp_le_exp.2
      push_cast
      nlinarith
    have hq : 0 ≤ (Real.exp (3 * δ) * Real.exp (φ z)) ^ 2 := by positivity
    calc localNormSq S (cellBall S z 3) R (chartSmul χ A) w
        ≤ (Real.exp (3 * δ) * Real.exp (φ z)) ^ 2 *
            (20737 * localNormSq S (cellBall S z 4) R A (constOneWeights F)) :=
          e1.trans (mul_le_mul_of_nonneg_left e2 hq)
      _ ≤ (Real.exp (3 * δ) * Real.exp (φ z)) ^ 2 *
            (20737 * ((Real.exp (4 * δ) * Real.exp (-φ z)) ^ 2 * localNormSq S (cellBall S z 4) R A w)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left e3 (by norm_num)) hq
      _ = ((Real.exp (3 * δ) * Real.exp (φ z)) ^ 2 * (Real.exp (4 * δ) * Real.exp (-φ z)) ^ 2) *
            (20737 * localNormSq S (cellBall S z 4) R A w) := by ring
      _ ≤ Real.exp 2 * (20737 * localNormSq S (cellBall S z 4) R A w) :=
          mul_le_mul_of_nonneg_right hprod (by positivity)
      _ ≤ Real.exp 2 * (20737 * ∑ y ∈ cellBall S z 4, localNorm S R A w y ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left e4 (by norm_num)) (Real.exp_pos _).le
      _ = Real.exp 2 * 20737 * ∑ y ∈ cellBall S z 4, localNorm S R A w y ^ 2 := by ring
  have hsq : weightedNorm S R (chartSmul χ A) w ^ 2 ≤
      (Real.exp 1 * (20737 * 6561) * weightedNorm S R A w) ^ 2 := by
    rw [weightedNorm_sq]
    have h1 := Finset.sum_le_sum hz
    rw [← Finset.mul_sum] at h1
    have h2 := sum_sum_cellBall_le S 4 (fun y => localNorm S R A w y ^ 2) (fun _ => sq_nonneg _)
    have e3 : ∑ y ∈ S, localNorm S R A w y ^ 2 = weightedNorm S R A w ^ 2 := by
      unfold weightedNorm
      rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    rw [e3] at h2
    refine h1.trans ((mul_le_mul_of_nonneg_left h2 (by positivity)).trans ?_)
    have hn : 0 ≤ weightedNorm S R A w ^ 2 := sq_nonneg _
    have e4 : (Real.exp 1 * (20737 * 6561) * weightedNorm S R A w) ^ 2 =
        Real.exp 2 * (20737 * 6561) ^ 2 * weightedNorm S R A w ^ 2 := by
      rw [mul_pow, mul_pow, ← Real.exp_nat_mul]
      norm_num
    rw [e4]
    have e5 : Real.exp 2 * 20737 * ((((2 * 4 + 1 : ℕ) : ℝ) ^ 4) * weightedNorm S R A w ^ 2) =
        Real.exp 2 * (20737 * 6561) * weightedNorm S R A w ^ 2 := by
      norm_num
      ring
    rw [e5]
    refine mul_le_mul_of_nonneg_right ?_ hn
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    norm_num
  exact (pow_le_pow_iff_left₀ (weightedNorm_nonneg _ _ _ _)
    (mul_nonneg (by positivity) (weightedNorm_nonneg _ _ _ _)) (by norm_num)).1 hsq
end YangMills.Construction.CoordinateCutoffs
end
