import YangMills.Construction.ColdChainAtEveryLevel.ComplexCells
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
namespace YangMills.Construction.PlaquettesNearCell
open BlockAverages LevelRecursion ComplexPlaquettes ComplexCells HullBounds BlockLines LatticePaths
  WeightedAverages.Chains LatticeFractionalIntegration ComplexifiedQuaternions FiniteDifferences
variable {F : BlockFrame}
theorem enclosingCell_shift_mem_cellBall (hamb : IsAdmissibleAmbient F) (hL : Odd F.blockSide)
    {S : Finset F.Cell} {z : F.Cell} {j : ℕ} (hj : j ≤ F.top)
    {h : Lattice4} (hh : h ∈ centredCube (F.blockSide ^ (F.top - j))) {g : Lattice4} (hg : ∀ i, |g i| ≤ 1)
    (hmem : cellCentre j z + siteOfCoords j h + siteOfCoords j g ∈ sitesOfCells S j) :
    enclosingCell (cellCentre j z + siteOfCoords j h + siteOfCoords j g : F.Site j) ∈ cellBall S z 1 := by
  classical
  obtain ⟨K, hK1, hK2, hK3⟩ := odd_pow_eq_two_mul_add_one hL (F.top - j)
  have hc := (mem_centredCube_iff _ _).1 hh
  rw [hK2] at hc
  set a : Lattice4 := fun i => if h i + g i > K then 1 else if h i + g i < -(K : ℤ) then -1 else 0 with ha
  set M : ℤ := (F.blockSide : ℤ) ^ (F.top - j) with hM
  set h' : Lattice4 := fun i => h i + g i - M * a i with hh'
  have hcube : h' ∈ centredCube (F.blockSide ^ (F.top - j)) := by
    refine (mem_centredCube_iff _ _).2 fun i => ?_
    rw [hK2]
    have h1 := hc i
    have h2 := abs_le.1 (hg i)
    simp only [hh', ha]
    split_ifs with c1 c2
    · rw [hK3] at *
      constructor <;> omega
    · rw [hK3] at *
      constructor <;> omega
    · constructor <;> omega
  have e : cellCentre j z + siteOfCoords j h + siteOfCoords j g =
      cellCentre j (z + siteOfCoords F.top a) + siteOfCoords j h' := by
    rw [cellCentre_add j hj, add_assoc, add_assoc, ← BlockAverages.siteOfCoords_add,
      ← BlockAverages.siteOfCoords_add]
    congr 2
    funext i
    simp only [Pi.add_apply, hh']
    ring
  have hcell : enclosingCell (cellCentre j z + siteOfCoords j h + siteOfCoords j g : F.Site j) =
      z + siteOfCoords F.top a := by
    rw [e, enclosingCell_cellCentre_add hL _ _ hcube]
  refine Finset.mem_filter.2 ⟨enclosingCell_mem hL hmem, ?_⟩
  rw [hcell, cellSupDist_comm]
  refine cellSupDist_add_le hamb z (by norm_num) fun i => ?_
  simp only [ha]
  split_ifs <;> simp
theorem add_mem_sitesOfCells_cellBall (hamb : IsAdmissibleAmbient F) (hL : Odd F.blockSide)
    {S : Finset F.Cell} {z : F.Cell}
    {x : F.Site 0} (hx : x ∈ sitesOfCells S 0) (hcell : enclosingCell x = z) {g : Lattice4}
    (hg : ∀ i, |g i| ≤ 1)
    (hmem : x + siteOfCoords 0 g ∈ sitesOfCells S 0) :
    x + siteOfCoords 0 g ∈ sitesOfCells (cellBall S z 1) 0 := by
  obtain ⟨y, hy, h, hh, hxe⟩ := mem_sitesOfCells.1 hx
  have hyz : y = z := by
    rw [← hcell, hxe, enclosingCell_cellCentre_add hL y h hh]
  subst hyz
  refine mem_sitesOfCells_of_enclosingCell_mem hL hmem ?_
  rw [hxe] at hmem ⊢
  exact enclosingCell_shift_mem_cellBall hamb hL (Nat.zero_le _) hh hg hmem
theorem abs_basisVector_le_one (i l : Fin 4) : |basisVector i l| ≤ 1 := by apply _root_.YangMills.Construction.BlockAverages.PatchLocality.abs_basisVector_le <;> assumption
theorem plaquette_bonds_mem_innerBonds (hamb : IsAdmissibleAmbient F) (hL : Odd F.blockSide)
    {S : Finset F.Cell} {z : F.Cell}
    {q : F.Site 0 × Fin 4 × Fin 4} (hq : q ∈ plaquettesOver S {z} 0) :
    (q.1, q.2.1) ∈ innerBonds (cellBall S z 1) 0 ∧
      (q.1 + unitStep 0 q.2.1, q.2.2) ∈ innerBonds (cellBall S z 1) 0 ∧
      (q.1 + unitStep 0 q.2.2, q.2.1) ∈ innerBonds (cellBall S z 1) 0 ∧
      (q.1, q.2.2) ∈ innerBonds (cellBall S z 1) 0 := by
  classical
  obtain ⟨hqS, hcell⟩ := Finset.mem_filter.1 hq
  have hcz : enclosingCell q.1 = z := Finset.mem_singleton.1 hcell
  obtain ⟨hq1, hq2⟩ := Finset.mem_filter.1 hqS
  have hc := hq2.2
  have h0 : q.1 ∈ sitesOfCells S 0 := hc (by simp [plaquetteCorners])
  have h1 : q.1 + unitStep 0 q.2.1 ∈ sitesOfCells S 0 := hc (by simp [plaquetteCorners])
  have h2 : q.1 + unitStep 0 q.2.2 ∈ sitesOfCells S 0 := hc (by simp [plaquetteCorners])
  have h3 : q.1 + unitStep 0 q.2.1 + unitStep 0 q.2.2 ∈ sitesOfCells S 0 :=
    hc (by simp [plaquetteCorners])
  have hzero : q.1 ∈ sitesOfCells (cellBall S z 1) 0 := by
    have := add_mem_sitesOfCells_cellBall hamb hL h0 hcz (g := 0) (by simp)
      (by simpa [siteOfCoords_zero] using h0)
    simpa [siteOfCoords_zero] using this
  have hA : q.1 + unitStep 0 q.2.1 ∈ sitesOfCells (cellBall S z 1) 0 :=
    add_mem_sitesOfCells_cellBall hamb hL h0 hcz (g := basisVector q.2.1) (abs_basisVector_le_one _) h1
  have hB : q.1 + unitStep 0 q.2.2 ∈ sitesOfCells (cellBall S z 1) 0 :=
    add_mem_sitesOfCells_cellBall hamb hL h0 hcz (g := basisVector q.2.2) (abs_basisVector_le_one _) h2
  have hne : q.2.1 ≠ q.2.2 := hq2.1.ne
  have hC : q.1 + unitStep 0 q.2.1 + unitStep 0 q.2.2 ∈ sitesOfCells (cellBall S z 1) 0 := by
    have e : q.1 + unitStep 0 q.2.1 + unitStep 0 q.2.2 =
        q.1 + siteOfCoords 0 (basisVector q.2.1 + basisVector q.2.2) := by
      rw [BlockAverages.siteOfCoords_add, add_assoc]
      rfl
    rw [e] at h3 ⊢
    refine add_mem_sitesOfCells_cellBall hamb hL h0 hcz (fun l => ?_) h3
    simp only [Pi.add_apply]
    by_cases a1 : l = q.2.1
    · subst a1
      simp [basisVector, hne]
    · by_cases a2 : l = q.2.2
      · subst a2
        simp [basisVector, a1]
      · simp [basisVector, a1, a2]
  have hC' : q.1 + unitStep 0 q.2.2 + unitStep 0 q.2.1 ∈ sitesOfCells (cellBall S z 1) 0 := by
    have e : q.1 + unitStep 0 q.2.2 + unitStep 0 q.2.1 = q.1 + unitStep 0 q.2.1 + unitStep 0 q.2.2 := by
      abel
    rw [e]
    exact hC
  simp only [innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
  exact ⟨⟨hzero, hA⟩, ⟨hA, hC⟩, ⟨hB, hC'⟩, ⟨hzero, hB⟩⟩
section Weights
theorem baseSite_zero (x : F.Site 0) : baseSite x = x := by apply _root_.YangMills.Construction.CellBumps.baseSite_zero <;> assumption
theorem baseDistance_add_unitStep (x : F.Site 0) (k : Fin 4) (p : F.Site 0) :
    baseDistance (x + unitStep 0 k) p ≤ baseDistance x p + 1 ∧
      baseDistance x p ≤ baseDistance (x + unitStep 0 k) p + 1 := by
  have hc : ∀ i, (((basisVector k i : ℤ) : ZMod (F.period 0 i)).valMinAbs).natAbs ≤ 1 := fun i =>
    (natAbs_valMinAbs_intCast_le _ _).trans (by
      have := abs_le.1 (abs_basisVector_le_one k i)
      omega)
  have hc' : ∀ i, (((-(basisVector k i) : ℤ) : ZMod (F.period 0 i)).valMinAbs).natAbs ≤ 1 := fun i =>
    (natAbs_valMinAbs_intCast_le _ _).trans (by
      have := abs_le.1 (abs_basisVector_le_one k i)
      omega)
  have hx : ∀ i, (baseSite (x + unitStep 0 k) - p : F.Site 0) i =
      (baseSite x - p : F.Site 0) i + ((basisVector k i : ℤ) : ZMod (F.period 0 i)) := by
    intro i
    simp only [baseSite_zero, Pi.sub_apply, Pi.add_apply, unitStep_eq]
    simp only [siteOfCoords]
    ring
  constructor
  · refine Finset.sup_le fun i _ => ?_
    rw [hx]
    refine (natAbs_valMinAbs_add_le _ _ _).trans ?_
    have h1 := natAbs_le_baseDistance x p i
    have h2 := hc i
    omega
  · refine Finset.sup_le fun i _ => ?_
    have hy : (baseSite x - p : F.Site 0) i = (baseSite (x + unitStep 0 k) - p : F.Site 0) i +
        ((-(basisVector k i) : ℤ) : ZMod (F.period 0 i)) := by
      rw [hx]
      push_cast
      ring
    rw [hy]
    refine (natAbs_valMinAbs_add_le _ _ _).trans ?_
    have h1 := natAbs_le_baseDistance (x + unitStep 0 k) p i
    have h2 := hc' i
    omega
theorem scaleRadius_le_two_mul (hodd : Odd F.blockSide) {x y : F.Site 0} {p : F.Site 0}
    (h : baseDistance y p ≤ baseDistance x p + 1) : scaleRadius F 0 p y ≤ 2 * scaleRadius F 0 p x := by
  have hL1 : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  have hd : ((baseDistance y p : ℕ) : ℝ) ≤ baseDistance x p + 1 := by exact_mod_cast h
  simp only [scaleRadius, pow_zero]
  set N : ℝ := (F.blockSide : ℝ) ^ F.top with hN
  have hN0 : 0 < N := by positivity
  set dx : ℝ := ((baseDistance x p : ℕ) : ℝ) with hdx
  set dy : ℝ := ((baseDistance y p : ℕ) : ℝ) with hdy
  set m := max 1 dx with hm
  have hm1 : 1 ≤ m := le_max_left _ _
  have hmx : dx ≤ m := le_max_right _ _
  rcases le_total N m with h1 | h1
  · rw [min_eq_left h1]
    have : min N (max 1 dy) ≤ N := min_le_left _ _
    linarith
  · rw [min_eq_right h1]
    have h3 : min N (max 1 dy) ≤ max 1 dy := min_le_right _ _
    have h4 : max 1 dy ≤ 2 * m := max_le (by linarith) (by linarith)
    linarith
theorem scaleWeight_le_two_mul_add_unitStep (hodd : Odd F.blockSide) {θ : ℝ} (hθ : |θ| ≤ 1 / 8)
    (x : F.Site 0) (k : Fin 4) (p : F.Site 0) :
    scaleWeight p θ 0 x ≤ 2 * scaleWeight p θ 0 (x + unitStep 0 k) := by
  obtain ⟨a, b⟩ := baseDistance_add_unitStep x k p
  have h1 := scaleRadius_le_two_mul (F := F) hodd a
  have h2 := scaleRadius_le_two_mul (F := F) hodd b
  set ρ₁ := scaleRadius F 0 p x with hρ₁
  set ρ₀ := scaleRadius F 0 p (x + unitStep 0 k) with hρ₀
  have p₁ : 0 < ρ₁ := scaleRadius_pos hodd.pos _ _ _
  have p₀ : 0 < ρ₀ := scaleRadius_pos hodd.pos _ _ _
  have hθ1 := abs_le.1 hθ
  have key : ρ₁ ^ (-θ) = (ρ₀ / ρ₁) ^ θ * ρ₀ ^ (-θ) := by
    rw [Real.div_rpow p₀.le p₁.le, Real.rpow_neg p₁.le, Real.rpow_neg p₀.le]
    have a1 : ρ₀ ^ θ ≠ 0 := (Real.rpow_pos_of_pos p₀ _).ne'
    have a2 : ρ₁ ^ θ ≠ 0 := (Real.rpow_pos_of_pos p₁ _).ne'
    field_simp
  show ρ₁ ^ (-θ) ≤ 2 * ρ₀ ^ (-θ)
  rw [key]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg p₀.le _)
  rcases le_total 0 θ with h | h
  · have h3 : ρ₀ / ρ₁ ≤ 2 := by
      rw [div_le_iff₀ p₁]
      exact h1
    have h4 : (ρ₀ / ρ₁) ^ θ ≤ (2 : ℝ) ^ θ := Real.rpow_le_rpow (by positivity) h3 h
    have h5 : (2 : ℝ) ^ θ ≤ 2 := by
      have := Real.rpow_le_rpow_of_exponent_le (x := 2) (by norm_num) (by linarith : θ ≤ 1)
      simpa using this
    linarith
  · have h3 : ρ₁ / ρ₀ ≤ 2 := by
      rw [div_le_iff₀ p₀]
      exact h2
    have e : (ρ₀ / ρ₁) ^ θ = (ρ₁ / ρ₀) ^ (-θ) := by
      rw [Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity), inv_div]
    rw [e]
    have h4 : (ρ₁ / ρ₀) ^ (-θ) ≤ (2 : ℝ) ^ (-θ) := Real.rpow_le_rpow (by positivity) h3 (by linarith)
    have h5 : (2 : ℝ) ^ (-θ) ≤ 2 := by
      have := Real.rpow_le_rpow_of_exponent_le (x := 2) (by norm_num) (by linarith : -θ ≤ 1)
      simpa using this
    linarith
end Weights
section Sum
variable {S : Finset F.Cell} {z : F.Cell}
theorem sum_comp_bond_le {D : Finset F.Cell} (Pz : Finset (F.Site 0 × Fin 4 × Fin 4))
    (φ : F.Site 0 × Fin 4 × Fin 4 → F.Site 0 × Fin 4) (hinj : ∀ q q', q.2 = q'.2 → φ q = φ q' → q = q')
    (hmap : ∀ q ∈ Pz, φ q ∈ innerBonds D 0) (g : F.Site 0 × Fin 4 → ℝ) (hg : ∀ b, 0 ≤ g b) :
    ∑ q ∈ Pz, g (φ q) ≤ 16 * ∑ b ∈ innerBonds D 0, g b := by
  classical
  rw [← Finset.sum_fiberwise (s := Pz) (g := fun q => q.2) (f := fun q => g (φ q))]
  refine (Finset.sum_le_card_nsmul _ _ (∑ b ∈ innerBonds D 0, g b) fun κ _ => ?_).trans ?_
  · refine sum_comp_le_of_injOn _ _ φ (fun q hq q' hq' e => ?_)
      (fun q hq => hmap q (Finset.mem_filter.1 hq).1) g hg
    have a := (Finset.mem_filter.1 (Finset.mem_coe.1 hq)).2
    have b := (Finset.mem_filter.1 (Finset.mem_coe.1 hq')).2
    exact hinj q q' (a.trans b.symm) e
  · simp
theorem finsetLpNorm_bondTerm_le (hodd : Odd F.blockSide) {D : Finset F.Cell} (p : F.Site 0) {θ : ℝ}
    (P : ℕ) (hP : 1 ≤ P)
    (Pz : Finset (F.Site 0 × Fin 4 × Fin 4)) (e : F.Site 0 → Fin 4 → ComplexQuat)
    (φ : F.Site 0 × Fin 4 × Fin 4 → F.Site 0 × Fin 4) (hinj : ∀ q q', q.2 = q'.2 → φ q = φ q' → q = q')
    (hmap : ∀ q ∈ Pz, φ q ∈ innerBonds D 0)
    (hw : ∀ q ∈ Pz, scaleWeight p θ 0 q.1 ≤ 2 * scaleWeight p θ 0 (φ q).1) :
    finsetLpNorm P Pz (fun q => scaleWeight p θ 0 q.1 * ‖e (φ q).1 (φ q).2‖) ≤
      32 * weightedScaleNorm D p θ P 0 (fun x i => ‖e x i‖) := by
  refine finsetLpNorm_le_of_sum_pow_le hP _ _ _ _ (by norm_num) ?_
  set g : F.Site 0 × Fin 4 → ℝ := fun b => |scaleWeight p θ 0 b.1 * ‖e b.1 b.2‖| ^ P with hg
  have hg0 : ∀ b, 0 ≤ g b := fun b => by
    simp only [hg]
    positivity
  have h1 : ∑ q ∈ Pz, |scaleWeight p θ 0 q.1 * ‖e (φ q).1 (φ q).2‖| ^ P ≤ ∑ q ∈ Pz, 2 ^ P * g (φ q) := by
    refine Finset.sum_le_sum fun q hq => ?_
    have hv := scaleWeight_pos hodd p θ 0 q.1
    have hv' := scaleWeight_pos hodd p θ 0 (φ q).1
    simp only [hg]
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity), ← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ P
    have := mul_le_mul_of_nonneg_right (hw q hq) (norm_nonneg (e (φ q).1 (φ q).2))
    linarith
  refine h1.trans ?_
  rw [← Finset.mul_sum]
  have h2 := sum_comp_bond_le Pz φ hinj hmap g hg0
  have h3 : (2 : ℝ) ^ P * (16 * ∑ b ∈ innerBonds D 0, g b) ≤ 32 ^ P * ∑ b ∈ innerBonds D 0, g b := by
    have e1 : (32 : ℝ) ^ P = 2 ^ P * 16 ^ P := by
      rw [← mul_pow]
      norm_num
    have e2 : (16 : ℝ) ≤ 16 ^ P := by
      calc (16 : ℝ) = 16 ^ 1 := by norm_num
        _ ≤ 16 ^ P := pow_le_pow_right₀ (by norm_num) hP
    have h4 : 0 ≤ ∑ b ∈ innerBonds D 0, g b := Finset.sum_nonneg fun b _ => hg0 b
    rw [e1, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right e2 h4) (by positivity)
  refine (mul_le_mul_of_nonneg_left h2 (by positivity)).trans h3
theorem finsetLpNorm_plaquetteSourceNorm_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (p : F.Site 0) {θ : ℝ} (hθ : |θ| ≤ 1 / 8) (P : ℕ) (hP : 1 ≤ P)
    (e : F.Site 0 → Fin 4 → ComplexQuat) :
    finsetLpNorm P (plaquettesOver S {z} 0) (fun q => scaleWeight p θ 0 q.1 * plaquetteSourceNorm q e) ≤
      128 * weightedScaleNorm (cellBall S z 1) p θ P 0 (fun x i => ‖e x i‖) := by
  set Pz := plaquettesOver S {z} 0 with hPz
  have hb : ∀ q ∈ Pz, _ := fun q hq => plaquette_bonds_mem_innerBonds hamb hodd (S := S) (z := z) (q := q) hq
  have t1 := finsetLpNorm_bondTerm_le hodd (D := cellBall S z 1) p (θ := θ) P hP Pz e (fun q => (q.1, q.2.1))
    (fun q q' h2 e1 => Prod.ext (Prod.ext_iff.1 e1).1 h2) (fun q hq => (hb q hq).1)
    (fun q _ => by
      have := scaleWeight_pos hodd p θ 0 q.1
      simp only
      linarith)
  have t4 := finsetLpNorm_bondTerm_le hodd (D := cellBall S z 1) p (θ := θ) P hP Pz e (fun q => (q.1, q.2.2))
    (fun q q' h2 e1 => Prod.ext (Prod.ext_iff.1 e1).1 h2) (fun q hq => (hb q hq).2.2.2)
    (fun q _ => by
      have := scaleWeight_pos hodd p θ 0 q.1
      simp only
      linarith)
  have t2 := finsetLpNorm_bondTerm_le hodd (D := cellBall S z 1) p (θ := θ) P hP Pz e
    (fun q => (q.1 + unitStep 0 q.2.1, q.2.2))
    (fun q q' h2 e1 => by
      have e2 : q.1 + unitStep 0 q.2.1 = q'.1 + unitStep 0 q'.2.1 := congrArg Prod.fst e1
      rw [h2] at e2
      exact Prod.ext (add_right_cancel e2) h2) (fun q hq => (hb q hq).2.1)
    (fun q _ => scaleWeight_le_two_mul_add_unitStep hodd hθ q.1 q.2.1 p)
  have t3 := finsetLpNorm_bondTerm_le hodd (D := cellBall S z 1) p (θ := θ) P hP Pz e
    (fun q => (q.1 + unitStep 0 q.2.2, q.2.1))
    (fun q q' h2 e1 => by
      have e2 : q.1 + unitStep 0 q.2.2 = q'.1 + unitStep 0 q'.2.2 := congrArg Prod.fst e1
      rw [h2] at e2
      exact Prod.ext (add_right_cancel e2) h2) (fun q hq => (hb q hq).2.2.1)
    (fun q _ => scaleWeight_le_two_mul_add_unitStep hodd hθ q.1 q.2.2 p)
  have a1 := finsetLpNorm_add_le hP Pz (fun q => scaleWeight p θ 0 q.1 * ‖e q.1 q.2.1‖ +
      scaleWeight p θ 0 q.1 * ‖e (q.1 + unitStep 0 q.2.1) q.2.2‖ +
      scaleWeight p θ 0 q.1 * ‖e (q.1 + unitStep 0 q.2.2) q.2.1‖)
    (fun q => scaleWeight p θ 0 q.1 * ‖e q.1 q.2.2‖)
  have a2 := finsetLpNorm_add_le hP Pz (fun q => scaleWeight p θ 0 q.1 * ‖e q.1 q.2.1‖ +
      scaleWeight p θ 0 q.1 * ‖e (q.1 + unitStep 0 q.2.1) q.2.2‖)
    (fun q => scaleWeight p θ 0 q.1 * ‖e (q.1 + unitStep 0 q.2.2) q.2.1‖)
  have a3 := finsetLpNorm_add_le hP Pz (fun q => scaleWeight p θ 0 q.1 * ‖e q.1 q.2.1‖)
    (fun q => scaleWeight p θ 0 q.1 * ‖e (q.1 + unitStep 0 q.2.1) q.2.2‖)
  have e3 : (fun q : F.Site 0 × Fin 4 × Fin 4 => scaleWeight p θ 0 q.1 * plaquetteSourceNorm q e) =
      fun q => scaleWeight p θ 0 q.1 * ‖e q.1 q.2.1‖ +
        scaleWeight p θ 0 q.1 * ‖e (q.1 + unitStep 0 q.2.1) q.2.2‖ +
        scaleWeight p θ 0 q.1 * ‖e (q.1 + unitStep 0 q.2.2) q.2.1‖ + scaleWeight p θ 0 q.1 * ‖e q.1 q.2.2‖ := by
    funext q
    unfold plaquetteSourceNorm
    ring
  rw [e3]
  simp only at t1 t2 t3 t4
  linarith
end Sum
section PlaquetteSum
variable {S : Finset F.Cell} {z : F.Cell}
theorem weighted_product_identity (c1 c2 n1 n2 L Y w w' : ℝ) (h : w * w' = 1) :
    (c1 + L * n1) * (c2 + L * n2) + 64 * 173 * n1 * n2 * (4 * Y) =
      (w * c1 + L * (w * n1)) * (w' * c2 + L * (w' * n2)) + 44288 * (((w * n1) * (w' * n2)) * Y) := by
  have e1 : (w * c1 + L * (w * n1)) * (w' * c2 + L * (w' * n2)) =
      (w * w') * ((c1 + L * n1) * (c2 + L * n2)) := by ring
  have e2 : ((w * n1) * (w' * n2)) * Y = (w * w') * (n1 * n2 * Y) := by ring
  rw [e1, e2, h]
  ring
theorem le_weighted_product {T c1 c2 n1 n2 L Y w w' : ℝ} (h : w * w' = 1)
    (hb : T ≤ (c1 + L * n1) * (c2 + L * n2) + 64 * 173 * n1 * n2 * (4 * Y)) :
    T ≤ (w * c1 + L * (w * n1)) * (w' * c2 + L * (w' * n2)) + 44288 * (((w * n1) * (w' * n2)) * Y) := by
  rw [← weighted_product_identity c1 c2 n1 n2 L Y w w' h]
  exact hb
set_option maxHeartbeats 1000000 in
theorem norm_complexPlaquetteTerm_second_diff_le_weighted (hodd : Odd F.blockSide) (R : F.GaugeField 0)
    {ξ e₁ e₂ : F.Site 0 → Fin 4 → ComplexQuat} {σ : ℝ} {q : F.Site 0 × Fin 4 × Fin 4}
    (hσ0 : 0 < σ) (hσ : ‖ofUnit (basePlaquetteHolonomy R q) - 1‖ ≤ σ) (p : F.Site 0) (θ : ℝ)
    (hsm : 24 * (3 * (plaquetteSourceNorm q ξ + plaquetteSourceNorm q e₁ + plaquetteSourceNorm q e₂) + σ) <
      1 / 256) :
    ‖complexPlaquetteTerm (expField R (ξ + e₁ + e₂)) q - complexPlaquetteTerm (expField R (ξ + e₁)) q -
      complexPlaquetteTerm (expField R (ξ + e₂)) q + complexPlaquetteTerm (expField R ξ) q‖ ≤
    (scaleWeight p θ 0 q.1 * ‖covariantCurl R q e₁‖ +
        12 * 173 * (3 * (plaquetteSourceNorm q ξ + plaquetteSourceNorm q e₁ + plaquetteSourceNorm q e₂) + σ) *
          (scaleWeight p θ 0 q.1 * plaquetteSourceNorm q e₁)) *
      (scaleWeight p (-θ) 0 q.1 * ‖covariantCurl R q e₂‖ +
        12 * 173 * (3 * (plaquetteSourceNorm q ξ + plaquetteSourceNorm q e₁ + plaquetteSourceNorm q e₂) + σ) *
          (scaleWeight p (-θ) 0 q.1 * plaquetteSourceNorm q e₂)) +
      44288 * (((scaleWeight p θ 0 q.1 * plaquetteSourceNorm q e₁) *
          (scaleWeight p (-θ) 0 q.1 * plaquetteSourceNorm q e₂)) *
        (‖plaquetteGap R q ξ‖ + ‖plaquetteGap R q (ξ + e₁)‖ + ‖plaquetteGap R q (ξ + e₂)‖ +
          ‖plaquetteGap R q (ξ + e₁ + e₂)‖)) := by
  have a0 := plaquetteSourceNorm_nonneg q ξ
  have a1 := plaquetteSourceNorm_nonneg q e₁
  have a2 := plaquetteSourceNorm_nonneg q e₂
  have hb := norm_complexPlaquetteTerm_second_diff_le R q
    (t := plaquetteSourceNorm q ξ + plaquetteSourceNorm q e₁ + plaquetteSourceNorm q e₂) hσ0 hσ
    (add_nonneg (add_nonneg a0 a1) a2) hsm ((le_add_of_nonneg_right a1).trans (le_add_of_nonneg_right a2))
    ((le_add_of_nonneg_left a0).trans (le_add_of_nonneg_right a2)) (le_add_of_nonneg_left (add_nonneg a0 a1))
  exact le_weighted_product (scaleWeight_mul_scaleWeight_neg hodd p θ 0 q.1) hb
set_option maxHeartbeats 1000000 in
theorem sum_norm_complexPlaquetteTerm_second_diff_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (R : F.GaugeField 0) {ξ e₁ e₂ : F.Site 0 → Fin 4 → ComplexQuat} {σ : ℝ}
    (hσ0 : 0 < σ) (hσ : ∀ q ∈ plaquettesOver S {z} 0, ‖ofUnit (basePlaquetteHolonomy R q) - 1‖ ≤ σ)
    (p : F.Site 0) {θ : ℝ}
    (hθ : |θ| ≤ 1 / 8)
    (hsm : ∀ q ∈ plaquettesOver S {z} 0,
      24 * (3 * (plaquetteSourceNorm q ξ + plaquetteSourceNorm q e₁ + plaquetteSourceNorm q e₂) + σ) <
        1 / 256) :
    ∑ q ∈ plaquettesOver S {z} 0,
        ‖complexPlaquetteTerm (expField R (ξ + e₁ + e₂)) q - complexPlaquetteTerm (expField R (ξ + e₁)) q -
          complexPlaquetteTerm (expField R (ξ + e₂)) q + complexPlaquetteTerm (expField R ξ) q‖ ≤
      (finsetLpNorm 2 (plaquettesOver S {z} 0) (fun q => scaleWeight p θ 0 q.1 * ‖covariantCurl R q e₁‖) +
          finsetLpNorm 4 (plaquettesOver S {z} 0)
              (fun q => 12 * 173 *
                (3 * (plaquetteSourceNorm q ξ + plaquetteSourceNorm q e₁ + plaquetteSourceNorm q e₂) + σ)) *
            (128 * weightedScaleNorm (cellBall S z 1) p θ 4 0 (fun x i => ‖e₁ x i‖))) *
        (finsetLpNorm 2 (plaquettesOver S {z} 0) (fun q => scaleWeight p (-θ) 0 q.1 * ‖covariantCurl R q e₂‖) +
          finsetLpNorm 4 (plaquettesOver S {z} 0)
              (fun q => 12 * 173 *
                (3 * (plaquetteSourceNorm q ξ + plaquetteSourceNorm q e₁ + plaquetteSourceNorm q e₂) + σ)) *
            (128 * weightedScaleNorm (cellBall S z 1) p (-θ) 4 0 (fun x i => ‖e₂ x i‖))) +
      44288 * ((128 * weightedScaleNorm (cellBall S z 1) p θ 4 0 (fun x i => ‖e₁ x i‖)) *
          (128 * weightedScaleNorm (cellBall S z 1) p (-θ) 4 0 (fun x i => ‖e₂ x i‖))) *
        finsetLpNorm 2 (plaquettesOver S {z} 0) (fun q => ‖plaquetteGap R q ξ‖ + ‖plaquetteGap R q (ξ + e₁)‖ +
          ‖plaquetteGap R q (ξ + e₂)‖ + ‖plaquetteGap R q (ξ + e₁ + e₂)‖) := by
  set Pz := plaquettesOver S {z} 0 with hPz
  have hθ' : |(-θ)| ≤ 1 / 8 := by rwa [abs_neg]
  have hpt := fun q (hq : q ∈ Pz) => norm_complexPlaquetteTerm_second_diff_le_weighted hodd R
    (ξ := ξ) (e₁ := e₁) (e₂ := e₂) hσ0 (hσ q hq) p θ (hsm q hq)
  set v : F.Site 0 × Fin 4 × Fin 4 → ℝ := fun q => scaleWeight p θ 0 q.1 with hv
  set v' : F.Site 0 × Fin 4 × Fin 4 → ℝ := fun q => scaleWeight p (-θ) 0 q.1 with hv'
  set Lp : F.Site 0 × Fin 4 × Fin 4 → ℝ :=
    fun q => 12 * 173 * (3 * (plaquetteSourceNorm q ξ + plaquetteSourceNorm q e₁ + plaquetteSourceNorm q e₂) + σ)
      with hLp
  set Ys : F.Site 0 × Fin 4 × Fin 4 → ℝ := fun q => ‖plaquetteGap R q ξ‖ + ‖plaquetteGap R q (ξ + e₁)‖ +
    ‖plaquetteGap R q (ξ + e₂)‖ + ‖plaquetteGap R q (ξ + e₁ + e₂)‖ with hYs
  set n₁ : F.Site 0 × Fin 4 × Fin 4 → ℝ := fun q => v q * plaquetteSourceNorm q e₁ with hn₁
  set n₂ : F.Site 0 × Fin 4 × Fin 4 → ℝ := fun q => v' q * plaquetteSourceNorm q e₂ with hn₂
  set c₁ : F.Site 0 × Fin 4 × Fin 4 → ℝ := fun q => v q * ‖covariantCurl R q e₁‖ with hc₁
  set c₂ : F.Site 0 × Fin 4 × Fin 4 → ℝ := fun q => v' q * ‖covariantCurl R q e₂‖ with hc₂
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have l1 := finsetLpNorm_plaquetteSourceNorm_le (S := S) (z := z) hamb hodd p hθ 4 (by norm_num) e₁
  have l2 := finsetLpNorm_plaquetteSourceNorm_le (S := S) (z := z) hamb hodd p hθ' 4 (by norm_num) e₂
  rw [← hPz] at l1 l2
  set U₁ := 128 * weightedScaleNorm (cellBall S z 1) p θ 4 0 (fun x i => ‖e₁ x i‖) with hU₁
  set U₂ := 128 * weightedScaleNorm (cellBall S z 1) p (-θ) 4 0 (fun x i => ‖e₂ x i‖) with hU₂
  have nU₁ : finsetLpNorm 4 Pz n₁ ≤ U₁ := l1
  have nU₂ : finsetLpNorm 4 Pz n₂ ≤ U₂ := l2
  have hL0 := finsetLpNorm_nonneg 4 Pz Lp
  have hs1 := sum_mul_le_finsetLpNorm_two_mul Pz (fun q => c₁ q + Lp q * n₁ q) (fun q => c₂ q + Lp q * n₂ q)
  have m1 : finsetLpNorm 2 Pz (fun q => c₁ q + Lp q * n₁ q) ≤ finsetLpNorm 2 Pz c₁ + finsetLpNorm 4 Pz Lp * U₁ := by
    refine (finsetLpNorm_add_le (by norm_num) Pz _ _).trans (add_le_add le_rfl ?_)
    exact (finsetLpNorm_two_mul_le Pz Lp n₁).trans (mul_le_mul_of_nonneg_left nU₁ hL0)
  have m2 : finsetLpNorm 2 Pz (fun q => c₂ q + Lp q * n₂ q) ≤ finsetLpNorm 2 Pz c₂ + finsetLpNorm 4 Pz Lp * U₂ := by
    refine (finsetLpNorm_add_le (by norm_num) Pz _ _).trans (add_le_add le_rfl ?_)
    exact (finsetLpNorm_two_mul_le Pz Lp n₂).trans (mul_le_mul_of_nonneg_left nU₂ hL0)
  have m3 := mul_le_mul m1 m2 (finsetLpNorm_nonneg _ _ _) (add_nonneg (finsetLpNorm_nonneg _ _ _)
    (mul_nonneg hL0 ((finsetLpNorm_nonneg _ _ _).trans nU₁)))
  have hs2 := sum_mul_le_finsetLpNorm_two_mul Pz (fun q => n₁ q * n₂ q) Ys
  have m4 : finsetLpNorm 2 Pz (fun q => n₁ q * n₂ q) ≤ U₁ * U₂ :=
    (finsetLpNorm_two_mul_le Pz n₁ n₂).trans
      (mul_le_mul nU₁ nU₂ (finsetLpNorm_nonneg _ _ _) ((finsetLpNorm_nonneg _ _ _).trans nU₁))
  have m5 : finsetLpNorm 2 Pz (fun q => n₁ q * n₂ q) * finsetLpNorm 2 Pz Ys ≤ U₁ * U₂ * finsetLpNorm 2 Pz Ys :=
    mul_le_mul_of_nonneg_right m4 (finsetLpNorm_nonneg _ _ _)
  have m6 := mul_le_mul_of_nonneg_left (hs2.trans m5) (by norm_num : (0 : ℝ) ≤ 44288)
  have e3 : 44288 * (U₁ * U₂) * finsetLpNorm 2 Pz Ys = 44288 * (U₁ * U₂ * finsetLpNorm 2 Pz Ys) := by ring
  rw [e3]
  exact add_le_add (hs1.trans m3) m6
end PlaquetteSum
end YangMills.Construction.PlaquettesNearCell
end
