import YangMills.Construction.RunningCouplingSlope.PlainAverageAlongComplexCurvesProof
import YangMills.Construction.RunningCouplingSlope.PlainAverageNearOneOnTheWhole
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.FullLattice
namespace NearIdentity
open Tower Tower.FullSpace Matrix
section Bounds
variable {ι : Type*}
private theorem norm_list_prod_sub_one_le (U : ι → Matrices.ComplexMatrix2) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (h : ∀ b, ‖U b - 1‖ ≤ ρ) (l : List ι) : ‖(l.map U).prod - 1‖ ≤ (1 + ρ) ^ l.length - 1 := by apply _root_.YangMills.Construction.RunningCouplingSlope.ContourMeanDerivative.norm_list_prod_sub_one_le <;> assumption
private theorem norm_apply_le_norm (A : Matrices.ComplexMatrix2) (a b : Fin 2) : ‖A a b‖ ≤ ‖A‖ := by apply _root_.YangMills.SharedProofs.p14523 <;> assumption
private theorem one_add_div_pow_sub_one_le {N : ℕ} (hN : 0 < N) {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1) :
    (1 + η / (2 * N)) ^ N - 1 ≤ η := by
  set x : ℝ := η / (2 * N) with hx
  have hNx : (N : ℝ) * x = η / 2 := by
    rw [hx]
    field_simp
  have e1 : (1 + x) ^ N ≤ Real.exp (η / 2) := by
    have h2 : 1 + x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
    calc (1 + x) ^ N ≤ Real.exp x ^ N := by gcongr
      _ = Real.exp (η / 2) := by rw [← Real.exp_nat_mul, hNx]
  have e2 : Real.exp (η / 2) ≤ 1 + η := by
    have h5 := Real.add_one_le_exp (-(η / 2))
    have h6 : Real.exp (η / 2) * Real.exp (-(η / 2)) = 1 := by
      rw [← Real.exp_add]
      simp
    have h7 := Real.exp_pos (η / 2)
    nlinarith
  linarith
end Bounds
section Scalars
private theorem sqrt_near_one (z : ℂ) (h : ‖z - 1‖ ≤ 1 / 10) :
    z ^ (1 / 2 : ℂ) ≠ 0 ∧ (z ^ (1 / 2 : ℂ)) ^ 2 = z ∧ ‖z ^ (1 / 2 : ℂ) - 1‖ ≤ ‖z - 1‖ ∧
      z ∈ Complex.slitPlane := by apply _root_.YangMills.Construction.RunningCouplingSlope.ContourMeanDerivative.sqrt_near_one <;> assumption
end Scalars
section Quaternions
private def IsQuaternionic (A : Matrices.ComplexMatrix2) : Prop := Matrix.adjugate A = Aᴴ
private theorem isQuaternionic_of_mem {g : Matrices.ComplexMatrix2}
    (hg : g ∈ Matrices.ComplexMatrix2.specialUnitary) : IsQuaternionic g := by
  rw [Matrix.mem_specialUnitaryGroup_iff] at hg
  obtain ⟨hu, hd⟩ := hg
  have h1 : star g * g = 1 := (Matrix.mem_unitaryGroup_iff').1 hu
  have h2 : g * Matrix.adjugate g = 1 := by
    rw [Matrix.mul_adjugate, hd, one_smul]
  have h3 : star g = Matrix.adjugate g := by
    calc star g = star g * (g * Matrix.adjugate g) := by rw [h2, mul_one]
      _ = Matrix.adjugate g := by rw [← mul_assoc, h1, one_mul]
  unfold IsQuaternionic
  rw [← h3]
  rfl
abbrev _root_.YangMills.DeltaSharedProofs.p2612 := @isQuaternionic_of_mem
private theorem isQuaternionic_add {A B : Matrices.ComplexMatrix2} (hA : IsQuaternionic A)
    (hB : IsQuaternionic B) : IsQuaternionic (A + B) := by
  unfold IsQuaternionic at *
  rw [Matrix.conjTranspose_add, ← hA, ← hB]
  simp only [Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring
abbrev _root_.YangMills.DeltaSharedProofs.p501936 := @isQuaternionic_add
private theorem isQuaternionic_smul (r : ℝ) {A : Matrices.ComplexMatrix2} (hA : IsQuaternionic A) :
    IsQuaternionic ((r : ℂ) • A) := by
  unfold IsQuaternionic at *
  rw [Matrix.conjTranspose_smul, ← hA]
  simp only [Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
abbrev _root_.YangMills.DeltaSharedProofs.p500416 := @isQuaternionic_smul
private theorem isQuaternionic_zero : IsQuaternionic 0 := by
  unfold IsQuaternionic
  simp only [Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
abbrev _root_.YangMills.DeltaSharedProofs.p502226 := @isQuaternionic_zero
private theorem isQuaternionic_sum {ι : Type*} (s : Finset ι) (f : ι → Matrices.ComplexMatrix2)
    (h : ∀ i ∈ s, IsQuaternionic (f i)) : IsQuaternionic (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isQuaternionic_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact isQuaternionic_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
abbrev _root_.YangMills.DeltaSharedProofs.p502446 := @isQuaternionic_sum
private theorem exists_det_eq_nonneg {A : Matrices.ComplexMatrix2} (hA : IsQuaternionic A) :
    ∃ d : ℝ, 0 ≤ d ∧ Matrix.det A = (d : ℂ) := by
  unfold IsQuaternionic at hA
  rw [Matrix.adjugate_fin_two] at hA
  have e11 : A 1 1 = star (A 0 0) := by
    have := congrFun (congrFun hA 0) 0
    simpa [Matrix.conjTranspose_apply] using this
  have e10 : A 1 0 = -star (A 0 1) := by
    have := congrFun (congrFun hA 1) 0
    have h : -A 1 0 = star (A 0 1) := by simpa [Matrix.conjTranspose_apply] using this
    rw [← h, neg_neg]
  refine ⟨Complex.normSq (A 0 0) + Complex.normSq (A 0 1),
    add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _), ?_⟩
  rw [Matrix.det_fin_two, e11, e10]
  simp only [Complex.star_def, Complex.ofReal_add, Complex.normSq_eq_conj_mul_self]
  ring
abbrev _root_.YangMills.DeltaSharedProofs.p501399 := @exists_det_eq_nonneg
private theorem inv_mem_specialUnitary {g : Matrices.ComplexMatrix2}
    (hg : g ∈ Matrices.ComplexMatrix2.specialUnitary) :
    g⁻¹ ∈ Matrices.ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.Tower.WilsonAnalyticity.inv_mem_specialUnitary <;> assumption
end Quaternions
section Main
variable {L k j : ℕ}
private theorem length_stepsInOrder {a' : ℝ} (d : Fin 4 → ℤ) (x : InfiniteLattice.LatticePoint a')
    (l : List (Fin 4)) :
    (stepsInOrder d x l).length = (l.map fun μ => (d μ).natAbs).sum := by apply _root_.YangMills.Construction.Tower.FullSpace.CubesAndPaths.length_stepsInOrder <;> assumption
private theorem inv_linkHolonomy {a : ℝ} (V : InfiniteLattice.Link a → Matrices.ComplexMatrix2)
    (hV : ∀ b, V b.opposite = (V b)⁻¹) (l : List (InfiniteLattice.Link a)) :
    (linkHolonomy V l)⁻¹ = linkHolonomy V ((l.map InfiniteLattice.Link.opposite).reverse) := by
  induction l with
  | nil =>
    have : (1 : Matrices.ComplexMatrix2)⁻¹ = 1 := Matrix.inv_eq_right_inv (mul_one 1)
    simpa [linkHolonomy] using this
  | cons b l ih =>
    simp only [linkHolonomy, List.map_cons, List.prod_cons, List.reverse_cons, List.map_append,
      List.prod_append, List.map_nil, List.prod_nil, mul_one, Matrix.mul_inv_rev, hV] at ih ⊢
    rw [ih]
private theorem linkHolonomy_mem {a : ℝ} (V : InfiniteLattice.Link a → Matrices.ComplexMatrix2)
    (hV : ∀ b, V b ∈ Matrices.ComplexMatrix2.specialUnitary) (l : List (InfiniteLattice.Link a)) :
    linkHolonomy V l ∈ Matrices.ComplexMatrix2.specialUnitary := by
  induction l with
  | nil => simpa [linkHolonomy] using Matrices.ComplexMatrix2.specialUnitary.one_mem
  | cons b l ih =>
    have e : linkHolonomy V (b :: l) = V b * linkHolonomy V l := by
      simp [linkHolonomy]
    rw [e]
    exact Matrices.ComplexMatrix2.specialUnitary.mul_mem (hV b) ih
abbrev _root_.YangMills.SharedProofs.p48031 := @linkHolonomy_mem
private theorem cubeVertices_finite_ncard (hZ : Tower.BlockPathContourPivotStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) (y : Vertex L k (j + 1)) :
    (cubeVertices L (meshAt L k j) y).Finite ∧
      (cubeVertices L (meshAt L k j) y).ncard = L ^ 4 := by
  have hT := (hZ L hL k 1 (j + 1) (by omega) (by omega) (by omega)).2.1
  have hLpos : 0 < L := by
    have := hL.2
    omega
  have hcard : (cube L (meshAt L k j) y).ncard = L ^ 4 := hT.ncard_eq y
  have hsub : cube L (meshAt L k j) y ⊆
      Set.range (Subtype.val : Vertex L k j → InfiniteLattice.AmbientSpace) := fun x hx => by
    have h1 : x ∈ (InfiniteLattice.latticeSubgroup (meshAt L k j) : Set InfiniteLattice.AmbientSpace) :=
      hT.subset_sublattice y hx
    exact ⟨⟨x, h1⟩, rfl⟩
  have hf : (cube L (meshAt L k j) y).Finite :=
    Set.finite_of_ncard_pos (by rw [hcard]; positivity)
  refine ⟨hf.preimage Subtype.val_injective.injOn, ?_⟩
  rw [← hcard]
  exact Set.ncard_preimage_of_injective_subset_range Subtype.val_injective hsub
private theorem length_contourLeg_le (y : Vertex L k (j + 1))
    (x : Vertex L k j) (hx : x ∈ cubeVertices L (meshAt L k j) y)
    (π : Equiv.Perm (Fin 4)) : (contourLeg y x π).length ≤ 2 * L := by
  obtain ⟨ν, hν, hxν⟩ := hx
  have hspec : IsCubeOffset L y x (cubeOffset L y x) :=
    Classical.epsilon_spec (p := IsCubeOffset L y x) ⟨ν, by rw [hxν]; simp, fun μ => by
      simpa using hν μ⟩
  rw [contourLeg, length_stepsInOrder]
  have hb1 : ∀ μ, ((cubeOffset L y x) μ).natAbs ≤ L / 2 := by
    intro μ
    have h3 := hspec.2 μ
    have h4 : (((cubeOffset L y x) μ).natAbs : ℤ) = |(cubeOffset L y x) μ| :=
      Int.natCast_natAbs _
    omega
  have h2 := List.sum_le_card_nsmul (((List.finRange 4).map π).map fun μ =>
    ((cubeOffset L y x) μ).natAbs) (L / 2) (by
      intro a ha
      obtain ⟨μ, -, rfl⟩ := List.mem_map.mp ha
      exact hb1 μ)
  simp only [List.length_map, List.length_finRange, smul_eq_mul] at h2
  omega
private theorem weight_eq_real (hL : 0 < L) :
    ((1 / 24 : ℂ) * PeriodicLattice.inverseFourthPowerWeight L) =
    ((1 / (24 * (L : ℝ) ^ 4) : ℝ) : ℂ) := by
  have hLC : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  rw [PeriodicLattice.inverseFourthPowerWeight]
  push_cast
  rw [_root_.zpow_neg]
  field_simp
abbrev _root_.YangMills.SharedProofs.p3617 := @weight_eq_real
private theorem estimates_near_identity (hZ : Tower.BlockPathContourPivotStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {η : ℝ} (hη0 : 0 < η) (hη : η ≤ 1 / 100)
    (hj : j < k) {V : Edge L k j → Matrices.ComplexMatrix2}
    (hV : V ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
    (hVρ : ∀ b, Matrices.ComplexMatrix2.operatorNorm (V b - 1) < η / (2 * ((5 * L : ℕ) : ℝ)))
    {c : Edge L k (j + 1)} (hc : c.IsPositivelyOriented) :
    Matrix.det (contourMean V c) ∈ Complex.slitPlane ∧ meanRadius V c ≠ 0 ∧
      Matrices.ComplexMatrix2.operatorNorm (normalizedMean V c - 1) ≤ 8 * η ∧
      normalizedMean V c ∈ PeriodicLattice.complexGaugeGroup := by
  have hLpos : 0 < L := by
    have := hL.2
    omega
  set ρ : ℝ := η / (2 * ((5 * L : ℕ) : ℝ)) with hρdef
  have h5L : 0 < 5 * L := by omega
  have hρ : 0 < ρ := by
    rw [hρdef]
    have : (0 : ℝ) < ((5 * L : ℕ) : ℝ) := by exact_mod_cast h5L
    positivity
  have hε : (1 + ρ) ^ (5 * L) - 1 ≤ η := one_add_div_pow_sub_one_le h5L hη0 (by linarith)
  obtain ⟨μ, hμ⟩ := hc
  have hT := (hZ L hL k 1 (j + 1) (by omega) (by omega) (by omega)).2.2.2.1
  obtain ⟨hfin, hncard⟩ := cubeVertices_finite_ncard hZ hL hj c.initial
  set S := hfin.toFinset with hSdef
  have hScard : S.card = L ^ 4 := by
    rw [← hncard]
    exact (Set.ncard_eq_toFinset_card _ hfin).symm
  set w : ℂ := (1 / 24 : ℂ) * PeriodicLattice.inverseFourthPowerWeight L with hw
  have hmean : ∀ U : Edge L k j → Matrices.ComplexMatrix2, contourMean U c =
      w • ∑ x ∈ S, ∑ π : Equiv.Perm (Fin 4), contourHolonomy U c x π := by
    intro U
    rw [contourMean, finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hrevV : ∀ b, V b.opposite = (V b)⁻¹ := fun b => hV.2 b
  have hcv : ∀ x ∈ S, ∀ π, ‖contourHolonomy V c x π - 1‖ ≤ (1 + ρ) ^ (5 * L) - 1 := by
    intro x hx π
    have hx1 : x ∈ cubeVertices L (meshAt L k j) c.initial := by simpa [hSdef] using hx
    have hx2 : shifted c x ∈ cubeVertices L (meshAt L k j) c.terminal := by
      show ((shifted c x : Vertex L k j) : InfiniteLattice.AmbientSpace) ∈
        cube L (meshAt L k j) c.terminal
      rw [hT.coe_shifted c x hx1]
      exact (hT.bijOn c).mapsTo hx1
    have hlen1 := length_contourLeg_le c.initial x hx1 π
    have hlen2 := length_contourLeg_le c.terminal (shifted c x) hx2 π
    have hlen3 : (crossingPath c x).length = L := by
      have e := hT.crossingPath_eq c μ hμ x hx1
      have e' : crossingPath c x = _ := e
      rw [e']
      simp
    set Γ := contourLeg c.initial x π ++ crossingPath c x ++
      ((contourLeg c.terminal (shifted c x) π).map InfiniteLattice.Link.opposite).reverse with hΓ
    have e : contourHolonomy V c x π = (Γ.map V).prod := by
      rw [contourHolonomy, inv_linkHolonomy V hrevV, hΓ]
      simp [linkHolonomy, List.map_append, List.prod_append, mul_assoc]
    have hlen : Γ.length ≤ 5 * L := by
      simp only [hΓ, List.length_append, List.length_reverse, List.length_map]
      omega
    rw [e]
    refine (norm_list_prod_sub_one_le V ρ hρ.le (fun b => (hVρ b).le) Γ).trans ?_
    have : (1 + ρ) ^ Γ.length ≤ (1 + ρ) ^ (5 * L) :=
      pow_le_pow_right₀ (by linarith) hlen
    linarith
  have hwval : w = (((1 / (24 * (L : ℝ) ^ 4) : ℝ)) : ℂ) := weight_eq_real hLpos
  have hwnorm : ‖w‖ = 1 / (24 * (L : ℝ) ^ 4) := by
    rw [hwval, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hcount : ∑ _x ∈ S, ∑ _π : Equiv.Perm (Fin 4), (1 : Matrices.ComplexMatrix2) =
      (((24 * (L : ℝ) ^ 4 : ℝ)) : ℂ) • (1 : Matrices.ComplexMatrix2) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, hScard]
    rw [← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    congr 1
    push_cast
    norm_num [Nat.factorial]
    ring
  have hone : w • ∑ _x ∈ S, ∑ _π : Equiv.Perm (Fin 4), (1 : Matrices.ComplexMatrix2) = 1 := by
    rw [hcount, smul_smul, hwval, ← Complex.ofReal_mul]
    have : 1 / (24 * (L : ℝ) ^ 4) * (24 * (L : ℝ) ^ 4) = 1 := by field_simp
    rw [this]
    simp
  have hW : ‖contourMean V c - 1‖ ≤ η := by
    have e : contourMean V c - 1 =
        w • ∑ x ∈ S, ∑ π : Equiv.Perm (Fin 4), (contourHolonomy V c x π - 1) := by
      have h0 : w • ∑ x ∈ S, ∑ π : Equiv.Perm (Fin 4), (contourHolonomy V c x π - 1) =
          w • (∑ x ∈ S, ∑ π : Equiv.Perm (Fin 4), contourHolonomy V c x π) -
            w • ∑ _x ∈ S, ∑ _π : Equiv.Perm (Fin 4), (1 : Matrices.ComplexMatrix2) := by
        simp only [Finset.sum_sub_distrib, smul_sub]
      rw [h0, hone, hmean]
    rw [e]
    have h1 : ‖∑ x ∈ S, ∑ π : Equiv.Perm (Fin 4), (contourHolonomy V c x π - 1)‖ ≤
        ∑ _x ∈ S, ∑ _π : Equiv.Perm (Fin 4), ((1 + ρ) ^ (5 * L) - 1) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x hx => ?_)
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun π _ => hcv x hx π)
    have h2 : ∑ _x ∈ S, ∑ _π : Equiv.Perm (Fin 4), ((1 + ρ) ^ (5 * L) - 1) =
        (24 * (L : ℝ) ^ 4) * ((1 + ρ) ^ (5 * L) - 1) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, hScard,
        nsmul_eq_mul]
      push_cast
      norm_num [Nat.factorial]
      ring
    rw [h2] at h1
    calc ‖w • ∑ x ∈ S, ∑ π : Equiv.Perm (Fin 4), (contourHolonomy V c x π - 1)‖
        ≤ ‖w‖ * ‖∑ x ∈ S, ∑ π : Equiv.Perm (Fin 4), (contourHolonomy V c x π - 1)‖ :=
          norm_smul_le _ _
      _ ≤ ‖w‖ * ((24 * (L : ℝ) ^ 4) * ((1 + ρ) ^ (5 * L) - 1)) := by gcongr
      _ = (1 + ρ) ^ (5 * L) - 1 := by
          rw [hwnorm]
          field_simp
      _ ≤ η := hε
  set W := contourMean V c with hWdef
  set E := W - 1 with hE
  have hentry : ∀ a b, ‖E a b‖ ≤ η := fun a b => (norm_apply_le_norm E a b).trans hW
  have hdet : ‖Matrix.det W - 1‖ ≤ 3 * η := by
    have e00 : W 0 0 = 1 + E 0 0 := by simp [hE]
    have e11 : W 1 1 = 1 + E 1 1 := by simp [hE]
    have e01 : W 0 1 = E 0 1 := by simp [hE]
    have e10 : W 1 0 = E 1 0 := by simp [hE]
    have e : Matrix.det W - 1 = E 0 0 + E 1 1 + E 0 0 * E 1 1 - E 0 1 * E 1 0 := by
      rw [Matrix.det_fin_two, e00, e11, e01, e10]
      ring
    rw [e]
    have a1 := hentry 0 0
    have a2 := hentry 1 1
    have a3 := hentry 0 1
    have a4 := hentry 1 0
    have m1 : ‖E 0 0 * E 1 1‖ ≤ η * η := by
      rw [norm_mul]
      exact mul_le_mul a1 a2 (norm_nonneg _) hη0.le
    have m2 : ‖E 0 1 * E 1 0‖ ≤ η * η := by
      rw [norm_mul]
      exact mul_le_mul a3 a4 (norm_nonneg _) hη0.le
    calc ‖E 0 0 + E 1 1 + E 0 0 * E 1 1 - E 0 1 * E 1 0‖
        ≤ ‖E 0 0 + E 1 1 + E 0 0 * E 1 1‖ + ‖E 0 1 * E 1 0‖ := norm_sub_le _ _
      _ ≤ ‖E 0 0‖ + ‖E 1 1‖ + ‖E 0 0 * E 1 1‖ + ‖E 0 1 * E 1 0‖ := by
          gcongr
          exact norm_add₃_le
      _ ≤ 3 * η := by nlinarith
  obtain ⟨hr0, hrsq, hrnear, hslit⟩ := sqrt_near_one (Matrix.det W) (by linarith)
  have hlen : meanRadius V c = (Matrix.det W) ^ (1 / 2 : ℂ) := rfl
  set r := (Matrix.det W) ^ (1 / 2 : ℂ) with hr
  have hav : normalizedMean V c = r⁻¹ • W := by
    rw [normalizedMean, hlen]
  have hrclose : ‖r - 1‖ ≤ 3 * η := hrnear.trans hdet
  have hrnorm : 1 / 2 ≤ ‖r‖ := by
    have h1 : ‖(1 : ℂ)‖ ≤ ‖r‖ + ‖r - 1‖ := by
      have := norm_sub_le r (r - 1)
      simpa using this
    simp at h1
    linarith
  have hrinv : ‖r⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    exact inv_le_of_inv_le₀ (by norm_num) (by norm_num; linarith)
  have hu : Matrices.ComplexMatrix2.operatorNorm (normalizedMean V c - 1) ≤ 8 * η := by
    have e : normalizedMean V c - 1 = r⁻¹ • (E + (1 - r) • (1 : Matrices.ComplexMatrix2)) := by
      rw [hav, smul_add, smul_smul, hE]
      have h1 : r⁻¹ * (1 - r) = r⁻¹ - 1 := by field_simp
      rw [h1, sub_smul, smul_sub, one_smul]
      abel
    rw [Matrices.ComplexMatrix2.operatorNorm, e]
    have h1 : ‖E + (1 - r) • (1 : Matrices.ComplexMatrix2)‖ ≤ η + 3 * η := by
      refine (norm_add_le _ _).trans (add_le_add hW ?_)
      refine (norm_smul_le _ _).trans ?_
      rw [norm_one, mul_one, norm_sub_rev]
      exact hrclose
    calc ‖r⁻¹ • (E + (1 - r) • (1 : Matrices.ComplexMatrix2))‖
        ≤ ‖r⁻¹‖ * ‖E + (1 - r) • (1 : Matrices.ComplexMatrix2)‖ := norm_smul_le _ _
      _ ≤ 2 * (η + 3 * η) := by gcongr
      _ = 8 * η := by ring
  have hudet : normalizedMean V c ∈ PeriodicLattice.complexGaugeGroup := by
    change Matrix.det (normalizedMean V c) = 1
    rw [hav, Matrix.det_smul, Fintype.card_fin, inv_pow, hrsq, inv_mul_cancel₀]
    intro h0
    exact hr0 (by rw [hr, h0]; simp)
  exact ⟨hslit, hlen ▸ hr0, hu, hudet⟩
private theorem plainAverage_compact (hZ : Tower.BlockPathContourPivotStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k)
    {V : Edge L k j → Matrices.ComplexMatrix2}
    (hVs : ∀ b, V b ∈ PeriodicLattice.compactGaugeGroup)
    {c : Edge L k (j + 1)} (hr0 : meanRadius V c ≠ 0)
    (hu : normalizedMean V c ∈ PeriodicLattice.complexGaugeGroup) :
    meanRadius V c = (((meanRadius V c).re : ℝ) : ℂ) ∧ 0 < (meanRadius V c).re ∧
      normalizedMean V c ∈ PeriodicLattice.compactGaugeGroup := by
  have hLpos : 0 < L := by
    have := hL.2
    omega
  have hVs' : ∀ b, V b ∈ Matrices.ComplexMatrix2.specialUnitary := hVs
  obtain ⟨hfin, -⟩ := cubeVertices_finite_ncard hZ hL hj c.initial
  have hcv : ∀ x π, contourHolonomy V c x π ∈ Matrices.ComplexMatrix2.specialUnitary := fun x π =>
    Matrices.ComplexMatrix2.specialUnitary.mul_mem
      (Matrices.ComplexMatrix2.specialUnitary.mul_mem (linkHolonomy_mem V hVs' _)
        (linkHolonomy_mem V hVs' _))
      (inv_mem_specialUnitary (linkHolonomy_mem V hVs' _))
  have hq : IsQuaternionic (contourMean V c) := by
    rw [contourMean, finsum_mem_eq_finite_toFinset_sum _ hfin, weight_eq_real hLpos]
    refine isQuaternionic_smul _ (isQuaternionic_sum _ _ fun x _ => isQuaternionic_sum _ _
      fun π _ => isQuaternionic_of_mem (hcv x π))
  obtain ⟨d, hd0, hd⟩ := exists_det_eq_nonneg hq
  have hlen : meanRadius V c = (d : ℂ) ^ (1 / 2 : ℂ) := by
    rw [meanRadius, hd]
  have hdpos : 0 < d := by
    rcases hd0.lt_or_eq with h | h
    · exact h
    · exfalso
      apply hr0
      rw [hlen, ← h]
      simp
  have hreal : meanRadius V c = ((d ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
    rw [hlen, Complex.ofReal_cpow hd0]
    norm_num
  have hre : (meanRadius V c).re = d ^ (1 / 2 : ℝ) := by
    rw [hreal, Complex.ofReal_re]
  refine ⟨by rw [hre]; exact hreal, by rw [hre]; exact Real.rpow_pos_of_pos hdpos _, ?_⟩
  have hqu : IsQuaternionic (normalizedMean V c) := by
    rw [normalizedMean, hreal, ← Complex.ofReal_inv]
    exact isQuaternionic_smul _ hq
  have hdet : Matrix.det (normalizedMean V c) = 1 := hu
  change normalizedMean V c ∈ Matrices.ComplexMatrix2.specialUnitary
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨(Matrix.mem_unitaryGroup_iff').2 ?_, hdet⟩
  have h1 : Matrix.adjugate (normalizedMean V c) * normalizedMean V c = 1 := by
    rw [Matrix.adjugate_mul, hdet, one_smul]
  rw [← h1]
  congr 1
  exact hqu.symm
end Main
end NearIdentity
open NearIdentity Tower Tower.FullSpace in
theorem normalizedMeanNearIdentity_holds (hZ : Tower.BlockPathContourPivotStatement) :
    NormalizedMeanNearIdentity := by
  intro L hL ε hε
  have hLpos : 0 < L := by
    have := hL.2
    omega
  set η : ℝ := min (ε / 16) (1 / 100) with hηdef
  have hη0 : 0 < η := lt_min (by positivity) (by norm_num)
  refine ⟨η / (2 * ((5 * L : ℕ) : ℝ)), by positivity, fun k j hj V hV hVρ c hc => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := estimates_near_identity hZ hL hη0 (min_le_right _ _) hj hV hVρ hc
  have h8 : 8 * η ≤ ε / 2 := by
    have := min_le_left (ε / 16) (1 / 100 : ℝ)
    linarith
  exact ⟨h1, h2, by linarith, h4, fun hs => plainAverage_compact hZ hL hj hs h2 h4⟩
end YangMills.Construction.RunningCouplingSlope.FullLattice
end
