import YangMills.Construction.Lattice.BoundsOfTheOneStepObjectsOnAPolydiscProof
import YangMills.Construction.Lattice.DomainsOfTheTwoSchemesProof
import YangMills.Construction.Lattice.OneStepObjectsReadInTheChartProof
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open YangMills.Construction.Matrices
open YangMills.Construction.Averaging
open YangMills.Construction.Conventions
namespace NearOneBounds
theorem mul_sub_one_norm_le {X Y : ComplexMatrix2} {d : ℝ} (hd : d ≤ 1) (hX : ‖X - 1‖ ≤ d)
    (hY : ‖Y - 1‖ ≤ d) : ‖X * Y - 1‖ ≤ 3 * d := by
  have e : X * Y - 1 = (X - 1) * (Y - 1) + (X - 1) + (Y - 1) := by noncomm_ring
  have h1 : 0 ≤ ‖Y - 1‖ := norm_nonneg _
  have h2 : ‖(X - 1) * (Y - 1)‖ ≤ ‖X - 1‖ * ‖Y - 1‖ := norm_mul_le _ _
  have h3 : ‖(X - 1) * (Y - 1) + (X - 1) + (Y - 1)‖ ≤
      ‖(X - 1) * (Y - 1)‖ + ‖X - 1‖ + ‖Y - 1‖ := norm_add₃_le
  rw [e]
  nlinarith
theorem inv_sub_one_norm_le (hE : ComplexMatrix2.ExpLogEstimates) {X : ComplexMatrix2} {d : ℝ}
    (hd : d ≤ 1 / 2) (hX : ‖X - 1‖ ≤ d) : ‖X⁻¹ - 1‖ ≤ 2 * d := by apply _root_.YangMills.Construction.PeriodicLattice.OneStepBounds.norm_inv_sub_one_le <;> assumption
theorem logSeries_norm_le (hE : ComplexMatrix2.ExpLogEstimates) {X : ComplexMatrix2} {d : ℝ}
    (hd : d ≤ 1 / 2) (hX : ‖X - 1‖ ≤ d) : ‖ComplexMatrix2.logSeries X‖ ≤ 2 * d := by apply _root_.YangMills.Construction.PeriodicLattice.OneStepBounds.norm_logSeries_le <;> assumption
theorem matExp_sub_one_norm_le (hE : ComplexMatrix2.ExpLogEstimates) {Z : ComplexMatrix2} {d : ℝ}
    (hd : d ≤ 1 / 2) (hZ : ‖Z‖ ≤ d) : ‖ComplexMatrix2.matExp Z - 1‖ ≤ 2 * d := by
  have h := (hE.1 Z).2
  have h0 : 0 ≤ ‖Z‖ := norm_nonneg _
  have h1 : Real.exp ‖Z‖ ≤ 1 / (1 - ‖Z‖) :=
    Real.exp_bound_div_one_sub_of_interval h0 (by linarith)
  have h2 : 1 / (1 - ‖Z‖) - 1 ≤ 2 * d := by
    rw [sub_le_iff_le_add, div_le_iff₀ (by linarith)]
    nlinarith
  linarith
section Families
variable {ι κ : Type} [Fintype ι] [Fintype κ]
theorem isLogMean_comp_equiv (e : κ ≃ ι) (𝒢 : Set ComplexMatrix2) (V : ι → ComplexMatrix2)
    (W : ComplexMatrix2) :
    ComplexMatrix2.IsLogMean 𝒢 (V ∘ e) W ↔ ComplexMatrix2.IsLogMean 𝒢 V W := by
  constructor
  · rintro ⟨h₁, h₂, h₃⟩
    refine ⟨h₁, fun i => ?_, ?_⟩
    · simpa using h₂ (e.symm i)
    · rw [← Equiv.sum_comp e]
      exact h₃
  · rintro ⟨h₁, h₂, h₃⟩
    refine ⟨h₁, fun i => h₂ (e i), ?_⟩
    rw [← h₃]
    exact Equiv.sum_comp e fun i => ComplexMatrix2.logSeries (V i * W⁻¹)
theorem complexLogMean_comp_equiv (e : κ ≃ ι) (V : ι → ComplexMatrix2) :
    complexLogMean (V ∘ e) = complexLogMean V := by apply _root_.YangMills.SharedProofs.p1929 <;> assumption
omit [Fintype ι] [Fintype κ] in
theorem familyDiameter_comp_equiv (e : κ ≃ ι) (V : ι → ComplexMatrix2) :
    ComplexMatrix2.familyDiameter (V ∘ e) = ComplexMatrix2.familyDiameter V :=
  (e.prodCongr e).iSup_comp
    (g := fun p : ι × ι => ComplexMatrix2.operatorNorm (V p.1 * (V p.2)⁻¹ - 1))
theorem complexLogMean_near_one [Nonempty ι] (hE : ComplexMatrix2.ExpLogEstimates)
    (hM : ∀ n : ℕ, 1 ≤ n → ComplexLogMeanProperties n) {V : ι → ComplexMatrix2} {τ : ℝ}
    (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1 / 1000000) (hV : ∀ i, V i ∈ complexGaugeGroup)
    (hn : ∀ i, ‖V i - 1‖ ≤ τ) :
    ComplexMatrix2.familyDiameter V < centreOfMassDiameter ∧
      ‖complexLogMean V - 1‖ ≤ 144 * τ := by
  have hinv : ∀ i, ‖(V i)⁻¹ - 1‖ ≤ 2 * τ := fun i =>
    inv_sub_one_norm_le hE (by linarith) (hn i)
  have hd : ComplexMatrix2.familyDiameter V ≤ 6 * τ := by
    unfold ComplexMatrix2.familyDiameter
    refine ciSup_le fun p => ?_
    have := mul_sub_one_norm_le (d := 2 * τ) (by linarith) ((hn p.1).trans (by linarith))
      (hinv p.2)
    show ‖V p.1 * (V p.2)⁻¹ - 1‖ ≤ 6 * τ
    linarith
  have hlt : ComplexMatrix2.familyDiameter V < centreOfMassDiameter := by
    have : (6 : ℝ) * τ < 1 / 40 := by linarith
    simpa [centreOfMassDiameter] using lt_of_le_of_lt hd this
  refine ⟨hlt, ?_⟩
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hs : V ∘ e ∈ smallComplexFamilies (Fintype.card ι) :=
    ⟨fun i => hV (e i), by rwa [familyDiameter_comp_equiv]⟩
  have hMF := hM (Fintype.card ι) Fintype.card_pos
  have hspec : IsNearComplexLogMean (V ∘ e) (complexLogMean (V ∘ e)) :=
    Classical.epsilon_spec (p := fun W => ComplexMatrix2.IsLogMean complexGaugeGroup (V ∘ e) W ∧
      ∃ i, ComplexMatrix2.operatorNorm ((V ∘ e) i * W⁻¹ - 1) ≤ complexMeanTolerance)
      (hMF.existsUnique _ hs).exists
  have hdet : (complexLogMean V).det = 1 := by
    have := hspec.1.1
    rw [complexLogMean_comp_equiv] at this
    exact this
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hsp := hMF.spread _ hs (e.symm i₀)
  rw [complexLogMean_comp_equiv, familyDiameter_comp_equiv] at hsp
  have hsp' : ‖V i₀ * (complexLogMean V)⁻¹ - 1‖ ≤ 24 * τ := by
    have e₁ : (V ∘ e) (e.symm i₀) = V i₀ := by simp
    rw [e₁] at hsp
    have : ComplexMatrix2.operatorNorm (V i₀ * (complexLogMean V)⁻¹ - 1) ≤
        4 * ComplexMatrix2.familyDiameter V := hsp
    show ComplexMatrix2.operatorNorm (V i₀ * (complexLogMean V)⁻¹ - 1) ≤ 24 * τ
    linarith
  have hVu : IsUnit (V i₀).det := by
    have : (V i₀).det = 1 := hV i₀
    rw [this]
    exact isUnit_one
  have hinvmean : (complexLogMean V)⁻¹ = (V i₀)⁻¹ * (V i₀ * (complexLogMean V)⁻¹) := by
    rw [← mul_assoc, Matrix.nonsing_inv_mul _ hVu, one_mul]
  have h72 : ‖(complexLogMean V)⁻¹ - 1‖ ≤ 72 * τ := by
    have := mul_sub_one_norm_le (X := (V i₀)⁻¹) (Y := V i₀ * (complexLogMean V)⁻¹)
      (d := 24 * τ) (by linarith) ((hinv i₀).trans (by linarith)) hsp'
    rw [← hinvmean] at this
    linarith
  have h144 := inv_sub_one_norm_le hE (d := 72 * τ) (by linarith) h72
  rw [Matrix.nonsing_inv_nonsing_inv _ (by rw [hdet]; exact isUnit_one)] at h144
  linarith
end Families
variable {L m : ℕ}
theorem pathHolonomy_det_eq_one {j : ℤ} {W : Bond L m j → ComplexMatrix2} :
    ∀ Γ : List (Bond L m j), (∀ b ∈ Γ, (W b).det = 1) → (pathHolonomy W Γ).det = 1
  | [], _ => by simp [pathHolonomy]
  | b :: Γ, h => by
    have e : pathHolonomy W (b :: Γ) = W b * pathHolonomy W Γ := by simp [pathHolonomy]
    rw [e, Matrix.det_mul, h b (by simp),
      pathHolonomy_det_eq_one Γ (fun b' hb' => h b' (List.mem_cons_of_mem _ hb')), one_mul]
theorem pathHolonomy_sub_one_norm_le {j : ℤ} {W : Bond L m j → ComplexMatrix2} {ε : ℝ}
    (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    ∀ Γ : List (Bond L m j), (∀ b ∈ Γ, ‖W b - 1‖ ≤ ε) →
      ‖pathHolonomy W Γ - 1‖ ≤ (2 ^ Γ.length - 1) * ε
  | [], _ => by simp [pathHolonomy]
  | b :: Γ, h => by
    have e : pathHolonomy W (b :: Γ) - 1 = (W b - 1) * (pathHolonomy W Γ - 1) + (W b - 1) +
        (pathHolonomy W Γ - 1) := by
      have : pathHolonomy W (b :: Γ) = W b * pathHolonomy W Γ := by simp [pathHolonomy]
      rw [this]
      noncomm_ring
    have ih := pathHolonomy_sub_one_norm_le h0 h1 Γ
      (fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))
    have hb := h b (by simp)
    have n0 : 0 ≤ ‖W b - 1‖ := norm_nonneg _
    have n1 : 0 ≤ ‖pathHolonomy W Γ - 1‖ := norm_nonneg _
    have h2 : ‖(W b - 1) * (pathHolonomy W Γ - 1)‖ ≤ ‖W b - 1‖ * ‖pathHolonomy W Γ - 1‖ :=
      norm_mul_le _ _
    have h3 : ‖(W b - 1) * (pathHolonomy W Γ - 1) + (W b - 1) + (pathHolonomy W Γ - 1)‖ ≤
        ‖(W b - 1) * (pathHolonomy W Γ - 1)‖ + ‖W b - 1‖ + ‖pathHolonomy W Γ - 1‖ :=
      norm_add₃_le
    rw [e]
    have h4 : ((2 : ℝ) ^ (b :: Γ).length - 1) * ε =
        2 * (((2 : ℝ) ^ Γ.length - 1) * ε) + ε := by
      simp only [List.length_cons, pow_succ]
      ring
    rw [h4]
    nlinarith
theorem length_le_sum_countP_of_cover {α : Type} (p : Fin 4 → α → Bool) :
    ∀ l : List α, (∀ a ∈ l, ∃ ν, p ν a = true) → l.length ≤ ∑ ν, l.countP (p ν)
  | [], _ => by simp
  | a :: l, h => by
    obtain ⟨ν, hν⟩ := h a (by simp)
    have ih := length_le_sum_countP_of_cover p l
      (fun a' ha' => h a' (List.mem_cons_of_mem _ ha'))
    have e : (∑ κ, (a :: l).countP (p κ)) =
        (∑ κ, l.countP (p κ)) + ∑ κ, (if p κ a = true then 1 else 0) := by
      simp only [List.countP_cons, Finset.sum_add_distrib]
    have h2 : 1 ≤ ∑ κ, (if p κ a = true then 1 else 0) := by
      calc 1 = (if p ν a = true then 1 else 0) := by simp [hν]
        _ ≤ _ := Finset.single_le_sum (f := fun κ => if p κ a = true then 1 else 0)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ ν)
    simp only [List.length_cons]
    omega
theorem length_le_four_mul {j : ℤ} {Γ : List (Bond L m j)} {Q : Fin 4 → Prop}
    {f : Fin 4 → Site L m j} {B : ℕ} (hb : ∀ b ∈ Γ, ∃ ν, Q ν ∧ b.target - b.source = f ν)
    (hB : ∀ ν, Q ν → countSteps Γ (f ν) ≤ B) : Γ.length ≤ 4 * B := by
  classical
  have h1 := length_le_sum_countP_of_cover
    (fun ν (b : Bond L m j) => decide (Q ν ∧ b.target - b.source = f ν))
    Γ (fun b hb' => by
      obtain ⟨ν, h⟩ := hb b hb'
      exact ⟨ν, by simpa using h⟩)
  have h2 : ∀ ν, Γ.countP (fun b : Bond L m j => decide (Q ν ∧ b.target - b.source = f ν)) ≤ B := by
    intro ν
    by_cases hQ : Q ν
    · refine le_trans ?_ (hB ν hQ)
      unfold countSteps
      refine List.countP_mono_left fun b _ h => ?_
      simp only [decide_eq_true_eq] at h ⊢
      exact h.2
    · have : Γ.countP (fun b : Bond L m j => decide (Q ν ∧ b.target - b.source = f ν)) = 0 := by
        refine List.countP_eq_zero.mpr fun b _ => ?_
        simp [hQ]
      omega
  have h3 : ∑ ν, Γ.countP (fun b : Bond L m j => decide (Q ν ∧ b.target - b.source = f ν)) ≤
      ∑ _ν : Fin 4, B := Finset.sum_le_sum fun ν _ => h2 ν
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h3
  omega
section Axial
variable {j : ℤ}
theorem mem_forwardFlow {b : Bond L m j} (μ : Fin 4) :
    ∀ (r : ℕ) (x : Site L m j), b ∈ forwardAxisPath x μ r →
      ∃ i : ℕ, i < r ∧ b.source = x + (i : ℤ) • unitStep L m j μ
  | 0, _, h => by simp [forwardAxisPath] at h
  | r + 1, x, h => by
    simp only [forwardAxisPath, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨0, by omega, by simp [Bond.forwardFrom]⟩
    · obtain ⟨i, hi, e⟩ := mem_forwardFlow μ r _ h
      refine ⟨i + 1, by omega, ?_⟩
      rw [e]
      push_cast
      rw [add_smul, one_smul]
      abel
theorem forwardFlow_add (μ : Fin 4) (a c : ℕ) : ∀ x : Site L m j,
    forwardAxisPath x μ (a + c) =
      forwardAxisPath x μ a ++ forwardAxisPath (x + (a : ℤ) • unitStep L m j μ) μ c := by
  induction a with
  | zero => intro x; simp [forwardAxisPath]
  | succ a ih =>
    intro x
    have e : x + ((a + 1 : ℕ) : ℤ) • unitStep L m j μ =
        x + unitStep L m j μ + (a : ℤ) • unitStep L m j μ := by
      push_cast
      rw [add_smul, one_smul]
      abel
    rw [e, show a + 1 + c = (a + c) + 1 by omega]
    simp only [forwardAxisPath, List.cons_append]
    rw [ih]
theorem forwardFlow_length (μ : Fin 4) (t : ℕ) : ∀ x : Site L m j,
    (forwardAxisPath x μ t).length = t := by
  induction t with
  | zero => intro x; rfl
  | succ t ih => intro x; simp [forwardAxisPath, ih]
theorem zsmul_unitStep_apply (μ ν : Fin 4) (n : ℤ) :
    ((n • unitStep L m j μ : Site L m j) : FourTorus L m) ν =
      if ν = μ then (((n : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) else 0 := by
  by_cases h : ν = μ
  · subst h
    simp [unitStep, pointOnAxis]
  · simp [unitStep, pointOnAxis, h]
theorem int_eq_zero_of_coe_eq_zero (hL : 0 < L) {d : ℤ}
    (hd : (((d : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) = 0)
    (hlt : |(d : ℝ)| < 2 * (L : ℝ) ^ ((m : ℤ) + j)) : d = 0 := by apply _root_.YangMills.Construction.PeriodicLattice.ChartInvariance.int_eq_zero_of_coe_mul_meshSize <;> assumption
theorem axialDisplacement_unique (hL : 0 < L) {x x' : Site L m j} {μ ν : Fin 4} {n n' : ℤ}
    (h : IsAxialDisplacement x x' μ n) (h' : IsAxialDisplacement x x' ν n') :
    (μ = ν ∧ n = n') ∨ (n = 0 ∧ n' = 0) := by
  have e : n • unitStep L m j μ = n' • unitStep L m j ν := h.1.symm.trans h'.1
  have coord : ∀ κ, ((n • unitStep L m j μ : Site L m j) : FourTorus L m) κ =
      ((n' • unitStep L m j ν : Site L m j) : FourTorus L m) κ := fun κ => by rw [e]
  have hb : |(n : ℝ)| < (L : ℝ) ^ ((m : ℤ) + j) := by
    have := h.2
    rwa [Int.cast_abs] at this
  have hb' : |(n' : ℝ)| < (L : ℝ) ^ ((m : ℤ) + j) := by
    have := h'.2
    rwa [Int.cast_abs] at this
  have hT : 0 < (L : ℝ) ^ ((m : ℤ) + j) := lt_of_le_of_lt (abs_nonneg _) hb
  by_cases hμν : μ = ν
  · subst hμν
    left
    refine ⟨rfl, ?_⟩
    have hc := coord μ
    rw [zsmul_unitStep_apply, zsmul_unitStep_apply, if_pos rfl, if_pos rfl] at hc
    have hz : ((((n - n' : ℤ) : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) = 0 := by
      push_cast
      rw [sub_mul, AddCircle.coe_sub, hc, sub_self]
    have := int_eq_zero_of_coe_eq_zero hL hz (by
      push_cast
      calc |(n : ℝ) - n'| ≤ |(n : ℝ)| + |(n' : ℝ)| := abs_sub _ _
        _ < _ := by linarith)
    omega
  · right
    have hc := coord μ
    rw [zsmul_unitStep_apply, zsmul_unitStep_apply, if_pos rfl, if_neg hμν] at hc
    have hc' := coord ν
    rw [zsmul_unitStep_apply, zsmul_unitStep_apply, if_neg (Ne.symm hμν), if_pos rfl] at hc'
    exact ⟨int_eq_zero_of_coe_eq_zero hL hc (by linarith),
      int_eq_zero_of_coe_eq_zero hL hc'.symm (by linarith)⟩
theorem axialPath_eq_forwardFlow (hL : 0 < L) {x y : Site L m j} {μ : Fin 4} {t : ℕ}
    (hy : y = x + (t : ℤ) • unitStep L m j μ) (ht : (t : ℝ) < (L : ℝ) ^ ((m : ℤ) + j)) :
    axialPath x y = forwardAxisPath x μ t := by
  have h : IsAxialDisplacement x y μ (t : ℤ) :=
    ⟨by rw [hy]; abel, by simpa using ht⟩
  have hex : ∃ q : Fin 4 × ℤ, IsAxialDisplacement x y q.1 q.2 := ⟨(μ, (t : ℤ)), h⟩
  unfold axialPath
  rw [dif_pos hex]
  rcases axialDisplacement_unique hL hex.choose_spec h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
    simp [flowAlong]
  · rw [h1]
    have ht0 : t = 0 := by exact_mod_cast h2
    subst ht0
    simp [flowAlong, forwardAxisPath]
end Axial
variable {K n : ℕ}
theorem exists_offset_of_mem {y : SiteAtLevel L m K (n + 1)} {x : SiteAtLevel L m K n}
    (hb : BlockCoordinates (levelDepth K n) y) (hx : x ∈ sitesInBlock (levelDepth K n) y) :
    ∃ p ∈ blockIndexBox L, x = offsetSite (y.toSublattice (levelDepth K n)) p := by
  have hx' : (x : FourTorus L m) ∈ unitBlock y := hx
  rw [← hb.1.2] at hx'
  obtain ⟨p, hp, e⟩ := hx'
  exact ⟨p, hp, Subtype.ext e.symm⟩
theorem contour_length_le (hG : BlockPaths.Statement)
    (hL : IsAdmissibleBlockingFactor L) (hm : 0 < m) (hn : n < K) {y : SiteAtLevel L m K (n + 1)}
    {x : SiteAtLevel L m K n} (hx : x ∈ sitesInBlock (levelDepth K n) y) :
    ∀ Γ ∈ contourSet y x, Γ.length ≤ 4 * L := by
  have hy := (hG L m K hL.1 hL.2 hm n hn).1 y
  obtain ⟨p, hp, rfl⟩ := exists_offset_of_mem hy.1 hx
  intro Γ hΓ
  obtain ⟨_, h2, h3, _, _⟩ := (hy.2.2 p hp).1 Γ hΓ
  refine length_le_four_mul (Q := fun ν => p ν ≠ 0)
    (f := fun ν => (p ν).sign • unitStep L m (levelDepth K n) ν) h3 fun ν hν => ?_
  obtain ⟨e, hb⟩ := h2 ν hν
  show countSteps Γ ((p ν).sign • unitStep L m (levelDepth K n) ν) ≤ L
  rw [e]
  rw [Int.abs_eq_natAbs] at hb
  unfold centreToFaceSteps at hb
  omega
theorem coordinateComb_length_le (hG : BlockPaths.Statement)
    (hL : IsAdmissibleBlockingFactor L) (hm : 0 < m) (hn : n < K) {y : SiteAtLevel L m K (n + 1)}
    {x : SiteAtLevel L m K n} (hx : x ∈ sitesInBlock (levelDepth K n) y) :
    (coordinateComb (blockAnchor (levelDepth K n) y) x).length ≤ 4 * L := by
  have hy := (hG L m K hL.1 hL.2 hm n hn).1 y
  obtain ⟨p, hp, rfl⟩ := exists_offset_of_mem hy.1 hx
  obtain ⟨_, _, _, h4, h5, _, _⟩ := (hy.2.2 p hp).2
  refine length_le_four_mul (Q := fun _ => True) (f := unitStep L m (levelDepth K n))
    (fun b hb => ?_) fun ν _ => ?_
  · obtain ⟨ν, h⟩ := h5 b hb
    exact ⟨ν, trivial, h⟩
  · obtain ⟨e, hb⟩ := h4 ν
    rw [e]
    omega
theorem axialPath_within_crossing {c : BondAtLevel L m K (n + 1)} {μ : Fin 4}
    (hS : DoubleBlockAxialPaths (levelDepth K n) c μ) (hL : 0 < L) {x : SiteAtLevel L m K n}
    (hx : x ∈ sitesInBlock (levelDepth K n) c.source) {b : BondAtLevel L m K n}
    (hb : b ∈ crossingPath c x) :
    (∀ b' ∈ axialPath x b.source, b' ∈ crossingPath c x) ∧
      (axialPath x b.source).length ≤ L := by
  obtain ⟨hd, hc, _, _⟩ := hS.1 x hx
  rw [hc] at hb
  obtain ⟨i, hi, e⟩ := mem_forwardFlow μ L x hb
  have hlt : (i : ℝ) < (L : ℝ) ^ ((m : ℤ) + levelDepth K n) := by
    have h2 := hd.2
    have h3 : ((|(L : ℤ)| : ℤ) : ℝ) = (L : ℝ) := by simp
    rw [h3] at h2
    exact lt_trans (by exact_mod_cast hi) h2
  rw [axialPath_eq_forwardFlow hL e hlt, hc, forwardFlow_length]
  refine ⟨fun b' hb' => ?_, hi.le⟩
  have h := forwardFlow_add (L := L) (m := m) (j := levelDepth K n) μ i (L - i) x
  rw [show i + (L - i) = L by omega] at h
  rw [h]
  exact List.mem_append_left _ hb'
theorem schemeObjectsNearOne_of_paths (hE : ComplexMatrix2.ExpLogEstimates)
    (hM : ∀ n : ℕ, 1 ≤ n → ComplexLogMeanProperties n)
    (hG : BlockPaths.Statement) (hL : IsAdmissibleBlockingFactor L) (hm : 0 < m)
    (hn : n < K) (s : AveragingScheme) (c : BondAtLevel L m K (n + 1))
    (hc : c.IsPositivelyOriented)
    {W : BondAtLevel L m K n → ComplexMatrix2}
    (hW : IsGaugeField complexGaugeGroup (bondsInDoubleBlock c) W)
    {τ η : ℝ} (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1 / 1000000) (hη : 100000 * τ ≤ η)
    (hpath : ∀ Γ : List (BondAtLevel L m K n),
      (∀ b ∈ Γ, b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n))) → Γ.length ≤ 4 * L →
        ‖pathHolonomy W Γ - 1‖ ≤ τ) :
    SchemeObjectsNearOne η s c W := by
  have hLpos : 0 < L := by
    have := hL.2
    omega
  obtain ⟨μ, hμ⟩ := id hc
  have hP := hG L m K hL.1 hL.2 hm n hn
  obtain ⟨hDB, -, -, hSt, hPD⟩ := hP.2 c μ hμ
  have hdet : ∀ Γ : List (BondAtLevel L m K n),
      (∀ b ∈ Γ, b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n))) →
        (pathHolonomy W Γ).det = 1 := fun Γ h =>
    pathHolonomy_det_eq_one Γ fun b hb => hW.1 b (h b hb)
  have hcv : ∀ y : SiteAtLevel L m K (n + 1), (y = c.source ∨ y = c.target) →
      ∀ x ∈ sitesInBlock (levelDepth K n) y,
        ‖contourHolonomy s W y x - 1‖ ≤ 144 * τ ∧ IsContourHolonomyDefined s W y x := by
    intro y hy x hx
    have hsub : ∀ b ∈ (bondsInside (unitBlock y) : Set (BondAtLevel L m K n)),
        b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)) := by
      intro b hb
      rcases hy with rfl | rfl
      · exact ⟨Or.inl hb.1, Or.inl hb.2⟩
      · exact ⟨Or.inr hb.1, Or.inr hb.2⟩
    have hcfg : IsGaugeField complexGaugeGroup (bondsInside (unitBlock y)) W :=
      ⟨fun b hb => hW.1 b (hsub b hb), fun b hb => hW.2 b (hsub b hb)⟩
    have hbonds := hPD.1 y hy x hx
    cases s with
    | centred =>
      have hin : ∀ σ, ∀ b ∈ orderedContour y x σ,
          b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)) := fun σ =>
        hbonds.1 _ ⟨σ, rfl⟩
      have : Nonempty (AxisOrdering y x) := ⟨(Finset.equivFin _).symm⟩
      have h := complexLogMean_near_one hE hM hτ0 hτ (V := contourHolonomies W y x)
        (fun σ => hdet _ (hin σ))
        (fun σ => hpath _ (hin σ) (contour_length_le hG hL hm hn hx _ ⟨σ, rfl⟩))
      exact ⟨h.2, hx, hcfg, h.1⟩
    | cornered =>
      exact ⟨(hpath _ hbonds.2 (coordinateComb_length_le hG hL hm hn hx)).trans (by linarith),
        hx, hcfg, trivial⟩
  have hcross : ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
      ‖pathHolonomy W (crossingPath c x) - 1‖ ≤ τ :=
    fun x hx => hpath _ (hPD.2 x hx) (by
      rw [(hSt.1 x hx).2.1, forwardFlow_length]
      omega)
  have hblk := (hP.1 c.source).1
  have hzero : c.source.toSublattice (levelDepth K n) ∈
      sitesInBlock (levelDepth K n) c.source := by
    have h0 : (0 : Fin 4 → ℤ) ∈ blockIndexBox L := by
      intro ν
      have : 0 ≤ centreToFaceSteps L := by
        unfold centreToFaceSteps
        omega
      simp only [Pi.zero_apply]
      omega
    have e : offsetSite (c.source.toSublattice (levelDepth K n)) 0 =
        c.source.toSublattice (levelDepth K n) := by
      simp [offsetSite]
    show ((c.source.toSublattice (levelDepth K n) : SiteAtLevel L m K n) : FourTorus L m) ∈
      unitBlock c.source
    rw [← hblk.1.2]
    exact ⟨0, h0, congrArg (fun z : SiteAtLevel L m K n => (z : FourTorus L m)) e⟩
  have htr : ‖baseTransport s W c - 1‖ ≤ τ := by
    cases s with
    | centred =>
      have e : baseTransport .centred W c =
          pathHolonomy W (crossingPath c (c.source.toSublattice (levelDepth K n))) := by
        show pathHolonomy W (axialPath (c.source.toSublattice (levelDepth K n))
          (c.target.toSublattice (levelDepth K n))) = _
        rw [hSt.2.1]
      rw [e]
      exact hcross _ hzero
    | cornered =>
      have e : baseTransport .cornered W c =
          pathHolonomy W (crossingPath c (blockAnchor (levelDepth K n) c.source)) := by
        show pathHolonomy W (axialPath (blockAnchor (levelDepth K n) c.source)
          (blockAnchor (levelDepth K n) c.target)) = _
        rw [hSt.2.2]
      rw [e]
      exact hcross _ hblk.2.2
  have hhead : ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
      shiftAcross c x ∈ sitesInBlock (levelDepth K n) c.target := by
    intro x hx
    rw [hDB.2.2.2.2.1 x hx, ← hDB.2.2.2.1]
    exact ⟨x, hx, rfl⟩
  have hX : ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
      ‖localDefect s W c x - 1‖ ≤ 7776 * τ := by
    intro x hx
    have h1 := (hcv _ (Or.inl rfl) x hx).1
    have h2 := hcross x hx
    have h3 := inv_sub_one_norm_le hE (d := 144 * τ) (by linarith)
      (hcv _ (Or.inr rfl) _ (hhead x hx)).1
    have h4 := inv_sub_one_norm_le hE (d := τ) (by linarith) htr
    have p1 := mul_sub_one_norm_le (d := 288 * τ) (by linarith) (h1.trans (by linarith))
      (h2.trans (by linarith))
    have p2 := mul_sub_one_norm_le (d := 864 * τ) (by linarith) (p1.trans (by linarith))
      (h3.trans (by linarith))
    have p3 := mul_sub_one_norm_le (d := 2592 * τ) (by linarith) (p2.trans (by linarith))
      (h4.trans (by linarith))
    have h5 : ‖localDefect s W c x - 1‖ ≤ 3 * (2592 * τ) := p3
    linarith
  have hfinB : (unitBlock c.source).Finite :=
    Set.finite_of_ncard_ne_zero (by rw [hblk.2.1]; exact pow_ne_zero _ hLpos.ne')
  have hinj : Function.Injective (fun x : SiteAtLevel L m K n => (x : FourTorus L m)) :=
    Subtype.val_injective
  have hfin : (sitesInBlock (levelDepth K n) c.source : Set (SiteAtLevel L m K n)).Finite :=
    hfinB.preimage hinj.injOn
  have hcard : (sitesInBlock (levelDepth K n) c.source : Set (SiteAtLevel L m K n)).ncard ≤
      L ^ 4 := by
    rw [← hblk.2.1, ← Set.ncard_image_of_injective _ hinj]
    exact Set.ncard_le_ncard (by rintro _ ⟨x, hx, rfl⟩; exact hx) hfinB
  have hsum : ‖∑ᶠ x ∈ (sitesInBlock (levelDepth K n) c.source : Set (SiteAtLevel L m K n)),
      ComplexMatrix2.logSeries (localDefect s W c x)‖ ≤ (L : ℝ) ^ 4 * (2 * (7776 * τ)) := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    calc _ ≤ ∑ _x ∈ hfin.toFinset, 2 * (7776 * τ) :=
          norm_sum_le_of_le _ fun x hx =>
            logSeries_norm_le hE (by linarith) (hX x ((Set.Finite.mem_toFinset hfin).mp hx))
      _ = ((sitesInBlock (levelDepth K n) c.source : Set (SiteAtLevel L m K n)).ncard : ℝ) *
            (2 * (7776 * τ)) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← Set.ncard_eq_toFinset_card _ hfin]
      _ ≤ _ := by
          have : ((sitesInBlock (levelDepth K n) c.source :
              Set (SiteAtLevel L m K n)).ncard : ℝ) ≤ (L : ℝ) ^ 4 := by exact_mod_cast hcard
          exact mul_le_mul_of_nonneg_right this (by linarith)
  have hLr : (0 : ℝ) < (L : ℝ) ^ 4 := by
    have : (0 : ℝ) < L := by exact_mod_cast hLpos
    positivity
  have hw : ‖inverseFourthPowerWeight L‖ = ((L : ℝ) ^ 4)⁻¹ := by
    have e : (L : ℝ) ^ (-4 : ℤ) = ((L : ℝ) ^ 4)⁻¹ := by
      rw [zpow_neg]
      norm_cast
    rw [inverseFourthPowerWeight, Complex.norm_real, e, Real.norm_of_nonneg (by positivity)]
  have hZ : ‖inverseFourthPowerWeight L •
      ∑ᶠ x ∈ (sitesInBlock (levelDepth K n) c.source : Set (SiteAtLevel L m K n)),
        ComplexMatrix2.logSeries (localDefect s W c x)‖ ≤ 2 * (7776 * τ) := by
    rw [norm_smul, hw, inv_mul_le_iff₀ hLr]
    exact hsum
  have hexp := matExp_sub_one_norm_le hE (d := 2 * (7776 * τ)) (by linarith) hZ
  have havg := mul_sub_one_norm_le (d := 2 * (2 * (7776 * τ))) (by linarith) hexp
    (htr.trans (by linarith))
  have hA : schemeBlockAverage s W c = positiveBondAverage s W c := by
    simp only [schemeBlockAverage, if_pos hc]
  refine ⟨⟨hW, ⟨fun x hx => (hcv _ (Or.inl rfl) x hx).2,
    fun x hx => (hcv _ (Or.inr rfl) x hx).2⟩, fun x hx => ?_⟩, ?_, ?_, ?_⟩
  · have := hX x hx
    show ‖localDefect s W c x - 1‖ < 1
    linarith
  · intro y hy x hx
    have hy' : y = c.source ∨ y = c.target := by simpa using hy
    exact (hcv y hy' x hx).1.trans (by linarith)
  · rw [hA]
    have h6 : ‖positiveBondAverage s W c - 1‖ ≤ 3 * (2 * (2 * (7776 * τ))) := havg
    show ‖positiveBondAverage s W c - 1‖ ≤ η
    linarith
  · intro x hx b hb
    obtain ⟨h1, h2⟩ := axialPath_within_crossing hSt hLpos hx hb
    exact (hpath _ (fun b' hb' => hPD.2 x hx b' (h1 b' hb')) (by omega)).trans (by linarith)
end NearOneBounds
theorem schemeObjectsNearOneUniformly_holds (hG : BlockPaths.Statement)
    (hM : ComplexLogMeanOfSmallFamilies) (hE : ComplexMatrix2.ExpLogEstimates) :
    SchemeObjectsNearOneUniformly := by
  intro L hL η hη
  have hA : (0 : ℝ) < 2 ^ (4 * L) := by positivity
  have hA1 : (1 : ℝ) ≤ 2 ^ (4 * L) := one_le_pow₀ (by norm_num)
  obtain ⟨τ, hτdef⟩ : ∃ τ : ℝ, τ = min η 1 / 1000000 := ⟨_, rfl⟩
  have hτ0 : 0 < τ := by
    rw [hτdef]
    positivity
  have hτ : τ ≤ 1 / 1000000 := by
    have := min_le_right η 1
    rw [hτdef]
    linarith
  have hτη : 100000 * τ ≤ η := by
    have := min_le_left η 1
    rw [hτdef]
    linarith
  have hε0 : 0 < τ / 2 ^ (4 * L) := by positivity
  have hε1 : τ / 2 ^ (4 * L) ≤ 1 := by
    rw [div_le_one hA]
    linarith
  refine ⟨τ / 2 ^ (4 * L), hε0, ?_⟩
  intro m K n hm hn s c hc W hW
  refine NearOneBounds.schemeObjectsNearOne_of_paths hE hM.2.2.2.1 hG hL hm hn s c hc hW.1
    hτ0.le hτ hτη fun Γ hΓ hlen => ?_
  have h := NearOneBounds.pathHolonomy_sub_one_norm_le (W := W) hε0.le hε1 Γ
    fun b hb => hW.2 b (hΓ b hb)
  have h2 : (2 : ℝ) ^ Γ.length ≤ 2 ^ (4 * L) := pow_le_pow_right₀ (by norm_num) hlen
  calc ‖pathHolonomy W Γ - 1‖ ≤ (2 ^ Γ.length - 1) * (τ / 2 ^ (4 * L)) := h
    _ ≤ 2 ^ (4 * L) * (τ / 2 ^ (4 * L)) :=
        mul_le_mul_of_nonneg_right (by linarith) hε0.le
    _ = τ := by field_simp
end YangMills.Construction.PeriodicLattice
