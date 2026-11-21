import YangMills.Construction.ChessboardTori.ChessboardBoundOfAFamily
import YangMills.Construction.ChessboardTori.ElementaryPropertiesOfAGrid
import YangMills.Construction.ChessboardTori.ReflectionBoundInOneDirection
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ChessboardTori.FamilyChessboardBound
theorem re_eq_norm_of_im_eq_zero (z : ℂ) (him : z.im = 0) (hre : 0 ≤ z.re) : z.re = ‖z‖ := by
  have hz : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [him])
  calc z.re = ‖(z.re : ℂ)‖ := by rw [Complex.norm_real, Real.norm_of_nonneg hre]
    _ = ‖z‖ := by rw [← hz]
theorem prod_rpow_rpow {ι : Type*} (s : Finset ι) (f : ι → ℝ) (r e : ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) : (∏ i ∈ s, f i ^ r) ^ e = ∏ i ∈ s, f i ^ (r * e) := by
  rw [← Real.finsetProd_rpow s _ (fun i hi => Real.rpow_nonneg (hf i hi) r) e]
  exact Finset.prod_congr rfl fun i hi => (Real.rpow_mul (hf i hi) r e).symm
theorem fourfold_prod_rpow (s₀ s₁ s₂ s₃ : Finset ℤ) (X : ℤ → ℤ → ℤ → ℤ → ℝ)
    (hX : ∀ a ∈ s₀, ∀ b ∈ s₁, ∀ c ∈ s₂, ∀ d ∈ s₃, 0 ≤ X a b c d) (e : ℝ) :
    ∏ a ∈ s₀, (∏ b ∈ s₁, (∏ c ∈ s₂, (∏ d ∈ s₃, X a b c d ^ e) ^ e) ^ e) ^ e =
      ∏ a ∈ s₀, ∏ b ∈ s₁, ∏ c ∈ s₂, ∏ d ∈ s₃, X a b c d ^ (e * e * e * e) := by
  refine Finset.prod_congr rfl fun a ha => ?_
  have e₁ : ∀ b ∈ s₁, ∀ c ∈ s₂, (∏ d ∈ s₃, X a b c d ^ e) ^ e = ∏ d ∈ s₃, X a b c d ^ (e * e) :=
    fun b hb c hc => prod_rpow_rpow _ _ _ _ (hX a ha b hb c hc)
  have e₂ : ∀ b ∈ s₁, (∏ c ∈ s₂, (∏ d ∈ s₃, X a b c d ^ e) ^ e) ^ e =
      ∏ c ∈ s₂, ∏ d ∈ s₃, X a b c d ^ (e * e * e) := by
    intro b hb
    rw [Finset.prod_congr rfl (e₁ b hb), ← Real.finsetProd_rpow _ _ (fun c hc =>
      Finset.prod_nonneg fun d hd => Real.rpow_nonneg (hX a ha b hb c hc d hd) _) e]
    exact Finset.prod_congr rfl fun c hc => prod_rpow_rpow _ _ _ _ (hX a ha b hb c hc)
  rw [Finset.prod_congr rfl e₂, ← Real.finsetProd_rpow _ _ (fun b hb =>
    Finset.prod_nonneg fun c hc => Finset.prod_nonneg fun d hd =>
      Real.rpow_nonneg (hX a ha b hb c hc d hd) _) e]
  refine Finset.prod_congr rfl fun b hb => ?_
  rw [← Real.finsetProd_rpow _ _ (fun c hc => Finset.prod_nonneg fun d hd =>
    Real.rpow_nonneg (hX a ha b hb c hc d hd) _) e]
  exact Finset.prod_congr rfl fun c hc => prod_rpow_rpow _ _ _ _ (hX a ha b hb c hc)
theorem vec_coords_eq (j : Fin 4 → ℤ) : ![j 0, j 1, j 2, j 3] = j := by
  funext i
  fin_cases i <;> rfl
theorem vec_mem_cubeIndexBox {k₀ : Fin 4 → ℤ} {n : ℕ} {a b c d : ℤ}
    (ha : a ∈ Finset.Ico (k₀ 0) (k₀ 0 + n)) (hb : b ∈ Finset.Ico (k₀ 1) (k₀ 1 + n))
    (hc : c ∈ Finset.Ico (k₀ 2) (k₀ 2 + n)) (hd : d ∈ Finset.Ico (k₀ 3) (k₀ 3 + n)) :
    ![a, b, c, d] ∈ cubeIndexBox k₀ n := by
  rw [cubeIndexBox, Fintype.mem_piFinset]
  intro μ
  fin_cases μ
  exacts [ha, hb, hc, hd]
theorem prod_cubeIndexBox (k₀ : Fin 4 → ℤ) (n : ℕ) (f : (Fin 4 → ℤ) → ℝ) :
    ∏ j ∈ cubeIndexBox k₀ n, f j =
      ∏ a ∈ Finset.Ico (k₀ 0) (k₀ 0 + n), ∏ b ∈ Finset.Ico (k₀ 1) (k₀ 1 + n),
        ∏ c ∈ Finset.Ico (k₀ 2) (k₀ 2 + n), ∏ d ∈ Finset.Ico (k₀ 3) (k₀ 3 + n),
          f ![a, b, c, d] := by
  simp only [← Finset.prod_product']
  refine Finset.prod_nbij' (fun j => (j 0, j 1, j 2, j 3))
    (fun p => ![p.1, p.2.1, p.2.2.1, p.2.2.2]) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    rw [cubeIndexBox, Fintype.mem_piFinset] at hj
    simp only [Finset.mem_product]
    exact ⟨hj 0, hj 1, hj 2, hj 3⟩
  · intro p hp
    simp only [Finset.mem_product] at hp
    exact vec_mem_cubeIndexBox hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
  · intro j _
    exact vec_coords_eq j
  · intro p _
    rfl
  · intro j _
    rw [vec_coords_eq]
theorem update_mem_cubeIndexBox {k₀ k : Fin 4 → ℤ} {n : ℕ} (hk : k ∈ cubeIndexBox k₀ n) {μ : Fin 4}
    {j : ℤ} (hj : j ∈ Finset.Ico (k₀ μ) (k₀ μ + n)) : Function.update k μ j ∈ cubeIndexBox k₀ n := by
  rw [cubeIndexBox, Fintype.mem_piFinset] at hk ⊢
  intro ν
  by_cases h : ν = μ
  · subst h
    simpa using hj
  · simpa [Function.update_of_ne h] using hk ν
variable {D : ChessboardSetup} (g : ReflectionGrid D)
theorem transportTo_mem (hg : GridBasicProperties.Statement) (x y : Fin 4 → ℤ)
    {G : D.GaugeField → ℂ} (hG : G ∈ ReflectionGrid.cellObservables (D := D) (g.cell x)) :
    g.transportTo (g.cell x) (g.cell y) G ∈ ReflectionGrid.cellObservables (D := D) (g.cell y) := by
  obtain ⟨-, -, -, hc, hr, -⟩ := hg D g
  obtain ⟨-, -, -, -, -, -, hc, -⟩ := hc
  obtain ⟨r, hr', -⟩ := hc _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  exact (hr _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ _ ⟨y, rfl⟩ r hr' G hG G hG 0).1
theorem transportTo_transportTo (hg : GridBasicProperties.Statement) (x y z : Fin 4 → ℤ)
    {G : D.GaugeField → ℂ} (hG : G ∈ ReflectionGrid.cellObservables (D := D) (g.cell x)) :
    g.transportTo (g.cell y) (g.cell z) (g.transportTo (g.cell x) (g.cell y) G) =
      g.transportTo (g.cell x) (g.cell z) G := by
  obtain ⟨-, -, -, hc, hr, -⟩ := hg D g
  obtain ⟨-, -, -, -, -, -, hc, -⟩ := hc
  obtain ⟨r, hr', -⟩ := hc _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  exact (hr _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ _ ⟨z, rfl⟩ r hr' G hG G hG 0).2.2.1
theorem reflectFamily_mem (hg : GridBasicProperties.Statement) {k₀ : Fin 4 → ℤ} {n : ℕ}
    {F : (Fin 4 → ℤ) → D.GaugeField → ℂ}
    (hF : ∀ k ∈ cubeIndexBox k₀ n, F k ∈ ReflectionGrid.cellObservables (D := D) (g.cell k)) {μ : Fin 4}
    {j : ℤ} (hj : j ∈ Finset.Ico (k₀ μ) (k₀ μ + n)) :
    ∀ k ∈ cubeIndexBox k₀ n,
      g.reflectFamily μ j F k ∈ ReflectionGrid.cellObservables (D := D) (g.cell k) :=
  fun _ hk => transportTo_mem g hg _ _ (hF _ (update_mem_cubeIndexBox hk hj))
theorem familyExpectation_congr {k₀ : Fin 4 → ℤ} {n : ℕ} {F F' : (Fin 4 → ℤ) → D.GaugeField → ℂ}
    (h : ∀ k ∈ cubeIndexBox k₀ n, F k = F' k) :
    D.familyExpectation k₀ n F = D.familyExpectation k₀ n F' := by
  unfold ChessboardSetup.familyExpectation
  congr 1
  funext U
  exact Finset.prod_congr rfl fun k hk => by rw [h k hk]
theorem reflectFamily_four (hg : GridBasicProperties.Statement) {k₀ : Fin 4 → ℤ} {n : ℕ}
    {F : (Fin 4 → ℤ) → D.GaugeField → ℂ}
    (hF : ∀ k ∈ cubeIndexBox k₀ n, F k ∈ ReflectionGrid.cellObservables (D := D) (g.cell k)) {a b c d : ℤ}
    (ha : a ∈ Finset.Ico (k₀ 0) (k₀ 0 + n)) (hb : b ∈ Finset.Ico (k₀ 1) (k₀ 1 + n))
    (hc : c ∈ Finset.Ico (k₀ 2) (k₀ 2 + n)) (hd : d ∈ Finset.Ico (k₀ 3) (k₀ 3 + n)) :
    ∀ k ∈ cubeIndexBox k₀ n,
      g.reflectFamily 3 d (g.reflectFamily 2 c (g.reflectFamily 1 b
        (g.reflectFamily 0 a F))) k =
      g.transportedFamily ![a, b, c, d] (F ![a, b, c, d]) k := by
  intro k _
  have hJ : Function.update (Function.update (Function.update (Function.update k 3 d) 2 c) 1 b) 0 a
      = ![a, b, c, d] := by
    funext i
    fin_cases i <;> simp [Function.update]
  have hG := hF _ (vec_mem_cubeIndexBox ha hb hc hd)
  simp only [ReflectionGrid.reflectFamily, ReflectionGrid.transportedFamily]
  rw [hJ, transportTo_transportTo g hg _ _ _ hG, transportTo_transportTo g hg _ _ _ hG,
    transportTo_transportTo g hg _ _ _ hG]
theorem proof (h₁ : OneAxisReflectionBound.Statement)
    (h₂ : GridBasicProperties.Statement) : FamilyChessboardBound.Statement := by
  intro D g hside k₀ n hn F hF
  have hstep := fun (μ : Fin 4) (H : (Fin 4 → ℤ) → D.GaugeField → ℂ) hH =>
    h₁ D g hside k₀ n hn μ H hH
  have he : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  have descend : ∀ (μ : Fin 4) (H : (Fin 4 → ℤ) → D.GaugeField → ℂ),
      (∀ k ∈ cubeIndexBox k₀ n, H k ∈ ReflectionGrid.cellObservables (D := D) (g.cell k)) →
      ∀ B : ℤ → ℝ, (∀ a ∈ Finset.Ico (k₀ μ) (k₀ μ + n),
        ‖D.familyExpectation k₀ n (g.reflectFamily μ a H)‖ ≤ B a) →
      ‖D.familyExpectation k₀ n H‖ ≤ ∏ a ∈ Finset.Ico (k₀ μ) (k₀ μ + n), B a ^ (1 / (n : ℝ)) := by
    intro μ H hH B hB
    obtain ⟨hre, hle⟩ := hstep μ H hH
    refine hle.trans (Finset.prod_le_prod (fun a ha => Real.rpow_nonneg (hre a ha).2 _)
      fun a ha => Real.rpow_le_rpow (hre a ha).2 ?_ he)
    rw [re_eq_norm_of_im_eq_zero _ (hre a ha).1 (hre a ha).2]
    exact hB a ha
  have real : ∀ {a b c d : ℤ}, a ∈ Finset.Ico (k₀ 0) (k₀ 0 + n) →
      b ∈ Finset.Ico (k₀ 1) (k₀ 1 + n) → c ∈ Finset.Ico (k₀ 2) (k₀ 2 + n) →
      d ∈ Finset.Ico (k₀ 3) (k₀ 3 + n) →
      (D.familyExpectation k₀ n (g.transportedFamily ![a, b, c, d] (F ![a, b, c, d]))).im = 0 ∧
        0 ≤ (D.familyExpectation k₀ n (g.transportedFamily ![a, b, c, d] (F ![a, b, c, d]))).re := by
    intro a b c d ha hb hc hd
    rw [← familyExpectation_congr (reflectFamily_four g h₂ hF ha hb hc hd)]
    exact (hstep 3 _ (reflectFamily_mem g h₂ (reflectFamily_mem g h₂
      (reflectFamily_mem g h₂ hF ha) hb) hc)).1 d hd
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [cubeIndexBox, Fintype.mem_piFinset] at hj
    have h := real (hj 0) (hj 1) (hj 2) (hj 3)
    rwa [vec_coords_eq] at h
  · let X : ℤ → ℤ → ℤ → ℤ → ℝ := fun a b c d =>
      (D.familyExpectation k₀ n (g.transportedFamily ![a, b, c, d] (F ![a, b, c, d]))).re
    have hexp : 1 / (n : ℝ) ^ 4 = 1 / (n : ℝ) * (1 / (n : ℝ)) * (1 / (n : ℝ)) * (1 / (n : ℝ)) := by
      ring
    have hfin : ∏ j ∈ cubeIndexBox k₀ n,
        (D.familyExpectation k₀ n (g.transportedFamily j (F j))).re ^ (1 / (n : ℝ) ^ 4) =
        ∏ a ∈ Finset.Ico (k₀ 0) (k₀ 0 + n), ∏ b ∈ Finset.Ico (k₀ 1) (k₀ 1 + n),
          ∏ c ∈ Finset.Ico (k₀ 2) (k₀ 2 + n), ∏ d ∈ Finset.Ico (k₀ 3) (k₀ 3 + n),
            X a b c d ^ (1 / (n : ℝ) * (1 / (n : ℝ)) * (1 / (n : ℝ)) * (1 / (n : ℝ))) := by
      rw [hexp]
      exact prod_cubeIndexBox k₀ n _
    rw [hfin, ← fourfold_prod_rpow _ _ _ _ X (fun a ha b hb c hc d hd => (real ha hb hc hd).2)]
    refine descend 0 F hF _ fun a ha => descend 1 _ (reflectFamily_mem g h₂ hF ha) _
      fun b hb => descend 2 _ (reflectFamily_mem g h₂ (reflectFamily_mem g h₂ hF ha) hb) _
      fun c hc => descend 3 _ (reflectFamily_mem g h₂ (reflectFamily_mem g h₂
        (reflectFamily_mem g h₂ hF ha) hb) hc) _ fun d hd => ?_
    rw [familyExpectation_congr (reflectFamily_four g h₂ hF ha hb hc hd)]
    exact (re_eq_norm_of_im_eq_zero _ (real ha hb hc hd).1 (real ha hb hc hd).2).ge
end YangMills.Construction.ChessboardTori.FamilyChessboardBound
end
