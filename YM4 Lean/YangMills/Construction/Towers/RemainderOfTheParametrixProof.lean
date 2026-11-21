import YangMills.Construction.Towers.BracketsOfTheParametrix
import YangMills.Construction.Towers.MoyalExpansionOfAStarProduct
import YangMills.Construction.Towers.RemainderOfTheParametrix
import YangMills.Construction.Towers.StarProductOfTwoSymbols
import YangMills.Construction.Towers.StarProductWithAConstantMatrix
import YangMills.Construction.Towers.SumsAndProductsOfSymbols
import YangMills.Construction.Towers.SymbolsOfTheParametrix
import Mathlib
set_option autoImplicit false
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.PeriodicOperators (toComplexVec)
noncomputable section
namespace YangMills.Construction.Tower.MagneticWeyl.ApproxInverseRemainderProof
open FluxExpansion SymbolAlgebra
abbrev MatValued (N : ℕ) := AmbientSpace → Matrix (Fin N) (Fin N) ℂ
variable {N : ℕ} [NeZero N]
def NormThreeLE (C : ℝ) (f : MatValued N) : Prop := IsWeylSymbol f ∧ weightedCoeffNorm 3 f ≤ C
def NormZeroLE (C : ℝ) (f : MatValued N) : Prop :=
  HasAbsSummableFourier f ∧ weightedCoeffNorm 0 f ≤ C
theorem hasAbsSummableFourier_of_isWeylSymbol {f : MatValued N} (hf : IsWeylSymbol f) :
    HasAbsSummableFourier f := by
  obtain ⟨c, hc, hs⟩ := hf
  exact ⟨c, hc, by simpa using hs 0 (by norm_num)⟩
theorem NormThreeLE.mono {C D : ℝ} {f : MatValued N} (hf : NormThreeLE C f) (h : C ≤ D) :
    NormThreeLE D f := ⟨hf.1, hf.2.trans h⟩
theorem NormZeroLE.mono {C D : ℝ} {f : MatValued N} (hf : NormZeroLE C f) (h : C ≤ D) :
    NormZeroLE D f := ⟨hf.1, hf.2.trans h⟩
theorem weightedCoeffNorm_three_nonneg (hR : SymbolAlgebra.Claim) {f : MatValued N}
    (hf : IsWeylSymbol f) : 0 ≤ weightedCoeffNorm 3 f :=
  ((hR N N N).2.1.2.2.2 f hf).1 3 (by norm_num)
theorem NormThreeLE.nonneg (hR : SymbolAlgebra.Claim) {C : ℝ} {f : MatValued N}
    (hf : NormThreeLE C f) : 0 ≤ C := (weightedCoeffNorm_three_nonneg hR hf.1).trans hf.2
theorem NormThreeLE.add (hR : SymbolAlgebra.Claim) {C D : ℝ} {f g : MatValued N}
    (hf : NormThreeLE C f) (hg : NormThreeLE D g) : NormThreeLE (C + D) (fun q => f q + g q) := by
  obtain ⟨h1, -, h3⟩ := (hR N N N).2.1.1 f g hf.1 hg.1
  exact ⟨h1, (h3 3 (by norm_num)).trans (add_le_add hf.2 hg.2)⟩
theorem NormThreeLE.smul (hR : SymbolAlgebra.Claim) (c : ℂ) {C : ℝ}
    {f : MatValued N} (hf : NormThreeLE C f) : NormThreeLE (‖c‖ * C) (fun q => c • f q) := by
  obtain ⟨h1, -, h3⟩ := (hR N N N).2.1.2.1 c f hf.1
  exact ⟨h1, (h3 3 (by norm_num)).le.trans (mul_le_mul_of_nonneg_left hf.2 (norm_nonneg c))⟩
theorem NormThreeLE.mul (hR : SymbolAlgebra.Claim) {C D : ℝ} {f g : MatValued N}
    (hf : NormThreeLE C f) (hg : NormThreeLE D g) : NormThreeLE (C * D) (fun q => f q * g q) := by
  obtain ⟨h1, h2, -⟩ := (hR N N N).2.2.1 f g hf.1 hg.1
  exact ⟨h1, (h2 3 (by norm_num)).trans
    (mul_le_mul hf.2 hg.2 (weightedCoeffNorm_three_nonneg hR hg.1) (hf.nonneg hR))⟩
theorem NormZeroLE.of_normThreeLE (hR : SymbolAlgebra.Claim) {C : ℝ}
    {f : MatValued N} (hf : NormThreeLE C f) : NormZeroLE C f :=
  ⟨hasAbsSummableFourier_of_isWeylSymbol hf.1, ((hR N N N).2.1.2.2.2 f hf.1).2.1.trans hf.2⟩
theorem NormZeroLE.add (hR : SymbolAlgebra.Claim) {C D : ℝ} {f g : MatValued N}
    (hf : NormZeroLE C f) (hg : NormZeroLE D g) : NormZeroLE (C + D) (fun q => f q + g q) := by
  obtain ⟨h1, -, h3⟩ := (hR N N N).1.1 f g hf.1 hg.1
  exact ⟨h1, h3.trans (add_le_add hf.2 hg.2)⟩
theorem NormZeroLE.smul (hR : SymbolAlgebra.Claim) (c : ℂ) {C : ℝ}
    {f : MatValued N} (hf : NormZeroLE C f) : NormZeroLE (‖c‖ * C) (fun q => c • f q) := by
  obtain ⟨h1, -, h3⟩ := (hR N N N).1.2 c f hf.1
  exact ⟨h1, h3.le.trans (mul_le_mul_of_nonneg_left hf.2 (norm_nonneg c))⟩
theorem NormZeroLE.zero (hR : SymbolAlgebra.Claim) :
    NormZeroLE 0 (fun _ => 0 : MatValued N) := by
  have hc := hasAbsSummableFourier_of_isWeylSymbol ((hR N N N).2.1.2.2.1 0).1
  have h := (hR N N N).1.2 0 _ hc
  simp only [zero_smul, norm_zero, zero_mul] at h
  exact ⟨h.1, h.2.2.le⟩
theorem NormZeroLE.sum (hR : SymbolAlgebra.Claim) {ι : Type*} (S : Finset ι)
    (C : ι → ℝ) (f : ι → MatValued N) (h : ∀ i ∈ S, NormZeroLE (C i) (f i)) :
    NormZeroLE (∑ i ∈ S, C i) (fun q => ∑ i ∈ S, f i q) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using NormZeroLE.zero hR
  | insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i S)).add hR
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
theorem isWeylSymbol_finsetSum (hR : SymbolAlgebra.Claim) {ι : Type*} (S : Finset ι)
    (c : ι → ℂ) (a : ι → MatValued N) (ha : ∀ i, IsWeylSymbol (a i)) :
    IsWeylSymbol (fun q => ∑ i ∈ S, c i • a i q) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using ((hR N N N).2.1.2.2.1 0).1
  | insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    exact ((hR N N N).2.1.1 _ _ ((hR N N N).2.1.2.1 (c i) (a i) (ha i)).1 ih).1
theorem moyalProduct_finsetSum_left (hR : SymbolAlgebra.Claim) (φ : ℝ) {ι : Type*}
    (S : Finset ι) (c : ι → ℂ) (a : ι → MatValued N) (g : MatValued N)
    (ha : ∀ i, IsWeylSymbol (a i)) (hg : IsWeylSymbol g) :
    moyalProduct φ (fun q => ∑ i ∈ S, c i • a i q) g =
      fun q => ∑ i ∈ S, c i • moyalProduct φ (a i) g q := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have h := ((hR N N N).2.2.2 φ g g g g 0 hg hg hg hg).2.2.1
    simpa using h
  | insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    have hs := isWeylSymbol_finsetSum hR S c a ha
    have hc := ((hR N N N).2.1.2.1 (c i) (a i) (ha i)).1
    have h1 := ((hR N N N).2.2.2 φ (fun q => c i • a i q) (fun q => ∑ j ∈ S, c j • a j q) g g 0
      hc hs hg hg).1
    have h2 := ((hR N N N).2.2.2 φ (a i) (a i) g g (c i) (ha i) (ha i) hg hg).2.2.1
    rw [h1, h2, ih]
theorem moyalProduct_finsetSum_right (hR : SymbolAlgebra.Claim) (φ : ℝ) {ι : Type*}
    (S : Finset ι) (c : ι → ℂ) (a : ι → MatValued N) (g : MatValued N)
    (ha : ∀ i, IsWeylSymbol (a i)) (hg : IsWeylSymbol g) :
    moyalProduct φ g (fun q => ∑ i ∈ S, c i • a i q) =
      fun q => ∑ i ∈ S, c i • moyalProduct φ g (a i) q := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have h := ((hR N N N).2.2.2 φ g g g g 0 hg hg hg hg).2.2.2
    simpa using h
  | insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    have hs := isWeylSymbol_finsetSum hR S c a ha
    have hc := ((hR N N N).2.1.2.1 (c i) (a i) (ha i)).1
    have h1 := ((hR N N N).2.2.2 φ g g (fun q => c i • a i q) (fun q => ∑ j ∈ S, c j • a j q) 0
      hg hg hc hs).2.1
    have h2 := ((hR N N N).2.2.2 φ g g (a i) (a i) (c i) hg hg (ha i) (ha i)).2.2.2
    rw [h1, h2, ih]
def fluxPolynomial (φ : ℝ) (a : Fin 3 → MatValued N) : MatValued N :=
  fun q => ∑ l : Fin 3, ((φ : ℂ) ^ (l : ℕ)) • a l q
theorem normThreeLE_fluxPolynomial (hR : SymbolAlgebra.Claim) {φ C : ℝ} (hφ : |φ| ≤ 1)
    {a : Fin 3 → MatValued N} (h : ∀ l, NormThreeLE C (a l)) :
    NormThreeLE (3 * C) (fluxPolynomial φ a) := by
  have hC := (h 0).nonneg hR
  have hb := (((h 0).smul hR ((φ : ℂ) ^ 0)).add hR ((h 1).smul hR ((φ : ℂ) ^ 1))).add hR
    ((h 2).smul hR ((φ : ℂ) ^ 2))
  have e : fluxPolynomial φ a = fun q => ((φ : ℂ) ^ 0 • a 0 q + (φ : ℂ) ^ 1 • a 1 q) +
      (φ : ℂ) ^ 2 • a 2 q := by
    funext q
    simp [fluxPolynomial, Fin.sum_univ_three]
  rw [e]
  refine hb.mono ?_
  have h1 : ‖(φ : ℂ) ^ 1‖ ≤ 1 := by simpa using hφ
  have h2 : ‖(φ : ℂ) ^ 2‖ ≤ 1 := by
    simpa using pow_le_one₀ (abs_nonneg φ) hφ (n := 2)
  have h0 : ‖(φ : ℂ) ^ 0‖ ≤ 1 := by simp
  nlinarith [mul_le_mul_of_nonneg_right h1 hC, mul_le_mul_of_nonneg_right h2 hC,
    mul_le_mul_of_nonneg_right h0 hC]
def orderTerm (r t : Fin 3 → MatValued N) (l m : Fin 3) : Fin 3 → MatValued N :=
  ![fun q => r l q * t m q,
    fun q => (-(Complex.I / 2)) • poissonBracket (r l) (t m) q,
    fun q => (-(1 / 8 : ℂ)) • secondPoissonBracket (r l) (t m) q]
theorem normZeroLE_orderTerm (hR : SymbolAlgebra.Claim) {Rs Tb : ℝ}
    {r t : Fin 3 → MatValued N} {l m : Fin 3} (hr : NormThreeLE Rs (r l))
    (ht : NormThreeLE Tb (t m)) (k : Fin 3) : NormZeroLE (4 * (Rs * Tb)) (orderTerm r t l m k) := by
  have hRs := hr.nonneg hR
  have hTb := ht.nonneg hR
  have hab : weightedCoeffNorm 3 (r l) * weightedCoeffNorm 3 (t m) ≤ Rs * Tb :=
    mul_le_mul hr.2 ht.2 (weightedCoeffNorm_three_nonneg hR ht.1) hRs
  have hp : 0 ≤ Rs * Tb := mul_nonneg hRs hTb
  obtain ⟨-, -, p3, p4, p5, p6⟩ := (hR N N N).2.2.1 (r l) (t m) hr.1 ht.1
  have hi : ‖(-(Complex.I / 2))‖ ≤ 1 := by simp; norm_num
  have he : ‖(-(1 / 8 : ℂ))‖ ≤ 1 := by simp; norm_num
  fin_cases k
  · exact (NormZeroLE.of_normThreeLE hR (hr.mul hR ht)).mono (by linarith)
  · refine (NormZeroLE.smul hR (-(Complex.I / 2)) (C := 2 * (Rs * Tb)) ⟨p3, ?_⟩).mono ?_
    · nlinarith
    · nlinarith
  · refine (NormZeroLE.smul hR (-(1 / 8 : ℂ)) (C := 4 * (Rs * Tb)) ⟨p5, ?_⟩).mono ?_
    · nlinarith
    · nlinarith
theorem regroup_by_order {M : Type*} [AddCommGroup M] [Module ℂ M] (c s : ℂ) (u : M)
    (W : Fin 3 → Fin 3 → Fin 3 → M) (r : Fin 3 → M)
    (e0 : W 0 0 0 + s • r 0 = u)
    (e1 : W 0 1 0 + W 1 0 0 + W 0 0 1 + s • r 1 = 0)
    (e2 : W 0 2 0 + W 1 1 0 + W 2 0 0 + W 0 1 1 + W 1 0 1 + W 0 0 2 + s • r 2 = 0) :
    (∑ l : Fin 3, ∑ m : Fin 3, c ^ ((l : ℕ) + (m : ℕ)) • ∑ k : Fin 3, c ^ (k : ℕ) • W l m k) +
        s • ∑ l : Fin 3, c ^ (l : ℕ) • r l =
      u + ∑ l : Fin 3, ∑ m : Fin 3, ∑ k : Fin 3,
        (if 3 ≤ (l : ℕ) + (m : ℕ) + (k : ℕ) then c ^ ((l : ℕ) + (m : ℕ) + (k : ℕ)) else 0) •
          W l m k := by
  simp only [Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two]
  norm_num
  linear_combination (norm := module) e0 + c • e1 + c ^ 2 • e2
theorem double_sum_split {M : Type*} [AddCommGroup M] [Module ℂ M] (c : ℂ)
    (A B : Fin 3 → Fin 3 → M) :
    ∑ l : Fin 3, c ^ (l : ℕ) • ∑ m : Fin 3, c ^ (m : ℕ) • (A l m + B l m) =
      (∑ l : Fin 3, ∑ m : Fin 3, c ^ ((l : ℕ) + (m : ℕ)) • A l m) +
        ∑ l : Fin 3, ∑ m : Fin 3, c ^ ((l : ℕ) + (m : ℕ)) • B l m := by
  simp only [Finset.smul_sum, smul_add, Finset.sum_add_distrib, smul_smul, pow_add]
def moyalTail (φ : ℝ) (a b : MatValued N) (q : AmbientSpace) : Matrix (Fin N) (Fin N) ℂ :=
  moyalProduct φ a b q - a q * b q + (Complex.I / 2 * (φ : ℂ)) • poissonBracket a b q +
    ((1 / 8 : ℂ) * (φ : ℂ) ^ 2) • secondPoissonBracket a b q
omit [NeZero N] in
theorem moyalProduct_eq_orderTerms (φ : ℝ) (r t : Fin 3 → MatValued N) (l m : Fin 3)
    (q : AmbientSpace) :
    moyalProduct φ (r l) (t m) q =
      (∑ k : Fin 3, (φ : ℂ) ^ (k : ℕ) • orderTerm r t l m k q) + moyalTail φ (r l) (t m) q := by
  have h0 : orderTerm r t l m 0 q = r l q * t m q := rfl
  have h1 : orderTerm r t l m 1 q = (-(Complex.I / 2)) • poissonBracket (r l) (t m) q := rfl
  have h2 : orderTerm r t l m 2 q = (-(1 / 8 : ℂ)) • secondPoissonBracket (r l) (t m) q := rfl
  rw [Fin.sum_univ_three, h0, h1, h2]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, moyalTail]
  module
theorem norm_highOrderCoeff {φ : ℝ} (hφ : |φ| ≤ 1) (n : ℕ) :
    ‖(if 3 ≤ n then (φ : ℂ) ^ n else 0)‖ ≤ |φ| ^ 3 := by
  split_ifs with h
  · simpa using pow_le_pow_of_le_one (abs_nonneg φ) hφ h
  · simp
theorem product_expansion (hR : SymbolAlgebra.Claim)
    (hS : MoyalProductBounds) (hM : MoyalRemainderBound)
    (hC : MoyalProductWithConstant)
    (r t : Fin 3 → MatValued N) {Rs Tb φ s : ℝ} (hr : ∀ l, NormThreeLE Rs (r l))
    (ht : ∀ m, NormThreeLE Tb (t m)) (hφ : |φ| ≤ 1) (σr : MatValued N) (hσ : IsWeylSymbol σr)
    (e0 : ∀ q, r 0 q * t 0 q + (s : ℂ) • r 0 q = 1)
    (e1 : ∀ q, r 0 q * t 1 q + r 1 q * t 0 q + (-(Complex.I / 2)) • poissonBracket (r 0) (t 0) q +
      (s : ℂ) • r 1 q = 0)
    (e2 : ∀ q, r 0 q * t 2 q + r 1 q * t 1 q + r 2 q * t 0 q +
      (-(Complex.I / 2)) • poissonBracket (r 0) (t 1) q +
      (-(Complex.I / 2)) • poissonBracket (r 1) (t 0) q +
      (-(1 / 8 : ℂ)) • secondPoissonBracket (r 0) (t 0) q + (s : ℂ) • r 2 q = 0) :
    ∃ e : MatValued N, IsWeylSymbol e ∧
      moyalProduct φ (fluxPolynomial φ r)
          (fun q => (fluxPolynomial φ t q + σr q) + (s : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) =
        (fun q => 1 + e q) ∧
      weightedCoeffNorm 0 e ≤
        (108 + 3 / 16) * (|φ| ^ 3 * (Rs * Tb)) + 3 * Rs * weightedCoeffNorm 3 σr := by
  have hRs : 0 ≤ Rs := (hr 0).nonneg hR
  have hTb : 0 ≤ Tb := (ht 0).nonneg hR
  have hρ := normThreeLE_fluxPolynomial hR hφ hr
  have hτ := normThreeLE_fluxPolynomial hR hφ ht
  have hrs : ∀ l, IsWeylSymbol (r l) := fun l => (hr l).1
  have hts : ∀ m, IsWeylSymbol (t m) := fun m => (ht m).1
  obtain ⟨ρ, hρe⟩ : ∃ ρ, ρ = fluxPolynomial φ r := ⟨_, rfl⟩
  obtain ⟨τ, hτe⟩ : ∃ τ, τ = fluxPolynomial φ t := ⟨_, rfl⟩
  rw [← hρe, ← hτe]
  rw [← hρe] at hρ
  rw [← hτe] at hτ
  obtain ⟨cst, hcste⟩ : ∃ cst : Matrix (Fin N) (Fin N) ℂ,
    cst = (s : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) := ⟨_, rfl⟩
  rw [← hcste]
  have hcst : IsWeylSymbol (fun _ : AmbientSpace => cst) := ((hR N N N).2.1.2.2.1 cst).1
  have hT : IsWeylSymbol (fun q => τ q + σr q) := ((hR N N N).2.1.1 τ σr hτ.1 hσ).1
  have hTall : IsWeylSymbol (fun q => (τ q + σr q) + cst) :=
    ((hR N N N).2.1.1 _ _ hT hcst).1
  have hs1 := ((hR N N N).2.2.2 φ ρ ρ (fun q => τ q + σr q) (fun _ => cst) 0
    hρ.1 hρ.1 hT hcst).2.1
  have hs2 := ((hR N N N).2.2.2 φ ρ ρ τ σr 0 hρ.1 hρ.1 hτ.1 hσ).2.1
  have hs3 : moyalProduct φ ρ (fun _ => cst) = fun q => ρ q * cst :=
    (hC φ N N ρ hρ.1 N).1 cst
  have hs4 : ∀ q, moyalProduct φ ρ τ q = ∑ l : Fin 3, ((φ : ℂ) ^ (l : ℕ)) •
      ∑ m : Fin 3, ((φ : ℂ) ^ (m : ℕ)) • moyalProduct φ (r l) (t m) q := by
    intro q
    have a1 : moyalProduct φ ρ τ = fun q => ∑ l : Fin 3, ((φ : ℂ) ^ (l : ℕ)) •
        moyalProduct φ (r l) τ q := by
      rw [hρe]
      exact moyalProduct_finsetSum_left hR φ Finset.univ _ r τ hrs hτ.1
    have a2 : ∀ l, moyalProduct φ (r l) τ = fun q => ∑ m : Fin 3, ((φ : ℂ) ^ (m : ℕ)) •
        moyalProduct φ (r l) (t m) q := by
      intro l
      rw [hτe]
      exact moyalProduct_finsetSum_right hR φ Finset.univ _ t (r l) hts (hrs l)
    rw [a1]
    simp only [a2]
  obtain ⟨H, hHe⟩ : ∃ H : MatValued N, H = fun q => ∑ l : Fin 3, ∑ m : Fin 3, ∑ k : Fin 3,
      (if 3 ≤ (l : ℕ) + (m : ℕ) + (k : ℕ) then (φ : ℂ) ^ ((l : ℕ) + (m : ℕ) + (k : ℕ)) else 0) •
        orderTerm r t l m k q := ⟨_, rfl⟩
  obtain ⟨Rm, hRme⟩ : ∃ Rm : MatValued N, Rm = fun q => ∑ l : Fin 3, ∑ m : Fin 3,
      (φ : ℂ) ^ ((l : ℕ) + (m : ℕ)) • moyalTail φ (r l) (t m) q := ⟨_, rfl⟩
  have hid : ∀ q, moyalProduct φ ρ (fun q => (τ q + σr q) + cst) q =
      1 + (H q + Rm q + moyalProduct φ ρ σr q) := by
    intro q
    have key := regroup_by_order (φ : ℂ) (s : ℂ) (1 : Matrix (Fin N) (Fin N) ℂ)
      (fun l m k => orderTerm r t l m k q) (fun l => r l q) (e0 q) (e1 q) (e2 q)
    have hρq : ρ q = ∑ l : Fin 3, ((φ : ℂ) ^ (l : ℕ)) • r l q := by rw [hρe]; rfl
    have hsq : ρ q * cst = (s : ℂ) • ρ q := by
      rw [hcste, mul_smul_comm, mul_one]
    have hsplit := double_sum_split (φ : ℂ)
      (fun l m => ∑ k : Fin 3, (φ : ℂ) ^ (k : ℕ) • orderTerm r t l m k q)
      (fun l m => moyalTail φ (r l) (t m) q)
    rw [hs1, hs2, hs3]
    simp only []
    rw [hs4 q]
    simp only [moyalProduct_eq_orderTerms φ r t]
    rw [hsplit, hsq, hρq, hHe, hRme]
    simp only []
    linear_combination (norm := module) key
  have hsym : IsWeylSymbol (moyalProduct φ ρ (fun q => (τ q + σr q) + cst)) :=
    (hS φ N N N ρ _ hρ.1 hTall).2.2.1
  refine ⟨fun q => moyalProduct φ ρ (fun q => (τ q + σr q) + cst) q +
    (-1 : Matrix (Fin N) (Fin N) ℂ),
    ((hR N N N).2.1.1 _ (fun _ => -1) hsym ((hR N N N).2.1.2.2.1 _).1).1, ?_, ?_⟩
  · have hx : ∀ x : Matrix (Fin N) (Fin N) ℂ, x = 1 + (x + -1) := fun x => by abel
    funext q
    exact hx _
  have he : (fun q => moyalProduct φ ρ (fun q => (τ q + σr q) + cst) q +
      (-1 : Matrix (Fin N) (Fin N) ℂ)) = fun q => (H q + Rm q) + moyalProduct φ ρ σr q := by
    funext q
    rw [hid q]
    abel
  rw [he]
  have hA : 0 ≤ |φ| ^ 3 := by positivity
  have hH : NormZeroLE (∑ _l : Fin 3, ∑ _m : Fin 3, ∑ _k : Fin 3, |φ| ^ 3 * (4 * (Rs * Tb))) H := by
    rw [hHe]
    refine NormZeroLE.sum hR Finset.univ _ _ fun l _ => NormZeroLE.sum hR Finset.univ _ _ fun m _ =>
      NormZeroLE.sum hR Finset.univ _ _ fun k _ => ?_
    refine ((normZeroLE_orderTerm hR (hr l) (ht m) k).smul hR _).mono ?_
    exact mul_le_mul_of_nonneg_right (norm_highOrderCoeff hφ _) (by positivity)
  have hRm : NormZeroLE (∑ _l : Fin 3, ∑ _m : Fin 3, 1 / 48 * |φ| ^ 3 * (Rs * Tb)) Rm := by
    rw [hRme]
    refine NormZeroLE.sum hR Finset.univ _ _ fun l _ =>
      NormZeroLE.sum hR Finset.univ _ _ fun m _ => ?_
    obtain ⟨m1, m2⟩ := hM φ N N N (r l) (t m) (hrs l) (hts m) (moyalTail φ (r l) (t m))
      (fun q => rfl)
    have hab : weightedCoeffNorm 3 (r l) * weightedCoeffNorm 3 (t m) ≤ Rs * Tb :=
      mul_le_mul (hr l).2 (ht m).2 (weightedCoeffNorm_three_nonneg hR (hts m)) hRs
    have hb : NormZeroLE (1 / 48 * |φ| ^ 3 * (Rs * Tb)) (moyalTail φ (r l) (t m)) := by
      refine ⟨m1, m2.trans ?_⟩
      rw [mul_assoc (1 / 48 * |φ| ^ 3)]
      exact mul_le_mul_of_nonneg_left hab (by positivity)
    refine (hb.smul hR ((φ : ℂ) ^ ((l : ℕ) + (m : ℕ)))).mono ?_
    have hc : ‖(φ : ℂ) ^ ((l : ℕ) + (m : ℕ))‖ ≤ 1 := by
      simpa using pow_le_one₀ (abs_nonneg φ) hφ (n := (l : ℕ) + (m : ℕ))
    exact mul_le_of_le_one_left (by positivity) hc
  have hQ : NormZeroLE (3 * Rs * weightedCoeffNorm 3 σr) (moyalProduct φ ρ σr) := by
    obtain ⟨-, -, q3, -, q5⟩ := hS φ N N N ρ σr hρ.1 hσ
    exact NormZeroLE.of_normThreeLE hR ⟨q3, (q5 3 (by norm_num)).trans
      (mul_le_mul_of_nonneg_right hρ.2 (weightedCoeffNorm_three_nonneg hR hσ))⟩
  refine ((hH.add hR hRm).add hR hQ).2.trans (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring
theorem shiftedInverse_mul {s : ℝ} (hs : 0 < s) (q : AmbientSpace) :
    shiftedInverse s q * (baseSymbol q + s) = 1 := by
  obtain ⟨p, hp, hn⟩ : ∃ p : ℝ, baseSymbol q = p ∧ 0 ≤ p :=
    ⟨∑ μ, (2 - 2 * Real.cos (q μ)),
      by simp [baseSymbol, Massive.latticeSymbol, Massive.axisSymbol, toComplexVec],
      Finset.sum_nonneg fun μ _ => by linarith [Real.cos_le_one (q μ)]⟩
  have hne : baseSymbol q + s ≠ 0 := by
    rw [hp]
    exact_mod_cast (ne_of_gt (by linarith : 0 < p + s))
  exact inv_mul_cancel₀ hne
omit [NeZero N] in
theorem relation_order_zero {s : ℝ} (hs : 0 < s) (q : AmbientSpace) :
    termZero N s q * baseSymbolMatrix N q + (s : ℂ) • termZero N s q = 1 := by
  have h := shiftedInverse_mul hs q
  simp only [termZero, baseSymbolMatrix, mul_smul_comm, mul_one]
  linear_combination (norm := module) h • (1 : Matrix (Fin N) (Fin N) ℂ)
omit [NeZero N] in
theorem relation_order_one {s : ℝ} (hs : 0 < s) (σ₁ : MatValued N) (q : AmbientSpace)
    (hb : poissonBracket (termZero N s) (baseSymbolMatrix N) q = 0) :
    termZero N s q * σ₁ q + termOne s σ₁ q * baseSymbolMatrix N q +
      (-(Complex.I / 2)) • poissonBracket (termZero N s) (baseSymbolMatrix N) q +
      (s : ℂ) • termOne s σ₁ q = 0 := by
  have h := shiftedInverse_mul hs q
  rw [hb]
  simp only [termZero, termOne, baseSymbolMatrix, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
    smul_zero, add_zero]
  linear_combination (norm := module) (-(shiftedInverse s q) * h) • σ₁ q
omit [NeZero N] in
theorem relation_order_two {s : ℝ} (hs : 0 < s) (σ₁ σ₂ : MatValued N) (q : AmbientSpace)
    (hb : poissonBracket (termOne s σ₁) (baseSymbolMatrix N) q +
      poissonBracket (termZero N s) σ₁ q = 0)
    (hc : secondPoissonBracket (termZero N s) (baseSymbolMatrix N) q =
      (shiftedInverseSecondDeriv s 0 q * baseSymbolSecondDeriv 1 q +
        shiftedInverseSecondDeriv s 1 q * baseSymbolSecondDeriv 0 q) •
        (1 : Matrix (Fin N) (Fin N) ℂ)) :
    termZero N s q * σ₂ q + termOne s σ₁ q * σ₁ q + termTwo s σ₁ σ₂ q * baseSymbolMatrix N q +
      (-(Complex.I / 2)) • poissonBracket (termZero N s) σ₁ q +
      (-(Complex.I / 2)) • poissonBracket (termOne s σ₁) (baseSymbolMatrix N) q +
      (-(1 / 8 : ℂ)) • secondPoissonBracket (termZero N s) (baseSymbolMatrix N) q +
      (s : ℂ) • termTwo s σ₁ σ₂ q = 0 := by
  have h := shiftedInverse_mul hs q
  rw [hc]
  simp only [termZero, termOne, termTwo, baseSymbolMatrix, smul_mul_assoc, mul_smul_comm, one_mul,
    mul_one, pow_two (σ₁ q)]
  linear_combination (norm := module)
    h • (shiftedInverse s q ^ 2 • (σ₁ q * σ₁ q) - shiftedInverse s q • σ₂ q +
      ((1 / 8 : ℂ) * (shiftedInverseSecondDeriv s 0 q * baseSymbolSecondDeriv 1 q +
        shiftedInverseSecondDeriv s 1 q * baseSymbolSecondDeriv 0 q)) •
        (1 : Matrix (Fin N) (Fin N) ℂ)) + (-(Complex.I / 2)) • hb
def secondDerivBound (y Sμ Fμ : ℝ) : ℝ := y * (y * Sμ) + 2 * (y * (y * (y * (Fμ * Fμ))))
def innerTermBound (y a b : ℝ) (S F : Fin 4 → ℝ) : ℝ :=
  y * (y * (a * a)) + y * b +
    1 / 8 * (secondDerivBound y (S 0) (F 0) * S 1 + secondDerivBound y (S 1) (F 1) * S 0)
theorem normThreeLE_shiftedInverseSecondDeriv (hR : SymbolAlgebra.Claim) {s y Sμ Fμ : ℝ}
    (μ : Fin 4) (hy : NormThreeLE y (termZero N s))
    (hS : NormThreeLE Sμ (fun q => baseSymbolSecondDeriv μ q • (1 : Matrix (Fin N) (Fin N) ℂ)))
    (hF : NormThreeLE Fμ (fun q => baseSymbolDeriv μ q • (1 : Matrix (Fin N) (Fin N) ℂ))) :
    NormThreeLE (secondDerivBound y Sμ Fμ)
      (fun q => shiftedInverseSecondDeriv s μ q • (1 : Matrix (Fin N) (Fin N) ℂ)) := by
  have hb := ((hy.mul hR (hy.mul hR hS)).smul hR (-1)).add hR
    ((hy.mul hR (hy.mul hR (hy.mul hR (hF.mul hR hF)))).smul hR 2)
  have e : (fun q => shiftedInverseSecondDeriv s μ q • (1 : Matrix (Fin N) (Fin N) ℂ)) =
      fun q => (-1 : ℂ) • (termZero N s q * (termZero N s q *
          (baseSymbolSecondDeriv μ q • (1 : Matrix (Fin N) (Fin N) ℂ)))) +
        (2 : ℂ) • (termZero N s q * (termZero N s q * (termZero N s q *
          ((baseSymbolDeriv μ q • (1 : Matrix (Fin N) (Fin N) ℂ)) *
            (baseSymbolDeriv μ q • (1 : Matrix (Fin N) (Fin N) ℂ)))))) := by
    funext q
    simp only [termZero, shiftedInverseSecondDeriv, mul_smul_comm, mul_one]
    module
  rw [e]
  refine hb.mono (le_of_eq ?_)
  simp [secondDerivBound]
theorem normThreeLE_termOne (hR : SymbolAlgebra.Claim) {s u y a : ℝ}
    {σ₁ : MatValued N} (hu : NormThreeLE u (termZero N s)) (hy : NormThreeLE y (termZero N s))
    (hA : NormThreeLE a σ₁) : NormThreeLE (u * (y * a)) (termOne s σ₁) := by
  have hb := (hu.mul hR (hy.mul hR hA)).smul hR (-1)
  have e : termOne s σ₁ = fun q => (-1 : ℂ) • (termZero N s q * (termZero N s q * σ₁ q)) := by
    funext q
    simp only [termZero, termOne, smul_mul_assoc, one_mul]
    module
  rw [e]
  exact hb.mono (le_of_eq (by simp))
theorem normThreeLE_termTwo (hR : SymbolAlgebra.Claim) {s u y a b : ℝ}
    {S F : Fin 4 → ℝ} {σ₁ σ₂ : MatValued N} (hu : NormThreeLE u (termZero N s))
    (hy : NormThreeLE y (termZero N s)) (hA : NormThreeLE a σ₁) (hB : NormThreeLE b σ₂)
    (hS : ∀ μ, NormThreeLE (S μ)
      (fun q => baseSymbolSecondDeriv μ q • (1 : Matrix (Fin N) (Fin N) ℂ)))
    (hF : ∀ μ, NormThreeLE (F μ)
      (fun q => baseSymbolDeriv μ q • (1 : Matrix (Fin N) (Fin N) ℂ))) :
    NormThreeLE (u * innerTermBound y a b S F) (termTwo s σ₁ σ₂) := by
  have h0 := normThreeLE_shiftedInverseSecondDeriv hR 0 hy (hS 0) (hF 0)
  have h1 := normThreeLE_shiftedInverseSecondDeriv hR 1 hy (hS 1) (hF 1)
  have hb := hu.mul hR
    (((hy.mul hR (hy.mul hR (hA.mul hR hA))).add hR ((hy.mul hR hB).smul hR (-1))).add hR
      (((h0.mul hR (hS 1)).add hR (h1.mul hR (hS 0))).smul hR (1 / 8)))
  have e : termTwo s σ₁ σ₂ = fun q => termZero N s q *
      ((termZero N s q * (termZero N s q * (σ₁ q * σ₁ q)) + (-1 : ℂ) • (termZero N s q * σ₂ q)) +
        (1 / 8 : ℂ) • ((shiftedInverseSecondDeriv s 0 q • (1 : Matrix (Fin N) (Fin N) ℂ)) *
            (baseSymbolSecondDeriv 1 q • (1 : Matrix (Fin N) (Fin N) ℂ)) +
          (shiftedInverseSecondDeriv s 1 q • (1 : Matrix (Fin N) (Fin N) ℂ)) *
            (baseSymbolSecondDeriv 0 q • (1 : Matrix (Fin N) (Fin N) ℂ)))) := by
    funext q
    simp only [termZero, termTwo, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
      pow_two (σ₁ q)]
    module
  rw [e]
  refine hb.mono (le_of_eq ?_)
  simp [innerTermBound]
set_option maxHeartbeats 2000000 in
theorem approxInverseRemainder_holds (hR : SymbolAlgebra.Claim)
    (hP : ApproxInverseSymbolBounds) (hB : FluxExpansionBrackets) (hM : MoyalRemainderBound)
    (hS : MoyalProductBounds) (hC : MoyalProductWithConstant) :
    ApproxInverseRemainder := by
  intro N _ z hz σ₁ σ₂ h₁ h₂
  obtain ⟨hψ, -, hder, hup⟩ := hP N
  obtain ⟨K₀, hK₀, hK⟩ := hup z hz
  obtain ⟨y, hye⟩ : ∃ y, y = K₀ / z := ⟨_, rfl⟩
  obtain ⟨a, hae⟩ : ∃ a, a = weightedCoeffNorm 3 σ₁ := ⟨_, rfl⟩
  obtain ⟨b, hbe⟩ : ∃ b, b = weightedCoeffNorm 3 σ₂ := ⟨_, rfl⟩
  obtain ⟨S, hSe⟩ : ∃ S : Fin 4 → ℝ, S = fun μ =>
    weightedCoeffNorm 3 (fun q => baseSymbolSecondDeriv μ q • (1 : Matrix (Fin N) (Fin N) ℂ)) :=
    ⟨_, rfl⟩
  obtain ⟨F, hFe⟩ : ∃ F : Fin 4 → ℝ, F = fun μ =>
    weightedCoeffNorm 3 (fun q => baseSymbolDeriv μ q • (1 : Matrix (Fin N) (Fin N) ℂ)) :=
    ⟨_, rfl⟩
  have hA : NormThreeLE a σ₁ := ⟨h₁, hae.ge⟩
  have hBd : NormThreeLE b σ₂ := ⟨h₂, hbe.ge⟩
  have hSb : ∀ μ, NormThreeLE (S μ)
      (fun q => baseSymbolSecondDeriv μ q • (1 : Matrix (Fin N) (Fin N) ℂ)) := fun μ =>
    ⟨(hder μ).2.1, by rw [hSe]⟩
  have hFb : ∀ μ, NormThreeLE (F μ)
      (fun q => baseSymbolDeriv μ q • (1 : Matrix (Fin N) (Fin N) ℂ)) := fun μ =>
    ⟨(hder μ).1.1, by rw [hFe]⟩
  have hy0 : 0 ≤ y := by rw [hye]; positivity
  have ha0 : 0 ≤ a := hA.nonneg hR
  have hb0 : 0 ≤ b := hBd.nonneg hR
  have hS0 : ∀ μ, 0 ≤ S μ := fun μ => (hSb μ).nonneg hR
  have hF0 : ∀ μ, 0 ≤ F μ := fun μ => (hFb μ).nonneg hR
  have hsb : ∀ μ, 0 ≤ secondDerivBound y (S μ) (F μ) := fun μ => by
    have := hS0 μ
    have := hF0 μ
    unfold secondDerivBound
    positivity
  have hI0 : 0 ≤ innerTermBound y a b S F := by
    have h0 := hsb 0
    have h1 := hsb 1
    have h2 := hS0 0
    have h3 := hS0 1
    unfold innerTermBound
    positivity
  obtain ⟨W, hWe⟩ : ∃ W, W = 1 + y * a + innerTermBound y a b S F := ⟨_, rfl⟩
  have hya0 : 0 ≤ y * a := mul_nonneg hy0 ha0
  have hW0 : 0 ≤ W := by rw [hWe]; positivity
  obtain ⟨R, hRe⟩ : ∃ R, R = K₀ * W := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by rw [hRe]; positivity
  have hψ3 : NormThreeLE (weightedCoeffNorm 3 (baseSymbolMatrix N)) (baseSymbolMatrix N) :=
    ⟨hψ.1, le_rfl⟩
  obtain ⟨Tb, hTe⟩ : ∃ Tb, Tb = weightedCoeffNorm 3 (baseSymbolMatrix N) + a + b := ⟨_, rfl⟩
  have hp0 : 0 ≤ weightedCoeffNorm 3 (baseSymbolMatrix N) := hψ3.nonneg hR
  have hT0 : 0 ≤ Tb := by rw [hTe]; positivity
  refine ⟨109 * R * Tb + 3 * R, by positivity, ?_⟩
  intro s φ hs hφ σr hσ
  have hs0 : 0 < s := hz.trans_le hs
  have hY : NormThreeLE (K₀ / s) (termZero N s) := hK s hs
  have hYy : NormThreeLE y (termZero N s) := hY.mono (by
    rw [hye]
    exact div_le_div_of_nonneg_left hK₀ hz hs)
  have hu0 : 0 ≤ K₀ / s := by positivity
  have hscale : ∀ X, X ≤ W → K₀ / s * X ≤ R / s := fun X hX => by
    refine (mul_le_mul_of_nonneg_left hX hu0).trans (le_of_eq ?_)
    rw [hRe]
    ring
  have hr : ∀ l, NormThreeLE (R / s)
      ((![termZero N s, termOne s σ₁, termTwo s σ₁ σ₂] : Fin 3 → MatValued N) l) := by
    intro l
    fin_cases l
    · refine hY.mono ?_
      have := hscale 1 (by rw [hWe]; linarith)
      simpa using this
    · exact (normThreeLE_termOne hR hY hYy hA).mono (hscale _ (by rw [hWe]; linarith))
    · exact (normThreeLE_termTwo hR hY hYy hA hBd hSb hFb).mono (hscale _ (by rw [hWe]; linarith))
  have ht : ∀ m, NormThreeLE Tb
      ((![baseSymbolMatrix N, σ₁, σ₂] : Fin 3 → MatValued N) m) := by
    intro m
    fin_cases m
    · exact hψ3.mono (by rw [hTe]; linarith)
    · exact hA.mono (by rw [hTe]; linarith)
    · exact hBd.mono (by rw [hTe]; linarith)
  obtain ⟨e, he1, he2, he3⟩ := product_expansion hR hS hM hC
    (![termZero N s, termOne s σ₁, termTwo s σ₁ σ₂] : Fin 3 → MatValued N)
    (![baseSymbolMatrix N, σ₁, σ₂] : Fin 3 → MatValued N) hr ht hφ σr hσ
    (fun q => relation_order_zero hs0 q)
    (fun q => relation_order_one hs0 σ₁ q (hB N s hs0 σ₁ h₁ q).1)
    (fun q => relation_order_two hs0 σ₁ σ₂ q (hB N s hs0 σ₁ h₁ q).2.1 (hB N s hs0 σ₁ h₁ q).2.2)
  have eρ : approxInverse s φ σ₁ σ₂ =
      fluxPolynomial φ (![termZero N s, termOne s σ₁, termTwo s σ₁ σ₂] : Fin 3 → MatValued N) := by
    funext q
    simp [approxInverse, fluxPolynomial, Fin.sum_univ_three]
  have eτ : fluxPolynomial φ (![baseSymbolMatrix N, σ₁, σ₂] : Fin 3 → MatValued N) =
      fun q => baseSymbolMatrix N q + (φ : ℂ) • σ₁ q + (φ : ℂ) ^ 2 • σ₂ q := by
    funext q
    simp [fluxPolynomial, Fin.sum_univ_three]
  have hρ := normThreeLE_fluxPolynomial hR hφ hr
  rw [eτ] at he2
  rw [eρ]
  refine ⟨hρ.1, e, he1, he2, he3.trans ?_⟩
  have hA3 : 0 ≤ |φ| ^ 3 := by positivity
  have hn : 0 ≤ weightedCoeffNorm 3 σr := weightedCoeffNorm_three_nonneg hR hσ
  have hx : 0 ≤ R / s := by positivity
  have e' : (109 * R * Tb + 3 * R) * (|φ| ^ 3 + weightedCoeffNorm 3 σr) / s =
      (109 * (R / s) * Tb + 3 * (R / s)) * (|φ| ^ 3 + weightedCoeffNorm 3 σr) := by ring
  rw [e']
  nlinarith [mul_nonneg (mul_nonneg hx hT0) hA3, mul_nonneg (mul_nonneg hx hT0) hn,
    mul_nonneg hx hA3]
end YangMills.Construction.Tower.MagneticWeyl.ApproxInverseRemainderProof
end
