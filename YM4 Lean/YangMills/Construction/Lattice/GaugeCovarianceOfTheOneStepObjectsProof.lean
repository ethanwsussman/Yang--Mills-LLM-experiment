import YangMills.Construction.Lattice.AveragingMapIsABorelMapProof
import YangMills.Construction.Lattice.GaugeCovarianceOfTheOneStepObjects
import YangMills.Construction.Lattice.GaugeCovarianceOfTheTwoSchemes
import YangMills.Construction.Lattice.KernelsOnPositiveBondFamilies
import YangMills.Construction.Lattice.NormExpAndGaugeTransport
import YangMills.Construction.Lattice.PathsOfBlocksAndDoubleBlocks
import YangMills.Construction.Matrices.LinearMapsCompositesAndCoordinatesOfRealAnalyticMapsProof
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.Matrices
namespace PeriodicLattice.StepObjectsCovarianceProof
variable {L m K n : ℕ}
theorem inv_mul_cancel_of_mem {g : ComplexMatrix2} (hg : g ∈ ComplexMatrix2.specialUnitary) :
    g⁻¹ * g = 1 := by apply _root_.YangMills.SharedProofs.p1227 <;> assumption
theorem mul_inv_cancel_of_mem {g : ComplexMatrix2} (hg : g ∈ ComplexMatrix2.specialUnitary) :
    g * g⁻¹ = 1 := by apply _root_.YangMills.SharedProofs.p21267 <;> assumption
theorem inv_inv_eq_of_mem {g : ComplexMatrix2} (hg : g ∈ ComplexMatrix2.specialUnitary) :
    g⁻¹⁻¹ = g := by apply _root_.YangMills.SharedProofs.p318 <;> assumption
theorem sandwich_mul_sandwich {p : ComplexMatrix2} (hp : p ∈ ComplexMatrix2.specialUnitary)
    (g A B k : ComplexMatrix2) :
    g * A * p⁻¹ * (p * B * k) = g * (A * B) * k := by
  calc g * A * p⁻¹ * (p * B * k) = g * A * (p⁻¹ * p) * B * k := by simp only [mul_assoc]
    _ = g * (A * B) * k := by
        rw [inv_mul_cancel_of_mem hp, mul_one]
        simp only [mul_assoc]
theorem sandwich_mul_inv_sandwich {g k : ComplexMatrix2}
    (hk : k ∈ ComplexMatrix2.specialUnitary) (A B : ComplexMatrix2) :
    (g * A * k⁻¹) * (g * B * k⁻¹)⁻¹ = g * (A * B⁻¹) * g⁻¹ := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, inv_inv_eq_of_mem hk]
  calc g * A * k⁻¹ * (k * (B⁻¹ * g⁻¹)) = g * A * (k⁻¹ * k) * (B⁻¹ * g⁻¹) := by
        simp only [mul_assoc]
    _ = g * (A * B⁻¹) * g⁻¹ := by
        rw [inv_mul_cancel_of_mem hk, mul_one]
        simp only [mul_assoc]
theorem sandwich_inv {g k : ComplexMatrix2} (hk : k ∈ ComplexMatrix2.specialUnitary)
    (A : ComplexMatrix2) :
    (g * A * k⁻¹)⁻¹ = k * A⁻¹ * g⁻¹ := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, inv_inv_eq_of_mem hk]
  simp only [mul_assoc]
theorem sandwich_product {g k : ComplexMatrix2} (hg : g ∈ ComplexMatrix2.specialUnitary)
    (hk : k ∈ ComplexMatrix2.specialUnitary) (v M w N : ComplexMatrix2) :
    (g * v * g⁻¹)⁻¹ * (g * M * k⁻¹) * (k * w * k⁻¹) * (g * N * k⁻¹)⁻¹ =
      g * (v⁻¹ * M * w * N⁻¹) * g⁻¹ := by
  rw [sandwich_inv hg v, sandwich_inv hk N, sandwich_mul_sandwich hg, sandwich_mul_sandwich hk,
    sandwich_mul_sandwich hk]
theorem conj_finsum_mem {g : ComplexMatrix2} (hg : g ∈ ComplexMatrix2.specialUnitary)
    {ι : Type*} (S : Set ι) (f : ι → ComplexMatrix2) :
    g * (∑ᶠ x ∈ S, f x) * g⁻¹ = ∑ᶠ x ∈ S, g * f x * g⁻¹ := by
  let e : ComplexMatrix2 ≃+ ComplexMatrix2 :=
    { toFun := fun X => g * X * g⁻¹
      invFun := fun X => g⁻¹ * X * g
      left_inv := fun X => by
        change g⁻¹ * (g * X * g⁻¹) * g = X
        calc g⁻¹ * (g * X * g⁻¹) * g = (g⁻¹ * g) * X * (g⁻¹ * g) := by simp only [mul_assoc]
          _ = X := by rw [inv_mul_cancel_of_mem hg, one_mul, mul_one]
      right_inv := fun X => by
        change g * (g⁻¹ * X * g) * g⁻¹ = X
        calc g * (g⁻¹ * X * g) * g⁻¹ = (g * g⁻¹) * X * (g * g⁻¹) := by simp only [mul_assoc]
          _ = X := by rw [mul_inv_cancel_of_mem hg, one_mul, mul_one]
      map_add' := fun X Y => by
        change g * (X + Y) * g⁻¹ = g * X * g⁻¹ + g * Y * g⁻¹
        rw [mul_add, add_mul] }
  classical
  rw [finsum_mem_def, finsum_mem_def]
  change e (∑ᶠ x, S.indicator f x) = _
  rw [AddEquiv.map_finsum]
  refine finsum_congr fun x => ?_
  by_cases hx : x ∈ S
  · simp only [Set.indicator_of_mem hx]
    rfl
  · simp only [Set.indicator_of_notMem hx, map_zero]
theorem conj_list_sum (g : ComplexMatrix2) {ι : Type*} (f : ι → ComplexMatrix2) (l : List ι) :
    g * (l.map f).sum * g⁻¹ = (l.map fun b => g * f b * g⁻¹).sum := by
  induction l with
  | nil => simp
  | cons b l ih =>
      simp only [List.map_cons, List.sum_cons, mul_add, add_mul]
      rw [ih]
theorem pathHolonomy_gaugeTransform_forwardFlow {j : ℤ} (u : Site L m j → ComplexMatrix2)
    (hu : ∀ x, u x ∈ ComplexMatrix2.specialUnitary)
    (W : Bond L m j → ComplexMatrix2) (μ : Fin 4) (t : ℕ) :
    ∀ x : Site L m j, pathHolonomy (_root_.YangMills.Construction.PeriodicLattice.gaugeTransform u W) (forwardAxisPath x μ t) =
      u x * pathHolonomy W (forwardAxisPath x μ t) * (u (x + (t : ℤ) • unitStep L m j μ))⁻¹ := by
  induction t with
  | zero =>
      intro x
      simp [forwardAxisPath, pathHolonomy, mul_inv_cancel_of_mem (hu x)]
  | succ t ih =>
      intro x
      have e : x + unitStep L m j μ + (t : ℤ) • unitStep L m j μ =
          x + ((t + 1 : ℕ) : ℤ) • unitStep L m j μ := by
        push_cast
        rw [add_smul, one_smul]
        abel
      have h := ih (x + unitStep L m j μ)
      rw [e] at h
      simp only [pathHolonomy, forwardAxisPath, List.map_cons, List.prod_cons] at h ⊢
      rw [h]
      simp only [_root_.YangMills.Construction.PeriodicLattice.gaugeTransform, Bond.forwardFrom]
      rw [sandwich_mul_sandwich (hu _), mul_assoc (u x)]
theorem pathHolonomy_gaugeTransform_backwardFlow {j : ℤ} (u : Site L m j → ComplexMatrix2)
    (hu : ∀ x, u x ∈ ComplexMatrix2.specialUnitary)
    (W : Bond L m j → ComplexMatrix2) (μ : Fin 4) (t : ℕ) :
    ∀ x : Site L m j, pathHolonomy (_root_.YangMills.Construction.PeriodicLattice.gaugeTransform u W) (backwardAxisPath x μ t) =
      u x * pathHolonomy W (backwardAxisPath x μ t) * (u (x - (t : ℤ) • unitStep L m j μ))⁻¹ := by
  induction t with
  | zero =>
      intro x
      simp [backwardAxisPath, pathHolonomy, mul_inv_cancel_of_mem (hu x)]
  | succ t ih =>
      intro x
      have e : x - unitStep L m j μ - (t : ℤ) • unitStep L m j μ =
          x - ((t + 1 : ℕ) : ℤ) • unitStep L m j μ := by
        push_cast
        rw [add_smul, one_smul]
        abel
      have h := ih (x - unitStep L m j μ)
      rw [e] at h
      simp only [pathHolonomy, backwardAxisPath, List.map_cons, List.prod_cons] at h ⊢
      rw [h]
      simp only [_root_.YangMills.Construction.PeriodicLattice.gaugeTransform, Bond.backwardFrom]
      rw [sandwich_mul_sandwich (hu _), mul_assoc (u x)]
theorem pathHolonomy_gaugeTransform_axialPath {j : ℤ} (u : Site L m j → ComplexMatrix2)
    (hu : ∀ x, u x ∈ ComplexMatrix2.specialUnitary)
    (W : Bond L m j → ComplexMatrix2) {x x' : Site L m j}
    (hd : ∃ q : Fin 4 × ℤ, IsAxialDisplacement x x' q.1 q.2) :
    pathHolonomy (_root_.YangMills.Construction.PeriodicLattice.gaugeTransform u W) (axialPath x x') =
      u x * pathHolonomy W (axialPath x x') * (u x')⁻¹ := by
  have hspec := hd.choose_spec.1
  unfold axialPath
  rw [dif_pos hd]
  generalize hd.choose = q at hspec ⊢
  obtain ⟨μ, k⟩ := q
  simp only at hspec ⊢
  unfold flowAlong
  by_cases hk : 0 ≤ k
  · rw [if_pos hk, _root_.YangMills.Construction.PeriodicLattice.StepObjectsCovarianceProof.pathHolonomy_gaugeTransform_forwardFlow u hu W μ _ x]
    have e : x + (k.toNat : ℤ) • unitStep L m j μ = x' := by
      rw [Int.toNat_of_nonneg hk, ← hspec]
      abel
    rw [e]
  · rw [if_neg hk, _root_.YangMills.Construction.PeriodicLattice.StepObjectsCovarianceProof.pathHolonomy_gaugeTransform_backwardFlow u hu W μ _ x]
    have e : x - ((-k).toNat : ℤ) • unitStep L m j μ = x' := by
      rw [Int.toNat_of_nonneg (by omega), neg_smul, ← hspec]
      abel
    rw [e]
theorem mem_forwardFlow {j : ℤ} {μ : Fin 4} {b : Bond L m j} (t : ℕ) :
    ∀ x : Site L m j, b ∈ forwardAxisPath x μ t →
      ∃ i : ℕ, i < t ∧ b = Bond.forwardFrom (x + (i : ℤ) • unitStep L m j μ) μ := by
  induction t with
  | zero =>
      intro x hb
      simp [forwardAxisPath] at hb
  | succ t ih =>
      intro x hb
      rw [forwardAxisPath, List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact ⟨0, by omega, by simp⟩
      · obtain ⟨i, hi, rfl⟩ := ih _ hb
        refine ⟨i + 1, by omega, ?_⟩
        have e : x + unitStep L m j μ + (i : ℤ) • unitStep L m j μ =
            x + ((i + 1 : ℕ) : ℤ) • unitStep L m j μ := by
          push_cast
          rw [add_smul, one_smul]
          abel
        rw [e]
theorem eval_of_conj {P : SymmetricBondSet L m K n} {a a' : LieBondField P}
    {u : SiteAtLevel L m K n → ComplexMatrix2}
    (ha : ∀ b : PositiveBondsOf P,
      (a' b : ComplexMatrix2) = ComplexMatrix2.conjugateBy (u b.1.source) (a b : ComplexMatrix2))
    {b : BondAtLevel L m K n} (hp : b.IsPositivelyOriented) :
    (a'.eval b : ComplexMatrix2) =
      ComplexMatrix2.conjugateBy (u b.source) (a.eval b : ComplexMatrix2) := by
  by_cases hb : b ∈ P.bonds
  · simp only [LieBondField.eval]
    rw [dif_pos (⟨hb, hp⟩ : b ∈ P.bonds ∧ b.IsPositivelyOriented),
      dif_pos (⟨hb, hp⟩ : b ∈ P.bonds ∧ b.IsPositivelyOriented)]
    exact ha ⟨b, hb, hp⟩
  · have h₁ : ¬ (b ∈ P.bonds ∧ b.IsPositivelyOriented) := fun x => hb x.1
    have h₂ : ¬ (b.opposite ∈ P.bonds ∧ b.opposite.IsPositivelyOriented) :=
      fun x => hb (P.opposite_mem _ x.1)
    simp only [LieBondField.eval]
    rw [dif_neg h₁, dif_neg h₂, dif_neg h₁, dif_neg h₂]
    simp [ComplexMatrix2.conjugateBy]
theorem twistedConfig_of_pos (c : BondAtLevel L m K (n + 1))
    (a : LieBondField (doubleBlockSymmetricSet c)) (W : BondAtLevel L m K n → ComplexMatrix2)
    {b : BondAtLevel L m K n} (hb : b.IsPositivelyOriented) :
    twistedConfig c a W b =
      ComplexMatrix2.matExp (Complex.I • (a.eval b : ComplexMatrix2)) * W b := by
  simp only [twistedConfig, expTwist, if_pos hb]
theorem twistedConfig_of_not_pos (c : BondAtLevel L m K (n + 1))
    (a : LieBondField (doubleBlockSymmetricSet c)) (W : BondAtLevel L m K n → ComplexMatrix2)
    {b : BondAtLevel L m K n} (hb : ¬ b.IsPositivelyOriented) :
    twistedConfig c a W b =
      (ComplexMatrix2.matExp (Complex.I • (a.eval b.opposite : ComplexMatrix2)) *
        W b.opposite)⁻¹ := by
  simp only [twistedConfig, expTwist, if_neg hb]
theorem matExp_conj_mul_sandwich (hM : NormExpAndGaugeTransport) {g : ComplexMatrix2}
    (hg : g ∈ ComplexMatrix2.specialUnitary) (A W k : ComplexMatrix2) :
    ComplexMatrix2.matExp (Complex.I • ComplexMatrix2.conjugateBy g A) * (g * W * k) =
      g * (ComplexMatrix2.matExp (Complex.I • A) * W) * k := by
  have e : Complex.I • ComplexMatrix2.conjugateBy g A = g * (Complex.I • A) * g⁻¹ := by
    simp only [ComplexMatrix2.conjugateBy, Matrix.mul_smul, Matrix.smul_mul]
  rw [e, (hM.2.2.2 g hg).1, sandwich_mul_sandwich hg]
theorem gaugeTransform_twistedConfig (hM : NormExpAndGaugeTransport)
    (c : BondAtLevel L m K (n + 1)) {a a' : LieBondField (doubleBlockSymmetricSet c)}
    (W₀ : BondAtLevel L m K n → ComplexMatrix2) {u : SiteAtLevel L m K n → ComplexMatrix2}
    (hu : ∀ x, u x ∈ ComplexMatrix2.specialUnitary)
    (ha : ∀ b : PositiveBondsOf (doubleBlockSymmetricSet c),
      (a' b : ComplexMatrix2) = ComplexMatrix2.conjugateBy (u b.1.source) (a b : ComplexMatrix2)) :
    _root_.YangMills.Construction.PeriodicLattice.gaugeTransform u (twistedConfig c a W₀) =
      twistedConfig c a' (_root_.YangMills.Construction.PeriodicLattice.gaugeTransform u W₀) := by
  have pos : ∀ {b : BondAtLevel L m K n}, b.IsPositivelyOriented →
      twistedConfig c a' (_root_.YangMills.Construction.PeriodicLattice.gaugeTransform u W₀) b =
        u b.source * twistedConfig c a W₀ b * (u b.target)⁻¹ := by
    intro b hb
    rw [twistedConfig_of_pos c _ _ hb, twistedConfig_of_pos c _ _ hb, eval_of_conj ha hb]
    exact matExp_conj_mul_sandwich hM (hu b.source) _ _ _
  funext b
  by_cases hb : b.IsPositivelyOriented
  · exact (pos hb).symm
  · have hr : b.opposite.IsPositivelyOriented := Bond.opposite_isPositivelyOriented hb
    have e := pos hr
    rw [twistedConfig_of_pos c _ _ hr] at e
    have e₂ : twistedConfig c a W₀ b = (twistedConfig c a W₀ b.opposite)⁻¹ := by
      rw [twistedConfig_of_not_pos c a W₀ hb, twistedConfig_of_pos c a W₀ hr]
    rw [twistedConfig_of_not_pos c _ _ hb, e, sandwich_inv (hu b.opposite.target)]
    change u b.source * twistedConfig c a W₀ b * (u b.target)⁻¹ = _
    rw [e₂]
    rfl
theorem twistedConfig_isGaugeField (hM : NormExpAndGaugeTransport)
    (hnb : ∀ b : BondAtLevel L m K n, b.IsPositivelyOriented →
      ¬ b.opposite.IsPositivelyOriented)
    (c : BondAtLevel L m K (n + 1)) (a : LieBondField (doubleBlockSymmetricSet c))
    (W₀ : BondAtLevel L m K n → ComplexMatrix2)
    (hW : IsGaugeField complexGaugeGroup (bondsInDoubleBlock c) W₀) :
    IsGaugeField complexGaugeGroup (bondsInDoubleBlock c) (twistedConfig c a W₀) := by
  have hdet : ∀ b ∈ bondsInDoubleBlock c,
      (ComplexMatrix2.matExp (Complex.I • (a.eval b : ComplexMatrix2)) * W₀ b).det = 1 := by
    intro b hb
    have h₁ : (ComplexMatrix2.matExp (Complex.I • (a.eval b : ComplexMatrix2))).det = 1 :=
      hM.2.1.1 _ (a.eval b).2
    have h₂ : (W₀ b).det = 1 := hW.1 b hb
    rw [Matrix.det_mul, h₁, h₂, one_mul]
  have hrev : ∀ b ∈ bondsInDoubleBlock c, b.opposite ∈ bondsInDoubleBlock c :=
    fun b hb => (doubleBlockSymmetricSet c).opposite_mem b hb
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · by_cases hp : b.IsPositivelyOriented
    · rw [twistedConfig_of_pos c a W₀ hp]
      exact hdet b hb
    · rw [twistedConfig_of_not_pos c a W₀ hp]
      change (_ : ComplexMatrix2)⁻¹.det = 1
      rw [Matrix.det_nonsing_inv, hdet _ (hrev b hb)]
      simp
  · by_cases hp : b.IsPositivelyOriented
    · rw [twistedConfig_of_pos c a W₀ hp, twistedConfig_of_not_pos c a W₀ (hnb b hp)]
      rfl
    · have hr := Bond.opposite_isPositivelyOriented hp
      rw [twistedConfig_of_pos c a W₀ hr, twistedConfig_of_not_pos c a W₀ hp]
      exact (Matrix.nonsing_inv_nonsing_inv _
        (by rw [hdet _ (hrev b hb)]; exact isUnit_one)).symm
theorem conjugateBy_sandwich {g k : ComplexMatrix2} (hk : k ∈ ComplexMatrix2.specialUnitary)
    (T A : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy (g * T * k⁻¹) (ComplexMatrix2.conjugateBy k A) =
      g * ComplexMatrix2.conjugateBy T A * g⁻¹ := by
  simp only [ComplexMatrix2.conjugateBy]
  rw [sandwich_inv hk]
  calc g * T * k⁻¹ * (k * A * k⁻¹) * (k * T⁻¹ * g⁻¹)
      = g * T * (k⁻¹ * k) * A * (k⁻¹ * k) * T⁻¹ * g⁻¹ := by simp only [mul_assoc]
    _ = g * (T * A * T⁻¹) * g⁻¹ := by
        rw [inv_mul_cancel_of_mem hk, mul_one, mul_one]
        simp only [mul_assoc]
theorem axialDisplacement_of_lt (hL : 13 ≤ L) (hm : 0 < m) (hn : n < K)
    (x : SiteAtLevel L m K n) (μ : Fin 4) {i : ℕ} (hi : i < L) :
    ∃ q : Fin 4 × ℤ,
      IsAxialDisplacement x (x + (i : ℤ) • unitStep L m (levelDepth K n) μ) q.1 q.2 := by
  refine ⟨(μ, (i : ℤ)), by simp, ?_⟩
  have hL' : (1 : ℝ) ≤ (L : ℝ) := by
    have : 1 ≤ L := by omega
    exact_mod_cast this
  have h₁ : (L : ℝ) ^ (1 : ℤ) ≤ (L : ℝ) ^ ((m : ℤ) + levelDepth K n) :=
    zpow_le_zpow_right₀ hL' (by simp only [levelDepth]; omega)
  rw [zpow_one] at h₁
  have h₂ : ((|(i : ℤ)| : ℤ) : ℝ) = (i : ℝ) := by
    rw [abs_of_nonneg (by omega)]
    simp
  simp only
  rw [h₂]
  have h₃ : (i : ℝ) < (L : ℝ) := by exact_mod_cast hi
  linarith
theorem straightenedMap_gaugeTransform (hP : BlockPaths.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hn : n < K)
    (s : AveragingScheme) (c : BondAtLevel L m K (n + 1)) (hc : c.IsPositivelyOriented)
    (W₀ : BondAtLevel L m K n → ComplexMatrix2)
    {a a' : LieBondField (doubleBlockSymmetricSet c)} {u : SiteAtLevel L m K n → ComplexMatrix2}
    (hu : ∀ x, u x ∈ ComplexMatrix2.specialUnitary)
    (ha : ∀ b : PositiveBondsOf (doubleBlockSymmetricSet c),
      (a' b : ComplexMatrix2) = ComplexMatrix2.conjugateBy (u b.1.source) (a b : ComplexMatrix2))
    (hcont : ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
      contourHolonomy s (_root_.YangMills.Construction.PeriodicLattice.gaugeTransform u W₀) c.source x =
        u (schemeBaseSite s (levelDepth K n) c.source) * contourHolonomy s W₀ c.source x *
          (u x)⁻¹) :
    straightenedMap s c (_root_.YangMills.Construction.PeriodicLattice.gaugeTransform u W₀) a' =
      ComplexMatrix2.conjugateBy (u (schemeBaseSite s (levelDepth K n) c.source))
        (straightenedMap s c W₀ a) := by
  obtain ⟨μ, hμ⟩ := hc
  have hS := ((hP L m K hL.1 hL.2 hm n hn).2 c μ hμ).2.2.2.1.1
  have hg := hu (schemeBaseSite s (levelDepth K n) c.source)
  have hw : ∀ (w : ℂ) (S : ComplexMatrix2),
      ComplexMatrix2.conjugateBy (u (schemeBaseSite s (levelDepth K n) c.source)) (w • S) =
        w • (u (schemeBaseSite s (levelDepth K n) c.source) * S *
          (u (schemeBaseSite s (levelDepth K n) c.source))⁻¹) := by
    intro w S
    simp only [ComplexMatrix2.conjugateBy, Matrix.mul_smul, Matrix.smul_mul]
  unfold straightenedMap
  rw [hw, conj_finsum_mem hg]
  congr 1
  refine finsum_mem_congr rfl fun x hx => ?_
  rw [conj_list_sum]
  refine congrArg List.sum (List.map_congr_left fun b hb => ?_)
  rw [(hS x hx).2.1] at hb
  obtain ⟨i, hi, rfl⟩ := mem_forwardFlow L x hb
  have hp : (Bond.forwardFrom (x + (i : ℤ) • unitStep L m (levelDepth K n) μ) μ).IsPositivelyOriented :=
    ⟨μ, by simp [Bond.forwardFrom]⟩
  have hd : ∃ q : Fin 4 × ℤ, IsAxialDisplacement x
      (Bond.forwardFrom (x + (i : ℤ) • unitStep L m (levelDepth K n) μ) μ).source q.1 q.2 :=
    axialDisplacement_of_lt hL.2 hm hn x μ hi
  rw [hcont x hx, _root_.YangMills.Construction.PeriodicLattice.StepObjectsCovarianceProof.pathHolonomy_gaugeTransform_axialPath u hu W₀ hd, eval_of_conj ha hp,
    sandwich_mul_sandwich (hu x)]
  exact conjugateBy_sandwich (hu _) _ _
theorem stepObjectsGaugeCovariance_holds (hcov : GaugeCovarianceStatement)
    (hM : NormExpAndGaugeTransport)
    (hP : BlockPaths.Statement) :
    StepObjectsGaugeCovariance := by
  intro L hL m K n hm hn s c hc W₀ a a' u hu ha hW
  have hsu : ∀ x, u x ∈ ComplexMatrix2.specialUnitary := hu
  have hg := _root_.YangMills.Construction.PeriodicLattice.StepObjectsCovarianceProof.gaugeTransform_twistedConfig hM c W₀ hsu ha
  have hC := twistedConfig_isGaugeField hM
    (fun b hb => Bond.opposite_not_isPositivelyOriented (by have := hL.2; omega)
      (by simp only [levelDepth]; omega) hb) c a W₀ hW
  have cW := hcov L hL m K n hm hn s c hc u W₀ (fun x _ => hsu x) hW
  have cP := hcov L hL m K n hm hn s c hc u _ (fun x _ => hsu x) hC
  have contourP : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
      ∀ x ∈ sitesInBlock (levelDepth K n) y,
      IsContourHolonomyDefined s (twistedConfig c a W₀) y x →
        IsContourHolonomyDefined s (twistedConfig c a' (gaugeTransform u W₀)) y x ∧
          contourHolonomy s (twistedConfig c a' (_root_.YangMills.Construction.PeriodicLattice.gaugeTransform u W₀)) y x =
            u (schemeBaseSite s (levelDepth K n) y) *
              contourHolonomy s (twistedConfig c a W₀) y x * (u x)⁻¹ := by
    intro y hy x hx d
    have := cP.contour y hy x hx d
    rwa [hg] at this
  have averageP : IsSchemeAverageDefined s (twistedConfig c a W₀) c →
      IsSchemeAverageDefined s (twistedConfig c a' (_root_.YangMills.Construction.PeriodicLattice.gaugeTransform u W₀)) c ∧
        schemeBlockAverage s (twistedConfig c a' (_root_.YangMills.Construction.PeriodicLattice.gaugeTransform u W₀)) c =
          u (schemeBaseSite s (levelDepth K n) c.source) *
            schemeBlockAverage s (twistedConfig c a W₀) c *
              (u (schemeBaseSite s (levelDepth K n) c.target))⁻¹ := by
    intro d
    have := cP.average d
    rw [hg] at this
    exact this
  have ratio : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
      ∀ x ∈ sitesInBlock (levelDepth K n) y,
      IsContourHolonomyDefined s (twistedConfig c a W₀) y x →
      IsContourHolonomyDefined s W₀ y x →
        IsContourHolonomyDefined s (twistedConfig c a' (gaugeTransform u W₀)) y x ∧
          IsContourHolonomyDefined s (_root_.YangMills.Construction.PeriodicLattice.gaugeTransform u W₀) y x ∧
            stepRatio s c a' (_root_.YangMills.Construction.PeriodicLattice.gaugeTransform u W₀) y x =
              u (schemeBaseSite s (levelDepth K n) y) * stepRatio s c a W₀ y x *
                (u (schemeBaseSite s (levelDepth K n) y))⁻¹ := by
    intro y hy x hx dP dW
    obtain ⟨dP', eP⟩ := contourP y hy x hx dP
    obtain ⟨dW', eW⟩ := cW.contour y hy x hx dW
    refine ⟨dP', dW', ?_⟩
    simp only [stepRatio]
    rw [eP, eW]
    exact sandwich_mul_inv_sandwich (hsu x) _ _
  have logF : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
      ∀ x ∈ sitesInBlock (levelDepth K n) y, IsContourRatioLogDefined s c a W₀ y x →
        IsContourRatioLogDefined s c a' (_root_.YangMills.Construction.PeriodicLattice.gaugeTransform u W₀) y x ∧
          stepLog s c a' (_root_.YangMills.Construction.PeriodicLattice.gaugeTransform u W₀) y x =
            ComplexMatrix2.conjugateBy (u (schemeBaseSite s (levelDepth K n) y))
              (stepLog s c a W₀ y x) := by
    rintro y hy x hx ⟨dP, dW, nr⟩
    obtain ⟨dP', dW', e⟩ := ratio y hy x hx dP dW
    have hl := (hM.2.2.2 _ (hsu (schemeBaseSite s (levelDepth K n) y))).2 _ nr
    refine ⟨⟨dP', dW', ?_⟩, ?_⟩
    · rw [e]
      exact hl.1
    · simp only [stepLog]
      rw [e, hl.2]
      simp only [ComplexMatrix2.conjugateBy, Matrix.mul_smul, Matrix.smul_mul]
  have gaugeF : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
      IsStepGaugeDefined s c a W₀ y →
        IsStepGaugeDefined s c a' (_root_.YangMills.Construction.PeriodicLattice.gaugeTransform u W₀) y ∧
          stepGauge s c a' (_root_.YangMills.Construction.PeriodicLattice.gaugeTransform u W₀) y =
            u (schemeBaseSite s (levelDepth K n) y) * stepGauge s c a W₀ y *
              (u (schemeBaseSite s (levelDepth K n) y))⁻¹ := by
    intro y hy F
    refine ⟨fun x hx => (logF y hy x hx (F x hx)).1, ?_⟩
    have hgy := hsu (schemeBaseSite s (levelDepth K n) y)
    have hs : (∑ᶠ x ∈ sitesInBlock (levelDepth K n) y,
          stepLog s c a' (_root_.YangMills.Construction.PeriodicLattice.gaugeTransform u W₀) y x) =
        u (schemeBaseSite s (levelDepth K n) y) *
          (∑ᶠ x ∈ sitesInBlock (levelDepth K n) y, stepLog s c a W₀ y x) *
            (u (schemeBaseSite s (levelDepth K n) y))⁻¹ := by
      rw [conj_finsum_mem hgy]
      exact finsum_mem_congr rfl fun x hx => (logF y hy x hx (F x hx)).2
    simp only [stepGauge]
    rw [hs, ← (hM.2.2.2 _ hgy).1]
    simp only [Matrix.mul_smul, Matrix.smul_mul]
  have ht : c.source ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))) := Or.inl rfl
  have hh : c.target ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))) := Or.inr rfl
  refine ⟨fun b _ => congrFun hg b, logF, gaugeF, ?_, ?_⟩
  · rintro ⟨⟨⟨vP, vP'⟩, ⟨vW, vW'⟩, r₁, r₂⟩, aP, aW, nr⟩
    have FT : IsStepGaugeDefined s c a W₀ c.source := fun x hx => ⟨vP x hx, vW x hx, r₁ x hx⟩
    have FH : IsStepGaugeDefined s c a W₀ c.target := fun x hx => ⟨vP' x hx, vW' x hx, r₂ x hx⟩
    obtain ⟨gt, et⟩ := gaugeF _ ht FT
    obtain ⟨gh, eh⟩ := gaugeF _ hh FH
    obtain ⟨fP', eP⟩ := averageP aP
    have fW' : IsSchemeAverageDefined s (_root_.YangMills.Construction.PeriodicLattice.gaugeTransform u W₀) c := (cW.average aW).1
    have eW : schemeBlockAverage s (_root_.YangMills.Construction.PeriodicLattice.gaugeTransform u W₀) c =
        u (schemeBaseSite s (levelDepth K n) c.source) * schemeBlockAverage s W₀ c *
          (u (schemeBaseSite s (levelDepth K n) c.target))⁻¹ := (cW.average aW).2
    have e : stepProduct s c a' (_root_.YangMills.Construction.PeriodicLattice.gaugeTransform u W₀) =
        u (schemeBaseSite s (levelDepth K n) c.source) * stepProduct s c a W₀ *
          (u (schemeBaseSite s (levelDepth K n) c.source))⁻¹ := by
      simp only [stepProduct]
      rw [et, eh, eP, eW]
      exact sandwich_product (hsu _) (hsu _) _ _ _ _
    have hl := (hM.2.2.2 _ (hsu (schemeBaseSite s (levelDepth K n) c.source))).2 _ nr
    refine ⟨⟨⟨⟨fun x hx => (gt x hx).1, fun x hx => (gh x hx).1⟩,
      ⟨fun x hx => (gt x hx).2.1, fun x hx => (gh x hx).2.1⟩,
      fun x hx => (gt x hx).2.2, fun x hx => (gh x hx).2.2⟩, fP', fW', ?_⟩, ?_⟩
    · rw [e]
      exact hl.1
    · simp only [stepVariable]
      rw [e, hl.2]
      simp only [ComplexMatrix2.conjugateBy, Matrix.mul_smul, Matrix.smul_mul]
  · intro d
    exact ⟨fun x hx => (cW.contour c.source ht x hx (d x hx)).1,
      _root_.YangMills.Construction.PeriodicLattice.StepObjectsCovarianceProof.straightenedMap_gaugeTransform hP hL hm hn s c hc W₀ hsu ha
        fun x hx => (cW.contour c.source ht x hx (d x hx)).2⟩
end PeriodicLattice.StepObjectsCovarianceProof
end YangMills.Construction
