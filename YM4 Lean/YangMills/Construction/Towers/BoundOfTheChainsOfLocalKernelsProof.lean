import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflectionsProof
import YangMills.Construction.Towers.BoundOfTheChainsOfLocalKernels
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
open TorusMetric (euclidNormVec)
namespace Tower.LocalFamilies.LoopTermsEstimate
variable {J : Type}
theorem euclidNormVec_nonneg (v : Fin 4 → ℝ) : 0 ≤ euclidNormVec v := Real.sqrt_nonneg _
theorem euclidNormVec_zero : euclidNormVec (0 : Fin 4 → ℝ) = 0 := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_zero <;> assumption
theorem euclidNormVec_add_le (v w : Fin 4 → ℝ) :
    euclidNormVec (v + w) ≤ euclidNormVec v + euclidNormVec w := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_add_le <;> assumption
theorem abs_apply_le_euclidNormVec (v : Fin 4 → ℝ) (μ : Fin 4) : |v μ| ≤ euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
def expLineSeries (b : ℝ) : ℝ≥0∞ := ∑' k : ℤ, ENNReal.ofReal (Real.exp (-(b * |(k : ℝ)|)))
theorem expLineSeries_ne_top {b : ℝ} (hb : 0 < b) : expLineSeries b ≠ ∞ := by
  refine Summable.tsum_ofReal_ne_top ?_
  have hgeo : Summable fun n : ℕ => Real.exp (-b) ^ n :=
    summable_geometric_of_lt_one (Real.exp_pos _).le (by simpa using hb)
  have hnat : ∀ n : ℕ, Real.exp (-(b * |(n : ℝ)|)) = Real.exp (-b) ^ n := fun n => by
    rw [← Real.exp_nat_mul, Nat.abs_cast]
    congr 1
    ring
  refine Summable.of_nat_of_neg (f := fun k : ℤ => Real.exp (-(b * |(k : ℝ)|))) ?_ ?_
  · refine hgeo.congr fun n => ?_
    simp only [Int.cast_natCast]
    exact (hnat n).symm
  · refine hgeo.congr fun n => ?_
    simp only [Int.cast_neg, Int.cast_natCast, abs_neg]
    exact (hnat n).symm
theorem tsum_pi_prod_eq_pow (h : ℤ → ℝ≥0∞) (d : ℕ) :
    ∑' v : Fin d → ℤ, ∏ μ, h (v μ) = (∑' k, h k) ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (d + 1) => ℤ)).tsum_eq, ENNReal.tsum_prod']
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
      ENNReal.tsum_mul_left, ih, ENNReal.tsum_mul_right]
    rw [pow_succ']
theorem tsum_exp_castVec_le {δ : ℝ} (hδ : 0 < δ) :
    ∑' n : Fin 4 → ℤ,
        ENNReal.ofReal (Real.exp (-(δ * euclidNormVec (PeriodicOperators.castVec n)))) ≤
      expLineSeries (δ / 4) ^ 4 := by
  rw [expLineSeries, ← tsum_pi_prod_eq_pow]
  refine ENNReal.tsum_le_tsum fun n => ?_
  rw [← ENNReal.ofReal_prod_of_nonneg fun _ _ => (Real.exp_pos _).le, ← Real.exp_sum]
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have hcoord : ∀ μ : Fin 4, |((n μ : ℤ) : ℝ)| ≤ euclidNormVec (PeriodicOperators.castVec n) :=
    fun μ => abs_apply_le_euclidNormVec (PeriodicOperators.castVec n) μ
  have hsum : ∑ μ : Fin 4, (δ / 4) * |((n μ : ℤ) : ℝ)| ≤
      δ * euclidNormVec (PeriodicOperators.castVec n) := by
    calc _ ≤ ∑ _μ : Fin 4, (δ / 4) * euclidNormVec (PeriodicOperators.castVec n) :=
          Finset.sum_le_sum fun μ _ => mul_le_mul_of_nonneg_left (hcoord μ) (by positivity)
      _ = _ := by simp; ring
  simp only [Finset.sum_neg_distrib]
  linarith
theorem tsum_const_le_of_ncard_le {P : Set J} {m : ℕ} (hf : P.Finite) (hc : P.ncard ≤ m)
    (a : ℝ≥0∞) : ∑' _ : P, a ≤ m * a := by
  rw [ENNReal.tsum_set_const]
  refine mul_le_mul_left ?_ a
  rw [← hf.cast_ncard_eq]
  exact_mod_cast hc
theorem tsum_exp_placement_le {x : J → InfiniteLattice.AmbientSpace} {m : ℕ}
    (h : IsIntegerPlacement x m) {δ : ℝ} (hδ : 0 < δ) (j' : J) :
    ∑' j, ENNReal.ofReal (Real.exp (-(δ * euclidNormVec (x j' - x j)))) ≤
      m * expLineSeries (δ / 4) ^ 4 := by
  choose k hk using h.on_lattice
  let G : (Fin 4 → ℤ) → ℝ≥0∞ := fun d =>
    ENNReal.ofReal (Real.exp (-(δ * euclidNormVec (PeriodicOperators.castVec (k j' - d)))))
  have hG : ∀ j, ENNReal.ofReal (Real.exp (-(δ * euclidNormVec (x j' - x j)))) =
      G (k j) := fun j => by
    have : x j' - x j = PeriodicOperators.castVec (k j' - k j) := by
      rw [hk j', hk j]
      funext μ
      simp [PeriodicOperators.castVec]
    simp only [G, this]
  simp_rw [hG]
  have hfib : ∀ d : Fin 4 → ℤ, ∑' j : {j | k j = d}, G (k j) ≤ m * G d := fun d => by
    have hsub : {j | k j = d} ⊆ {j | x j = PeriodicOperators.castVec d} := fun j hj => by
      have hj' : k j = d := hj
      simp only [Set.mem_ofPred_eq, hk j, hj']
    have hfin := (h.fibre_bounded (PeriodicOperators.castVec d)).1
    have hcard := (h.fibre_bounded (PeriodicOperators.castVec d)).2
    have heq : ∑' j : {j | k j = d}, G (k j) = ∑' _ : {j | k j = d}, G d :=
      tsum_congr fun j => by rw [show k j.1 = d from j.2]
    rw [heq]
    exact tsum_const_le_of_ncard_le (hfin.subset hsub) ((Set.ncard_le_ncard hsub hfin).trans hcard) _
  calc ∑' j, G (k j)
      = ∑' y : Σ d : Fin 4 → ℤ, {j // k j = d}, G (k y.2.1) :=
        ((Equiv.sigmaFiberEquiv k).tsum_eq fun j => G (k j)).symm
    _ = ∑' (d : Fin 4 → ℤ) (j : {j // k j = d}), G (k j.1) := ENNReal.tsum_sigma' _
    _ ≤ ∑' d, (m : ℝ≥0∞) * G d := ENNReal.tsum_le_tsum hfib
    _ = m * ∑' d, G d := ENNReal.tsum_mul_left
    _ = m * ∑' d, ENNReal.ofReal (Real.exp (-(δ * euclidNormVec (PeriodicOperators.castVec d)))) := by
        rw [← (Equiv.subLeft (k j')).tsum_eq]
        simp [G]
    _ ≤ m * expLineSeries (δ / 4) ^ 4 := by gcongr; exact tsum_exp_castVec_le hδ
def kernelAction (K : J → J → ℂ) (u : J → ℝ≥0∞) : J → ℝ≥0∞ := fun j' => ∑' j, ‖K j' j‖ₑ * u j
def IsExpDominated (x : J → InfiniteLattice.AmbientSpace) (ε a : ℝ) (u : J → ℝ≥0∞) : Prop :=
  ∀ j, u j ≤ ENNReal.ofReal (a * Real.exp (-(ε * euclidNormVec (x j))))
theorem enorm_le_ofReal_of_norm_le {z : ℂ} {r : ℝ} (h : ‖z‖ ≤ r) : ‖z‖ₑ ≤ ENNReal.ofReal r := by
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal h
def latticeConst (m : ℕ) (c : ℝ) : ℝ := ((m : ℝ≥0∞) * expLineSeries (c / 2 / 4) ^ 4).toReal
theorem latticeConst_nonneg (m : ℕ) (c : ℝ) : 0 ≤ latticeConst m c := ENNReal.toReal_nonneg
theorem ofReal_latticeConst (m : ℕ) {c : ℝ} (hc : 0 < c) :
    ENNReal.ofReal (latticeConst m c) = (m : ℝ≥0∞) * expLineSeries (c / 2 / 4) ^ 4 :=
  ENNReal.ofReal_toReal
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top m)
      (ENNReal.pow_ne_top (expLineSeries_ne_top (by positivity))))
theorem kernelAction_le {x : J → InfiniteLattice.AmbientSpace} {m : ℕ}
    (h : IsIntegerPlacement x m) {c ε a : ℝ} (hc : 0 < c) (hε₀ : 0 ≤ ε) (hε : ε ≤ c / 2)
    (ha : 0 ≤ a) {u : J → ℝ≥0∞} (hu : IsExpDominated x ε a u) {K : J → J → ℂ} {b : J → ℝ}
    (hb : ∀ j, 0 ≤ b j)
    (hK : ∀ j' j, ‖K j' j‖ ≤ b j' * Real.exp (-(c * euclidNormVec (x j' - x j))))
    (j' : J) :
    kernelAction K u j' ≤ ENNReal.ofReal
      (b j' * a * latticeConst m c * Real.exp (-(ε * euclidNormVec (x j')))) := by
  have hterm : ∀ j, ‖K j' j‖ₑ * u j ≤
      ENNReal.ofReal (b j' * a * Real.exp (-(ε * euclidNormVec (x j')))) *
        ENNReal.ofReal (Real.exp (-(c / 2 * euclidNormVec (x j' - x j)))) := fun j => by
    refine (mul_le_mul' (enorm_le_ofReal_of_norm_le (hK j' j)) (hu j)).trans ?_
    rw [← ENNReal.ofReal_mul (mul_nonneg (hb j') (Real.exp_pos _).le),
      ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (hb j') ha) (Real.exp_pos _).le)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hd := euclidNormVec_nonneg (x j' - x j)
    have htri : euclidNormVec (x j') ≤ euclidNormVec (x j' - x j) + euclidNormVec (x j) := by
      have := euclidNormVec_add_le (x j' - x j) (x j)
      simpa using this
    have hexp : Real.exp (-(c * euclidNormVec (x j' - x j))) *
        Real.exp (-(ε * euclidNormVec (x j))) ≤
        Real.exp (-(ε * euclidNormVec (x j'))) *
          Real.exp (-(c / 2 * euclidNormVec (x j' - x j))) := by
      rw [← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      nlinarith [mul_le_mul_of_nonneg_left htri hε₀, mul_le_mul_of_nonneg_right hε hd]
    calc _ = b j' * a * (Real.exp (-(c * euclidNormVec (x j' - x j))) *
            Real.exp (-(ε * euclidNormVec (x j)))) := by ring
      _ ≤ b j' * a * (Real.exp (-(ε * euclidNormVec (x j'))) *
            Real.exp (-(c / 2 * euclidNormVec (x j' - x j)))) :=
          mul_le_mul_of_nonneg_left hexp (mul_nonneg (hb j') ha)
      _ = _ := by ring
  calc kernelAction K u j' ≤ ∑' j, ENNReal.ofReal (b j' * a * Real.exp (-(ε * euclidNormVec (x j')))) *
        ENNReal.ofReal (Real.exp (-(c / 2 * euclidNormVec (x j' - x j)))) :=
        ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (b j' * a * Real.exp (-(ε * euclidNormVec (x j')))) *
        ∑' j, ENNReal.ofReal (Real.exp (-(c / 2 * euclidNormVec (x j' - x j)))) :=
        ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (b j' * a * Real.exp (-(ε * euclidNormVec (x j')))) *
        ENNReal.ofReal (latticeConst m c) := by
        rw [ofReal_latticeConst m hc]
        gcongr
        exact tsum_exp_placement_le h (by positivity) j'
    _ = _ := by
        rw [← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (hb j') ha) (Real.exp_pos _).le)]
        congr 1
        ring
def cubicConst (g : ℝ) : ℝ := (3 / g) ^ 3 * Real.exp g
theorem cubicConst_nonneg {g : ℝ} (hg : 0 < g) : 0 ≤ cubicConst g := by
  unfold cubicConst
  positivity
theorem one_add_pow_three_le {g r : ℝ} (hg : 0 < g) (hr : 0 ≤ r) :
    (1 + r) ^ 3 ≤ cubicConst g * Real.exp (g * r) := by
  have h1 : g * (1 + r) / 3 ≤ Real.exp (g * (1 + r) / 3) := by
    have := Real.add_one_le_exp (g * (1 + r) / 3)
    linarith
  have h2 : 1 + r ≤ 3 / g * Real.exp (g * (1 + r) / 3) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hg]
    linarith
  calc (1 + r) ^ 3 ≤ (3 / g * Real.exp (g * (1 + r) / 3)) ^ 3 :=
        pow_le_pow_left₀ (by positivity) h2 3
    _ = (3 / g) ^ 3 * Real.exp (g * (1 + r) / 3) ^ 3 := mul_pow _ _ _
    _ = (3 / g) ^ 3 * (Real.exp g * Real.exp (g * r)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 2
        push_cast
        ring
    _ = _ := by
        unfold cubicConst
        ring
theorem norm_le_of_cubicGrowth {x : J → InfiniteLattice.AmbientSpace} {A c : ℝ} (hA : 0 ≤ A)
    (hc : 0 < c) {X : J → J → ℂ} (hX : IsCubicGrowthLocalKernel x A X) (j' j : J) :
    ‖X j' j‖ ≤ A * Real.exp (2 * c) * (1 + euclidNormVec (x j')) ^ 3 *
      Real.exp (-(c * euclidNormVec (x j' - x j))) := by
  have h1r : 0 ≤ 1 + euclidNormVec (x j') := by
    have := euclidNormVec_nonneg (x j')
    linarith
  by_cases hd : euclidNormVec (x j' - x j) ≤ 2
  · have hone : 1 ≤ Real.exp (2 * c) * Real.exp (-(c * euclidNormVec (x j' - x j))) := by
      rw [← Real.exp_add]
      refine Real.one_le_exp ?_
      nlinarith
    calc ‖X j' j‖ ≤ A * (1 + euclidNormVec (x j')) ^ 3 * 1 := by
          simpa using hX.2 j' j
      _ ≤ A * (1 + euclidNormVec (x j')) ^ 3 * (Real.exp (2 * c) *
            Real.exp (-(c * euclidNormVec (x j' - x j)))) :=
          mul_le_mul_of_nonneg_left hone (mul_nonneg hA (pow_nonneg h1r 3))
      _ = _ := by ring
  · rw [hX.1 j' j hd, norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg hA (Real.exp_pos _).le) (pow_nonneg h1r 3))
      (Real.exp_pos _).le
theorem isExpDominated_kernelAction_decay {x : J → InfiniteLattice.AmbientSpace} {m : ℕ}
    (h : IsIntegerPlacement x m) {c ε a s : ℝ} (hc : 0 < c) (hε₀ : 0 ≤ ε) (hε : ε ≤ c / 2)
    (hs : 0 ≤ s) (ha : 0 ≤ a) {u : J → ℝ≥0∞} (hu : IsExpDominated x ε a u) {S : J → J → ℂ}
    (hS : IsExpDecayKernel x c s S) :
    IsExpDominated x ε (s * a * latticeConst m c) (kernelAction S u) := fun j' =>
  kernelAction_le h hc hε₀ hε ha hu (b := fun _ => s) (fun _ => hs) hS j'
theorem isExpDominated_kernelAction_growth {x : J → InfiniteLattice.AmbientSpace} {m : ℕ}
    (h : IsIntegerPlacement x m) {c ε g a A : ℝ} (hc : 0 < c) (hg : 0 < g) (hε₀ : 0 ≤ ε - g)
    (hε : ε ≤ c / 2) (hA : 0 ≤ A) (ha : 0 ≤ a) {u : J → ℝ≥0∞} (hu : IsExpDominated x ε a u)
    {X : J → J → ℂ} (hX : IsCubicGrowthLocalKernel x A X) :
    IsExpDominated x (ε - g) (A * Real.exp (2 * c) * a * latticeConst m c * cubicConst g)
      (kernelAction X u) := fun j' => by
  have hb : ∀ j, 0 ≤ A * Real.exp (2 * c) * (1 + euclidNormVec (x j)) ^ 3 := fun j => by
    have := euclidNormVec_nonneg (x j)
    exact mul_nonneg (mul_nonneg hA (Real.exp_pos _).le) (pow_nonneg (by linarith) 3)
  refine (kernelAction_le h hc (by linarith) hε ha hu hb (norm_le_of_cubicGrowth hA hc hX) j').trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hr := euclidNormVec_nonneg (x j')
  generalize euclidNormVec (x j') = r at hr ⊢
  have hcube := one_add_pow_three_le hg hr
  have hsplit : Real.exp (-((ε - g) * r)) = Real.exp (g * r) * Real.exp (-(ε * r)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have key : (1 + r) ^ 3 * Real.exp (-(ε * r)) ≤ cubicConst g * Real.exp (-((ε - g) * r)) := by
    rw [hsplit]
    calc _ ≤ cubicConst g * Real.exp (g * r) * Real.exp (-(ε * r)) :=
          mul_le_mul_of_nonneg_right hcube (Real.exp_pos _).le
      _ = _ := by ring
  have hcoef : 0 ≤ A * Real.exp (2 * c) * a * latticeConst m c :=
    mul_nonneg (mul_nonneg (mul_nonneg hA (Real.exp_pos _).le) ha) (latticeConst_nonneg m c)
  calc _ = A * Real.exp (2 * c) * a * latticeConst m c *
        ((1 + r) ^ 3 * Real.exp (-(ε * r))) := by ring
    _ ≤ A * Real.exp (2 * c) * a * latticeConst m c *
        (cubicConst g * Real.exp (-((ε - g) * r))) := mul_le_mul_of_nonneg_left key hcoef
    _ = _ := by ring
def pairConst (m : ℕ) (c : ℝ) : ℝ :=
  Real.exp (2 * c) * latticeConst m c ^ 2 * cubicConst (c / 8)
theorem pairConst_nonneg (m : ℕ) {c : ℝ} (hc : 0 < c) : 0 ≤ pairConst m c :=
  mul_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _)) (cubicConst_nonneg (by positivity))
theorem isExpDominated_kernelAction_pair {x : J → InfiniteLattice.AmbientSpace} {m : ℕ}
    (h : IsIntegerPlacement x m) {c ε a A s : ℝ} (hc : 0 < c) (hε₁ : c / 8 ≤ ε)
    (hε : ε ≤ c / 2) (hs : 0 ≤ s) (hA : 0 ≤ A) (ha : 0 ≤ a) {u : J → ℝ≥0∞}
    (hu : IsExpDominated x ε a u) {S X : J → J → ℂ} (hS : IsExpDecayKernel x c s S)
    (hX : IsCubicGrowthLocalKernel x A X) :
    IsExpDominated x (ε - c / 8) (pairConst m c * A * s * a) (kernelAction S (kernelAction X u)) := by
  have hg : 0 < c / 8 := by positivity
  have h1 := isExpDominated_kernelAction_growth h hc hg (by linarith) hε hA ha hu hX
  have hcoef : 0 ≤ A * Real.exp (2 * c) * a * latticeConst m c * cubicConst (c / 8) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hA (Real.exp_pos _).le) ha)
      (latticeConst_nonneg m c)) (cubicConst_nonneg hg)
  have h2 := isExpDominated_kernelAction_decay h hc (by linarith) (by linarith) hs hcoef h1 hS
  have heq : s * (A * Real.exp (2 * c) * a * latticeConst m c * cubicConst (c / 8)) *
      latticeConst m c = pairConst m c * A * s * a := by
    unfold pairConst
    ring
  rwa [heq] at h2
theorem isExpDominated_column {x : J → InfiniteLattice.AmbientSpace} {c s : ℝ} (hc : 0 < c)
    (hs : 0 ≤ s) {S : J → J → ℂ} (hS : IsExpDecayKernel x c s S) (o : OriginIndex x) :
    IsExpDominated x (c / 2) s (fun j => ‖S j o.1‖ₑ) := fun j => by
  refine enorm_le_ofReal_of_norm_le ((hS j o.1).trans ?_)
  rw [o.2, sub_zero]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hs
  nlinarith [euclidNormVec_nonneg (x j)]
theorem tsum_origin_le {x : J → InfiniteLattice.AmbientSpace} {m : ℕ}
    (h : IsIntegerPlacement x m) {ε a : ℝ} {F : OriginIndex x → J → ℝ≥0∞}
    (hF : ∀ o, IsExpDominated x ε a (F o)) :
    ∑' o : OriginIndex x, F o o.1 ≤ ENNReal.ofReal (m * a) := by
  have hb : ∀ o : OriginIndex x, F o o.1 ≤ ENNReal.ofReal a := fun o => by
    have := hF o o.1
    rwa [o.2, euclidNormVec_zero, mul_zero, neg_zero, Real.exp_zero, mul_one] at this
  calc _ ≤ ∑' _ : OriginIndex x, ENNReal.ofReal a := ENNReal.tsum_le_tsum hb
    _ ≤ m * ENNReal.ofReal a :=
        tsum_const_le_of_ncard_le (P := {j | x j = 0}) (h.fibre_bounded 0).1 (h.fibre_bounded 0).2 _
    _ = _ := by rw [ENNReal.ofReal_mul (Nat.cast_nonneg m), ENNReal.ofReal_natCast]
theorem summable_norm_and_tsum_le {P : Type} (F : P → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (h : ∑' p, ‖F p‖ₑ ≤ ENNReal.ofReal B) :
    Summable (fun p => ‖F p‖) ∧ ∑' p, ‖F p‖ ≤ B := by
  have hne : ∑' p, ‖F p‖ₑ ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  have hnorm : ∀ p, (‖F p‖ₑ).toReal = ‖F p‖ := fun p => toReal_enorm _
  refine ⟨by simpa only [hnorm] using ENNReal.summable_toReal hne, ?_⟩
  have hle := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rw [ENNReal.tsum_toReal_eq (fun _ => enorm_ne_top), ENNReal.toReal_ofReal hB] at hle
  simpa only [hnorm] using hle
theorem tsum_enorm_loopTermsOne (x : J → InfiniteLattice.AmbientSpace) (S₀ X S₁ : J → J → ℂ) :
    ∑' p, ‖loopTermsOne x S₀ X S₁ p‖ₑ =
      ∑' o : OriginIndex x, kernelAction S₀ (kernelAction X fun j => ‖S₁ j o.1‖ₑ) o.1 := by
  simp only [ENNReal.tsum_prod', loopTermsOne, enorm_mul, mul_assoc, kernelAction,
    ENNReal.tsum_mul_left]
theorem tsum_enorm_loopTermsTwo (x : J → InfiniteLattice.AmbientSpace) (S₀ X S₁ Y S₂ : J → J → ℂ) :
    ∑' p, ‖loopTermsTwo x S₀ X S₁ Y S₂ p‖ₑ =
      ∑' o : OriginIndex x,
        kernelAction S₀ (kernelAction X (kernelAction S₁ (kernelAction Y fun j => ‖S₂ j o.1‖ₑ))) o.1 := by
  simp only [ENNReal.tsum_prod', loopTermsTwo, enorm_mul, mul_assoc, kernelAction,
    ENNReal.tsum_mul_left]
theorem tsum_enorm_loopTermsThree (x : J → InfiniteLattice.AmbientSpace)
    (S₀ X S₁ Y S₂ W S₃ : J → J → ℂ) :
    ∑' p, ‖loopTermsThree x S₀ X S₁ Y S₂ W S₃ p‖ₑ =
      ∑' o : OriginIndex x,
        kernelAction S₀ (kernelAction X (kernelAction S₁ (kernelAction Y
          (kernelAction S₂ (kernelAction W fun j => ‖S₃ j o.1‖ₑ))))) o.1 := by
  simp only [ENNReal.tsum_prod', loopTermsThree, enorm_mul, mul_assoc, kernelAction,
    ENNReal.tsum_mul_left]
theorem coeff_le_one {m P A s : ℝ} (hm : 0 ≤ m) (hP : 0 ≤ P) (hA : 0 ≤ A) :
    m * (P * A * s * s) ≤ m * (P + P ^ 2 + P ^ 3) * A * s ^ 2 := by
  have hle : P ≤ P + P ^ 2 + P ^ 3 := by nlinarith [sq_nonneg P, pow_nonneg hP 3]
  calc _ = m * P * (A * s ^ 2) := by ring
    _ ≤ m * (P + P ^ 2 + P ^ 3) * (A * s ^ 2) := by gcongr
    _ = _ := by ring
theorem coeff_le_two {m P A A' s : ℝ} (hm : 0 ≤ m) (hP : 0 ≤ P) (hA : 0 ≤ A) (hA' : 0 ≤ A')
    (hs : 0 ≤ s) :
    m * (P * A * s * (P * A' * s * s)) ≤ m * (P + P ^ 2 + P ^ 3) * A * A' * s ^ 3 := by
  have hle : P ^ 2 ≤ P + P ^ 2 + P ^ 3 := by nlinarith [pow_nonneg hP 3]
  calc _ = m * P ^ 2 * (A * A' * s ^ 3) := by ring
    _ ≤ m * (P + P ^ 2 + P ^ 3) * (A * A' * s ^ 3) := by gcongr
    _ = _ := by ring
theorem coeff_le_three {m P A A' A'' s : ℝ} (hm : 0 ≤ m) (hP : 0 ≤ P) (hA : 0 ≤ A) (hA' : 0 ≤ A')
    (hA'' : 0 ≤ A'') :
    m * (P * A * s * (P * A' * s * (P * A'' * s * s))) ≤
      m * (P + P ^ 2 + P ^ 3) * A * A' * A'' * s ^ 4 := by
  have hle : P ^ 3 ≤ P + P ^ 2 + P ^ 3 := by nlinarith [sq_nonneg P]
  calc _ = m * P ^ 3 * (A * A' * A'' * s ^ 4) := by ring
    _ ≤ m * (P + P ^ 2 + P ^ 3) * (A * A' * A'' * s ^ 4) := by gcongr
    _ = _ := by ring
theorem loopTermsBound_holds : LoopTermsBound := by
  intro c m hc
  have hP := pairConst_nonneg m hc
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  refine ⟨m * (pairConst m c + pairConst m c ^ 2 + pairConst m c ^ 3), by positivity, ?_⟩
  intro J x h s hs
  refine ⟨?_, ?_, ?_⟩
  · intro S₀ S₁ X A hA h₀ h₁ hX
    refine summable_norm_and_tsum_le _ (by positivity) ?_
    rw [tsum_enorm_loopTermsOne]
    refine (tsum_origin_le h fun o =>
      isExpDominated_kernelAction_pair h hc (by linarith) le_rfl hs hA hs
        (isExpDominated_column hc hs h₁ o) h₀ hX).trans ?_
    exact ENNReal.ofReal_le_ofReal (coeff_le_one hm hP hA)
  · intro S₀ S₁ S₂ X Y A A' hA hA' h₀ h₁ h₂ hX hY
    refine summable_norm_and_tsum_le _ (by positivity) ?_
    rw [tsum_enorm_loopTermsTwo]
    refine (tsum_origin_le h fun o =>
      isExpDominated_kernelAction_pair h hc (by linarith) (by linarith) hs hA (by positivity)
        (isExpDominated_kernelAction_pair h hc (by linarith) le_rfl hs hA' hs
          (isExpDominated_column hc hs h₂ o) h₁ hY)
        h₀ hX).trans ?_
    exact ENNReal.ofReal_le_ofReal (coeff_le_two hm hP hA hA' hs)
  · intro S₀ S₁ S₂ S₃ X Y W A A' A'' hA hA' hA'' h₀ h₁ h₂ h₃ hX hY hW
    refine summable_norm_and_tsum_le _ (by positivity) ?_
    rw [tsum_enorm_loopTermsThree]
    refine (tsum_origin_le h fun o =>
      isExpDominated_kernelAction_pair h hc (by linarith) (by linarith) hs hA (by positivity)
        (isExpDominated_kernelAction_pair h hc (by linarith) (by linarith) hs hA' (by positivity)
          (isExpDominated_kernelAction_pair h hc (by linarith) le_rfl hs hA'' hs
            (isExpDominated_column hc hs h₃ o) h₂ hW)
          h₁ hY)
        h₀ hX).trans ?_
    exact ENNReal.ofReal_le_ofReal (coeff_le_three hm hP hA hA' hA'')
end Tower.LocalFamilies.LoopTermsEstimate
end YangMills.Construction
end
