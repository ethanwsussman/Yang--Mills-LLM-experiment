import YangMills.Construction.FreeKernel.ConvolutionDecayBoundsProof
import YangMills.Construction.FreeKernel.HolderFieldInteriorEstimateProof
import YangMills.Construction.FreeKernel.LengthPowerSums
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeKernel.SecondDiffCube
open YangMills.Construction.FreeKernel YangMills.Construction.InfiniteLattice
open scoped ENNReal
variable {d : ℕ} {ξ : ℝ}
lemma val_sub_apply (p q : GridSite d ξ) (i : Fin d) :
    ((p - q : GridSite d ξ) : Fin d → ℝ) i = (p : Fin d → ℝ) i - (q : Fin d → ℝ) i := rfl
lemma val_add_apply (p q : GridSite d ξ) (i : Fin d) :
    ((p + q : GridSite d ξ) : Fin d → ℝ) i = (p : Fin d → ℝ) i + (q : Fin d → ℝ) i := rfl
lemma val_gridStep_apply (κ μ : Fin d) :
    ((gridStep κ : GridSite d ξ) : Fin d → ℝ) μ = if μ = κ then ξ else 0 := by
  simp [gridStep, Pi.single_apply]
lemma gridLength_nonneg (p : GridSite d ξ) : 0 ≤ gridLength p := by apply _root_.YangMills.Construction.PoissonInterior.zero_le_gridLength <;> assumption
lemma abs_apply_le_gridLength (p : GridSite d ξ) (μ : Fin d) :
    |(p : Fin d → ℝ) μ| ≤ gridLength p :=
  Finset.single_le_sum (f := fun μ => |(p : Fin d → ℝ) μ|) (fun _ _ => abs_nonneg _)
    (Finset.mem_univ μ)
lemma gridLength_sub_comm (p q : GridSite d ξ) : gridLength (p - q) = gridLength (q - p) := by apply _root_.YangMills.Construction.FreeKernel.ConvDecay.siteNorm_sub_comm <;> assumption
lemma gridLength_sub_le_add (p q w : GridSite d ξ) :
    gridLength (p - w) ≤ gridLength (p - q) + gridLength (q - w) := by apply _root_.YangMills.Construction.FreeKernel.ConvDecay.siteNorm_sub_le <;> assumption
lemma eq_of_gridLength_nonpos {p q : GridSite d ξ} (h : gridLength (p - q) ≤ 0) : p = q := by
  have h0 : gridLength (p - q) = 0 := le_antisymm h (gridLength_nonneg _)
  unfold gridLength l1Length at h0
  rw [Finset.sum_eq_zero_iff_of_nonneg fun _ _ => abs_nonneg _] at h0
  refine Subtype.ext (funext fun μ => ?_)
  have := h0 μ (Finset.mem_univ μ)
  rw [abs_eq_zero, val_sub_apply] at this
  linarith
def intCoord (p : GridSite d ξ) (μ : Fin d) : ℤ := ⌊(p : Fin d → ℝ) μ / ξ⌋
lemma val_eq_intCoord_mul (hξ : 0 < ξ) (p : GridSite d ξ) (μ : Fin d) :
    (p : Fin d → ℝ) μ = (intCoord p μ : ℝ) * ξ := by
  obtain ⟨n, hn⟩ := p.2
  unfold intCoord
  rw [hn μ, mul_div_cancel_right₀ _ hξ.ne', Int.floor_intCast]
lemma spacing_le_abs_sub_of_ne (hξ : 0 < ξ) {p q : GridSite d ξ} {μ : Fin d}
    (h : (p : Fin d → ℝ) μ ≠ (q : Fin d → ℝ) μ) :
    ξ ≤ |(p : Fin d → ℝ) μ - (q : Fin d → ℝ) μ| := by
  rw [val_eq_intCoord_mul hξ p μ, val_eq_intCoord_mul hξ q μ] at h ⊢
  have hne : intCoord p μ - intCoord q μ ≠ 0 := by
    intro h0
    apply h
    rw [sub_eq_zero.1 h0]
  have h1 : (1 : ℝ) ≤ |((intCoord p μ - intCoord q μ : ℤ) : ℝ)| := by
    have := Int.one_le_abs hne
    rw [← Int.cast_abs]
    exact_mod_cast this
  rw [← sub_mul, abs_mul, abs_of_pos hξ]
  push_cast at h1
  nlinarith
lemma spacing_le_gridLength_of_ne (hξ : 0 < ξ) {p q : GridSite d ξ} (h : p ≠ q) :
    ξ ≤ gridLength (p - q) := by
  have : ∃ μ, (p : Fin d → ℝ) μ ≠ (q : Fin d → ℝ) μ := by
    by_contra hc
    push Not at hc
    exact h (Subtype.ext (funext hc))
  obtain ⟨μ, hμ⟩ := this
  exact (spacing_le_abs_sub_of_ne hξ hμ).trans (abs_apply_le_gridLength (p - q) μ)
lemma supLength_le_iff (hd : 0 < d) (v : Fin d → ℝ) (t : ℝ) :
    supLength v ≤ t ↔ ∀ μ, |v μ| ≤ t := by
  constructor
  · intro h μ
    exact (le_ciSup (f := fun μ => |v μ|) (Set.finite_range _).bddAbove μ).trans h
  · intro h
    have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    exact ciSup_le h
lemma mem_gridCube_iff (hd : 0 < d) {c z : GridSite d ξ} {t : ℝ} :
    z ∈ gridCube c t ↔ ∀ μ, |(z : Fin d → ℝ) μ - (c : Fin d → ℝ) μ| ≤ t := supLength_le_iff hd _ t
def IsBetween (x x' p : GridSite d ξ) : Prop :=
  ∀ μ, ((x : Fin d → ℝ) μ ≤ (p : Fin d → ℝ) μ ∧ (p : Fin d → ℝ) μ ≤ (x' : Fin d → ℝ) μ) ∨
    ((x' : Fin d → ℝ) μ ≤ (p : Fin d → ℝ) μ ∧ (p : Fin d → ℝ) μ ≤ (x : Fin d → ℝ) μ)
lemma isBetween_left (x x' : GridSite d ξ) : IsBetween x x' x := fun μ => by
  rcases le_total ((x : Fin d → ℝ) μ) ((x' : Fin d → ℝ) μ) with h | h
  · exact Or.inl ⟨le_rfl, h⟩
  · exact Or.inr ⟨h, le_rfl⟩
lemma gridLength_le_of_isBetween {x x' p : GridSite d ξ} (h : IsBetween x x' p) :
    gridLength (p - x) ≤ gridLength (x - x') := by
  unfold gridLength l1Length
  refine Finset.sum_le_sum fun μ _ => ?_
  simp only [val_sub_apply]
  rcases h μ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
    linarith
  · rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
    linarith
lemma l1Length_eq_of_update (w w' : Fin d → ℝ) (κ : Fin d) (h : ∀ μ, μ ≠ κ → w' μ = w μ) :
    l1Length w = l1Length w' + (|w κ| - |w' κ|) := by
  unfold l1Length
  rw [← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_single κ (fun μ _ hμ => ?_) (fun hκ => absurd (Finset.mem_univ κ) hκ)
  rw [h μ hμ, sub_self]
lemma abs_sub_le_of_steps_aux (hξ : 0 < ξ) (f : GridSite d ξ → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (x' : GridSite d ξ) (n : ℕ) :
    ∀ x : GridSite d ξ, gridLength (x - x') ≤ n * ξ →
      (∀ (p : GridSite d ξ) (κ : Fin d), IsBetween x x' p → IsBetween x x' (p + gridStep κ) →
        |f (p + gridStep κ) - f p| ≤ ξ * K) →
      |f x - f x'| ≤ K * gridLength (x - x') := by
  induction n with
  | zero =>
    intro x hx _
    have : x = x' := eq_of_gridLength_nonpos (by simpa using hx)
    subst this
    simpa using mul_nonneg hK (gridLength_nonneg _)
  | succ n ih =>
    intro x hx hstep
    by_cases hxx : x = x'
    · subst hxx
      simpa using mul_nonneg hK (gridLength_nonneg _)
    have hex : ∃ κ, (x : Fin d → ℝ) κ ≠ (x' : Fin d → ℝ) κ := by
      by_contra hc
      push Not at hc
      exact hxx (Subtype.ext (funext hc))
    obtain ⟨κ, hκ⟩ := hex
    have hgap := spacing_le_abs_sub_of_ne hξ hκ
    have key : ∀ y : GridSite d ξ, (∀ μ, μ ≠ κ → (y : Fin d → ℝ) μ = (x : Fin d → ℝ) μ) →
        (((x : Fin d → ℝ) κ ≤ (y : Fin d → ℝ) κ ∧ (y : Fin d → ℝ) κ ≤ (x' : Fin d → ℝ) κ) ∨
          ((x' : Fin d → ℝ) κ ≤ (y : Fin d → ℝ) κ ∧ (y : Fin d → ℝ) κ ≤ (x : Fin d → ℝ) κ)) →
        |(x : Fin d → ℝ) κ - (y : Fin d → ℝ) κ| = ξ → |f x - f y| ≤ ξ * K →
        |f x - f x'| ≤ K * gridLength (x - x') := by
      intro y hyo hyb hyd hfy
      have hlen : gridLength (x - x') = gridLength (y - x') + ξ := by
        have := l1Length_eq_of_update ((x - x' : GridSite d ξ) : Fin d → ℝ)
          ((y - x' : GridSite d ξ) : Fin d → ℝ) κ (fun μ hμ => by
            simp only [val_sub_apply]
            rw [hyo μ hμ])
        have h2 : |((x - x' : GridSite d ξ) : Fin d → ℝ) κ| -
            |((y - x' : GridSite d ξ) : Fin d → ℝ) κ| = ξ := by
          simp only [val_sub_apply]
          rcases hyb with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
            rw [abs_of_nonpos (by linarith)] at hyd
            linarith
          · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
            rw [abs_of_nonneg (by linarith)] at hyd
            linarith
        unfold gridLength
        rw [this, h2]
      have hbet : ∀ p : GridSite d ξ, IsBetween y x' p → IsBetween x x' p := by
        intro p hp μ
        by_cases hμ : μ = κ
        · subst hμ
          rcases hyb with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hp μ with ⟨h3, h4⟩ | ⟨h3, h4⟩
          · exact Or.inl ⟨by linarith, h4⟩
          · exact Or.inl ⟨by linarith, by linarith⟩
          · exact Or.inr ⟨by linarith, by linarith⟩
          · exact Or.inr ⟨h3, by linarith⟩
        · have := hp μ
          rw [hyo μ hμ] at this
          exact this
      have hy := ih y (by push_cast at hx; linarith)
        (fun p κ' hp hp' => hstep p κ' (hbet p hp) (hbet _ hp'))
      calc |f x - f x'| ≤ |f x - f y| + |f y - f x'| := abs_sub_le _ _ _
        _ ≤ ξ * K + K * gridLength (y - x') := add_le_add hfy hy
        _ = K * gridLength (x - x') := by rw [hlen]; ring
    have hcoord : ∀ (q : GridSite d ξ) (μ : Fin d), μ ≠ κ →
        ((q + gridStep κ : GridSite d ξ) : Fin d → ℝ) μ = (q : Fin d → ℝ) μ := by
      intro q μ hμ
      rw [val_add_apply, val_gridStep_apply, if_neg hμ, add_zero]
    have hcoordκ : ∀ q : GridSite d ξ,
        ((q + gridStep κ : GridSite d ξ) : Fin d → ℝ) κ = (q : Fin d → ℝ) κ + ξ := by
      intro q
      rw [val_add_apply, val_gridStep_apply, if_pos rfl]
    rcases lt_or_gt_of_ne hκ with hlt | hgt
    · rw [abs_of_nonpos (by linarith)] at hgap
      have hB : IsBetween x x' (x + gridStep κ) := by
        intro μ
        by_cases hμ : μ = κ
        · subst hμ
          rw [hcoordκ]
          exact Or.inl ⟨by linarith, by linarith⟩
        · rw [hcoord x μ hμ]
          exact isBetween_left x x' μ
      refine key (x + gridStep κ) (hcoord x) ?_ ?_ ?_
      · rw [hcoordκ]
        exact Or.inl ⟨by linarith, by linarith⟩
      · rw [hcoordκ, sub_add_cancel_left, abs_neg, abs_of_pos hξ]
      · rw [abs_sub_comm]
        exact hstep x κ (isBetween_left x x') hB
    · rw [abs_of_nonneg (by linarith)] at hgap
      have hco : ∀ μ, μ ≠ κ →
          ((x - gridStep κ : GridSite d ξ) : Fin d → ℝ) μ = (x : Fin d → ℝ) μ := by
        intro μ hμ
        rw [val_sub_apply, val_gridStep_apply, if_neg hμ, sub_zero]
      have hcoκ : ((x - gridStep κ : GridSite d ξ) : Fin d → ℝ) κ = (x : Fin d → ℝ) κ - ξ := by
        rw [val_sub_apply, val_gridStep_apply, if_pos rfl]
      have hB : IsBetween x x' (x - gridStep κ) := by
        intro μ
        by_cases hμ : μ = κ
        · subst hμ
          rw [hcoκ]
          exact Or.inr ⟨by linarith, by linarith⟩
        · rw [hco μ hμ]
          exact isBetween_left x x' μ
      refine key (x - gridStep κ) hco ?_ ?_ ?_
      · rw [hcoκ]
        exact Or.inr ⟨by linarith, by linarith⟩
      · rw [hcoκ, sub_sub_cancel, abs_of_pos hξ]
      · have := hstep (x - gridStep κ) κ hB (by rw [sub_add_cancel]; exact isBetween_left x x')
        rwa [sub_add_cancel] at this
lemma abs_sub_le_of_steps (hξ : 0 < ξ) (f : GridSite d ξ → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (x x' : GridSite d ξ)
    (hstep : ∀ (p : GridSite d ξ) (κ : Fin d), IsBetween x x' p → IsBetween x x' (p + gridStep κ) →
      |f (p + gridStep κ) - f p| ≤ ξ * K) :
    |f x - f x'| ≤ K * gridLength (x - x') := by
  obtain ⟨n, hn⟩ := exists_nat_ge (gridLength (x - x') / ξ)
  exact abs_sub_le_of_steps_aux hξ f hK x' n x ((div_le_iff₀ hξ).1 hn) hstep
lemma rpow_neg_le_rpow_neg {t t₀ q : ℝ} (h0 : 0 < t₀) (h : t₀ ≤ t) (hq : 0 ≤ q) :
    t ^ (-q) ≤ t₀ ^ (-q) :=
  Real.rpow_le_rpow_of_nonpos h0 h (by linarith)
section Kernel
variable {cK : ℝ} {C : GridSite d ξ → ℝ}
end Kernel
section Faces
open scoped Classical
variable {c : GridSite d ξ} {r : ℝ} {B : Finset (GridSite d ξ)}
end Faces
lemma innerPowerTerm_nonneg (hξ : 0 < ξ) (σ t : ℝ) (z : GridSite d ξ) :
    0 ≤ innerPowerTerm d ξ σ t z := by
  unfold innerPowerTerm
  refine Set.indicator_nonneg (fun w _ => mul_nonneg (pow_nonneg hξ.le _) ?_) z
  exact Real.rpow_nonneg (gridLength_nonneg w) _
lemma div_rpow_eq_mul_rpow_neg {l r σ : ℝ} (hl : 0 ≤ l) (hr : 0 < r) :
    (l / r) ^ σ = l ^ σ * r ^ (-σ) := by
  rw [Real.div_rpow hl hr.le, Real.rpow_neg hr.le, div_eq_mul_inv]
structure CubeSumData (ξ r σ cK a : ℝ) (k H : GridSite d ξ → ℝ) (B : Finset (GridSite d ξ)) :
    Prop where
  dim : 3 ≤ d
  spacing : 0 < ξ
  radius : 0 < r
  exponent_pos : 0 < σ
  exponent_lt : σ < 1
  number : 0 ≤ cK
  seminorm : 0 ≤ a
  kernel : ∀ y, |k y| ≤ cK * (gridLength y + ξ) ^ (-(d : ℝ))
  kernel_diff : ∀ κ y, |forwardDiff κ k y| ≤ cK * (gridLength y + ξ) ^ (-((d : ℝ) + 1))
  holder : ∀ z ∈ B, ∀ z' ∈ B, |H z - H z'| ≤ (gridLength (z - z') / r) ^ σ * a
  diameter : ∀ z ∈ B, ∀ z' ∈ B, gridLength (z - z') ≤ 2 * d * r
  powers : LengthPowerSumBounds
  balls : BallSumBounds d ξ cK
namespace CubeSumData
variable {r σ cK a : ℝ} {k H : GridSite d ξ → ℝ} {B : Finset (GridSite d ξ)}
lemma abs_kernel_le (S : CubeSumData ξ r σ cK a k H B) {y : GridSite d ξ}
    (hy : 0 < gridLength y) :
    |k y| ≤ cK * gridLength y ^ (-(d : ℝ)) :=
  (S.kernel y).trans (mul_le_mul_of_nonneg_left
    (rpow_neg_le_rpow_neg hy (by linarith [S.spacing]) (Nat.cast_nonneg d)) S.number)
lemma prefactor_nonneg (S : CubeSumData ξ r σ cK a k H B) : 0 ≤ cK * r ^ (-σ) * a :=
  mul_nonneg (mul_nonneg S.number (Real.rpow_nonneg S.radius.le _)) S.seminorm
lemma near_term_le (S : CubeSumData ξ r σ cK a k H B) {x z : GridSite d ξ} (hx : x ∈ B)
    (hz : z ∈ B) {t : ℝ} (ht : gridLength (z - x) ≤ t) :
    ξ ^ d * |k (x - z) * (H z - H x)| ≤
      (cK * r ^ (-σ) * a) * innerPowerTerm d ξ σ t (z - x) := by
  have hA := S.prefactor_nonneg
  by_cases hzx : z = x
  · subst hzx
    have h0 : H z - H z = 0 := sub_self _
    rw [h0, mul_zero, abs_zero, mul_zero]
    exact mul_nonneg hA (innerPowerTerm_nonneg S.spacing _ _ _)
  · have hl : 0 < gridLength (z - x) :=
      S.spacing.trans_le (spacing_le_gridLength_of_ne S.spacing hzx)
    have hin : innerPowerTerm d ξ σ t (z - x) =
        ξ ^ d * gridLength (z - x) ^ (-(d : ℝ) + σ) :=
      Set.indicator_of_mem (show (z - x) ∈ {w : GridSite d ξ | 0 < l1Length (w : Fin d → ℝ) ∧
        l1Length (w : Fin d → ℝ) ≤ t} from ⟨hl, ht⟩) _
    have hk : |k (x - z)| ≤ cK * gridLength (z - x) ^ (-(d : ℝ)) := by
      have := S.abs_kernel_le (y := x - z) (by rw [gridLength_sub_comm]; exact hl)
      rwa [gridLength_sub_comm] at this
    have hHz := S.holder z hz x hx
    rw [hin, abs_mul, Real.rpow_add hl]
    calc ξ ^ d * (|k (x - z)| * |H z - H x|)
        ≤ ξ ^ d * ((cK * gridLength (z - x) ^ (-(d : ℝ))) *
            ((gridLength (z - x) / r) ^ σ * a)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul hk hHz (abs_nonneg _)
              (mul_nonneg S.number (Real.rpow_nonneg hl.le _)))
            (pow_nonneg S.spacing.le _)
      _ = _ := by
          rw [div_rpow_eq_mul_rpow_neg hl.le S.radius]
          ring
lemma two_rpow_cast_succ (d : ℕ) : (2 : ℝ) ^ ((d : ℝ) + 1) = 2 ^ (d + 1) := by
  have := Real.rpow_natCast (2 : ℝ) (d + 1)
  rwa [Nat.cast_add, Nat.cast_one] at this
lemma kernel_sub_le (S : CubeSumData ξ r σ cK a k H B) {x x' z : GridSite d ξ}
    (hfar : 2 * gridLength (x - x') < gridLength (z - x)) :
    |k (x - z) - k (x' - z)| ≤
      (cK * 2 ^ (d + 1) * gridLength (z - x) ^ (-((d : ℝ) + 1))) * gridLength (x - x') := by
  have hρ0 := gridLength_nonneg (x - x')
  have hl : 0 < gridLength (z - x) := by linarith
  have hK0 : 0 ≤ cK * 2 ^ (d + 1) * gridLength (z - x) ^ (-((d : ℝ) + 1)) :=
    mul_nonneg (mul_nonneg S.number (by positivity)) (Real.rpow_nonneg hl.le _)
  refine abs_sub_le_of_steps S.spacing (fun p => k (p - z)) hK0 x x' fun q κ hq _ => ?_
  have hlen : gridLength (z - x) / 2 ≤ gridLength (q - z) := by
    have h1 := gridLength_le_of_isBetween hq
    have h2 := gridLength_sub_le_add z q x
    rw [gridLength_sub_comm z q] at h2
    linarith
  have hstep : q + gridStep κ - z = q - z + gridStep κ := by abel
  have hdiff : k (q + gridStep κ - z) - k (q - z) = ξ * forwardDiff κ k (q - z) := by
    unfold forwardDiff
    rw [hstep, ← mul_assoc, mul_inv_cancel₀ S.spacing.ne', one_mul]
  simp only [hdiff, abs_mul, abs_of_pos S.spacing]
  refine mul_le_mul_of_nonneg_left ?_ S.spacing.le
  have h3 : (gridLength (q - z) + ξ) ^ (-((d : ℝ) + 1)) ≤
      (gridLength (z - x) / 2) ^ (-((d : ℝ) + 1)) :=
    rpow_neg_le_rpow_neg (by linarith) (by linarith [S.spacing]) (by positivity)
  have h4 : (gridLength (z - x) / 2) ^ (-((d : ℝ) + 1)) =
      2 ^ (d + 1) * gridLength (z - x) ^ (-((d : ℝ) + 1)) := by
    rw [Real.div_rpow hl.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
      two_rpow_cast_succ, div_inv_eq_mul, mul_comm]
  calc |forwardDiff κ k (q - z)| ≤ cK * (gridLength (q - z) + ξ) ^ (-((d : ℝ) + 1)) :=
        S.kernel_diff κ _
    _ ≤ cK * (2 ^ (d + 1) * gridLength (z - x) ^ (-((d : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left (h4 ▸ h3) S.number
    _ = _ := by ring
lemma far_term_le (S : CubeSumData ξ r σ cK a k H B) {x x' z : GridSite d ξ} (hx : x ∈ B)
    (hz : z ∈ B) (hfar : 2 * gridLength (x - x') < gridLength (z - x)) :
    ξ ^ d * |(k (x - z) - k (x' - z)) * (H z - H x)| ≤
      (gridLength (x - x') * cK * 2 ^ (d + 1) * r ^ (-σ) * a) *
        outerPowerTerm d ξ σ (2 * gridLength (x - x')) (z - x) := by
  have hρ0 := gridLength_nonneg (x - x')
  have hl : 0 < gridLength (z - x) := by linarith
  have hout : outerPowerTerm d ξ σ (2 * gridLength (x - x')) (z - x) =
      ξ ^ d * gridLength (z - x) ^ (-(d : ℝ) - 1 + σ) :=
    Set.indicator_of_mem (show (z - x) ∈ {w : GridSite d ξ |
      2 * gridLength (x - x') < l1Length (w : Fin d → ℝ)} from hfar) _
  have hk := S.kernel_sub_le hfar
  have hHz := S.holder z hz x hx
  have hexp : -(d : ℝ) - 1 + σ = -((d : ℝ) + 1) + σ := by ring
  rw [hout, abs_mul, hexp, Real.rpow_add hl]
  calc ξ ^ d * (|k (x - z) - k (x' - z)| * |H z - H x|)
      ≤ ξ ^ d * (((cK * 2 ^ (d + 1) * gridLength (z - x) ^ (-((d : ℝ) + 1))) *
            gridLength (x - x')) * ((gridLength (z - x) / r) ^ σ * a)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hk hHz (abs_nonneg _)
            (mul_nonneg (mul_nonneg (mul_nonneg S.number (by positivity))
              (Real.rpow_nonneg hl.le _)) hρ0))
          (pow_nonneg S.spacing.le _)
    _ = _ := by
        rw [div_rpow_eq_mul_rpow_neg hl.le S.radius]
        ring
end CubeSumData
namespace CubeSumData
variable {r σ cK a : ℝ} {k H : GridSite d ξ → ℝ} {B : Finset (GridSite d ξ)}
end CubeSumData
end YangMills.Construction.FreeKernel.SecondDiffCube
