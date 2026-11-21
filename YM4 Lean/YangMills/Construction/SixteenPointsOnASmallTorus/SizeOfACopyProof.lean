import YangMills.Construction.SixteenPointsOnASmallTorus.SizeOfACopy
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SmallTorusCopies
open TorusFields WeightedResponses TestFunctions
private def gridPoint (a₀ : ℝ) (w : Fin 4 → ℤ) : EuclideanFourSpace :=
  WithLp.toLp 2 fun μ => a₀ / 2 * (w μ : ℝ)
private def symCoords {n : ℕ} (u : TorusSite n) : Fin 4 → ℤ := fun μ => (u μ).valMinAbs
private def reflectSite {n : ℕ} (M : ℕ) (k : Fin 4 → ℕ) (d : TorusSite n) : TorusSite n := fun μ =>
  (-1 : ZMod n) ^ k μ * (d μ - 2 * (M : ZMod n) * (k μ : ZMod n))
private theorem reflectedPoint_eq_gridPoint {m : ℕ} (a₀ : ℝ) (M : ℕ) (k : Fin 4 → ℕ) (p : TorusPlaquette m) :
    reflectedPoint a₀ M k p = gridPoint a₀ (symCoords (reflectSite M k (doubledBarycentre p))) := rfl
private theorem supDist_reflectSite {n : ℕ} (M : ℕ) (k : Fin 4 → ℕ) (d d' : TorusSite n) :
    supDist (reflectSite M k d) (reflectSite M k d') = supDist d d' := by
  unfold supDist
  refine Finset.sup_congr rfl fun μ _ => ?_
  have e : reflectSite M k d μ - reflectSite M k d' μ = (-1 : ZMod n) ^ k μ * (d μ - d' μ) := by
    simp only [reflectSite]; ring
  rw [e]
  rcases neg_one_pow_eq_or (ZMod n) (k μ) with s | s
  · rw [s, one_mul]
  · rw [s, neg_one_mul, ZMod.natAbs_valMinAbs_neg]
private theorem supDist_comm {n : ℕ} (x y : TorusSite n) : supDist x y = supDist y x := by
  unfold supDist
  refine Finset.sup_congr rfl fun μ _ => ?_
  rw [← neg_sub, ZMod.natAbs_valMinAbs_neg]
abbrev _root_.YangMills.SharedProofs.p9265 := @supDist_comm
private theorem shortest_step_lands {M : ℕ} (u u' : ZMod (2 * (2 * M))) (hM : 0 < M) (hu : |u.valMinAbs| < (M : ℤ)) :
    u.valMinAbs + (u' - u).valMinAbs = u'.valMinAbs ∨
      ((M : ℤ) ≤ |u'.valMinAbs| ∧ (M : ℤ) ≤ |u.valMinAbs + (u' - u).valMinAbs|) := by
  have : NeZero (2 * (2 * M)) := ⟨by omega⟩
  have hdvd : ((2 * (2 * M) : ℕ) : ℤ) ∣ (u.valMinAbs + (u' - u).valMinAbs - u'.valMinAbs) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    ring
  obtain ⟨j, hj⟩ := hdvd
  have h1 : (u' - u).valMinAbs.natAbs ≤ 2 * (2 * M) / 2 := ZMod.natAbs_valMinAbs_le _
  have h2 : u'.valMinAbs.natAbs ≤ 2 * (2 * M) / 2 := ZMod.natAbs_valMinAbs_le _
  have h1' : |(u' - u).valMinAbs| ≤ 2 * (M : ℤ) := by rw [Int.abs_eq_natAbs]; omega
  have h2' : |u'.valMinAbs| ≤ 2 * (M : ℤ) := by rw [Int.abs_eq_natAbs]; omega
  obtain ⟨a1, a2⟩ := abs_le.mp h1'
  obtain ⟨b1, b2⟩ := abs_le.mp h2'
  obtain ⟨c1, c2⟩ := abs_lt.mp hu
  push_cast at hj
  by_cases hj0 : j = 0
  · left
    rw [hj0, mul_zero] at hj
    omega
  · right
    rcases (by omega : 1 ≤ j ∨ j ≤ -1) with hp | hp
    · have : 4 * (M : ℤ) ≤ 2 * (2 * (M : ℤ)) * j := by nlinarith
      exact ⟨le_abs.mpr (Or.inr (by omega)), le_abs.mpr (Or.inl (by omega))⟩
    · have : 2 * (2 * (M : ℤ)) * j ≤ -(4 * (M : ℤ)) := by nlinarith
      exact ⟨le_abs.mpr (Or.inl (by omega)), le_abs.mpr (Or.inr (by omega))⟩
private theorem source_eq_zero_of_far {l ρ H a₀ : ℝ} {Λ : NNReal} {f : EuclideanFourSpace → ℝ} {M : ℕ}
    (hf : IsLocalizedSource l ρ H Λ f) (hρ : 0 < ρ)
    (ha : 0 < a₀) (hl : l = M * a₀) {w : Fin 4 → ℤ} {μ : Fin 4} (hw : (M : ℤ) ≤ |w μ|) : f (gridPoint a₀ w) = 0 := by
  by_contra hne
  have hface := hf.away_from_faces _ hne μ
  have e : |(gridPoint a₀ w) μ| = a₀ / 2 * |(w μ : ℝ)| := by
    simp only [gridPoint, PiLp.toLp_apply, abs_mul]
    rw [abs_of_pos (by positivity : 0 < a₀ / 2)]
  have hw' : (M : ℝ) ≤ |(w μ : ℝ)| := by exact_mod_cast hw
  rw [e, hl] at hface
  nlinarith
private theorem dist_gridPoint_add_le {a₀ : ℝ} (ha : 0 < a₀) (w δ : Fin 4 → ℤ) (T : ℕ) (hδ : ∀ μ, (δ μ).natAbs ≤ T) :
    dist (gridPoint a₀ w) (gridPoint a₀ (w + δ)) ≤ a₀ * T := by
  rw [EuclideanSpace.dist_eq]
  refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
  have hcoord : ∀ μ : Fin 4, dist ((gridPoint a₀ w) μ) ((gridPoint a₀ (w + δ)) μ) ^ 2 ≤ (a₀ / 2 * T) ^ 2 := by
    intro μ
    have e : dist ((gridPoint a₀ w) μ) ((gridPoint a₀ (w + δ)) μ) = a₀ / 2 * |(δ μ : ℝ)| := by
      simp only [gridPoint, PiLp.toLp_apply, Pi.add_apply, Real.dist_eq]
      rw [show a₀ / 2 * (w μ : ℝ) - a₀ / 2 * ((w μ + δ μ : ℤ) : ℝ) = a₀ / 2 * (-(δ μ : ℝ)) by push_cast; ring,
        abs_mul, abs_neg, abs_of_pos (by positivity : 0 < a₀ / 2)]
    have hT : |(δ μ : ℝ)| ≤ T := by
      have : |δ μ| ≤ (T : ℤ) := by
        rw [Int.abs_eq_natAbs]
        exact_mod_cast hδ μ
      exact_mod_cast this
    rw [e]
    gcongr
  calc ∑ μ : Fin 4, dist ((gridPoint a₀ w) μ) ((gridPoint a₀ (w + δ)) μ) ^ 2
      ≤ ∑ _μ : Fin 4, (a₀ / 2 * T) ^ 2 := Finset.sum_le_sum fun μ _ => hcoord μ
    _ = (a₀ * T) ^ 2 := by simp; ring
private theorem abs_sub_le_of_ne_zero {l ρ H a₀ : ℝ} {Λ : NNReal} {f : EuclideanFourSpace → ℝ} {M : ℕ}
    (hf : IsLocalizedSource l ρ H Λ f)
    (hρ : 0 < ρ) (ha : 0 < a₀) (hM : 0 < M) (hl : l = M * a₀) (u u' : TorusSite (2 * (2 * M)))
    (hne : f (gridPoint a₀ (symCoords u)) ≠ 0) :
    |f (gridPoint a₀ (symCoords u)) - f (gridPoint a₀ (symCoords u'))| ≤ Λ * (a₀ * supDist u' u) := by
  have hu : ∀ μ, |symCoords u μ| < (M : ℤ) := by
    intro μ
    by_contra hc
    exact hne (source_eq_zero_of_far hf hρ ha hl (not_lt.mp hc))
  set δ : Fin 4 → ℤ := fun μ => (u' μ - u μ).valMinAbs with hδdef
  have hy : f (gridPoint a₀ (symCoords u + δ)) = f (gridPoint a₀ (symCoords u')) := by
    by_cases hall : ∀ μ, symCoords u μ + δ μ = symCoords u' μ
    · have : symCoords u + δ = symCoords u' := funext hall
      rw [this]
    · obtain ⟨μ, hμ⟩ := not_forall.mp hall
      rcases shortest_step_lands (u μ) (u' μ) hM (hu μ) with e | ⟨e1, e2⟩
      · exact absurd e hμ
      · rw [source_eq_zero_of_far hf hρ ha hl (w := symCoords u + δ) (μ := μ) e2,
          source_eq_zero_of_far hf hρ ha hl (w := symCoords u') (μ := μ) e1]
  rw [← hy, ← Real.dist_eq]
  refine (hf.lipschitz.dist_le_mul _ _).trans ?_
  refine mul_le_mul_of_nonneg_left (dist_gridPoint_add_le ha _ _ _ fun μ => ?_) Λ.2
  exact Finset.le_sup (f := fun i => ((u' i - u i).valMinAbs).natAbs) (Finset.mem_univ μ)
private theorem abs_sub_le_supDist {l ρ H a₀ : ℝ} {Λ : NNReal} {f : EuclideanFourSpace → ℝ} {M : ℕ}
    (hf : IsLocalizedSource l ρ H Λ f)
    (hρ : 0 < ρ) (ha : 0 < a₀) (hM : 0 < M) (hl : l = M * a₀) (u u' : TorusSite (2 * (2 * M))) :
    |f (gridPoint a₀ (symCoords u)) - f (gridPoint a₀ (symCoords u'))| ≤ Λ * (a₀ * supDist u u') := by
  by_cases h1 : f (gridPoint a₀ (symCoords u)) = 0
  · by_cases h2 : f (gridPoint a₀ (symCoords u')) = 0
    · rw [h1, h2, sub_zero, abs_zero]
      positivity
    · rw [abs_sub_comm]
      exact abs_sub_le_of_ne_zero hf hρ ha hM hl u' u h2
  · rw [supDist_comm]
    exact abs_sub_le_of_ne_zero hf hρ ha hM hl u u' h1
private theorem weightNorm_reflectedWeight_le {m M : ℕ} (hm : m = 2 * M) (L t : ℕ) (hL : 0 < L) {l ρ H a₀ : ℝ}
    {Λ : NNReal} {f : EuclideanFourSpace → ℝ}
    (hf : IsLocalizedSource l ρ H Λ f) (hρ : 0 < ρ) (ha : 0 < a₀) (hM : 0 < M) (hl : l = M * a₀)
    (hsp : (L : ℝ) ^ t * a₀ ≤ min 1 ρ) (k : Fin 4 → ℕ) :
    weightNorm L t (m := m) (reflectedWeight a₀ M k f) ≤ 2 * sourceNorm ρ H Λ := by
  subst hm
  have hH : 0 ≤ H := (abs_nonneg _).trans (hf.abs_le 0)
  have hN : H ≤ sourceNorm ρ H Λ := le_max_left _ _
  have hN' : min 1 ρ * (Λ : ℝ) ≤ sourceNorm ρ H Λ := le_max_right _ _
  have hN0 : 0 ≤ sourceNorm ρ H Λ := hH.trans hN
  have hLt : (0 : ℝ) < (L : ℝ) ^ t := by positivity
  refine max_le ?_ ?_
  · refine Real.iSup_le (fun p => ?_) (by positivity)
    have := hf.abs_le (reflectedPoint a₀ M k p.1)
    simp only [reflectedWeight]
    linarith
  · refine Real.iSup_le (fun pp => ?_) (by positivity)
    obtain ⟨⟨p, _⟩, ⟨p', _⟩⟩ := pp
    simp only [reflectedWeight, barycentreDist]
    rw [reflectedPoint_eq_gridPoint, reflectedPoint_eq_gridPoint]
    have key := abs_sub_le_supDist hf hρ ha hM hl (reflectSite M k (doubledBarycentre p))
      (reflectSite M k (doubledBarycentre p'))
    rw [supDist_reflectSite] at key
    set T : ℕ := supDist (doubledBarycentre p) (doubledBarycentre p') with hT
    rcases Nat.eq_zero_or_pos T with h0 | h0
    · rw [h0]
      simp only [Nat.cast_zero, zero_div, div_zero]
      positivity
    · have hTr : (0 : ℝ) < T := by exact_mod_cast h0
      rw [div_le_iff₀ (by positivity)]
      refine key.trans ?_
      have hΛ : (0 : ℝ) ≤ Λ := Λ.2
      have : (Λ : ℝ) * ((L : ℝ) ^ t * a₀) ≤ sourceNorm ρ H Λ := by
        calc (Λ : ℝ) * ((L : ℝ) ^ t * a₀) ≤ Λ * min 1 ρ := mul_le_mul_of_nonneg_left hsp hΛ
          _ = min 1 ρ * Λ := mul_comm _ _
          _ ≤ _ := hN'
      have e : 2 * sourceNorm ρ H Λ * ((T : ℝ) / (2 * (L : ℝ) ^ t)) = sourceNorm ρ H Λ * T / (L : ℝ) ^ t := by
        field_simp
      rw [e, le_div_iff₀ hLt]
      calc (Λ : ℝ) * (a₀ * T) * (L : ℝ) ^ t = (Λ * ((L : ℝ) ^ t * a₀)) * T := by ring
        _ ≤ sourceNorm ρ H Λ * T := mul_le_mul_of_nonneg_right this hTr.le
theorem reflectedWeightNormBound : reflectedWeightNormBoundStatement := by
  intro L _ _ K κ t ρ H Λ f htκ hρ _ hf hsp k
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hLr : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have ha : 0 < levelSpacing L K 0 := by
    unfold levelSpacing
    exact zpow_pos (by exact_mod_cast hL) _
  have hm : fineSide L t (twoCellSide L κ t) = 2 * L ^ κ := by
    rw [fineSide_eq, twoCellSide, mul_assoc, pow_sub_mul_pow L htκ]
  have hst : (L : ℝ) ^ t * levelSpacing L K 0 = levelSpacing L K t := by
    unfold levelSpacing
    rw [← zpow_natCast, ← zpow_add₀ hLr]
    congr 1
    push_cast
    ring
  refine weightNorm_reflectedWeight_le hm L t hL hf hρ ha (pow_pos hL κ) ?_ (by rw [hst]; exact hsp) _
  simp only [cellLength]
  push_cast
  ring
end YangMills.Construction.SmallTorusCopies
end
