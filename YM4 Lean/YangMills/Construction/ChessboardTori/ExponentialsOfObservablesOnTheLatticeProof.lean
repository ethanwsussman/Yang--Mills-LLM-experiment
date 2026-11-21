import YangMills.Construction.ChessboardTori.PeriodicRealizationOnARectangularTorusProof
import YangMills.Construction.ChessboardTori.ExponentialsOfObservablesOnTheLattice
import YangMills.Construction.ChessboardTori.LinksAndPlaquettesUnderLatticeIsometries
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ChessboardTori
open InfiniteLattice (AmbientSpace)
namespace ExponentialObservableRules
def axisCount (i j μ : Fin 4) : ℤ :=
  (if μ = i then 1 else 0) + (if μ = j then 1 else 0)
theorem axes_eq_of_axisCount_mod_two : ∀ i j i' j' : Fin 4, i < j → i' < j' →
    (∀ μ, axisCount i j μ % 2 = axisCount i' j' μ % 2) → i = i' ∧ j = j' := by
  decide
variable (D : ChessboardSetup)
theorem mesh_pos : 0 < D.mesh := by apply _root_.YangMills.Construction.ChessboardTori.ChessboardSetup.mesh_pos <;> assumption
variable {D}
theorem center_apply (p : D.Plaquette) {k : Fin 4 → ℤ}
    (hk : ∀ μ, (p.corner : AmbientSpace) μ = (k μ : ℝ) * D.mesh) (μ : Fin 4) :
    p.center μ = ((2 * k μ + axisCount p.lowAxis p.highAxis μ : ℤ) : ℝ) * (D.mesh / 2) := by apply _root_.YangMills.Construction.ChessboardTori.BoxTorusQuotient.center_apply <;> assumption
theorem center_injective {p q : D.Plaquette} (hpq : p.center = q.center) : p = q := by
  obtain ⟨k, hk⟩ := p.corner.2
  obtain ⟨k', hk'⟩ := q.corner.2
  have hne : D.mesh / 2 ≠ 0 := (half_pos (mesh_pos D)).ne'
  have hint : ∀ μ, 2 * k μ + axisCount p.lowAxis p.highAxis μ =
      2 * k' μ + axisCount q.lowAxis q.highAxis μ := by
    intro μ
    have hμ := congrFun hpq μ
    rw [center_apply p hk, center_apply q hk'] at hμ
    exact_mod_cast mul_right_cancel₀ hne hμ
  obtain ⟨hlow, hhigh⟩ := axes_eq_of_axisCount_mod_two _ _ _ _ p.lowAxis_lt_highAxis
    q.lowAxis_lt_highAxis fun μ => by
      have := hint μ
      omega
  have hcorner : p.corner = q.corner := by
    refine Subtype.ext (funext fun μ => ?_)
    have hμ := hint μ
    rw [← hlow, ← hhigh] at hμ
    have hkk : k μ = k' μ := by omega
    rw [hk, hk', hkk]
  exact InfiniteLattice.ElementaryPlaquette.ext hcorner hlow hhigh
theorem toFun_injective (r : D.LatticeSym) : Function.Injective r.toFun := by
  intro x y hxy
  have hzero : TorusMetric.euclidNormVec (x - y) = 0 := by
    rw [← r.preservesDist, hxy, sub_self]
    simp [TorusMetric.euclidNormVec]
  have hnonneg : 0 ≤ ∑ μ, (x - y) μ ^ 2 := Finset.sum_nonneg fun μ _ => sq_nonneg _
  rw [TorusMetric.euclidNormVec, Real.sqrt_eq_zero hnonneg] at hzero
  funext μ
  have hsq := (Finset.sum_eq_zero_iff_of_nonneg fun μ _ => sq_nonneg ((x - y) μ)).mp hzero μ
    (Finset.mem_univ μ)
  have hμ : (x - y) μ = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp hsq
  simpa [sub_eq_zero] using hμ
theorem finite_setOf_center_mem {B : Set AmbientSpace} (hB : Bornology.IsBounded B) :
    {p : D.Plaquette | p.center ∈ B}.Finite := by
  have hpos : 0 < D.mesh / 2 := half_pos (mesh_pos D)
  obtain ⟨R, hR⟩ := hB.subset_closedBall 0
  have hcoord : ∀ p : D.Plaquette, ∃ c : Fin 4 → ℤ,
      ∀ μ, p.center μ = (c μ : ℝ) * (D.mesh / 2) := by
    intro p
    obtain ⟨k, hk⟩ := p.corner.2
    exact ⟨_, center_apply p hk⟩
  choose c hc using hcoord
  refine Set.Finite.of_injOn (f := c)
    (t := Set.Icc (fun _ => -⌈R / (D.mesh / 2)⌉) (fun _ => ⌈R / (D.mesh / 2)⌉)) ?_ ?_
    (Set.finite_Icc _ _)
  · intro p hp
    have hnorm : ‖p.center‖ ≤ R := by simpa using hR hp
    have hreal : ∀ μ, |(c p μ : ℝ)| ≤ R / (D.mesh / 2) := by
      intro μ
      have hμ : ‖p.center μ‖ ≤ R := (norm_le_pi_norm _ μ).trans hnorm
      rw [hc p μ, Real.norm_eq_abs, abs_mul, abs_of_pos hpos] at hμ
      exact (le_div_iff₀ hpos).mpr hμ
    have hint : ∀ μ, |c p μ| ≤ ⌈R / (D.mesh / 2)⌉ := by
      intro μ
      have hμ : ((|c p μ| : ℤ) : ℝ) ≤ R / (D.mesh / 2) := by
        rw [Int.cast_abs]
        exact hreal μ
      exact Int.cast_le.mp (hμ.trans (Int.le_ceil _))
    exact ⟨fun μ => (abs_le.mp (hint μ)).1, fun μ => (abs_le.mp (hint μ)).2⟩
  · intro p _ q _ hpq
    refine center_injective (funext fun μ => ?_)
    rw [hc p μ, hc q μ, hpq]
theorem support_smeared_finite {v : AmbientSpace → ℂ} (hv : ChessboardSetup.HasBoundedSupport v)
    (U : D.GaugeField) :
    (Function.support fun p : D.Plaquette =>
      InfiniteLattice.faceEnergy U p • v p.center).Finite := by
  obtain ⟨B, hB, hvB⟩ := hv
  refine (finite_setOf_center_mem hB).subset fun p hp => ?_
  by_contra hout
  exact hp (by simp [hvB _ hout])
theorem smeared_pullbackField (hsym : D.LatticeSymMapsLinksFaces)
    (r : D.LatticeSym) (v : AmbientSpace → ℂ) (U : D.GaugeField) :
    D.smeared v (r.pullbackField U) = D.smeared (v ∘ invMap r.toFun) U := by
  obtain ⟨-, hsurj, -, hcenter, henergy⟩ := hsym r
  have hinj : Function.Injective (D.imageFace r) := fun p q hpq =>
    center_injective (toFun_injective r (by rw [← hcenter, ← hcenter, hpq]))
  let σ : D.Plaquette ≃ D.Plaquette := Equiv.ofBijective _ ⟨hinj, hsurj⟩
  simp only [ChessboardSetup.smeared, InfiniteLattice.smearedEnergy]
  refine Eq.trans (finsum_congr fun p => ?_) (finsum_comp_equiv σ)
  have hσ : σ p = D.imageFace r p := rfl
  rw [hσ, henergy, hcenter, Function.comp_apply, invMap,
    Function.leftInverse_invFun (toFun_injective r)]
theorem conj_smeared (v : AmbientSpace → ℂ) (U : D.GaugeField) :
    starRingEnd ℂ (D.smeared v U) = D.smeared (fun x => starRingEnd ℂ (v x)) U := by
  simp only [ChessboardSetup.smeared, InfiniteLattice.smearedEnergy]
  refine ((starAddEquiv (R := ℂ)).map_finsum _).trans (finsum_congr fun p => ?_)
  change starRingEnd ℂ _ = _
  simp [Complex.real_smul]
theorem smeared_add {v w : AmbientSpace → ℂ} (hv : ChessboardSetup.HasBoundedSupport v)
    (hw : ChessboardSetup.HasBoundedSupport w) (U : D.GaugeField) :
    D.smeared v U + D.smeared w U = D.smeared (v + w) U := by
  simp only [ChessboardSetup.smeared, InfiniteLattice.smearedEnergy]
  rw [← finsum_add_distrib (support_smeared_finite hv U) (support_smeared_finite hw U)]
  exact finsum_congr fun p => by simp [smul_add]
end ExponentialObservableRules
open ExponentialObservableRules in
theorem ExponentialObservableRules.holds
    (hsym : LatticeSymmetryAction.Statement) :
    ExponentialObservableRules.Statement := by
  intro D r v w _ hv _ hw
  refine ⟨funext fun U => ?_, funext fun U => ?_, funext fun U => ?_⟩
  · change Complex.exp (D.smeared v (r.pullbackField U)) = _
    rw [smeared_pullbackField (hsym D)]
  · rw [← Complex.exp_conj, conj_smeared]
  · rw [← Complex.exp_add, smeared_add hv hw]
end YangMills.Construction.ChessboardTori
end
