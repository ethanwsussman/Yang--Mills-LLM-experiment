import YangMills.Construction.DirichletOperator.ScalesOfTheApproximateInverse
import YangMills.Construction.DirichletOperator.FunctionsOnTheTorusOfACube
import YangMills.Construction.DirichletOperator.HolderSeminormsOfAFormOfACubeNearASite
import YangMills.Construction.DirichletOperator.InequalitiesOnCubesOfTheFirstKindProof
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.CubeFormHolder
open Set
open YangMills.Construction.CubeTorus (levelSpacing)
open YangMills.Construction.Dirichlet YangMills.Construction.Torus
open YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions
open YangMills.Construction.PartitionCubes
open YangMills.Construction.PartitionCubes.CubeTorus (SiteFunctionsMatch)
open YangMills.Construction.PartitionCubes.CubeGeometry (restrictToFine)
open YangMills.Construction.CubeObservable
noncomputable section
theorem supNorm_add_le {S : ℝ} (h : LengthAxioms 4 S) (p q : PeriodicTorus 4 S) :
    supNorm (p + q) ≤ supNorm p + supNorm q := by
  have hbdd : ∀ r : PeriodicTorus 4 S,
      BddBelow {t | ∃ v : Fin 4 → ℝ, torusProj 4 S v = r ∧ t = ‖v‖} :=
    fun r => ⟨0, by rintro _ ⟨v, -, rfl⟩; exact norm_nonneg v⟩
  have hne : ∀ r : PeriodicTorus 4 S,
      {t | ∃ v : Fin 4 → ℝ, torusProj 4 S v = r ∧ t = ‖v‖}.Nonempty := by
    intro r
    obtain ⟨v, hv⟩ := h.torusProj_surjective r
    exact ⟨_, v, hv, rfl⟩
  have h₁ : ∀ v w : Fin 4 → ℝ, torusProj 4 S v = p → torusProj 4 S w = q →
      supNorm (p + q) ≤ ‖v‖ + ‖w‖ := by
    intro v w hv hw
    have hc : torusProj 4 S (v + w) = p + q := by
      subst hv hw
      funext μ
      simp [torusProj]
    exact (csInf_le (hbdd _) ⟨v + w, hc, rfl⟩).trans (norm_add_le v w)
  have h₂ : ∀ w : Fin 4 → ℝ, torusProj 4 S w = q → supNorm (p + q) - ‖w‖ ≤ supNorm p := by
    intro w hw
    refine le_csInf (hne p) ?_
    rintro _ ⟨v, hv, rfl⟩
    linarith [h₁ v w hv hw]
  have h₃ : supNorm (p + q) - supNorm p ≤ supNorm q := by
    refine le_csInf (hne q) ?_
    rintro _ ⟨w, hw, rfl⟩
    linarith [h₂ w hw]
  linarith
theorem finite_fineSite (hT : TorusLengthsStatement) (R : NestedRegions) : Finite R.FineSite := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineSite <;> assumption
theorem finite_fineBond (hT : TorusLengthsStatement) (R : NestedRegions) : Finite R.FineBond := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineBond <;> assumption
section Seminorms
variable {R : NestedRegions} {α lam : ℝ}
theorem holderSite_term_le [Finite R.FineSite] (f : R.FineSite → ℝ) {x x' : R.FineSite}
    (h₀ : 0 < siteLOneDist x x') (h₁ : siteLOneDist x x' ≤ lam) :
    (lam / siteLOneDist x x') ^ α * ‖f x' - f x‖ ≤ holderSite α lam f := by
  refine le_csSup ?_ ⟨x, x', h₀, h₁, rfl⟩
  refine (finite_range fun z : R.FineSite × R.FineSite =>
    (lam / siteLOneDist z.1 z.2) ^ α * ‖f z.2 - f z.1‖).bddAbove.mono ?_
  rintro r ⟨a, a', -, -, -, rfl⟩
  exact ⟨(a, a'), rfl⟩
theorem holderSite_nonneg (f : R.FineSite → ℝ) : 0 ≤ holderSite α lam f := by apply _root_.YangMills.Construction.FirstTypeGreenRegularity.holderSite_nonneg <;> assumption
theorem holderBond_nonneg (f : R.FineBond → ℝ) : 0 ≤ holderBond α lam f := by apply _root_.YangMills.Construction.FirstTypeGreenRegularity.holderBond_nonneg <;> assumption
theorem supSite_nonneg (f : R.FineSite → ℝ) : 0 ≤ supSite f :=
  Real.iSup_nonneg fun _ => norm_nonneg _
theorem abs_le_supSite [Finite R.FineSite] (f : R.FineSite → ℝ) (x : R.FineSite) :
    |f x| ≤ supSite f :=
  le_ciSup (f := fun x => ‖f x‖) (Finite.bddAbove_range _) x
theorem holderSite_mul_le [Finite R.FineSite] (ζ c : R.FineSite → ℝ) (hc : ∀ x, |c x| ≤ 1)
    (hs : holderSite α lam c ≤ 1) :
    holderSite α lam (fun x => ζ x * c x) ≤ holderSite α lam ζ + supSite ζ := by
  refine Real.sSup_le ?_ (add_nonneg (holderSite_nonneg _) (supSite_nonneg _))
  rintro _ ⟨x, x', h₀, h₁, rfl⟩
  have ha := holderSite_term_le (α := α) ζ h₀ h₁
  have hb := holderSite_term_le (α := α) c h₀ h₁
  have hw : 0 ≤ (lam / siteLOneDist x x') ^ α :=
    Real.rpow_nonneg (div_pos (h₀.trans_le h₁) h₀).le _
  set w := (lam / siteLOneDist x x') ^ α
  have hx : |ζ x| ≤ supSite ζ := abs_le_supSite ζ x
  have e : ‖ζ x' * c x' - ζ x * c x‖ ≤ ‖ζ x' - ζ x‖ + |ζ x| * ‖c x' - c x‖ := by
    have e₁ : ζ x' * c x' - ζ x * c x = (ζ x' - ζ x) * c x' + ζ x * (c x' - c x) := by ring
    rw [e₁]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Real.norm_eq_abs (ζ x), Real.norm_eq_abs (c x')]
    have := mul_le_mul_of_nonneg_left (hc x') (norm_nonneg (ζ x' - ζ x))
    linarith
  have hcn : w * ‖c x' - c x‖ ≤ 1 := hb.trans hs
  have hcn0 : 0 ≤ w * ‖c x' - c x‖ := mul_nonneg hw (norm_nonneg _)
  calc w * ‖ζ x' * c x' - ζ x * c x‖
      ≤ w * (‖ζ x' - ζ x‖ + |ζ x| * ‖c x' - c x‖) := mul_le_mul_of_nonneg_left e hw
    _ = w * ‖ζ x' - ζ x‖ + |ζ x| * (w * ‖c x' - c x‖) := by ring
    _ ≤ holderSite α lam ζ + supSite ζ * 1 := by
        refine add_le_add ha ?_
        exact mul_le_mul hx hcn hcn0 (supSite_nonneg _)
    _ = holderSite α lam ζ + supSite ζ := by ring
end Seminorms
variable {𝒮 : NestedRegions} {M : ℕ}
theorem scale_pos' (n : ℕ) : 0 < 𝒮.scale n := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.scale_pos <;> assumption
structure CubeFacts (Q : LevelCube 𝒮 M) : Prop where
  lengths : LengthAxioms 4 𝒮.side
  isometry : IsLocalIsometry Q
  norms : NormsPreserved Q
  ξ_eq : Q.system.setting.ξ = 𝒮.ξ
  mapSite_injOn : ∀ x x' : 𝒮.FineSite, (x : 𝒮.Point) ∈ Q.thicken (5 / 6) →
    (x' : 𝒮.Point) ∈ Q.thicken (5 / 6) → Q.system.mapSite x = Q.system.mapSite x' → x = x'
open Classical in
def localRestriction (Q : LevelCube 𝒮 M) (f : 𝒮.FineSite → ℝ) : Q.system.setting.FineSite → ℝ :=
  fun c => if h : ∃ x : 𝒮.FineSite, (x : 𝒮.Point) ∈ Q.thicken (5 / 6) ∧ Q.system.mapSite x = c
    then f h.choose else 0
namespace CubeFacts
variable {Q : LevelCube 𝒮 M} (H : CubeFacts Q)
include H
theorem mapSite_coe (x : 𝒮.FineSite) (hx : (x : 𝒮.Point) ∈ Q.thicken (5 / 6)) :
    ((Q.system.mapSite x : Q.system.setting.FineSite) : Q.system.setting.Point) =
      Q.system.embed x := by
  refine H.isometry.mapSite_eq _ hx x ?_
  show supNorm ((x : 𝒮.Point) - (x : 𝒮.Point)) ≤ 4 * 𝒮.scale (Q.level + 1)
  rw [sub_self, H.lengths.supNorm_zero]
  have := scale_pos' (𝒮 := 𝒮) (Q.level + 1)
  positivity
theorem siteFunctionsMatch (f : 𝒮.FineSite → ℝ) (hf : Q.SiteFnNear f) :
    SiteFunctionsMatch Q f (localRestriction Q f) where
  vanishes_off := hf
  image_vanishes_off := by
    intro c hc
    unfold localRestriction
    rw [dif_neg]
    rintro ⟨x, hx, rfl⟩
    exact hc ⟨x, hx, (H.mapSite_coe x hx).symm⟩
  eq_on := by
    intro x hx
    have h : ∃ x' : 𝒮.FineSite, (x' : 𝒮.Point) ∈ Q.thicken (5 / 6) ∧
        Q.system.mapSite x' = Q.system.mapSite x := ⟨x, hx, rfl⟩
    have e := H.mapSite_injOn _ _ h.choose_spec.1 hx h.choose_spec.2
    simp only [localRestriction, dif_pos h]
    rw [e]
end CubeFacts
section Lemma
variable {Q : LevelCube 𝒮 M} {y : 𝒮.Point} {α : ℝ} {ζ : 𝒮.FineSite → ℝ}
end Lemma
end
end YangMills.Construction.CubeFormHolder
