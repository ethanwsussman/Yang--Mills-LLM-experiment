import YangMills.Construction.Dirichlet.CommutatorBounds
import YangMills.Construction.Dirichlet.CubePartitionOfUnity
import YangMills.Construction.LatticeCalculus.Identities
import YangMills.Construction.Torus.PartitionsShellsCubes
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Torus YangMills.Construction.Dirichlet
noncomputable section
namespace YangMills.Construction.Dirichlet.Commutator
section Lengths
variable {d : ℕ} {S : ℝ}
theorem exists_torusProj_eq (p : PeriodicTorus d S) : ∃ v : Fin d → ℝ, torusProj d S v = p := by
  choose v hv using fun μ => QuotientAddGroup.mk_surjective (p μ)
  exact ⟨v, funext hv⟩
theorem torusProj_add (v w : Fin d → ℝ) :
    torusProj d S (v + w) = torusProj d S v + torusProj d S w := by
  funext μ
  simp [torusProj]
theorem torusProj_neg (v : Fin d → ℝ) : torusProj d S (-v) = -torusProj d S v := by
  funext μ
  simp [torusProj]
theorem sInf_lifts_add_le (f : (Fin d → ℝ) → ℝ) (nonneg : ∀ v, 0 ≤ f v)
    (add_le : ∀ v w, f (v + w) ≤ f v + f w) (p q : PeriodicTorus d S) :
    sInf {r | ∃ v : Fin d → ℝ, torusProj d S v = p + q ∧ r = f v} ≤
      sInf {r | ∃ v : Fin d → ℝ, torusProj d S v = p ∧ r = f v} +
        sInf {r | ∃ v : Fin d → ℝ, torusProj d S v = q ∧ r = f v} := by
  have nonempty : ∀ u : PeriodicTorus d S,
      {r | ∃ v : Fin d → ℝ, torusProj d S v = u ∧ r = f v}.Nonempty := by
    intro u
    obtain ⟨v, hv⟩ := exists_torusProj_eq u
    exact ⟨f v, v, hv, rfl⟩
  have bdd : BddBelow {r | ∃ v : Fin d → ℝ, torusProj d S v = p + q ∧ r = f v} :=
    ⟨0, by rintro r ⟨v, -, rfl⟩; exact nonneg v⟩
  have first : ∀ v w, torusProj d S v = p → torusProj d S w = q →
      sInf {r | ∃ v : Fin d → ℝ, torusProj d S v = p + q ∧ r = f v} ≤ f v + f w := by
    intro v w hv hw
    exact (csInf_le bdd ⟨v + w, by rw [torusProj_add, hv, hw], rfl⟩).trans (add_le v w)
  have second : ∀ w, torusProj d S w = q →
      sInf {r | ∃ v : Fin d → ℝ, torusProj d S v = p + q ∧ r = f v} - f w ≤
        sInf {r | ∃ v : Fin d → ℝ, torusProj d S v = p ∧ r = f v} := by
    intro w hw
    refine le_csInf (nonempty p) ?_
    rintro r ⟨v, hv, rfl⟩
    linarith [first v w hv hw]
  have third : sInf {r | ∃ v : Fin d → ℝ, torusProj d S v = p + q ∧ r = f v} -
      sInf {r | ∃ v : Fin d → ℝ, torusProj d S v = p ∧ r = f v} ≤
        sInf {r | ∃ v : Fin d → ℝ, torusProj d S v = q ∧ r = f v} := by
    refine le_csInf (nonempty q) ?_
    rintro r ⟨w, hw, rfl⟩
    linarith [second w hw]
  linarith
theorem sInf_lifts_neg (f : (Fin d → ℝ) → ℝ) (neg_eq : ∀ v, f (-v) = f v)
    (p : PeriodicTorus d S) :
    sInf {r | ∃ v : Fin d → ℝ, torusProj d S v = -p ∧ r = f v} =
      sInf {r | ∃ v : Fin d → ℝ, torusProj d S v = p ∧ r = f v} := by
  congr 1
  ext r
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨-v, by rw [torusProj_neg, hv, neg_neg], (neg_eq v).symm⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨-v, by rw [torusProj_neg, hv], (neg_eq v).symm⟩
theorem supNorm_add_le (p q : PeriodicTorus d S) : supNorm (p + q) ≤ supNorm p + supNorm q :=
  sInf_lifts_add_le (fun v => ‖v‖) norm_nonneg norm_add_le p q
theorem supNorm_neg (p : PeriodicTorus d S) : supNorm (-p) = supNorm p :=
  sInf_lifts_neg (fun v => ‖v‖) norm_neg p
theorem supNorm_le_norm_of_proj {p : PeriodicTorus d S} {v : Fin d → ℝ}
    (hv : torusProj d S v = p) : supNorm p ≤ ‖v‖ :=
  csInf_le ⟨0, by rintro r ⟨w, -, rfl⟩; exact norm_nonneg w⟩ ⟨v, hv, rfl⟩
theorem supNorm_zero_le : supNorm (0 : PeriodicTorus d S) ≤ 0 := by
  have h : torusProj d S (0 : Fin d → ℝ) = 0 := by
    funext μ
    simp [torusProj]
  simpa using supNorm_le_norm_of_proj h
theorem supNorm_sub_comm (p q : PeriodicTorus d S) : supNorm (p - q) = supNorm (q - p) := by
  rw [← supNorm_neg, neg_sub]
theorem supNorm_sub_le_add (p q r : PeriodicTorus d S) :
    supNorm (p - r) ≤ supNorm (p - q) + supNorm (q - r) := by
  have h := supNorm_add_le (p - q) (q - r)
  rwa [sub_add_sub_cancel] at h
theorem lOneNorm_add_le (p q : PeriodicTorus d S) :
    lOneNorm (p + q) ≤ lOneNorm p + lOneNorm q :=
  sInf_lifts_add_le (fun v => ∑ μ, |v μ|) (fun _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
    (fun v w => (Finset.sum_le_sum fun μ _ => abs_add_le (v μ) (w μ)).trans
      Finset.sum_add_distrib.le) p q
theorem lOneNorm_neg (p : PeriodicTorus d S) : lOneNorm (-p) = lOneNorm p :=
  sInf_lifts_neg (fun v => ∑ μ, |v μ|) (fun v => by simp) p
theorem lOneNorm_sub_le_add (p q r : PeriodicTorus d S) :
    lOneNorm (p - q) ≤ lOneNorm (p - r) + lOneNorm (q - r) := by
  have h := lOneNorm_add_le (p - r) (-(q - r))
  rwa [lOneNorm_neg, ← sub_eq_add_neg, sub_sub_sub_cancel_right] at h
theorem supNorm_sub_le_of_isNeighbor {ξ : ℝ} (hξ : 0 < ξ) {x x' : LatticeSite d S ξ}
    (h : IsNeighbor x x') :
    supNorm ((x' : PeriodicTorus d S) - (x : PeriodicTorus d S)) ≤ ξ := by
  obtain ⟨μ, rfl | rfl⟩ := h
  · have e : ((x + unitStep d S ξ μ : LatticeSite d S ξ) : PeriodicTorus d S) -
        (x : PeriodicTorus d S) = torusProj d S (Pi.single μ ξ) := by
      simp [unitStep]
    rw [e]
    refine (supNorm_le_norm_of_proj rfl).trans ?_
    rw [Pi.norm_single, Real.norm_of_nonneg hξ.le]
  · have e : ((x - unitStep d S ξ μ : LatticeSite d S ξ) : PeriodicTorus d S) -
        (x : PeriodicTorus d S) = -torusProj d S (Pi.single μ ξ) := by
      simp [unitStep]
    rw [e, supNorm_neg]
    refine (supNorm_le_norm_of_proj rfl).trans ?_
    rw [Pi.norm_single, Real.norm_of_nonneg hξ.le]
theorem abs_finsum_mem_le_ncard_mul {α : Type*} {s : Set α} (hs : s.Finite) (f : α → ℝ) (C : ℝ)
    (h : ∀ x ∈ s, |f x| ≤ C) : |∑ᶠ x ∈ s, f x| ≤ (s.ncard : ℝ) * C := by
  rw [finsum_mem_eq_finite_toFinset_sum f hs, Set.ncard_eq_toFinset_card s hs]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have := Finset.sum_le_card_nsmul hs.toFinset (fun x => |f x|) C
    (fun x hx => h x (hs.mem_toFinset.mp hx))
  simpa using this
end Lengths
section Places
variable {d L : ℕ} {S aMinus aPlus : ℝ} (B : BlockSetting d L aMinus aPlus S)
structure ChainGeometry : Prop where
  chain : ChainMemberFacts L B.ξ B.M B.t B.Ω
  shells : ∀ n ≤ lastNonemptyIndex B.Ω, ShellCubeFacts L B.ξ B.M B.t B.Ω n
  location : SiteLocationFacts L B.ξ B.t B.Ω
  cube_sites : ∀ n ≤ lastNonemptyIndex B.Ω, ∀ y ∈ shellSites L B.ξ B.Ω n, ∀ z : Fin d → ℝ,
    torusProj d S z = y → CubeSiteFacts L B.ξ B.Ω y z
  ncard_neighbors : ∀ x : LatticeSite d S B.ξ, {x' | IsNeighbor x x'}.ncard = 2 * d
theorem centreSpacing_pos (hL : 1 ≤ L) (y : PeriodicTorus d S) : 0 < B.centreSpacing y :=
  mul_pos (zpow_pos (by exact_mod_cast hL) _) B.isSeparatedChain.scale_pos
theorem ξ_le_centreSpacing (hL : 1 ≤ L) (y : PeriodicTorus d S) : B.ξ ≤ B.centreSpacing y := by
  have h : (1 : ℝ) ≤ (L : ℝ) ^ ((shellIndex L B.ξ B.Ω y : ℕ) : ℤ) :=
    one_le_zpow₀ (by exact_mod_cast hL) (by positivity)
  exact le_mul_of_one_le_left B.isSeparatedChain.scale_pos.le h
theorem commutatorOp_of_mem (h ψ : LatticeSite d S B.ξ → ℝ) (x : LatticeSite d S B.ξ)
    (hx : (x : PeriodicTorus d S) ∈ B.Ω 0) :
    B.commutatorOp h ψ x =
      (∑ᶠ x' ∈ {x' : LatticeSite d S B.ξ | IsNeighbor x x'},
          (B.ξ ^ 2)⁻¹ * (h x' - h x) * (ψ x' - ψ x)) -
        latticeLaplacian h x * ψ x -
        B.a (B.centreIndex (B.centreOf x)) * (B.centreSpacing (B.centreOf x) ^ 2)⁻¹ *
          (B.ξ / B.centreSpacing (B.centreOf x)) ^ d *
          ∑ᶠ x' ∈ {x' : LatticeSite d S B.ξ | (x' : PeriodicTorus d S) ∈ B.cell (B.centreOf x)},
            (h x' - h x) * ψ x' := by
  unfold BlockSetting.commutatorOp restrictTo
  exact Set.indicator_of_mem
    (show x ∈ {x : LatticeSite d S B.ξ | (x : PeriodicTorus d S) ∈ B.Ω 0} from hx) _
theorem centreOf_spec (F : ChainGeometry B) (x : LatticeSite d S B.ξ)
    (hx : (x : PeriodicTorus d S) ∈ B.Ω 0) :
    B.centreOf x ∈ B.centres ∧ (x : PeriodicTorus d S) ∈ B.cell (B.centreOf x) := by
  obtain ⟨y, hy, hint, -⟩ := F.location.exists_of_mem x x.2 hx
  exact Classical.epsilon_spec (p := fun y => y ∈ B.centres ∧ (x : PeriodicTorus d S) ∈ B.cell y)
    ⟨y, hy, interior_subset hint⟩
theorem centreOf_eq (F : ChainGeometry B) (x : LatticeSite d S B.ξ)
    (hx : (x : PeriodicTorus d S) ∈ B.Ω 0) {y : PeriodicTorus d S} (hy : y ∈ B.centres)
    (hxy : (x : PeriodicTorus d S) ∈ B.cell y) : B.centreOf x = y := by
  obtain ⟨y₀, -, -, huniq, -⟩ := F.location.exists_of_mem x x.2 hx
  have h₁ : B.centreOf x = y₀ :=
    by_contra fun hne => huniq _ (centreOf_spec B F x hx).1 hne (centreOf_spec B F x hx).2
  have h₂ : y = y₀ := by_contra fun hne => huniq y hy hne hxy
  rw [h₁, h₂]
theorem centreIndex_le_t {y : PeriodicTorus d S} (hy : y ∈ B.centres) : B.centreIndex y ≤ B.t := by
  obtain ⟨n, hnt, hn⟩ := hy
  exact (Nat.sInf_le hn).trans hnt
end Places
section Bound
variable {d L : ℕ} {S aMinus aPlus : ℝ} (B : BlockSetting d L aMinus aPlus S)
end Bound
end YangMills.Construction.Dirichlet.Commutator
