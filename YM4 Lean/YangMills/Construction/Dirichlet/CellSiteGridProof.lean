import YangMills.Construction.Dirichlet.CellSiteGrid
import YangMills.Construction.Dirichlet.CommutatorBoundsProof
import YangMills.Construction.Dirichlet.ShellCells
import YangMills.Construction.Torus.ChainScales
import YangMills.Construction.Torus.ProjSmallCubes
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Torus YangMills.Construction.Torus.NestedCubes
noncomputable section
namespace YangMills.Construction.Dirichlet.CellSiteGrid
variable {d : ℕ} {S : ℝ}
theorem torusProj_add (v w : Fin d → ℝ) : torusProj d S (v + w) = torusProj d S v + torusProj d S w := by apply _root_.YangMills.Construction.Dirichlet.Commutator.torusProj_add <;> assumption
theorem exists_int_mul_of_torusProj_eq {v w : Fin d → ℝ} (h : torusProj d S v = torusProj d S w) (μ : Fin d) :
    ∃ m : ℤ, v μ - w μ = (m : ℝ) * S := by
  have h1 : ((v μ : ℝ) : AddCircle S) = ((w μ : ℝ) : AddCircle S) := congrFun h μ
  have h2 : ((v μ - w μ : ℝ) : AddCircle S) = 0 := by
    rw [AddCircle.coe_sub, h1, sub_self]
  obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff S).1 h2
  exact ⟨m, by rw [← hm]; simp⟩
theorem mem_centeredBox_iff {N : ℝ} {h : ℕ} (hN : N = 2 * (h : ℝ) + 1) (k : Fin d → ℤ) :
    k ∈ centeredBox d N ↔ ∀ μ, |k μ| ≤ (h : ℤ) := by
  have hh : (N - 1) / 2 = (h : ℝ) := by rw [hN]; ring
  simp only [centeredBox, mem_ofPred_eq, hh]
  refine forall_congr' fun μ => ?_
  rw [← Int.cast_abs]
  exact_mod_cast Iff.rfl
theorem offsetPoint_add_single (ξ : ℝ) (z : Fin d → ℝ) (k : Fin d → ℤ) (μ : Fin d) :
    offsetPoint S ξ z (k + Pi.single μ 1) =
      offsetPoint S ξ z k + (unitStep d S ξ μ : PeriodicTorus d S) := by
  have h : (unitStep d S ξ μ : PeriodicTorus d S) = torusProj d S (Pi.single μ ξ) := rfl
  rw [h, offsetPoint, offsetPoint, ← torusProj_add]
  congr 1
  funext ν
  by_cases hν : ν = μ
  · subst hν
    simp
    ring
  · simp [Pi.single_eq_of_ne hν]
theorem offsetPoint_sub_single (ξ : ℝ) (z : Fin d → ℝ) (k : Fin d → ℤ) (μ : Fin d) :
    offsetPoint S ξ z (k - Pi.single μ 1) =
      offsetPoint S ξ z k - (unitStep d S ξ μ : PeriodicTorus d S) := by
  rw [eq_sub_iff_add_eq, ← offsetPoint_add_single]
  simp
theorem abs_single_one_le (μ ν : Fin d) : |(Pi.single μ 1 : Fin d → ℤ) ν| ≤ 1 := by
  by_cases hν : ν = μ
  · subst hν
    simp
  · simp [Pi.single_eq_of_ne hν]
theorem eq_of_offsetPoint_eq {ξ : ℝ} {N κ h : ℕ} (hξ : 0 < ξ) (hN : N = 2 * h + 1) (hκ : 0 < κ)
    (hS : S = 2 * (κ : ℝ) * ((N : ℝ) * ξ)) (z : Fin d → ℝ) {k k' : Fin d → ℤ}
    (hk : ∀ μ, |k μ| ≤ (h : ℤ)) (hk' : ∀ μ, |k' μ| ≤ (h : ℤ) + 1)
    (heq : offsetPoint S ξ z k = offsetPoint S ξ z k') : k = k' := by
  funext ν
  obtain ⟨m, hm⟩ := exists_int_mul_of_torusProj_eq (v := fun μ => z μ + ξ * (k μ : ℝ))
    (w := fun μ => z μ + ξ * (k' μ : ℝ)) heq ν
  have hint : k ν - k' ν = m * (2 * (κ : ℤ) * (N : ℤ)) := by
    have hr : ((k ν : ℝ) - (k' ν : ℝ)) = (m : ℝ) * (2 * (κ : ℝ) * (N : ℝ)) := by
      apply mul_left_cancel₀ hξ.ne'
      rw [hS] at hm
      linear_combination hm
    exact_mod_cast hr
  have hb : |k ν - k' ν| ≤ 2 * (h : ℤ) + 1 := by
    have h1 := abs_le.1 (hk ν)
    have h2 := abs_le.1 (hk' ν)
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  by_contra hne
  have hm0 : m ≠ 0 := by
    rintro rfl
    apply hne
    linarith
  have hm1 : 1 ≤ |m| := Int.one_le_abs hm0
  have hNz : (N : ℤ) = 2 * (h : ℤ) + 1 := by exact_mod_cast hN
  have hκ1 : (1 : ℤ) ≤ (κ : ℤ) := by exact_mod_cast hκ
  have hpos : (0 : ℤ) ≤ 2 * (κ : ℤ) * (N : ℤ) := by positivity
  rw [hint, abs_mul, abs_of_nonneg hpos, hNz] at hb
  nlinarith [mul_le_mul hm1 (le_refl (2 * (κ : ℤ) * (2 * (h : ℤ) + 1))) (by positivity)
    (abs_nonneg m), mul_le_mul_of_nonneg_right hκ1 (by positivity : (0 : ℤ) ≤ 2 * (2 * (h : ℤ) + 1))]
theorem exists_lattice_path_in_box (h : ℕ) (r : ℕ) : ∀ k k' : Fin d → ℤ, (∀ μ, |k μ| ≤ (h : ℤ)) →
    (∀ μ, |k' μ| ≤ (h : ℤ)) → ∑ μ, (k μ - k' μ).natAbs = r →
    ∃ p : ℕ → Fin d → ℤ, p 0 = k ∧ p r = k' ∧
      (∀ i < r, ∃ μ, p (i + 1) = p i + Pi.single μ 1 ∨ p (i + 1) = p i - Pi.single μ 1) ∧
      ∀ i ≤ r, ∀ μ, |p i μ| ≤ (h : ℤ) := by
  induction r with
  | zero =>
    intro k k' hk _ hsum
    have hkk : k = k' := by
      funext μ
      have h0 := (Finset.sum_eq_zero_iff.1 hsum) μ (Finset.mem_univ μ)
      have := Int.natAbs_eq_zero.1 h0
      linarith
    refine ⟨fun _ => k, rfl, hkk, fun i hi => absurd hi (Nat.not_lt_zero i), fun _ _ => hk⟩
  | succ r ih =>
    intro k k' hk hk' hsum
    obtain ⟨μ, hμ⟩ : ∃ μ, k μ ≠ k' μ := by
      by_contra hall
      push Not at hall
      have : ∑ μ, (k μ - k' μ).natAbs = 0 :=
        Finset.sum_eq_zero fun μ _ => by simp [hall μ]
      omega
    have main : ∀ ε : ℤ, (ε = 1 ∨ ε = -1) → 0 < ε * (k' μ - k μ) →
        (∃ ν, k + Pi.single μ ε = k + Pi.single ν 1 ∨ k + Pi.single μ ε = k - Pi.single ν 1) →
        ∃ p : ℕ → Fin d → ℤ, p 0 = k ∧ p (r + 1) = k' ∧
          (∀ i < r + 1, ∃ μ, p (i + 1) = p i + Pi.single μ 1 ∨
            p (i + 1) = p i - Pi.single μ 1) ∧
          ∀ i ≤ r + 1, ∀ μ, |p i μ| ≤ (h : ℤ) := by
      intro ε hε hpos hstep
      have hbound : ∀ ν, |(k + (Pi.single μ ε : Fin d → ℤ)) ν| ≤ (h : ℤ) := by
        intro ν
        by_cases hν : ν = μ
        · subst hν
          have h1 := abs_le.1 (hk ν)
          have h2 := abs_le.1 (hk' ν)
          simp only [Pi.add_apply, Pi.single_eq_same]
          rw [abs_le]
          rcases hε with rfl | rfl <;> constructor <;> omega
        · simpa [Pi.single_eq_of_ne hν] using hk ν
      have hsum' : ∑ ν, ((k + (Pi.single μ ε : Fin d → ℤ)) ν - k' ν).natAbs = r := by
        have e1 := Finset.add_sum_erase Finset.univ (fun ν => (k ν - k' ν).natAbs)
          (Finset.mem_univ μ)
        have e2 := Finset.add_sum_erase Finset.univ
          (fun ν => ((k + (Pi.single μ ε : Fin d → ℤ)) ν - k' ν).natAbs) (Finset.mem_univ μ)
        have e3 : ∑ ν ∈ Finset.univ.erase μ, ((k + (Pi.single μ ε : Fin d → ℤ)) ν - k' ν).natAbs =
            ∑ ν ∈ Finset.univ.erase μ, (k ν - k' ν).natAbs := by
          refine Finset.sum_congr rfl fun ν hν => ?_
          have hne : ν ≠ μ := Finset.ne_of_mem_erase hν
          simp [Pi.single_eq_of_ne hne]
        have e4 : ((k + (Pi.single μ ε : Fin d → ℤ)) μ - k' μ).natAbs + 1 = (k μ - k' μ).natAbs := by
          simp only [Pi.add_apply, Pi.single_eq_same]
          rcases hε with rfl | rfl <;> omega
        omega
      obtain ⟨q, hq0, hqr, hqs, hqb⟩ := ih _ k' hbound hk' hsum'
      refine ⟨fun i => Nat.casesOn i k q, rfl, hqr, ?_, ?_⟩
      · intro i hi
        cases i with
        | zero =>
          obtain ⟨ν, hν⟩ := hstep
          exact ⟨ν, by simpa [hq0] using hν⟩
        | succ i => exact hqs i (by omega)
      · intro i hi
        cases i with
        | zero => exact hk
        | succ i => exact hqb i (by omega)
    rcases lt_or_gt_of_ne hμ with hlt | hgt
    · exact main 1 (Or.inl rfl) (by omega) ⟨μ, Or.inl rfl⟩
    · refine main (-1) (Or.inr rfl) (by omega) ⟨μ, Or.inr ?_⟩
      rw [Pi.single_neg, sub_eq_add_neg]
theorem cellGridFacts_of_isCenteredGrid {L : ℕ} {ξ : ℝ} {Ω : ℕ → Set (PeriodicTorus d S)}
    {y : PeriodicTorus d S} {z : Fin d → ℝ} {N κ h : ℕ} (hξ : 0 < ξ) (hN : N = 2 * h + 1) (hκ : 0 < κ)
    (hσ : shellSpacing L ξ Ω y = (N : ℝ) * ξ) (hS : S = 2 * (κ : ℝ) * ((N : ℝ) * ξ))
    (hz : torusProj d S z = y) (hy : y ∈ spacingLattice d S ξ)
    (hgrid : _root_.YangMills.Construction.Torus.NestedCubes.IsCenteredGrid S ξ (shellSpacing L ξ Ω y / ξ) z
      ((spacingLattice d S ξ : Set (PeriodicTorus d S)) ∩ _root_.YangMills.Construction.Torus.siteCube L ξ Ω y))
    (hcov : ProjCubes.ProjFacts d S) : CellGridFacts L ξ Ω y z := by
  have hNξ : (N : ℝ) = shellSpacing L ξ Ω y / ξ := by
    rw [hσ]
    field_simp
  have hNR : (N : ℝ) = 2 * (h : ℝ) + 1 := by exact_mod_cast hN
  have hC : ∀ k, k ∈ centeredBox d (shellSpacing L ξ Ω y / ξ) ↔ ∀ μ, |k μ| ≤ (h : ℤ) :=
    mem_centeredBox_iff (hNξ ▸ hNR)
  have hlat : ∀ k, offsetPoint S ξ z k ∈ spacingLattice d S ξ := by
    intro k
    have hsplit : offsetPoint S ξ z k = y + torusProj d S fun μ => (k μ : ℝ) * ξ := by
      rw [← hz, offsetPoint, ← torusProj_add]
      congr 1
      funext μ
      simp [mul_comm]
    rw [hsplit]
    exact (spacingLattice d S ξ).add_mem hy ⟨k, rfl⟩
  have hblock : ∀ k, (∀ μ, |k μ| ≤ (h : ℤ)) → offsetPoint S ξ z k ∈ _root_.YangMills.Construction.Torus.siteCube L ξ Ω y := by
    intro k hk
    have : offsetPoint S ξ z k ∈ (spacingLattice d S ξ : Set (PeriodicTorus d S)) ∩ _root_.YangMills.Construction.Torus.siteCube L ξ Ω y := by
      rw [← hgrid.image_eq]
      exact mem_image_of_mem _ ((hC k).2 hk)
    exact this.2
  have hsurj : ∀ x : LatticeSite d S ξ, (x : PeriodicTorus d S) ∈ _root_.YangMills.Construction.Torus.siteCube L ξ Ω y →
      ∃ k, (∀ μ, |k μ| ≤ (h : ℤ)) ∧ offsetPoint S ξ z k = x := by
    intro x hx
    have : (x : PeriodicTorus d S) ∈ (spacingLattice d S ξ : Set (PeriodicTorus d S)) ∩ _root_.YangMills.Construction.Torus.siteCube L ξ Ω y :=
      ⟨x.2, hx⟩
    rw [← hgrid.image_eq] at this
    obtain ⟨k, hk, hkx⟩ := this
    exact ⟨k, (hC k).1 hk, hkx⟩
  have hinj : ∀ k k', (∀ μ, |k μ| ≤ (h : ℤ)) → (∀ μ, |k' μ| ≤ (h : ℤ)) →
      offsetPoint S ξ z k = offsetPoint S ξ z k' → k = k' := fun k k' hk hk' he =>
    hgrid.injOn ((hC k).2 hk) ((hC k').2 hk') he
  have hadj : ∀ k k', (∀ μ, |k μ| ≤ (h : ℤ)) → (∀ μ, |k' μ| ≤ (h : ℤ)) →
      ∀ x x' : LatticeSite d S ξ, (x : PeriodicTorus d S) = offsetPoint S ξ z k →
      (x' : PeriodicTorus d S) = offsetPoint S ξ z k' →
      (IsNeighbor x x' ↔ ∃ μ, k' = k + Pi.single μ 1 ∨ k' = k - Pi.single μ 1) := by
    intro k k' hk hk' x x' hx hx'
    constructor
    · rintro ⟨μ, hμ | hμ⟩
      · refine ⟨μ, Or.inl (eq_of_offsetPoint_eq hξ hN hκ hS z hk' ?_ ?_)⟩
        · intro ν
          have h1 := abs_le.1 (hk ν)
          have h2 := abs_le.1 (abs_single_one_le μ ν)
          simp only [Pi.add_apply]
          rw [abs_le]
          constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
        · rw [offsetPoint_add_single, ← hx, ← hx', hμ]
          rfl
      · refine ⟨μ, Or.inr (eq_of_offsetPoint_eq hξ hN hκ hS z hk' ?_ ?_)⟩
        · intro ν
          have h1 := abs_le.1 (hk ν)
          have h2 := abs_le.1 (abs_single_one_le μ ν)
          simp only [Pi.sub_apply]
          rw [abs_le]
          constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
        · rw [offsetPoint_sub_single, ← hx, ← hx', hμ]
          rfl
    · rintro ⟨μ, hμ | hμ⟩
      · refine ⟨μ, Or.inl (Subtype.ext ?_)⟩
        rw [hx', hμ, offsetPoint_add_single, ← hx]
        rfl
      · refine ⟨μ, Or.inr (Subtype.ext ?_)⟩
        rw [hx', hμ, offsetPoint_sub_single, ← hx]
        rfl
  have hlen : ∀ k k', (∀ μ, |k μ| ≤ (h : ℤ)) → (∀ μ, |k' μ| ≤ (h : ℤ)) →
      lOneNorm (offsetPoint S ξ z k - offsetPoint S ξ z k') =
        ξ * ∑ μ, |((k μ - k' μ : ℤ) : ℝ)| := by
    intro k k' hk hk'
    have hnorm : ‖(fun μ => z μ + ξ * (k μ : ℝ)) - (fun μ => z μ + ξ * (k' μ : ℝ))‖ ≤ S / 2 := by
      have hS0 : 0 ≤ S / 2 := by rw [hS]; positivity
      refine (pi_norm_le_iff_of_nonneg hS0).2 fun μ => ?_
      have hdiff : |k μ - k' μ| ≤ 2 * (h : ℤ) := by
        have h1 := abs_le.1 (hk μ)
        have h2 := abs_le.1 (hk' μ)
        rw [abs_le]
        constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
      have hdiffR : |((k μ - k' μ : ℤ) : ℝ)| ≤ 2 * (h : ℝ) := by
        rw [← Int.cast_abs]
        exact_mod_cast hdiff
      have hκ1 : (1 : ℝ) ≤ (κ : ℝ) := by exact_mod_cast hκ
      have heq : ((fun μ => z μ + ξ * (k μ : ℝ)) - (fun μ => z μ + ξ * (k' μ : ℝ))) μ =
          ξ * ((k μ - k' μ : ℤ) : ℝ) := by
        simp only [Pi.sub_apply]
        push_cast
        ring
      rw [heq, Real.norm_eq_abs, abs_mul, abs_of_pos hξ, hS, hNR]
      have h0 : (0 : ℝ) ≤ h := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hdiffR hξ.le,
        mul_le_mul_of_nonneg_right hκ1 (by positivity : (0 : ℝ) ≤ (2 * (h : ℝ) + 1) * ξ)]
    have := hcov.lOneNorm_eq _ _ hnorm
    refine this.trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    have heq : z μ + ξ * (k μ : ℝ) - (z μ + ξ * (k' μ : ℝ)) = ξ * ((k μ - k' μ : ℤ) : ℝ) := by
      push_cast
      ring
    rw [heq, abs_mul, abs_of_pos hξ]
  refine ⟨hgrid, ?_, ?_, ?_, ?_⟩
  · intro k hk k' hk' x x' hx hx'
    exact hadj k k' ((hC k).1 hk) ((hC k').1 hk') x x' hx hx'
  · refine ⟨N, hNξ, ?_⟩
    have hidx : ∀ (a : Fin d → Fin N) μ, |((a μ : ℕ) : ℤ) - (h : ℤ)| ≤ (h : ℤ) := by
      intro a μ
      have := (a μ).2
      rw [abs_le]
      constructor <;> omega
    let e₀ : (Fin d → Fin N) →
        {x : LatticeSite d S ξ // (x : PeriodicTorus d S) ∈ _root_.YangMills.Construction.Torus.siteCube L ξ Ω y} := fun a =>
      ⟨⟨offsetPoint S ξ z fun μ => ((a μ : ℕ) : ℤ) - (h : ℤ), hlat _⟩, hblock _ (hidx a)⟩
    have hbij : Function.Bijective e₀ := by
      constructor
      · intro a b hab
        have h1 : offsetPoint S ξ z (fun μ => ((a μ : ℕ) : ℤ) - (h : ℤ)) =
            offsetPoint S ξ z fun μ => ((b μ : ℕ) : ℤ) - (h : ℤ) :=
          congrArg (fun w : {x : LatticeSite d S ξ //
            (x : PeriodicTorus d S) ∈ _root_.YangMills.Construction.Torus.siteCube L ξ Ω y} => ((w.1 : LatticeSite d S ξ) : PeriodicTorus d S)) hab
        have h2 := hinj _ _ (hidx a) (hidx b) h1
        funext μ
        have h3 : ((a μ : ℕ) : ℤ) - (h : ℤ) = ((b μ : ℕ) : ℤ) - (h : ℤ) := congrFun h2 μ
        apply Fin.ext
        omega
      · rintro ⟨x, hx⟩
        obtain ⟨k, hk, hkx⟩ := hsurj x hx
        have hb : ∀ μ, (k μ + (h : ℤ)).toNat < N := by
          intro μ
          have h1 := abs_le.1 (hk μ)
          omega
        refine ⟨fun μ => ⟨(k μ + (h : ℤ)).toNat, hb μ⟩, ?_⟩
        apply Subtype.ext
        apply Subtype.ext
        change offsetPoint S ξ z (fun μ => (((k μ + (h : ℤ)).toNat : ℕ) : ℤ) - (h : ℤ)) = x
        rw [← hkx]
        congr 1
        funext μ
        have h1 := abs_le.1 (hk μ)
        omega
    refine ⟨Equiv.ofBijective e₀ hbij, fun a b => ?_⟩
    change IsNeighbor (e₀ a).1 (e₀ b).1 ↔ PathProductAdj a b
    rw [hadj _ _ (hidx a) (hidx b) (e₀ a).1 (e₀ b).1 rfl rfl]
    constructor
    · rintro ⟨μ, hμ⟩
      refine ⟨μ, ?_, ?_⟩
      · rw [SimpleGraph.pathGraph_adj]
        rcases hμ with hμ | hμ
        · have h1 := congrFun hμ μ
          simp only [Pi.add_apply, Pi.single_eq_same] at h1
          left
          omega
        · have h1 := congrFun hμ μ
          simp only [Pi.sub_apply, Pi.single_eq_same] at h1
          right
          omega
      · intro ν hν
        apply Fin.ext
        rcases hμ with hμ | hμ
        · have h1 := congrFun hμ ν
          simp only [Pi.add_apply, Pi.single_eq_of_ne hν] at h1
          omega
        · have h1 := congrFun hμ ν
          simp only [Pi.sub_apply, Pi.single_eq_of_ne hν] at h1
          omega
    · rintro ⟨μ, hμ, hν⟩
      rw [SimpleGraph.pathGraph_adj] at hμ
      refine ⟨μ, ?_⟩
      rcases hμ with hμ | hμ
      · left
        funext ν'
        by_cases hνμ : ν' = μ
        · subst hνμ
          simp only [Pi.add_apply, Pi.single_eq_same]
          omega
        · have := congrArg Fin.val (hν ν' hνμ)
          simp only [Pi.add_apply, Pi.single_eq_of_ne hνμ]
          omega
      · right
        funext ν'
        by_cases hνμ : ν' = μ
        · subst hνμ
          simp only [Pi.sub_apply, Pi.single_eq_same]
          omega
        · have := congrArg Fin.val (hν ν' hνμ)
          simp only [Pi.sub_apply, Pi.single_eq_of_ne hνμ]
          omega
  · intro x x' hx hx'
    obtain ⟨k, hk, hkx⟩ := hsurj x hx
    obtain ⟨k', hk', hkx'⟩ := hsurj x' hx'
    obtain ⟨p, hp0, hpr, hps, hpb⟩ := exists_lattice_path_in_box h _ k k' hk hk' rfl
    refine ⟨∑ μ, (k μ - k' μ).natAbs, fun i => ⟨offsetPoint S ξ z (p i), hlat _⟩, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← hkx, ← hkx', hlen k k' hk hk']
      field_simp
      push_cast
      refine Finset.sum_congr rfl fun μ _ => ?_
      rw [Nat.cast_natAbs, Int.cast_abs]
      push_cast
      rfl
    · apply Subtype.ext
      simp only [hp0, hkx]
    · apply Subtype.ext
      simp only [hpr, hkx']
    · intro i hi
      obtain ⟨μ, hμ⟩ := hps i hi
      exact (hadj (p i) (p (i + 1)) (hpb i hi.le) (hpb (i + 1) hi) _ _ rfl rfl).2 ⟨μ, hμ⟩
    · intro i hi
      exact hblock _ (hpb i hi)
  · intro x hx
    obtain ⟨k, hk, hkx⟩ := hsurj x hx
    have hy0 : y = offsetPoint S ξ z 0 := by
      rw [← hz, offsetPoint]
      congr 1
      funext μ
      simp
    have hlen0 := hlen k 0 hk (fun μ => by simp)
    rw [← hy0, hkx] at hlen0
    rw [hlen0]
    have hsum : ∑ μ, |((k μ - (0 : Fin d → ℤ) μ : ℤ) : ℝ)| ≤ (d : ℝ) * (h : ℝ) := by
      have : ∀ μ ∈ (Finset.univ : Finset (Fin d)),
          |((k μ - (0 : Fin d → ℤ) μ : ℤ) : ℝ)| ≤ (h : ℝ) := by
        intro μ _
        rw [← Int.cast_abs]
        simpa using (by exact_mod_cast hk μ : ((|k μ| : ℤ) : ℝ) ≤ (h : ℝ))
      simpa using Finset.sum_le_card_nsmul _ _ _ this
    rw [hσ, hNR]
    have h0 : (0 : ℝ) ≤ (d : ℝ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hsum hξ.le, mul_nonneg h0 hξ.le]
theorem allCellGridFacts_holds (hBlocks : ShellCells.AllShellCellFacts)
    (hSides : ChainScales.ScalesStatement)
    (hCover : ProjCubes.ProjFactsHold)
    (hNested : PropertiesOfOddRefinement) : AllCellGridFacts := by
  intro d L S ξ M R₁ t Ω hd hL hodd hsep n hn y hy z hz
  have hsides := hSides d L S ξ M R₁ t Ω (by omega) hsep
  have hblocks := hBlocks d L S ξ M R₁ t Ω hd hL hodd hsep n hn
  have hindex : shellIndex L ξ Ω y = n := hblocks.shellIndex_eq y hy
  have hξ : 0 < ξ := hsep.scale_pos
  have hsp : shellSpacing L ξ Ω y = scaleSpacing L ξ n := by
    rw [shellSpacing, hindex]
  have hspN : scaleSpacing L ξ n = ((L ^ n : ℕ) : ℝ) * ξ := by
    simp [scaleSpacing]
  obtain ⟨u, -, -, hk⟩ := hsides.side_even_multiple
  obtain ⟨κ, hκ, hS⟩ := hk (n : ℤ) (by omega)
  have hoddN : Odd (L ^ n) := hodd.pow
  obtain ⟨h, hN⟩ := hoddN
  have hnest := hNested d S (scaleSpacing L ξ n) ξ (L ^ n) (2 * κ) hd hξ hodd.pow hspN (by omega)
    (by rw [hS]; push_cast; ring)
  have hgrid := hnest.isCenteredGrid_inter_cube y hy.2.1 z hz
  have hyξ : y ∈ spacingLattice d S ξ := hnest.spacingLattice_le hy.2.1
  refine cellGridFacts_of_isCenteredGrid (N := L ^ n) (κ := κ) (h := h) hξ hN hκ (hsp.trans hspN)
    (by rw [hS, hspN]) hz hyξ ?_ (hCover d S hsep.period_pos)
  rw [_root_.YangMills.Construction.Torus.siteCube, hsp]
  exact hgrid
end YangMills.Construction.Dirichlet.CellSiteGrid
end
