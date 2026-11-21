import YangMills.Construction.Lattice.QuotientLatticesAndNeighbours
import YangMills.Construction.Torus.PointsAndTuplesOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.TorusMetric
noncomputable section
namespace YangMills.Construction.QuotientLattices
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.AmbientPoints (torusEuclidNorm_eq_sqrt torusEuclidNorm_torusProj_le
  exists_torusProj_eq_euclidNormVec_eq torusEuclidNorm_sub_self torusEuclidNorm_sub_comm
  eq_of_torusEuclidNorm_sub_eq_zero euclidNormVec_sub_self euclidNormVec_sub_comm
  eq_of_euclidNormVec_sub_eq_zero)
theorem addCircle_coe_mul_intCast_eq_zero (S : ℝ) (t : ℤ) :
    ((S * (t : ℝ) : ℝ) : AddCircle S) = 0 :=
  (AddCircle.coe_eq_zero_iff S).2 ⟨t, by simp [mul_comm]⟩
theorem isLeast_torusEuclidNorm_periodShiftedDiff (S : ℝ) (a b : AmbientSpace) :
    IsLeast (range fun n : Fin 4 → ℤ => euclidNormVec (periodShiftedDiff S a b n))
      (torusEuclidNorm (torusProj S a - torusProj S b)) := by
  constructor
  · obtain ⟨v, hv, hv'⟩ := exists_torusProj_eq_euclidNormVec_eq (torusProj S a - torusProj S b)
    have hz : ∀ μ, ∃ t : ℤ, v μ = a μ - b μ + S * (t : ℝ) := by
      intro μ
      have h : ((v μ : ℝ) : AddCircle S) = ((a μ - b μ : ℝ) : AddCircle S) := by
        rw [AddCircle.coe_sub]
        exact congrFun hv μ
      rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff] at h
      obtain ⟨t, ht⟩ := h
      refine ⟨t, ?_⟩
      rw [zsmul_eq_mul] at ht
      linarith
    choose n hn using hz
    refine ⟨n, ?_⟩
    change euclidNormVec (periodShiftedDiff S a b n) = _
    rw [← hv']
    congr 1
    funext μ
    simp [periodShiftedDiff, hn μ]
  · rintro _ ⟨n, rfl⟩
    have h : torusProj S a - torusProj S b = torusProj S (periodShiftedDiff S a b n) := by
      funext μ
      change ((a μ : ℝ) : AddCircle S) - ((b μ : ℝ) : AddCircle S) =
        ((a μ - b μ + S * (n μ : ℝ) : ℝ) : AddCircle S)
      rw [AddCircle.coe_add, addCircle_coe_mul_intCast_eq_zero, add_zero, AddCircle.coe_sub]
    change _ ≤ euclidNormVec (periodShiftedDiff S a b n)
    rw [h]
    exact torusEuclidNorm_torusProj_le _
theorem minPeriodicDist_eq_torusEuclidNorm (S : ℝ) (a b : AmbientSpace) :
    minPeriodicDist S a b = torusEuclidNorm (torusProj S a - torusProj S b) :=
  (isLeast_torusEuclidNorm_periodShiftedDiff S a b).csInf_eq
theorem minPeriodicDistOfClasses_holds (S : ℝ) : MinPeriodicDistOfClasses S := by
  intro a b
  refine ⟨?_, fun a' b' ha hb => ?_, fun h => ?_, minPeriodicDist_eq_torusEuclidNorm S a b⟩
  · rw [minPeriodicDist_eq_torusEuclidNorm]
    exact isLeast_torusEuclidNorm_periodShiftedDiff S a b
  · rw [minPeriodicDist_eq_torusEuclidNorm, minPeriodicDist_eq_torusEuclidNorm, ha, hb]
  · rw [minPeriodicDist_eq_torusEuclidNorm] at h
    exact eq_of_torusEuclidNorm_sub_eq_zero _ _ h
section SignedSteps
variable {X : Type} [AddCommGroup X]
theorem isSignedAxisStep_unique {e : Fin 4 → X} (hinj : Function.Injective (unitStepsWithZero e))
    {x x' : X} {ε ε' : ℤˣ} {μ μ' : Fin 4} (h : IsSignedAxisStep e x x' ε μ)
    (h' : IsSignedAxisStep e x x' ε' μ') : ε = ε' ∧ μ = μ' := by
  have e₁ : unitStepsWithZero e (some (ε, μ)) = unitStepsWithZero e (some (ε', μ')) := by
    change (ε : ℤ) • e μ = (ε' : ℤ) • e μ'
    rw [← show x' - x = (ε : ℤ) • e μ from h, ← show x' - x = (ε' : ℤ) • e μ' from h']
  have e₂ := hinj e₁
  simpa using e₂
theorem stepsDistinctAndSigned_of_injective {Λ : AddSubgroup X} {e : Fin 4 → X}
    (hmem : ∀ μ, e μ ∈ Λ) (hinj : Function.Injective (unitStepsWithZero e)) :
    StepsDistinctAndSigned Λ e := by
  refine ⟨?_, hinj, fun x _ x' _ =>
    ⟨fun ε μ ε' μ' h h' => isSignedAxisStep_unique hinj h h', ?_⟩⟩
  · rintro (_ | ⟨ε, μ⟩)
    · exact Λ.zero_mem
    · exact Λ.zsmul_mem (hmem μ) _
  · intro ε μ h
    have hneg : IsSignedAxisStep e x' x (-ε) μ := by
      have h₁ : x' - x = (ε : ℤ) • e μ := h
      change x - x' = ((-ε : ℤˣ) : ℤ) • e μ
      rw [Units.val_neg, neg_smul, ← h₁]
      abel
    refine ⟨hneg, ?_⟩
    rcases Int.units_eq_one_or ε with rfl | rfl
    · refine Or.inl ⟨⟨μ, h⟩, ?_⟩
      rintro ⟨ν, hν⟩
      exact absurd (isSignedAxisStep_unique hinj hneg hν).1 (by decide)
    · have hneg' : IsSignedAxisStep e x' x 1 μ := by simpa using hneg
      refine Or.inr ⟨⟨μ, hneg'⟩, ?_⟩
      rintro ⟨ν, hν⟩
      exact absurd (isSignedAxisStep_unique hinj h hν).1 (by decide)
theorem neighboursAtSpacing_of_dist {d : X → X → ℝ} {Λ : AddSubgroup X} {a : ℝ} {e : Fin 4 → X}
    (hself : ∀ p, d p p = 0) (hzero : ∀ p q, d p q = 0 → p = q)
    (hpair : ∀ x ∈ Λ, ∀ x' ∈ Λ, d x x' = a ↔ AreNeighbours e x x') :
    NeighboursAtSpacing d Λ a e := by
  refine ⟨hpair, fun s hs himg => ?_⟩
  have hmaps : ∀ x ∈ Λ, s x ∈ Λ := fun x hx => by
    have h : s x ∈ s '' (Λ : Set X) := ⟨x, hx, rfl⟩
    rw [himg] at h
    exact h
  have hsurj : ∀ y ∈ Λ, ∃ x ∈ (Λ : Set X), s x = y := fun y hy => by
    have h : y ∈ s '' (Λ : Set X) := by
      rw [himg]
      exact hy
    exact h
  refine ⟨fun x _ y _ h => hzero x y ?_, ?_, ?_⟩
  · rw [← hs x y, h, hself]
  · intro x hx x' hx' h
    exact (hpair _ (hmaps x hx) _ (hmaps x' hx')).1
      (by rw [hs]; exact (hpair x hx x' hx').2 h)
  · intro y hy y' hy' h
    have i₁ := Function.invFunOn_mem (hsurj y hy)
    have i₂ := Function.invFunOn_mem (hsurj y' hy')
    refine (hpair _ i₁ _ i₂).1 ?_
    rw [← hs, Function.invFunOn_eq (hsurj y hy), Function.invFunOn_eq (hsurj y' hy')]
    exact (hpair y hy y' hy').2 h
end SignedSteps
def unitIntVectors : Option (ℤˣ × Fin 4) → Fin 4 → ℤ
  | none => 0
  | some q => Pi.single q.2 (q.1 : ℤ)
theorem abs_unitIntVectors_le (q : Option (ℤˣ × Fin 4)) (μ : Fin 4) :
    |unitIntVectors q μ| ≤ 1 := by
  rcases q with _ | ⟨ε, ν⟩
  · simp [unitIntVectors]
  · by_cases h : μ = ν
    · subst h
      rcases Int.units_eq_one_or ε with rfl | rfl <;> simp [unitIntVectors]
    · simp [unitIntVectors, Pi.single_eq_of_ne h]
theorem unitIntVectors_injective : Function.Injective unitIntVectors := by
  rintro (_ | ⟨ε, μ⟩) (_ | ⟨ε', μ'⟩) h
  · rfl
  · have h₁ := congrFun h μ'
    simp [unitIntVectors] at h₁
    exact absurd h₁.symm ε'.ne_zero
  · have h₁ := congrFun h μ
    simp [unitIntVectors] at h₁
  · by_cases hμ : μ = μ'
    · subst hμ
      have h₁ := congrFun h μ
      simp only [unitIntVectors, Pi.single_eq_same] at h₁
      rw [Units.ext h₁]
    · have h₁ := congrFun h μ
      simp [unitIntVectors, Pi.single_eq_of_ne hμ] at h₁
theorem eq_of_unitIntVectors_modEq {M : ℤ} (hM : 2 < M) {q q' : Option (ℤˣ × Fin 4)}
    (h : ∀ μ, unitIntVectors q μ ≡ unitIntVectors q' μ [ZMOD M]) : q = q' := by
  apply unitIntVectors_injective
  funext μ
  have h₁ : M ∣ unitIntVectors q' μ - unitIntVectors q μ := (Int.modEq_iff_dvd).1 (h μ)
  have h₂ : |unitIntVectors q' μ - unitIntVectors q μ| < M := by
    have a₁ := abs_le.1 (abs_unitIntVectors_le q μ)
    have a₂ := abs_le.1 (abs_unitIntVectors_le q' μ)
    rw [abs_lt]
    constructor <;> linarith [a₁.1, a₁.2, a₂.1, a₂.2]
  have h₃ := Int.eq_zero_of_abs_lt_dvd h₁ h₂
  linarith
theorem scaledIntVector_single (a : ℝ) (μ : Fin 4) :
    scaledIntVector a (Pi.single μ 1) = Pi.single μ a := by
  funext ν
  by_cases h : ν = μ
  · subst h
    simp [scaledIntVector]
  · simp [scaledIntVector, Pi.single_eq_of_ne h]
theorem unitStepsWithZero_scaledIntVector (a : ℝ) (q : Option (ℤˣ × Fin 4)) :
    unitStepsWithZero (fun μ => scaledIntVector a (Pi.single μ 1)) q =
      scaledIntVector a (unitIntVectors q) := by
  rcases q with _ | ⟨ε, μ⟩
  · funext ν
    simp [unitStepsWithZero, unitIntVectors, scaledIntVector]
  · funext ν
    by_cases h : ν = μ
    · subst h
      simp [unitStepsWithZero, unitIntVectors, scaledIntVector]
    · simp [unitStepsWithZero, unitIntVectors, scaledIntVector, Pi.single_eq_of_ne h]
theorem torusProj_zsmul (S : ℝ) (c : ℤ) (v : AmbientSpace) :
    c • torusProj S v = torusProj S (c • v) := by
  funext μ
  change c • ((v μ : ℝ) : AddCircle S) = ((c • v μ : ℝ) : AddCircle S)
  simp
theorem unitStepsWithZero_torusProj (S : ℝ) (f : Fin 4 → AmbientSpace) (q : Option (ℤˣ × Fin 4)) :
    unitStepsWithZero (fun μ => torusProj S (f μ)) q = torusProj S (unitStepsWithZero f q) := by
  rcases q with _ | ⟨ε, μ⟩
  · funext ν
    simp [unitStepsWithZero, torusProj]
  · exact torusProj_zsmul S _ _
section Classes
variable {S a : ℝ} {M : ℕ}
theorem torusProj_scaledIntVector_eq_iff (ha : a ≠ 0) (hS : S = (M : ℝ) * a) (N N' : Fin 4 → ℤ) :
    torusProj S (scaledIntVector a N) = torusProj S (scaledIntVector a N') ↔
      ∀ μ, N μ ≡ N' μ [ZMOD (M : ℤ)] := by
  constructor
  · intro h μ
    have h₁ : (((N' μ : ℝ) * a : ℝ) : AddCircle S) = (((N μ : ℝ) * a : ℝ) : AddCircle S) :=
      (congrFun h μ).symm
    rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff] at h₁
    obtain ⟨t, ht⟩ := h₁
    rw [zsmul_eq_mul, hS] at ht
    have h₂ : (t : ℝ) * (M : ℝ) = (N' μ : ℝ) - (N μ : ℝ) := by
      apply mul_right_cancel₀ ha
      rw [sub_mul, ← ht]
      ring
    have h₃ : t * (M : ℤ) = N' μ - N μ := by exact_mod_cast h₂
    exact (Int.modEq_iff_dvd).2 ⟨t, by rw [← h₃]; ring⟩
  · intro h
    funext μ
    obtain ⟨t, ht⟩ := (Int.modEq_iff_dvd).1 (h μ)
    change (((N μ : ℝ) * a : ℝ) : AddCircle S) = (((N' μ : ℝ) * a : ℝ) : AddCircle S)
    have ht' : (N' μ : ℝ) - (N μ : ℝ) = (M : ℝ) * (t : ℝ) := by exact_mod_cast ht
    symm
    rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
    refine ⟨t, ?_⟩
    rw [zsmul_eq_mul, hS, ← sub_mul, ht']
    ring
theorem euclidNormVec_scaledIntVector (ha : 0 < a) (r : Fin 4 → ℤ) :
    euclidNormVec (scaledIntVector a r) = a * Real.sqrt (∑ μ, (r μ : ℝ) ^ 2) := by
  have h : ∀ μ, scaledIntVector a r μ ^ 2 = a ^ 2 * (r μ : ℝ) ^ 2 := fun μ => by
    simp only [scaledIntVector]
    ring
  simp only [euclidNormVec, h]
  rw [← Finset.mul_sum, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha.le]
theorem exists_shortest_representative (ha : 0 < a) (hS : S = (M : ℝ) * a) (N : Fin 4 → ℤ) :
    ∃ r : Fin 4 → ℤ, torusProj S (scaledIntVector a r) = torusProj S (scaledIntVector a N) ∧
      torusEuclidNorm (torusProj S (scaledIntVector a N)) = a * Real.sqrt (∑ μ, (r μ : ℝ) ^ 2) := by
  obtain ⟨b, hb, hb'⟩ := exists_torusProj_eq_euclidNormVec_eq (torusProj S (scaledIntVector a N))
  have hz : ∀ μ, ∃ r : ℤ, b μ = (r : ℝ) * a := by
    intro μ
    have h : ((b μ : ℝ) : AddCircle S) = (((N μ : ℝ) * a : ℝ) : AddCircle S) := congrFun hb μ
    rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff] at h
    obtain ⟨t, ht⟩ := h
    rw [zsmul_eq_mul, hS] at ht
    refine ⟨N μ + t * (M : ℤ), ?_⟩
    push_cast
    linarith
  choose r hr using hz
  have hbr : b = scaledIntVector a r := funext hr
  subst hbr
  exact ⟨r, hb, by rw [← hb', euclidNormVec_scaledIntVector ha]⟩
theorem torusEuclidNorm_torusProj_of_abs_le (hS₀ : 0 < S) (v : AmbientSpace)
    (hv : ∀ μ, |v μ| ≤ S / 2) :
    torusEuclidNorm (torusProj S v) = euclidNormVec v := by
  rw [torusEuclidNorm_eq_sqrt]
  have h : ∀ μ, ‖torusProj S v μ‖ ^ 2 = v μ ^ 2 := fun μ => by
    have h₁ : ‖((v μ : ℝ) : AddCircle S)‖ = |v μ| :=
      (AddCircle.norm_coe_eq_abs_iff S hS₀.ne').2 (by rw [abs_of_pos hS₀]; exact hv μ)
    change ‖((v μ : ℝ) : AddCircle S)‖ ^ 2 = _
    rw [h₁, sq_abs]
  simp only [euclidNormVec, h]
def torusClassSteps (S a : ℝ) (μ : Fin 4) : Torus4 S :=
  torusProj S (scaledIntVector a (Pi.single μ 1))
theorem unitStepsWithZero_torusClassSteps (q : Option (ℤˣ × Fin 4)) :
    unitStepsWithZero (torusClassSteps S a) q =
      torusProj S (scaledIntVector a (unitIntVectors q)) := by
  rw [← unitStepsWithZero_scaledIntVector]
  exact unitStepsWithZero_torusProj S (fun μ => scaledIntVector a (Pi.single μ 1)) q
theorem unitStepsWithZero_torusClassSteps_injective (ha : a ≠ 0) (hS : S = (M : ℝ) * a)
    (hM : 2 < M) : Function.Injective (unitStepsWithZero (torusClassSteps S a)) := by
  intro q q' h
  rw [unitStepsWithZero_torusClassSteps, unitStepsWithZero_torusClassSteps,
    torusProj_scaledIntVector_eq_iff ha hS] at h
  exact eq_of_unitIntVectors_modEq (by exact_mod_cast hM) h
theorem torusEuclidNorm_eq_mesh_iff (ha : 0 < a) (hS : S = (M : ℝ) * a) (hM : 2 < M)
    (N : Fin 4 → ℤ) :
    torusEuclidNorm (torusProj S (scaledIntVector a N)) = a ↔
      ∃ (ε : ℤˣ) (μ : Fin 4),
        torusProj S (scaledIntVector a N) = (ε : ℤ) • torusClassSteps S a μ := by
  have hM' : (2 : ℝ) < M := by exact_mod_cast hM
  have hS₀ : 0 < S := by
    rw [hS]
    positivity
  constructor
  · intro h
    obtain ⟨r, hr, he⟩ := exists_shortest_representative ha hS N
    rw [h] at he
    have h₁ : Real.sqrt (∑ μ, (r μ : ℝ) ^ 2) = 1 :=
      (mul_left_cancel₀ ha.ne' (he.symm.trans (mul_one a).symm))
    have h₂ : ∑ μ, (r μ : ℝ) ^ 2 = 1 := by
      have h₃ := Real.sq_sqrt (show 0 ≤ ∑ μ, (r μ : ℝ) ^ 2 from
        Finset.sum_nonneg fun μ _ => sq_nonneg (r μ : ℝ))
      rw [h₁] at h₃
      linarith
    have h₃ : ∑ μ, r μ ^ 2 = 1 := by exact_mod_cast h₂
    obtain ⟨μ, h₄ | h₄⟩ := InfiniteLattice.int_vec_unit_of_sum_sq_eq_one r h₃
    · refine ⟨1, μ, ?_⟩
      rw [← hr, h₄]
      have h₅ := unitStepsWithZero_torusClassSteps (S := S) (a := a) (some (1, μ))
      simpa [unitStepsWithZero, unitIntVectors] using h₅.symm
    · refine ⟨-1, μ, ?_⟩
      rw [← hr, h₄]
      have h₅ := unitStepsWithZero_torusClassSteps (S := S) (a := a) (some (-1, μ))
      simpa [unitStepsWithZero, unitIntVectors, Pi.single_neg] using h₅.symm
  · rintro ⟨ε, μ, h⟩
    have h₁ : torusProj S (scaledIntVector a N) =
        torusProj S (scaledIntVector a (unitIntVectors (some (ε, μ)))) := by
      rw [h, ← unitStepsWithZero_torusClassSteps]
      rfl
    rw [h₁, torusEuclidNorm_torusProj_of_abs_le hS₀]
    · rw [euclidNormVec_scaledIntVector ha]
      have h₂ : ∑ ν, (unitIntVectors (some (ε, μ)) ν : ℝ) ^ 2 = 1 := by
        rw [Finset.sum_eq_single μ]
        · rcases Int.units_eq_one_or ε with rfl | rfl <;> simp [unitIntVectors]
        · intro ν _ hν
          simp [unitIntVectors, Pi.single_eq_of_ne hν]
        · simp
      rw [h₂, Real.sqrt_one, mul_one]
    · intro ν
      have h₂ : |(unitIntVectors (some (ε, μ)) ν : ℝ)| ≤ 1 := by
        exact_mod_cast abs_unitIntVectors_le _ ν
      simp only [scaledIntVector, abs_mul, abs_of_pos ha]
      rw [hS]
      nlinarith
end Classes
section AmbientLattice
variable {a : ℝ}
theorem spaceAxisSteps_apply (a : ℝ) (μ : Fin 4) :
    spaceAxisSteps a μ = scaledIntVector a (Pi.single μ 1) :=
  (scaledIntVector_single a μ).symm
theorem spaceAxisSteps_eq (a : ℝ) :
    spaceAxisSteps a = fun μ => scaledIntVector a (Pi.single μ 1) :=
  funext (spaceAxisSteps_apply a)
theorem unitStepsWithZero_spaceAxisSteps_injective (ha : a ≠ 0) :
    Function.Injective (unitStepsWithZero (spaceAxisSteps a)) := by
  intro q q' h
  rw [spaceAxisSteps_eq, unitStepsWithZero_scaledIntVector, unitStepsWithZero_scaledIntVector] at h
  apply unitIntVectors_injective
  funext μ
  have h₁ := congrFun h μ
  simp only [scaledIntVector] at h₁
  exact_mod_cast mul_right_cancel₀ ha h₁
theorem spaceAxisSteps_mem (a : ℝ) (μ : Fin 4) :
    spaceAxisSteps a μ ∈ InfiniteLattice.latticeSubgroup a :=
  (InfiniteLattice.axisStep a μ).2
theorem spaceDist_eq_iff_areNeighbours (ha : 0 < a) :
    ∀ x ∈ InfiniteLattice.latticeSubgroup a, ∀ x' ∈ InfiniteLattice.latticeSubgroup a,
      spaceDist x x' = a ↔ AreNeighbours (spaceAxisSteps a) x x' := by
  intro x hx x' hx'
  constructor
  · intro h
    have h₁ : euclidNormVec (x' - x) = |a| := by
      rw [euclidNormVec_sub_comm, abs_of_pos ha]
      exact h
    obtain ⟨μ, h₂ | h₂⟩ := InfiniteLattice.isAdjacent_of_euclidNormVec ⟨x, hx⟩ ⟨x', hx'⟩ h₁
    · refine ⟨1, μ, ?_⟩
      have h₃ := congrArg Subtype.val h₂
      change x' - x = _ at h₃
      change x' - x = _
      rw [h₃]
      simp [spaceAxisSteps]
    · refine ⟨-1, μ, ?_⟩
      have h₃ := congrArg Subtype.val h₂
      change x' - x = _ at h₃
      change x' - x = _
      rw [h₃]
      simp [spaceAxisSteps]
  · rintro ⟨ε, μ, h⟩
    have h₁ : x' - x = (ε : ℤ) • spaceAxisSteps a μ := h
    change euclidNormVec (x - x') = a
    rw [euclidNormVec_sub_comm, h₁]
    rcases Int.units_eq_one_or ε with rfl | rfl
    · have h₂ : ((1 : ℤˣ) : ℤ) • spaceAxisSteps a μ = Pi.single μ a := by
        simp [spaceAxisSteps, InfiniteLattice.axisStep]
      rw [h₂, InfiniteLattice.euclidNormVec_single, abs_of_pos ha]
    · have h₂ : ((-1 : ℤˣ) : ℤ) • spaceAxisSteps a μ = Pi.single μ (-a) := by
        simp [spaceAxisSteps, InfiniteLattice.axisStep, Pi.single_neg]
      rw [h₂, InfiniteLattice.euclidNormVec_single, abs_neg, abs_of_pos ha]
end AmbientLattice
theorem torusAxisSteps_eq (L n k j : ℕ) :
    torusAxisSteps L n k j =
      torusClassSteps (PeriodicLattice.torusSide L n)
        (PeriodicLattice.meshSize L (refinementIndex k j)) := by
  funext μ ν
  by_cases h : ν = μ
  · subst h
    simp [torusAxisSteps, PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, torusClassSteps,
      torusProj, scaledIntVector]
  · simp [torusAxisSteps, PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, torusClassSteps,
      torusProj, scaledIntVector, Pi.single_eq_of_ne h]
theorem exists_coords_of_mem_sublattice {L n : ℕ} {i : ℤ} {x : PeriodicLattice.FourTorus L n}
    (hx : x ∈ PeriodicLattice.sublattice L n i) :
    ∃ N : Fin 4 → ℤ,
      x = torusProj (PeriodicLattice.torusSide L n) (scaledIntVector (PeriodicLattice.meshSize L i) N) := by
  obtain ⟨N, hN⟩ := hx
  exact ⟨N, funext hN⟩
theorem torusDist_eq_iff_areNeighbours {L n k j M : ℕ}
    (ha : 0 < PeriodicLattice.meshSize L (refinementIndex k j))
    (hS : PeriodicLattice.torusSide L n = (M : ℝ) * PeriodicLattice.meshSize L (refinementIndex k j))
    (hM : 2 < M) :
    ∀ x ∈ PeriodicLattice.sublattice L n (refinementIndex k j),
      ∀ x' ∈ PeriodicLattice.sublattice L n (refinementIndex k j),
        torusDist L n x x' = PeriodicLattice.meshSize L (refinementIndex k j) ↔
          AreNeighbours (torusAxisSteps L n k j) x x' := by
  intro x hx x' hx'
  obtain ⟨N, hN⟩ :=
    exists_coords_of_mem_sublattice ((PeriodicLattice.sublattice L n _).sub_mem hx' hx)
  have h₁ : torusDist L n x x' = torusEuclidNorm (x' - x) := torusEuclidNorm_sub_comm x x'
  rw [h₁, hN, torusEuclidNorm_eq_mesh_iff ha hS hM, ← hN, torusAxisSteps_eq]
  exact Iff.rfl
theorem isQuotientLattice_of_coords {L n k j : ℕ} (hL : 0 < L) (hn : 1 ≤ n) (hjk : j ≤ k)
    (hc : PeriodicLattice.torusSide L n / PeriodicLattice.meshSize L (refinementIndex k j) =
      (sitesPerAxis L n k j : ℝ))
    (ha : 0 < PeriodicLattice.meshSize L (refinementIndex k j))
    (hS : PeriodicLattice.torusSide L n =
      (sitesPerAxis L n k j : ℝ) * PeriodicLattice.meshSize L (refinementIndex k j))
    (hM : 2 * L ≤ sitesPerAxis L n k j)
    (hcoords : ∀ y x : PeriodicLattice.Site L n (refinementIndex k j),
      ∃ N : Fin 4 → ℤ, x = PeriodicLattice.offsetSite y N)
    (hcong : ∀ (y : PeriodicLattice.Site L n (refinementIndex k j)) (N N' : Fin 4 → ℤ),
      PeriodicLattice.offsetSite y N = PeriodicLattice.offsetSite y N' ↔
        ∀ μ, N μ ≡ N' μ [ZMOD (sitesPerAxis L n k j : ℕ)])
    (halong : ∀ (y : PeriodicLattice.Site L n (refinementIndex k j)) (μ : Fin 4),
      (PeriodicLattice.axisLine y μ).ncard = sitesPerAxis L n k j) :
    IsQuotientLattice L n k j := by
  have hi : 0 ≤ refinementIndex k j := by
    simp only [refinementIndex]
    omega
  have hM0 : 0 < sitesPerAxis L n k j := by omega
  have hsite : Finite (PeriodicLattice.Site L n (refinementIndex k j)) := by
    let f : (Fin 4 → Fin (sitesPerAxis L n k j)) →
        PeriodicLattice.Site L n (refinementIndex k j) :=
      fun r => PeriodicLattice.offsetSite 0 fun μ => ((r μ : ℕ) : ℤ)
    have hf : Function.Surjective f := by
      intro x
      obtain ⟨N, rfl⟩ := hcoords 0 x
      have hMz : (0 : ℤ) < (sitesPerAxis L n k j : ℕ) := by exact_mod_cast hM0
      have hnn : ∀ μ, 0 ≤ N μ % ((sitesPerAxis L n k j : ℕ) : ℤ) := fun μ =>
        Int.emod_nonneg _ hMz.ne'
      refine ⟨fun μ => ⟨(N μ % ((sitesPerAxis L n k j : ℕ) : ℤ)).toNat, ?_⟩, ?_⟩
      · have := Int.emod_lt_of_pos (N μ) hMz
        have := hnn μ
        omega
      · refine (hcong 0 _ _).2 fun μ => ?_
        change (((N μ % ((sitesPerAxis L n k j : ℕ) : ℤ)).toNat : ℕ) : ℤ) ≡ _ [ZMOD _]
        rw [Int.toNat_of_nonneg (hnn μ)]
        exact Int.mod_modEq _ _
    exact Finite.of_surjective f hf
  refine ⟨hi, by omega, by omega, ?_, hc, hM, ?_, ?_, ?_, halong, hsite, ?_, ?_⟩
  · change (L : ℝ) ^ (-refinementIndex k j) = _
    rw [show -refinementIndex k j = (j : ℤ) - (k : ℤ) by simp [refinementIndex]]
  · rintro x ⟨N, hN⟩
    refine ⟨fun μ => N μ * ((sitesPerAxis L n k j : ℕ) : ℤ), fun μ => ?_⟩
    rw [hN μ, hS]
    push_cast
    ring
  · ext x
    constructor
    · rintro ⟨N, hN⟩
      exact ⟨scaledIntVector _ N, ⟨N, fun μ => rfl⟩, funext fun μ => (hN μ).symm⟩
    · rintro ⟨v, ⟨N, hN⟩, rfl⟩
      refine ⟨N, fun μ => ?_⟩
      change ((v μ : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) = _
      rw [hN μ]
  · exact torusProj_scaledIntVector_eq_iff ha.ne' hS
  · exact Finite.of_injective
      (fun b : PeriodicLattice.Bond L n (refinementIndex k j) => (b.source, b.target))
      fun b c h => PeriodicLattice.Bond.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  · exact Finite.of_injective
      (fun p : PeriodicLattice.Plaquette L n (refinementIndex k j) =>
        (p.origin, p.firstAxis, p.secondAxis))
      fun p q h => by
        have h₁ : p.origin = q.origin := congrArg Prod.fst h
        have h₂ : p.firstAxis = q.firstAxis := congrArg (fun t => t.2.1) h
        have h₃ : p.secondAxis = q.secondAxis := congrArg (fun t => t.2.2) h
        exact PeriodicLattice.Plaquette.ext h₁ h₂ h₃
theorem straightPathLengthCriterion_holds {L : ℕ} (hL : 0 < L) (n k j : ℕ) :
    StraightPathLengthCriterion L n k j := by
  intro t
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have e₁ : (L : ℝ) ^ ((n : ℤ) + refinementIndex k j) =
      (L : ℝ) ^ n * (L : ℝ) ^ refinementIndex k j := by
    rw [zpow_add₀ hL0.ne', zpow_natCast]
  have e₂ : PeriodicLattice.meshSize L (refinementIndex k j) =
      ((L : ℝ) ^ refinementIndex k j)⁻¹ :=
    zpow_neg _ _
  have e₃ : PeriodicLattice.torusSide L n / 2 = (L : ℝ) ^ n := by
    simp [PeriodicLattice.torusSide]
  rw [e₁, e₂, e₃, ← div_eq_mul_inv, div_lt_iff₀ (zpow_pos hL0 _)]
theorem torusAndSpaceLatticeProperties_of_coordinateDescription
    (h : PeriodicLattice.CoordinateDescription) : TorusAndSpaceLatticeProperties := by
  intro L hL n j k hn hjk
  obtain ⟨hodd, hbig⟩ := hL
  have hL₀ : 0 < L := by omega
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL₀
  have hindex : -(n : ℤ) ≤ refinementIndex k j := by
    simp only [refinementIndex]
    omega
  have hcoord := (h L n hodd hbig (by omega)).1 (refinementIndex k j) hindex
  have hMeq : 2 * PeriodicLattice.halfPeriod L n (refinementIndex k j) =
      sitesPerAxis L n k j := by
    have e : ((n : ℤ) + refinementIndex k j).toNat = n + k - j := by
      simp only [refinementIndex]
      omega
    simp only [sitesPerAxis, PeriodicLattice.halfPeriod, e]
  unfold PeriodicLattice.SublatticeCoordinates at hcoord
  rw [hMeq] at hcoord
  have ha : 0 < PeriodicLattice.meshSize L (refinementIndex k j) := zpow_pos hL0 _
  have hS : PeriodicLattice.torusSide L n =
      (sitesPerAxis L n k j : ℝ) * PeriodicLattice.meshSize L (refinementIndex k j) := by
    rw [← hcoord.1, div_mul_cancel₀ _ ha.ne']
  have hM : 2 * L ≤ sitesPerAxis L n k j := by
    have h₁ : L ≤ L ^ (n + k - j) := Nat.le_self_pow (by omega) L
    simp only [sitesPerAxis]
    omega
  have hM2 : 2 < sitesPerAxis L n k j := by omega
  have hinj : Function.Injective (unitStepsWithZero (torusAxisSteps L n k j)) := by
    rw [torusAxisSteps_eq]
    exact unitStepsWithZero_torusClassSteps_injective ha.ne' hS hM2
  refine ⟨⟨n, by omega, rfl⟩,
    isQuotientLattice_of_coords hL₀ hn hjk hcoord.1 ha hS hM hcoord.2.2.2.1 hcoord.2.2.2.2.1
      hcoord.2.2.2.2.2.1,
    straightPathLengthCriterion_holds hL₀ n k j,
    fun hk => ⟨⟨⟨k, by omega⟩, rfl⟩, rfl⟩,
    minPeriodicDistOfClasses_holds _,
    stepsDistinctAndSigned_of_injective (fun μ => (PeriodicLattice.unitStep L n _ μ).2) hinj,
    stepsDistinctAndSigned_of_injective (spaceAxisSteps_mem _)
      (unitStepsWithZero_spaceAxisSteps_injective ha.ne'),
    neighboursAtSpacing_of_dist (fun p => torusEuclidNorm_sub_self p)
      (fun p q e => eq_of_torusEuclidNorm_sub_eq_zero p q e)
      (torusDist_eq_iff_areNeighbours ha hS hM2),
    neighboursAtSpacing_of_dist (fun p => euclidNormVec_sub_self p)
      (fun p q e => eq_of_euclidNormVec_sub_eq_zero p q e)
      (spaceDist_eq_iff_areNeighbours ha)⟩
end YangMills.Construction.QuotientLattices
