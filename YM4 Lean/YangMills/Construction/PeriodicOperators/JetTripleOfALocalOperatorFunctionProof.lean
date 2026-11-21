import YangMills.Construction.PeriodicOperators.JetTripleOfALocalOperatorFunction
import YangMills.Construction.PeriodicOperators.KernelsOfALocalOperatorFunction
import YangMills.Construction.PeriodicOperators.TaylorCoefficientsOfALocalOperatorFunction
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators.LocalOpFunTriple
open JetDomains
open LocalOpFunTaylor
theorem bilinDot_add_left (a b y : Fin 4 → ℂ) : bilinDot (a + b) y = bilinDot a y + bilinDot b y := by
  simp [bilinDot, add_mul, Finset.sum_add_distrib]
theorem bilinDot_smul_left (c : ℂ) (a y : Fin 4 → ℂ) : bilinDot (c • a) y = c * bilinDot a y := by
  simp [bilinDot, Finset.mul_sum, mul_assoc]
theorem bilinDot_smul_right (c : ℂ) (a y : Fin 4 → ℂ) : bilinDot a (c • y) = c * bilinDot a y := by
  simp only [bilinDot, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun μ _ => by ring
theorem bilinDot_sub_right (a y z : Fin 4 → ℂ) : bilinDot a (y - z) = bilinDot a y - bilinDot a z := by
  simp [bilinDot, mul_sub, Finset.sum_sub_distrib]
def phaseForm (u v : Fin 4 → ℂ) : MomentumLinearForm where
  toFun := fun z => Complex.I * (bilinDot z.1 u + bilinDot z.2 v)
  map_add' := fun z w => by
    simp only [Prod.fst_add, Prod.snd_add, bilinDot_add_left]
    ring
  map_smul' := fun a z => by
    simp only [Prod.smul_fst, Prod.smul_snd, bilinDot_smul_left, RingHom.id_apply, smul_eq_mul]
    ring
theorem phaseForm_apply (u v κ p : Fin 4 → ℂ) :
    phaseForm u v (κ, p) = Complex.I * (bilinDot κ u + bilinDot p v) := rfl
theorem exists_expSum_of_fintype {P L J : Type} [Fintype J] (ev : L → P → ℂ) (b : J → L)
    (f : J → MomentumLinearForm) :
    ∃ (n : ℕ) (f' : Fin n → MomentumLinearForm) (a : Fin n → L), ∀ (κ p : Fin 4 → ℂ) (e : P),
      ∑ j, ev (b j) e * Complex.exp (f j (κ, p)) =
        expSum (fun j => ev (a j) e) f' κ p := by
  let eqv := Fintype.equivFin J
  refine ⟨Fintype.card J, fun i => f (eqv.symm i), fun i => b (eqv.symm i), fun κ p e => ?_⟩
  simp only [expSum]
  exact (Equiv.sum_comp eqv.symm fun j => ev (b j) e * Complex.exp (f j (κ, p))).symm
theorem applyKernel_eq_finset_sum {J J' : Type} (Y : J' → J → ℂ) (x : J') (S : Finset J)
    (h : ∀ y, y ∉ S → Y x y = 0) (g : J → ℂ) :
    applyKernel Y g x = ∑ y : S, Y x y * g y := by
  simp only [applyKernel]
  rw [tsum_eq_sum (s := S) fun y hy => by rw [h y hy, zero_mul]]
  exact (Finset.sum_coe_sort S fun y => Y x y * g y).symm
open Classical in
theorem linearMapEntry_eq_of_blochWave {I I' : PeriodicData} (A : QuotHom I I') (w : Fin 4 → ℂ)
    (x₀ : I'.Carrier) (c : I.UnitQuot) (X : ℂ) (h : X = blochWave I' w (A (Pi.single c 1)) x₀) :
    linearMapEntry A (I'.mkQuot 1 x₀) c =
      Complex.exp (-(Complex.I * bilinDot w (toComplexVec (I'.pos x₀)))) * X := by
  rw [h]
  simp only [blochWave, linearMapEntry]
  rw [← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]
section Entries
variable {F I I' : PeriodicData} {T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ} {ρ R : ℝ}
open Classical in
theorem linear_entries (hF : IsPeriodic F) (hI : IsPeriodic I)
    (hI' : IsPeriodic I') (hC : CovariantFiniteRange.Claim)
    (H : LocalOpFunTaylor.Claim)
    (hT : IsLocalWith F I I' T ρ R) {P : Type} (ε : P → F.UnitQuot → ℂ) (σ : ℂ)
    (q : (Fin 4 → ℂ) → Fin 4 → ℂ) (hq : ∀ p, q p = σ • p)
    (A : (Fin 4 → ℂ) → P → (Fin 4 → ℂ) → QuotHom I I')
    (hA : ∀ p e κ φ y, applyKernel (coeffOne F I I' T (blochWave F (q p) (ε e)))
      (blochWave I κ φ) y = blochWave I' (κ + q p) (A p e κ φ) y)
    (c' : I'.UnitQuot) (c : I.UnitQuot) :
    ∃ (n : ℕ) (f : Fin n → MomentumLinearForm) (a : Fin n → (F.UnitQuot → ℂ) →ₗ[ℂ] ℂ),
      ∀ (p κ : Fin 4 → ℂ) (e : P),
        linearMapEntry (A p e κ) c' c = expSum (fun j => a j (ε e)) f κ p := by
  obtain ⟨x₀, rfl⟩ : ∃ x₀, I'.mkQuot 1 x₀ = c' := Quot.exists_rep c'
  have hfinI := (hC.1 I hI).1 (I'.pos x₀) R
  have hfinF := (hC.1 F hF).1 (I'.pos x₀) R
  have := hfinF.to_subtype
  cases nonempty_fintype (nearIndices F (I'.pos x₀) R)
  let S := hfinI.toFinset
  let v₀ := toComplexVec (I'.pos x₀)
  let b : S × nearIndices F (I'.pos x₀) R → (F.UnitQuot → ℂ) →ₗ[ℂ] ℂ := fun j =>
    (linearCoeffFamily F I I' T R x₀ j.1 j.2 * (Pi.single c 1 : I.UnitQuot → ℂ) (I.mkQuot 1 j.1)) •
      LinearMap.proj (F.mkQuot 1 j.2)
  let f : S × nearIndices F (I'.pos x₀) R → MomentumLinearForm := fun j =>
    phaseForm (toComplexVec (I.pos j.1) - v₀) (σ • (toComplexVec (F.pos j.2) - v₀))
  obtain ⟨n, f', a, h⟩ :=
    exists_expSum_of_fintype (fun (l : (F.UnitQuot → ℂ) →ₗ[ℂ] ℂ) (e : P) => l (ε e)) b f
  refine ⟨n, f', a, fun p κ e => ?_⟩
  refine Eq.trans ?_ (h κ p e)
  have hvan : ∀ y, y ∉ S →
      coeffOne F I I' T (blochWave F (q p) (ε e)) x₀ y = 0 := by
    intro y hy
    obtain ⟨-, ⟨-, hv⟩, -⟩ := H F I I' hF hI hI' T ρ R hT (blochWave F (q p) (ε e)) 0 x₀ y 0
    exact (hv fun hd => hy (hfinI.mem_toFinset.2 hd)).2.1
  rw [linearMapEntry_eq_of_blochWave (A p e κ) (κ + q p) x₀ c _
    ((applyKernel_eq_finset_sum _ x₀ S hvan _).symm.trans (hA p e κ _ x₀)), Fintype.sum_prod_type,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  obtain ⟨⟨-, -, hfirst, -, -⟩, -⟩ := H F I I' hF hI hI' T ρ R hT 0 0 x₀ y 0
  rw [hfirst (blochWave F (q p) (ε e)), finsum_eq_sum_of_fintype, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have he : phaseForm (toComplexVec (I.pos y) - v₀)
      (σ • (toComplexVec (F.pos k) - v₀)) (κ, p) =
        -(Complex.I * bilinDot (κ + q p) v₀) + Complex.I * bilinDot (q p) (toComplexVec (F.pos k)) +
          Complex.I * bilinDot κ (toComplexVec (I.pos y)) := by
    rw [phaseForm_apply, hq]
    simp only [bilinDot_add_left, bilinDot_sub_right, bilinDot_smul_left, bilinDot_smul_right]
    ring
  simp only [b, f, he, Complex.exp_add, blochWave, LinearMap.smul_apply, LinearMap.proj_apply,
    smul_eq_mul]
  ring
open Classical in
theorem quadratic_entries (hF : IsPeriodic F) (hI : IsPeriodic I)
    (hI' : IsPeriodic I') (hC : CovariantFiniteRange.Claim)
    (H : LocalOpFunTaylor.Claim)
    (hT : IsLocalWith F I I' T ρ R)
    (A : (Fin 4 → ℂ) → (F.UnitQuot → ℂ) → (F.UnitQuot → ℂ) → (Fin 4 → ℂ) → QuotHom I I')
    (hA : ∀ p εPlus εMinus κ φ y, applyKernel
      (coeffTwo F I I' T (blochWave F p εPlus) (blochWave F (-p) εMinus))
      (blochWave I κ φ) y = blochWave I' κ (A p εPlus εMinus κ φ) y)
    (c' : I'.UnitQuot) (c : I.UnitQuot) :
    ∃ (n : ℕ) (f : Fin n → MomentumLinearForm)
      (a : Fin n → (F.UnitQuot → ℂ) →ₗ[ℂ] (F.UnitQuot → ℂ) →ₗ[ℂ] ℂ),
      ∀ (p κ : Fin 4 → ℂ) (εPlus εMinus : F.UnitQuot → ℂ),
        linearMapEntry (A p εPlus εMinus κ) c' c =
          expSum (fun j => a j εPlus εMinus) f κ p := by
  obtain ⟨x₀, rfl⟩ : ∃ x₀, I'.mkQuot 1 x₀ = c' := Quot.exists_rep c'
  have hfinI := (hC.1 I hI).1 (I'.pos x₀) R
  have hfinF := (hC.1 F hF).1 (I'.pos x₀) R
  have := hfinF.to_subtype
  cases nonempty_fintype (nearIndices F (I'.pos x₀) R)
  let S := hfinI.toFinset
  let v₀ := toComplexVec (I'.pos x₀)
  let b : S × nearIndices F (I'.pos x₀) R × nearIndices F (I'.pos x₀) R →
      (F.UnitQuot → ℂ) →ₗ[ℂ] (F.UnitQuot → ℂ) →ₗ[ℂ] ℂ := fun j =>
    (quadraticCoeffFamily F I I' T R x₀ j.1 j.2.1 j.2.2 *
        (Pi.single c 1 : I.UnitQuot → ℂ) (I.mkQuot 1 j.1)) •
      (LinearMap.mul ℂ ℂ).compl₁₂ (LinearMap.proj (F.mkQuot 1 j.2.1))
        (LinearMap.proj (F.mkQuot 1 j.2.2))
  let f : S × nearIndices F (I'.pos x₀) R × nearIndices F (I'.pos x₀) R →
      MomentumLinearForm := fun j =>
    phaseForm (toComplexVec (I.pos j.1) - v₀)
      (toComplexVec (F.pos j.2.1) - toComplexVec (F.pos j.2.2))
  obtain ⟨n, f', a, h⟩ := exists_expSum_of_fintype
    (fun (l : (F.UnitQuot → ℂ) →ₗ[ℂ] (F.UnitQuot → ℂ) →ₗ[ℂ] ℂ)
      (e : (F.UnitQuot → ℂ) × (F.UnitQuot → ℂ)) => l e.1 e.2) b f
  refine ⟨n, f', a, fun p κ εPlus εMinus => ?_⟩
  refine Eq.trans ?_ (h κ p (εPlus, εMinus))
  have hvan : ∀ y, y ∉ S →
      coeffTwo F I I' T (blochWave F p εPlus) (blochWave F (-p) εMinus) x₀ y = 0 := by
    intro y hy
    obtain ⟨-, ⟨-, hv⟩, -⟩ := H F I I' hF hI hI' T ρ R hT (blochWave F p εPlus)
      (blochWave F (-p) εMinus) x₀ y 0
    exact (hv fun hd => hy (hfinI.mem_toFinset.2 hd)).2.2
  rw [linearMapEntry_eq_of_blochWave (A p εPlus εMinus κ) κ x₀ c _
    ((applyKernel_eq_finset_sum _ x₀ S hvan _).symm.trans (hA p εPlus εMinus κ _ x₀)),
    Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  obtain ⟨⟨-, -, -, -, hsecond⟩, -⟩ := H F I I' hF hI hI' T ρ R hT 0 0 x₀ y 0
  rw [hsecond.2 (blochWave F p εPlus) (blochWave F (-p) εMinus), Fintype.sum_prod_type]
  simp only [finsum_eq_sum_of_fintype]
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k' _ => ?_
  have he : phaseForm (toComplexVec (I.pos y) - v₀)
      (toComplexVec (F.pos k) - toComplexVec (F.pos k')) (κ, p) =
        -(Complex.I * bilinDot κ v₀) + Complex.I * bilinDot p (toComplexVec (F.pos k)) +
          Complex.I * bilinDot (-p) (toComplexVec (F.pos k')) +
          Complex.I * bilinDot κ (toComplexVec (I.pos y)) := by
    have hneg : -p = (-1 : ℂ) • p := by simp
    rw [phaseForm_apply, hneg]
    simp only [bilinDot_sub_right, bilinDot_smul_left]
    ring
  simp only [b, f, he, Complex.exp_add, blochWave, LinearMap.smul_apply, LinearMap.proj_apply,
    LinearMap.compl₁₂_apply, LinearMap.mul_apply', smul_eq_mul]
  ring
end Entries
theorem holds (hK : OpFunKernels.Claim)
    (hC : CovariantFiniteRange.Claim)
    (H : LocalOpFunTaylor.Claim) : LocalOpFunTriple.Claim := by
  intro F I I' hF hI hI' T hTl
  obtain ⟨ρ, R, hT⟩ := id hTl
  have hset : ∀ (p : Fin 4 → ℂ) (εPlus εMinus : F.UnitQuot → ℂ),
      ActionTripleUnique F I I' T p εPlus εMinus :=
    fun p εPlus εMinus => ((hK F I I' hF hI hI' T hTl).2 p εPlus εMinus).1
  have hspec : ∀ (p : Fin 4 → ℂ) (εPlus εMinus : F.UnitQuot → ℂ),
      IsActionTriple F I I' T p εPlus εMinus
        (Classical.epsilon (IsActionTriple F I I' T p εPlus εMinus)) :=
    fun p εPlus εMinus => Classical.epsilon_spec (hset p εPlus εMinus).exists
  refine ⟨hset, fun c' c => ?_, fun c' c => ?_, fun c' c => ?_⟩
  · obtain ⟨n, f, a, h⟩ := linear_entries hF hI hI' hC H hT
      (P := (F.UnitQuot → ℂ) × (F.UnitQuot → ℂ)) (fun e => e.1) 1 id (fun p => by simp)
      (fun p e κ => (jetAlong F I I' T p e.1 e.2).f10 κ)
      (fun p e κ φ y => (hspec p e.1 e.2 κ φ y).1) c' c
    exact ⟨n, f, a, fun p κ εPlus εMinus => h p κ (εPlus, εMinus)⟩
  · obtain ⟨n, f, a, h⟩ := linear_entries hF hI hI' hC H hT
      (P := (F.UnitQuot → ℂ) × (F.UnitQuot → ℂ)) (fun e => e.2) (-1) (fun p => -p)
      (fun p => by simp)
      (fun p e κ => (jetAlong F I I' T p e.1 e.2).f01 κ)
      (fun p e κ φ y => by
        have h := (hspec p e.1 e.2 κ φ y).2.1
        rw [sub_eq_add_neg] at h
        exact h) c' c
    exact ⟨n, f, a, fun p κ εPlus εMinus => h p κ (εPlus, εMinus)⟩
  · obtain ⟨n, f, a, h⟩ := quadratic_entries hF hI hI' hC H hT
      (fun p εPlus εMinus κ => (jetAlong F I I' T p εPlus εMinus).f11 κ)
      (fun p εPlus εMinus κ φ y => (hspec p εPlus εMinus κ φ y).2.2) c' c
    exact ⟨n, f, a, h⟩
end YangMills.Construction.PeriodicOperators.LocalOpFunTriple
end
