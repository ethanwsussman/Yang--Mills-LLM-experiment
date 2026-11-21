import YangMills.Construction.Lattice.GaugeCovarianceOfHolonomyProof
import YangMills.Construction.Lattice.NormExpAndGaugeTransport
import YangMills.Construction.Matrices.LinearMapsCompositesAndCoordinatesOfRealAnalyticMapsProof
import Mathlib
open scoped Matrix.Norms.L2Operator
namespace YangMills.Construction.PeriodicLattice
open YangMills.Construction.Matrices
variable {L m : ℕ} {j : ℤ}
private theorem mem_unitary_of_mem_specialUnitary {g : ComplexMatrix2}
    (hg : g ∈ ComplexMatrix2.specialUnitary) : g ∈ unitary ComplexMatrix2 :=
  Matrix.specialUnitaryGroup_le_unitaryGroup hg
private theorem mul_inv_of_mem_specialUnitary {g : ComplexMatrix2}
    (hg : g ∈ ComplexMatrix2.specialUnitary) : g * g⁻¹ = 1 := by apply _root_.YangMills.SharedProofs.p21267 <;> assumption
private theorem inv_mul_of_mem_specialUnitary {g : ComplexMatrix2}
    (hg : g ∈ ComplexMatrix2.specialUnitary) : g⁻¹ * g = 1 := by apply _root_.YangMills.SharedProofs.p1227 <;> assumption
private theorem inv_mem_specialUnitary {g : ComplexMatrix2}
    (hg : g ∈ ComplexMatrix2.specialUnitary) : g⁻¹ ∈ ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.Tower.WilsonAnalyticity.inv_mem_specialUnitary <;> assumption
private theorem det_eq_one_of_mem_specialUnitary {g : ComplexMatrix2}
    (hg : g ∈ ComplexMatrix2.specialUnitary) : g.det = 1 :=
  (Matrix.mem_specialUnitaryGroup_iff.1 hg).2
private theorem operatorNorm_unitary_mul_mul {u v : ComplexMatrix2} (X : ComplexMatrix2)
    (hu : u ∈ unitary ComplexMatrix2) (hv : v ∈ unitary ComplexMatrix2) :
    ComplexMatrix2.operatorNorm (u * X * v) = ComplexMatrix2.operatorNorm X := by
  show ‖u * X * v‖ = ‖X‖
  rw [CStarRing.norm_mul_mem_unitary _ hv, CStarRing.norm_mem_unitary_mul _ hu]
private theorem operatorNorm_conj {g : ComplexMatrix2} (hg : g ∈ ComplexMatrix2.specialUnitary)
    (X : ComplexMatrix2) :
    ComplexMatrix2.operatorNorm (g * X * g⁻¹) = ComplexMatrix2.operatorNorm X :=
  operatorNorm_unitary_mul_mul X (mem_unitary_of_mem_specialUnitary hg)
    (mem_unitary_of_mem_specialUnitary (inv_mem_specialUnitary hg))
private theorem conj_sub_one_eq {g : ComplexMatrix2} (hg : g ∈ ComplexMatrix2.specialUnitary)
    (X : ComplexMatrix2) : g * X * g⁻¹ - 1 = g * (X - 1) * g⁻¹ := by
  rw [mul_sub, sub_mul, mul_one, mul_inv_of_mem_specialUnitary hg]
private theorem operatorNorm_conj_sub_one {g : ComplexMatrix2}
    (hg : g ∈ ComplexMatrix2.specialUnitary) (X : ComplexMatrix2) :
    ComplexMatrix2.operatorNorm (g * X * g⁻¹ - 1) = ComplexMatrix2.operatorNorm (X - 1) := by
  rw [conj_sub_one_eq hg, operatorNorm_conj hg]
private theorem conj_pow_eq {g : ComplexMatrix2} (hg : g ∈ ComplexMatrix2.specialUnitary)
    (Y : ComplexMatrix2) (k : ℕ) : (g * Y * g⁻¹) ^ k = g * Y ^ k * g⁻¹ := by
  induction k with
  | zero => simp [mul_inv_of_mem_specialUnitary hg]
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    calc g * Y ^ k * g⁻¹ * (g * Y * g⁻¹) = g * Y ^ k * (g⁻¹ * g) * Y * g⁻¹ := by
          simp only [mul_assoc]
      _ = g * (Y ^ k * Y) * g⁻¹ := by
          rw [inv_mul_of_mem_specialUnitary hg, mul_one]
          simp only [mul_assoc]
private theorem summable_logSeries_terms {X : ComplexMatrix2}
    (hX : ComplexMatrix2.operatorNorm (X - 1) < 1) :
    Summable fun n : ℕ => ((n + 1 : ℂ)⁻¹) • (1 - X) ^ (n + 1) := by
  have hr : ‖1 - X‖ < 1 := by
    rw [norm_sub_rev]
    exact hX
  refine Summable.of_norm_bounded (g := fun n : ℕ => ‖1 - X‖ ^ (n + 1))
    ((summable_nat_add_iff 1).2 (summable_geometric_of_lt_one (norm_nonneg _) hr)) fun n => ?_
  have hc : ‖((n + 1 : ℂ)⁻¹)‖ ≤ 1 := by
    have h₁ : ‖(n + 1 : ℂ)‖ = (n : ℝ) + 1 := by
      have := Complex.norm_natCast (n + 1)
      push_cast at this
      exact this
    rw [norm_inv, h₁]
    exact inv_le_one_of_one_le₀ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  calc ‖((n + 1 : ℂ)⁻¹) • (1 - X) ^ (n + 1)‖
      ≤ ‖((n + 1 : ℂ)⁻¹)‖ * ‖(1 - X) ^ (n + 1)‖ := norm_smul_le _ _
    _ ≤ 1 * ‖1 - X‖ ^ (n + 1) :=
        mul_le_mul hc (norm_pow_le _ _) (norm_nonneg _) zero_le_one
    _ = ‖1 - X‖ ^ (n + 1) := one_mul _
abbrev _root_.YangMills.DeltaSharedProofs.p501283 := @summable_logSeries_terms
abbrev _root_.YangMills.SharedProofs.p26260 := @summable_logSeries_terms
private theorem logSeries_conj {g : ComplexMatrix2} (hg : g ∈ ComplexMatrix2.specialUnitary)
    {X : ComplexMatrix2} (hX : ComplexMatrix2.operatorNorm (X - 1) < 1) :
    ComplexMatrix2.logSeries (g * X * g⁻¹) = g * ComplexMatrix2.logSeries X * g⁻¹ := by
  have hs := summable_logSeries_terms hX
  have hone : 1 - g * X * g⁻¹ = g * (1 - X) * g⁻¹ := by
    rw [mul_sub, sub_mul, mul_one, mul_inv_of_mem_specialUnitary hg]
  have key : ∀ n : ℕ, ((n + 1 : ℂ)⁻¹) • (1 - g * X * g⁻¹) ^ (n + 1) =
      g * (((n + 1 : ℂ)⁻¹) • (1 - X) ^ (n + 1)) * g⁻¹ := by
    intro n
    rw [hone, conj_pow_eq hg, Matrix.mul_smul, Matrix.smul_mul]
  simp only [ComplexMatrix2.logSeries, key]
  rw [(hs.mul_left g).tsum_mul_right, hs.tsum_mul_left, mul_neg, neg_mul]
private theorem matExp_I_smul_mem_unitaryGroup {A : ComplexMatrix2} (hA : A = A.conjTranspose) :
    ComplexMatrix2.matExp (Complex.I • A) ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  refine Matrix.mem_unitaryGroup_iff.2 ?_
  have hstar : (Complex.I • A).conjTranspose = -(Complex.I • A) := by
    rw [Matrix.conjTranspose_smul, ← hA]
    simp
  have hadj : star (ComplexMatrix2.matExp (Complex.I • A)) =
      ComplexMatrix2.matExp (-(Complex.I • A)) := by
    rw [Matrix.star_eq_conjTranspose, ← hstar]
    exact (Matrix.exp_conjTranspose _).symm
  rw [hadj]
  show NormedSpace.exp (Complex.I • A) * NormedSpace.exp (-(Complex.I • A)) = 1
  rw [Matrix.exp_neg]
  exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp _))
private theorem det_matExp_I_smul_of_fullTrace_eq_zero
    (hdet : ∀ Z : ComplexMatrix2,
      (ComplexMatrix2.matExp Z).det = Complex.exp (ComplexMatrix2.fullTrace Z))
    {A : ComplexMatrix2} (hA : ComplexMatrix2.fullTrace A = 0) :
    (ComplexMatrix2.matExp (Complex.I • A)).det = 1 := by
  have h : ComplexMatrix2.fullTrace (Complex.I • A) = 0 := by
    have hA' : Matrix.trace A = 0 := hA
    show Matrix.trace (Complex.I • A) = 0
    rw [Matrix.trace_smul, hA', smul_zero]
  rw [hdet, h, Complex.exp_zero]
private theorem gaugeTransform_opposite_of_compact {ℬ : Set (Bond L m j)}
    {U : Bond L m j → ComplexMatrix2} {u : Site L m j → ComplexMatrix2}
    (hu : ∀ x ∈ endpointsOf ℬ, u x ∈ compactGaugeGroup)
    (hrev : ∀ b ∈ ℬ, U b.opposite = (U b)⁻¹) :
    ∀ b ∈ ℬ, gaugeTransform u U b.opposite = (gaugeTransform u U b)⁻¹ := by
  intro b hb
  have hh : u b.target ∈ ComplexMatrix2.specialUnitary := hu _ ⟨b, hb, Or.inr rfl⟩
  have hinv : ((u b.target)⁻¹)⁻¹ = u b.target :=
    Matrix.nonsing_inv_nonsing_inv _
      (by rw [det_eq_one_of_mem_specialUnitary hh]; exact isUnit_one)
  show u b.target * U b.opposite * (u b.source)⁻¹ = (u b.source * U b * (u b.target)⁻¹)⁻¹
  rw [hrev b hb]
  simp only [Matrix.mul_inv_rev, hinv, mul_assoc]
private theorem gaugeTransform_mem_complexGaugeGroup {ℬ : Set (Bond L m j)}
    {U : Bond L m j → ComplexMatrix2} {u : Site L m j → ComplexMatrix2}
    (hu : ∀ x ∈ endpointsOf ℬ, u x ∈ compactGaugeGroup)
    (hU : ∀ b ∈ ℬ, U b ∈ complexGaugeGroup) :
    ∀ b ∈ ℬ, gaugeTransform u U b ∈ complexGaugeGroup := by
  intro b hb
  have ht : u b.source ∈ ComplexMatrix2.specialUnitary := hu _ ⟨b, hb, Or.inl rfl⟩
  have hh : u b.target ∈ ComplexMatrix2.specialUnitary := hu _ ⟨b, hb, Or.inr rfl⟩
  have hd : (U b).det = 1 := hU b hb
  show (u b.source * U b * (u b.target)⁻¹).det = 1
  rw [Matrix.det_mul, Matrix.det_mul, hd, det_eq_one_of_mem_specialUnitary ht,
    det_eq_one_of_mem_specialUnitary (inv_mem_specialUnitary hh), one_mul, one_mul]
private theorem gaugeTransform_mem_compactGaugeGroup {ℬ : Set (Bond L m j)}
    {U : Bond L m j → ComplexMatrix2} {u : Site L m j → ComplexMatrix2}
    (hu : ∀ x ∈ endpointsOf ℬ, u x ∈ compactGaugeGroup)
    (hU : ∀ b ∈ ℬ, U b ∈ compactGaugeGroup) :
    ∀ b ∈ ℬ, gaugeTransform u U b ∈ compactGaugeGroup := by
  intro b hb
  have ht : u b.source ∈ ComplexMatrix2.specialUnitary := hu _ ⟨b, hb, Or.inl rfl⟩
  have hh : u b.target ∈ ComplexMatrix2.specialUnitary := hu _ ⟨b, hb, Or.inr rfl⟩
  have hb' : U b ∈ ComplexMatrix2.specialUnitary := hU b hb
  exact ComplexMatrix2.specialUnitary.mul_mem (ComplexMatrix2.specialUnitary.mul_mem ht hb')
    (inv_mem_specialUnitary hh)
private theorem isBondPathFromTo_tail_of_cons {b : Bond L m j} {Γ : List (Bond L m j)}
    {x x' : Site L m j} (h : IsBondPathFromTo (b :: Γ) x x') :
    b.source = x ∧ IsBondPathFromTo Γ b.target x' := by apply _root_.YangMills.SharedProofs.p46261 <;> assumption
private theorem pathHolonomy_gaugeTransform_of_compact {ℬ : Set (Bond L m j)}
    {U : Bond L m j → ComplexMatrix2} {u : Site L m j → ComplexMatrix2}
    (hu : ∀ x ∈ endpointsOf ℬ, u x ∈ compactGaugeGroup) (Γ : List (Bond L m j)) :
    ∀ x x' : Site L m j, x ∈ endpointsOf ℬ → IsBondPathFromTo Γ x x' → (∀ b ∈ Γ, b ∈ ℬ) →
      pathHolonomy (gaugeTransform u U) Γ = u x * pathHolonomy U Γ * (u x')⁻¹ := by
  induction Γ with
  | nil =>
    intro x x' hx hp _
    obtain rfl : x = x' := hp.2.1 rfl
    have hx' : u x ∈ ComplexMatrix2.specialUnitary := hu x hx
    simp [pathHolonomy, mul_inv_of_mem_specialUnitary hx']
  | cons b Γ ih =>
    intro x x' hx hp hΓ
    obtain ⟨rfl, hp'⟩ := isBondPathFromTo_tail_of_cons hp
    have hb : b ∈ ℬ := hΓ b (by simp)
    have hh : u b.target ∈ ComplexMatrix2.specialUnitary := hu _ ⟨b, hb, Or.inr rfl⟩
    have ih' := ih b.target x' ⟨b, hb, Or.inr rfl⟩ hp' fun c hc => hΓ c (by simp [hc])
    have e₁ : pathHolonomy (gaugeTransform u U) (b :: Γ) =
        gaugeTransform u U b * pathHolonomy (gaugeTransform u U) Γ := by simp [pathHolonomy]
    have e₂ : pathHolonomy U (b :: Γ) = U b * pathHolonomy U Γ := by simp [pathHolonomy]
    rw [e₁, e₂, ih']
    show u b.source * U b * (u b.target)⁻¹ * (u b.target * pathHolonomy U Γ * (u x')⁻¹) = _
    calc u b.source * U b * (u b.target)⁻¹ * (u b.target * pathHolonomy U Γ * (u x')⁻¹)
        = u b.source * U b * ((u b.target)⁻¹ * u b.target) * pathHolonomy U Γ * (u x')⁻¹ := by
          simp only [mul_assoc]
      _ = u b.source * (U b * pathHolonomy U Γ) * (u x')⁻¹ := by
          rw [inv_mul_of_mem_specialUnitary hh, mul_one]
          simp only [mul_assoc]
private theorem boundaryBonds_isClosedBondPath (p : Plaquette L m j) :
    IsBondPathFromTo p.boundaryBonds p.origin p.origin := by apply _root_.YangMills.SharedProofs.p81322 <;> assumption
theorem normExpAndGaugeTransport_holds (hexp : ComplexMatrix2.ExpLogEstimates) :
    NormExpAndGaugeTransport := by
  have hdet : ∀ Z : ComplexMatrix2,
      (ComplexMatrix2.matExp Z).det = Complex.exp (ComplexMatrix2.fullTrace Z) :=
    hexp.2.2.2.2.2.1
  refine ⟨⟨fun X Y => norm_mul_le X Y, norm_one,
    fun X u v hu hv => operatorNorm_unitary_mul_mul X hu hv,
    fun g hg X => ⟨operatorNorm_conj_sub_one hg X, operatorNorm_conj hg X⟩⟩,
    ⟨fun A hA => ?_, fun A hA => ?_⟩,
    ?_, fun g hg => ⟨fun Z => ?_, fun X hX => ⟨?_, logSeries_conj hg hX⟩⟩⟩
  · exact det_matExp_I_smul_of_fullTrace_eq_zero hdet hA
  · obtain ⟨h₁, h₂⟩ : A = A.conjTranspose ∧ ComplexMatrix2.fullTrace A = 0 := hA
    exact Matrix.mem_specialUnitaryGroup_iff.2
      ⟨matExp_I_smul_mem_unitaryGroup h₁, det_matExp_I_smul_of_fullTrace_eq_zero hdet h₂⟩
  · intro L _ m K n _ _ _ ℬ U u _ hU hu
    refine ⟨⟨gaugeTransform_mem_complexGaugeGroup hu hU.1, gaugeTransform_opposite_of_compact hu hU.2⟩,
      fun hR => ⟨gaugeTransform_mem_compactGaugeGroup hu hR.1,
        gaugeTransform_opposite_of_compact hu hR.2⟩,
      fun Γ x x' hx hp hΓ => pathHolonomy_gaugeTransform_of_compact hu Γ x x' hx hp hΓ,
      fun p hp => ?_⟩
    exact pathHolonomy_gaugeTransform_of_compact hu p.boundaryBonds p.origin p.origin
      ⟨Bond.forwardFrom p.origin p.firstAxis, hp _ (by simp [Plaquette.boundaryBonds]), Or.inl rfl⟩
      (boundaryBonds_isClosedBondPath p) hp
  · exact Matrix.exp_conj g Z
      ((Matrix.isUnit_iff_isUnit_det _).mpr
        (by rw [det_eq_one_of_mem_specialUnitary hg]; exact isUnit_one))
  · rw [operatorNorm_conj_sub_one hg]
    exact hX
end YangMills.Construction.PeriodicLattice
