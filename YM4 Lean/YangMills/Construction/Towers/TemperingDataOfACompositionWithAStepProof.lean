import YangMills.Construction.PeriodicOperators.SymbolOfAnOperatorWithDecayProof
import YangMills.Construction.Coordinates.HolomorphicIffDifferentiable
import YangMills.Construction.Towers.PlaneWavesUnderTheMapOfOneStep
import YangMills.Construction.Towers.PolarisationOfACompositionWithAStep
import YangMills.Construction.Towers.SymbolOfACompositionNearZeroProof
import YangMills.Construction.Towers.SymbolOfTheTotalNormaliserIsATemperingChoiceProof
import YangMills.Construction.Towers.TemperingDataOfACompositionWithAStep
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.Tower.TemperedComposition
open YangMills.Construction.Tower YangMills.Construction.PeriodicOperators YangMills.Construction.PeriodicOperators.Tempered YangMills.Construction.PeriodicOperators.Tempered.OneStep YangMills.Construction.PeriodicOperators.RiemannSums
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.OneLoopLaw.GaugeColourMomenta (HessianVanishesOffAntipodal)
variable {L : ℕ}
private theorem sides_mono {P Q : ℕ → Prop} (h : EventuallyForSides L P)
    (hpq : ∀ n, 0 < n → P n → Q n) : EventuallyForSides L Q := by
  obtain ⟨s₀, h₀, h⟩ := h
  exact ⟨s₀, h₀, fun s hs hle n hn e => hpq n hn (h s hs hle n hn e)⟩
private theorem sides_and {P Q : ℕ → Prop} (hP : EventuallyForSides L P)
    (hQ : EventuallyForSides L Q) : EventuallyForSides L fun n => P n ∧ Q n := by apply _root_.YangMills.SharedProofs.p21504 <;> assumption
private theorem sides_succ (hL : 2 ≤ L) {P : ℕ → Prop} (h : EventuallyForSides L P) :
    EventuallyForSides L fun n => P (n + 1) := by
  obtain ⟨s₀, h₀, h⟩ := h
  refine ⟨s₀, h₀, fun s _ hle n _ e =>
    h (PeriodicLattice.torusSide L (n + 1)) ⟨n + 1, Nat.succ_pos n, rfl⟩ ?_ (n + 1) (Nat.succ_pos n) rfl⟩
  refine hle.trans ?_
  rw [← e]
  have h1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have h2 : (0 : ℝ) < (L : ℝ) ^ n := by positivity
  simp only [PeriodicLattice.torusSide, pow_succ]
  nlinarith
section HessianSums
variable {n : ℕ} {F : FieldFamily L}
private theorem hessian_zero_left (hf : OneLoopLaw.ComplexHessianOfMember.Properties F n)
    {B : UnitEdge L n → Matrices.ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n 0 0) : complexHessian F n 0 B = 0 := by apply _root_.YangMills.SharedProofs.p5135 <;> assumption
private theorem hessian_smul_left (hf : OneLoopLaw.ComplexHessianOfMember.Properties F n) (c : ℂ)
    {B B' : UnitEdge L n → Matrices.ComplexMatrix2} (hB : B ∈ complexEdgeForms L n 0 0)
    (hB' : B' ∈ complexEdgeForms L n 0 0) :
    complexHessian F n (c • B) B' = c * complexHessian F n B B' := by
  have h := hf.linear_left c B hB 0 (zero_mem _) B' hB'
  rwa [add_zero, hessian_zero_left hf hB', add_zero] at h
private theorem hessian_sum_left {ι : Type*} (hf : OneLoopLaw.ComplexHessianOfMember.Properties F n)
    (s : Finset ι)
    {W : ι → UnitEdge L n → Matrices.ComplexMatrix2} (hW : ∀ j ∈ s, W j ∈ complexEdgeForms L n 0 0)
    {B' : UnitEdge L n → Matrices.ComplexMatrix2} (hB' : B' ∈ complexEdgeForms L n 0 0) :
    complexHessian F n (∑ j ∈ s, W j) B' = ∑ j ∈ s, complexHessian F n (W j) B' := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hessian_zero_left hf hB'
  | insert j s hj ih =>
    have hj' := hW j (Finset.mem_insert_self j s)
    have hs : ∀ l ∈ s, W l ∈ complexEdgeForms L n 0 0 :=
      fun l hl => hW l (Finset.mem_insert_of_mem hl)
    have h := hf.linear_left 1 (W j) hj' (∑ l ∈ s, W l) (Submodule.sum_mem _ hs) B' hB'
    rw [one_smul, one_mul] at h
    rw [Finset.sum_insert hj, Finset.sum_insert hj, h, ih hs]
private theorem hessian_combination_left {ι κ : Type*} [Fintype κ]
    (hf : OneLoopLaw.ComplexHessianOfMember.Properties F n)
    (s : Finset ι) (u : ℂ) (c : ι → κ → ℂ) {W : ι → κ → UnitEdge L n → Matrices.ComplexMatrix2}
    (hW : ∀ j ∈ s, ∀ ρ, W j ρ ∈ complexEdgeForms L n 0 0)
    {B' : UnitEdge L n → Matrices.ComplexMatrix2}
    (hB' : B' ∈ complexEdgeForms L n 0 0) :
    complexHessian F n (u • ∑ j ∈ s, ∑ ρ, c j ρ • W j ρ) B' =
      u * ∑ j ∈ s, ∑ ρ, c j ρ * complexHessian F n (W j ρ) B' := by
  have h1 : ∀ j ∈ s, ∀ ρ ∈ (Finset.univ : Finset κ), c j ρ • W j ρ ∈ complexEdgeForms L n 0 0 :=
    fun j hj ρ _ => Submodule.smul_mem _ _ (hW j hj ρ)
  have h2 : ∀ j ∈ s, ∑ ρ, c j ρ • W j ρ ∈ complexEdgeForms L n 0 0 :=
    fun j hj => Submodule.sum_mem _ (h1 j hj)
  rw [hessian_smul_left hf u (Submodule.sum_mem _ h2) hB', hessian_sum_left hf s h2 hB']
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [hessian_sum_left hf _ (h1 j hj) hB']
  exact Finset.sum_congr rfl fun ρ _ => hessian_smul_left hf _ (hW j hj ρ) hB'
private theorem hessian_combination_right {ι κ : Type*} [Fintype κ]
    (hf : OneLoopLaw.ComplexHessianOfMember.Properties F n)
    (s : Finset ι) (u : ℂ) (c : ι → κ → ℂ) {W : ι → κ → UnitEdge L n → Matrices.ComplexMatrix2}
    (hW : ∀ j ∈ s, ∀ ρ, W j ρ ∈ complexEdgeForms L n 0 0)
    {B : UnitEdge L n → Matrices.ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n 0 0) :
    complexHessian F n B (u • ∑ j ∈ s, ∑ ρ, c j ρ • W j ρ) =
      u * ∑ j ∈ s, ∑ ρ, c j ρ * complexHessian F n B (W j ρ) := by
  have h : u • ∑ j ∈ s, ∑ ρ, c j ρ • W j ρ ∈ complexEdgeForms L n 0 0 :=
    Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j hj =>
      Submodule.sum_mem _ fun ρ _ => Submodule.smul_mem _ _ (hW j hj ρ))
  exact (hf.symm B hB _ h).trans ((hessian_combination_left hf s u c hW hB).trans
    (congrArg (u * ·) (Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun ρ _ =>
      congrArg (c j ρ * ·) (hf.symm _ (hW j hj ρ) B hB))))
end HessianSums
private def negResidue (L : ℕ) (m : Fin 4 → ℤ) : Fin 4 → ℤ := fun ν => (-m ν) % (L : ℤ)
private theorem negResidue_mem (hL : 0 < L) (m : Fin 4 → ℤ) : negResidue L m ∈ residueBox L := by
  have h : (0 : ℤ) < L := by exact_mod_cast hL
  simp only [residueBox, Fintype.mem_piFinset, Finset.mem_Ico]
  exact fun ν => ⟨Int.emod_nonneg _ h.ne', Int.emod_lt_of_pos _ h⟩
private theorem dvd_negResidue_add (m : Fin 4 → ℤ) (ν : Fin 4) :
    (L : ℤ) ∣ negResidue L m ν + m ν :=
  ⟨-(-m ν / (L : ℤ)), by rw [negResidue, Int.emod_def]; ring⟩
private theorem eq_negResidue {m m' : Fin 4 → ℤ} (hm' : m' ∈ residueBox L)
    (h : ∀ ν, (L : ℤ) ∣ m' ν + m ν) : m' = negResidue L m := by
  funext ν
  have hb := Finset.mem_Ico.1 (Fintype.mem_piFinset.1 hm' ν)
  have hc : -m ν ≡ m' ν [ZMOD (L : ℤ)] :=
    Int.modEq_iff_dvd.2 (by simpa [sub_neg_eq_add] using h ν)
  have hd : m' ν % (L : ℤ) = m' ν := Int.emod_eq_of_lt hb.1 hb.2
  rw [negResidue, hc.eq, hd]
private theorem rescaledMomentum_mem (hL : 0 < L) {n : ℕ} {p : AmbientSpace}
    (hp : p ∈ dualLattice (2 * L ^ n)) (m' : Fin 4 → ℤ) :
    rescaledMomentum L p m' ∈ dualLattice (2 * L ^ (n + 1)) := by
  obtain ⟨k, hk⟩ := hp
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  refine ⟨fun μ => k μ + 2 * (L : ℤ) ^ n * m' μ, fun μ => ?_⟩
  simp only [rescaledMomentum, hk μ]
  push_cast
  field_simp
  ring
private theorem rescaledMomentum_add_not_mem (hL : 0 < L) (p : AmbientSpace) {m' m'' : Fin 4 → ℤ}
    (hm'' : m'' ∈ residueBox L) (hne : m'' ≠ negResidue L m') :
    rescaledMomentum L p m' + rescaledMomentum L (-p) m'' ∉ periodLattice := by
  rintro ⟨z, hz⟩
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  refine hne (eq_negResidue hm'' fun ν => ⟨z ν, ?_⟩)
  have h := hz ν
  simp only [Pi.add_apply, rescaledMomentum, Pi.neg_apply] at h
  have h2 : (2 * Real.pi) * ((m'' ν : ℝ) + m' ν) = (2 * Real.pi) * ((L : ℝ) * z ν) := by
    field_simp at h
    linarith
  have h3 : (m'' ν : ℝ) + m' ν = (L : ℝ) * z ν :=
    mul_left_cancel₀ (by positivity) h2
  exact_mod_cast h3
private theorem rescaledMomentum_negResidue (hL : 0 < L) (p : AmbientSpace) (m' : Fin 4 → ℤ) :
    ∃ e : Fin 4 → ℤ, rescaledMomentum L (-p) (negResidue L m') =
      -rescaledMomentum L p m' + (2 * Real.pi) • castVec e := by
  choose e he using fun ν => dvd_negResidue_add (L := L) m' ν
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  refine ⟨e, funext fun ν => ?_⟩
  have h : (negResidue L m' ν : ℝ) + m' ν = (L : ℝ) * e ν := by exact_mod_cast he ν
  simp only [rescaledMomentum, Pi.neg_apply, Pi.add_apply, Pi.smul_apply, castVec, smul_eq_mul]
  field_simp
  linear_combination (2 * Real.pi) * h
private theorem rescaledFreq_toComplexVec (p : AmbientSpace) (m' : Fin 4 → ℤ) :
    rescaledFreq L (toComplexVec p) m' = toComplexVec (rescaledMomentum L p m') := by apply _root_.YangMills.Construction.CompositeSymbolNearZero.rescaledFreq_toComplexVec <;> assumption
private theorem toComplexVec_neg (p : AmbientSpace) : toComplexVec (-p) = -toComplexVec p := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.SymbolExpansion.toComplexVec_neg_eq <;> assumption
section FourierModes
variable {n i : ℕ} {F : FieldFamily L}
private theorem compStep_hessian_fourierModes (hL : 0 < L)
    (hw : OneLoopLaw.PlaneWaveSymmetries.PlaneWaveLaws L n)
    (hw' : OneLoopLaw.PlaneWaveSymmetries.PlaneWaveLaws L (n + 1))
    (hf : OneLoopLaw.ComplexHessianOfMember.Properties F (n + 1))
    (hcong : ∀ m m' : Fin 4 → ℤ, StepEntryBounds.CongruentMod L m m' → ∀ κ ρ μ,
      stepEntry L i m κ ρ μ = stepEntry L i m' κ ρ μ)
    (hpol : ∀ B ∈ complexEdgeForms L n 0 0, ∀ B' ∈ complexEdgeForms L n 0 0,
      complexHessian (compStep hL i F) n B B' =
        complexHessian F (n + 1) (complexStepPushforward hL n i B) (complexStepPushforward hL n i B'))
    (hpw : ∀ p ∈ dualLattice (2 * L ^ n), ∀ (a : Fin 3) (μ : Fin 4),
      complexStepPushforward hL n i (fourierModeForm L n a p μ) =
        (L : ℂ)⁻¹ • ∑ m' ∈ residueBox L, ∑ ρ,
          stepEntry L i m' (toComplexVec p) ρ μ • fourierModeForm L (n + 1) a (rescaledMomentum L p m') ρ)
    (hoff : HessianVanishesOffAntipodal F (n + 1))
    {p : AmbientSpace} (hp : p ∈ dualLattice (2 * L ^ n)) (a a' : Fin 3) (μ ν : Fin 4) :
    complexHessian (compStep hL i F) n (fourierModeForm L n a p μ) (fourierModeForm L n a' (-p) ν) =
      (L : ℂ)⁻¹ * (L : ℂ)⁻¹ * ∑ m' ∈ residueBox L, ∑ ρ, ∑ σ,
        stepEntry L i m' (toComplexVec p) ρ μ * stepEntry L i (-m') (-toComplexVec p) σ ν *
          complexHessian F (n + 1) (fourierModeForm L (n + 1) a (rescaledMomentum L p m') ρ)
            (fourierModeForm L (n + 1) a' (-rescaledMomentum L p m') σ) := by
  have hnp : -p ∈ dualLattice (2 * L ^ n) := neg_mem hp
  have hq : ∀ m', rescaledMomentum L p m' ∈ dualLattice (2 * L ^ (n + 1)) :=
    rescaledMomentum_mem hL hp
  have hq' : ∀ m', rescaledMomentum L (-p) m' ∈ dualLattice (2 * L ^ (n + 1)) :=
    rescaledMomentum_mem hL hnp
  have hW : ∀ m' ρ,
      fourierModeForm L (n + 1) a (rescaledMomentum L p m') ρ ∈ complexEdgeForms L (n + 1) 0 0 :=
    fun m' ρ => hw'.mem_complex a ρ _ (hq m')
  have hW' : ∀ m' σ,
      fourierModeForm L (n + 1) a' (rescaledMomentum L (-p) m') σ ∈ complexEdgeForms L (n + 1) 0 0 :=
    fun m' σ => hw'.mem_complex a' σ _ (hq' m')
  have hR : (L : ℂ)⁻¹ • ∑ m'' ∈ residueBox L, ∑ σ, stepEntry L i m'' (toComplexVec (-p)) σ ν •
      fourierModeForm L (n + 1) a' (rescaledMomentum L (-p) m'') σ ∈ complexEdgeForms L (n + 1) 0 0 :=
    Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ =>
      Submodule.sum_mem _ fun σ _ => Submodule.smul_mem _ _ (hW' j σ))
  have key : ∀ m' ∈ residueBox L, ∀ ρ,
      complexHessian F (n + 1) (fourierModeForm L (n + 1) a (rescaledMomentum L p m') ρ)
        ((L : ℂ)⁻¹ • ∑ m'' ∈ residueBox L, ∑ σ, stepEntry L i m'' (toComplexVec (-p)) σ ν •
          fourierModeForm L (n + 1) a' (rescaledMomentum L (-p) m'') σ) =
      (L : ℂ)⁻¹ * ∑ σ, stepEntry L i (-m') (-toComplexVec p) σ ν *
        complexHessian F (n + 1) (fourierModeForm L (n + 1) a (rescaledMomentum L p m') ρ)
          (fourierModeForm L (n + 1) a' (-rescaledMomentum L p m') σ) := by
    intro m' _ ρ
    rw [hessian_combination_right hf _ _
      (fun m'' σ => stepEntry L i m'' (toComplexVec (-p)) σ ν)
      (W := fun m'' σ => fourierModeForm L (n + 1) a' (rescaledMomentum L (-p) m'') σ)
      (fun j _ σ => hW' j σ) (hW m' ρ)]
    congr 1
    rw [Finset.sum_eq_single (negResidue L m')]
    · obtain ⟨e, he⟩ := rescaledMomentum_negResidue hL p m'
      refine Finset.sum_congr rfl fun σ _ => ?_
      have hc : StepEntryBounds.CongruentMod L (negResidue L m') (-m') := fun ν' => by
        simpa [sub_neg_eq_add] using dvd_negResidue_add (L := L) m' ν'
      rw [hcong _ _ hc, toComplexVec_neg, he,
        hw'.periodic a' σ _ (neg_mem (hq m')) e]
    · intro m'' hm'' hne
      refine Finset.sum_eq_zero fun σ _ => ?_
      rw [hoff a a' ρ σ _ (hq m') _ (hq' m'') (rescaledMomentum_add_not_mem hL p hm'' hne), mul_zero]
    · exact fun h => absurd (negResidue_mem hL m') h
  rw [hpol _ (hw.mem_complex a μ p hp) _ (hw.mem_complex a' ν (-p) hnp), hpw p hp,
    hpw (-p) hnp, hessian_combination_left hf _ _
      (fun m' ρ => stepEntry L i m' (toComplexVec p) ρ μ)
      (W := fun m' ρ => fourierModeForm L (n + 1) a (rescaledMomentum L p m') ρ)
      (fun j _ ρ => hW j ρ) hR, mul_assoc]
  congr 1
  have h2 : ∀ m' ∈ residueBox L, ∀ ρ ∈ (Finset.univ : Finset (Fin 4)),
      stepEntry L i m' (toComplexVec p) ρ μ *
        complexHessian F (n + 1) (fourierModeForm L (n + 1) a (rescaledMomentum L p m') ρ)
        ((L : ℂ)⁻¹ • ∑ m'' ∈ residueBox L, ∑ σ, stepEntry L i m'' (toComplexVec (-p)) σ ν •
          fourierModeForm L (n + 1) a' (rescaledMomentum L (-p) m'') σ) =
      (L : ℂ)⁻¹ * ∑ σ, stepEntry L i m' (toComplexVec p) ρ μ *
        stepEntry L i (-m') (-toComplexVec p) σ ν *
        complexHessian F (n + 1) (fourierModeForm L (n + 1) a (rescaledMomentum L p m') ρ)
          (fourierModeForm L (n + 1) a' (-rescaledMomentum L p m') σ) := by
    intro m' hm' ρ _
    rw [key m' hm' ρ, mul_left_comm, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun σ _ => by ring
  rw [Finset.sum_congr rfl fun m' hm' => Finset.sum_congr rfl (h2 m' hm')]
  simp only [← Finset.mul_sum]
end FourierModes
private theorem norm_triple_sum_sub_le (R : Finset (Fin 4 → ℤ)) (A B : (Fin 4 → ℤ) → Fin 4 → ℂ)
    (x y : (Fin 4 → ℤ) → Fin 4 → Fin 4 → ℂ) (c : ℂ) (K E : ℝ) (hK : 0 ≤ K)
    (hA : ∀ m ρ, ‖A m ρ‖ ≤ K) (hB : ∀ m σ, ‖B m σ‖ ≤ K)
    (hxy : ∀ m ∈ R, ∀ ρ σ, ‖x m ρ σ - y m ρ σ‖ ≤ E) :
    ‖c * ∑ m ∈ R, ∑ ρ, ∑ σ, A m ρ * B m σ * x m ρ σ -
        c * ∑ m ∈ R, ∑ ρ, ∑ σ, A m ρ * y m ρ σ * B m σ‖ ≤
      ‖c‖ * R.card * 16 * K ^ 2 * E := by
  have h1 : ∑ m ∈ R, ∑ ρ, ∑ σ, A m ρ * B m σ * x m ρ σ -
      ∑ m ∈ R, ∑ ρ, ∑ σ, A m ρ * y m ρ σ * B m σ =
      ∑ m ∈ R, ∑ ρ, ∑ σ, A m ρ * B m σ * (x m ρ σ - y m ρ σ) := by
    simp only [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun ρ _ =>
      Finset.sum_congr rfl fun σ _ => by ring
  have h2 : ∀ m ∈ R, ∀ ρ σ, ‖A m ρ * B m σ * (x m ρ σ - y m ρ σ)‖ ≤ K * K * E := by
    intro m hm ρ σ
    rw [norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul (hA m ρ) (hB m σ) (norm_nonneg _) hK) (hxy m hm ρ σ)
      (norm_nonneg _) (mul_nonneg hK hK)
  have h3 : ‖∑ m ∈ R, ∑ ρ, ∑ σ, A m ρ * B m σ * (x m ρ σ - y m ρ σ)‖ ≤
      ∑ m ∈ R, ∑ _ρ : Fin 4, ∑ _σ : Fin 4, K * K * E :=
    norm_sum_le_of_le _ fun m hm => norm_sum_le_of_le _ fun ρ _ =>
      norm_sum_le_of_le _ fun σ _ => h2 m hm ρ σ
  rw [← mul_sub, h1, norm_mul]
  calc ‖c‖ * _ ≤ ‖c‖ * ∑ m ∈ R, ∑ _ρ : Fin 4, ∑ _σ : Fin 4, K * K * E :=
        mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    _ = ‖c‖ * R.card * 16 * K ^ 2 * E := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
private theorem compStep_hessian_bound {n i : ℕ} {F : FieldFamily L} {π : SymbolArray} {E K : ℝ}
    (hL : 0 < L)
    (hK : 0 ≤ K) (hH : ∀ (m' : Fin 4 → ℤ) (κ : Fin 4 → ℂ) (ρ μ : Fin 4),
      κ ∈ imStrip 0 → ‖stepEntry L i m' κ ρ μ‖ ≤ K) {p : AmbientSpace} {a a' : Fin 3} {μ ν : Fin 4}
    (hbound : ∀ m' : Fin 4 → ℤ, ∀ ρ σ,
      ‖(((PeriodicLattice.torusSide L (n + 1))⁻¹ ^ 4 : ℝ) : ℂ) *
          complexHessian F (n + 1) (fourierModeForm L (n + 1) a (rescaledMomentum L p m') ρ)
            (fourierModeForm L (n + 1) a' (-rescaledMomentum L p m') σ) -
        (if a = a' then π ρ σ (toComplexVec (rescaledMomentum L p m')) else 0)‖ ≤ E)
    (X : ℂ) (hX : X = (L : ℂ)⁻¹ * (L : ℂ)⁻¹ * ∑ m' ∈ residueBox L, ∑ ρ, ∑ σ,
        stepEntry L i m' (toComplexVec p) ρ μ * stepEntry L i (-m') (-toComplexVec p) σ ν *
          complexHessian F (n + 1) (fourierModeForm L (n + 1) a (rescaledMomentum L p m') ρ)
            (fourierModeForm L (n + 1) a' (-rescaledMomentum L p m') σ)) :
    ‖(((PeriodicLattice.torusSide L n)⁻¹ ^ 4 : ℝ) : ℂ) * X -
        (if a = a' then stepSymbolArray L i π μ ν (toComplexVec p) else 0)‖ ≤
      (L : ℝ) ^ 2 * (residueBox L).card * 16 * K ^ 2 * E := by
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hside : PeriodicLattice.torusSide L (n + 1) = (L : ℝ) * PeriodicLattice.torusSide L n := by
    simp only [PeriodicLattice.torusSide, pow_succ]
    ring
  have hs0 : PeriodicLattice.torusSide L n ≠ 0 := by
    have : (0 : ℝ) < (L : ℝ) ^ n := by
      have : (0 : ℝ) < L := by exact_mod_cast hL
      positivity
    simp only [PeriodicLattice.torusSide]
    positivity
  have hs : (((PeriodicLattice.torusSide L n)⁻¹ ^ 4 : ℝ) : ℂ) * ((L : ℂ)⁻¹ * (L : ℂ)⁻¹) =
      (L : ℂ) ^ 2 * (((PeriodicLattice.torusSide L (n + 1))⁻¹ ^ 4 : ℝ) : ℂ) := by
    have hsc : ((PeriodicLattice.torusSide L n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs0
    rw [hside]
    push_cast
    field_simp
  have hl : (((PeriodicLattice.torusSide L n)⁻¹ ^ 4 : ℝ) : ℂ) * X = (L : ℂ) ^ 2 *
      ∑ m' ∈ residueBox L, ∑ ρ, ∑ σ,
        stepEntry L i m' (toComplexVec p) ρ μ * stepEntry L i (-m') (-toComplexVec p) σ ν *
          ((((PeriodicLattice.torusSide L (n + 1))⁻¹ ^ 4 : ℝ) : ℂ) *
            complexHessian F (n + 1) (fourierModeForm L (n + 1) a (rescaledMomentum L p m') ρ)
              (fourierModeForm L (n + 1) a' (-rescaledMomentum L p m') σ)) := by
    rw [hX, ← mul_assoc, hs, mul_assoc]
    congr 1
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun ρ _ =>
      Finset.sum_congr rfl fun σ _ => by ring
  have hr : (if a = a' then stepSymbolArray L i π μ ν (toComplexVec p) else 0) = (L : ℂ) ^ 2 *
      ∑ m' ∈ residueBox L, ∑ ρ, ∑ σ, stepEntry L i m' (toComplexVec p) ρ μ *
        (if a = a' then π ρ σ (toComplexVec (rescaledMomentum L p m')) else 0) *
        stepEntry L i (-m') (-toComplexVec p) σ ν := by
    split_ifs with h
    · simp only [stepSymbolArray, rescaledFreq_toComplexVec]
    · simp
  have hsp : toComplexVec p ∈ imStrip 0 := fun ρ => by simp [toComplexVec]
  have hsn : -toComplexVec p ∈ imStrip 0 := fun ρ => by simp [toComplexVec]
  rw [hl, hr]
  have hb := norm_triple_sum_sub_le (residueBox L)
    (fun m ρ => stepEntry L i m (toComplexVec p) ρ μ)
    (fun m σ => stepEntry L i (-m) (-toComplexVec p) σ ν)
    (fun m ρ σ => (((PeriodicLattice.torusSide L (n + 1))⁻¹ ^ 4 : ℝ) : ℂ) *
      complexHessian F (n + 1) (fourierModeForm L (n + 1) a (rescaledMomentum L p m) ρ)
        (fourierModeForm L (n + 1) a' (-rescaledMomentum L p m) σ))
    (fun m ρ σ => if a = a' then π ρ σ (toComplexVec (rescaledMomentum L p m)) else 0)
    ((L : ℂ) ^ 2) K E hK (fun m ρ => hH m _ ρ μ hsp) (fun m σ => hH (-m) _ σ ν hsn)
    (fun m _ ρ σ => hbound m ρ σ)
  simpa using hb
private theorem halfSupRate_pos {δ₀ : ℝ} (h : δ₀ ∈ FreeStrip.halfSupRate) : 0 < δ₀ := by apply _root_.YangMills.Construction.Tower.NormaliserSymbol.pos_of_mem_halfSupRate <;> assumption
private def openImStrip (ς : ℝ) : Set (Fin 4 → ℂ) := {κ | ∀ μ, |(κ μ).im| < ς}
private theorem isOpen_openImStrip (ς : ℝ) : IsOpen (openImStrip ς) := by apply _root_.YangMills.Construction.PeriodicOperators.ExpDecaySymbol.isOpen_openImStrip <;> assumption
private theorem rescaledFreq_mem_imStrip (hL : 0 < L) {δ ς : ℝ} (hς : ς ≤ δ) {κ : Fin 4 → ℂ}
    (hκ : κ ∈ openImStrip ς) (m' : Fin 4 → ℤ) : rescaledFreq L κ m' ∈ imStrip δ := by
  intro ρ
  have h1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have h0 : (0 : ℝ) < L := by linarith
  have him : (rescaledFreq L κ m' ρ).im = (κ ρ).im / L := by
    have hc : ((L : ℂ)) = ((L : ℝ) : ℂ) := by simp
    simp only [rescaledFreq, PlaneWaves.shiftedFreq]
    rw [hc, Complex.div_ofReal_im]
    simp
  rw [him, abs_div, abs_of_pos h0]
  have h2 := (hκ ρ).le
  have h3 : |(κ ρ).im| / L ≤ |(κ ρ).im| := div_le_self (abs_nonneg _) h1
  linarith
private theorem differentiable_rescaledFreq (m' : Fin 4 → ℤ) :
    Differentiable ℂ fun κ : Fin 4 → ℂ => rescaledFreq L κ m' := by
  refine differentiable_pi.2 fun ρ => ?_
  simp only [rescaledFreq, PlaneWaves.shiftedFreq, div_eq_mul_inv]
  exact ((differentiable_apply ρ).add_const _).mul_const _
private theorem stepSymbolArray_differentiableOn (hL : 0 < L) {i : ℕ} {π : SymbolArray} {ς δ : ℝ}
    (hς : ς ≤ δ) {O : Set (Fin 4 → ℂ)} (hO : imStrip δ ⊆ O)
    (hπ : ∀ ρ σ, DifferentiableOn ℂ (π ρ σ) O) {O₁ : Set (Fin 4 → ℂ)} (hO₁ : openImStrip ς ⊆ O₁)
    (hH : ∀ m' ρ μ, DifferentiableOn ℂ (fun κ => stepEntry L i m' κ ρ μ) O₁) (μ ν : Fin 4) :
    DifferentiableOn ℂ (stepSymbolArray L i π μ ν) (openImStrip ς) := by
  have hneg : MapsTo (fun κ : Fin 4 → ℂ => -κ) (openImStrip ς) O₁ := fun κ hκ => hO₁ fun ρ => by
    simpa using hκ ρ
  have hdn : DifferentiableOn ℂ (fun κ : Fin 4 → ℂ => -κ) (openImStrip ς) :=
    Differentiable.differentiableOn (by fun_prop)
  have hterm : ∀ (m' : Fin 4 → ℤ) (ρ σ : Fin 4), DifferentiableOn ℂ (fun κ =>
      stepEntry L i m' κ ρ μ * π ρ σ (rescaledFreq L κ m') * stepEntry L i (-m') (-κ) σ ν)
      (openImStrip ς) := fun m' ρ σ =>
    (((hH m' ρ μ).mono hO₁).mul ((hπ ρ σ).comp (differentiable_rescaledFreq m').differentiableOn
      fun κ hκ => hO (rescaledFreq_mem_imStrip hL hς hκ m'))).mul ((hH (-m') σ ν).comp hdn hneg)
  exact (DifferentiableOn.fun_sum fun m' _ => DifferentiableOn.fun_sum fun ρ _ =>
    DifferentiableOn.fun_sum fun σ _ => hterm m' ρ σ).const_mul _
private theorem stepSymbolArray_bounded (hL : 0 < L) {i : ℕ} {π : SymbolArray} {ς δ K : ℝ}
    (hς : ς ≤ δ) {O : Set (Fin 4 → ℂ)} (hO : imStrip δ ⊆ O) (hK : 0 ≤ K)
    (hπ : ∀ ρ σ, ∃ C : ℝ, ∀ κ ∈ O, ‖π ρ σ κ‖ ≤ C)
    (hH : ∀ (m' : Fin 4 → ℤ) (ρ μ : Fin 4), ∀ κ ∈ openImStrip ς, ‖stepEntry L i m' κ ρ μ‖ ≤ K)
    (μ ν : Fin 4) : ∃ C : ℝ, ∀ κ ∈ openImStrip ς, ‖stepSymbolArray L i π μ ν κ‖ ≤ C := by
  choose C hC using hπ
  refine ⟨‖(L : ℂ) ^ 2‖ * ∑ _m' ∈ residueBox L, ∑ ρ, ∑ σ, K * |C ρ σ| * K, fun κ hκ => ?_⟩
  have hneg : -κ ∈ openImStrip ς := fun ρ => by simpa using hκ ρ
  have hterm : ∀ (m' : Fin 4 → ℤ) (ρ σ : Fin 4),
      ‖stepEntry L i m' κ ρ μ * π ρ σ (rescaledFreq L κ m') * stepEntry L i (-m') (-κ) σ ν‖ ≤
        K * |C ρ σ| * K := by
    intro m' ρ σ
    rw [norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul (hH m' ρ μ κ hκ)
      ((hC ρ σ _ (hO (rescaledFreq_mem_imStrip hL hς hκ m'))).trans (le_abs_self _))
      (norm_nonneg _) hK)
      (hH _ σ ν _ hneg) (norm_nonneg _) (mul_nonneg hK (abs_nonneg _))
  simp only [stepSymbolArray]
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_sum_le_of_le _ fun m' _ => norm_sum_le_of_le _ fun ρ _ =>
    norm_sum_le_of_le _ fun σ _ => hterm m' ρ σ) (norm_nonneg _)
theorem compStepTemperedWitnessExists_holds (h₁ : HessianOfStepComposite.Claim)
    (h₂ : StepImageOfFourierModes.ImageExpansion)
    (h₃ : StepEntryBounds.Claim)
    (h₄ : OneLoopLaw.GaugeColourMomenta.GaugeColourMomentumClaim)
    (h₅ : ResponseOperators.Claim) (h₆ : OneLoopLaw.ComplexHessianOfMember.Statement)
    (h₇ : OneLoopLaw.PlaneWaveSymmetries.PlaneWaveLawsHold)
    (h₈ : Coordinates.ComplexCoordinates.HolomorphicDifferentiable.HolomorphicIffDifferentiableStatement) :
    CompStepTemperedWitnessExists := by
  intro L hL hs F δ π e i hF hc
  have hL2 : 2 ≤ L := by
    have := hs.2
    omega
  obtain ⟨δ₀, hδ₀, -⟩ := h₅
  have hδ₀pos : 0 < δ₀ := halfSupRate_pos hδ₀
  have hH := h₃ δ₀ hδ₀ L hs i
  obtain ⟨K, hKb⟩ := hH.bounded
  have hK : 0 ≤ K := (norm_nonneg _).trans (hKb 0 0 0 0 fun μ => by
    simpa using hδ₀pos.le)
  have hmin : 0 < min δ (2 * δ₀) := lt_min hc.delta_pos (by linarith)
  have hsub : openImStrip (min δ (2 * δ₀)) ⊆ imStrip (2 * δ₀) := fun κ hκ μ =>
    ((hκ μ).trans_le (min_le_right _ _)).le
  obtain ⟨O₁, hO₁o, hO₁, hHol⟩ := hH.holomorphic
  obtain ⟨O, hO, hol⟩ := hc.analytic
  have hOo : IsOpen O := (hol 0 0).1.1
  have hπd : ∀ ρ σ, DifferentiableOn ℂ (π ρ σ) O := fun ρ σ =>
    differentiableOn_pi.1 ((h₈ 4 1 O _ hOo).1 (hol ρ σ).1) 0
  have hHd : ∀ m' ρ μ, DifferentiableOn ℂ (fun κ => stepEntry L i m' κ ρ μ) O₁ := fun m' ρ μ =>
    differentiableOn_pi.1 ((h₈ 4 1 O₁ _ hO₁o).1 (hHol m' ρ μ)) 0
  refine ⟨min δ (2 * δ₀) / 2, (L : ℝ) ^ 2 * (residueBox L).card * 16 * K ^ 2, ⟨half_pos hmin,
    ⟨openImStrip (min δ (2 * δ₀)), fun κ hκ μ => (hκ μ).trans_lt (by linarith), fun μ ν =>
      ⟨(h₈ 4 1 _ _ (isOpen_openImStrip _)).2 (differentiableOn_pi.2 fun _ =>
        stepSymbolArray_differentiableOn hL (min_le_left _ _) hO hπd (hsub.trans hO₁) hHd μ ν),
        stepSymbolArray_bounded hL (min_le_left _ _) hO hK (fun ρ σ => (hol ρ σ).2)
          (fun m' ρ μ κ hκ => hKb m' ρ μ κ (hsub hκ)) μ ν⟩⟩, ?_, ?_, ?_⟩⟩
  · exact sides_mono (sides_succ hL2 hc.err_nonneg) fun n _ h => mul_nonneg (by positivity) h
  · simpa using ((tendsto_add_atTop_iff_nat 1).2 hc.err_tendsto).const_mul
      ((L : ℝ) ^ 2 * (residueBox L).card * 16 * K ^ 2)
  · refine sides_mono (sides_and (h₁ L hL hs F i hF) (sides_and (h₂ L hL hs i)
      (sides_and (sides_succ hL2 hF) (sides_and (sides_succ hL2 ((h₄ L hL hs).1 F hF))
        (sides_and (sides_succ hL2 hc.approx) (sides_succ hL2 hc.err_nonneg))))))
      fun n hn ⟨a₁, a₂, a₃, a₄, a₅, a₆⟩ p hp a a' μ ν => ?_
    have hw := h₇ L n hs hn
    have hw' := h₇ L (n + 1) hs (Nat.succ_pos n)
    have hf := h₆ L (n + 1) hs (Nat.succ_pos n) F a₃
    have hq := rescaledMomentum_mem (n := n) hL hp
    exact compStep_hessian_bound hL hK
      (fun m' κ ρ μ hκ => hKb m' ρ μ κ fun ν => (hκ ν).trans (by linarith))
      (fun m' ρ σ => a₅ _ (hq m') a a' ρ σ) _
      (compStep_hessian_fourierModes hL hw hw' hf hH.eq_of_congr a₁ a₂ a₄.2.2.2.2 hp a a' μ ν)
end YangMills.Construction.Tower.TemperedComposition
end
