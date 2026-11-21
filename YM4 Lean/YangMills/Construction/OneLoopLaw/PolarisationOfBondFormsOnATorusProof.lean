import YangMills.Construction.OneLoopLaw.BondFormsAsSumsOfPlaneWaves
import YangMills.Construction.OneLoopLaw.GaugeColourMomentaAndDifferencesOfFunctionalsProof
import YangMills.Construction.OneLoopLaw.PolarisationIsInvariantUnderIsometries
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.OneLoopLaw.BondFormHessianOnTorus
open YangMills.Construction.Tower
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.Tempered
open YangMills.Construction.PeriodicOperators.RiemannSums
open YangMills.Construction.InfiniteLattice (AmbientSpace)
section Bilinearity
variable {L n : ℕ} {F : FieldFamily L}
private theorem hessian_zero_left (hF : ComplexHessianOfMember.Properties F n)
    {W : UnitEdge L n → Matrices.ComplexMatrix2} (hW : W ∈ complexEdgeForms L n 0 0) :
    complexHessian F n 0 W = 0 := by apply _root_.YangMills.SharedProofs.p5135 <;> assumption
private theorem hessian_smul_left (hF : ComplexHessianOfMember.Properties F n) (c : ℂ)
    {V W : UnitEdge L n → Matrices.ComplexMatrix2} (hV : V ∈ complexEdgeForms L n 0 0)
    (hW : W ∈ complexEdgeForms L n 0 0) :
    complexHessian F n (c • V) W = c * complexHessian F n V W := by
  have h := hF.linear_left c V hV 0 (Submodule.zero_mem _) W hW
  rwa [add_zero, hessian_zero_left hF hW, add_zero] at h
private theorem hessian_smul_right (hF : ComplexHessianOfMember.Properties F n) (c : ℂ)
    {V W : UnitEdge L n → Matrices.ComplexMatrix2} (hV : V ∈ complexEdgeForms L n 0 0)
    (hW : W ∈ complexEdgeForms L n 0 0) :
    complexHessian F n V (c • W) = c * complexHessian F n V W := by
  rw [hF.symm V hV _ (Submodule.smul_mem _ c hW), hessian_smul_left hF c hW hV,
    hF.symm W hW V hV]
private theorem hessian_sum_left (hF : ComplexHessianOfMember.Properties F n) {ι : Type*}
    (t : Finset ι) (A : ι → ℂ) (v : ι → UnitEdge L n → Matrices.ComplexMatrix2)
    (hv : ∀ i, v i ∈ complexEdgeForms L n 0 0) {W : UnitEdge L n → Matrices.ComplexMatrix2}
    (hW : W ∈ complexEdgeForms L n 0 0) :
    complexHessian F n (∑ i ∈ t, A i • v i) W = ∑ i ∈ t, A i * complexHessian F n (v i) W := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using hessian_zero_left hF hW
  | insert i t hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      hF.linear_left (A i) (v i) (hv i) _
        (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ (A j) (hv j)) W hW, ih]
private theorem hessian_sum_right (hF : ComplexHessianOfMember.Properties F n) {ι : Type*}
    (t : Finset ι) (A : ι → ℂ) (v : ι → UnitEdge L n → Matrices.ComplexMatrix2)
    (hv : ∀ i, v i ∈ complexEdgeForms L n 0 0) {V : UnitEdge L n → Matrices.ComplexMatrix2}
    (hV : V ∈ complexEdgeForms L n 0 0) :
    complexHessian F n V (∑ i ∈ t, A i • v i) = ∑ i ∈ t, A i * complexHessian F n V (v i) := by
  rw [hF.symm V hV _ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ (A j) (hv j)),
    hessian_sum_left hF t A v hv hV]
  exact Finset.sum_congr rfl fun i _ => by rw [hF.symm (v i) (hv i) V hV]
private theorem hessian_scaled_double_sum (hF : ComplexHessianOfMember.Properties F n)
    {ι : Type*} [Fintype ι] (s : ℂ) (A A' : ι → ℂ)
    (v v' : ι → UnitEdge L n → Matrices.ComplexMatrix2)
    (hv : ∀ i, v i ∈ complexEdgeForms L n 0 0) (hv' : ∀ i, v' i ∈ complexEdgeForms L n 0 0) :
    complexHessian F n (s • ∑ i, A i • v i) (s • ∑ i, A' i • v' i) =
      s * (s * ∑ i, ∑ j, A i * A' j * complexHessian F n (v i) (v' j)) := by
  have hS : (∑ i, A i • v i) ∈ complexEdgeForms L n 0 0 :=
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ (A j) (hv j)
  have hS' : (∑ i, A' i • v' i) ∈ complexEdgeForms L n 0 0 :=
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ (A' j) (hv' j)
  rw [hessian_smul_left hF s hS (Submodule.smul_mem _ s hS'),
    hessian_smul_right hF s hS hS', hessian_sum_left hF _ A v hv hS']
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hessian_sum_right hF _ A' v' hv' (hv i), Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring
end Bilinearity
private theorem exists_axis_phase_ne_one {z : AmbientSpace} (hz : z ∉ periodLattice) :
    ∃ ρ, Complex.exp (-(Complex.I * (z ρ : ℂ))) ≠ 1 := by
  by_contra h
  push Not at h
  apply hz
  choose k hk using fun ρ => Complex.exp_eq_one_iff.mp (h ρ)
  refine ⟨fun ρ => -k ρ, fun ρ => ?_⟩
  apply Complex.ofReal_injective
  apply mul_left_cancel₀ Complex.I_ne_zero
  push_cast
  linear_combination -(hk ρ)
private theorem bilinDot_basis (p : AmbientSpace) (ρ : Fin 4) :
    bilinDot (toComplexVec p) (toComplexVec (castVec (Pi.single ρ 1))) = (p ρ : ℂ) := by
  rw [bilinDot, Finset.sum_eq_single ρ]
  · simp [toComplexVec, castVec]
  · intro μ _ h
    simp [toComplexVec, castVec, h]
  · simp
private theorem hessian_vanishes_off_periods
    (hMotions : UnitLatticeMotions.Statement)
    (hWaves : PlaneWaveSymmetries.PlaneWaveLawsHold)
    (hInvariant : ComplexHessianInvariance.Statement)
    (hMember : ComplexHessianOfMember.Statement)
    (L n : ℕ) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (F : FieldFamily L)
    (hF : IsAdmissibleMember (F n)) (a a' : Fin 3) (μ ν : Fin 4) (p : AmbientSpace)
    (hp : p ∈ dualLattice (2 * L ^ n)) (p' : AmbientSpace) (hp' : p' ∈ dualLattice (2 * L ^ n))
    (hpp : p + p' ∉ periodLattice) :
    complexHessian F n (fourierModeForm L n a p μ) (fourierModeForm L n a' p' ν) = 0 := by
  obtain ⟨ρ, hρ⟩ := exists_axis_phase_ne_one hpp
  have props := hMember L n hL hn F hF
  have laws := hWaves L n hL hn
  obtain ⟨f, hind, hiso, honto⟩ := hMotions.2.2.2 L n hL hn 1 (one_mem _) hMotions.2.2.1
    (Pi.single ρ 1)
  have hV := laws.mem_complex a μ p hp
  have hV' := laws.mem_complex a' ν p' hp'
  have h := hInvariant L n hL hn F hF f hiso honto _ hV _ hV'
  have e₁ := laws.shift f _ hiso honto hind a μ p hp
  have e₂ := laws.shift f _ hiso honto hind a' ν p' hp'
  simp only [PlaneWaveSymmetries.tangentPushforward, bilinDot_basis] at e₁ e₂
  rw [e₁, e₂, hessian_smul_left props _ hV (Submodule.smul_mem _ _ hV'),
    hessian_smul_right props _ hV hV', ← mul_assoc, ← Complex.exp_add] at h
  have hexp : -(Complex.I * (p ρ : ℂ)) + -(Complex.I * (p' ρ : ℂ)) =
      -(Complex.I * (((p + p') ρ : ℝ) : ℂ)) := by
    simp only [Pi.add_apply]
    push_cast
    ring
  rw [hexp] at h
  have h₁ : (Complex.exp (-(Complex.I * (((p + p') ρ : ℝ) : ℂ))) - 1) *
      complexHessian F n (fourierModeForm L n a p μ) (fourierModeForm L n a' p' ν) = 0 := by
    rw [sub_mul, one_mul, h, sub_self]
  exact (mul_eq_zero.mp h₁).resolve_left (sub_ne_zero.mpr hρ)
theorem planeWaveExpansion_of_steps (hEdges : FourierExpansion.BondFormFourierExpansion)
    (hMotions : UnitLatticeMotions.Statement)
    (hWaves : PlaneWaveSymmetries.PlaneWaveLawsHold)
    (hInvariant : ComplexHessianInvariance.Statement)
    (hMember : ComplexHessianOfMember.Statement) : PlaneWaveExpansion := by
  intro L n hL hn F hF
  have hsel := hessian_vanishes_off_periods hMotions hWaves hInvariant hMember L n hL hn F hF
  refine ⟨fun a a' μ ν p hp p' hp' hpp => hsel a a' μ ν p hp p' hp' hpp, fun x y a a' => ?_⟩
  obtain ⟨hfin, hsum⟩ := hEdges L n hL hn
  have : Fintype (DualClasses (2 * L ^ n)) := Fintype.ofFinite _
  have props := hMember L n hL hn F hF
  have laws := hWaves L n hL hn
  set r : DualClasses (2 * L ^ n) → dualLattice (2 * L ^ n) := fun c => Quotient.out c with hr
  have hmk : ∀ c, (QuotientAddGroup.mk (r c) : DualClasses (2 * L ^ n)) = c :=
    fun c => QuotientAddGroup.out_eq' c
  rw [hsum a x, hsum a' y, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
    finsum_eq_sum_of_fintype,
    hessian_scaled_double_sum props _ _ _ _ _
      (fun c => laws.mem_complex a x.2 _ (r c).2)
      (fun c => laws.mem_complex a' y.2 _ (r c).2)]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_eq_single (-c)]
  · have hper : ((r c : AmbientSpace) + (r (-c) : AmbientSpace)) ∈ periodLattice := by
      have h0 : (QuotientAddGroup.mk (r c + r (-c)) : DualClasses (2 * L ^ n)) = 0 := by
        rw [QuotientAddGroup.mk_add, hmk, hmk, add_neg_cancel]
      exact AddSubgroup.mem_addSubgroupOf.mp ((QuotientAddGroup.eq_zero_iff _).mp h0)
    obtain ⟨e, he⟩ := hper
    have hcoord : ∀ μ, (r (-c) : AmbientSpace) μ =
        -(r c : AmbientSpace) μ + (e μ : ℝ) * (2 * Real.pi) := by
      intro μ
      have := he μ
      simp only [Pi.add_apply] at this
      linarith
    have hpoint : (r (-c) : AmbientSpace) = -(r c : AmbientSpace) + (2 * Real.pi) • castVec e := by
      funext μ
      simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, castVec, hcoord μ]
      ring
    have hneg : -(r c : AmbientSpace) ∈ dualLattice (2 * L ^ n) := neg_mem (r c).2
    have hmode : fourierModeForm L n a' (r (-c) : AmbientSpace) y.2 =
        fourierModeForm L n a' (-(r c : AmbientSpace)) y.2 := by
      rw [hpoint]
      exact laws.periodic a' y.2 _ hneg e
    have hphase : Complex.exp (-(Complex.I * bilinDot (toComplexVec (r c : AmbientSpace))
          (toComplexVec (castVec x.1)))) *
        Complex.exp (-(Complex.I * bilinDot (toComplexVec (r (-c) : AmbientSpace))
          (toComplexVec (castVec y.1)))) =
        Complex.exp (Complex.I * bilinDot (toComplexVec (r c : AmbientSpace))
          (toComplexVec (castVec (y.1 - x.1)))) := by
      rw [← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
      refine ⟨-∑ μ, e μ * y.1 μ, ?_⟩
      simp only [bilinDot, toComplexVec, castVec, Fin.sum_univ_four, hcoord, Pi.sub_apply]
      push_cast
      ring
    rw [hmode, hphase]
    ring
  · intro c' _ hne
    have hnot : (r c : AmbientSpace) + (r c' : AmbientSpace) ∉ periodLattice := by
      intro hmem
      have h0 : (QuotientAddGroup.mk (r c + r c') : DualClasses (2 * L ^ n)) = 0 :=
        (QuotientAddGroup.eq_zero_iff _).mpr (AddSubgroup.mem_addSubgroupOf.mpr hmem)
      rw [QuotientAddGroup.mk_add, hmk, hmk] at h0
      exact hne (eq_neg_of_add_eq_zero_right h0)
    rw [hsel a a' x.2 y.2 _ (r c).2 _ (r c').2 hnot, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h
end YangMills.Construction.OneLoopLaw.BondFormHessianOnTorus
end
