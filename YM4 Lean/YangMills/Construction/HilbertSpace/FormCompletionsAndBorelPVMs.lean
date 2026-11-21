import YangMills.Construction.EnergyMomentum.LatticeBasics
import YangMills.Construction.HilbertSpace.FormsOperatorsSpectralMeasures
import YangMills.Construction.JointSpectrum.CommutingFamilies
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ComplexConjugate ComplexOrder ENNReal
noncomputable section
namespace YangMills.Construction.FormHilbert
open YangMills.Construction.HilbertSpace
section Forms
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
structure IsPosSesqForm (b : SesqForm V) : Prop where
  sesq : b.IsSesquilinear
  nonneg : b.IsNonnegDiag
theorem isPosSesqForm_zero : IsPosSesqForm (fun _ _ => 0 : SesqForm V) where
  sesq := ⟨by simp, by simp, by simp, by simp⟩
  nonneg := fun _ => by simp
theorem IsPosSesqForm.isConjSymm {b : SesqForm V} (h : IsPosSesqForm b) : b.IsConjSymm := by
  intro x y
  have hs := h.sesq
  have dx := (h.nonneg x).1
  have dy := (h.nonneg y).1
  have e₁ := (h.nonneg (x + y)).1
  have e₂ := (h.nonneg (x + Complex.I • y)).1
  rw [hs.add_left, hs.add_right, hs.add_right] at e₁
  rw [hs.add_left, hs.add_right, hs.add_right, hs.smul_left, hs.smul_left, hs.smul_right,
    hs.smul_right] at e₂
  simp only [Complex.add_im, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.I_re,
    Complex.I_im, Complex.mul_re] at e₁ e₂
  apply Complex.ext
  · simp only [Complex.conj_re]
    linarith
  · simp only [Complex.conj_im]
    linarith
def posRestrict (b : SesqForm V) : SesqForm V :=
  open Classical in if IsPosSesqForm b then b else fun _ _ => 0
theorem isPosSesqForm_posRestrict (b : SesqForm V) : IsPosSesqForm (posRestrict b) := by
  unfold posRestrict
  split_ifs with h
  · exact h
  · exact isPosSesqForm_zero
theorem posRestrict_eq_self {b : SesqForm V} (h : IsPosSesqForm b) : posRestrict b = b :=
  if_pos h
@[reducible] def formInnerCore (b : SesqForm V) : PreInnerProductSpace.Core ℂ V where
  inner := posRestrict b
  conj_inner_symm x y := ((isPosSesqForm_posRestrict b).isConjSymm y x).symm
  re_inner_nonneg x := ((isPosSesqForm_posRestrict b).nonneg x).2
  add_left := (isPosSesqForm_posRestrict b).sesq.add_left
  smul_left x y r := (isPosSesqForm_posRestrict b).sesq.smul_left r x y
def FormSeminormed (_b : SesqForm V) : Type _ := V
instance (b : SesqForm V) : SeminormedAddCommGroup (FormSeminormed b) :=
  @InnerProductSpace.Core.toSeminormedAddCommGroup ℂ V _ _ _ (formInnerCore b)
instance (b : SesqForm V) : InnerProductSpace ℂ (FormSeminormed b) :=
  InnerProductSpace.ofCore (formInnerCore b)
abbrev FormCompletion (b : SesqForm V) : Type _ := UniformSpace.Completion (FormSeminormed b)
def formClass (b : SesqForm V) : V →ₗ[ℂ] FormCompletion b :=
  (UniformSpace.Completion.toComplₗᵢ (𝕜 := ℂ) (E := FormSeminormed b)).toLinearMap
theorem inner_formClass {b : SesqForm V} (h : IsPosSesqForm b) (x y : V) :
    inner ℂ (formClass b x) (formClass b y) = b x y := by
  refine Eq.trans (UniformSpace.Completion.inner_coe (𝕜 := ℂ) (show FormSeminormed b from x)
    (show FormSeminormed b from y)) ?_
  change posRestrict b x y = b x y
  rw [posRestrict_eq_self h]
end Forms
section Operators
variable {H H' : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
theorem isSelfAdjoint_iff_inner_eq (A : H →L[ℂ] H) :
    IsSelfAdjoint A ↔ ∀ u v, inner ℂ u (A v) = inner ℂ (A u) v := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  exact ⟨fun h u v => (h u v).symm, fun h u v => (h u v).symm⟩
theorem le_iff_inner_sub_nonneg {A B : H →L[ℂ] H} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    B ≤ A ↔ ∀ u, 0 ≤ inner ℂ u ((A - B) u) := by apply _root_.YangMills.Construction.LatticeBasics.le_iff_inner_nonneg <;> assumption
def IsUnitaryLinearMap (U : H →ₗ[ℂ] H') : Prop :=
  Function.Bijective U ∧ ∀ u v, inner ℂ (U u) (U v) = inner ℂ u v
theorem mem_unitary_iff_isUnitaryLinearMap (U : H →L[ℂ] H) :
    U ∈ unitary (H →L[ℂ] H) ↔ IsUnitaryLinearMap (U : H →ₗ[ℂ] H) := by
  constructor
  · intro h
    let e := Unitary.linearIsometryEquiv ⟨U, h⟩
    have he : ∀ u, e u = U u := fun u => rfl
    refine ⟨?_, fun u v => ?_⟩
    · have : (U : H → H) = e := funext fun u => (he u).symm
      simpa [this] using e.bijective
    · simpa [he] using e.inner_map_map u v
  · rintro ⟨hb, hi⟩
    have h₁ : star U * U = 1 := by
      have := (ContinuousLinearMap.inner_map_map_iff_adjoint_comp_self U).mp hi
      simpa [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def] using this
    have h₂ : U * star U = 1 := by
      ext u
      obtain ⟨w, rfl⟩ := hb.2 u
      have : (star U) (U w) = w := congrArg (fun T : H →L[ℂ] H => T w) h₁
      change U (star U (U w)) = U w
      rw [this]
    exact Unitary.mem_iff.mpr ⟨h₁, h₂⟩
def StrongTendsto (A : ℕ → H →L[ℂ] H) (B : H →L[ℂ] H) : Prop :=
  ∀ u, Tendsto (fun n => ‖A n u - B u‖) atTop (𝓝 0)
def IsOrthProjOnto (P : H →L[ℂ] H) (M : Set H) : Prop :=
  IsStarProjection P ∧ Set.range P = M
def orthSet (M : Set H) : Set H := {w | ∀ u ∈ M, inner ℂ u w = 0}
end Operators
section Spectral
open YangMills.Construction.JointSpectrum
variable (ι : Type*) (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
abbrev MeasSubset (ι : Type*) : Type _ := {S : Set (SpectralDomain ι) // MeasurableSet S}
structure BorelPVM where
  proj : MeasSubset ι → H →L[ℂ] H
  isStarProj : ∀ S, IsStarProjection (proj S)
  proj_univ : proj ⟨univ, MeasurableSet.univ⟩ = 1
  proj_inter : ∀ S T : MeasSubset ι,
    proj ⟨S.1 ∩ T.1, S.2.inter T.2⟩ = proj S * proj T
  hasSum_iUnion : ∀ (u : H) (S : ℕ → MeasSubset ι),
    (Pairwise fun k l => Disjoint (S k).1 (S l).1) →
      HasSum (fun k => inner ℂ u (proj (S k) u))
        (inner ℂ u (proj ⟨⋃ k, (S k).1, MeasurableSet.iUnion fun k => (S k).2⟩ u))
variable {ι H}
namespace BorelPVM
instance : CoeFun (BorelPVM ι H) fun _ => MeasSubset ι → H →L[ℂ] H :=
  ⟨proj⟩
theorem inner_apply_eq_norm_sq (E : BorelPVM ι H) (S : MeasSubset ι) (u : H) :
    inner ℂ u (E S u) = ((‖E S u‖ ^ 2 : ℝ) : ℂ) := by
  have hs := (isSelfAdjoint_iff_inner_eq (E S)).mp (E.isStarProj S).isSelfAdjoint
  have hi : E S (E S u) = E S u :=
    congrArg (fun T : H →L[ℂ] H => T u) (E.isStarProj S).isIdempotentElem.eq
  have h₁ : inner ℂ u (E S u) = inner ℂ (E S u) (E S u) := by
    have := hs u (E S u)
    rwa [hi] at this
  rw [h₁, inner_self_eq_norm_sq_to_K]
  push_cast
  rfl
theorem norm_sq_apply_empty (E : BorelPVM ι H) (u : H) :
    ‖E ⟨∅, MeasurableSet.empty⟩ u‖ ^ 2 = 0 := by
  have h := E.hasSum_iUnion u (fun _ => ⟨∅, MeasurableSet.empty⟩)
    (fun _ _ _ => disjoint_bot_left)
  have h₀ := h.summable.tendsto_atTop_zero
  have h₁ : inner ℂ u (E ⟨∅, MeasurableSet.empty⟩ u) = 0 :=
    tendsto_nhds_unique tendsto_const_nhds h₀
  rw [inner_apply_eq_norm_sq] at h₁
  exact_mod_cast h₁
def quadMeasure (E : BorelPVM ι H) (u : H) :
    Measure (SpectralDomain ι) :=
  Measure.ofMeasurable (fun S hS => ENNReal.ofReal (‖E ⟨S, hS⟩ u‖ ^ 2))
    (by simp only [E.norm_sq_apply_empty u, ENNReal.ofReal_zero])
    (by
      intro f hf hd
      have h := E.hasSum_iUnion u (fun k => ⟨f k, hf k⟩) hd
      simp only [inner_apply_eq_norm_sq] at h
      have hr := Complex.hasSum_ofReal.mp h
      rw [← hr.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hr.summable])
theorem quadMeasure_apply (E : BorelPVM ι H) (u : H) (S : MeasSubset ι) :
    E.quadMeasure u S.1 = ENNReal.ofReal (‖E S u‖ ^ 2) :=
  Measure.ofMeasurable_apply _ S.2
def IsSpectralIntegral (E : BorelPVM ι H) (φ : SpectralDomain ι → ℂ)
    (A : H →L[ℂ] H) : Prop :=
  ∀ u, inner ℂ u (A u) = ∫ p, φ p ∂(E.quadMeasure u)
def spectralOp (E : BorelPVM ι H) (φ : SpectralDomain ι → ℂ) : H →L[ℂ] H :=
  open Classical in if h : ∃ A, E.IsSpectralIntegral φ A then Classical.choose h else 0
def IsSupportedOn (E : BorelPVM ι H) (C : MeasSubset ι) : Prop :=
  E ⟨C.1ᶜ, C.2.compl⟩ = 0
end BorelPVM
def IsBddMeasurable (φ : SpectralDomain ι → ℂ) : Prop :=
  Measurable φ ∧ ∃ K : ℝ, ∀ p, ‖φ p‖ ≤ K
def IsJointPVM [Fintype ι] [Nonempty ι] (F : CommutingFamily H ι)
    (E : BorelPVM ι H) : Prop :=
  E.IsSpectralIntegral (fun p => ((p.1 : ℝ) : ℂ)) F.A ∧
    ∀ l, E.IsSpectralIntegral (fun p => ((p.2 l : Circle) : ℂ)) (F.B l : H →L[ℂ] H)
end Spectral
section Integrable
variable {Y : Type*} [mY : MeasurableSpace Y]
def subFieldL2 (m : Measure Y) (G : MeasurableSpace Y) (_hG : G ≤ mY) :
    Set (Lp ℂ 2 m) :=
  {f | ∃ g : Y → ℂ, Measurable[G] g ∧ (f : Y → ℂ) =ᵐ[m] g}
def densityMeasure (φ : Y → ℝ) (m : Measure Y) : Measure Y :=
  m.withDensity fun y => ENNReal.ofReal (φ y)
end Integrable
end YangMills.Construction.FormHilbert
