import YangMills.Construction.HilbertSpace.FormCompletionsAndBorelPVMs
import YangMills.Construction.ReflectionPositivity.TwoReflectionsAndFormsOfADirection
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
open InfiniteLattice (GaugeField LatticePoint axisStep shift halfSpaceLocalObservables observableSupNorm)
open ReflectionPositivity.MirrorHyperplanes (unitPositiveClass linkReflect siteReflect linkReflectionForm siteReflectionForm)
open HilbertSpace (SesqForm)
open JointSpectrum (CommutingFamily SpectralDomain)
open FormHilbert
instance {J H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    Inhabited (BorelPVM J H) := by
  classical
  let x : SpectralDomain J := (0, fun _ => 1)
  refine ⟨{ proj := fun S => if x ∈ S.1 then 1 else 0
            isStarProj := fun S => ?_
            proj_univ := by simp
            proj_inter := fun S S' => ?_
            hasSum_iUnion := fun v S hS => ?_ }⟩
  · split_ifs
    · exact IsStarProjection.one _
    · exact IsStarProjection.zero _
  · by_cases hx : x ∈ S.1 <;> by_cases hx' : x ∈ S'.1 <;> simp [hx, hx']
  · by_cases hex : ∃ k, x ∈ (S k).1
    · obtain ⟨k, hk⟩ := hex
      have hmem : x ∈ ⋃ k, (S k).1 := mem_iUnion.mpr ⟨k, hk⟩
      simp only [hmem, if_true]
      convert hasSum_single k
        (f := fun j => inner ℂ v ((if x ∈ (S j).1 then (1 : H →L[ℂ] H) else 0) v)) ?_ using 1
      · simp [hk]
      · intro j hj
        have : x ∉ (S j).1 := fun hx => (Set.disjoint_left.mp (hS hj) hx) hk
        simp [this]
    · have hmem : x ∉ ⋃ k, (S k).1 := fun hx => hex (mem_iUnion.mp hx)
      have hnot : ∀ j, x ∉ (S j).1 := fun j hj => hex ⟨j, hj⟩
      simp [hmem, hnot]
instance {J H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Fintype J] [Nonempty J] : Nonempty (CommutingFamily H J) :=
  ⟨{ A := 0
     B := fun _ => 1
     isSelfAdjoint_A := IsSelfAdjoint.zero _
     zero_le_A := le_rfl
     A_le_one := (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
       ContinuousLinearMap.isPositive_one
     commute_A_B := fun _ => Commute.zero_left _
     commute_B_B := fun _ _ => Commute.refl _ }⟩
inductive ReflectionPair
  | link
  | site
abbrev TransverseAxis (μ : Fin 4) : Type := {a : Fin 4 // a ≠ μ}
instance (μ : Fin 4) : Nonempty (TransverseAxis μ) :=
  ⟨⟨μ + 1, by revert μ; decide⟩⟩
def intPoint (w : Fin 4 → ℤ) : LatticePoint (1 : ℝ) :=
  ⟨fun i => (w i : ℝ), w, fun i => by simp⟩
namespace ReflectionPair
variable (r : ReflectionPair) (ν : unitPositiveClass) (μ : Fin 4)
def reflect : InfiniteLattice.UnitLatticeSymmetry :=
  match r with
  | link => linkReflect μ
  | site => siteReflect μ
def pairForm : SesqForm (halfSpaceLocalObservables μ) :=
  match r with
  | link => linkReflectionForm ν μ
  | site => siteReflectionForm ν μ
theorem pairForm_apply (F G : halfSpaceLocalObservables μ) :
    r.pairForm ν μ F G = ∫ U, conj ((r.reflect μ).actOn
      (F : GaugeField (1 : ℝ) → ℂ) U) * (G : GaugeField (1 : ℝ) → ℂ) U
      ∂(ν : Measure (GaugeField (1 : ℝ))) := by
  cases r <;> rfl
abbrev Hilb : Type := FormCompletion (r.pairForm ν μ)
def obsClass (F : GaugeField (1 : ℝ) → ℂ) : r.Hilb ν μ :=
  open Classical in
  if hF : F ∈ halfSpaceLocalObservables μ then formClass (r.pairForm ν μ) ⟨F, hF⟩ else 0
def IsTransferOp (T : r.Hilb ν μ →L[ℂ] r.Hilb ν μ) : Prop :=
  ∀ F ∈ halfSpaceLocalObservables μ, T (r.obsClass ν μ F) =
    r.obsClass ν μ ((shift (axisStep 1 μ)).actOn F)
def IsShiftOp (a : Fin 4) (V : r.Hilb ν μ →L[ℂ] r.Hilb ν μ) : Prop :=
  ∀ F ∈ halfSpaceLocalObservables μ, V (r.obsClass ν μ F) =
    r.obsClass ν μ ((shift (axisStep 1 a)).actOn F)
def IsOpFamily (S : CommutingFamily (r.Hilb ν μ) (TransverseAxis μ)) : Prop :=
  r.IsTransferOp ν μ S.A ∧ ∀ a, r.IsShiftOp ν μ a.1 (S.B a : r.Hilb ν μ →L[ℂ] r.Hilb ν μ)
def opFamily : CommutingFamily (r.Hilb ν μ) (TransverseAxis μ) :=
  Classical.epsilon (r.IsOpFamily ν μ)
def transferOp : r.Hilb ν μ →L[ℂ] r.Hilb ν μ := (r.opFamily ν μ).A
def shiftOp (a : TransverseAxis μ) : r.Hilb ν μ →L[ℂ] r.Hilb ν μ :=
  ((r.opFamily ν μ).B a : r.Hilb ν μ →L[ℂ] r.Hilb ν μ)
def shiftMonomial (w : Fin 4 → ℤ) : r.Hilb ν μ →L[ℂ] r.Hilb ν μ :=
  (r.opFamily ν μ).unitaryMonomial fun a => w a.1
def jointPVM : BorelPVM (TransverseAxis μ) (r.Hilb ν μ) :=
  Classical.epsilon (IsJointPVM (r.opFamily ν μ))
end ReflectionPair
def spectrumTop (J : Type*) : MeasSubset J :=
  ⟨{x | x.1 = 1}, measurable_fst (measurableSet_singleton _)⟩
def spectrumBottom (J : Type*) : MeasSubset J :=
  ⟨{x | x.1 = 0}, measurable_fst (measurableSet_singleton _)⟩
def ReflectionPairTheorem : Prop :=
  ∀ (ν : unitPositiveClass) (μ : Fin 4) (r : ReflectionPair),
    (IsPosSesqForm (r.pairForm ν μ) ∧ (r.pairForm ν μ).IsConjSymm ∧
      ∀ F ∈ halfSpaceLocalObservables μ, ‖r.obsClass ν μ F‖ ≤ observableSupNorm F) ∧
    ((∃! T, r.IsTransferOp ν μ T) ∧
      (∀ a : TransverseAxis μ, ∃! V : r.Hilb ν μ →L[ℂ] r.Hilb ν μ,
        V ∈ unitary (r.Hilb ν μ →L[ℂ] r.Hilb ν μ) ∧ r.IsShiftOp ν μ a.1 V) ∧
      r.IsOpFamily ν μ (r.opFamily ν μ)) ∧
    (∀ F ∈ halfSpaceLocalObservables μ, ∀ G ∈ halfSpaceLocalObservables μ, ∀ (n : ℕ) (w : Fin 4 → ℤ),
      w μ = 0 →
      inner ℂ (r.obsClass ν μ F)
          ((r.transferOp ν μ ^ n * r.shiftMonomial ν μ w) (r.obsClass ν μ G)) =
        ∫ U, conj ((r.reflect μ).actOn F U) *
          (shift (n • axisStep 1 μ + intPoint w)).actOn G U
          ∂(ν : Measure (GaugeField (1 : ℝ)))) ∧
    ((∃! P, IsJointPVM (r.opFamily ν μ) P) ∧
      IsJointPVM (r.opFamily ν μ) (r.jointPVM ν μ) ∧
      IsOrthProjOnto (r.jointPVM ν μ (spectrumTop (TransverseAxis μ)))
        {v | (1 - r.transferOp ν μ) v = 0} ∧
      IsOrthProjOnto (r.jointPVM ν μ (spectrumBottom (TransverseAxis μ)))
        {v | r.transferOp ν μ v = 0})
end YangMills.Construction.ReflectionPositivity.DirectionPictures
end
