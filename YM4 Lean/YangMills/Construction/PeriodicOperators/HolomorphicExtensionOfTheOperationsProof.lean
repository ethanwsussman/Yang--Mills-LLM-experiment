import YangMills.Construction.PeriodicOperators.PeriodicOperatorsOfFiniteRangeAsLocalOperatorFunctionsProof
import YangMills.Construction.PeriodicOperators.HolomorphicExtensionOfTheOperations
import YangMills.Construction.PeriodicOperators.MatricesOnATorusInCoordinatesProof
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.PeriodicOperators.HolomorphicCoordinateClosure
open YangMills.Construction.Coordinates.ComplexCoordinates.PowerSeriesHolomorphy (openPolydisk)
private def HolOnDisk {l : ℕ} (ρ : ℝ) (h : YangMills.Construction.Coordinates.ComplexCoordinates l → ℂ) : Prop :=
  YangMills.Construction.Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) (openPolydisk 0 ρ) (fun z _ => h z)
private lemma isOpen_openPolydisk_zero {l : ℕ} (ρ : ℝ) :
    IsOpen (openPolydisk (0 : YangMills.Construction.Coordinates.ComplexCoordinates l) ρ) := by apply _root_.YangMills.Construction.PeriodicOperators.TorusMatrixCoordinates.isOpen_openPolydisk_zero <;> assumption
private lemma holOnDisk_iff {l : ℕ} (ρ : ℝ) (h : YangMills.Construction.Coordinates.ComplexCoordinates l → ℂ) :
    HolOnDisk ρ h ↔ ContinuousOn h (openPolydisk 0 ρ) ∧
      ∀ a ∈ openPolydisk (0 : YangMills.Construction.Coordinates.ComplexCoordinates l) ρ,
      ∀ j : Fin l, ∀ᶠ w in 𝓝 (0 : ℂ),
        DifferentiableAt ℂ (fun w : ℂ =>
          h (a + w • YangMills.Construction.Coordinates.ComplexCoordinates.stdBasisVector j)) w := by
  unfold HolOnDisk YangMills.Construction.Coordinates.ComplexCoordinates.IsHolomorphicIn
  constructor
  · rintro ⟨-, hc, hd⟩
    refine ⟨(continuous_apply (0 : Fin 1)).comp_continuousOn hc, fun a ha j => ?_⟩
    filter_upwards [hd a ha j] with w hw
    exact (differentiableAt_pi.1 hw) 0
  · rintro ⟨hc, hd⟩
    refine ⟨isOpen_openPolydisk_zero ρ, continuousOn_pi.2 fun _ => hc, fun a ha j => ?_⟩
    filter_upwards [hd a ha j] with w hw
    exact differentiableAt_pi.2 fun _ => hw
abbrev _root_.YangMills.DeltaSharedProofs.p501307 := @holOnDisk_iff
private lemma holOnDisk_const {l : ℕ} (ρ : ℝ) (c : ℂ) :
    HolOnDisk ρ (fun _ : YangMills.Construction.Coordinates.ComplexCoordinates l => c) := by apply _root_.YangMills.Construction.PeriodicOperators.ConstantOpFun.isHolomorphicIn_const <;> assumption
private lemma holOnDisk_apply {l : ℕ} (ρ : ℝ) (i : Fin l) :
    HolOnDisk ρ (fun z : YangMills.Construction.Coordinates.ComplexCoordinates l => z i) := by
  refine (holOnDisk_iff ρ _).2 ⟨(continuous_apply i).continuousOn, fun a _ j =>
    Eventually.of_forall fun w => ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  fun_prop
private lemma HolOnDisk.add {l : ℕ} {ρ : ℝ} {f g : YangMills.Construction.Coordinates.ComplexCoordinates l → ℂ}
    (hf : HolOnDisk ρ f) (hg : HolOnDisk ρ g) :
    HolOnDisk ρ (fun z => f z + g z) := by
  obtain ⟨c, d⟩ := (holOnDisk_iff ρ f).1 hf
  obtain ⟨c', d'⟩ := (holOnDisk_iff ρ g).1 hg
  refine (holOnDisk_iff ρ _).2 ⟨c.add c', fun a ha j => ?_⟩
  filter_upwards [d a ha j, d' a ha j] with w u v
  exact u.add v
abbrev _root_.YangMills.DeltaSharedProofs.p500673 := @HolOnDisk.add
private lemma HolOnDisk.mul {l : ℕ} {ρ : ℝ} {f g : YangMills.Construction.Coordinates.ComplexCoordinates l → ℂ}
    (hf : HolOnDisk ρ f) (hg : HolOnDisk ρ g) :
    HolOnDisk ρ (fun z => f z * g z) := by
  obtain ⟨c, d⟩ := (holOnDisk_iff ρ f).1 hf
  obtain ⟨c', d'⟩ := (holOnDisk_iff ρ g).1 hg
  refine (holOnDisk_iff ρ _).2 ⟨c.mul c', fun a ha j => ?_⟩
  filter_upwards [d a ha j, d' a ha j] with w u v
  exact u.mul v
abbrev _root_.YangMills.DeltaSharedProofs.p501019 := @HolOnDisk.mul
private lemma HolOnDisk.mono {l : ℕ} {ρ ρ' : ℝ} {f : YangMills.Construction.Coordinates.ComplexCoordinates l → ℂ}
    (hle : ρ' ≤ ρ) (hf : HolOnDisk ρ f) :
    HolOnDisk ρ' f := by
  obtain ⟨c, d⟩ := (holOnDisk_iff ρ f).1 hf
  have hsub : openPolydisk (0 : YangMills.Construction.Coordinates.ComplexCoordinates l) ρ' ⊆ openPolydisk 0 ρ :=
    fun z hz j => (hz j).trans_le hle
  exact (holOnDisk_iff ρ' _).2 ⟨c.mono hsub, fun a ha j => d a (hsub ha) j⟩
private lemma HolOnDisk.comp_reindex {l l' : ℕ} {ρ : ℝ}
    {f : YangMills.Construction.Coordinates.ComplexCoordinates l → ℂ} (σ : Fin l → Fin l')
    (hσ : Function.Injective σ) (hf : HolOnDisk ρ f) :
    HolOnDisk ρ (fun z : YangMills.Construction.Coordinates.ComplexCoordinates l' => f (fun i => z (σ i))) := by
  obtain ⟨c, d⟩ := (holOnDisk_iff ρ f).1 hf
  have hmaps : MapsTo (fun (z : YangMills.Construction.Coordinates.ComplexCoordinates l') (i : Fin l) => z (σ i))
      (openPolydisk 0 ρ) (openPolydisk 0 ρ) := fun z hz i => hz (σ i)
  refine (holOnDisk_iff ρ _).2 ⟨c.comp (by fun_prop) hmaps, fun a ha j => ?_⟩
  by_cases hj : ∃ j', σ j' = j
  · obtain ⟨j', rfl⟩ := hj
    have key : ∀ w : ℂ,
        (fun i => (a + w • YangMills.Construction.Coordinates.ComplexCoordinates.stdBasisVector (σ j')) (σ i)) =
        (fun i => a (σ i)) + w • YangMills.Construction.Coordinates.ComplexCoordinates.stdBasisVector j' := by
      intro w
      ext i
      by_cases hi : i = j'
      · subst hi; simp [YangMills.Construction.Coordinates.ComplexCoordinates.stdBasisVector]
      · have : σ i ≠ σ j' := fun e => hi (hσ e)
        simp [YangMills.Construction.Coordinates.ComplexCoordinates.stdBasisVector, hi, this]
    simp only [key]
    exact d _ (hmaps ha) j'
  · have key : ∀ w : ℂ,
        (fun i => (a + w • YangMills.Construction.Coordinates.ComplexCoordinates.stdBasisVector j) (σ i)) =
        fun i => a (σ i) := by
      intro w
      ext i
      have : σ i ≠ j := fun e => hj ⟨i, e⟩
      simp [YangMills.Construction.Coordinates.ComplexCoordinates.stdBasisVector, this]
    simp only [key]
    exact Eventually.of_forall fun _ => differentiableAt_const _
private lemma exists_holOnDisk_of_subset {F : PeriodicData} {ρ : ℝ} {S T : Set F.Carrier} {l' : ℕ}
    (e' : Fin l' ≃ T) (hST : S ⊆ T) {g : (F.Carrier → ℂ) → ℂ}
    (hg : HolomorphicInValuesBelow F ρ S g) :
    ∃ f : YangMills.Construction.Coordinates.ComplexCoordinates l' → ℂ, HolOnDisk ρ f ∧
      ∀ x, IsSupBelow F x ρ → g x = f (fieldValues e' x) := by
  obtain ⟨l, e, f, hf, hfg⟩ := hg
  let σ : Fin l → Fin l' := fun i => e'.symm ⟨e i, hST (e i).2⟩
  have hσ : Function.Injective σ := by
    intro i j hij
    have := congrArg Subtype.val (e'.symm.injective hij)
    exact e.injective (Subtype.ext this)
  refine ⟨fun z => f (fun i => z (σ i)), HolOnDisk.comp_reindex σ hσ hf, fun x hx => ?_⟩
  rw [hfg x hx]
  congr 1
  ext i
  simp [fieldValues, σ]
theorem closureHolds_holds : ClosureHolds := by
  intro F ρ T _ hT
  have : Finite T := hT
  obtain ⟨l, ⟨e⟩⟩ := Finite.exists_equiv_fin T
  have e' : Fin l ≃ T := e.symm
  have ofHol : ∀ {g : (F.Carrier → ℂ) → ℂ} (f : YangMills.Construction.Coordinates.ComplexCoordinates l → ℂ),
      HolOnDisk ρ f → (∀ x, IsSupBelow F x ρ → g x = f (fieldValues e' x)) →
      HolomorphicInValuesBelow F ρ T g :=
    fun f hf hfg => ⟨l, e', f, hf, hfg⟩
  have hadd : ∀ g g' : (F.Carrier → ℂ) → ℂ, HolomorphicInValuesBelow F ρ T g →
      HolomorphicInValuesBelow F ρ T g' → HolomorphicInValuesBelow F ρ T fun x => g x + g' x := by
    intro g g' hg hg'
    obtain ⟨f, hf, hfg⟩ := exists_holOnDisk_of_subset e' subset_rfl hg
    obtain ⟨f', hf', hfg'⟩ := exists_holOnDisk_of_subset e' subset_rfl hg'
    exact ofHol _ (hf.add hf') fun x hx => by rw [hfg x hx, hfg' x hx]
  have hconst : ∀ c : ℂ, HolomorphicInValuesBelow F ρ T fun _ => c :=
    fun c => ofHol _ (holOnDisk_const ρ c) fun _ _ => rfl
  refine
    { of_subset := ?_, of_radius_le := ?_, congr_below := ?_, const := hconst, coord := ?_,
      add := hadd, mul := ?_, sum := ?_ }
  · intro S g hST hg
    obtain ⟨f, hf, hfg⟩ := exists_holOnDisk_of_subset e' hST hg
    exact ofHol f hf hfg
  · rintro ρ' g - hle ⟨m, n, f, hf, hfg⟩
    refine ⟨m, n, f, HolOnDisk.mono hle hf, fun x hx => hfg x ?_⟩
    obtain ⟨r, hr, hb⟩ := hx
    exact ⟨r, hr.trans_le hle, hb⟩
  · rintro g g' hgg ⟨m, n, f, hf, hfg⟩
    exact ⟨m, n, f, hf, fun x hx => by rw [← hgg x hx, hfg x hx]⟩
  · intro k hk
    refine ofHol (fun z => z (e'.symm ⟨k, hk⟩)) (holOnDisk_apply ρ _) fun x _ => ?_
    simp [fieldValues]
  · intro g g' hg hg'
    obtain ⟨f, hf, hfg⟩ := exists_holOnDisk_of_subset e' subset_rfl hg
    obtain ⟨f', hf', hfg'⟩ := exists_holOnDisk_of_subset e' subset_rfl hg'
    exact ofHol _ (hf.mul hf') fun x hx => by rw [hfg x hx, hfg' x hx]
  · intro ι s g
    classical
    induction s using Finset.induction_on with
    | empty =>
      intro _
      simpa using hconst 0
    | insert i s hi ih =>
      intro hs
      have := hadd _ _ (hs i (Finset.mem_insert_self i s))
        (ih fun j hj => hs j (Finset.mem_insert_of_mem hj))
      simpa [Finset.sum_insert hi] using this
end YangMills.Construction.PeriodicOperators.HolomorphicCoordinateClosure
end
