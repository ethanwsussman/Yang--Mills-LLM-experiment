import YangMills.Construction.Continuum.DisjointMembersOfTheStockBetweenCompactAndOpenSets
import YangMills.Construction.Continuum.SeparatingFamilyIsCountableStableAndApproximating
import YangMills.Construction.InfiniteLattice.SeparatedTuplesOfFourSpaceAsSymbols
import YangMills.Construction.Torus.SeparatedTuplesFormsAndDistinctPointsOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
open Filter Set YangMills.Construction.Continuum.SeparatedFourTuples YangMills.Construction.AmbientPoints YangMills.Construction.Continuum.CanonicalDecomposition YangMills.Construction.Continuum.RationalBoxes YangMills.Construction.TestFunctions
open scoped Topology
noncomputable section
namespace YangMills.Construction.CanonicalDecomposition
variable {s : Conventions.StandingParameters}
theorem image_homeomorphR4 (A : Set (EuclideanFour s)) :
    (homeomorphR4 s) '' A = A := by
  ext x
  exact ⟨by rintro ⟨y, hy, rfl⟩; exact hy, fun hx => ⟨x, hx, rfl⟩⟩
theorem isCompact_pi_of_isCompact {A : Set (EuclideanFour s)} (hA : IsCompact A) :
    IsCompact (X := Fin 4 → ℝ) A := by
  have h := hA.image (homeomorphR4 s).continuous
  rwa [image_homeomorphR4] at h
theorem isCompact_of_isCompact_pi {A : Set (EuclideanFour s)} (hA : IsCompact (X := Fin 4 → ℝ) A) :
    IsCompact A := by
  rw [← (homeomorphR4 s).isCompact_image, image_homeomorphR4]
  exact hA
theorem isOpen_pi_of_isOpen {A : Set (EuclideanFour s)} (hA : IsOpen A) :
    IsOpen (X := Fin 4 → ℝ) A := by
  have h := (homeomorphR4 s).isOpenMap A hA
  rwa [image_homeomorphR4] at h
theorem isCompact_of_mem_boxUnions {Q : Set (Fin 4 → ℝ)} (hQ : Q ∈ boxUnions) : IsCompact Q := by
  obtain ⟨r, b, hb, rfl⟩ := hQ
  refine isCompact_iUnion fun i => ?_
  obtain ⟨c, d, -, e⟩ := hb i
  rw [e]
  exact isCompact_univ_pi fun μ => isCompact_Icc
theorem tsupport_subset_of_mem_c1Off {Q : Set (Fin 4 → ℝ)} (hQ : Q ∈ boxUnions)
    {f : EuclideanFour s → ℝ} (hf : f ∈ c1Off Q) : tsupport f ⊆ Q := by
  rw [tsupport_eq_of_r4]
  refine closure_minimal (fun x hx => ?_) (isCompact_of_mem_boxUnions hQ).isClosed
  by_contra hxQ
  exact hx (hf.2 x hxQ)
theorem sub_mem_c1Off {Q : Set (Fin 4 → ℝ)} {f g : (Fin 4 → ℝ) → ℝ}
    (hf : f ∈ c1Off Q) (hg : g ∈ c1Off Q) : f - g ∈ c1Off Q := by
  refine ⟨ContDiff.sub hf.1 hg.1, fun x hx => ?_⟩
  simp [hf.2 x hx, hg.2 x hx]
theorem sharpNormR4_sub_comm (M : ℝ) (f g : (Fin 4 → ℝ) → ℝ) :
    sharpNormR4 M (f - g) = sharpNormR4 M (g - f) := by
  have h₁ : uniformNorm (f - g) = uniformNorm (g - f) := by
    unfold uniformNorm
    congr 1
    funext x
    simpa using norm_sub_rev (f x) (g x)
  have h₂ : lipConstR4 (f - g) = lipConstR4 (g - f) := by
    unfold lipConstR4 bestLipschitzConstant
    congr 1
    ext C
    have h : ∀ x y, ‖(f - g) x - (f - g) y‖ = ‖(g - f) x - (g - f) y‖ := fun x y => by
      rw [← norm_neg]
      congr 1
      simp only [Pi.sub_apply]
      ring
    simp only [h]
  unfold sharpNormR4
  rw [h₁, h₂]
theorem isDistIsometry_hyperoctahedralEquiv
    {w : InfiniteLattice.AmbientSpace ≃ₗ[ℝ] InfiniteLattice.AmbientSpace}
    (hw : w ∈ InfiniteLattice.hyperoctahedralLinearGroup) :
    IsDistIsometry (hyperoctahedralEquiv s w) := by
  obtain ⟨π, ε, h⟩ := (InfiniteLattice.mem_hyperoctahedralLinearGroup_iff w).1 hw
  have key : ∀ a b : Fin 4 → ℝ,
      TorusMetric.euclidNormVec (w a - w b) = TorusMetric.euclidNormVec (a - b) := by
    intro a b
    unfold TorusMetric.euclidNormVec
    congr 1
    rw [← Equiv.sum_comp π (fun ν => (a - b) ν ^ 2)]
    refine Finset.sum_congr rfl fun μ _ => ?_
    simp only [Pi.sub_apply, h]
    rcases Int.units_eq_one_or (ε μ) with e | e
    · rw [e]
      simp
    · rw [e]
      simp
      ring
  intro x y
  exact key x y
theorem exists_mem_separatingTuples_transport {r : EuclideanFour s ≃ EuclideanFour s}
    (hr : IsDistIsometry r)
    (hD : ∀ f ∈ ⋃ Q, chosenSaturatedFamily s Q,
      transportFn r f ∈ ⋃ Q, chosenSaturatedFamily s Q)
    {X : SepTuple s} (hX : X ∈ separatingTuples s) :
    ∃ Y ∈ separatingTuples s, Y.1 = transportedTuple r X.1 := by
  rcases hX with hX | ⟨h₁, hX⟩
  · obtain rfl : X = nilSepTuple s := hX
    exact ⟨nilSepTuple s, Or.inl rfl, (transportedTuple_nil r).symm⟩
  · exact ⟨⟨transportedTuple r X.1, FourSpaceSymbols.transportSymTuple_mem hr ⟨X.1, X.2⟩⟩,
      Or.inr ⟨h₁, fun i => hD _ (hX i)⟩, rfl⟩
theorem separatingTuples_countable
    (hU : (⋃ Q, chosenSaturatedFamily s Q).Countable) : (separatingTuples s).Countable := by
  have : Countable (⋃ Q, chosenSaturatedFamily s Q : Set ((Fin 4 → ℝ) → ℝ)) := hU.to_subtype
  let φ : (Σ n : ℕ, Fin n → (⋃ Q, chosenSaturatedFamily s Q : Set ((Fin 4 → ℝ) → ℝ))) →
      FunctionTuple s .euclidean := fun p => ⟨p.1, fun i => (p.2 i).1⟩
  have hpre : (Subtype.val ⁻¹' range φ : Set (SepTuple s)).Countable :=
    (countable_range φ).preimage Subtype.val_injective
  refine ((countable_singleton (nilSepTuple s)).union hpre).mono ?_
  rintro X (hX | ⟨-, hX⟩)
  · exact Or.inl hX
  · exact Or.inr ⟨⟨tupleLength X, fun i => ⟨tupleComponents X i, hX i⟩⟩, rfl⟩
theorem concat_mem_separatingTuples {X Y : SepTuple s}
    (hX : X ∈ separatingTuples s) (hY : Y ∈ separatingTuples s) (h : CanConcat X Y) :
    concat X Y h ∈ separatingTuples s := by
  rcases hX with hX | ⟨h₁, hX⟩
  · obtain rfl : X = nilSepTuple s := hX
    have e : concat (nilSepTuple s) Y h = Y := nil_concat Y
    rwa [e]
  rcases hY with hY | ⟨-, hY⟩
  · obtain rfl : Y = nilSepTuple s := hY
    have e : concat X (nilSepTuple s) h = X := concat_nil X
    rw [e]
    exact Or.inr ⟨h₁, hX⟩
  have key : ∀ i : Fin (tupleLength X + tupleLength Y),
      appendTuple X Y i ∈ ⋃ Q, chosenSaturatedFamily s Q := by
    intro i
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · simpa [appendTuple] using hX a
    · simpa [appendTuple] using hY b
  refine Or.inr ⟨?_, key⟩
  change 1 ≤ tupleLength X + tupleLength Y
  omega
theorem hasSupportApprox_separatingTuples {M : ℝ}
    (hD : IsDenseInvariantFamily s (chosenSaturatedFamily s))
    (hsharp : ∀ Q ∈ boxUnions, ∀ f ∈ c1Off Q, sharpNormR4 M f ≤ 80 * M * c1NormR4 f)
    (hM : 1 ≤ M) (hsq : DisjointUnionsBetweenCompactAndOpen) :
    HasSupportApprox s M (separatingTuples s) := by
  intro X h₁ O hO hXO
  have hX := tupleComponents_mem X
  let A : Fin (tupleLength X) → Set (EuclideanFour s) := fun i => tsupport (tupleComponents X i)
  let f : Fin (tupleLength X) → (Fin 4 → ℝ) → ℝ := tupleComponents X
  obtain ⟨Q, hQ, hdisj, hAQ⟩ := hsq (tupleLength X) h₁ A O
    (fun i => isCompact_pi_of_isCompact (hX.1 i).2) (fun i j hij => hX.2 hij)
    (fun i => isOpen_pi_of_isOpen (hO i)) hXO
  have hf₀ : ∀ i (x : EuclideanFour s), x ∉ Q i → tupleComponents X i x = 0 := fun i x hx =>
    image_eq_zero_of_notMem_tsupport fun hx' => hx ((hAQ i).1 hx')
  have hf : ∀ i, f i ∈ c1Off (Q i) := fun i =>
    ⟨(isC1Fn_euclidean_iff _).1 (hX.1 i).1, hf₀ i⟩
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hex : ∀ (n : ℕ) (i : Fin (tupleLength X)), ∃ h ∈ chosenSaturatedFamily s ⟨Q i, hQ i⟩,
      c1NormR4 (f i - h) < 1 / ((n : ℝ) + 1) := fun n i =>
    hD.dense ⟨Q i, hQ i⟩ _ (hf i) _ (hpos n)
  choose g hgD hgn using hex
  have hg : ∀ n i, g n i ∈ c1Off (Q i) := fun n i => hD.sub ⟨Q i, hQ i⟩ (hgD n i)
  let G : ℕ → Fin (tupleLength X) → EuclideanFour s → ℝ := g
  have hts : ∀ n i, tsupport (G n i) ⊆ Q i := fun n i =>
    tsupport_subset_of_mem_c1Off (hQ i) (hg n i)
  have hsep : ∀ n, G n ∈ separatedTuples s .euclidean (tupleLength X) := fun n =>
    ⟨fun i => ⟨(isC1Fn_euclidean_iff _).2 (hg n i).1,
        (isCompact_of_isCompact_pi (s := s) (A := Q i)
          (isCompact_of_mem_boxUnions (hQ i))).of_isClosed_subset (isClosed_tsupport _) (hts n i)⟩,
      fun i j hij => (hdisj hij).mono (hts n i) (hts n j)⟩
  refine ⟨fun n => ⟨G n, hsep n⟩, fun n => Or.inr ⟨h₁, fun i => mem_iUnion.2 ⟨_, hgD n i⟩⟩,
    fun n i => (hts n i).trans (hAQ i).2, fun i => ?_⟩
  have hlim : Tendsto (fun n : ℕ => 80 * M * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (80 * M)
  refine squeeze_zero (fun n => le_max_of_le_left (Real.iSup_nonneg fun _ => norm_nonneg _))
    (fun n => ?_) hlim
  have h₂ := hsharp (Q i) (hQ i) _ (sub_mem_c1Off (hf i) (hg n i))
  have h₃ : 80 * M * c1NormR4 (f i - g n i) ≤ 80 * M * (1 / ((n : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_left (hgn n i).le (by linarith)
  exact ((sharpNormR4_sub_comm M _ _).le.trans h₂).trans h₃
theorem separatingTuplesProperties_of_boxes
    (hboxes : BoxSpaceProperties.Claim) (hsat : ChosenFamilyIsSaturatedDense)
    (hsq : DisjointUnionsBetweenCompactAndOpen) :
    SeparatingTuplesProperties.Claim := by
  intro s M hM
  have hb := hboxes s M hM
  have hD := (hsat s).1
  have := hb.boxes_countable.to_subtype
  refine ⟨separatingTuples_countable (countable_iUnion hD.countable),
    fun X hX w hw => exists_mem_separatingTuples_transport (isDistIsometry_hyperoctahedralEquiv hw)
      (fun f hf => hD.invariant_hyperoctahedral w hw f hf) hX,
    fun X hX v hv => exists_mem_separatingTuples_transport
      (R4TupleForms.isDistIsometry_shiftEquiv v)
      (fun f hf => hD.invariant_shift v hv f hf) hX,
    fun X hX Y hY h => concat_mem_separatingTuples hX hY h,
    hasSupportApprox_separatingTuples hD hb.sharpNorm_le_c1Norm hM hsq⟩
end YangMills.Construction.CanonicalDecomposition
