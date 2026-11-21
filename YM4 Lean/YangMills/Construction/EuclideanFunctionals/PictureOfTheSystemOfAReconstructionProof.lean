import YangMills.Construction.EuclideanFunctionals.PictureOfTheSystemOfAReconstruction
import YangMills.Construction.EuclideanFunctionals.RoomForTheInsertion
import Mathlib
set_option autoImplicit false
open YangMills.Construction.RealPlane
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.ReconSystemPicture
open DefinitionComparison
theorem conjReflection_actFree_freeConj (hA : TupleRules.MotionOnFree)
    (w : EuclidMotion) (F : FreeSep) :
    (conjReflection w).actFree (freeConj (w.actFree F)) = w.actFree (flipConj F) := by
  have hmul : conjReflection w * w = w * timeFlip := by
    simp [conjReflection]
  rw [(hA w w F).2.1, (hA (conjReflection w) w (freeConj F)).1, hmul, flipConj,
    (hA w timeFlip (freeConj F)).1]
theorem mappedInsertionForm_eq_rotatedInsertion (hT : TupleRules.TupleSpanActionRules)
    (S : ConnFamily) (w : hyperoctahedral) {c : ℝ} {F A : FreeSep} {h : R4 → ℂ}
    (hc : IsStripHeight c F h A) :
    mappedInsertionForm S w ((w : EuclidMotion).actFree F) ((w : EuclidMotion).actFn h)
        ((w : EuclidMotion).actFree A) =
      rotatedInsertion S w F h A := by
  obtain ⟨-, -, hAct, -, -, hRules, hAssoc, hTuples, -, hRefl, -, -⟩ := hT
  have hF : F ∈ finCombIn {x | c < x 3} := by
    rw [finCombIn_eq_freeSpanIn]
    exact hc.left_mem
  have hA : A ∈ finCombIn {x | c < x 3} := by
    rw [finCombIn_eq_freeSpanIn]
    exact hc.right_mem
  have hthree := hRefl.2 c hc.pos F hF A hA h hc.mem_C1c hc.supp_subset
  have hdef := (hAssoc _ _ _ hthree).1
  have hr₁ := (hRules (w : EuclidMotion) _ _ hdef).2.2.2.2
  have hr₂ := (hRules (w : EuclidMotion) _ _ hthree.1).2.2.2.2
  have hentries : ComplexComponents (fun _ : Fin 1 => h) :=
    ⟨le_rfl, fun _ => hc.mem_C1c, fun k l hkl => absurd (Subsingleton.elim k l) hkl⟩
  obtain ⟨-, -, -, -, -, hentries', himage, -⟩ :=
    hTuples Set.univ isOpen_univ (w : EuclidMotion) 1 (fun _ => h) hentries
      (fun _ => Set.subset_univ _)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hsame, -⟩ :=
    hTuples Set.univ isOpen_univ (w : EuclidMotion) 1 (fun _ => (w : EuclidMotion).actFn h)
      hentries' (fun _ => Set.subset_univ _)
  rw [mappedInsertionForm_image hAct]
  simp only [rotatedInsertion, singleComplex, freeMul3, singleComponent]
  rw [hr₁, hr₂, himage, hsame, conjReflection_actFree_freeConj hAct]
theorem heightNorm_eq_rotatedLoweredNorm {m : SharpScale} {S : ConnFamily}
    {σ : EuclidFunctionalWithRecon m S}
    (s : OSDataOf σ) (hA : TupleRules.MotionOnFree)
    (w : hyperoctahedral) {c : ℝ} (hc : 0 < c) (F : freeSpanIn {x | c < x 3}) :
    heightNorm σ c F.1 = rotatedLoweredNorm s.toSymm w hc F := by
  have hclass : reconClass σ (pullDown c F.1) =
      classOrZero s.osData.cls (lowerBy hc F) :=
    s.corresponds.cls_eq _
  simp only [heightNorm, rotatedLoweredNorm, rotatedClass, inv_actFree_actFree hA]
  rw [hclass]
theorem reconSystemPicturesAgree_holds (hT : TupleRules.TupleSpanActionRules)
    (hR : InsertionRoom.Holds) : ReconSystemPicturesAgree := by
  intro m S σ s w
  have hAct : TupleRules.MotionOnFree := hT.2.2.1
  have hopen : IsOpen upperHalf :=
    isOpen_lt continuous_const (continuous_apply 3)
  have hplate : ∀ (p c : ℝ) (hp : 0 < p) (hc : c ∈ productBoundFractions),
      ∀ φ ∈ realLabels, ∀ C : ℝ, ImagePlaneProductBoundWith σ w hp hc φ C ↔
        SymmRotatedProductBoundWith s.toSymm w hp
          (productBoundFractions_subset_stripFractionRange hc) φ C := by
    intro p c hp hc φ hφ C
    have hsame : ∀ (η : ℝ) (hη : η ∈ gapWidthRange), ∀ α ∈ complexProfiles,
        tsupport α ⊆ planeStrip c η → ∀ F F' : freeSpanIn {x | η / 4 < x 3},
        ‖mappedInsertionForm S w ((w : EuclidMotion).actFree F.1)
            ((w : EuclidMotion).actFn (productFunction α φ)) ((w : EuclidMotion).actFree F'.1)‖ ≤
          C * η ^ (-p) * profileL1Norm α * heightNorm σ (η / 4) F.1 *
            heightNorm σ (η / 4) F'.1 ↔
        ‖rotatedInsertion S w F.1 (productFunction α φ) F'.1‖ ≤
          C * η ^ (-p) * profileL1Norm α *
            rotatedLoweredNorm s.toSymm w (quarter_pos_of_mem_gapWidthRange hη) F *
            rotatedLoweredNorm s.toSymm w (quarter_pos_of_mem_gapWidthRange hη) F' := by
      intro η hη α hα hsupp F F'
      rw [mappedInsertionForm_eq_rotatedInsertion hT S w
          (hR.2.2.2 η hη c (productBoundFractions_subset_stripFractionRange hc) α hα φ hφ hsupp
            F.1 F.2 F'.1 F'.2),
        heightNorm_eq_rotatedLoweredNorm s hAct w (quarter_pos_of_mem_gapWidthRange hη) F,
        heightNorm_eq_rotatedLoweredNorm s hAct w (quarter_pos_of_mem_gapWidthRange hη) F']
    constructor
    · intro H η hη α hα hsupp F F'
      refine (hsame η hη α hα hsupp F F').1 (H η hη α hα hsupp F.1 ?_ F'.1 ?_)
      · rw [finCombIn_eq_freeSpanIn]
        exact F.2
      · rw [finCombIn_eq_freeSpanIn]
        exact F'.2
    · intro H η hη α hα hsupp F hF F' hF'
      rw [finCombIn_eq_freeSpanIn] at hF hF'
      exact (hsame η hη α hα hsupp ⟨F, hF⟩ ⟨F', hF'⟩).2 (H η hη α hα hsupp ⟨F, hF⟩ ⟨F', hF'⟩)
  refine ⟨?_, rfl, ?_, ?_, ?_⟩
  · exact SetLike.coe_injective (by
      rw [mappedUpperSpan, Submodule.map_coe]
      exact (hT.2.1 (w : EuclidMotion) upperHalf hopen).2.2.image_eq)
  · intro A
    exact (s.corresponds.cls_eq _).symm
  · intro c F A h hc
    exact mappedInsertionForm_eq_rotatedInsertion hT S w hc
  · intro p c hp hc
    refine ⟨?_, hplate p c hp hc⟩
    rw [hasProductBoundInRotatedPlane_iff]
    exact forall₂_congr fun φ hφ => exists_congr (hplate p c hp hc φ hφ)
end YangMills.Construction.EuclideanFunctionals.ReconSystemPicture
