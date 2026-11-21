import YangMills.Construction.EuclideanFunctionals.ConeConditionOfTheSystemOfAReconstruction
import YangMills.Construction.EuclideanFunctionals.InsertionOfTheSystemOfAReconstruction
import YangMills.Construction.EuclideanFunctionals.InvarianceOfConnectedFunctionsAndOfTheCentredFunctional
import YangMills.Construction.EuclideanFunctionals.MeasureOfTheSystemOfAReconstruction
import YangMills.Construction.EuclideanFunctionals.PictureOfTheSystemOfAReconstruction
import YangMills.Construction.EuclideanFunctionals.PlateBoundOfTheSystemOfAReconstruction
import YangMills.Construction.EuclideanFunctionals.PositiveFormAndEnvelopeOfLocalBounds
import YangMills.Construction.EuclideanFunctionals.ReconstructionOfASystem
import YangMills.Construction.EuclideanFunctionals.SymmetryOfConnectedFunctionsAndOfTheCentredFunctional
import YangMills.Construction.EuclideanFunctionals.SystemAndReconstructionFixEachOther
import YangMills.Construction.EuclideanFunctionals.SystemOfAReconstruction
import YangMills.Construction.EuclideanFunctionals.TubeOperatorOfTheSystemOfAReconstruction
import YangMills.Construction.EuclideanFunctionals.TwoDefinitionsOfASymmetricEuclideanFunctional
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.DefinitionComparison
theorem twoDefinitionsAgree_of_parts
    (hSymm : ConnectedSymmetry.Main)
    (hInv : InvarianceComparison.Holds)
    (hPos : PositivityAndEnvelope.Holds)
    (hData : OSDataOfRecon.Holds)
    (hRecon : ReconOfOSData.Holds)
    (hMutual : MutualDetermination.Holds)
    (hMeas : ReconSystemMeasuresAgree)
    (hCone : SystemConeCondition.Holds)
    (hIns : SystemInsertion.Holds)
    (hProd : ProductBoundOfOSData.Holds)
    (hPic : ReconSystemPicturesAgree)
    (hTube : TubeOperator.Main) :
    TwoDefinitionsAgree := by
  intro m S
  have toData : ∀ σ : EuclidFunctionalWithRecon m S,
      Nonempty (OSDataOf σ) := fun σ => by
    obtain ⟨d, hd⟩ := hData m S σ
    exact ⟨{ isSymmMultilinReal := (hSymm S).1 σ.symm
             isLatticeInvariant := (hInv S).1 σ.invariant
             isOSPositive := (hPos m S).1.1 σ.positive
             osData := d
             corresponds := hd }⟩
  have toRecon : ∀ τ : SymmEuclidFunctional m S,
      Nonempty (ReconOf τ) := fun τ => by
    obtain ⟨R, hR⟩ := hRecon m S τ
    exact ⟨{ symm := (hSymm S).2 τ.isSymmMultilinReal
             invariant := (hInv S).2 τ.isLatticeInvariant
             positive := (hPos m S).1.2 τ.isOSPositive
             recon := R
             corresponds := hR }⟩
  refine ⟨⟨hSymm S, hInv S, (hPos m S).1, (hPos m S).2⟩, toData,
    toRecon, fun H _ _ _ => hMutual H S, ⟨?_, ?_⟩, fun σ s =>
      ⟨hMeas m S σ s, hCone m S σ s, hIns m S σ s, hProd m S σ s, hPic m S σ s,
        hTube m S σ s⟩⟩
  · rintro ⟨τ⟩
    obtain ⟨r⟩ := toRecon τ
    exact ⟨r.toRecon⟩
  · rintro ⟨σ⟩
    obtain ⟨s⟩ := toData σ
    exact ⟨s.toSymm⟩
end YangMills.Construction.EuclideanFunctionals.DefinitionComparison
