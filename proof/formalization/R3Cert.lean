/- Library root for the R3 (Phi <= 1) exact-arithmetic formalization. -/
import R3Cert.ExactCruxes
import R3Cert.DEC
import R3Cert.Involution
import R3Cert.Matching
import R3Cert.CavityTree
import R3Cert.Bridge
import R3Cert.BridgeStep2
import R3Cert.BridgeStep3
import R3Cert.BridgeStep4
import R3Cert.Sweep
import R3Cert.Jensen
import R3Cert.JTail
import R3Cert.Hull
import R3Cert.Structure
import R3Cert.HullFull
import R3Cert.Grid
import R3Cert.Reach
import R3Cert.NodesSmall
import R3Cert.TieHarmonic
import R3Cert.NearStar
import R3Cert.BushBound
import R3Cert.Locality
import R3Cert.ChainMargin
import R3Cert.Plainify
import R3Cert.PlainFormula

import R3Cert.LemmaA

import R3Cert.Potential

import R3Cert.PotentialBound

import R3Cert.PotentialCrux

import R3Cert.PotentialAux

import R3Cert.PotentialGVal

import R3Cert.PotentialNearStar
import R3Cert.PotentialConvex
import R3Cert.PotentialClassify
import R3Cert.PotentialReduce
import R3Cert.PotentialAssembly
import R3Cert.PotentialM0
import R3Cert.PotentialM0Region
import R3Cert.PotentialM1
import R3Cert.PotentialM1Fold
import R3Cert.PotentialM1Piece
import R3Cert.PotentialEBase
import R3Cert.PotentialE2
import R3Cert.PotentialE2Small
import R3Cert.PotentialE13
import R3Cert.PotentialFinal
import R3Cert.BridgeStep3b
import R3Cert.BridgeStep3c
import R3Cert.BridgeStep3d
import R3Cert.BridgeStep4b
import R3Cert.BridgeStep4c
import R3Cert.BridgeStep4d
import R3Cert.BridgeStep3e
import R3Cert.BridgeStep3f
import R3Cert.BridgeStep4e
import R3Cert.BridgeStep4f
import R3Cert.BridgeStep4g
import R3Cert.BridgeStep4h
import R3Cert.BridgeStep4i
import R3Cert.BridgeStep4j
import R3Cert.BridgeStep4k
import R3Cert.R47Tree
import R3Cert.R47HubState
import R3Cert.R47HubForms
import R3Cert.R47Backbone
import R3Cert.R47BackboneAmp
import R3Cert.R47Step
import R3Cert.R47StepSize
import R3Cert.R47Cert
import R3Cert.R47CertB
import R3Cert.R47CertC
import R3Cert.R47CertD
import R3Cert.R47Dress
import R3Cert.R47Capped
import R3Cert.R47Head
import R3Cert.R47HeadId
import R3Cert.R47Mono
import R3Cert.R47Dispatch
import R3Cert.R47Rotate
import R3Cert.R47RotateV
import R3Cert.R47OrderedStep
import R3Cert.R47VeeId
import R3Cert.R47MirrorId
import R3Cert.R47VeeMono
import R3Cert.R47VeeDispatch
import R3Cert.R47StepMono
import R3Cert.R47Legs
import R3Cert.R47LegsRate
import R3Cert.LegsCherries
import R3Cert.R47LegsAT
import R3Cert.HomogeneousSlice
import R3Cert.NearStarBandSlice
import R3Cert.MasterCore
import R3Cert.R7CollapseMono
import R3Cert.R7CollapseT0
import R3Cert.GStep2TypeFace
import R3Cert.GStep3TypeFace
import R3Cert.GStepFullFace
import R3Cert.GStepCore
import R3Cert.CappedJointSkeleton
import R3Cert.CavityIdentities
import R3Cert.GLemmaAssembly
import R3Cert.ProdBounds
import R3Cert.CappedJointConfig
import R3Cert.CappedJointAchievable
import R3Cert.GArmExtAbstract
import R3Cert.GLemmaAbstract
import R3Cert.CappedJointClosure
import R3Cert.VertexLemma
import R3Cert.VertexLemmaFull
import R3Cert.GLemmaConfig
import R3Cert.TieClosure
import R3Cert.R47Shed
import R3Cert.R47Perm
import R3Cert.R47Parse
import R3Cert.R47RateZBound
import R3Cert.R47Rate
import R3Cert.FractalTail
import R3Cert.HingeProfileFloor
import R3Cert.R7CollapsePointFloor

import R3Cert.R7CollapseCompose

-- BG closure-campaign Lean drafts (CI-gated; name-checked, not previously compiled)
-- NearStarUnimodal dropped: rewrite failure at :159 (ratio-unimodality; sibling claim refuted by campaign verify)
import R3Cert.BridgeStep4l
import R3Cert.R47RootInvariance
import R3Cert.R47CampaignBrick

-- LPRSC: the integrality-aware marginal-tie certificate primitive (new Telperion shape)
import R3Cert.LPRSC

-- Single-hub objective in closed form (Hdom / R6 entry point)
import R3Cert.R47SingleHub

-- Merge-layer capstone restated in the real per(L)/prod-deg object (G7 composition step)
import R3Cert.R47MergePerL

-- R7' top-composition capstone: conjecture1 reduced to the two open layers (conditional)
import R3Cert.R47TopCapstone

-- Normal-form structural theory (Hdom infrastructure)
import R3Cert.R47NormalForm
