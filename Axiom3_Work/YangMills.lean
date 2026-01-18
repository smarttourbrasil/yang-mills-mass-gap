/-
  YangMills - Formal Verification of Yang-Mills Mass Gap
  
  Gap 3: BFS Cluster Expansion Convergence
  
  Main module file importing all Gap 3 components.
  
  Version: 1.0 (January 2026)
  Authors: Consensus Framework
-/

-- Core definitions
import YangMills.Gap3.SimpleCluster

-- Lemma A: Combinatorial counting bound
import YangMills.Gap3.LemmaA_Combinatorial

-- Lemma B: Analytic decay bound  
import YangMills.Gap3.LemmaB_Analytic

-- Convergence corollary
import YangMills.Gap3.Corollary_Convergence

-- Main theorem: Axiom 3'
import YangMills.Gap3.Axiom3Prime
