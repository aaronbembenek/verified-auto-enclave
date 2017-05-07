# verified-auto-enclave
## Aaron Bembenek, Lily Tsai, Ezra Zigmond

Verified automatic placement of Intel SGX-like enclaves that provides provable security against low-level attackers.

`make` compiles all proofs.

##SImpE Files
SImpE is a simplified security-typed calculus that models enclaves. We prove that a well-typed SImpE program has security properties.

- SImpE.v : Model of SImpE syntax, semantics
- SImpE2.v : Model of SImpE2 syntax, semantics, security definitions
- SImpECommon.v : General definitions of security policies and levels, machine model used by SImpE
- SImpE2Adequacy.v : Lemmas about SImpE2 Soudness and Completeness
- SImpE2TypeSystem.v : Lemmas about SImpE2 Well-Typeness Preservation
- SImpESecurity.v : Lemmas about noninterference security of SImpE programs
- SImpE2Helpers.v : Helpers necessary to prove adequacy of SImpE2 
- SImpE2SecurityHelpers.v : Helpers necessary to prove security lemmas (preservation and observational equivalence)

##Translation Files
The translation scheme takes an ImpS program and produces an ImpE program. ImpS is a security-typed calculus without enclaves. ImpE is a security-typed calculus that models enclaves. We prove that the translation scheme preserves well-typedness.

- ImpE.v : Model of ImpE syntax, semantics
- ImpS.v : Model of ImpS syntax, semantics
- Common.v : General definitions of security policies and levels, machine model used by ImpE and ImpS
- IdTrans.v : A naive computational translation
- Translation2.v : A model of the translation scheme and a proof that the translation sheme preserves well-typedness.
