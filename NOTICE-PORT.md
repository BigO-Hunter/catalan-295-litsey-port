Toolchain port of μ(G) ≤ 295 to the BigOSpeedrun Catalan profile — NOTICE

Credit is sacred. The construction and the proof are Sean Litsey's.

1. Construction and proof (the mathematics, unchanged)
   Sean Litsey, "An irrationality measure for Catalan's constant" —
   https://github.com/slitsey/catalan-irrationality-measure at commit
   65cfcc216b2fd8a6c52f84a8ea41fb654b11eddb (2026-11-06), Apache-2.0 (LICENSE, NOTICE).
   The theorem formalized there is μ(G) ≤ 295:
   CatalanMeasure.GenD.Signed.RouteI.Measure295.catalan_irrationalityMeasure_295.
   Every Lean module in Submission/ is his text, except the two disclosed elaborator
   adjustments and the import-prefix conversion below. No statement is changed and no
   proof step is re-derived by us.

2. OpenAI-preprint lineage
   Litsey's development is a descendant of the OpenAI formalization accompanying
   "Catalan's constant is irrational" (OpenAI, 24 September 2026;
   https://github.com/openai/math commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, OAI/,
   Apache-2.0), vendored in OAI/ with the modifications listed in NOTICE item 1, and of
   PrimeNumberTheoremAnd (AlexKontorovich, commit c39a7511, Apache-2.0) as patched by OPENAI
   (NOTICE item 2). The Davis inverse-image quadrature certificates in
   CatalanMeasure/GenD/Signed/Davis/ (33 files, PROVENANCE.json) are Cinna Davis's,
   github.com/1337isnot1337/catalan-constant commit 3c451531, Apache-2.0 (NOTICE item 4).
   All of that material is carried here unchanged, with Litsey's NOTICE retained verbatim.

3. Our role: toolchain port, nothing else
   We changed only the toolchain and layout so that the same proof builds at the profile
   the BigOSpeedrun Catalan challenge pins, per docs/convert-layout.md of
   bigospeedrun/verifier:
   a. Layout: the Lean source roots OAI, PrimeNumberTheoremAnd, CatalanMeasure and
      CatalanCore are copied to Submission/ with the prefix `Submission.` added to
      imports of those roots (the reference script of docs/convert-layout.md, run with
      roots "OAI PrimeNumberTheoremAnd CatalanMeasure CatalanCore"; the fourth root,
      CatalanCore, is present in the 295 tree and required by
      CatalanMeasure/GenD/Uniform/W/). No other line of any moved file is changed, apart
      from item 3c and 3d below.
   b. Pin: lean-toolchain is leanprover/lean4:v4.34.1 and Mathlib is
      d13f23b723b8a846827a245b89c10fc7d3f11612, the Catalan profile pin (the upstream
      v4.35.0-rc2 build files are kept as *-upstream and are not used).
   c. Elaborator adjustment in Submission/CatalanMeasure/GenD/Cert/Assembly.lean:
      in blockOK_ofS the decided conjunct is closed via
      decide_eq_true_eq.mpr (of_decide_eq_true hPb) instead of of_decide_eq_true hPb.
      The toD rewrite reaches the proposition but not the Decidable instance term at
      this profile. The statement of blockOK_ofS is unchanged.
   d. Budget adjustment in Submission/CatalanMeasure/GenD/Signed/SheetNear.lean:
      set_option maxHeartbeats 1600000 in is added before theorem near_Sterm_le (the
      default 200000 is exceeded at this profile). The statement of near_Sterm_le is
      unchanged.
   e. New files: Submission/CatalanStatement.lean is a byte-for-byte copy of
      challenges/catalan/Statement.lean of bigospeedrun/verifier; Submission.lean is a
      new bridge (the transport of `upperBoundFor_of_endpoint` from
      challenges/catalan/Validation.lean) proving
      Race.bound : BigOSpeedrun.Catalan.Bound ((295 : ℚ) / 1) from Litsey's theorem.

4. What was verified here
   lake build Submission at the pin, with #print axioms Race.bound showing only
   [propext, Classical.choice, Quot.sound]. The build log is PORT_BUILD.log, the axiom
   output is in Submission.lean. Statements: the conversion is byte-preserving (each file
   keeps its own line terminators), so a plain `diff -r` of Submission/ against the source
   tree shows only the changes listed in item 3 — see PORT_DIFF.txt. All source files of
   this repository use CRLF line endings; the converted copies keep them.
