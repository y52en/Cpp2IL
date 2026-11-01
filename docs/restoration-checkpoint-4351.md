# ARM64 recovery checkpoint 4351

This checkpoint publishes the upstream-derived recovery candidate through round 4351. It includes scalar struct snapshot projection, conservative field-address recovery, ARM64 atomic and aggregate handling, bounded ELF unwind parsing, and direct initialization of value-type locals.

## Recorded validation

- Frozen candidate SHA-256: `7828b9e715e3724345ffd7f7f21dafdf2038de755c2126063639becb77e9ff8b`.
- Recorded full Cpp2IL.Core.Tests run: 4,481 passed, 0 failed, 0 skipped.
- Fixed 14,845-method source census: 7,965 non-stub bodies without native verification; 3,839 diagnostic/unsupported bodies; 2,360 missing or ambiguous mappings; 681 empty bodies.
- No source classification regressions relative to round 4346. These source counts are not native agreement counts.
- Direct local initialization removed scratch locals in 343 mscorlib methods; this is an IL simplification, not 343 native matches.
- The diagnostic DateTimeParse target remains different from the original native implementation. This checkpoint does not claim native adoption or achievement of the 90% objective.

Publication checks verified all 841 frozen manifest file hashes and compared 773 production/test C# files with this checkout after newline normalization. The portable repository-relative test-data path is retained instead of the validation machine's absolute path. Recorded tests belong to the frozen candidate; the publication did not rerun the full suite.

The later round 4354 parameter-ordinal candidate is deliberately excluded because two runtime fixture tests failed. No third-party fork changes are introduced by this publication.
