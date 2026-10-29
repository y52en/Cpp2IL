# ARM64 restoration checkpoint (2026-10-30)

This checkpoint extends the previous PR snapshot with recovery changes and regression tests from the tested packed-before-float source checkpoint.

- Recover registered method identities, hidden MethodInfo values, receiver counterparts and leaf accessors using native evidence.
- Recover parameterized base initialization, proven scalar constructor setup and zero-state constructors while retaining ambiguity and side-effect guards.
- Preserve native widths for integer extensions, scalar comparisons, indirect aggregate arguments and returns, and packed stores containing float and integer lanes.
- Improve interface metadata/phi handling, metadata initialization forks, class initialization and equivalent-edge copies.
- Add focused positive and rejection tests for the new recovery paths.

The checkpoint source was checked against the immutable input hashes of a completed full core test run: **3,916 passed, 0 failed**. Source line endings are normalized for Git; the test fixture paths remain repository-relative. The adjacent JSON records the source file hashes and validation scope.

Unit tests and compilation do not establish native equivalence of every recovered method. Original native comparison, metadata/callee checks, whole-program non-regression and independent rebuild remain separate restoration acceptance gates. Unfinished constant-reset dominance experiments and external Unity/SDK build tooling are excluded.
