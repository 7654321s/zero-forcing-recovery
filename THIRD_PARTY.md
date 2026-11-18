# Dependencies and attribution

The project's Lean proofs, Python scripts and documentation are distributed under the root MIT license. This does not relicense dependencies or claim originality for established mathematics.

| Dependency | Version or revision | License and source |
| --- | --- | --- |
| Lean | 4.35.0 | Apache-2.0; [leanprover/lean4](https://github.com/leanprover/lean4) |
| Mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679` | Apache-2.0; [leanprover-community/mathlib4](https://github.com/leanprover-community/mathlib4/tree/56a005855ea17e0b0958f73ec801ae140b0a1679) |

Lake resolves Mathlib's transitive dependencies using the committed manifest. These dependencies retain their own copyright notices and license files. They are downloaded separately, rather than vendored as project sources.

The project was developed with AI assistance through Codex. The finite-tree classification is proved for the recorded formal definitions, assumptions and axioms. Mathematical priority and independent human review remain unconfirmed; the model interpretation is documented separately in review/MODEL.md.
