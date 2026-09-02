# Contributing

This is a research fork of [Physlib](https://github.com/leanprover-community/physlib); see
the [README](README.md) for what it adds and how it relates to upstream.

- Contributions to the **base physics library** belong upstream:
  see https://physlib.io/get-involved.
- Contributions to the **entropic-gravity program, the ZIL knowledge graph, or the audit
  tooling** belong here. Open a pull request against `master`. The review standards are
  upstream's ([docs/ReviewGuidelines.md](docs/ReviewGuidelines.md)) plus this fork's rules:
  no `sorry`, no `axiom` declarations ([AGENTS.md](AGENTS.md)), and physical claims must
  carry `zil attach` metadata naming their premises.
- AI-assisted contributions must follow [AI-POLICY.md](AI-POLICY.md): the human author
  certifies every line, and bibliographic verification is never delegated to an AI.

Before opening a PR, run:

```bash
lake build                      # must be green
./scripts/zil-graph-report.sh   # buried_conditionality must stay 0
```
