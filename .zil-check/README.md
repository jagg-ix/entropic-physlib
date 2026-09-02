# ZIL graph validation outputs

Each `.txt` file here is the recorded validation output of one `.zc` knowledge graph
(see `.zil/`), produced by `./scripts/zil-check.sh` against the pinned `zil-lean` engine
(revision in `formalization/zil/ZIL_REVISION`; the same revision is a lake dependency).
They are evidence artifacts, not documentation: regenerate with

```bash
ZIL_LEAN_DIR=/path/to/zil-lean ./scripts/zil-check.sh
```
