import Lake
open Lake DSL

/-! Host test of this fork's public functions against the vectors in `tests/cryptography`.

It requires the repository's own EthLib by path and shares its resolved dependencies.

So it needs no download of its own.

Run from this directory: `lake build hosttest && .lake/build/bin/hosttest`. -/

package «hosttest» where
  packagesDir := "../../.lake/packages"

require EthLib from ".." / ".."

lean_exe «hosttest» where
  root := `Main
